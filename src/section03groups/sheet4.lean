/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import group_theory.subgroup.basic -- import Lean's subgroups

/-

# Group homomorphisms

We show how to build the type `my_group_hom G H` of group homomorphisms
from `G` to `H`. We make notation `G →** H` for this, so `f : G →** H`
means "`f` is a group homomorphism from `G` to `H`".

-/

/-- `my_group_hom G H` is the type of group homomorphisms from `G` to `H`. -/
@[ext] structure my_group_hom (G H : Type) [group G] [group H] :=
(to_fun : G → H)
(map_mul' (a b : G) : to_fun (a * b) = to_fun a * to_fun b)

namespace my_group_hom

-- throughout this sheet, `G` and `H` will be groups.
variables {G H : Type} [group G] [group H]

-- We use notation `G →** H` for the type of group homs from `G` to `H`.
notation G ` →** ` H := my_group_hom G H

-- A group hom is a function, and so we set up a "coercion"
-- so that a group hom can be regarded as a function (even
-- though it's actually a pair consisting of a function and an axiom)
-- instance : has_coe (G →** H) (G → H) := { coe := my_group_hom.to_fun }
instance : has_coe_to_fun (G →** H) (λ _, G → H) :=
{ coe := my_group_hom.to_fun }

-- Notice that we can now write `f (a * b)` even though `f` isn't actually a
-- function, it's a pair consisting of a function `f.to_fun` and an axiom `f.map_mul'`.
-- The below lemma is how we want to use it as mathematicians though.
lemma map_mul (f : G →** H) (a b : G) : 
  f (a * b) = f a * f b :=
begin
  -- the point is that f.map_mul and f.map_mul' are *definitionally equal*
  -- but *syntactically different*, and the primed version looks uglier.
  -- The point of this lemma is that `f.map_mul` looks nicer.
  exact f.map_mul' a b
end

-- let `f` be a group hom
variable (f : G →** H)

-- To prove `map_one` you're going to need to know what the below lemma
-- is called. Uncomment it, look at the output, and remember it. It's
-- a useful part of the group theory API.

-- example (a b : G) : a * b = b ↔ a = 1 := by library_search -- look at the output.

-- Now see if you can do these.
@[simp] lemma map_one : f 1 = 1 :=
begin
  have : f 1 = f 1 := by simp,
  nth_rewrite 0 ←mul_one (1 : G) at this,
  rw map_mul at this,
  exact mul_right_eq_self.mp this,
end

lemma map_inv (a : G) : f a⁻¹ = (f a)⁻¹ :=
begin
  have := map_one f,
  rw ←mul_inv_self a at this,
  rw map_mul at this,
  exact (inv_eq_of_mul_eq_one this).symm,
end

variable (G)

/-- `id G` is the identity group homomorphism from `G` to `G`. -/
def id : G →** G :=
{ to_fun := λ a, a,
  map_mul' := by simp } -- fill in the proof that the identity function is a group hom!

variables {K : Type} [group K] {G}

/-- `φ.comp ψ` is the composite of `φ` and `ψ`. -/
def comp (φ : G →** H) (ψ : H →** K) : G →** K :=
{ to_fun := λ g, ψ (φ g),
  map_mul' := begin intros, rw map_mul, rw map_mul, end -- fill in the proof that composite of two group homs is a group hom!
}

-- The next three lemmas are pretty standard, but they are also in fact
-- the axioms that show that groups form a category.
lemma id_comp : (id G).comp f = f :=
begin
  ext,
  refl,
end

lemma comp_id : f.comp (id H) = f :=
begin
  ext,
  refl,
end

lemma comp_assoc {L : Type} [group L] (φ : G →** H) (ψ : H →** K) (ρ : K →** L) :
  (φ.comp ψ).comp ρ = φ.comp (ψ.comp ρ) :=
begin
  ext,
  refl,
end

/-- The kernel of a group homomorphism, as a subgroup of the source group. -/
def ker (f : G →** H) : subgroup G :=
{ carrier := {g : G | f g = 1 },
  one_mem' := begin exact map_one f end,
  mul_mem' := begin intros a b ha hb, simp [map_mul, *] at *,  end,
  inv_mem' := begin intros x hx, simp [map_inv, *] at *, end,
}

/-- The image of a group homomorphism, as a subgroup of the target group. -/
def im (f : G →** H) : subgroup H :=
{ carrier := {h : H | ∃ g : G, f g = h },
  one_mem' := begin use 1, simp, end,
  mul_mem' :=
  begin
    intros a b ha hb,
    cases ha with a' ha,
    cases hb with b' hb,
    use a' * b',
    simp [map_mul, *],
  end,
  inv_mem' :=
  begin
    intros x hx,
    cases hx with x' hx,
    use x'⁻¹,
    simp [map_inv, *],
  end,
}

/-- The image of a subgroup under a group homomorphism, as a subgroup. -/
def map (f : G →** H) (K : subgroup G) : subgroup H :=
{ carrier := {h : H | ∃ g : G, g ∈ K ∧ f g = h },
  one_mem' := begin use 1, simp [map_one, K.one_mem], end,
  mul_mem' :=
  begin
    intros a b ha hb,
    cases ha with a' ha,
    cases hb with b' hb,
    use a' * b',
    simp [map_mul, K.mul_mem, *],
  end,
  inv_mem' :=
  begin
    intros x hx,
    cases hx with x' hx,
    use x'⁻¹,
    simp [map_inv, K.inv_mem, *],
  end,
}

/-- The preimage of a subgroup under a group homomorphism, as a subgroup. -/
def comap (f : G →** H) (K : subgroup H) : subgroup G :=
{ carrier := {g : G | f g ∈ K },
  one_mem' := begin simp [map_one, K.one_mem], end,
  mul_mem' :=
  begin
    intros a b ha hb,
    simp [map_mul, K.mul_mem, *] at *,
  end,
  inv_mem' :=
  begin
    intros x hx,
    simp [map_inv, K.inv_mem, *] at *,
  end,
}

/-- Pushing a subgroup along one homomorphism and then another is equal to
  pushing it forward along the composite of the homomorphisms. -/
lemma map_comp (φ : G →** H) (ψ : H →** K) (L : subgroup G) :
  (φ.comp ψ).map L = ψ.map (φ.map L) :=
begin
  ext,
  split,
  {
    intro hx,
    cases hx with x' hx,
    simp [map, comp, *] at *,
    use x',
    split,
    { exact hx.1 },
    { exact hx.2 },
  },
  {
    intro hx,
    cases hx with x' hx,
    cases hx.1 with x'' hx',
    use x'',
    split,
    { exact hx'.1 },
    dsimp [comp],
    have hx := hx.2,
    rw ←hx'.2 at hx,
    exact hx,
  },
end

/-- Pulling a subgroup back along one homomorphism and then another, is equal
to pulling it back along the composite of the homomorphisms. -/
lemma comap_comp (φ : G →** H) (ψ : H →** K) (L : subgroup K) :
  (φ.comp ψ).comap L = φ.comap (ψ.comap L) :=
begin
  ext,
  split,
  {
    intro hx,
    exact hx,
  },
  {
    intro hx,
    exact hx,
  }
end

end my_group_hom
