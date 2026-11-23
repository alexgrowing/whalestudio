import ReciprocityTheory.BasicDefinitions.ExistsUnique

namespace ReciprocityTheory.Def

open Matrix

variable {k : Type*} [CommRing k] {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module k M]

def C1 (G : Type*) [TopologicalSpace G] (N : Submodule k M) : Submodule k (G → M) where
  carrier := {c | IsLocallyConstant c ∧ ∀ g, c g ∈ N}
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g => N.add_mem (ha.2 g) (hb.2 g)⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ => N.zero_mem⟩
  smul_mem' := fun c x hx => ⟨hx.1.comp (fun m => c • m), fun g => N.smul_mem c (hx.2 g)⟩

def C2 (G : Type*) [TopologicalSpace G] (N : Submodule k M) : Submodule k (G × G → M) where
  carrier := {c | IsLocallyConstant c ∧ ∀ x, c x ∈ N}
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g => N.add_mem (ha.2 g) (hb.2 g)⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ => N.zero_mem⟩
  smul_mem' := fun c x hx => ⟨hx.1.comp (fun m => c • m), fun g => N.smul_mem c (hx.2 g)⟩

def d0 (π : Representation k G M) : M →ₗ[k] (G → M) where
  toFun m := fun g => π g m - m
  map_add' := fun a b => by ext g; simp; abel
  map_smul' := fun c a => by ext g; simp [smul_sub]

def d1 (π : Representation k G M) : (G → M) →ₗ[k] (G × G → M) where
  toFun c := fun x => π x.1 (c x.2) - c (x.1 * x.2) + c x.1
  map_add' := fun a b => by ext x; simp; abel
  map_smul' := fun c a => by ext x; simp [smul_sub, smul_add]

def d2 (π : Representation k G M) : (G × G → M) →ₗ[k] (G × G × G → M) where
  toFun z := fun x => π x.1 (z (x.2.1, x.2.2)) - z (x.1 * x.2.1, x.2.2) + z (x.1, x.2.1 * x.2.2) - z (x.1, x.2.1)
  map_add' := fun a b => by ext x; simp; abel
  map_smul' := fun c a => by ext x; simp [smul_sub, smul_add]

def Z1 (π : Representation k G M) (N : Submodule k M) : Submodule k (G → M) :=
  C1 G N ⊓ LinearMap.ker (d1 π)

def B1 (π : Representation k G M) (N : Submodule k M) : Submodule k (G → M) := N.map (d0 π)

def Z2 (π : Representation k G M) (N : Submodule k M) : Submodule k (G × G → M) :=
  C2 G N ⊓ LinearMap.ker (d2 π)

def B2 (π : Representation k G M) (N : Submodule k M) : Submodule k (G × G → M) := (C1 G N).map (d1 π)

abbrev H1 (π : Representation k G M) (N : Submodule k M) : Type _ := Z1 π N ⧸ (B1 π N).submoduleOf (Z1 π N)

abbrev H2 (π : Representation k G M) (N : Submodule k M) : Type _ := Z2 π N ⧸ (B2 π N).submoduleOf (Z2 π N)

def adRep {n : ℕ} (rbar : G →* GL (Fin n) k) : Representation k G (Matrix (Fin n) (Fin n) k) where
  toFun g :=
    { toFun := fun X => (rbar g).val * X * ((rbar g)⁻¹).val
      map_add' := fun X Y => by simp [mul_add, add_mul]
      map_smul' := fun c X => by simp }
  map_one' := by ext X : 1; simp
  map_mul' := fun g h => by ext X : 1; simp [mul_assoc]

end ReciprocityTheory.Def
