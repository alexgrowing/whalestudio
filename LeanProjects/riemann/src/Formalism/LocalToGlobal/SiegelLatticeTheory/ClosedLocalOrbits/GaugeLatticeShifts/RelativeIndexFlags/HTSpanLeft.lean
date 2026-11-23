import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem gmap_eq_iff (g : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap g L = L ↔ ∀ y, y ∈ L ↔ g y ∈ L := by
  have hm : ∀ x, x ∈ Formalism.HermitianLatticesTheory.gmap g L ↔ g.symm x ∈ L := by
    intro x
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨g.symm x, hx, by simp⟩
  constructor
  · intro h y
    have := hm (g y)
    rw [h] at this
    simpa using this.symm
  · intro h
    ext x
    rw [hm, h (g.symm x)]
    simp

variable (Λ : Submodule (𝓞 E) S.V)

theorem isAutLam_mul {a b : S.V ≃ₗ[E] S.V} (ha : IsAutLam S Λ a) (hb : IsAutLam S Λ b) :
    IsAutLam S Λ (a * b) := by
  refine ⟨mul_mem ha.1 hb.1, (gmap_eq_iff _ _).2 fun y => ?_⟩
  rw [(gmap_eq_iff _ _).1 hb.2 y, (gmap_eq_iff _ _).1 ha.2 (b y)]
  rfl

theorem isAutLam_inv {a : S.V ≃ₗ[E] S.V} (ha : IsAutLam S Λ a) : IsAutLam S Λ a⁻¹ := by
  refine ⟨inv_mem ha.1, (gmap_eq_iff _ _).2 fun y => ?_⟩
  have := (gmap_eq_iff _ _).1 ha.2 (a.symm y)
  change y ∈ Λ ↔ a.symm y ∈ Λ
  rw [this]
  simp

variable {Λ}

theorem maps_of_sub {g : S.V ≃ₗ[E] S.V} {A B : Submodule E S.V} (hAB : A ≤ B)
    (h : ∀ x ∈ B, g x - x ∈ A) : ∀ x ∈ B, g x ∈ B := by
  intro x hx
  have := B.add_mem (hAB (h x hx)) hx
  simpa using this

theorem symm_maps {g : S.V ≃ₗ[E] S.V} {B : Submodule E S.V} (h : ∀ x ∈ B, g x ∈ B) :
    ∀ x ∈ B, g.symm x ∈ B := by
  haveI : FiniteDimensional E S.V := S.fd
  have hle : B.map (g : S.V →ₗ[E] S.V) ≤ B := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : B.map (g : S.V →ₗ[E] S.V) = B :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq g B)
  intro x hx
  rw [← heq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

theorem inv_sub {g : S.V ≃ₗ[E] S.V} {A B : Submodule E S.V} (hAB : A ≤ B)
    (h : ∀ x ∈ B, g x - x ∈ A) : ∀ x ∈ B, g.symm x - x ∈ A := by
  intro x hx
  have hy : g.symm x ∈ B := symm_maps (maps_of_sub hAB h) x hx
  have := A.neg_mem (h _ hy)
  simpa using this

theorem mul_sub' {g h : S.V ≃ₗ[E] S.V} {A B : Submodule E S.V} (hAB : A ≤ B)
    (hg : ∀ x ∈ B, g x - x ∈ A) (hh : ∀ x ∈ B, h x - x ∈ A) : ∀ x ∈ B, g (h x) - x ∈ A := by
  intro x hx
  have := A.add_mem (hg _ (maps_of_sub hAB hh x hx)) (hh x hx)
  simpa using this

variable {r : ℕ}

theorem xflag_mono {T : E} (F : LFlag S r T) (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  refine Submodule.span_mono (Set.image_mono fun i hi => ?_)
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

theorem mem_orth_iff (U : Submodule E S.V) (y : S.V) : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem hT_span_left {ι : Type*} (v : ι → S.V) (y : S.V) (hv : ∀ a, S.hT (v a) y = 0) :
    ∀ x ∈ Submodule.span E (Set.range v), S.hT x y = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, rfl⟩ := h
    exact hv a
  | zero => simp
  | add x z _ _ h1 h2 => simp [LinearMap.map_add₂, h1, h2]
  | smul c x _ h => simp [LinearMap.map_smulₛₗ₂, h]

theorem xsp_le_orth {T : E} (F : LFlag S r T) : Xsp F ≤ orth S (Xsp F) := by
  intro y hy
  rw [mem_orth_iff]
  intro x hx
  refine hT_span_left F.fl.e y (fun a => ?_) x hx

  have hk : Xsp F ≤ LinearMap.ker (S.hT (F.fl.e a)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, rfl⟩
    exact F.fl.e_iso a b
  exact hk hy

theorem z_mem_orth {T : E} (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  rw [mem_orth_iff]
  exact hT_span_left F.fl.e F.fl.z F.fl.z_orth

theorem nlam_mul {T : E} {F : LFlag S r T} {a b : S.V ≃ₗ[E] S.V} (ha : a ∈ NLam Λ F)
    (hb : b ∈ NLam Λ F) : a * b ∈ NLam Λ F :=
  ⟨isAutLam_mul Λ ha.1 hb.1, fun j x hx => mul_sub' (xflag_mono F j) (ha.2.1 j) (hb.2.1 j) x hx,
    fun x hx => mul_sub' (xsp_le_orth F) ha.2.2 hb.2.2 x hx⟩

theorem nlam_inv {T : E} {F : LFlag S r T} {a : S.V ≃ₗ[E] S.V} (ha : a ∈ NLam Λ F) :
    a⁻¹ ∈ NLam Λ F :=
  ⟨isAutLam_inv Λ ha.1, fun j x hx => inv_sub (xflag_mono F j) (ha.2.1 j) x hx,
    fun x hx => inv_sub (xsp_le_orth F) ha.2.2 x hx⟩

end Gen

end Formalism.L2.SG.Pf.RelativeIndexFlags
