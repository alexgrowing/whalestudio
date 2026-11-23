import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
open Classical

noncomputable section

namespace GlobalTheory.StableRange

open LinearMap Module

theorem exists_injective_add_comp {κ V : Type} [Field κ] [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (f g : V →ₗ[κ] V) (h : range f ⊔ range g = ⊤) : ∃ t : V →ₗ[κ] V, Function.Injective (f + g ∘ₗ t) := by
  obtain ⟨K', hK⟩ := (ker f).exists_isCompl
  set π := (range f).mkQ
  have hs : Function.Surjective (π ∘ₗ g) := by
    intro y
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
    have hv : v ∈ range f ⊔ range g := h ▸ Submodule.mem_top
    obtain ⟨a, ha, b, ⟨w, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hv
    refine ⟨w, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    convert neg_mem ha using 1
    abel
  have hd : finrank κ (ker f) = finrank κ (V ⧸ range f) := by
    have := f.finrank_range_add_finrank_ker
    have := (range f).finrank_quotient_add_finrank
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hd
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (π ∘ₗ g) (e : ker f →ₗ[κ] V ⧸ range f) hs
  refine ⟨l ∘ₗ Submodule.linearProjOfIsCompl (ker f) K' hK, ?_⟩
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  set p := Submodule.linearProjOfIsCompl (ker f) K' hK v with hpdef
  have hfv : π (f v) = 0 := (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self f v)
  have hgl : π (g (l p)) = e p := LinearMap.congr_fun hl p
  have h1 : e p = 0 := by
    have := congrArg π hv
    rw [LinearMap.add_apply, map_add, LinearMap.comp_apply, LinearMap.comp_apply, ← hpdef, hfv, hgl,
      zero_add, map_zero] at this
    exact this
  have hp : p = 0 := by simpa using h1
  have hvK' : v ∈ K' := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hK).1 hp
  have hvK : v ∈ ker f := by
    rw [LinearMap.mem_ker]
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← hpdef, hp, map_zero, map_zero,
      add_zero] at hv
    exact hv
  exact (Submodule.disjoint_def.1 hK.disjoint) v hvK hvK'

theorem field_exists_isUnit_det {κ n : Type} [Field κ] [Fintype n] [DecidableEq n] (A S C D : Matrix n n κ)
    (h : C * A + D * S = 1) : ∃ τ : Matrix n n κ, IsUnit (A + τ * S).det := by
  have ht : Aᵀ * Cᵀ + Sᵀ * Dᵀ = 1 := by
    rw [← transpose_mul, ← transpose_mul, ← transpose_add, h, transpose_one]
  have hr : range (toLin' Aᵀ) ⊔ range (toLin' Sᵀ) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = Aᵀ *ᵥ (Cᵀ *ᵥ v) + Sᵀ *ᵥ (Dᵀ *ᵥ v) := by
      rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, ht, one_mulVec]
    rw [hv]
    exact Submodule.add_mem_sup ⟨_, toLin'_apply _ _⟩ ⟨_, toLin'_apply _ _⟩
  obtain ⟨t, ht⟩ := exists_injective_add_comp _ _ hr
  refine ⟨(LinearMap.toMatrix' t)ᵀ, ?_⟩
  have hM : Function.Injective (Aᵀ + Sᵀ * LinearMap.toMatrix' t).mulVec := by
    have e : (Aᵀ + Sᵀ * LinearMap.toMatrix' t).mulVec = ⇑(toLin' Aᵀ + toLin' Sᵀ ∘ₗ t) := by
      funext v
      simp [add_mulVec, ← mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    rw [e]; exact ht
  rw [← det_transpose, transpose_add, transpose_mul, transpose_transpose, ← Matrix.isUnit_iff_isUnit_det]
  exact mulVec_injective_iff_isUnit.1 hM

theorem local_exists_isUnit_det {R n : Type} [CommRing R] [IsLocalRing R] [Fintype n] [DecidableEq n]
    (A S C D : Matrix n n R) (h : C * A + D * S = 1) : ∃ T : Matrix n n R, IsUnit (A + T * S).det := by
  set φ := IsLocalRing.residue R
  obtain ⟨τ, hτ⟩ := field_exists_isUnit_det (φ.mapMatrix A) (φ.mapMatrix S) (φ.mapMatrix C) (φ.mapMatrix D)
    (by rw [← map_mul, ← map_mul, ← map_add, h, map_one])
  obtain ⟨T, hT⟩ : ∃ T : Matrix n n R, φ.mapMatrix T = τ :=
    ⟨τ.map (Function.surjInv IsLocalRing.residue_surjective), by
      ext i j; exact Function.surjInv_eq _ _⟩
  refine ⟨T, IsUnit.of_map φ _ ?_⟩
  rw [RingHom.map_det, map_add, map_mul, hT]
  exact hτ

end GlobalTheory.StableRange

open GlobalTheory.StableRange in

theorem GlobalTheory.StableRange.exists_mem_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (A S C D : Matrix (Fin n) (Fin n) k), A ∈ intM k (Fin n) (Fin n) → S ∈ intM k (Fin n) (Fin n) →
    C ∈ intM k (Fin n) (Fin n) → D ∈ intM k (Fin n) (Fin n) → C * A + D * S = 1 →
    ∃ T ∈ intM k (Fin n) (Fin n), ∃ u ∈ KO k (Fin n), u.val = A + T * S := by
  intro k _ _ _ _ n A S C D hA hS hC hD h
  let ι := algebraMap 𝒪[k] k
  have lift : ∀ X ∈ intM k (Fin n) (Fin n), ∃ X' : Matrix (Fin n) (Fin n) 𝒪[k], ι.mapMatrix X' = X :=
    fun X hX => ⟨fun i j => ⟨X i j, hX i j⟩, rfl⟩
  obtain ⟨A', rfl⟩ := lift A hA
  obtain ⟨S', rfl⟩ := lift S hS
  obtain ⟨C', rfl⟩ := lift C hC
  obtain ⟨D', rfl⟩ := lift D hD
  have hinj : Function.Injective (ι.mapMatrix : Matrix (Fin n) (Fin n) 𝒪[k] → _) := fun X Y hXY => by
    ext i j; exact congrFun (congrFun hXY i) j
  have h' : C' * A' + D' * S' = 1 := hinj (by rw [map_add, map_mul, map_mul, map_one]; exact h)
  obtain ⟨T', hT'⟩ := local_exists_isUnit_det A' S' C' D' h'
  refine ⟨ι.mapMatrix T', fun i j => (T' i j).2,
    Matrix.GeneralLinearGroup.map ι ((Matrix.isUnit_iff_isUnit_det _).2 hT').unit, ⟨_, rfl⟩, ?_⟩
  rw [← map_mul, ← map_add]
  rfl

end
