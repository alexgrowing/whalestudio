import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerOntoStd

open GlobalTheory.AdelTranslate GlobalTheory.AdLat GlobalTheory.UnRep

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem glue_map (c : E ≃ₐ[F] E) (e : FiniteAdeleRing (𝓞 F) F) (γ : Matrix (Fin n) (Fin n) E) :
    (glue e γ).map (sg (FiniteAdeleRing (𝓞 F) F) c) = glue e (γ.map c) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [glue, fm, sg]
  · simp [glue, fm, sg, Matrix.one_apply_ne h]

theorem mul_glue_sub_one {e α : FiniteAdeleRing (𝓞 F) F} (h : α * e = 0) (γ : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (α ⊗ₜ[F] (1 : E) : RA F E) * (glue e γ - 1) i j = 0 := by
  have h0 : (α ⊗ₜ[F] (1 : E) : RA F E) * (e ⊗ₜ[F] (1 : E)) = 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, h, TensorProduct.zero_tmul]
  simp only [glue, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (fm F γ i j - (1 : Matrix (Fin n) (Fin n) (RA F E)) i j) * h0

theorem mul_idem_eq_zero {k M : ℕ} (hk : k.Coprime M) {v : HeightOneSpectrum (𝓞 F)} (hv : (M : 𝓞 F) ∈ v.asIdeal)
    {α : FiniteAdeleRing (𝓞 F) F} (hα : ∀ v', v' ≠ v → α v' = 0) : α * idem F k = 0 := by
  refine DFunLike.ext _ _ fun w => ?_
  change α w * idem F k w = 0
  by_cases h : w = v
  · subst h
    rw [idem_apply, if_neg, mul_zero]
    intro hk'
    obtain ⟨a, b, hab⟩ : IsCoprime (k : 𝓞 F) (M : 𝓞 F) := Nat.Coprime.cast hk
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (w.asIdeal.mul_mem_left a hk') (w.asIdeal.mul_mem_left b hv)))
  · rw [hα w h, zero_mul]

end General

theorem finPart_cA (D : D7) (x : AE D) :
    finPart D (cA D x) = sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (finPart D x) :=
  GlobalTheory.UnitarySplit.map_sig (sndA D.host.F) D.sp.cm.sig x

set_option maxHeartbeats 1000000 in

theorem exists_trivAt_isMov : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ M : ℕ, 0 < M → ∀ Λ ∈ Vset D.host.E S.rank M, ∃ h ∈ GfC S, TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h ∧ IsMov (fmtC S h) (stdL D.host.E S.rank) Λ := by
  rintro D S T C M - Λ ⟨-, hU', k, hk0, hkM, h1, h2⟩
  have hU : (⟨Λ⟩ : GenLat D.host.E S.rank).Unimod := (GlobalTheory.Dict.GenLatCmp.unimod_iff Λ).2 hU'
  have h₁ : ∀ x ∈ Λ, k • x ∈ stdL D.host.E S.rank := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact h1 x hx
  have h₂ : ∀ x ∈ stdL D.host.E S.rank, k • x ∈ Λ := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact h2 x hx
  obtain ⟨k', γ, hk', hγ, h₃, h₄⟩ := GlobalTheory.AdaptUnitary.exists_unitary_adapted D.host.E (hostOfRecord D) S.rank ⟨Λ⟩ k hU hk0
    (by rw [GlobalTheory.Dict.GenLatCmp.std_eq, span_smul_le_iff]; exact h₂) k hk0
  rw [GlobalTheory.Dict.GenLatCmp.std_eq] at h₃ h₄
  set c := GlobalTheory.Member.cF D with hc
  have c2 : ∀ x, c (c x) = x := fun x => star_star x
  set δ : Matrix (Fin S.rank) (Fin S.rank) D.host.E := (γ.map c)ᵀ with hδ
  have hδγ : δ * γ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← hγ i j]
    rfl
  have hγδ : γ * δ = 1 := mul_eq_one_comm.1 hδγ
  have hδc : γᵀ.map c = δ := rfl
  have h₅ : ∀ x ∈ stdL D.host.E S.rank, k' • δ *ᵥ x ∈ Λ := fun x hx => by
    obtain ⟨w, hw, e⟩ := h₄ x hx
    rwa [← Nat.cast_smul_eq_nsmul D.host.E, ← Matrix.mulVec_smul, e, Matrix.mulVec_mulVec, hδγ, Matrix.one_mulVec]
  have h₆ : ∀ x ∈ Λ, k' • γ *ᵥ x ∈ stdL D.host.E S.rank := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]
    exact h₃ x hx
  have he := idem_mul (F := D.host.F) k
  have t1 : γᵀ * δᵀ = 1 := by rw [← Matrix.transpose_mul, hδγ, Matrix.transpose_one]
  have t2 : δᵀ * γᵀ = 1 := by rw [← Matrix.transpose_mul, hγδ, Matrix.transpose_one]
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D S
  obtain ⟨h, hh, eh⟩ := lift ⟨glue (idem _ k) γᵀ, glue (idem _ k) δᵀ, glue_mul he t1, glue_mul he t2⟩ (by
    rw [C.m.gS, Matrix.transpose_one]
    refine isUnA_of c ?_
    change ((glue (idem _ k) γᵀ).map _)ᵀ * glue (idem _ k) γᵀ = 1
    rw [glue_map_sg, hδc]
    exact glue_mul he t2)
  have e1 : fmt S h = glue (idem _ k) γᵀ := congrArg Units.val eh
  have e2 : fmtC S h = glue (idem _ k) δ := by
    rw [← hδc, ← glue_map, ← e1]
    ext i j
    exact finPart_cA D _
  refine ⟨h, hh, ?_, ?_⟩
  · rintro v hv ε ⟨α, rfl, -, hα⟩ i j
    have hM : (M : 𝓞 D.host.F) ∈ v.asIdeal := hv (Ideal.mem_span_singleton_self _)
    apply GlobalTheory.UnitarySplit.parts_inj D
    · rw [map_mul, map_zero]
      have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
        change ((0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
        exact TensorProduct.zero_tmul _ _
      rw [this, zero_mul]
    · rw [map_mul, map_zero]
      have : finPart D ((mt S h - 1) i j) = (fmt S h - 1) i j := by
        rw [Matrix.sub_apply, Matrix.sub_apply, (finPart D).map_sub]
        congr 1
        by_cases hij : i = j
        · subst hij
          rw [Matrix.one_apply_eq, Matrix.one_apply_eq, (finPart D).map_one]
        · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, (finPart D).map_zero]
      rw [this, e1]
      exact mul_glue_sub_one (mul_idem_eq_zero hkM hM hα) _ i j
  · rw [e2]
    intro u
    constructor
    · intro hu
      refine ⟨_, glue_mem_hat (F := D.host.F) hk' h₆ h₁ u hu, ?_⟩
      rw [Matrix.mulVec_mulVec, glue_mul he hδγ, Matrix.one_mulVec]
    · rintro ⟨z, hz, ez⟩
      rw [ez]
      exact glue_mem_hat (F := D.host.F) hk' h₅ h₂ z hz

end GlobalTheory.KerOntoStd
