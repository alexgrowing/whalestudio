import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSeparating
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceFormMapSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenSchwartzFiniteDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubspaceAdaptedBasisChangeExistsStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

open scoped Classical

namespace GlobalTheory.CharKerSub

def projS {R : Type} [Zero R] {κ : Type} (s : Set κ) (z : κ → R) : κ → R := fun i => if i ∈ s then z i else 0

theorem projS_dot {R : Type} [CommRing R] {κ : Type} [Fintype κ] (s : Set κ) (z y : κ → R) :
    projS s z ⬝ᵥ y = z ⬝ᵥ projS s y := by
  simp only [dotProduct, projS]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

def projH {R : Type} [AddCommGroup R] {κ : Type} (s : Set κ) : (κ → R) →+ (κ → R) where
  toFun := projS s
  map_zero' := funext fun i => by simp [projS]
  map_add' a b := funext fun i => by simp only [projS, Pi.add_apply]; split_ifs <;> simp

theorem projH_apply {R : Type} [AddCommGroup R] {κ : Type} (s : Set κ) (z : κ → R) : projH s z = projS s z := rfl

theorem projS_projS {R : Type} [Zero R] {κ : Type} (s : Set κ) (z : κ → R) : projS s (projS s z) = projS s z := by
  funext i
  simp only [projS]
  split_ifs <;> rfl

theorem continuous_projS {R : Type} [AddCommGroup R] [TopologicalSpace R] {κ : Type} (s : Set κ) :
    Continuous (projS (R := R) s) := by
  refine continuous_pi fun i => ?_
  by_cases h : i ∈ s
  · simp only [projS, h, if_true]
    exact continuous_apply i
  · simp only [projS, h, if_false]
    exact continuous_const

theorem coord (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (κ : Type) [Fintype κ]
    (s : Set κ) (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (adeleClass F).adm κ)
    (hinv : ∀ v : κ → AF F, (∀ i ∉ s, v i = 0) → ∀ φ ∈ schA F κ, l (fun x => ψ (x ⬝ᵥ v) * φ x) = l φ)
    (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (h0 : ∀ x : κ → AF F, (∀ i ∈ s, x i = 0) → Φ x = 0) : l Φ = 0 := by
  obtain ⟨W, hW, hdec⟩ := GlobalTheory.T.compact_open_schwartz_finite_decomposition F κ Φ hΦ
  obtain ⟨U₀, hU₀o, hU₀c, hU₀W, -⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ W hW
  obtain ⟨U₁, hU₁o, -, hU₁U₀, hsep⟩ :=
    GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ _ (hU₀o.mem_nhds U₀.zero_mem)
  have hπc : Continuous (projH (R := Af F) s) := continuous_projS s
  let U : AddSubgroup (κ → Af F) := U₀ ⊓ U₁.comap (projH s)
  have hUo : IsOpen (U : Set (κ → Af F)) := hU₀o.inter (hU₁o.preimage hπc)
  have hUc : IsCompact (U : Set (κ → Af F)) :=
    hU₀c.inter_right ((AddSubgroup.isClosed_of_isOpen U₁ hU₁o).preimage hπc)
  obtain ⟨T, G, hG, hΦeq⟩ := hdec U hUo hUc fun x hx => hU₀W hx.1
  rw [hΦeq, map_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  have hq1 := GlobalTheory.CharForm.cosetInd_mem_SB U hUo hUc q
  by_cases hq : projS s q.out ∈ U₁
  ·
    obtain ⟨Tq, hTq⟩ := hl _ hq1
    have hmem : projS s q.out ∈ U := ⟨hU₁U₀ hq, by
      show projH s (projS s q.out) ∈ U₁
      rw [projH_apply, projS_projS]
      exact hq⟩
    have hcq : (((q.out - projS s q.out : κ → Af F)) : (κ → Af F) ⧸ U) = q := by
      conv_rhs => rw [← QuotientAddGroup.out_eq' q]
      rw [QuotientAddGroup.eq_iff_sub_mem, sub_sub_cancel_left]
      exact U.neg_mem hmem
    have hGq : ∀ X : κ → mixedEmbedding.mixedSpace F, (∀ i ∈ s, X i = 0) → G q X = 0 := by
      intro X hX
      rw [← hcq, hG _ X]
      apply h0
      intro i hi
      have hc : (q.out - projS s q.out) i = 0 := by simp [projS, hi]
      rw [hX i hi, map_zero, hc]
      exact GlobalTheory.FinSepChar.pairA_zero_zero
    let P : Submodule ℝ (κ → mixedEmbedding.mixedSpace F) :=
      { carrier := {X | ∀ i ∈ s, X i = 0}
        add_mem' := fun {a b} ha hb i hi => by simp [ha i hi, hb i hi]
        zero_mem' := fun i _ => rfl
        smul_mem' := fun r X hX i hi => by simp [hX i hi] }
    have key := GlobalTheory.SchwartzHadamard.eq_of_eqOn P Tq ?_ (G q) 0
      (fun p hp => by rw [hGq p hp, zero_apply])
    · rw [hTq, key, map_zero]
    intro L hL f g hfg
    rw [← hTq, ← hTq]
    obtain ⟨Y, hY⟩ := GlobalTheory.TraceDual.exists_trace_rep F κ (LinearMap.toContinuousLinearMap ((-(2 * Real.pi)) • L))
    let Y' : κ → mixedEmbedding.mixedSpace F := projS s Y
    have hLY : ∀ X, L X = ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y' i) := by
      intro X
      have hsplit : L X = L (projS s X) := by
        have hm : X - projS s X ∈ P := fun i hi => by simp [projS, hi]
        have := hL _ hm
        rw [map_sub, sub_eq_zero] at this
        exact this
      have h2 := hY (projS s X)
      simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.smul_apply, smul_eq_mul] at h2
      have hpi : -(2 * Real.pi) ≠ 0 := by have := Real.pi_pos; linarith
      rw [hsplit, mul_left_cancel₀ hpi h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [projS, Y']
      split_ifs <;> simp
    have hv : ∀ i ∉ s, (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y' i)) 0) i = 0 :=
      fun i hi => by
        simp only [Y', projS, if_neg hi, map_zero]
        rfl
    have hchar : ∀ x : κ → AF F, ψ (x ⬝ᵥ fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y' i)) 0) =
        GlobalTheory.ArchSch.ech (L fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) := by
      intro x
      rw [GlobalTheory.CharInvForm.psi_dot_inf hψ, hLY, GlobalTheory.ArchSch.ech]
      congr 1
      push_cast
      ring
    rw [← hinv _ hv _ (GlobalTheory.CharInvForm.mem_schA f hq1)]
    congr 1
    funext x
    simp only [pureA, hfg, hchar]
    ring
  ·
    obtain ⟨y, hyU, hy⟩ := hsep _ hq
    have hv : ∀ i ∉ s, (fun i => pairA F 0 (projS s y i)) i = 0 := fun i hi => by
      simp only [projS, if_neg hi]
      exact GlobalTheory.FinSepChar.pairA_zero_zero
    have hmul : (fun x => ψ (x ⬝ᵥ fun i => pairA F 0 (projS s y i)) * pureA F (G q) (GlobalTheory.CharForm.cosetInd U q) x) =
        ψ (pairA F 0 (projS s q.out ⬝ᵥ y)) • pureA F (G q) (GlobalTheory.CharForm.cosetInd U q) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, pureA, GlobalTheory.CharForm.cosetInd]
      split_ifs with hx
      · have hm : -q.out + (fun i => (x i).2) ∈ U := by
          rw [← QuotientAddGroup.out_eq' q] at hx
          exact QuotientAddGroup.eq.mp hx.symm
        have hdot : (x ⬝ᵥ fun i => pairA F 0 (projS s y i)) =
            pairA F 0 (projS s q.out ⬝ᵥ y) + pairA F 0 (projS s (-q.out + fun i => (x i).2) ⬝ᵥ y) := by
          have hadd : projS s q.out + projS s (-q.out + fun i => (x i).2) = projS s (fun i => (x i).2) := by
            have := (projH (R := Af F) s).map_add q.out (-q.out + fun i => (x i).2)
            rw [add_neg_cancel_left] at this
            exact this.symm
          rw [← GlobalTheory.CharInvForm.pairA_zero_add, ← add_dotProduct, hadd, projS_dot, GlobalTheory.CharInvForm.dot_pairA_fin]
        have h1 : ψ (pairA F 0 (projS s (-q.out + fun i => (x i).2) ⬝ᵥ y)) = 1 := hyU _ hm.2
        rw [hdot, AddChar.map_add_eq_mul, h1, mul_one]
      · simp
    have e := hinv _ hv _ (GlobalTheory.CharInvForm.mem_schA (G q) hq1)
    rw [hmul, map_smul, smul_eq_mul] at e
    have h3 : (ψ (pairA F 0 (projS s q.out ⬝ᵥ y)) - 1) * l (pureA F (G q) (GlobalTheory.CharForm.cosetInd U q)) = 0 := by
      rw [sub_mul, e, one_mul, sub_self]
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hy)

theorem schr_zero_fst {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (φ : (κ → AF F) → ℂ) : schr ψ (0, w) φ = fun x => ψ (x ⬝ᵥ w) * φ x := by
  funext x
  simp [schr]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (Y₀ : Submodule F (κ → F)),
    ∀ l ∈ (adeleClass F).adm κ,
    (∀ (t : AF F), ∀ y ∈ Y₀, ∀ φ ∈ schA F κ, l (schr ψ (0, t • fun i => algebraMap F (AF F) (y i)) φ) = l φ) →
    ∀ Φ ∈ schA F κ, (∀ x : κ → AF F, (∀ y ∈ Y₀, x ⬝ᵥ (fun i => algebraMap F (AF F) (y i)) = 0) → Φ x = 0) → l Φ = 0 := by
  intro F _ _ ψ hψ κ _ Y₀ l hl hinv Φ hΦ h0
  obtain ⟨P, hP, s, hrow, hspan⟩ := GlobalTheory.T.subspace_adapted_basis_change_exists F κ Y₀
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  let Pm : Matrix κ κ (AF F) := P.map (algebraMap F (AF F))
  let Qm : Matrix κ κ (AF F) := P⁻¹.map (algebraMap F (AF F))
  have e1 : Pm * Qm = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : Qm * Pm = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  have hl' : l ∘ₗ GlobalTheory.AdelicSvNLevi.compM P ∈ (adeleClass F).adm κ := by
    intro g hg
    obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (GlobalTheory.AdelicSvNLevi.finHomeo P P⁻¹ h1 h2).continuous,
      hg.2.comp_homeomorph (GlobalTheory.AdelicSvNLevi.finHomeo P P⁻¹ h1 h2)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (GlobalTheory.AdelicSvNLevi.archEquiv P P⁻¹ h1 h2)),
      fun f => ?_⟩
    rw [LinearMap.comp_apply, GlobalTheory.AdelicSvNLevi.comp_pureA P P⁻¹ h1 h2, hT]
    rfl
  have key := coord F ψ hψ κ s _ hl' ?_ _ (GlobalTheory.AdelicSvNLevi.comp_mem P⁻¹ P h2 h1 Φ hΦ) ?_
  · have hc : GlobalTheory.AdelicSvNLevi.compM P (GlobalTheory.AdelicSvNLevi.compM P⁻¹ Φ) = Φ := by
      funext x
      change Φ (Qm *ᵥ (Pm *ᵥ x)) = Φ x
      rw [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
    rw [LinearMap.comp_apply, hc] at key
    exact key
  · intro v hv φ hφ
    have hgood : ∀ φ ∈ schA F κ, l (schr ψ (0, ∑ i, v i • Pm i) φ) = l φ := by
      refine Finset.sum_induction (fun i => v i • Pm i) (fun w => ∀ φ ∈ schA F κ, l (schr ψ (0, w) φ) = l φ)
        (fun a b ha hb φ hφ => ?_) (fun φ _ => ?_) fun i _ φ hφ => ?_
      · have hs : schr ψ (0, a + b) φ = schr ψ (0, a) (schr ψ (0, b) φ) := by
          funext x
          simp only [schr_zero_fst, dotProduct_add, AddChar.map_add_eq_mul, mul_assoc]
        rw [hs, ha _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), hb φ hφ]
      · simp only [schr_zero_fst, dotProduct_zero, AddChar.map_zero_eq_one, one_mul]
      · by_cases hi : i ∈ s
        · exact hinv (v i) (P i) (hrow i hi) φ hφ
        · simp only [hv i hi, zero_smul, schr_zero_fst, dotProduct_zero, AddChar.map_zero_eq_one, one_mul]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hgood _ (GlobalTheory.AdelicSvNLevi.comp_mem P P⁻¹ h1 h2 φ hφ),
      schr_zero_fst]
    congr 1
    funext x
    change ψ ((Pm *ᵥ x) ⬝ᵥ v) * φ (Pm *ᵥ x) = ψ (x ⬝ᵥ ∑ i, v i • Pm i) * φ (Pm *ᵥ x)
    have hs : ∑ i, v i • Pm i = v ᵥ* Pm := (Matrix.vecMul_eq_sum v Pm).symm
    rw [hs, dotProduct_comm x, ← Matrix.dotProduct_mulVec, dotProduct_comm]
  · intro z hz
    refine h0 (Qm *ᵥ z) fun y hy => ?_
    obtain ⟨c, hc, rfl⟩ := hspan y hy
    have hm : (fun i => algebraMap F (AF F) ((c ᵥ* P) i)) = (fun i => algebraMap F (AF F) (c i)) ᵥ* Pm :=
      funext fun i => RingHom.map_vecMul _ _ _ _
    rw [hm, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ s
    · rw [hz i hi, mul_zero]
    · simp only [hc i hi, map_zero, zero_mul]

end GlobalTheory.CharKerSub
