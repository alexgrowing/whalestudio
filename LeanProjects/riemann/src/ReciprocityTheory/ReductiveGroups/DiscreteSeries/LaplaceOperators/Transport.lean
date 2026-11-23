import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportGeo
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace NNReal ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

namespace Transport

theorem uh_mul {k r : ℕ} {a b : Mat k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) :
    a * b ∈ UH (Hpk k r) := by
  exact (Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) (Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r)).2.1 a ha b hb

theorem uh_facts {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {a : Mat k r} (ha : a ∈ UH (Hpk k r)) :
    IsUnit a.det ∧ a⁻¹ ∈ UH (Hpk k r) ∧ Formalism.REAL.inUJ ε (P * a * P⁻¹) := by
  have hG := (Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) (Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r)).2.2 a ha
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  exact ⟨hG.1, hG.2, (Formalism.QuantumDeterminants.uHConj _ ε (Hpk k r) P hPd hP.2 a).1 ha⟩

theorem conj_mem_uh {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {g : Mat k r} (hg : Formalism.REAL.inUJ ε g) : P⁻¹ * g * P ∈ UH (Hpk k r) := by
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  rw [Formalism.QuantumDeterminants.uHConj _ ε (Hpk k r) P hPd hP.2]
  have h : P * (P⁻¹ * g * P) * P⁻¹ = g := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPd, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hPd]
  rw [h]
  exact hg

theorem aaFun_cayley {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ}
    {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (T : S7.KType ε Λ) (μ : Fin (2 * r + k + 1) → ℤ) {P P' : Mat k r}
    (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hP' : Formalism.MainNotions.S.IsCayley k r ε P')
    (μW μN : Measure (Mt k r)) (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp))
    (v₁ v₂ : T.V) (ξ : Vp) (x₀ x : Mat k r) :
    P⁻¹ * P' ∈ UH (Hpk k r) ∧
      aaFun T μ P' μW μN ψ π v₁ v₂ ξ x₀ x =
        aaFun T μ P μW μN ψ π v₁ v₂ ξ (x₀ * (P⁻¹ * P')⁻¹) (x * (P⁻¹ * P')⁻¹) := by
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hP'd : IsUnit P'.det := (Matrix.isUnit_iff_isUnit_det P').1 hP'.1
  have hb : P⁻¹ * P' ∈ UH (Hpk k r) := by
    have h1 : ∀ X : Mat k r, (P⁻¹)ᴴ * (Pᴴ * X) = X := by
      intro X
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hPd,
        Matrix.conjTranspose_one, Matrix.one_mul]
    show (P⁻¹ * P')ᴴ * Hpk k r * (P⁻¹ * P') = Hpk k r
    nth_rewrite 1 [← hP.2]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hPd, h1]
    rw [← hP'.2, Matrix.mul_assoc]
  have hbd : IsUnit (P⁻¹ * P').det := by
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det P hPd).mul hP'd
  have key : ∀ Y : Mat k r, P' * (x₀⁻¹ * (Y * x)) * P'⁻¹ =
      P * ((x₀ * (P⁻¹ * P')⁻¹)⁻¹ * (Y * (x * (P⁻¹ * P')⁻¹))) * P⁻¹ := by
    intro Y
    rw [Matrix.mul_inv_rev x₀, Matrix.nonsing_inv_nonsing_inv _ hbd, Matrix.mul_inv_rev P⁻¹ P',
      Matrix.nonsing_inv_nonsing_inv _ hPd]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPd, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hPd]
  refine ⟨hb, ?_⟩
  simp only [aaFun, sInt, psiCoef, key]

theorem psiM_iso {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T T' : S7.KType ε Λ) :
    ∃ U : T.V ≃ₗᵢ[ℂ] T'.V, ∀ (μ : Fin n → ℤ) (g : Matrix (Fin n) (Fin n) ℂ) (v : T.V),
      S7.PsiM T' μ g (U v) = U (S7.PsiM T μ g v) := by
  obtain ⟨φ, hφK, -, hφw⟩ := HW.kType_unique T T'
  let C : (T.V →L[ℂ] T.V) ≃L[ℂ] (T'.V →L[ℂ] T'.V) :=
    ContinuousLinearEquiv.arrowCongr φ.toContinuousLinearEquiv φ.toContinuousLinearEquiv
  have hC : ∀ (A : T.V →L[ℂ] T.V) (v : T.V), C A (φ v) = φ (A v) := by
    intro A v
    simp [C, ContinuousLinearEquiv.arrowCongr_apply]
  have hop : ∀ k : S7.KG ε, C (T.op k) = T'.op k := by
    intro k
    ext w
    obtain ⟨v, rfl⟩ := φ.surjective w
    rw [hC, hφK]
  have hproj : C (S7.projW T) = S7.projW T' := by
    ext w
    obtain ⟨v, rfl⟩ := φ.surjective w
    rw [hC]
    simp only [S7.projW, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul, hφw]
    rw [← hφw, LinearIsometryEquiv.inner_map_map]
  have hmul : ∀ A B : T.V →L[ℂ] T.V, C (A * B) = C A * C B := by
    intro A B
    ext w
    obtain ⟨v, rfl⟩ := φ.surjective w
    simp only [ContinuousLinearMap.mul_apply, hC]
  have hfin : Module.finrank ℂ T'.V = Module.finrank ℂ T.V :=
    (φ.toLinearEquiv.finrank_eq).symm
  have hps : ∀ (μ : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ), S7.psM T' μ x = C (S7.psM T μ x) := by
    intro μ x
    unfold S7.psM
    rw [map_smul, ← ContinuousLinearEquiv.integral_comp_comm, hfin]
    congr 2
    funext k
    rw [map_smul, hmul, hmul, hop, hproj, hop]
  have hPsi : ∀ (μ : Fin n → ℤ) (g : Matrix (Fin n) (Fin n) ℂ), S7.PsiM T' μ g = C (S7.PsiM T μ g) := by
    intro μ g
    unfold S7.PsiM
    split_ifs with h
    · rw [hmul, hop, hps]
    · simp
  refine ⟨φ, fun μ g v => ?_⟩
  rw [hPsi, hC]

theorem uw_closedSubgroup (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Formalism.FourierDecayAlt.B2.IsClosedSubgroup (UWset k r z) := by
  have hG := Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) (Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [UWset, Set.mem_setOf_eq, Matrix.one_mulVec]
    exact ⟨hG.1, by simp⟩
  · intro g hg h hh
    simp only [UWset, Set.mem_setOf_eq] at hg hh ⊢
    obtain ⟨hg1, hg2, hg3⟩ := hg
    obtain ⟨hh1, hh2, hh3⟩ := hh
    refine ⟨hG.2.1 g hg1 h hh1, fun a => ⟨?_, ?_⟩, ?_⟩
    · rw [← Matrix.mulVec_mulVec, (hh2 a).1, (hg2 a).1]
    · rw [← Matrix.mulVec_mulVec, (hh2 a).2, (hg2 a).2]
    · rw [← Matrix.mulVec_mulVec, hh3, hg3]
  · intro g hg
    simp only [UWset, Set.mem_setOf_eq] at hg ⊢
    obtain ⟨hg1, hg2, hg3⟩ := hg
    have hu := (hG.2.2 g hg1).1
    have key : ∀ v, g *ᵥ v = v → g⁻¹ *ᵥ v = v := by
      intro v hv
      conv_lhs => rw [← hv]
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    exact ⟨(hG.2.2 g hg1).2, fun a => ⟨key _ (hg2 a).1, key _ (hg2 a).2⟩, key _ hg3⟩
  · intro g hg
    simp only [UWset, Set.mem_setOf_eq] at hg
    exact (hG.2.2 g hg.1).1
  · have hA : IsClosed (UH (Hpk k r)) :=
      isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
        continuous_id) continuous_const
    have hB : IsClosed {g : Mat k r | ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
        g *ᵥ bvec (esI k r a) = bvec (esI k r a)} := by
      simp only [Set.setOf_forall, Set.setOf_and]
      exact isClosed_iInter fun a =>
        (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
          (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
    have hC : IsClosed {g : Mat k r | g *ᵥ z = z} :=
      isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
    exact hA.inter (hB.inter hC)

theorem n_closedSubgroup (k r : ℕ) : Formalism.FourierDecayAlt.B2.IsClosedSubgroup (Nset k r) := Formalism.FourierDecayAlt.P.B2x2.closedN k r

theorem haar_unique {k r : ℕ} {S : Set (Mat k r)} (hS : Formalism.FourierDecayAlt.B2.IsClosedSubgroup S)
    (hex : ∃ μ₀ : Measure (Mt k r), Formalism.FourierDecayAlt.B.IsHaarOn S μ₀) {μ μ' : Measure (Mt k r)}
    (hμ : Formalism.MainNotions.S.IsHaarOn S μ) (hμ' : Formalism.MainNotions.S.IsHaarOn S μ') :
    ∃ κ : ℝ, 0 < κ ∧ μ = ENNReal.ofReal κ • μ' := by
  obtain ⟨μ₀, h₀⟩ := hex
  obtain ⟨c, hc, hμc⟩ := ReciprocityTheory.ChartRestriction.DS.Mult1.haarUniqueSF' k r S μ₀ μ hS h₀ hμ
  obtain ⟨c', hc', hμc'⟩ := ReciprocityTheory.ChartRestriction.DS.Mult1.haarUniqueSF' k r S μ₀ μ' hS h₀ hμ'
  refine ⟨((c / c' : ℝ≥0) : ℝ), NNReal.coe_pos.2 (div_pos (pos_iff_ne_zero.2 hc) (pos_iff_ne_zero.2 hc')), ?_⟩
  rw [hμc, hμc', ENNReal.smul_def c, ENNReal.smul_def c', smul_smul, ENNReal.ofReal_coe_nnreal,
    ← ENNReal.coe_mul, div_mul_cancel₀ c hc']

def conjEquiv {k r : ℕ} (a : Mat k r) (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun := conjM a
  invFun := conjM a⁻¹
  left_inv x := by
    show a⁻¹ * (a * Matrix.of x * a⁻¹) * a⁻¹⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv a ha]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ ha, Matrix.nonsing_inv_mul _ ha,
      Matrix.mul_one]
  right_inv x := by
    show a * (a⁻¹ * Matrix.of x * a⁻¹⁻¹) * a⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv a ha]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ ha, Matrix.mul_nonsing_inv _ ha,
      Matrix.mul_one]
  measurable_toFun := by
    have hc : Continuous (conjM (k := k) (r := r) a) := by
      unfold conjM
      exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact hc.measurable
  measurable_invFun := by
    have hc : Continuous (conjM (k := k) (r := r) a⁻¹) := by
      unfold conjM
      exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact hc.measurable

theorem haar_conj {k r : ℕ} {S S' : Set (Mat k r)} {a : Mat k r} (ha : IsUnit a.det)
    (hSS : ∀ h, h ∈ S ↔ a * h * a⁻¹ ∈ S') {μ : Measure (Mt k r)} (hμ : Formalism.MainNotions.S.IsHaarOn S μ) :
    Formalism.MainNotions.S.IsHaarOn S' (Measure.map (conjM a) μ) := by
  have hmeas : Measurable (conjM (k := k) (r := r) a) := (conjEquiv a ha).measurable
  have hmapeq : Measure.map (conjM a) μ = Measure.map (conjEquiv a ha) μ := rfl
  obtain ⟨hsf, hne, hnull, hleft⟩ := hμ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmapeq]
    exact MeasurableEquiv.sigmaFinite_map _
  · exact (Measure.map_ne_zero_iff hmeas.aemeasurable).2 hne
  · have hpre : (conjEquiv a ha) ⁻¹' {x | Matrix.of x ∉ S'} = {x | Matrix.of x ∉ S} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [hSS (Matrix.of x)]
      exact Iff.rfl
    rw [hmapeq, MeasurableEquiv.map_apply, hpre]
    exact hnull
  · intro s hs
    have hs' : a⁻¹ * s * a ∈ S := by
      rw [hSS]
      have h : a * (a⁻¹ * s * a) * a⁻¹ = s := by
        simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.mul_one,
          Matrix.mul_nonsing_inv_cancel_left _ _ ha]
      rw [h]
      exact hs
    have hl : ∀ b : Mat k r, Measurable (lmulM (k := k) (r := r) b) := by
      intro b
      have hc : Continuous (lmulM (k := k) (r := r) b) := by
        unfold lmulM
        exact continuous_const.matrix_mul continuous_id
      exact hc.measurable
    have hcomp : lmulM s ∘ conjM a = conjM a ∘ lmulM (a⁻¹ * s * a) := by
      funext x
      show s * (a * Matrix.of x * a⁻¹) = a * (a⁻¹ * s * a * Matrix.of x) * a⁻¹
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ ha]
    rw [Measure.map_map (hl s) hmeas, hcomp, ← Measure.map_map hmeas (hl _), hleft _ hs']

theorem conj_data {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {c c' : Fin r → ℂ}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hc : ∀ a, c a ≠ 0)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hc' : ∀ a, c' a ≠ 0) :
    ∃ a : Mat k r, a ∈ UH (Hpk k r) ∧ IsUnit a.det ∧
      (∀ h, h ∈ UWset k r z ↔ a * h * a⁻¹ ∈ UWset k r z') ∧
      (∀ m, m ∈ Nset k r ↔ a * m * a⁻¹ ∈ Nset k r) ∧
      (∀ m ∈ Nset k r, Formalism.MainNotions.S.psiGen k r z' c' (a * m * a⁻¹) = Formalism.MainNotions.S.psiGen k r z c m) ∧
      (∀ g, Formalism.MainNotions.S.IsFrameW k r z g → ∃ g', Formalism.MainNotions.S.IsFrameW k r z' g' ∧
        ∀ h, a * (g * Formalism.MainNotions.S.blockW k r h * g⁻¹) * a⁻¹ = g' * Formalism.MainNotions.S.blockW k r h * g'⁻¹) := TransportGeo.conj_data hz hT hc hz' hT' hc'

theorem pi_conj {k r : ℕ} {u : Fin k → ℝ}
    {Vp Vp' : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [NormedAddCommGroup Vp']
    [InnerProductSpace ℂ Vp'] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Vp →L[ℂ] Vp)}
    {π' : Mat k r → (Vp' →L[ℂ] Vp')} {a : Mat k r} (ha : IsUnit a.det)
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hz' : inWb k r z') (hT' : 0 < Tz k r z')
    (hUW : ∀ h, h ∈ UWset k r z ↔ a * h * a⁻¹ ∈ UWset k r z')
    (hfr : ∀ g, Formalism.MainNotions.S.IsFrameW k r z g → ∃ g', Formalism.MainNotions.S.IsFrameW k r z' g' ∧
      ∀ h, a * (g * Formalism.MainNotions.S.blockW k r h * g⁻¹) * a⁻¹ = g' * Formalism.MainNotions.S.blockW k r h * g'⁻¹)
    (hπ : Formalism.MainNotions.S.IsHCTypeW k r z u π) (hπ' : Formalism.MainNotions.S.IsHCTypeW k r z' u π') :
    ∃ U : Vp ≃ₗᵢ[ℂ] Vp', ∀ h ∈ UWset k r z, ∀ ξ : Vp, π' (a * h * a⁻¹) (U ξ) = U (π h ξ) := TransportGeo.pi_conj ha hz hT hz' hT' hUW hfr hπ hπ'

theorem aaFun_data {k r : ℕ} {u : Fin k → ℝ}
    {Vp Vp' : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    [NormedAddCommGroup Vp'] [InnerProductSpace ℂ Vp'] [CompleteSpace Vp']
    {z z' : Fin (2 * r + k + 1) → ℂ} {c c' : Fin r → ℂ} {π : Mat k r → (Vp →L[ℂ] Vp)}
    {π' : Mat k r → (Vp' →L[ℂ] Vp')} {μW μN μW' μN' : Measure (Mt k r)}
    (hB : IsBData z c u π μW μN) (hB' : IsBData z' c' u π' μW' μN') :
    ∃ (a : Mat k r) (U : Vp ≃ₗᵢ[ℂ] Vp') (κ : ℝ), a ∈ UH (Hpk k r) ∧ 0 < κ ∧
      ∀ (ε : Fin (2 * r + k + 1) → Bool) (Λ : Fin (2 * r + k + 1) → ℝ) (T : S7.KType ε Λ)
        (μ : Fin (2 * r + k + 1) → ℤ) (P : Mat k r) (v₁ v₂ : T.V) (ξ : Vp) (x₀ x : Mat k r),
        aaFun T μ P μW' μN' (Formalism.MainNotions.S.psiGen k r z' c') π' v₁ v₂ (U ξ) x₀ x =
          κ • U (aaFun T μ P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v₁ v₂ ξ (a⁻¹ * x₀) (a⁻¹ * x)) := by
  obtain ⟨hz, hT, hc, hπ, hW, hN⟩ := hB
  obtain ⟨hz', hT', hc', hπ', hW', hN'⟩ := hB'
  obtain ⟨a, ha, had, hUW, hNN, hψ, hfr⟩ := conj_data hz hT hc hz' hT' hc'
  obtain ⟨U, hU⟩ := pi_conj had hz hT hz' hT' hUW hfr hπ hπ'
  obtain ⟨κW, hκW, hWeq⟩ := haar_unique (uw_closedSubgroup k r z')
    (Formalism.FourierDecayAlt.P.weyl_haar_exists k r z' hz' hT') (haar_conj had hUW hW) hW'
  obtain ⟨κN, hκN, hNeq⟩ := haar_unique (n_closedSubgroup k r)
    (Formalism.FourierDecayAlt.P.unipotent_haar_exists k r) (haar_conj had hNN hN) hN'
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have : SigmaFinite μW' := hW'.1
  have : SigmaFinite μN' := hN'.1
  let e := conjEquiv a had
  have he : ∀ y, e y = conjM a y := fun _ => rfl
  have hinvW := (uw_closedSubgroup k r z).inv_mem
  refine ⟨a, U, (κW * κN)⁻¹, ha, by positivity, ?_⟩
  intro ε Λ T μ P v₁ v₂ ξ x₀ x
  have hprod : (Measure.map (conjM a) μW).prod (Measure.map (conjM a) μN) =
      Measure.map (Prod.map (conjM a) (conjM a)) (μW.prod μN) :=
    Measure.map_prod_map μW μN e.measurable e.measurable
  rw [hWeq, hNeq, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul] at hprod
  have hWae : ∀ᵐ y ∂μW, Matrix.of y ∈ UWset k r z := by
    rw [ae_iff]; simpa using hW.2.2.1
  have hNae : ∀ᵐ y ∂μN, Matrix.of y ∈ Nset k r := by
    rw [ae_iff]; simpa using hN.2.2.1
  have hpae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  have hE : MeasurableEmbedding (Prod.map (conjM (k := k) (r := r) a) (conjM a)) :=
    (MeasurableEquiv.prodCongr e e).measurableEmbedding
  have hmain : ((ENNReal.ofReal κW * ENNReal.ofReal κN).toReal) •
      aaFun T μ P μW' μN' (Formalism.MainNotions.S.psiGen k r z' c') π' v₁ v₂ (U ξ) x₀ x =
      U (aaFun T μ P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v₁ v₂ ξ (a⁻¹ * x₀) (a⁻¹ * x)) := by
    unfold aaFun sInt
    have hUint : ∀ f : Mt k r × Mt k r → Vp,
        ∫ p, U (f p) ∂(μW.prod μN) = U (∫ p, f p ∂(μW.prod μN)) :=
      fun f => U.toLinearIsometry.integral_comp_comm f
    rw [← integral_smul_measure, hprod, hE.integral_map, ← hUint]
    refine integral_congr_ae ?_
    filter_upwards [hpae] with p hp
    have hof : ∀ y : Mt k r, Matrix.of (conjM a y) = a * Matrix.of y * a⁻¹ := fun _ => rfl
    simp only [Prod.map_fst, Prod.map_snd, hof, LinearIsometryEquiv.map_smul]
    have hmat : x₀⁻¹ * (a * Matrix.of p.1 * a⁻¹ * (a * Matrix.of p.2 * a⁻¹) * x) =
        (a⁻¹ * x₀)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * (a⁻¹ * x)) := by
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv a had]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ had]
    have hinv : (a * Matrix.of p.1 * a⁻¹)⁻¹ = a * (Matrix.of p.1)⁻¹ * a⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv a had, Matrix.mul_assoc]
    rw [hmat]
    congr 1
    unfold chiInv
    rw [hψ _ hp.2, hinv, hU _ (hinvW _ hp.1), LinearIsometryEquiv.map_smul]
  have hc0 : (ENNReal.ofReal κW * ENNReal.ofReal κN).toReal = κW * κN := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hκW.le, ENNReal.toReal_ofReal hκN.le]
  rw [hc0] at hmain
  rw [← hmain, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

theorem aaFun_K {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} {u : Fin k → ℝ}
    {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (T : S7.KType ε Λ) (μ : Fin (2 * r + k + 1) → ℤ) {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {π : Mat k r → (Vp →L[ℂ] Vp)} {μW μN : Measure (Mt k r)}
    (hB : IsBData z c u π μW μN) (k₁ k₂ : S7.KG ε) (w₁ w₂ : T.V) (ξ : Vp) {x₀ x : Mat k r}
    (hx₀ : x₀ ∈ UH (Hpk k r)) (hx : x ∈ UH (Hpk k r)) :
    aaFun T μ P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (T.op k₁ w₁) (T.op k₂ w₂) ξ x₀ x =
      aaFun T μ P μW μN (Formalism.MainNotions.S.psiGen k r z c) π w₁ w₂ ξ
        (x₀ * (P⁻¹ * S7.toMK k₂ * P)) (x * (P⁻¹ * S7.toMK k₁ * P)) := by
  obtain ⟨-, -, -, -, hW, hN⟩ := hB
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hWae : ∀ᵐ y ∂μW, Matrix.of y ∈ UWset k r z := by
    rw [ae_iff]; simpa using hW.2.2.1
  have hNae : ∀ᵐ y ∂μN, Matrix.of y ∈ Nset k r := by
    rw [ae_iff]; simpa using hN.2.2.1
  have hprod : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  have hK2 : (S7.toMK k₂)⁻¹ = S7.toMK k₂⁻¹ := Matrix.inv_eq_left_inv (S7.toMK_inv_mul' k₂)
  have hB2 : (P⁻¹ * S7.toMK k₂ * P)⁻¹ = P⁻¹ * S7.toMK k₂⁻¹ * P := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hd, hK2, Matrix.mul_assoc]
  have hinner : ∀ a b : T.V, ⟪T.op k₂ a, b⟫_ℂ = ⟪a, T.op k₂⁻¹ b⟫_ℂ := by
    intro a b
    have hb : b = T.op k₂ (T.op k₂⁻¹ b) := by
      rw [← ContinuousLinearMap.mul_apply, ← S7.op_mul', mul_inv_cancel, S7.op_one']
      rfl
    conv_lhs => rw [hb]
    exact ContinuousLinearMap.inner_map_map_of_mem_unitary (T.τ k₂).property a _
  unfold aaFun sInt
  refine integral_congr_ae ?_
  filter_upwards [hprod] with p hp
  have hs : Matrix.of p.1 * Matrix.of p.2 * x ∈ UH (Hpk k r) := uh_mul (uh_mul hp.1.1 hp.2.1) hx
  have hg : x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x) ∈ UH (Hpk k r) :=
    uh_mul (uh_facts hP hx₀).2.1 hs
  have hJ := (uh_facts hP hg).2.2
  congr 1
  unfold psiCoef
  rw [hinner]
  have key : S7.toMK k₂⁻¹ * (P * (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹) * S7.toMK k₁ =
      P * ((x₀ * (P⁻¹ * S7.toMK k₂ * P))⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * (x * (P⁻¹ * S7.toMK k₁ * P)))) *
        P⁻¹ := by
    rw [Matrix.mul_inv_rev, hB2]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, Matrix.mul_nonsing_inv _ hd,
      Matrix.mul_one]
  rw [← key, S7.psiM_equiv T μ k₂⁻¹ k₁ hJ]
  rfl

def IntCoefStatement : Prop :=
  ∀ (k r : ℕ), 1 ≤ k → ∀ (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ), GapLap ε lam h →
  ∀ (u : Fin k → ℝ) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ), S7.IsMu lam μ →
  ∀ (P : Mat k r), Formalism.MainNotions.S.IsCayley k r ε P →
  ∀ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN : Measure (Mt k r)),
    IsBData z c u π μW μN → ∀ (v₁ v₂ : T.V) (ξ : Vp) (x₀ x : Mat k r), x₀ ∈ UH (Hpk k r) → x ∈ UH (Hpk k r) →
    Integrable (fun p : Mt k r × Mt k r =>
      psiCoef T μ P v₁ v₂ (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) (μW.prod μN)

theorem transport (hIC : IntCoefStatement) {k r : ℕ} (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {u : Fin k → ℝ} {h : ℝ} (hgap : GapLap ε lam h) :
    BesselNZ ε lam u → BesselAll ε lam u := by
  rintro ⟨T₀, μ₀, P₀, z₀, c₀, Vp₀, i₁, i₂, i₃, π₀, μW₀, μN₀, hμ₀, hP₀, hB₀, v₁, v₂, ξ₀, y₀, y, hy₀, hy, hne⟩
  intro T μ P z c Vp _ _ _ π μW μN hμ hP hB v hv
  have hμeq : μ = μ₀ := by
    funext a
    have h := (hμ a).trans (hμ₀ a).symm
    exact_mod_cast h
  subst hμeq

  obtain ⟨hb, hcay⟩ := aaFun_cayley T₀ μ hP₀ hP μW₀ μN₀ (Formalism.MainNotions.S.psiGen k r z₀ c₀) π₀ v₁ v₂ ξ₀
    (y₀ * (P₀⁻¹ * P)) (y * (P₀⁻¹ * P))
  have hbd := (uh_facts hP hb).1
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ hbd, Matrix.mul_nonsing_inv_cancel_right _ _ hbd] at hcay
  rw [← hcay] at hne

  obtain ⟨a, U, κ, ha, hκ, hdata⟩ := aaFun_data hB₀ hB
  have had := (uh_facts hP ha).1
  have hne2 : aaFun T₀ μ P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v₁ v₂ (U ξ₀)
      (a * (y₀ * (P₀⁻¹ * P))) (a * (y * (P₀⁻¹ * P))) ≠ 0 := by
    rw [hdata, Matrix.nonsing_inv_mul_cancel_left _ _ had, Matrix.nonsing_inv_mul_cancel_left _ _ had]
    exact smul_ne_zero (by exact_mod_cast hκ.ne') (fun h0 => hne (U.injective (by rw [h0, map_zero])))
  have hX₀ : a * (y₀ * (P₀⁻¹ * P)) ∈ UH (Hpk k r) := uh_mul ha (uh_mul hy₀ hb)
  have hX : a * (y * (P₀⁻¹ * P)) ∈ UH (Hpk k r) := uh_mul ha (uh_mul hy hb)

  obtain ⟨U₁, hU₁⟩ := psiM_iso T₀ T
  have hne3 : aaFun T μ P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (U₁ v₁) (U₁ v₂) (U ξ₀)
      (a * (y₀ * (P₀⁻¹ * P))) (a * (y * (P₀⁻¹ * P))) ≠ 0 := by
    convert hne2 using 1
    unfold aaFun sInt psiCoef
    congr 1
    funext p
    simp only [hU₁, LinearIsometryEquiv.inner_map_map]

  set ψ := Formalism.MainNotions.S.psiGen k r z c with hψ
  let F : T.V → T.V → Vp → Mat k r → Mat k r → Mt k r × Mt k r → Vp := fun w₁ w₂ ξ Y₀ Y p =>
    psiCoef T μ P w₁ w₂ (Y₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Y)) •
      chiInv ψ π (Matrix.of p.1) (Matrix.of p.2) ξ
  have hA : ∀ w₁ w₂ ξ Y₀ Y, aaFun T μ P μW μN ψ π w₁ w₂ ξ Y₀ Y = ∫ p, F w₁ w₂ ξ Y₀ Y p ∂(μW.prod μN) :=
    fun _ _ _ _ _ => rfl
  have hint : ∀ w₁ w₂ ξ {Y₀ Y : Mat k r}, Y₀ ∈ UH (Hpk k r) → Y ∈ UH (Hpk k r) →
      Integrable (F w₁ w₂ ξ Y₀ Y) (μW.prod μN) :=
    fun w₁ w₂ ξ _ _ h₀ h₁ => hIC k r hk ε lam h hgap u Vp T μ hμ P hP z c π μW μN hB w₁ w₂ ξ _ _ h₀ h₁
  have hlin₁ : ∀ (b : ℂ) (w w' w₂ : T.V) ξ {Y₀ Y : Mat k r}, Y₀ ∈ UH (Hpk k r) → Y ∈ UH (Hpk k r) →
      aaFun T μ P μW μN ψ π (b • w + w') w₂ ξ Y₀ Y =
        b • aaFun T μ P μW μN ψ π w w₂ ξ Y₀ Y + aaFun T μ P μW μN ψ π w' w₂ ξ Y₀ Y := by
    intro b w w' w₂ ξ Y₀ Y h₀ h₁
    have e : F (b • w + w') w₂ ξ Y₀ Y = fun p => b • F w w₂ ξ Y₀ Y p + F w' w₂ ξ Y₀ Y p := by
      funext p
      simp only [F, psiCoef, map_add, map_smul, inner_add_right, inner_smul_right, add_smul, mul_smul]
    have i1 : Integrable (fun p => b • F w w₂ ξ Y₀ Y p) (μW.prod μN) := (hint w w₂ ξ h₀ h₁).smul b
    rw [hA, hA, hA, e, integral_add i1 (hint w' w₂ ξ h₀ h₁), integral_smul]
  have hlin₂ : ∀ (b : ℂ) (w₁ w w' : T.V) ξ {Y₀ Y : Mat k r}, Y₀ ∈ UH (Hpk k r) → Y ∈ UH (Hpk k r) →
      aaFun T μ P μW μN ψ π w₁ (b • w + w') ξ Y₀ Y =
        (starRingEnd ℂ b) • aaFun T μ P μW μN ψ π w₁ w ξ Y₀ Y + aaFun T μ P μW μN ψ π w₁ w' ξ Y₀ Y := by
    intro b w₁ w w' ξ Y₀ Y h₀ h₁
    have e : F w₁ (b • w + w') ξ Y₀ Y =
        fun p => (starRingEnd ℂ b) • F w₁ w ξ Y₀ Y p + F w₁ w' ξ Y₀ Y p := by
      funext p
      simp only [F, psiCoef, inner_add_left, inner_smul_left, add_smul, mul_smul]
    have i1 : Integrable (fun p => (starRingEnd ℂ b) • F w₁ w ξ Y₀ Y p) (μW.prod μN) :=
      (hint w₁ w ξ h₀ h₁).smul _
    rw [hA, hA, hA, e, integral_add i1 (hint w₁ w' ξ h₀ h₁), integral_smul]
  have hz₁ : ∀ w₂ ξ Y₀ Y, aaFun T μ P μW μN ψ π 0 w₂ ξ Y₀ Y = 0 := by
    intro w₂ ξ Y₀ Y
    simp [aaFun, sInt, psiCoef]
  have hz₂ : ∀ w₁ ξ Y₀ Y, aaFun T μ P μW μN ψ π w₁ 0 ξ Y₀ Y = 0 := by
    intro w₁ ξ Y₀ Y
    simp [aaFun, sInt, psiCoef]
  have hKmem : ∀ kk : S7.KG ε, P⁻¹ * S7.toMK kk * P ∈ UH (Hpk k r) :=
    fun kk => conj_mem_uh hP (by exact (kk : S7.UJ ε).2)
  have hop1 : ∀ w : T.V, T.op 1 w = w := fun w => by rw [S7.op_one']; rfl

  by_contra hcon'
  have hcon : ∀ (ξ : Vp) (x₀ x : Mat k r), x₀ ∈ UH (Hpk k r) → x ∈ UH (Hpk k r) →
      aaFun T μ P μW μN ψ π v v ξ x₀ x = 0 :=
    fun ξ x₀ x h0 h1 => by_contra fun h2 => hcon' ⟨ξ, x₀, x, h0, h1, h2⟩
  set ξ' := U ξ₀
  let Z₁ : Submodule ℂ T.V :=
    { carrier := {w | ∀ (k₂ : S7.KG ε) (Y₀ Y : Mat k r), Y₀ ∈ UH (Hpk k r) → Y ∈ UH (Hpk k r) →
          aaFun T μ P μW μN ψ π w (T.op k₂ v) ξ' Y₀ Y = 0}
      add_mem' := by
        intro w w' hw hw' k₂ Y₀ Y h₀ h₁
        have := hlin₁ 1 w w' (T.op k₂ v) ξ' h₀ h₁
        rw [one_smul, one_smul] at this
        rw [this, hw k₂ Y₀ Y h₀ h₁, hw' k₂ Y₀ Y h₀ h₁, add_zero]
      zero_mem' := fun k₂ Y₀ Y _ _ => hz₁ _ _ _ _
      smul_mem' := by
        intro b w hw k₂ Y₀ Y h₀ h₁
        have := hlin₁ b w 0 (T.op k₂ v) ξ' h₀ h₁
        rw [add_zero, hz₁, add_zero] at this
        rw [this, hw k₂ Y₀ Y h₀ h₁, smul_zero] }
  have hZ₁ : Z₁ = ⊤ := by
    rcases T.irred Z₁ (by
      intro kk w hw k₂ Y₀ Y h₀ h₁
      have := aaFun_K T μ hP hB kk 1 w (T.op k₂ v) ξ' h₀ h₁
      rw [hop1] at this
      rw [this]
      exact hw k₂ _ _ (uh_mul h₀ (hKmem 1)) (uh_mul h₁ (hKmem kk))) with h | h
    · exfalso
      have hvZ : v ∈ Z₁ := by
        intro k₂ Y₀ Y h₀ h₁
        have := aaFun_K T μ hP hB 1 k₂ v v ξ' h₀ h₁
        rw [hop1] at this
        rw [this]
        exact hcon ξ' _ _ (uh_mul h₀ (hKmem k₂)) (uh_mul h₁ (hKmem 1))
      rw [h, Submodule.mem_bot] at hvZ
      exact hv hvZ
    · exact h
  let Z₂ : Submodule ℂ T.V :=
    { carrier := {w | ∀ (w₁ : T.V) (Y₀ Y : Mat k r), Y₀ ∈ UH (Hpk k r) → Y ∈ UH (Hpk k r) →
          aaFun T μ P μW μN ψ π w₁ w ξ' Y₀ Y = 0}
      add_mem' := by
        intro w w' hw hw' w₁ Y₀ Y h₀ h₁
        have := hlin₂ 1 w₁ w w' ξ' h₀ h₁
        rw [one_smul, map_one, one_smul] at this
        rw [this, hw w₁ Y₀ Y h₀ h₁, hw' w₁ Y₀ Y h₀ h₁, add_zero]
      zero_mem' := fun w₁ Y₀ Y _ _ => hz₂ _ _ _ _
      smul_mem' := by
        intro b w hw w₁ Y₀ Y h₀ h₁
        have := hlin₂ b w₁ w 0 ξ' h₀ h₁
        rw [add_zero, hz₂, add_zero] at this
        rw [this, hw w₁ Y₀ Y h₀ h₁, smul_zero] }
  have hZ₂ : Z₂ = ⊤ := by
    rcases T.irred Z₂ (by
      intro kk w hw w₁ Y₀ Y h₀ h₁
      have := aaFun_K T μ hP hB 1 kk w₁ w ξ' h₀ h₁
      rw [hop1] at this
      rw [this]
      exact hw w₁ _ _ (uh_mul h₀ (hKmem kk)) (uh_mul h₁ (hKmem 1))) with h | h
    · exfalso
      have hvZ : v ∈ Z₂ := by
        intro w₁ Y₀ Y h₀ h₁
        have h1 : w₁ ∈ Z₁ := by rw [hZ₁]; exact Submodule.mem_top
        have := h1 1 Y₀ Y h₀ h₁
        rwa [hop1] at this
      rw [h, Submodule.mem_bot] at hvZ
      exact hv hvZ
    · exact h
  have hw₂ : U₁ v₂ ∈ Z₂ := by rw [hZ₂]; exact Submodule.mem_top
  exact hne3 (hw₂ (U₁ v₁) _ _ hX₀ hX)

end Transport

end ReciprocityTheory.ChartRestriction.DS.Lap
