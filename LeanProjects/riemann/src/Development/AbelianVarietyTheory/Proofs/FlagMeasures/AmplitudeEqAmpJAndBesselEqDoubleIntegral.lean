import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.SgInf.AmpJ

theorem integral_map_of_ae_leftInv {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableEq Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X} {g : X → Y} {r : Y → X}
    (hg : Measurable g) (hr : Measurable r) (hrg : ∀ᵐ x ∂μ, r (g x) = x) (f : Y → E) :
    ∫ y, f y ∂(μ.map g) = ∫ x, f (g x) ∂μ := by
  by_cases hf : AEStronglyMeasurable f (μ.map g)
  · exact integral_map hg.aemeasurable hf
  · have hfg : ¬ AEStronglyMeasurable (fun x => f (g x)) μ := by
      intro h
      have hmm : (μ.map g).map r = μ := by
        rw [Measure.map_map hr hg]
        rw [Measure.map_congr (g := id) (by filter_upwards [hrg] with x hx using hx), Measure.map_id]
      rw [← hmm] at h
      have h2 := h.comp_aemeasurable hr.aemeasurable
      apply hf
      refine h2.congr ?_
      have hs : MeasurableSet {y | g (r y) = y} := measurableSet_eq_fun (hg.comp hr) measurable_id
      have hae : ∀ᵐ y ∂(μ.map g), g (r y) = y :=
        (ae_map_iff hg.aemeasurable hs).2 (by filter_upwards [hrg] with x hx; simp [hx])
      filter_upwards [hae] with y hy
      simp [Function.comp, hy]
    rw [integral_non_aestronglyMeasurable hf, integral_non_aestronglyMeasurable hfg]

variable {k r : ℕ}

theorem hpk_unit : IsUnit (Hpk k r).det := by
  have h := (hpkFacts k r).2.1
  have : (Hpk k r).det * (Hpk k r).det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  exact isUnit_iff_exists_inv.2 ⟨_, this⟩

theorem unit_of_mem {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : IsUnit g.det :=
  ((uHGroup _ (Hpk k r) hpk_unit).2.2 g hg).1

theorem inv_mem {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) :=
  ((uHGroup _ (Hpk k r) hpk_unit).2.2 g hg).2

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  obtain ⟨hU, hfix, hz⟩ := hh
  have hd := unit_of_mem hU
  have key : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]
  exact ⟨inv_mem hU, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩

theorem psi_eq_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) : psi k r z c = psiGen k r z (fun _ => c) := by
  funext g
  unfold psi psiGen ell
  rw [Finset.mul_sum]
  rfl

theorem psi_congr {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {g g' : Mat k r} (h : ell k r z g = ell k r z g') :
    psi k r z c g = psi k r z c g' := by
  unfold psi; rw [h]

end GlobalTheory.SgInf.AmpJ

noncomputable section
namespace GlobalTheory.SgInf.AmpJ
variable {k r : ℕ}

def lmulEquiv (γ : Mat k r) (hγ : IsUnit γ.det) : Mt k r ≃ᵐ Mt k r :=
  Homeomorph.toMeasurableEquiv
    { toFun := lmulM γ
      invFun := lmulM γ⁻¹
      left_inv := fun x => by
        show γ⁻¹ * (γ * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγ, Matrix.one_mul]
      right_inv := fun x => by
        show γ * (γ⁻¹ * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hγ, Matrix.one_mul]
      continuous_toFun := (continuous_const (y := γ)).matrix_mul (continuous_id (X := Mat k r))
      continuous_invFun := (continuous_const (y := γ⁻¹)).matrix_mul (continuous_id (X := Mat k r)) }

theorem part1 {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (μG : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (hμ : IsHaarOn (GG k r) μG)
    (γ : Mat k r) (hγ : γ ∈ GG k r) : OO μG Φ Φ' γ = ampJ μG 1 Φ Φ' γ := by
  have hd : IsUnit γ.det := unit_of_mem hγ
  unfold OO ampJ
  rw [Complex.ofReal_one, inv_one, one_smul]
  have hmap : μG.map (lmulEquiv γ hd) = μG := hμ.2.2.2 γ hγ
  conv_lhs => rw [← hmap]
  rw [integral_map_equiv]
  congr 1
  funext x
  show rk1 (Φ (γ * Matrix.of x)) (Φ' (γ⁻¹ * (γ * Matrix.of x))) = _
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  rfl

theorem pis_inv {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [CompleteSpace Wp] {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {π : Mat k r → (Wp →L[ℂ] Wp)}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : IsURepOn (UWset k r z) π)
    {h n : Mat k r} (hh : h ∈ UWset k r z) (hn : n ∈ Nset k r) :
    PiS (psi k r z c) π (h * n)⁻¹ = psi k r z c n⁻¹ • π h⁻¹ := by
  have hd := unit_of_mem hh.1
  have hni : n⁻¹ ∈ Nset k r := (nSubgroup k r).2.2 n hn
  have hm := uWNormal k r z hz h hh n⁻¹ hni
  have heq : (h * n)⁻¹ = h⁻¹ * (h * n⁻¹ * h⁻¹) := by
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd,
      Matrix.one_mul]
  rw [heq, psi_eq_psiGen, ((GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z (fun _ => c) π hz hT hπ).1 h⁻¹ (uw_inv hh) _ hm.1).2,
    ← psi_eq_psiGen, psi_congr hm.2]

theorem adj_inv {Wq : Type*} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Wq →L[ℂ] Wq)} (hπ : IsURepOn (UWset k r z) π)
    {h : Mat k r} (hh : h ∈ UWset k r z) : ContinuousLinearMap.adjoint (π h) = π h⁻¹ := by
  have hd := unit_of_mem hh.1
  have h1 : (π h).comp (π h⁻¹) = 1 := by
    rw [← hπ.1.2 h hh h⁻¹ (uw_inv hh), Matrix.mul_nonsing_inv _ hd, hπ.1.1]
  have h2 : (ContinuousLinearMap.adjoint (π h)).comp (π h) = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (π h)).1 (hπ.2.1 h hh)
  calc ContinuousLinearMap.adjoint (π h) = (ContinuousLinearMap.adjoint (π h)).comp ((π h).comp (π h⁻¹)) := by
        rw [h1]; rfl
    _ = π h⁻¹ := by rw [← ContinuousLinearMap.comp_assoc, h2]; rfl

end GlobalTheory.SgInf.AmpJ

noncomputable section
namespace GlobalTheory.SgInf.AmpJ
variable {k r : ℕ}

theorem pt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp]
    {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq]
    (σ : Mat k r → (H →L[ℂ] H)) (z z' : Fin (2 * r + k + 1) → ℂ) (c₀ : ℂ) (π : Mat k r → (Wp →L[ℂ] Wp))
    (π' : Mat k r → (Wq →L[ℂ] Wq)) (x y : H) (ξ : Wp) (ξ' : Wq)
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hz' : inWb k r z') (hT' : 0 < Tz k r z')
    (hπ : IsURepOn (UWset k r z) π) (hπ' : IsURepOn (UWset k r z') π') (γ : Mat k r)
    {h n h' n' : Mat k r} (hh : h ∈ UWset k r z) (hn : n ∈ Nset k r) (hh' : h' ∈ UWset k r z')
    (hn' : n' ∈ Nset k r) :
    coef σ x y (h * n * γ * (h' * n')⁻¹) •
        rk1 (PiS (psi k r z c₀) π (h * n)⁻¹ ξ) (PiS (psi k r z' c₀) π' (h' * n')⁻¹ ξ') =
      (psi k r z c₀ n⁻¹ * star (psi k r z' c₀ n'⁻¹)) •
        ((π h⁻¹).comp ((coef σ x y (h⁻¹⁻¹ * n⁻¹⁻¹ * γ * n'⁻¹ * h'⁻¹) • rk1 ξ ξ').comp (π' h'⁻¹⁻¹))) := by
  rw [pis_inv c₀ hz hT hπ hh hn, pis_inv c₀ hz' hT' hπ' hh' hn',
    Matrix.nonsing_inv_nonsing_inv _ (unit_of_mem hh.1), Matrix.nonsing_inv_nonsing_inv _ (unit_of_mem hn.1),
    Matrix.nonsing_inv_nonsing_inv _ (unit_of_mem hh'.1), Matrix.mul_inv_rev h' n']
  have hadj : ∀ η, ⟪ξ', π' h' η⟫_ℂ = ⟪π' h'⁻¹ ξ', η⟫_ℂ := by
    intro η
    rw [← adj_inv hπ' hh', ContinuousLinearMap.adjoint_inner_left]
  ext η
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, rankOneInnerOperator_apply, map_smul,
    inner_smul_left, smul_smul, hadj, Matrix.mul_assoc]
  congr 1
  simp only [Complex.star_def]
  ring

end GlobalTheory.SgInf.AmpJ

noncomputable section
namespace GlobalTheory.SgInf.AmpJ
variable {k r : ℕ}

theorem continuous_hPart : Continuous (X := Mt k r) (Y := Mt k r) (fun s => hPart k r (Matrix.of s)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [hPart]
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact continuous_const
  · exact continuous_const

theorem continuous_mulP : Continuous (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) :=
  (continuous_fst (X := Mat k r) (Y := Mat k r)).matrix_mul continuous_snd

def mulP (p : Mt k r × Mt k r) : Mt k r := lmulM (Matrix.of p.1) p.2

theorem measurable_mulP : Measurable (mulP : Mt k r × Mt k r → Mt k r) := continuous_mulP.measurable

def splitS (s : Mt k r) : Mt k r × Mt k r :=
  (hPart k r (Matrix.of s), mulP (invM (hPart k r (Matrix.of s)), s))

theorem measurable_splitS : Measurable (splitS : Mt k r → Mt k r × Mt k r) := by
  have h0 : Measurable (α := Mt k r) (β := Mt k r) (fun s => hPart k r (Matrix.of s)) :=
    continuous_hPart.measurable
  have h1 : Measurable (fun s : Mt k r => (invM (hPart k r (Matrix.of s)), s)) :=
    (measurable_invM.comp h0).prodMk measurable_id
  exact h0.prodMk (measurable_mulP.comp h1)

theorem splitS_mul {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [CompleteSpace Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : IsURepOn (UWset k r z) π)
    (p : Mt k r × Mt k r) (hh : Matrix.of p.1 ∈ UWset k r z) (hn : Matrix.of p.2 ∈ Nset k r) :
    splitS (lmulM (Matrix.of p.1) p.2) = p := by
  have hP : hPart k r (Matrix.of p.1 * Matrix.of p.2) = Matrix.of p.1 :=
    ((GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z (fun _ => 0) π hz hT hπ).1 _ hh _ hn).1
  have hd := unit_of_mem hh.1
  unfold splitS
  refine Prod.ext ?_ ?_
  · exact hP
  · show (hPart k r (Matrix.of p.1 * Matrix.of p.2))⁻¹ * (Matrix.of p.1 * Matrix.of p.2) = Matrix.of p.2
    rw [hP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

end GlobalTheory.SgInf.AmpJ

noncomputable section
namespace GlobalTheory.SgInf.AmpJ
variable {k r : ℕ}

def inv4 (p : (Mt k r × Mt k r) × (Mt k r × Mt k r)) : (Mt k r × Mt k r) × (Mt k r × Mt k r) :=
  Prod.map (Prod.map invM invM) (Prod.map invM invM) p

theorem measurable_ambientMatrixFourFoldInverse : Measurable (inv4 : (Mt k r × Mt k r) × (Mt k r × Mt k r) → _) :=
  (measurable_invM.prodMap measurable_invM).prodMap (measurable_invM.prodMap measurable_invM)

theorem part2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp]
    {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq]
    (σ : Mat k r → (H →L[ℂ] H)) (z z' : Fin (2 * r + k + 1) → ℂ) (c₀ : ℂ) (π : Mat k r → (Wp →L[ℂ] Wp))
    (π' : Mat k r → (Wq →L[ℂ] Wq)) (μW μW' μN : Measure (Mt k r)) (x y : H) (ξ : Wp) (ξ' : Wq)
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hz' : inWb k r z') (hT' : 0 < Tz k r z')
    (hπ : IsURepOn (UWset k r z) π) (hπ' : IsURepOn (UWset k r z') π')
    (hμW : IsHaarOn (UWset k r z) μW) (hμW' : IsHaarOn (UWset k r z') μW') (hμN : IsHaarOn (Nset k r) μN)
    (γ : Mat k r) :
    besselJ k r z z' c₀ π π' μW μN μW' (fun g => coef σ x y g • rk1 ξ ξ') γ =
      Iint (psi k r z c₀) (psi k r z' c₀) π π'
        ((μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2)
        ((μW'.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) σ x y ξ ξ' γ := by
  have := hμW.1; have := hμW'.1; have := hμN.1
  have : BorelSpace (Mt k r × Mt k r) := Prod.borelSpace
  have : BorelSpace ((Mt k r × Mt k r) × (Mt k r × Mt k r)) := Prod.borelSpace
  have : MeasurableEq ((Mt k r × Mt k r) × (Mt k r × Mt k r)) := ⟨isClosed_diagonal.measurableSet⟩
  have aeOf : ∀ {S : Set (Mat k r)} {μ : Measure (Mt k r)}, IsHaarOn S μ → ∀ᵐ x ∂μ, Matrix.of x ∈ S := by
    intro S μ hμ
    rw [ae_iff]
    simpa using hμ.2.2.1
  have hae : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)),
      Matrix.of p.1.1 ∈ UWset k r z ∧ Matrix.of p.1.2 ∈ Nset k r ∧
        Matrix.of p.2.1 ∈ UWset k r z' ∧ Matrix.of p.2.2 ∈ Nset k r := by
    have a1 := (Measure.quasiMeasurePreserving_fst (μ := μW.prod μN) (ν := μW'.prod μN)).ae ((Measure.quasiMeasurePreserving_fst (μ := μW) (ν := μN)).ae (aeOf hμW))
    have a2 := (Measure.quasiMeasurePreserving_fst (μ := μW.prod μN) (ν := μW'.prod μN)).ae ((Measure.quasiMeasurePreserving_snd (μ := μW) (ν := μN)).ae (aeOf hμN))
    have a3 := (Measure.quasiMeasurePreserving_snd (μ := μW.prod μN) (ν := μW'.prod μN)).ae ((Measure.quasiMeasurePreserving_fst (μ := μW') (ν := μN)).ae (aeOf hμW'))
    have a4 := (Measure.quasiMeasurePreserving_snd (μ := μW.prod μN) (ν := μW'.prod μN)).ae ((Measure.quasiMeasurePreserving_snd (μ := μW') (ν := μN)).ae (aeOf hμN))
    filter_upwards [a1, a2, a3, a4] with p h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩

  have hWi : μW.map invM = μW := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μW).2.2 hμW).1.2
  have hW'i : μW'.map invM = μW' := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z' hz' hT' μW').2.2 hμW').1.2
  have hNi : μN.map invM = μN := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μN).2.1 hμN).1.2
  have hinv4 : ((μW.prod μN).prod (μW'.prod μN)).map inv4 = (μW.prod μN).prod (μW'.prod μN) := by
    unfold inv4
    rw [← Measure.map_prod_map _ _ (measurable_invM.prodMap measurable_invM)
      (measurable_invM.prodMap measurable_invM), ← Measure.map_prod_map _ _ measurable_invM measurable_invM,
      ← Measure.map_prod_map _ _ measurable_invM measurable_invM, hWi, hW'i, hNi]
  have hii : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), inv4 (inv4 p) = p := by
    filter_upwards [hae] with p hp
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := p
    obtain ⟨h1, h2, h3, h4⟩ := hp
    show ((invM (invM a), invM (invM b)), (invM (invM c), invM (invM d))) = ((a, b), (c, d))
    rw [invM_invM _ (unit_of_mem h1.1), invM_invM _ (unit_of_mem h2.1), invM_invM _ (unit_of_mem h3.1),
      invM_invM _ (unit_of_mem h4.1)]
  have hsplit : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)),
      Prod.map splitS splitS (Prod.map mulP mulP p) = p := by
    filter_upwards [hae] with p hp
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := p
    obtain ⟨h1, h2, h3, h4⟩ := hp
    show (splitS (lmulM (Matrix.of a) b), splitS (lmulM (Matrix.of c) d)) = ((a, b), (c, d))
    rw [splitS_mul hz hT hπ (a, b) h1 h2, splitS_mul hz' hT' hπ' (c, d) h3 h4]
  unfold besselJ Iint
  rw [show (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) = mulP from rfl,
    Measure.map_prod_map _ _ measurable_mulP measurable_mulP,
    integral_map_of_ae_leftInv (measurable_mulP.prodMap measurable_mulP)
      (measurable_splitS.prodMap measurable_splitS) hsplit]
  conv_lhs => rw [← hinv4]
  rw [integral_map_of_ae_leftInv measurable_ambientMatrixFourFoldInverse measurable_ambientMatrixFourFoldInverse hii]
  refine integral_congr_ae ?_
  filter_upwards [hae] with p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  exact (pt σ z z' c₀ π π' x y ξ ξ' hz hT hz' hT' hπ hπ' γ h1 h2 h3 h4).symm

end GlobalTheory.SgInf.AmpJ

namespace GlobalTheory.SgInf.AmpJ

theorem oo_eq_ampJ_and_besselJ_eq_Iint : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] , (∀ (μG : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq), IsHaarOn (GG k r) μG → ∀ γ ∈ GG k r, OO μG Φ Φ' γ = ampJ μG 1 Φ Φ' γ) ∧ ∀ (σ : Mat k r → (H →L[ℂ] H)) (z z' : Fin (2 * r + k + 1) → ℂ) (c₀ : ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μW μW' μN : Measure (Mt k r)) (x y : H) (ξ : Wp) (ξ' : Wq), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → IsURepOn (GG k r) σ → IsURepOn (UWset k r z) π → IsURepOn (UWset k r z') π' → IsHaarOn (UWset k r z) μW → IsHaarOn (UWset k r z') μW' → IsHaarOn (Nset k r) μN → ∀ γ ∈ GG k r, besselJ k r z z' c₀ π π' μW μN μW' (fun g => coef σ x y g • rk1 ξ ξ') γ = Iint (psi k r z c₀) (psi k r z' c₀) π π' ((μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) ((μW'.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) σ x y ξ ξ' γ := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _
  refine ⟨fun μG Φ Φ' hμ γ hγ => part1 μG Φ Φ' hμ γ hγ, ?_⟩
  intro σ z z' c₀ π π' μW μW' μN x y ξ ξ' hz hT hz' hT' _ hπ hπ' hμW hμW' hμN γ _
  exact part2 σ z z' c₀ π π' μW μW' μN x y ξ ξ' hz hT hz' hT' hπ hπ' hμW hμW' hμN γ

end GlobalTheory.SgInf.AmpJ
