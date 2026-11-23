import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilSchrodingerRealParameter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentMapContinuousAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EqZeroOfFourierCoefficientsVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfoldingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParamStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorizationStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.RationalHermitianCountable.CountableRatHerm

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.HandIAdd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

section Unfolding

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.StdUnn.PolesModel GlobalTheory.StdUnn.HeightExists GlobalTheory.Eis
open GlobalTheory.CompanionTheory.SwUnf GlobalTheory.CompanionTheory.HermPoisson GlobalTheory.CompanionTheory.SiegelUnip
open PositivityTheory.PfSWUS.HUnfold (majorant countable_cosets countable_ratHerm sec_det_one)

theorem isSection_npow_height {D : D7} {n : ℕ} {H : G D n → ℝ≥0} (hH : IsHeight H) (s : ℂ) :
    IsSection 1 s (fun x => npow (H x) (s + (n : ℂ) / 2)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  rw [height_eq hH]
  exact isSection_iff.2
    (isIwasawa.npow_iwAbs_mem HeightExists.isClosed_P continuous_modP HeightExists.isCompact_K _)

theorem stdSec_self {D : D7} {n : ℕ} (H : G D n → ℝ≥0) (φ : G D n → ℂ) (s : ℂ) : stdSec H φ s s = φ := by
  funext x
  simp [stdSec, npow]

theorem integrable_bigCell_spherical {D : D7} {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {H : G D n → ℝ≥0} (hH : IsHeight H) {nb : hermA D n → G D n} {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}
    (hCD : CoefData nb lam 𝓖) {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) (β : HermE D n) (hβ : β.1.det ≠ 0)
    {s : ℂ} (hs : (n : ℝ) / 2 < s.re) (g : G D n) :
    Integrable (fun b : hermA D n => npow (H (w * nb b * g)) (s + (n : ℂ) / 2)) lam := by
  obtain ⟨hnb, hHaar, hD, hD1⟩ := hCD
  let φ : G D n → ℂ := fun x => npow (H x) (s + (n : ℂ) / 2)
  have hsz : IsSection 1 s φ := isSection_npow_height hH s
  have hstd : stdSec H φ s s = φ := stdSec_self H φ s
  have hLI : LeftInv (P D n ⊓ GF D n) φ := leftInv_of_isSection ⟨continuous_const, fun _ => rfl⟩ hsz
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : ContinuousAdd (hermA D n) := ⟨Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)) _⟩
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  haveI : MeasurableAdd (hermA D n) := ContinuousAdd.measurableAdd
  haveI := hHaar
  haveI := countable_ratHerm (D := D) (n := n)
  haveI := countable_cosets (D := D) (n := n)
  let F : Cosets (P D n) (GF D n) → hermA D n → ℂ := fun q b => term (P D n) (GF D n) φ (nb b * g) q
  let F0 : hermA D n → ℂ := fun b => φ (w * nb b * g)
  let ch : hermA D n → ℂ := chi ψ (-(β.1.map (incA D)))
  have hch : ∀ b, ch b = ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) :=
    fun b => chi_neg_left ψ _ b
  have hβr : -(β.1.map (incA D)) ∈ ratMx D n n := neg_mem (mem_ratMx.2 ⟨β.1, rfl⟩)
  have hcont : Continuous φ := hsz.2.1
  have hnbc : Continuous nb := nb_continuous hnb
  have hγ : ∀ l : ratHerm D n, nb l.1 ∈ GF D n := fun l => nb_rat hnb l.2
  obtain ⟨-, K0, hK0, hK0x⟩ := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := n)
  obtain ⟨u, hu, hub⟩ := majorant hH hsz hs (hK0.image (hnbc.mul continuous_const (g := fun _ => g)))
  have hbound : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ ∑' q, u q := by
    intro b
    obtain ⟨γ, hγm, hγK⟩ := hK0x b
    let γ' : GF D n := ⟨nb γ, nb_rat hnb hγm⟩
    have hle : ∀ q, ‖F q b‖ ≤ u ((rmulEquiv (P D n) (GF D n) γ').symm q) := by
      intro q
      have h2 := term_mul_left hLI γ' (nb b * g) ((rmulEquiv (P D n) (GF D n) γ').symm q)
      rw [Equiv.apply_symm_apply] at h2
      have h1 : F q b = term (P D n) (GF D n) φ (nb (γ + b) * g)
          ((rmulEquiv (P D n) (GF D n) γ').symm q) := by
        show term (P D n) (GF D n) φ (nb b * g) q = _
        rw [← h2, nb_add hnb, mul_assoc]
      rw [h1]
      have h3 := hub ((rmulEquiv (P D n) (GF D n) γ').symm q) _ ⟨γ + b, hγK, rfl⟩
      rw [hstd] at h3
      exact h3
    have hsu : Summable (fun q => u ((rmulEquiv (P D n) (GF D n) γ').symm q)) :=
      (Equiv.summable_iff (rmulEquiv (P D n) (GF D n) γ').symm).2 hu
    have hsF : Summable (fun q => ‖F q b‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsu
    refine ⟨hsF, ?_⟩
    calc ∑' q, ‖F q b‖ ≤ ∑' q, u ((rmulEquiv (P D n) (GF D n) γ').symm q) := Summable.tsum_le_tsum hle hsF hsu
      _ = ∑' q, u q := Equiv.tsum_eq _ _
  have hF : ∀ q, AEStronglyMeasurable (F q) lam := fun q => by
    have : Continuous (F q) := hcont.comp (continuous_const.mul (hnbc.mul continuous_const))
    exact this.aestronglyMeasurable
  have hchm : AEStronglyMeasurable ch lam := (continuous_chi hψ _).aestronglyMeasurable
  have hchn : ∀ b, ‖ch b‖ = 1 := fun b => hψ.2.1 _
  have hcha : ∀ a b, ch (a + b) = ch a * ch b := fun a b => chi_add_right ψ _ a b
  have hchr : ∀ l : ratHerm D n, ch l = 1 := fun l => chi_rat hψ hβr l
  let τ : ratHerm D n → Cosets (P D n) (GF D n) ≃ Cosets (P D n) (GF D n) :=
    fun l => rmulEquiv (P D n) (GF D n) ⟨nb l.1, hγ l⟩
  have hτ : ∀ (l : ratHerm D n) q b, F q ((l : hermA D n) + b) = F (τ l q) b := by
    intro l q b
    show term (P D n) (GF D n) φ (nb ((l : hermA D n) + b) * g) q =
      term (P D n) (GF D n) φ (nb b * g) (rmulEquiv (P D n) (GF D n) ⟨nb l.1, hγ l⟩ q)
    rw [nb_add hnb, mul_assoc]
    exact term_mul_left hLI (⟨nb l.1, hγ l⟩ : GF D n) (nb b * g) q
  have hτc : ∀ (l : ratHerm D n) q, cosetCell (τ l q) = cosetCell q := by
    intro l q
    obtain ⟨x, hx⟩ := mem_ratMx.1 (AddSubgroup.mem_comap.1 l.2)
    refine GlobalTheory.T.coset_cell_invariant_unipotent q _ x ?_
    show mat (nb l.1) = _
    rw [hnb l.1]
    exact congrArg (fun m => blk4 1 m 0 1) hx.symm
  obtain ⟨e, he, hfib, hval⟩ := GlobalTheory.T.big_cell_cosets_hermitian_param hw hnb
  have he0 : ∀ (l : ratHerm D n) b, F (e l) b = F0 ((l : hermA D n) + b) := by
    intro l b
    show term (P D n) (GF D n) φ (nb b * g) (e l) = φ (w * nb ((l : hermA D n) + b) * g)
    rw [hval _ hLI l (nb b * g), nb_add hnb]
    simp only [mul_assoc]
  have hsmall : ∀ y, y ≠ (⊥ : Submodule D.host.E (Fin n → D.host.E)) →
      ∃ ν, ch ν ≠ 1 ∧ ∀ q, cosetCell q = y → ∀ b, F q (ν + b) = F q b := by
    intro y hy
    obtain ⟨ν0, hν, hsm⟩ := GlobalTheory.T.nondegenerate_character_cell_factorization hψ β hβ y hy
    refine ⟨ν0, by rw [hch]; exact hν, fun q hq b => ?_⟩
    obtain ⟨p, hp, a, ha, hd, hpe⟩ :=
      hsm ((q.out : GF D n) : G D n) (nb ν0) q.out.2 (ratOf q.out) (mat_ratOf q.out) hq (hnb ν0)
    show φ (((q.out : GF D n) : G D n) * (nb (ν0 + b) * g)) =
      φ (((q.out : GF D n) : G D n) * (nb b * g))
    rw [nb_add hnb, mul_assoc, ← mul_assoc ((q.out : GF D n) : G D n), hpe, mul_assoc]
    exact sec_det_one hsz hp ha hd _
  exact (GlobalTheory.T.fundamental_domain_fourier_unfolding lam (ratHerm D n) 𝓖 hD hD1 cosetCell ⊥ F F0 ch hF hchm hchn hcha hchr
    (∑' q, u q) hbound τ hτ hτc e he hfib he0 hsmall).1

end Unfolding

theorem integrable_npow_height {D : D7} {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {H : G D n → ℝ≥0} (hH : IsHeight H) {nb : hermA D n → G D n} {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}
    (hCD : CoefData nb lam 𝓖) {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) (β : HermE D n) (hβ : β.1.det ≠ 0)
    {s : ℂ} (hs : (n : ℝ) / 2 < s.re) (g : G D n) :
    Integrable (fun b : hermA D n => npow (H (w * nb b * g)) (s + (n : ℂ) / 2)) lam := by
  exact integrable_bigCell_spherical hψ hH hCD hw β hβ hs g

end PositivityTheory.PfSWUS.HandIAdd

end
