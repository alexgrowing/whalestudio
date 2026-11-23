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
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.HUnfold

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.StdUnn.PolesModel GlobalTheory.StdUnn.HeightExists GlobalTheory.Eis
open PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SwUnf GlobalTheory.CompanionTheory.HermPoisson GlobalTheory.CompanionTheory.SiegelUnip

variable {D : D7} {n : ℕ}

theorem majorant {χ : (AE D)ˣ →* Circle} {H : G D n → ℝ≥0} (h : IsHeight H) {s₁ : ℂ} {φ : G D n → ℂ}
    (hφ : IsSection χ s₁ φ) {s : ℂ} (hs : (n : ℝ) / 2 < s.re) {C : Set (G D n)} (hC : IsCompact C) :
    ∃ u : Cosets (P D n) (GF D n) → ℝ, Summable u ∧
      ∀ q, ∀ g ∈ C, ‖term (P D n) (GF D n) (stdSec H φ s₁ s) g q‖ ≤ u q := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  have h1 : Continuous (iwAbs modP (K D n)) := isIwasawa.continuous_iwAbs HeightExists.isClosed_P continuous_modP HeightExists.isCompact_K
  have h2 : Continuous fun g => Real.log (iwAbs modP (K D n) g) :=
    (NNReal.continuous_coe.comp h1).log fun g => (NNReal.coe_pos.2 (iwAbs_pos _ _ g)).ne'
  obtain ⟨u, hu, hb⟩ := exists_majorant (χ := χ.comp detP) (ρ := (n : ℝ) / 2) (σ := (n : ℝ) / 2)
    (Φ := stdSec H φ s₁) isIwasawa HeightExists.isCompact_K
    (Continuous.continuousOn (by
      simp only [stdSec, height_eq h, npow_eq_exp (iwAbs_pos _ _ _)]
      exact (hφ.2.1.comp continuous_snd).mul (((Complex.continuous_ofReal.comp (h2.comp continuous_snd)).mul
        (continuous_fst.sub continuous_const)).cexp)))
    (fun z _ => by
      have := (isSection_iff.1 (isSection_stdSec h hφ z)).1
      push_cast
      exact this)
    summable_spherical (isCompact_singleton (x := s)) (Set.singleton_subset_iff.2 hs) hC
  exact ⟨u, hu, fun q g hg => hb q s rfl g hg⟩

theorem sect_eq {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (H : G D n → ℝ≥0)
    (Φ : schwartzA θ V.rank n) (z : ℂ) :
    sect ω H Φ z = stdSec H (fun g : G D n => (ω g Φ).1 0) (s0 V n) z :=
  funext fun _ => mul_comm _ _

theorem countable_GF : Countable (GF D n) := by
  haveI : Countable D.host.E := GlobalTheory.CompanionTheory.FourierComplete.countable_numberField D.host.E
  haveI : Countable (Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) :=
    inferInstanceAs (Countable (Fin (n + n) → Fin (n + n) → D.host.E))
  refine Function.Injective.countable (f := fun γ : GF D n => ratOf γ) fun a b hab => ?_
  apply Subtype.ext
  apply mat_inj
  rw [mat_ratOf, mat_ratOf]
  simp only at hab
  rw [hab]

theorem countable_cosets : Countable (Cosets (P D n) (GF D n)) := by
  haveI := countable_GF (D := D) (n := n)
  exact Function.Surjective.countable (f := Quot.mk _) Quot.mk_surjective

theorem countable_ratHerm : Countable (ratHerm D n) := by
  haveI : Countable D.host.E := GlobalTheory.CompanionTheory.FourierComplete.countable_numberField D.host.E
  haveI : Countable (Matrix (Fin n) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin n → Fin n → D.host.E))
  have hmem : ∀ q : ratHerm D n, q.1.1 ∈ ratMx D n n := fun q => AddSubgroup.mem_comap.1 q.2
  choose g hg using fun q : ratHerm D n => mem_ratMx.1 (hmem q)
  exact Function.Injective.countable (f := g) fun a b h =>
    Subtype.ext (Subtype.ext (by rw [← hg a, ← hg b, h]))

theorem sec_det_one {χ : (AE D)ˣ →* Circle} {z : ℂ} {φ : G D n → ℂ} (hφ : IsSection χ z φ) {p : G D n}
    (hp : p ∈ P D n) {a : GL (Fin n) (AE D)} (ha : blkA (mat p) = a.1) (hd : Matrix.GeneralLinearGroup.det a = 1)
    (g : G D n) : φ (p * g) = φ g := by
  rw [hφ.1 p hp a ha g, hd, map_one, map_one]
  simp

theorem unfold : PositivityTheory.PfSWUS.Unfold := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS _hR nb lam 𝓖 hCD w hw β hβ z hz g
  obtain ⟨hnb, hHaar, hD, hD1⟩ := hCD
  obtain ⟨𝓕, hμ⟩ := hS.hμ
  have hsec := GlobalTheory.StdUnn.SiegelSection.fock_mem_degenerate D n V ψ hS.hψ χ hS.hχ hS.hη θ hS.hθ μ 𝓕 hμ ω hS.hω
    l hS.hl s hS.hs Φ hS.hΦ
  have hLI : LeftInv (P D n ⊓ GF D n) (sect ω H Φ z) :=
    GlobalTheory.StdUnn.LeftInvSect.leftInv_sect D n (GlobalTheory.StdUnn.Iwasawa.exists_mul D n) V ψ χ θ μ ω hS.hχ hS.hω H hS.hH Φ z
  have hsz : IsSection χ z (sect ω H Φ z) := by
    rw [sect_eq]; exact isSection_stdSec hS.hH hsec z
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
  let F : Cosets (P D n) (GF D n) → hermA D n → ℂ := fun q b => term (P D n) (GF D n) (sect ω H Φ z) (nb b * g) q
  let F0 : hermA D n → ℂ := fun b => sect ω H Φ z (w * nb b * g)
  let ch : hermA D n → ℂ := chi ψ (-(β.1.map (incA D)))
  have hch : ∀ b, ch b = ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) :=
    fun b => chi_neg_left ψ _ b
  have hβr : -(β.1.map (incA D)) ∈ ratMx D n n := neg_mem (mem_ratMx.2 ⟨β.1, rfl⟩)
  have hcont : Continuous (sect ω H Φ z) := hsz.2.1
  have hnbc : Continuous nb := nb_continuous hnb
  have hγ : ∀ l : ratHerm D n, nb l.1 ∈ GF D n := fun l => nb_rat hnb l.2
  obtain ⟨-, K0, hK0, hK0x⟩ := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := n)
  obtain ⟨u, hu, hub⟩ := majorant hS.hH hsec hz (hK0.image (hnbc.mul continuous_const (g := fun _ => g)))
  have hbound : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ ∑' q, u q := by
    intro b
    obtain ⟨γ, hγm, hγK⟩ := hK0x b
    let γ' : GF D n := ⟨nb γ, nb_rat hnb hγm⟩
    have hle : ∀ q, ‖F q b‖ ≤ u ((rmulEquiv (P D n) (GF D n) γ').symm q) := by
      intro q
      have h2 := term_mul_left hLI γ' (nb b * g) ((rmulEquiv (P D n) (GF D n) γ').symm q)
      rw [Equiv.apply_symm_apply] at h2
      have h1 : F q b = term (P D n) (GF D n) (sect ω H Φ z) (nb (γ + b) * g)
          ((rmulEquiv (P D n) (GF D n) γ').symm q) := by
        show term (P D n) (GF D n) (sect ω H Φ z) (nb b * g) q = _
        rw [← h2, nb_add hnb, mul_assoc]
      rw [h1, sect_eq]
      exact hub _ _ ⟨γ + b, hγK, rfl⟩
    have hsu : Summable (fun q => u ((rmulEquiv (P D n) (GF D n) γ').symm q)) :=
      (Equiv.summable_iff (rmulEquiv (P D n) (GF D n) γ').symm).2 hu
    have hsF : Summable (fun q => ‖F q b‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsu
    refine ⟨hsF, ?_⟩
    calc ∑' q, ‖F q b‖ ≤ ∑' q, u ((rmulEquiv (P D n) (GF D n) γ').symm q) := Summable.tsum_le_tsum hle hsF hsu
      _ = ∑' q, u q := Equiv.tsum_eq _ _
  have hF : ∀ q, AEStronglyMeasurable (F q) lam := fun q => by
    have : Continuous (F q) := hcont.comp (continuous_const.mul (hnbc.mul continuous_const))
    exact this.aestronglyMeasurable
  have hchm : AEStronglyMeasurable ch lam := (continuous_chi hS.hψ _).aestronglyMeasurable
  have hchn : ∀ b, ‖ch b‖ = 1 := fun b => hS.hψ.2.1 _
  have hcha : ∀ a b, ch (a + b) = ch a * ch b := fun a b => chi_add_right ψ _ a b
  have hchr : ∀ l : ratHerm D n, ch l = 1 := fun l => chi_rat hS.hψ hβr l
  let τ : ratHerm D n → Cosets (P D n) (GF D n) ≃ Cosets (P D n) (GF D n) :=
    fun l => rmulEquiv (P D n) (GF D n) ⟨nb l.1, hγ l⟩
  have hτ : ∀ (l : ratHerm D n) q b, F q ((l : hermA D n) + b) = F (τ l q) b := by
    intro l q b
    show term (P D n) (GF D n) (sect ω H Φ z) (nb ((l : hermA D n) + b) * g) q =
      term (P D n) (GF D n) (sect ω H Φ z) (nb b * g) (rmulEquiv (P D n) (GF D n) ⟨nb l.1, hγ l⟩ q)
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
    show term (P D n) (GF D n) (sect ω H Φ z) (nb b * g) (e l) = sect ω H Φ z (w * nb ((l : hermA D n) + b) * g)
    rw [hval _ hLI l (nb b * g), nb_add hnb]
    simp only [mul_assoc]
  have hsmall : ∀ y, y ≠ (⊥ : Submodule D.host.E (Fin n → D.host.E)) →
      ∃ ν, ch ν ≠ 1 ∧ ∀ q, cosetCell q = y → ∀ b, F q (ν + b) = F q b := by
    intro y hy
    obtain ⟨ν0, hν, hsm⟩ := GlobalTheory.T.nondegenerate_character_cell_factorization hS.hψ β hβ y hy
    refine ⟨ν0, by rw [hch]; exact hν, fun q hq b => ?_⟩
    obtain ⟨p, hp, a, ha, hd, hpe⟩ :=
      hsm ((q.out : GF D n) : G D n) (nb ν0) q.out.2 (ratOf q.out) (mat_ratOf q.out) hq (hnb ν0)
    show sect ω H Φ z (((q.out : GF D n) : G D n) * (nb (ν0 + b) * g)) =
      sect ω H Φ z (((q.out : GF D n) : G D n) * (nb b * g))
    rw [nb_add hnb, mul_assoc, ← mul_assoc ((q.out : GF D n) : G D n), hpe, mul_assoc]
    exact sec_det_one hsz hp ha hd _
  obtain ⟨hint, heq⟩ := GlobalTheory.T.fundamental_domain_fourier_unfolding lam (ratHerm D n) 𝓖 hD hD1 cosetCell ⊥ F F0 ch hF hchm hchn hcha hchr
    (∑' q, u q) hbound τ hτ hτc e he hfib he0 hsmall
  refine ⟨hint, ?_⟩
  have lhs : fc ψ lam 𝓖 nb (fun x => eis ω H Φ x z) β g = ∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam := by
    simp only [fc]
    congr 1
    funext b
    rw [hch]
    rfl
  rw [lhs, heq]
  congr 1
  funext b
  rw [hch]

end PositivityTheory.PfSWUS.HUnfold
