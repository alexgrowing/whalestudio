import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilSchrodingerRealParameter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCellsDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinRationalPoints
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfoldingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParamStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorizationStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

namespace GlobalTheory.CompanionTheory.SwUnf
open GlobalTheory.Eis

variable {D : D7} {n : ℕ}

theorem sect_facts {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {Φ : schwartzA θ V.rank n} (hS : Std D n V ψ χ θ μ ω H l s ν Φ) {z : ℂ} (hz : (n : ℝ) / 2 < z.re) :
    Continuous (sect ω H Φ z) ∧ LeftInv (P D n ⊓ GF D n) (sect ω H Φ z) ∧
    (∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → Matrix.GeneralLinearGroup.det a = 1 → ∀ g,
      sect ω H Φ z (p * g) = sect ω H Φ z g) ∧
    ∀ C : Set (G D n), IsCompact C → ∃ u : Cosets (P D n) (GF D n) → ℝ, Summable u ∧
      ∀ q, ∀ g ∈ C, ‖term (P D n) (GF D n) (sect ω H Φ z) g q‖ ≤ u q := by
  obtain ⟨𝓕, hμ⟩ := hS.hμ
  have hsec := GlobalTheory.StdUnn.SiegelSection.fock_mem_degenerate D n V ψ hS.hψ χ hS.hχ hS.hη θ hS.hθ μ 𝓕 hμ ω hS.hω l hS.hl s hS.hs Φ hS.hΦ
  have e : ∀ z, sect ω H Φ z = stdSec H (fun g : G D n => (ω g Φ).1 0) (s0 V n) z :=
    fun z => funext fun g => mul_comm _ _
  have hs2 := GlobalTheory.StdUnn.PolesModel.isSection_stdSec hS.hH hsec z
  rw [← e] at hs2
  refine ⟨hs2.2.1, GlobalTheory.StdUnn.LeftInvSect.leftInv_sect D n (GlobalTheory.StdUnn.Iwasawa.exists_mul D n) V ψ χ θ μ ω hS.hχ hS.hω H hS.hH Φ z,
    fun p hp a ha h1 g => ?_, fun C hC => ?_⟩
  · rw [hs2.1 p hp a ha g, h1]
    simp [npow]
  · haveI := t2Space_adeleRing' (F := D.host.F)
    have h1 : Continuous (iwAbs (PolesModel.modP (D := D) (n := n)) (K D n)) :=
      PolesModel.isIwasawa.continuous_iwAbs GlobalTheory.StdUnn.Model.isClosed_P PolesModel.continuous_modP GlobalTheory.StdUnn.Model.isCompact_K
    have h2 : Continuous fun g => Real.log (iwAbs (PolesModel.modP (D := D) (n := n)) (K D n) g) :=
      (NNReal.continuous_coe.comp h1).log fun g => (NNReal.coe_pos.2 (iwAbs_pos _ _ g)).ne'
    have hc : Continuous fun x : ℂ × G D n => stdSec H (fun g : G D n => (ω g Φ).1 0) (s0 V n) x.1 x.2 := by
      simp only [stdSec, PolesModel.height_eq hS.hH, npow_eq_exp (iwAbs_pos _ _ _)]
      exact (hsec.2.1.comp continuous_snd).mul (((Complex.continuous_ofReal.comp (h2.comp continuous_snd)).mul
        (continuous_fst.sub continuous_const)).cexp)
    obtain ⟨u, hu, hb⟩ := exists_majorant (Φ := fun s => stdSec H (fun g : G D n => (ω g Φ).1 0) (s0 V n) s)
      (χ := χ.comp PolesModel.detP) (ρ := (n : ℝ) / 2) (σ := (n : ℝ) / 2) PolesModel.isIwasawa GlobalTheory.StdUnn.Model.isCompact_K
      hc.continuousOn
      (fun z _ => by
        have := (PolesModel.isSection_iff.1 (PolesModel.isSection_stdSec hS.hH hsec z)).1
        push_cast
        exact this) PolesModel.summable_spherical (S := {z}) isCompact_singleton (Set.singleton_subset_iff.2 hz) hC
    refine ⟨u, hu, fun q g hg => ?_⟩
    rw [e]; exact hb q z rfl g hg

end GlobalTheory.CompanionTheory.SwUnf

namespace GlobalTheory.CompanionTheory.SwUnf
open GlobalTheory.Eis GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

variable {D : D7} {n : ℕ}

theorem nb_add {nb : hermA D n → G D n} (h : IsNMap nb) (a b : hermA D n) : nb (a + b) = nb a * nb b := by
  apply mat_inj
  rw [mat_mul, h, h, h, submatrix_fromBlocks_mul]
  simp [add_comm]

theorem continuous_blk4_right : Continuous fun b : Mx D n n => (blk4 1 b 0 1 : Mx D (n + n) (n + n)) := by
  refine continuous_matrix fun i j => ?_
  simp only [blk4, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
  · exact continuous_const
  · exact continuous_apply_apply i j
  · exact continuous_const
  · exact continuous_const

theorem nb_continuous {nb : hermA D n → G D n} (h : IsNMap nb) : Continuous nb := by
  have hn : ∀ b, (nb b)⁻¹ = nb (-b) := fun b => by
    rw [eq_comm, eq_inv_iff_mul_eq_one, ← nb_add h]
    apply mat_inj
    rw [neg_add_cancel, h, mat_one]
    simp [block_matrix_one]
  rw [(isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous_iff, Units.continuous_iff]
  constructor
  · have : Continuous fun b : hermA D n => (blk4 1 b.1 0 1 : Mx D (n + n) (n + n)) :=
      continuous_blk4_right.comp continuous_subtype_val
    exact this.congr fun b => (h b).symm
  · have : Continuous fun b : hermA D n => (blk4 1 (-b).1 0 1 : Mx D (n + n) (n + n)) :=
      continuous_blk4_right.comp (continuous_subtype_val.comp continuous_neg)
    refine this.congr fun b => ?_
    rw [← h, ← hn]
    simp [mat, map_inv]

theorem nb_mem_GF {nb : hermA D n → G D n} (h : IsNMap nb) (l : ratHerm D n) : ∃ b : Matrix (Fin n) (Fin n) D.host.E,
    nb l.1 ∈ GF D n ∧ mat (nb l.1) = blk4 1 (b.map (incA D)) 0 1 := by
  obtain ⟨b, hb⟩ := AddSubgroup.mem_comap.1 l.2
  have hb' : b.map (incA D) = l.1.1 := hb
  refine ⟨b, ?_, by rw [h, hb']⟩
  rw [ChartRat.mem_GF_iff, h]
  refine ⟨blk4 1 b 0 1, ?_⟩
  change (blk4 1 b 0 1).map (incA D) = _
  rw [GlobalTheory.CompanionTheory.Hypotheses₂.WeilU.blk4_map_alt, hb']
  have e0 : (0 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 0 := map_zero (incA D).mapMatrix
  have e1 : (1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 1 := map_one (incA D).mapMatrix
  rw [e0, e1]

theorem rat_mem_of (b : Matrix (Fin n) (Fin n) D.host.E) : (b.map (incA D) : Mx D n n) ∈ ratMx D n n :=
  ⟨b, rfl⟩

theorem countable_E : Countable D.host.E :=
  (Module.finBasis ℚ D.host.E).equivFun.injective.countable

theorem countable_mat (a b : ℕ) : Countable (Matrix (Fin a) (Fin b) D.host.E) :=
  haveI := countable_E (D := D)
  inferInstanceAs (Countable (Fin a → Fin b → D.host.E))

theorem countable_ratHerm : Countable (ratHerm D n) := by
  haveI := countable_mat (D := D) n n
  have hinj : Function.Injective fun l : ratHerm D n => (Classical.choose (AddSubgroup.mem_comap.1 l.2) :
      Matrix (Fin n) (Fin n) D.host.E) := fun a b h => by
    have ha := Classical.choose_spec (AddSubgroup.mem_comap.1 a.2)
    have hb := Classical.choose_spec (AddSubgroup.mem_comap.1 b.2)
    simp only at h
    rw [h] at ha
    exact Subtype.ext (Subtype.ext (ha.symm.trans hb))
  exact hinj.countable

theorem countable_GF : Countable (GF D n) := by
  haveI := countable_mat (D := D) (n + n) (n + n)
  have hinj : Function.Injective (ratOf (D := D) (n := n)) := fun a b h =>
    Subtype.ext (mat_inj (by rw [mat_ratOf, mat_ratOf, h]))
  exact hinj.countable

theorem countable_cosets : Countable (Cosets (P D n) (GF D n)) := by
  haveI := countable_GF (D := D) (n := n)
  exact Quotient.countable

theorem unfold : PositivityTheory.PfSWUS.Unfold := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC w hw β hβ z hz g
  obtain ⟨hcont, hinv, hdet, hmaj⟩ := sect_facts hS hz
  obtain ⟨hNb, hHaar, hFD, hvol⟩ := hC
  have hψ := hS.hψ
  have hcn := nb_continuous hNb
  have hcolat := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := n)
  haveI : DiscreteTopology (ratHerm D n) := hcolat.1
  haveI : Countable (ratHerm D n) := countable_ratHerm
  haveI : Countable (Cosets (P D n) (GF D n)) := countable_cosets
  obtain ⟨e, he, hr, hterm⟩ := GlobalTheory.T.big_cell_cosets_hermitian_param hw hNb
  choose bb hbG hbm using nb_mem_GF hNb
  let F : Cosets (P D n) (GF D n) → hermA D n → ℂ := fun q b => term (P D n) (GF D n) (sect ω H Φ z) (nb b * g) q
  let ch : hermA D n → ℂ := fun b => ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))
  let τ : ratHerm D n → Cosets (P D n) (GF D n) ≃ Cosets (P D n) (GF D n) := fun l => rmulEquiv _ _ ⟨nb l.1, hbG l⟩
  have hτ : ∀ (l : ratHerm D n) q b, F q ((l : hermA D n) + b) = F (τ l q) b := fun l q b => by
    simp only [F]
    rw [nb_add hNb, mul_assoc]
    exact term_mul_left hinv ⟨nb l.1, hbG l⟩ _ q
  have hchc : Continuous ch := by
    have := GlobalTheory.CompanionTheory.HermPoisson.continuous_chi hψ (-(β.1.map (incA D)) : Mx D n n)
    exact this.congr fun b => GlobalTheory.CompanionTheory.HermPoisson.chi_neg_left ψ _ b
  obtain ⟨K0, hK0, hKc⟩ := hcolat.2
  obtain ⟨u, hu, hub⟩ := hmaj ((fun d => nb d * g) '' K0) (hK0.image (hcn.mul continuous_const))
  have hM : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ ∑' q, u q := fun b => by
    obtain ⟨γ, hγ, hb⟩ := hKc b
    have hb2 : ∀ q, ‖F q b‖ ≤ u ((τ ⟨γ, hγ⟩).symm q) := fun q => by
      have := hτ ⟨γ, hγ⟩ ((τ ⟨γ, hγ⟩).symm q) b
      rw [Equiv.apply_symm_apply] at this
      rw [← this]
      exact hub _ _ ⟨_, hb, rfl⟩
    have hs2 : Summable fun q => u ((τ ⟨γ, hγ⟩).symm q) := (τ ⟨γ, hγ⟩).symm.summable_iff.2 hu
    refine ⟨.of_nonneg_of_le (fun _ => norm_nonneg _) hb2 hs2, ?_⟩
    refine (Summable.tsum_le_tsum hb2 (.of_nonneg_of_le (fun _ => norm_nonneg _) hb2 hs2) hs2).trans_eq ?_
    exact (τ ⟨γ, hγ⟩).symm.tsum_eq u
  have := GlobalTheory.T.fundamental_domain_fourier_unfolding lam (ratHerm D n) 𝓖 hFD hvol cosetCell (⊥ : Submodule D.host.E (Fin n → D.host.E)) F
    (fun b => sect ω H Φ z (w * nb b * g)) ch
    (fun q => Continuous.aestronglyMeasurable (hcont.comp (continuous_const.mul (hcn.mul continuous_const))))
    hchc.aestronglyMeasurable
    (fun b => hψ.2.1 _)
    (fun a b => by
      simp only [ch, AddSubgroup.coe_add]
      rw [Matrix.mul_add, Matrix.trace_add, GlobalTheory.CompanionTheory.HermPoisson.halfTr_add', neg_add, AddChar.map_add_eq_mul])
    (fun l => by
      have := GlobalTheory.CompanionTheory.HermPoisson.chi_rat hψ (m := (-(β.1.map (incA D)) : Mx D n n)) (neg_mem (rat_mem_of β.1)) l
      rw [GlobalTheory.CompanionTheory.HermPoisson.chi_neg_left] at this
      exact this)
    _ hM τ hτ (fun l q => GlobalTheory.T.coset_cell_invariant_unipotent q ⟨nb l.1, hbG l⟩ (bb l) (hbm l)) e he hr
    (fun l b => by
      simp only [F]
      rw [hterm _ hinv, nb_add hNb]
      simp only [mul_assoc])
    (fun y hy => by
      obtain ⟨ν', h1, h2⟩ := GlobalTheory.T.nondegenerate_character_cell_factorization hψ β hβ y hy
      refine ⟨ν', h1, fun q hq b => ?_⟩
      obtain ⟨p, hp, a, ha, hd, hpe⟩ := h2 (q.out : GF D n) (nb ν') (q.out : GF D n).2 (ratOf q.out) (mat_ratOf _) hq (hNb _)
      simp only [F, term]
      rw [nb_add hNb, mul_assoc (nb ν'), ← mul_assoc _ (nb ν'), hpe, mul_assoc, hdet p hp a ha hd])
  exact this

end GlobalTheory.CompanionTheory.SwUnf
