import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainUnfoldingTwoSumsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTermsUniformlySummableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCentreRationalFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCentreCharacterCellStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCosetsParamRationalStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf
open GlobalTheory.Eis

variable {D : D7} {n ρ p : ℕ}

theorem chz_add (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (a b : hermA D ρ) :
    chz ψ b₀ (a + b) = chz ψ b₀ a * chz ψ b₀ b := by
  simp only [chz, AddSubgroup.coe_add]
  rw [Matrix.mul_add, Matrix.trace_add, GlobalTheory.CompanionTheory.HermPoisson.halfTr_add', AddChar.map_add_eq_mul]

theorem chz_norm {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (a : hermA D ρ) :
    ‖chz ψ b₀ a‖ = 1 := hψ.2.1 _

theorem chz_cont {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) : Continuous (chz ψ b₀) :=
  GlobalTheory.CompanionTheory.HermPoisson.continuous_chi hψ (b₀.1.map (incA D) : Mx D ρ ρ)

theorem chz_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (l : ratHerm D ρ) :
    chz ψ b₀ l.1 = 1 :=
  GlobalTheory.CompanionTheory.HermPoisson.chi_rat hψ (m := (b₀.1.map (incA D) : Mx D ρ ρ)) ⟨b₀.1, rfl⟩ l

theorem continuous_jacobi_map_zero {hn : ρ + p = n} (M : Maps D hn) : Continuous fun z : hermA D ρ => M.nzx z 0 :=
  M.nzx_cont.comp (continuous_id.prodMk continuous_const)

set_option maxHeartbeats 1600000 in

theorem unfold_on {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {b₀ : HermE D ρ} (hb₀ : b₀.1.det ≠ 0) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {s : ℂ} {f : G D n → ℂ}
    (hf : Continuous f) (hl : IsLaw χ s f) (hs : (n : ℝ) / 2 < s.re) (C : Set (G D n)) (hC : IsCompact C) :
    ∃ Um : Cosets (P D n) (GF D n) → ℝ, Summable Um ∧
    ∃ e : ratHerm D ρ × (Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) → Cosets (P D n) (GF D n),
      Function.Injective e ∧ ∀ g ∈ C,
      (∀ u, ‖Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)‖ ≤ ∑' l : ratHerm D ρ, Um (e (l, u))) ∧
      HasSum (fun u : Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E =>
        Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)) (zc M m ψ b₀ (eisS f) g) := by
  obtain ⟨hinv, hdet, hmaj⟩ := GlobalTheory.T.eisenstein_terms_uniformly_summable hχ hf hl hs
  obtain ⟨hHaar, hFD, hvol⟩ := m.hz
  obtain ⟨hadd, hcsh, hcem, hrat⟩ := GlobalTheory.T.heisenberg_centre_rational_form M
  have hcolat := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := ρ)
  haveI : Countable (ratHerm D ρ) := countable_ratHerm
  haveI : Countable (Cosets (P D n) (GF D n)) := countable_cosets
  haveI : Countable (Cosets (P D p) (GF D p)) := countable_cosets
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) := countable_mat ρ p
  obtain ⟨e, he, hfib, hτe, hterm⟩ := GlobalTheory.T.heisenberg_cosets_param_rational hn M
  obtain ⟨K0, hK0, hKc⟩ := hcolat.2
  have hcn := continuous_jacobi_map_zero M
  obtain ⟨Um, hUm, hub⟩ := hmaj ((fun d : hermA D ρ × G D n => M.nzx d.1 0 * d.2) '' (K0 ×ˢ C))
    ((hK0.prod hC).image ((hcn.comp continuous_fst).mul continuous_snd))
  refine ⟨Um, hUm, e, he, fun g hg => ?_⟩
  let F : Cosets (P D n) (GF D n) → hermA D ρ → ℂ := fun q b => term (P D n) (GF D n) f (M.nzx b 0 * g) q
  let F0 : Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E → hermA D ρ → ℂ := fun u z =>
    f (M.w * M.nzx z 0 * (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g))
  let ch : hermA D ρ → ℂ := fun b => conj (chz ψ b₀ b)
  let τ : ratHerm D ρ → Cosets (P D n) (GF D n) ≃ Cosets (P D n) (GF D n) := fun l =>
    rmulEquiv _ _ ⟨M.nzx l.1 0, (hrat l).1⟩
  have hτ : ∀ (l : ratHerm D ρ) q b, F q ((l : hermA D ρ) + b) = F (τ l q) b := fun l q b => by
    simp only [F]
    rw [hadd, mul_assoc]
    exact term_mul_left hinv ⟨M.nzx l.1 0, (hrat l).1⟩ _ q
  have hchc : Continuous ch := Complex.continuous_conj.comp (chz_cont hψ b₀)
  have hF : ∀ q, Continuous (F q) := fun q =>
    hf.comp (continuous_const.mul (hcn.mul continuous_const))
  have hF0 : ∀ (l : ratHerm D ρ) u b, F (e (l, u)) b = F0 u ((l : hermA D ρ) + b) := fun l u b => by
    simp only [F, F0]
    rw [hterm f hinv, hadd]
    congr 1
    have h1 : M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * (M.nzx b 0 * g) =
        M.nzx b 0 * (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g) := by
      rw [← mul_assoc, mul_assoc (M.sh _), ← hcem, ← mul_assoc, ← hcsh]
      simp only [mul_assoc]
    simp only [mul_assoc] at h1 ⊢
    rw [h1]
  have key := GlobalTheory.T.fundamental_domain_unfolding_two_sums m.lz (ratHerm D ρ) m.𝓖 hFD hvol
    (fun q : Cosets (P D n) (GF D n) => zKer hn (ratOf q.out)) (⊥ : Submodule D.host.E (Fin ρ → D.host.E)) F F0 ch
    (fun q => (hF q).aestronglyMeasurable) hchc.aestronglyMeasurable
    (fun b => by simp only [ch, RCLike.norm_conj]; exact chz_norm hψ b₀ b)
    (fun a b => by simp only [ch]; rw [chz_add, map_mul])
    (fun l => by simp only [ch]; rw [chz_rat hψ b₀ l, map_one])
    Um hUm τ hτ
    (fun l q => by
      obtain ⟨ζ, -, hζ⟩ := (hrat l).2
      have := GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv (D := D) (n := n) q ⟨M.nzx l.1 0, (hrat l).1⟩ (bl hn ζ 0 0 0) hζ
      change (cosetCell (τ l q)).comap (zinc hn) = (cosetCell q).comap (zinc hn)
      rw [show cosetCell (τ l q) = cosetCell q from this])
    (fun b => by
      obtain ⟨γ, hγ, hb⟩ := hKc b
      refine ⟨-⟨γ, hγ⟩, fun q => ?_⟩
      have h1 := hτ (-⟨γ, hγ⟩) q (γ + b)
      have h2 : (((-⟨γ, hγ⟩ : ratHerm D ρ) : hermA D ρ) + (γ + b)) = b := by simp
      rw [h2] at h1
      rw [h1]
      exact hub _ _ ⟨(γ + b, g), ⟨hb, hg⟩, rfl⟩)
    e he hfib (fun l l' u => hτe l l' u (hrat l').1) hF0
    (fun y hy => by
      obtain ⟨ν, hν1, hν⟩ := GlobalTheory.T.nondegenerate_centre_character_cell hn hψ b₀ hb₀ y hy
      refine ⟨ν, ?_, fun q hq b => ?_⟩
      · intro h
        apply hν1
        have := congrArg (starRingEnd ℂ) h
        simpa [ch] using this
      · obtain ⟨x, hxP, a, ha, hd, hpe⟩ : ∃ x ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat x) = a.1 ∧
            Matrix.GeneralLinearGroup.det a = 1 ∧ (q.out : G D n) * M.nzx ν 0 = x * (q.out : G D n) := by
          obtain ⟨x, hx, a, ha, hd, hpe⟩ := hν (q.out : GF D n) (M.nzx ν 0) (q.out : GF D n).2 (ratOf q.out) (mat_ratOf _) hq
            (by rw [M.nzx_mat, adj_zero])
          exact ⟨x, hx, a, ha, hd, hpe⟩
        simp only [F, term]
        rw [hadd, mul_assoc (M.nzx ν 0), ← mul_assoc _ (M.nzx ν 0), hpe, mul_assoc, hdet x hxP a ha hd])
  refine ⟨fun u => ?_, ?_⟩
  · obtain ⟨hi, hle⟩ := key.1 u
    refine le_trans ?_ hle
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [F0, norm_mul, RCLike.norm_conj, chz_norm hψ b₀, mul_one]
  · exact key.2

theorem zUnfold : ZUnfold := by
  intro D n ρ p hn M m ψ hψ b₀ hb₀ χ hχ s f hf hl hs g
  refine ⟨?_, fun C hC => ?_⟩
  · obtain ⟨Um, -, e, -, h⟩ := unfold_on M m hψ hb₀ hχ hf hl hs {g} isCompact_singleton
    exact (h g rfl).2
  · obtain ⟨Um, hUm, e, he, h⟩ := unfold_on M m hψ hb₀ hχ hf hl hs C hC
    refine ⟨fun u => ∑' l : ratHerm D ρ, Um (e (l, u)), ?_, fun g hg u => (h g hg).1 u⟩
    have h1 : Summable (fun x : (Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) × ratHerm D ρ => Um (e (x.2, x.1))) :=
      hUm.comp_injective (he.comp Prod.swap_injective)
    exact h1.prod

end GlobalTheory.CompanionTheory.ZUnf
