import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadraticPowerCharacterSplitPlacesValuesInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqValueEqOneAtInertPlaceOfRestrictsToQuadratic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerConjPos

open GlobalTheory.LFun GlobalTheory.LPositivity Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps (IsPosReal)

theorem lsd_pos : ∀ (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : GlobalTheory.LFun.Fam D.host.E) (μ : (AE D)ˣ →* Circle) (r : ℕ) (κ s : ℝ), IsHeckeChar D μ → ResEta D μ 0 → GlobalTheory.LFun.UnrOff (F := D.host.F) μ (S : Set (HeightOneSpectrum (𝓞 D.host.F))) → GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B r κ → κ + 1 < s → (∀ w ∉ GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))), (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w ≠ w' → B w' = (B w).map star) ∧ (¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → (B w).map star = B w)) → ∃ l : ℝ, 0 < l ∧ GlobalTheory.LFun.LSD D S B μ (s : ℂ) = l := by
  intro D S B μ r κ s _ hb hμ hB hs hst
  classical
  have hc := isCMExt_host D
  have hb' := (resEta_iff μ 0).1 hb
  have hcv : Converges (above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (twist B (val μ)⁻¹) (s : ℂ) :=
    hB.converges_twist_val μ (by simpa using hs)
  have hpos : IsPosReal (LS (S : Set (HeightOneSpectrum (𝓞 D.host.F))) (twist B (val μ)⁻¹) (s : ℂ)) := by
    refine isPosReal_of_hasProd (hasProd_Lv hcv) hcv.ne_zero fun v => ?_
    have hnot : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 →
        w ∉ above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))) := fun w hw e => v.2 (hw ▸ e)
    have hlt : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 →
        ∀ x ∈ twist B (val μ)⁻¹ w, ‖(x : ℂ) * npow w (-(s : ℂ))‖ < 1 := fun w hw =>
      norm_lt_one_of_bounded (hB.twist fun u _ => by simp [norm_val]) (by rw [Complex.ofReal_re]; linarith)
        (hnot w hw)
    have hun : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 → UnrAt μ w := fun w hw =>
      hμ w (hnot w hw)
    by_cases hv : IsSplit (E := D.host.E) v.1
    · obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v.1 := by
        obtain ⟨P, -, -, hP, -⟩ := hv
        exact ⟨P, HeightOneSpectrum.ext hP⟩
      obtain ⟨w', hne, hall, hN, hN', -⟩ := SplitChart.exists_conj_place hc hw hv
      have hw' := (hall w').2 (Or.inr rfl)
      have e : Formalism.L2.Host.aboveF (L := D.host.E) D.host.F v.1 = {w, w'} := by ext u; simp [mem_aboveF, hall]
      have e2 : npow w' (-(s : ℂ)) = npow w (-(s : ℂ)) := by rw [npow, npow, hN, hN']
      have e3 : twist B (val μ)⁻¹ w' = (twist B (val μ)⁻¹ w).map star := by
        have hm := GlobalTheory.T.quadraticPowerCharacter_splitPlaces_values_inverse _ _ _ hc μ 0 hb' w w' (hw.trans hw'.symm) hne (hun w hw) (hun w' hw')
        have hs' : (val μ w')⁻¹ = star (val μ w)⁻¹ := by
          rw [star_inv, star_eq_inv (norm_val μ w), inv_inv, eq_comm, eq_inv_iff_mul_eq_one, hm]
        simp only [twist, Pi.inv_apply, hs', Multiset.map_map, Function.comp_def, star_mul',
          (hst w (hnot w hw)).1 w' (hw'.trans hw.symm) hne]
      rw [Lv, e, Finset.prod_pair hne, locL, locL, e2, ← eulerFac_add]
      refine isPosReal_eulerFac (by
        rw [e3, Multiset.map_add, Multiset.map_map, add_comm]
        simp only [Function.comp_def, star_star, Multiset.map_id']) (star_npow _ _) fun x hx => ?_
      exact (Multiset.mem_add.1 hx).elim (hlt w hw x) (e2 ▸ hlt w' hw' x)
    · refine isPosReal_prod _ fun w hw => ?_
      have hw := mem_aboveF.1 hw
      have hi : IsInertAt D.host.F D.host.E v.1 w := hw ▸ (split_or_inert D w).resolve_left (hw ▸ hv)
      refine isPosReal_eulerFac ?_ (star_npow _ _) (hlt w hw)
      have hs' : star (val μ w)⁻¹ = (val μ w)⁻¹ := by
        rw [star_inv, star_eq_inv (norm_val μ w), inv_inv, eq_inv_iff_mul_eq_one, ← sq,
          GlobalTheory.T.sq_value_eq_one_at_inert_place_of_restrictsToQuadratic _ _ _ hc μ 0 hb' _ w hi (hun w hw)]
      have hBw := (hst w (hnot w hw)).2 (by rw [hw]; exact hv)
      conv_rhs => rw [twist, ← hBw]
      simp only [twist, Pi.inv_apply, hs', Multiset.map_map, Function.comp_def, star_mul']
  obtain ⟨l, hl, e⟩ := isPosReal_iff.1 hpos
  exact ⟨l, hl, e⟩

end GlobalTheory.EulerConjPos

end
