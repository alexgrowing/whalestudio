import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealSpanPrimeVariableBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOfPowLeOfPowLeSameAdicTopologyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfSpanOfStrictStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictIndepPowOfRegularPairStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.AinfTopBasis

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    ∃ ι : Type, Nonempty (TopBasis bk.ev bk.J ι) := by
  intro l _ K bk
  obtain ⟨h0, hu, -, hJ⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  obtain ⟨ι, b, i₀, hb, hspan, hind⟩ := GlobalTheory.T.ideal_span_prime_variable_basis l K bk
  have he := bk.deg_pos
  have hstrict := GlobalTheory.T.strict_indep_pow_of_regular_pair bk.S (Ainf l) bk.ev (l : bk.S) X ι b
    (fun x hx => by
      rw [map_natCast, mul_comm] at hx
      exact WittVector.eq_zero_of_p_mul_eq_zero x hx)
    (fun x hx => by
      rw [map_natCast, ← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker] at hx ⊢
      rw [map_mul, bk.ev_X, WittVector.constantCoeff_apply (x := WittVector.teichmuller l _),
        WittVector.teichmuller_coeff_zero] at hx
      exact (mul_eq_zero.1 hx).resolve_left h0) hind
  have hS : IsAdicComplete (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}) bk.S := by
    have h := ReciprocityTheory.P1.isAdicComplete_comap_constantCoeff (Ideal.span {(l : Wq l bk.a)})
    rwa [← ReciprocityTheory.P1.map_C_sup_span_X, Ideal.map_span, Set.image_singleton, map_natCast] at h
  have hA : IsAdicComplete ((Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev) (Ainf l) := by
    rw [← Ideal.span_insert, Ideal.map_span, Set.image_pair, map_natCast]
    refine (GlobalTheory.Per.AinfComplete.main l _ fun h => hu ?_).1
    have h2 := h.map (WittVector.constantCoeff (p := l) (R := OCb l))
    rwa [bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h2
  obtain ⟨TB, -⟩ := GlobalTheory.T.exists_adicTopologicalBasis_of_span_of_strict bk.S (Ainf l) bk.ev _ ι b i₀ hb
    (Submodule.FG.sup (Submodule.fg_span_singleton _) (Submodule.fg_span_singleton _)) hS hA hspan hstrict
  obtain ⟨TB', -⟩ := GlobalTheory.T.exists_of_pow_le_of_pow_le_same_adicTopology bk.S (Ainf l) bk.ev _ ι TB bk.J (1 + bk.Ep.natDegree) 1
    hS.toIsHausdorff (by omega) one_pos
    (by
      rw [← hJ]
      refine Ideal.sup_pow_add_le_pow_sup_pow.trans ?_
      rw [pow_one, Ideal.span_singleton_pow])
    (by
      rw [pow_one, ← hJ]
      refine sup_le_sup_left ?_ _
      rw [Ideal.span_singleton_le_span_singleton]
      exact dvd_pow_self _ he.ne')
  exact ⟨ι, ⟨TB'⟩⟩

end GlobalTheory.BSP.AinfTopBasis
