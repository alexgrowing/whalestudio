import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionarySizeBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TranslatedJetsDictionary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionarySizeBoundStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
namespace GlobalTheory.DictFree
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
end GlobalTheory.DictFree
namespace GlobalTheory.DictFree
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 MvPolynomial
end GlobalTheory.DictFree
namespace GlobalTheory.DictFree
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 MvPolynomial
theorem twisted_dictionary_eventually_large : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun ch => GlobalTheory.SumSize.DictAt ch := by
  intro hP hI
  obtain ⟨CF0, hCF⟩ := _root_.GlobalTheory.T.translated_jets_dictionary hP hI
  refine ⟨CF0, fun ε CF hCF0 => ?_⟩
  obtain ⟨x₀, hx⟩ := hCF ε CF hCF0
  refine ⟨x₀, ?_⟩
  intro D large₂ hε hx₀ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt
  have H2 := hx D large₂ hε hx₀ Γ Pl0 T A Ks R F hS ch hIs hAt
  intro t p hp k d hk hcos hz hP' x y
  obtain ⟨Ls, Lt, κ, hLs, hLt, hκ, hdiff, hq, htr⟩ := H2 p hp x y
  obtain ⟨n, c, w, hwL, hwf, hcI, hcN, hvec⟩ := GlobalTheory.T.cosetDatumVector_finite_heisenbergCombination ch.S.toGridChoice t p hp k d hk hcos hz hP'
  choose ζ s hζ hs hjet using fun i => htr k hk (w i) (hwL i)
  refine ⟨Ls, Lt, κ, n, fun i => oppQ p (c i) * ζ i, s, hLs, hLt, hκ, hs, fun i => ?_, fun ρ => ?_, hq, fun mon => ?_⟩
  · obtain ⟨m, hm, hζm⟩ := hζ i
    have hζi : IsIntegral ℤ (ζ i) := ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [hζm]⟩
    have e : (k : Qbar) ^ (D.R.f * (ch.G.pS p).rank * (ch.G.pT p).rank) * (oppQ p (c i) * ζ i) =
        oppQ p ((k : Qbar) ^ (D.R.f * (ch.G.pS p).rank * (ch.G.pT p).rank) * c i) * ζ i := by
      rw [map_mul, map_pow, map_natCast]; ring
    rw [e]
    exact ((hcI i).map (oppQ p).toIntAlgHom).mul hζi
  · have h1 : ∀ i, ‖ρ (ζ i)‖ = 1 := fun i => by
      obtain ⟨m, hm, hζm⟩ := hζ i
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 (by rw [← norm_pow, ← map_pow, hζm, map_one, norm_one])
    calc ∑ i, ‖ρ (oppQ p (c i) * ζ i)‖ = ∑ i, ‖(ρ.comp (oppQ p)) (c i)‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, norm_mul, h1, mul_one]; rfl
      _ ≤ 1 := hcN _
  · have hvac : IsThetaFunO ch.W.ψ _ _ (ch.S.Z.vac p) := (ch.S.Z.vac_is p hp).2.theta
    show jetTab ch.W ch.S.N.frC p (ch.S.Z.vec d) _ _ mon = _
    rw [hvec, jetTab_comb ch.W ch.S.N.frC p hvac _ w hwf]
    simp only [hjet]
    set Gt := Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
      (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p) with hGt
    set M := MvPolynomial.monomial (mon.mapDomain (fvar ch.G p)) (1 : ℂ)
    set Per := (mon.mapDomain (fvar ch.G p)).prod fun v e => period ch.S.Z.δ v.1 ^ e
    have hGi : ∀ i, Differentiable ℂ (fun z => κ * ((ζ i : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) Gt z)) :=
      fun i => ((differentiable_U _ (s i) hdiff).const_mul _).const_mul _
    have hfun : (fun z => κ * ∑ i, ((oppQ p (c i) * ζ i : Qbar) : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) Gt z) =
        ∑ i ∈ Finset.univ, ((oppQ p (c i) : Qbar) : ℂ) • fun z => κ * ((ζ i : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) Gt z) := by
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    rw [hfun, GlobalTheory.NormSum.RepInv.applyAt0_sum _ _ _ hGi, Finset.mul_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [oppQ_coe]
    simp only [map_mul, opp_opp]
    ring
end GlobalTheory.DictFree
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_dictionary_correspondence : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun ch => GlobalTheory.SumSize.DictAt ch := by
  first | exact @_root_.GlobalTheory.DictFree.twisted_dictionary_eventually_large | exact _root_.GlobalTheory.DictFree.twisted_dictionary_eventually_large | (intros; apply _root_.GlobalTheory.DictFree.twisted_dictionary_eventually_large <;> assumption)
end
