import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalIwasawaDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanIwasawaDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory.AdelicIwasawaGlue

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

open Classical in

theorem exists_arch_part (x : ∀ w : InfinitePlace F, GArch σ J w) (s : Finset (InfinitePlace F)) :
    ∃ q : GAd σ J, (∀ v, proj σ J v q = 1) ∧ ∀ w, projArch σ J w q = if w ∈ s then x w else 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun v => map_one _, fun w => by simp⟩
  | insert w s hw ih =>
    obtain ⟨q, h1, h2⟩ := ih
    refine ⟨embArch σ J w (x w) * q, fun v => by simp [h1 v], fun u => ?_⟩
    by_cases e : u = w
    · subst e; simp [h2 u, hw]
    · rw [map_mul, projArch_embArch_ne σ J e, one_mul, h2 u]; simp [Finset.mem_insert, e]

open Classical in

theorem exists_fin_part (x : ∀ v : HeightOneSpectrum (𝓞 F), GLoc σ J v) (s : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ q : GAd σ J, (∀ w, projArch σ J w q = 1) ∧ ∀ v, proj σ J v q = if v ∈ s then x v else 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun w => map_one _, fun v => by simp⟩
  | insert v s hv ih =>
    obtain ⟨q, h1, h2⟩ := ih
    refine ⟨emb σ J v (x v) * q, fun w => by simp [h1 w], fun u => ?_⟩
    by_cases e : u = v
    · subst e; simp [h2 u, hv]
    · rw [map_mul, proj_emb_ne σ J e, one_mul, h2 u]; simp [Finset.mem_insert, e]

end GlobalTheory.AdelicIwasawaGlue

namespace GlobalTheory.AdelicIwasawa

open GlobalTheory.AdelicU GlobalTheory.AdelicIwasawaGlue

theorem iwasawa : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ g : GA D V, ∃ p : PA Φ.flag0, ∃ k ∈ (levelAll D.sp.cm.sig V.gram L a), g = p * k := by
  classical
  intro D V Φ L a hG g
  haveI : Submodule.IsLattice _ L := hG.1
  choose pf hpf kf hkf hf using fun v => GlobalTheory.T.local_iwasawa_decomposition D V Φ L a hG v (proj _ _ v g)
  choose pa hpa ka hka ha using fun w => GlobalTheory.T.archimedean_iwasawa_decomposition D V Φ L a hG w (projArch _ _ w g)
  have hS := (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram L g)
  set S := (Filter.eventually_cofinite.1 hS).toFinset with hSdef
  obtain ⟨qa, qa1, qa2⟩ := exists_arch_part D.sp.cm.sig V.gram pa Finset.univ
  obtain ⟨qf, qf1, qf2⟩ := exists_fin_part D.sp.cm.sig V.gram pf S
  have hp : qa * qf ∈ PA Φ.flag0 := by
    refine GlobalTheory.Cusp.IsoFlag.mem_par_adelic.2 ⟨fun w => ?_, fun v => ?_⟩
    · rw [map_mul, qa2 w, qf1 w, mul_one, if_pos (Finset.mem_univ w)]; exact hpa w
    · rw [map_mul, qa1 v, qf2 v, one_mul]
      split_ifs
      · exact hpf v
      · exact one_mem _
  refine ⟨⟨qa * qf, hp⟩, (qa * qf)⁻¹ * g, mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩, (mul_inv_cancel_left (qa * qf) g).symm⟩
  · rw [map_mul, map_inv, map_mul, qa1 v, qf2 v, one_mul]
    split_ifs with h
    · rw [hf v, inv_mul_cancel_left]; exact hkf v
    · rw [inv_one, one_mul]
      by_contra hc
      exact h ((Set.Finite.mem_toFinset _).2 hc)
  · rw [map_mul, map_inv, map_mul, qa2 w, qf1 w, mul_one, if_pos (Finset.mem_univ w), ha w, inv_mul_cancel_left]
    exact hka w

end GlobalTheory.AdelicIwasawa
