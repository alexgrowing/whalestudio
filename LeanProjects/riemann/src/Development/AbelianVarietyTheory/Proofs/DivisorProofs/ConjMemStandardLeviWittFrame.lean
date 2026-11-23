import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceFromModelStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.Cusp.ConjLevi

variable {D : D7} {V : HSp D}

theorem ratAct_mul_apply (a b : GF V) (v : V.V) :
    GlobalTheory.Cusp.ratAct D.sp.cm V (a * b) v = GlobalTheory.Cusp.ratAct D.sp.cm V a (GlobalTheory.Cusp.ratAct D.sp.cm V b v) := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (a * b).1.1 = a.1.1 * b.1.1 from rfl, Matrix.toLin_mul V.frame V.frame V.frame]
  rfl

theorem ratAct_one_apply (v : V.V) : GlobalTheory.Cusp.ratAct D.sp.cm V 1 v = v := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (1 : GF V).1.1 = 1 from rfl, Matrix.toLin_one]
  rfl

theorem ratAct_inv_apply (g : GF V) (v : V.V) :
    GlobalTheory.Cusp.ratAct D.sp.cm V g⁻¹ (GlobalTheory.Cusp.ratAct D.sp.cm V g v) = v := by
  rw [← ratAct_mul_apply, inv_mul_cancel, ratAct_one_apply]

theorem conj_maps (γ g : GF V) (S : Submodule D.host.E V.V)
    (h : ∀ v ∈ S, GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ S) :
    ∀ w ∈ S.map (GlobalTheory.Cusp.ratAct D.sp.cm V g),
      GlobalTheory.Cusp.ratAct D.sp.cm V (g * γ * g⁻¹) w ∈ S.map (GlobalTheory.Cusp.ratAct D.sp.cm V g) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [ratAct_mul_apply, ratAct_inv_apply, ratAct_mul_apply]
  exact ⟨_, h y hy, rfl⟩

theorem map_span_range (g : GF V) {a : ℕ} (x : Fin a → V.V) (y : Fin a → V.V)
    (hx : ∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = y i) :
    (Submodule.span D.host.E (Set.range x)).map (GlobalTheory.Cusp.ratAct D.sp.cm V g) =
      Submodule.span D.host.E (Set.range y) := by
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext i
  exact hx i

end GlobalTheory.Cusp.ConjLevi

open GlobalTheory.Cusp.ConjLevi in

theorem GlobalTheory.Cusp.ConjLevi.conj_mem_levi_stdVec : ∀ {D : D7} {V : HSp D} (Φ : WittFrame V) (γ g : GF V) {a : ℕ} (ha : a ≤ wittIndex V) (j : Fin (wittIndex V)), j.val + 1 = a → ∀ (x x' : Fin a → V.V), (∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = Φ.e (Fin.castLE ha i)) → (∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x' i) = Φ.f (Fin.castLE ha i)) → (∀ v ∈ Submodule.span D.host.E (Set.range x), GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ Submodule.span D.host.E (Set.range x)) → (∀ v ∈ Submodule.span D.host.E (Set.range x'), GlobalTheory.Cusp.ratAct D.sp.cm V γ v ∈ Submodule.span D.host.E (Set.range x')) → rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) {stdVec j} := by
  intro D V Φ γ g a ha j hj x x' hx hx' h1 h2
  have hmem : ∀ i : Fin (wittIndex V), i ≤ j ↔ ∃ k : Fin a, Fin.castLE ha k = i := fun i => by
    constructor
    · intro hi
      exact ⟨⟨i.val, by have := Fin.le_def.1 hi; omega⟩, Fin.ext rfl⟩
    · rintro ⟨k, rfl⟩
      exact Fin.le_def.2 (by simp only [Fin.val_castLE]; omega)
  have hE : Φ.sub (stdVec j) = Submodule.span D.host.E (Set.range fun i : Fin a => Φ.e (Fin.castLE ha i)) := by
    rw [WittFrame.sub]
    congr 1
    ext v
    simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, stdVec]
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · by_cases h : i ≤ j
        · obtain ⟨k, rfl⟩ := (hmem i).1 h; exact ⟨k, rfl⟩
        · rw [if_neg h] at hi; exact absurd hi (by decide)
      · by_cases h : i ≤ j
        · rw [if_pos h] at hi; exact absurd hi (by decide)
        · rw [if_neg h] at hi; exact absurd hi (by decide)
    · rintro ⟨k, rfl⟩
      exact Or.inl ⟨_, by rw [if_pos ((hmem _).2 ⟨k, rfl⟩)], rfl⟩
  have hF : Φ.sub (-stdVec j) = Submodule.span D.host.E (Set.range fun i : Fin a => Φ.f (Fin.castLE ha i)) := by
    rw [WittFrame.sub]
    congr 1
    ext v
    simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, stdVec, Pi.neg_apply]
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · by_cases h : i ≤ j
        · rw [if_pos h] at hi; exact absurd hi (by decide)
        · rw [if_neg h] at hi; exact absurd hi (by decide)
      · by_cases h : i ≤ j
        · obtain ⟨k, rfl⟩ := (hmem i).1 h; exact ⟨k, rfl⟩
        · rw [if_neg h] at hi; exact absurd hi (by decide)
    · rintro ⟨k, rfl⟩
      refine Or.inr ⟨_, ?_, rfl⟩
      rw [if_pos ((hmem _).2 ⟨k, rfl⟩)]
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  unfold WittFrame.levi
  simp only [Finset.mem_singleton, iInf_iInf_eq_left]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH _ _ _ (g * γ * g⁻¹) ∈ _
    rw [GlobalTheory.Cusp.diagH_mem_parab, hE, ← map_span_range g x _ hx]
    exact conj_maps γ g _ h1
  · show GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH _ _ _ (g * γ * g⁻¹) ∈ _
    rw [GlobalTheory.Cusp.diagH_mem_parab, hF, ← map_span_range g x' _ hx']
    exact conj_maps γ g _ h2
