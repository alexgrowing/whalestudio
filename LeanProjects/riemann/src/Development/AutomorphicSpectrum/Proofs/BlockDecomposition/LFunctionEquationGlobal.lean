import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GammaFactorTransportRingEquiv
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteCoord
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation

section Trace

variable {K : Type} [Field K] [NumberField K]

abbrev aQ (p : Pl) (q : ℚ) : p.adicCompletion ℚ :=
  @algebraMap ℚ (p.adicCompletion ℚ) _ _ (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ p) q

end Trace

section Deg

variable {K : Type} [Field K] [NumberField K]

theorem finrank_pos' (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] :
    0 < Module.finrank (Qv v) (Kv K w) := by
  have : Module.Finite (Qv v) (Kv K w) := inferInstance
  exact Module.finrank_pos

theorem sum_finrank' (h2 : Module.finrank ℚ K = 2) (v : Pl) :
    ∑ u : SemiLocal.PlacesOver K v, Module.finrank (Qv v) (Kv K u.1) = 2 :=
  (SemiLocal.sum_finrank_eq K v).trans h2

theorem places_split (h2 : Module.finrank ℚ K = 2) (v : Pl) (w₁ w₂ : PlK K)
    [i₁ : w₁.asIdeal.LiesOver v.asIdeal] [i₂ : w₂.asIdeal.LiesOver v.asIdeal] (hne : w₁ ≠ w₂) :
    (∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → w = w₁ ∨ w = w₂) ∧
      Module.finrank (Qv v) (Kv K w₁) = 1 ∧ Module.finrank (Qv v) (Kv K w₂) = 1 := by
  classical
  have hs := sum_finrank' h2 v
  set a : SemiLocal.PlacesOver K v := ⟨w₁, i₁⟩
  set b : SemiLocal.PlacesOver K v := ⟨w₂, i₂⟩
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h)
  have p₁ := finrank_pos' v w₁
  have p₂ := finrank_pos' v w₂
  have h3 : Module.finrank (Qv v) (Kv K w₁) + Module.finrank (Qv v) (Kv K w₂) ≤ 2 := by
    have := Finset.sum_le_sum_of_subset (f := fun u : SemiLocal.PlacesOver K v => Module.finrank (Qv v) (Kv K u.1))
      (Finset.subset_univ ({a, b} : Finset (SemiLocal.PlacesOver K v)))
    rw [Finset.sum_pair hab, hs] at this
    exact this
  refine ⟨fun w hw => ?_, by omega, by omega⟩
  by_contra hc
  push_neg at hc
  set c : SemiLocal.PlacesOver K v := ⟨w, hw⟩
  have hca : c ≠ a := fun h => hc.1 (congrArg Subtype.val h)
  have hcb : c ≠ b := fun h => hc.2 (congrArg Subtype.val h)
  have p₃ : 0 < Module.finrank (Qv v) (Kv K w) := by
    haveI := hw
    exact finrank_pos' v w
  have := Finset.sum_le_sum_of_subset (f := fun u : SemiLocal.PlacesOver K v => Module.finrank (Qv v) (Kv K u.1))
    (Finset.subset_univ ({c, a, b} : Finset (SemiLocal.PlacesOver K v)))
  rw [Finset.sum_insert (by simp [hca, hcb]), Finset.sum_pair hab, hs] at this
  have e : Module.finrank (Qv v) (Kv K w) + (Module.finrank (Qv v) (Kv K w₁) + Module.finrank (Qv v) (Kv K w₂)) ≤ 2 := this
  omega

theorem places_nonsplit (h2 : Module.finrank ℚ K = 2) (v : Pl) (w : PlK K)
    [i : w.asIdeal.LiesOver v.asIdeal] (hu : ∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) :
    Module.finrank (Qv v) (Kv K w) = 2 := by
  haveI : Unique (SemiLocal.PlacesOver K v) := ⟨⟨⟨w, i⟩⟩, fun x => Subtype.ext (hu x.1 x.2)⟩
  have hs := sum_finrank' h2 v
  rw [Fintype.sum_unique] at hs
  have : (default : SemiLocal.PlacesOver K v) = ⟨w, i⟩ := Subsingleton.elim _ _
  rw [this] at hs
  exact hs

end Deg

section Places

variable {K : Type} [Field K] [NumberField K]

theorem isUnit1_localCharK (c : HeckeCharacter K) (w : PlK K) : IsUnit1 (localChar c w) :=
  ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c w, fun x => by
    rw [GroundTheory.Automorphic.GodementSection.coe_localChar]; exact Circle.norm_coe _⟩

theorem isUnit1_cAt (c : HeckeCharacter K) (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] :
    IsUnit1 (cAt c v w) :=
  ⟨(isUnit1_localCharK c w).1.comp (Continuous.units_map _ (_root_.continuous_algebraMap (Qv v) (Kv K w))),
    fun x => (isUnit1_localCharK c w).2 _⟩

theorem algebraMap_bijective (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal]
    (h1 : Module.finrank (Qv v) (Kv K w) = 1) : Function.Bijective (algebraMap (Qv v) (Kv K w)) := by
  refine ⟨(algebraMap (Qv v) (Kv K w)).injective, fun y => ?_⟩
  have hy : y ∈ (⊥ : Subalgebra (Qv v) (Kv K w)) := by
    rw [Subalgebra.bot_eq_top_of_finrank_eq_one h1]; trivial
  exact Algebra.mem_bot.1 hy

end Places

theorem continuous_charInv {A : Type} [AddCommGroup A] [TopologicalSpace A] (ψ : AddChar A Circle) (h : Continuous ψ) :
    Continuous (⇑(ψ⁻¹ : AddChar A Circle)) := by
  have : (⇑(ψ⁻¹ : AddChar A Circle)) = fun x => (ψ x)⁻¹ := by
    funext x; rw [AddChar.inv_apply, AddChar.map_neg_eq_inv]
  rw [this]
  exact h.inv

end GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation
