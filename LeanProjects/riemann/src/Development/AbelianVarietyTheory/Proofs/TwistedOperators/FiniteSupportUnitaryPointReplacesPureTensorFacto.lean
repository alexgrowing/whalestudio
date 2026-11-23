import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryFactorFiniteSetOfPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.PlaceProd

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n}

theorem mat_injOne (g : UA σ X.J) (h : mat g = 1) : g = 1 := Subtype.ext (Units.ext h)

theorem mat_mul' (g k : UA σ X.J) : mat (g * k) = mat g * mat k := rfl

theorem mat_one' : mat (1 : UA σ X.J) = 1 := rfl

theorem mat_inv_mul' (g : UA σ X.J) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul', inv_mul_cancel, mat_one']

theorem one_mem_UAt {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  rw [mat_one', sub_self, smul_zero]

end GlobalTheory.PlaceProd

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaceProd GlobalTheory.AdelicU in

theorem GlobalTheory.PlaceProd.pure_of_finSupp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (gS : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J),
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ∧ (∀ v ∉ S, φ' v = φ v) ∧
        (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v) ∧
        om (gS, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' := by
  classical
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP S
  have hstd := hP.good.std
  induction S using Finset.induction_on with
  | empty =>
    intro gS hgS f φ hSB _
    have h1 : mat gS = 1 := by
      have := hgS 1 (by simp)
      rwa [one_smul, sub_eq_zero] at this
    have hg : gS = 1 := mat_injOne gS h1
    refine ⟨φ, hSB, fun _ _ => rfl, fun v => by simp, ?_⟩
    subst hg
    rw [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one]
    rfl
  | @insert v S' hv ih =>
    intro gS hgS f φ hSB hvac
    obtain ⟨g1, k, hgk, h2, h3, -, -⟩ := GlobalTheory.T.exists_adelicUnitary_factor_finiteSetOfPlaces σ X gS {v}
    have hg1 : g1 ∈ UAt σ X (evFin F v) := fun u hu =>
      h2 u (fun w hw => by rw [Finset.mem_singleton.1 hw]; exact hu)
    have hk : ∀ u : AF F, (∀ w ∈ S', evFin F w u = 0) → u • (mat k - 1) = 0 := by
      intro u hu
      set e : AF F := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he
      have hsplit : u = e * u + (1 - e) * u := by ring
      have ha : (e * u) • (mat k - 1) = 0 := by
        apply h3 v (Finset.mem_singleton_self v)
        rw [he, GlobalTheory.ThK.LocalOps.liftV_one_mul]
        intro u' hu'
        exact GlobalTheory.LatVac.at_liftV v _ u' hu'
      have hb : ((1 - e) * u) • (mat k - 1) = 0 := by
        set u' : AF F := (1 - e) * u with hu'def
        have hv' : evFin F v u' = 0 := by
          simp [hu'def, he, map_mul, map_sub, GlobalTheory.LatVac.evFin_liftV]
        have hS : u' • (mat gS - 1) = 0 := hgS u' (by
          intro w hw
          rcases Finset.mem_insert.1 hw with rfl | hw
          · exact hv'
          · simp [hu'def, map_mul, hu w hw])
        have hg1' : u' • (mat g1 - 1) = 0 := hg1 u' hv'
        have hkk : k = g1⁻¹ * gS := by rw [hgk, inv_mul_cancel_left]
        have hkdef : mat k - 1 = mat g1⁻¹ * (mat gS - 1) - mat g1⁻¹ * (mat g1 - 1) := by
          rw [hkk, mat_mul', Matrix.mul_sub, Matrix.mul_sub, mat_inv_mul', Matrix.mul_one]
          abel
        rw [hkdef, smul_sub, ← Matrix.mul_smul, ← Matrix.mul_smul, hS, hg1', Matrix.mul_zero, sub_self]
      rw [hsplit, add_smul, ha, hb, add_zero]
    obtain ⟨φ₁, hSB1, hoff1, haug1, hom1⟩ := ih k hk f φ hSB hvac
    obtain ⟨φ₂, hSB2, hact⟩ :=
      GlobalTheory.ThK.LocalOps.acts_exists hP v (g1, 1) hg1 (one_mem_UAt (evFin F v)) (φ₁ v) (hSB1 v)
    have hnot : ∀ᶠ w in Filter.cofinite, w ∉ S' :=
      Filter.eventually_cofinite.2 (S'.finite_toSet.subset fun x hx => by simpa using hx)
    have hstd1 : ∀ᶠ w in Filter.cofinite,
        φ₁ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
      filter_upwards [hvac, hstd, hnot] with w h1 h2 h3
      rw [hoff1 w h3, h1, h2]
    have hpure := GlobalTheory.TensUniq.pure_mem_schA f φ₁ hSB1 hstd1
    have hstep := GlobalTheory.ThK.LocalOps.acts_pure v (om (g1, 1)) f φ₁ φ₂ hpure
      (GlobalTheory.PureFactor.mulSupport_finite φ₁ hstd1) hact
    refine ⟨Function.update φ₁ v φ₂, ?_, ?_, ?_, ?_⟩
    · intro w
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hSB2
      · rw [Function.update_of_ne hw]; exact hSB1 w
    · intro w hw
      have hwv : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self _ _)
      have hwS : w ∉ S' := fun h => hw (Finset.mem_insert_of_mem h)
      rw [Function.update_of_ne hwv]; exact hoff1 w hwS
    · intro w
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self, ← hoff1 w hv]
        exact Submodule.subset_span ⟨g1, hg1, φ₁ w, hSB1 w, φ₂, hSB2, hact, rfl⟩
      · rw [Function.update_of_ne hw]; exact haug1 w
    · rw [hgk, show ((g1 * k, 1) : UA σ X.J × UA σ W.J) = (g1, 1) * (k, 1) by simp, map_mul,
        Module.End.mul_apply, hom1, hstep]
