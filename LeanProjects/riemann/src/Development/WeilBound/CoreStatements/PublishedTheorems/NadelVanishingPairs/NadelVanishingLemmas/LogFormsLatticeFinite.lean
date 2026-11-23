import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LatticeModelFiniteQuasicoherent
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogFormsEqChartForms
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MemChartFormsIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCoordinateWedgeLinearIndependentSpanEqTop
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR

theorem mem_chartForms_iff_sum_card {K : Type} [Field K] (A : Subring K) {n : ℕ} (x : Fin n → Kˣ)
    (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) (η : abelian₂ K) :
    η ∈ chartForms A x J t a ↔ ∃ d : {I : Finset (Fin n) // I.card = a} → K, (∀ I, d I ∈ A) ∧
      η = ∑ I, d I • (((t⁻¹ * ∏ j ∈ I.1 \ J, x j : Kˣ) : K) • logWedge x I.1) := by
  classical
  rw [GlobalTheory.T.mem_chart_forms_iff K A n x J t a η]
  have ht : (t : K) ≠ 0 := t.ne_zero
  have hP : ∀ I : Finset (Fin n), ∏ j ∈ I \ J, (x j : K) ≠ 0 := fun I =>
    Finset.prod_ne_zero_iff.2 fun j _ => (x j).ne_zero
  have hsplit : ∀ f : Finset (Fin n) → abelian₂ K, (∀ I, I.card ≠ a → f I = 0) →
      ∑ I, f I = ∑ I : {I : Finset (Fin n) // I.card = a}, f I.1 := by
    intro f hf
    rw [← Fintype.sum_subtype_add_sum_subtype (fun I : Finset (Fin n) => I.card = a) f,
      Finset.sum_eq_zero (s := (Finset.univ : Finset {I : Finset (Fin n) // ¬ I.card = a}))
        (fun I _ => hf I.1 I.2), add_zero]
  constructor
  · rintro ⟨c, hc0, hcA, rfl⟩
    refine ⟨fun I => c I.1 * t / ∏ j ∈ I.1 \ J, (x j : K), fun I => hcA I.1, ?_⟩
    rw [hsplit (fun I => c I • logWedge x I) (fun I hI => by simp only [hc0 I hI, zero_smul])]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [smul_smul]
    congr 1
    have := hP I.1
    push_cast
    field_simp
  · rintro ⟨d, hdA, rfl⟩
    refine ⟨fun I => if h : I.card = a then d ⟨I, h⟩ * ((t⁻¹ * ∏ j ∈ I \ J, x j : Kˣ) : K) else 0,
      ?_, ?_, ?_⟩
    · intro I hI
      simp [hI]
    · intro I
      by_cases hI : I.card = a
      · dsimp only
        rw [dif_pos hI]
        have e : d ⟨I, hI⟩ * ((t⁻¹ * ∏ j ∈ I \ J, x j : Kˣ) : K) * t / ∏ j ∈ I \ J, (x j : K) =
            d ⟨I, hI⟩ := by
          have := hP I
          push_cast
          field_simp
        rw [e]
        exact hdA _
      · dsimp only
        rw [dif_neg hI, zero_mul, zero_div]
        exact zero_mem A
    · rw [hsplit (fun I => (if h : I.card = a then d ⟨I, h⟩ * ((t⁻¹ * ∏ j ∈ I \ J, x j : Kˣ) : K)
          else 0) • logWedge x I) (fun I hI => by simp only [dif_neg hI, zero_smul])]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [dif_pos I.2, smul_smul]

theorem latModel_logAt_isFiniteQC : ∀ (X : Scheme.{0}) [IsIntegral X] {C : Type} [Fintype C]
    (E : C → CartierDiv X) {n : ℕ} {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (a : ℕ)
    (F : X.Modules), LatModel (logAt (suppAll E) G a) F → GlobalTheory.QCoh.IsFiniteQC F := by
  intro X _ C _ E n ι 𝒜 G a F hF
  refine GlobalTheory.T.lattice_model_finite_quasicoherent X _ F hF fun y => ?_
  obtain ⟨i, hi⟩ : ∃ i, y ∈ 𝒜.U i := by
    have : y ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
    simpa [Opens.mem_iSup] using this
  obtain ⟨t, ht⟩ := G.exists_isEqn y
  obtain ⟨W, hyW, hW⟩ := ht.exists_nhds
  obtain ⟨f, hfW, hyf⟩ := (𝒜.affine i).exists_basicOpen_le (V := W) ⟨y, hyW⟩ hi
  let S := {I : Finset (Fin n) // I.card = a}
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let u : S → X.functionFieldˣ := fun I => t⁻¹ * ∏ j ∈ I.1 \ 𝒜.J i, 𝒜.x i j
  let g : S → abelian₂ X.functionField := fun I => ((u I : X.functionFieldˣ) : X.functionField) • logWedge (𝒜.x i) I.1
  refine ⟨X.basicOpen f, Fintype.card S, fun k => g (e k), hyf, (𝒜.affine i).basicOpen f, ?_, ?_⟩
  · have hc : IsCoord (𝒜.x i) := ((𝒜.chart i).chart _ (𝒜.gen i)).coord
    have h1 := (GlobalTheory.LogDR.logWedge_basis _ n (𝒜.x i) hc).1.comp (fun k => (e k).1)
      (Subtype.val_injective.comp e.injective)
    exact h1.units_smul (fun k => u (e k))
  · intro z hz w
    have hzU : z ∈ 𝒜.U i := X.basicOpen_le f hz
    have hzt : G.IsEqn z t := hW z (hfW hz)
    rw [GlobalTheory.T.log_forms_eq_chart_forms (suppAll E) (𝒜.U i) (𝒜.x i) (𝒜.J i) G z t a (𝒜.chart i) hzU hzt,
      mem_chartForms_iff_sum_card]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨fun k => d (e k), fun k => hd _, (e.sum_comp fun I => d I • g I).symm⟩
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun I => c (e.symm I), fun I => hc _, ?_⟩
      rw [← e.sum_comp]
      simp only [Equiv.symm_apply_apply]
      rfl

end GlobalTheory.LogDR
