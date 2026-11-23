import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PExactSequence
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact
import GroundTheory.HeightsAndTheta.Heights.Slopes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SlopeBoundComparableMetricStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeFullRankSublatticeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeBoundedMapStatement
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PtBoundary

variable {K : Type} [Field K] [NumberField K]

theorem finrank_submodule_of_torsion {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] (N : Submodule R M) (h : ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x ∈ N) :
    Module.finrank R N = Module.finrank R M := by
  have h0 : Module.rank R (M ⧸ N) = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    obtain ⟨a, ha, hax⟩ := h x
    refine ⟨a, ha, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hax
  have h1 := rank_quotient_add_rank_of_isDomain N
  rw [h0, zero_add] at h1
  simp only [Module.finrank, h1]

theorem saturated_ker (E E' : HermitianBundle.{0} K) (q : E.carrier →ₗ[𝓞 K] E'.carrier) :
    E.Saturated (LinearMap.ker q) := by
  intro a x ha hx
  rw [LinearMap.mem_ker, map_smul] at hx
  rw [LinearMap.mem_ker]
  have : Module.IsTorsionFree (𝓞 K) E'.carrier := inferInstance
  exact (smul_eq_zero.mp hx).resolve_left ha

def barMap (E E' : HermitianBundle.{0} K) (P : Submodule (𝓞 K) E.carrier) (hP : E.Saturated P)
    (q : E.carrier →ₗ[𝓞 K] E'.carrier) (hq : P ≤ LinearMap.ker q) :
    (E.quot P hP).carrier →ₗ[𝓞 K] E'.carrier :=
  P.liftQ q hq

theorem sqAt_barMap_le (E E' : HermitianBundle.{0} K) (P : Submodule (𝓞 K) E.carrier)
    (hP : E.Saturated P) (q : E.carrier →ₗ[𝓞 K] E'.carrier) (hq : P ≤ LinearMap.ker q) (c : ℝ)
    (h : ∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier),
      sqAt E' σ (q.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x)
    (σ : K →+* ℂ) (y : Fibre σ (E.quot P hP).carrier) :
    sqAt E' σ ((barMap E E' P hP q hq).lTensor (ComplexAt σ) y) ≤
      c * sqAt (E.quot P hP) σ y := by
  letI := HermitianBundle.quot_projective hP
  let V := subFibre E.metric σ P
  let y' : Fibre σ (E.carrier ⧸ P) := y
  let s : Fibre σ E.carrier := fibreMap σ (HermitianBundle.quotSection E P hP) y'
  let v : FibreSpace E.metric σ := HermitianBundle.quotFibreMap E P hP σ y
  let x : Fibre σ E.carrier := (FibreSpace.equiv E.metric σ).symm v
  have hvx : FibreSpace.equiv E.metric σ x = v := by simp [x]
  have hdiff : FibreSpace.equiv E.metric σ s - v ∈ V := by
    have hv : v = Vᗮ.starProjection (FibreSpace.equiv E.metric σ s) := rfl
    have e : Vᗮ.starProjection (FibreSpace.equiv E.metric σ s) =
        FibreSpace.equiv E.metric σ s - V.starProjection (FibreSpace.equiv E.metric σ s) := by
      rw [Submodule.starProjection_orthogonal']
      rfl
    rw [hv, e, sub_sub_cancel]
    exact V.starProjection_apply_mem _
  obtain ⟨w, hw⟩ := hdiff
  have hw' : fibreMap σ P.subtype w = s - x := by
    apply (FibreSpace.equiv E.metric σ).injective
    rw [map_sub, hvx]
    exact hw
  have hsub : q ∘ₗ P.subtype = 0 := by
    ext z
    exact hq z.2
  have hsec : q ∘ₗ HermitianBundle.quotSection E P hP = P.liftQ q hq := by
    have h1 : P.liftQ q hq ∘ₗ P.mkQ = q := Submodule.liftQ_mkQ P q hq
    calc q ∘ₗ HermitianBundle.quotSection E P hP
        = P.liftQ q hq ∘ₗ (P.mkQ ∘ₗ HermitianBundle.quotSection E P hP) := by
          rw [← LinearMap.comp_assoc, h1]
      _ = P.liftQ q hq := by
          rw [HermitianBundle.mkQ_comp_quotSection, LinearMap.comp_id]
  have hqx : (barMap E E' P hP q hq).lTensor (ComplexAt σ) y = q.lTensor (ComplexAt σ) x := by
    have h1 : fibreMap σ q s = (barMap E E' P hP q hq).lTensor (ComplexAt σ) y := by
      have h0 : fibreMap σ q s = fibreMap σ (P.liftQ q hq) y' :=
        (fibreMap_fibreMap σ q (HermitianBundle.quotSection E P hP) y').trans
          (congrArg (fun f => fibreMap σ f y') hsec)
      exact h0
    have h2 : fibreMap σ q (s - x) = 0 := by
      rw [← hw', fibreMap_fibreMap, hsub]
      simp [fibreMap]
    rw [map_sub, h1] at h2
    exact sub_eq_zero.mp h2
  have hnorm : sqAt (E.quot P hP) σ y = sqAt E σ x := by
    have h1 : sqAt E σ x = (inner ℂ (FibreSpace.equiv E.metric σ x) (FibreSpace.equiv E.metric σ x)).re := rfl
    rw [h1, hvx]
    rfl
  rw [hqx, hnorm]
  exact h σ x

theorem normDegree_top_eq (E : HermitianBundle.{0} K) :
    E.normDegree ⊤ = E.arithDegree / Module.finrank ℚ K := by
  rw [HermitianBundle.normDegree, HermitianBundle.degree_top_eq_arithDegree]

theorem final_real (C L ρ m x g : ℝ) (hC : 1 ≤ C) (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hm : 0 ≤ m) (hx : 0 ≤ x) (hg : 0 ≤ g)
    (hρg : ρ ≤ g) (hmx : m ≤ x + g * L) :
    C * Real.log (2 + ρ + m) + L / 2 ≤
      (C + g + g * L + L) * Real.log (2 + (C + g + g * L + L) + x) + (C + g + g * L + L) := by
  have hgL : 0 ≤ g * L := mul_nonneg hg hL
  set C' := C + g + g * L + L with hC'
  have h1 : 2 + ρ + m ≤ 2 + C' + x := by rw [hC']; linarith
  have h0 : 0 < 2 + ρ + m := by linarith
  have h2 : Real.log (2 + ρ + m) ≤ Real.log (2 + C' + x) := Real.log_le_log h0 h1
  have h3 : 0 ≤ Real.log (2 + ρ + m) := Real.log_nonneg (by linarith)
  have h4 : C ≤ C' := by rw [hC']; linarith
  have h5 : C * Real.log (2 + ρ + m) ≤ C' * Real.log (2 + C' + x) :=
    mul_le_mul h4 h2 h3 (by linarith)
  have h6 : L / 2 ≤ C' := by rw [hC']; linarith
  linarith

theorem slopeMax_le_log : ∀ (g : ℕ) (C : ℝ), 1 ≤ C → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (r : ℕ) (ε : Fin r → E.carrier) (q : E.carrier →ₗ[𝓞 K] E'.carrier), Module.finrank (𝓞 K) E.carrier = g → LinearIndependent (𝓞 K) ε → LinearMap.ker q = Submodule.span (𝓞 K) (Set.range ε) → (∀ e' : E'.carrier, ∃ (a : 𝓞 K) (e : E.carrier), a ≠ 0 ∧ q e = a • e') → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2) → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (q.lTensor (ComplexAt σ) x) ≤ C * sqAt E σ x) → E'.slopeMax ≤ ((C * Real.log (2 + Module.finrank (𝓞 K) E'.carrier + max (-E'.normDegree ⊤) 0) : ℝ) : EReal) → E.slopeMax ≤ ((C' * Real.log (2 + C' + max (-E.normDegree ⊤) 0) + C' : ℝ) : EReal) := by
  intro g C hC
  have hC0 : 0 < C := by linarith
  have hL : 0 ≤ Real.log C := Real.log_nonneg hC
  refine ⟨C + g + g * Real.log C + Real.log C, by positivity, ?_⟩
  intro K _ _ E E' r ε q hg hli hker hfull hgram hexp hslope
  set L := Real.log C with hLdef
  set P : Submodule (𝓞 K) E.carrier := Submodule.span (𝓞 K) (Set.range ε) with hPdef
  have hP : E.Saturated P := hker ▸ saturated_ker E E' q
  have hPq : P ≤ LinearMap.ker q := hker.ge
  set X := HermitianBundle.subQuotExtension E P hP with hX
  set φ := barMap E E' P hP q hPq with hφ
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have hφq : ∀ e, φ (P.mkQ e) = q e := fun e => rfl

  let b : Module.Basis (Fin r) (𝓞 K) (E.sub P).carrier := Module.Basis.span hli
  have hb : ∀ (σ : K →+* ℂ) (w : Fin r → ℂ),
      sqAt (E.sub P) σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) =
        sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) := by
    intro σ w
    have h1 : X.incl.lTensor (ComplexAt σ) (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) =
        ∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.lTensor_tmul]
      congr 1
      exact congrArg Subtype.val (Module.Basis.span_apply hli a)
    rw [← h1]
    simp only [sqAt]
    rw [X.incl_isometric]
  obtain ⟨hP1, hP2⟩ := GlobalTheory.T.slope_bound_comparable_metric K (E.sub P) r b C hC (fun σ w => by rw [hb]; exact hgram σ w)

  obtain ⟨hQ1, hQ2⟩ := GlobalTheory.T.normalized_degree_bounded_map K (E.quot P hP) E' φ C hφinj hC0
    (fun σ y => sqAt_barMap_le E E' P hP q hPq C hexp σ y)

  have hrP : Module.finrank (𝓞 K) (E.sub P).carrier = r := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hrk := X.finrank_eq
  have hrange : Module.finrank (𝓞 K) ((⊤ : Submodule (𝓞 K) (E.quot P hP).carrier).map φ) =
      Module.finrank (𝓞 K) E'.carrier := by
    apply finrank_submodule_of_torsion
    intro e'
    obtain ⟨a, e, ha, he⟩ := hfull e'
    exact ⟨a, ha, he ▸ ⟨P.mkQ e, trivial, hφq e⟩⟩
  have hrQ : Module.finrank (𝓞 K) (E.quot P hP).carrier = Module.finrank (𝓞 K) E'.carrier := by
    rw [← hrange, Submodule.map_top]
    exact (LinearMap.finrank_range_of_inj hφinj).symm
  have hsum : r + Module.finrank (𝓞 K) E'.carrier = g := by
    rw [← hg, hrk, hrP, hrQ]
  obtain ⟨hI1, -⟩ := GlobalTheory.T.normalized_degree_full_rank_sublattice K E' ((⊤ : Submodule (𝓞 K) (E.quot P hP).carrier).map φ) hrange

  have hdeg : E.normDegree ⊤ = (E.sub P).normDegree ⊤ + (E.quot P hP).normDegree ⊤ := by
    rw [normDegree_top_eq, normDegree_top_eq, normDegree_top_eq, X.arithDegree_eq_add, add_div]
  have hQd := hQ1 ⊤
  have hrkTop : (E.quot P hP).rank ⊤ = Module.finrank (𝓞 K) E'.carrier := by
    rw [HermitianBundle.rank, finrank_top, hrQ]
  rw [hrkTop] at hQd
  set ρ : ℕ := Module.finrank (𝓞 K) E'.carrier with hρ
  have hsumR : (r : ℝ) + ρ = g := by exact_mod_cast hsum
  have hP2' := (abs_le.mp hP2).2
  have hgL : (g : ℝ) * L = r * L + ρ * L := by rw [← hsumR]; ring
  have hrL : 0 ≤ (r : ℝ) * L := by positivity
  have hρL : 0 ≤ (ρ : ℝ) * L := by positivity
  have hm : max (-E'.normDegree ⊤) 0 ≤ max (-E.normDegree ⊤) 0 + g * L := by
    apply max_le
    · have := le_max_left (-E.normDegree ⊤) 0
      nlinarith
    · have := le_max_right (-E.normDegree ⊤) 0
      nlinarith
  have hreal := final_real C L ρ (max (-E'.normDegree ⊤) 0) (max (-E.normDegree ⊤) 0) g hC hL
    (by positivity) (le_max_right _ _) (le_max_right _ _) (by positivity)
    (by have : (0 : ℝ) ≤ r := by positivity
        linarith) hm
  have hfirst : L / 2 ≤ (C + g + g * L + L) * Real.log (2 + (C + g + g * L + L) + max (-E.normDegree ⊤) 0) + (C + g + g * L + L) := by
    have h0 : (0 : ℝ) ≤ g := by positivity
    have h1 : 0 ≤ (C + g + g * L + L) := by positivity
    have h2 : 0 ≤ Real.log (2 + (C + g + g * L + L) + max (-E.normDegree ⊤) 0) :=
      Real.log_nonneg (by have := le_max_right (-E.normDegree ⊤) 0; linarith)
    have h3 := mul_nonneg h1 h2
    nlinarith
  refine (SlopeMaxExtension.main K _ _ _ X).trans (max_le ?_ ?_)
  · exact hP1.trans (by exact_mod_cast hfirst)
  · refine hQ2.trans ((add_le_add_left hslope _).trans ?_)
    rw [← EReal.coe_add]
    exact_mod_cast hreal

end GlobalTheory.CompanionTheory.Ar.PtBoundary

end
