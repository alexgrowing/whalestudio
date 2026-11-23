import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTestDivisorsKltLcPencilBoundariesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisorStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_pos_mul_lt_of_finite {ι : Type*} {T : Set ι} (hT : T.Finite) (A O : ι → ℚ)
    (hA : ∀ t ∈ T, 0 < A t) : ∃ c : ℚ, 0 < c ∧ ∀ t ∈ T, c * O t < A t := by
  have h : ∀ᶠ c in nhdsWithin (0 : ℚ) (Set.Ioi 0), ∀ t ∈ T, c * O t < A t :=
    (Filter.eventually_all_finite hT).2 fun t ht => by
      have h1 : Filter.Tendsto (fun c : ℚ => c * O t) (nhds 0) (nhds (0 * O t)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at h1
      exact nhdsWithin_le_nhds (h1.eventually (gt_mem_nhds (hA t ht)))
  obtain ⟨c, hc, hc'⟩ := (h.and self_mem_nhdsWithin).exists
  exact ⟨c, hc', hc⟩

theorem exists_pos_kltAt_add_smul : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (B : X → ℚ), 0 < m → IsLogCanonicalMultiple p n Δ m G → (∀ y, KltAt p n Δ y) → IsQCart B → ∃ c : ℚ, 0 < c ∧ ∀ y, KltAt p n (Δ + c • B) y := by
  intro hP X _ _ _ p n hproj hn Δ m G B hm hG hklt hB
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hproj
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hproj).1
  obtain ⟨η, hη, hGη⟩ := hG
  obtain ⟨m', D₀, hm', -, rfl⟩ := hB
  obtain ⟨S, hS, hSt⟩ := GlobalTheory.T.finite_test_divisors_klt_lc_pencil_boundaries hP X p n hproj hn η m G D₀ hη hm
  have hloc : ∀ x : X, ∃ (U : X.Opens) (g f : X.functionFieldˣ), x ∈ U ∧
      ∀ y ∈ U, G.IsEqn y g ∧ D₀.IsEqn y f := by
    intro x
    obtain ⟨g, hg⟩ := G.exists_isEqn x
    obtain ⟨f, hf⟩ := D₀.exists_isEqn x
    obtain ⟨U, hU, hgU⟩ := hg.exists_nhds
    obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
    exact ⟨U ⊓ V, g, f, ⟨hU, hV⟩, fun y hy => ⟨hgU y hy.1, hfV y hy.2⟩⟩
  choose U g f hxU hUeq using hloc
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => (U x : Set X))
    fun x => (U x).isOpen.mem_nhds (hxU x)
  let T : Set (DivOver p × X) := {q | q.1 ∈ S ∧ q.2 ∈ t ∧ ∃ y ∈ U q.2, q.1.Through y}
  have hT : T.Finite := (hS.prod t.finite_toSet).subset fun q hq => ⟨hq.1, hq.2.1⟩
  obtain ⟨c, hc, hcT⟩ := exists_pos_mul_lt_of_finite hT
    (fun q => discrep q.1 η m (g q.2) + 1) (fun q => (q.1.ord (f q.2) : ℚ)) (by
      rintro ⟨E, x₀⟩ ⟨-, -, y, hy, hEy⟩
      have := ((hGη y _ (hUeq x₀ y hy).1).kltAt_iff hn hη hm).1 (hklt y) E hEy
      simp only
      linarith)
  refine ⟨c * m', mul_pos hc (by exact_mod_cast hm'), fun y => ?_⟩
  obtain ⟨x₀, hx₀t, hy⟩ : ∃ x₀ ∈ t, y ∈ U x₀ := by
    have : y ∈ ⋃ x ∈ t, (U x : Set X) := ht.symm ▸ trivial
    simpa using this
  obtain ⟨hgy, hfy⟩ := hUeq x₀ y hy
  have hlog := hGη y _ hgy
  have hD : ∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z →
      qWeil D₀ m' z = (E.ord (f x₀) : ℚ) / m' := by
    intro z hz E hE
    rw [qWeil, (hUeq x₀ z (hz.mem_open (U x₀).isOpen hy)).2.mult_eq, hE.ord_eq]
  obtain ⟨m'', g'', hm'', hlog'', hdisc⟩ := GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ (qWeil D₀ m') η y m m' (g x₀)
    (f x₀) (c * m') hm hm' hlog hD
  refine (hlog''.kltAt_iff hn hη hm'').2 fun E hE => ?_
  rw [hdisc]
  have key := (hSt y (g x₀) (f x₀) c hgy hfy).1 (fun E' hE'S hE'y => by
    have := hcT (E', x₀) ⟨hE'S, hx₀t, y, hy, hE'y⟩
    simp only at this
    linarith) E hE
  have hm0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  have : c * m' * ((E.ord (f x₀) : ℚ) / m') = c * E.ord (f x₀) := by field_simp
  linarith

end GlobalTheory.PairStep
