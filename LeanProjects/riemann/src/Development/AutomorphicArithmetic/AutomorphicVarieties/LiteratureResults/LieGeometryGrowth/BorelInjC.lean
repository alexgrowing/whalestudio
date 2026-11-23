import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.G1
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CuspRapid
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DeRhamInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HarmEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HarmLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ImportsVariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SumCoordRe
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmEx
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a}

private theorem rapid_of_rapidD {q : ℕ} {ω : Co Ξ q} (h : RapidD ω) : Rapid ω := fun X N => h [] X N

private theorem ev_add' (x y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (g : GA E a) : ev (x + y) g = ev x g + ev y g := by
  ext i; simp [ev]

private theorem ev_smul' (c : ℂ) (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (g : GA E a) : ev (c • x) g = c • ev x g := by
  ext i; simp [ev]

private theorem rapid_sum {q s : ℕ} (ω : Fin s → Co Ξ q) (c : Fin s → ℂ) (h : ∀ i, Rapid (ω i)) :
    Rapid (∑ i, c i • ω i) := by
  have hq : ∀ g : GA E a, 0 ≤ qht g := fun g => zero_le_one.trans ((qhtFacts E a).1 g)
  refine Finset.sum_induction _ (fun ω : Co Ξ q => Rapid ω) ?_ ?_ ?_
  · intro α β hα hβ X N
    obtain ⟨C, hC⟩ := hα X N
    obtain ⟨D, hD⟩ := hβ X N
    refine ⟨C + D, fun g => ?_⟩
    rw [AlternatingMap.add_apply, ev_add']
    refine (mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg (hq _) N)).trans ?_
    rw [add_mul]
    exact add_le_add (hC g) (hD g)
  · intro X N
    refine ⟨0, fun g => ?_⟩
    have : ev ((0 : Co Ξ q) X) g.1 = 0 := by
      have := ev_smul' (Ξ := Ξ) 0 0 g.1
      simpa using this
    rw [this]; simp
  · intro i _ X N
    obtain ⟨C, hC⟩ := h i X N
    refine ⟨‖c i‖ * C, fun g => ?_⟩
    rw [AlternatingMap.smul_apply, ev_smul', norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg _)

private theorem noExact' (ha : 1 ≤ a) {n : ℕ} {e : Fin n → Herm E a} (he : IsFrame e) {U : Subgroup (GL (Fin a) (Af E))}
    (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) {r : ℝ} (hr : HasOne Ξ r)
    {q : ℕ} (ω : Co Ξ q) (hω : IsHarm U Ξ r e ω) (hR : Rapid ω) (hex : IsRelExact U Ξ ω) : ω = 0 := by
  cases q with
  | zero => exact hex
  | succ q =>
    obtain ⟨η, hη, rfl⟩ := hex
    obtain ⟨χ, hχ⟩ := twEx E a ha r
    obtain ⟨G, hG⟩ := admEx E a Ξ
    have hd : IsData Ξ r χ G e := ⟨hr, hχ, hG, he⟩
    have hL : IsLev U Ξ (dCo (smLie Ξ) η) := ((harmLin E a n e U Ξ r (q + 1)).2 _).1 hω
    have hM : Moderate (dCo (smLie Ξ) η) := ⟨0, fun X => by
      obtain ⟨C, hC⟩ := hR X 0
      exact ⟨C, fun g => by simpa using hC g⟩⟩
    have hP := pairFacts E a ha Measure.haar U hUo Ξ r χ G n e hd (q + 1)
    exact hP.2.2.1 _ hL (hP.1 _ _ hL hL hR hM)
      (g1 E a ha Measure.haar U hUo hUc Ξ r χ G n e hd q _ η hL hη hR hω.coclosed hM)

theorem UpperTheory.V.Lit.Geo.borelInjC :
    UpperTheory.V.Published.BorelInjC := by
  intro E _ _ _ a ha U hUo hUc Ξ S hS hC
  classical
  obtain ⟨n, e, he⟩ := frameEx E a
  obtain ⟨r, hr⟩ := oneReal E a Ξ
  have hex : ∀ π : CuspSub E a, ∃ (q : ℕ) (ω : Co Ξ q),
      π ∈ S → ω ≠ 0 ∧ IsHarm U Ξ r e ω ∧ ∀ X, ω X ∈ tens Ξ.d π.V := fun π => by
    by_cases h : π ∈ S
    · obtain ⟨q, ω, hω⟩ := harmEx E a ha n e he U hUc π Ξ r hr (hC π h).1 (hC π h).2
      exact ⟨q, ω, fun _ => hω⟩
    · exact ⟨0, 0, fun h' => absurd h' h⟩
  choose deg w hw using hex
  refine UpperTheory.V.Lit.Bor.count _ S deg _ fun q s f hf hq => ?_
  have hex2 : ∀ i, ∃ ω : Co Ξ q, ω ≠ 0 ∧ IsHarm U Ξ r e ω ∧ ∀ X, ω X ∈ tens Ξ.d (f i).V := fun i => by
    obtain ⟨hi, rfl⟩ := hq i
    exact ⟨w _, hw _ hi⟩
  choose ω h0 hH hV using hex2
  refine deRhamInj E a ha U hUo hUc Ξ q s ω
    (fun i => ⟨((harmLin E a n e U Ξ r q).2 _).1 (hH i), (hH i).closed⟩) fun c hc => ?_
  exact indep E a Ξ.d q s f (fun i j h => hf (hS _ (hq i).1 _ (hq j).1 h)) ω h0 hV c
    (noExact' ha he hUo hUc hr _ ((harmLin E a n e U Ξ r q).1 s ω c hH)
      (rapid_sum ω c fun i => rapid_of_rapidD (cuspRapid E a (f i) Ξ q (ω i) (hV i))) hc)

end
