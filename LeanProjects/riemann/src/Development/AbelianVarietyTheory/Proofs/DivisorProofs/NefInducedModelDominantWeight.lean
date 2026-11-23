import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DominantInducedModelReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjModelClosedFiberIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefDominantWeightPositivityStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open Limits

namespace GlobalTheory.NefDeRhamCore

theorem descend (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
    (hp : IsProjOver p) (hq : IsProjOver q) (π : Y ⟶ X) (hπ : π ≫ p = q) (hsurj : Function.Surjective π) (L : HermLB p)
    (r : ℕ) [Fact r.Prime]
    (hL : ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod r) Γ(Z, ⊤)],
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod r) ((L.pull π hπ).B.pull i) 1) :
    ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod r) Γ(Z, ⊤)],
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod r) (L.B.pull i) 1 := by
  intro Z i _ _ _ hd
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hq).1
  have : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π p
  have : Surjective π := ⟨hsurj⟩
  have : IsNoetherian Y := isNoetherian_of_isProjOver hq
  have : IsNoetherian X := isNoetherian_of_isProjOver hp
  have : IsNoetherian Z := by
    have := LocallyOfFiniteType.isLocallyNoetherian i
    have := QuasiCompact.compactSpace_of_compactSpace i
    exact {}
  let g := pullback.snd π i
  have : IsProper g := inferInstance
  have : Surjective g := inferInstance
  obtain ⟨w, hw, hdeg⟩ := GlobalTheory.NefDescent.fibre_point _ Z g (genericPoint Z) (g.surjective _)
  let C : Closeds (pullback π i : Scheme.{0}) := ⟨closure {w}, isClosed_closure⟩
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  have hgen := GlobalTheory.NefDescent.red_genericPoint _ w C rfl
  let f := redι C ≫ g
  let i' := redι C ≫ pullback.fst π i
  have hη : f (genericPoint _) = genericPoint Z := by
    simp only [f, Scheme.Hom.comp_apply, hgen, hw]
  have hdeg' : 0 < f.residueDegree (genericPoint _) := by
    simp only [f, CurveDegreesCompare.residueDegree_comp, hgen, GlobalTheory.Published.residueDegree_of_isClosedImmersion, mul_one]
    exact hdeg
  have hd' := GlobalTheory.NefDescent.dim_eq_one _ Z f hd hη hdeg'
  have : IsNoetherian (Scheme.IdealSheafData.vanishingIdeal C).subscheme := by
    have := LocallyOfFiniteType.isLocallyNoetherian i'
    have := QuasiCompact.compactSpace_of_compactSpace i'
    exact {}
  have : IsFinite f := GlobalTheory.NefDescent.isFinite_of_dim _ Z f hd' hd hη
  letI : Algebra (ZMod r) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) := algebraΓAlong (ZMod r) f
  have h1 := hL _ i' hd'
  have hN : (L.B.pull i).IsLB := LB.isLB_pull L.isLB i
  have hcomm : i' ≫ π = f ≫ i := by simp only [i', f, g, Category.assoc, pullback.condition]
  have e1 : topSelfIntersection (ZMod r) ((L.pull π hπ).B.pull i') 1 = topSelfIntersection (ZMod r) ((L.B.pull i).pull f) 1 := by
    rw [topSelf_def, topSelf_def]
    refine interNum_congr_cls (ZMod r) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB π) i')
      (fun _ => LB.isLB_pull hN f) fun _ => ?_
    show pull i' (pull π (cls L.B L.isLB)) = pull f (pull i (cls L.B L.isLB))
    rw [← pull_comp, ← pull_comp, hcomm]
  have e2 : topSelfIntersection (ZMod r) ((L.B.pull i).pull f) 1 = interNumOn (ZMod r) f (fun _ : Fin 1 => L.B.pull i) :=
    (interNumOn_const_eq_topSelf (k := ZMod r) (fun _ => rfl) hN 1).symm
  have e3 : interNumOn (ZMod r) f (fun _ : Fin 1 => L.B.pull i) = interNumOn (ZMod r) f ![L.B.pull i] :=
    congrArg _ (funext fun j => by fin_cases j; rfl)
  have hproj : IsProjOver (strHom (ZMod r) Z) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom (ZMod r) Z ≫ spMap (Int.castRingHom (ZMod r)) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod r) Z ≫ spMap (Int.castRingHom (ZMod r))) := by rw [e]; infer_instance
    have : IsProper (strHom (ZMod r) Z) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod r)))
    exact ProperCurve.isProjOver_of_isProper _ hd
  have e4 := GlobalTheory.T.intersection_number_finite_pushforward (ZMod r) Z _ f hproj hd hη (L.B.pull i) hN
  have e5 : interNum (ZMod r) (structureModule Z) ![L.B.pull i] = topSelfIntersection (ZMod r) (L.B.pull i) 1 := by
    rw [topSelf_def]
    exact congrArg _ (funext fun j => by fin_cases j; rfl)
  have hT : 0 ≤ (f.residueDegree (genericPoint _) : ℤ) * topSelfIntersection (ZMod r) (L.B.pull i) 1 := by
    rw [← e5, ← e4, ← e3, ← e2, ← e1]
    exact h1
  exact nonneg_of_mul_nonneg_right hT (by exact_mod_cast hdeg')

theorem exists_model_nonneg : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H →
  ∀ (B : ℝ), 2 ≤ B → ∀ (u : Wt O.Y) (s : ℚ), IsRat O.Y u → 0 < s → WeightThresholdDefs.Dominant O.Y (A.sh u s) → NefCond O.Y B (A.sh u s) →
  ∀ (c : O.s.Comp) (M : TrueGeo.Model (O.var c)) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ),
  (O.Mb B u s c).Induced M L k cf → ∀ (q : ℕ) [Fact q.Prime], q ∉ FlagAr.setB O.Y B →
  ∃ (N : TrueGeo.Model (O.var c)) (π : N.X ⟶ M.X) (hπ : π ≫ M.p = N.p), Function.Surjective π ∧
    ∀ (Z : Scheme.{0}) (i : Z ⟶ N.X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod q) Γ(Z, ⊤)],
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod q) ((L.pull π hπ).B.pull i) 1 := by
  intro hX hP hH D O hO A T H hR B hB u s hu hs hdom hnef c M L k cf hI q _ hq
  obtain ⟨X', p', π, hπ, ρ, hρ, hproj, hsurj, κ, a, hκ, ha, heq⟩ := GlobalTheory.T.dominant_induced_model_reduction hP hH D O hO A T H hR B hB u s hu hs hdom c M L k cf hI q
  refine ⟨M, 𝟙 _, Category.id_comp _, Function.surjective_id, ?_⟩
  intro Z i _ _ _ hd
  have hL : ∀ (Z : Scheme.{0}) (i : Z ⟶ X') [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod q) Γ(Z, ⊤)],
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod q) ((L.pull π hπ).B.pull i) 1 := by
    intro Z i _ _ _ hd
    have e := heq Z i hd
    have h1 := GlobalTheory.T.proj_model_closed_fiber_integral hP hH D O hO A T H hR _ c X' p' hproj ρ hρ q Z i hd
    have h2 := GlobalTheory.T.nef_dominant_weight_positivity hX hP hH D O hO A T H hR B hB _ hdom hnef c X' p' hproj ρ hρ q hq Z i hd
    have h3 : (0 : ℝ) ≤ κ * (topSelfIntersection (ZMod q) ((L.pull π hπ).B.pull i) 1 : ℝ) := by
      rw [e]; exact add_nonneg (mul_nonneg ha (by exact_mod_cast h1)) h2
    exact_mod_cast nonneg_of_mul_nonneg_right h3 hκ
  have := descend _ M.X X' M.p p' M.ar.isProjOver hproj π hπ hsurj L q hL Z i hd
  have e : topSelfIntersection (ZMod q) ((L.pull (𝟙 M.X) (Category.id_comp _)).B.pull i) 1 = topSelfIntersection (ZMod q) (L.B.pull i) 1 := by
    rw [topSelf_def, topSelf_def]
    refine interNum_congr_cls (ZMod q) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB _) i)
      (fun _ => LB.isLB_pull L.isLB i) fun _ => ?_
    show pull i (pull (𝟙 M.X) (cls L.B L.isLB)) = pull i (cls L.B L.isLB)
    rw [pull_id]
  rw [e]; exact this

end GlobalTheory.NefDeRhamCore

end
