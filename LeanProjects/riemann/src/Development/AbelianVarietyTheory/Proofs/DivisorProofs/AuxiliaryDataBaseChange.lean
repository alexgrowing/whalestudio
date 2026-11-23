import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BoundaryRSmooth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)}
  [SmoothOfRelativeDimension Dw.dim (genStr Z)]

theorem r_cInfAt (x : OddPrimesWithRootsOfUnity Z) (σ' : c.F →+* ℂ) {yc : CxPts (genStr Z) σ'} (h : ¬ LiesIn yc (genBd Z)) :
    CInfAt (x.r σ') yc := by
  have hl : ∀ i, CInfAt (fun z => Real.log (x.nrm σ' i z ^ 2)) yc := fun i =>
    (cInfAt_iff_smoothOn (manifold Z σ') (isOpen_not_liesIn (x.cpt i))).2 ((x.nrm_div σ' i).smoothOn_log) yc
      (fun h' => h ((x.liesIn_genBd_iff yc).2 ⟨i, h'⟩))
  have hs : ∀ s : Finset (Fin x.m), CInfAt (fun z => ∑ i ∈ s, Real.log (x.nrm σ' i z ^ 2)) yc := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simpa using cInfAt_const 0 yc
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hl a).add ih
  refine ((cInfAt_const (Real.exp 1) yc).add (hs Finset.univ).neg).congr ?_
  filter_upwards [(isOpen_not_liesIn (genBd Z)).mem_nhds h] with z hz
  rw [OddPrimesWithRootsOfUnity.r, ← Finset.prod_pow, Real.log_prod fun i _ => pow_ne_zero 2 (x.nrm_pos hz i).ne', sub_eq_add_neg]

end GlobalTheory.BoundaryRSmooth

open GlobalTheory.BoundaryRSmooth in

theorem GlobalTheory.BoundaryRSmooth.cInfAt_r_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) (T : Scheme.{0}) (b : T ⟶ Z.X) (q : T ⟶ Sp (𝓞 c.F)), b ≫ Z.s = q → (∀ w : T, b w ∈ abLocus Z.t.G) → ∀ σ' : c.F →+* ℂ, ∃ ρ : CxPts q (σ'.comp (algebraMap (𝓞 c.F) c.F)) → ℝ, ∀ y, CInfAt ρ y ∧ ∃ yc : CxPts (genStr Z) σ', y.1 ≫ b = yc.1 ≫ genι Z ∧ ¬ LiesIn yc (genBd Z) ∧ ρ y = x.r σ' yc := by
  intro E _ _ _ H Dw l Xo c Z _ x T b q hb hab σ'
  have P : IsPullback (genι Z) (genStr Z) Z.s (spMap (algebraMap (𝓞 c.F) c.F)) := IsPullback.of_hasPullback _ _
  have hsp : spMap (σ'.comp (algebraMap (𝓞 c.F) c.F)) = spMap σ' ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hm0 (w : CxPts (genStr Z) σ') : (w.1 ≫ genι Z) ≫ Z.s = spMap (σ'.comp (algebraMap (𝓞 c.F) c.F)) := by
    rw [Category.assoc, P.w, ← Category.assoc, w.2, hsp]
  let m : CxPts (genStr Z) σ' → CxPts Z.s (σ'.comp (algebraMap (𝓞 c.F) c.F)) := fun w => ⟨w.1 ≫ genι Z, hm0 w⟩
  let s : CxPts Z.s (σ'.comp (algebraMap (𝓞 c.F) c.F)) → CxPts (genStr Z) σ' := fun y =>
    ⟨P.lift y.1 (spMap σ') (y.2.trans hsp), P.lift_snd _ _ _⟩
  have hms (y) : m (s y) = y := Subtype.ext (P.lift_fst _ _ _)
  have hsm (w) : s (m w) = w := Subtype.ext (P.hom_ext (P.lift_fst _ _ _) ((P.lift_snd _ _ _).trans w.2.symm))
  let f : CxPts Z.s (σ'.comp (algebraMap (𝓞 c.F) c.F)) → ℝ := fun y => x.r σ' (s y)
  refine ⟨fun y => f (Points.PtsOver.map b hb _ y), fun y => ?_⟩
  set y0 := Points.PtsOver.map b hb (spMap (σ'.comp (algebraMap (𝓞 c.F) c.F))) y with hy0
  have e0 : (s y0).1 ≫ genι Z = y.1 ≫ b := congrArg Subtype.val (hms y0)
  have hnb : ¬ LiesIn (s y0) (genBd Z) := by
    intro hL
    have h1 := mem_genBd_iff.1 hL
    apply h1
    have h2 : (genι Z) ((s y0).1 (IsLocalRing.closedPoint ℂ)) = b (y.1 (IsLocalRing.closedPoint ℂ)) := by
      have := congrArg (fun φ : Sp ℂ ⟶ Z.X => φ (IsLocalRing.closedPoint ℂ)) e0
      exact this
    rw [h2]
    exact hab _
  refine ⟨CInfAt.pull b hb ?_, s y0, e0.symm, hnb, rfl⟩
  have hz : CInfAt (fun w => f (m w)) (s y0) :=
    (r_cInfAt x σ' hnb).congr (.of_forall fun w => by simp only [f, hsm])
  have := GlobalTheory.Mean4O.OnModelCInf.baseChange_cInfAt c.F Z.X (gen Z) Z.s (genStr Z) (genι Z) P σ'
    (σ'.comp (algebraMap (𝓞 c.F) c.F)) m (fun _ => rfl) f (s y0) hz
  rwa [hms] at this
