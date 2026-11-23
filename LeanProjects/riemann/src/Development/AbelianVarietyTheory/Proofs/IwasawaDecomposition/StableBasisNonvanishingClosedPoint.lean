import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IntFam

theorem exists_closed_mem_basicOpen_of_stableBasis : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (m : ℕ)
    (b : Fin m → SecAb D k α), GlobalTheory.IntFam.StableBasis D k α b → ∀ c : Fin m → R, (∃ i, c i ∉ maximalIdeal R) →
      ∃ (j : Fin 4 → D.P.L.ι) (y : D.P.A.left), D.P.A.hom y = closedPoint R ∧
        y ∈ D.P.A.left.basicOpen ((∑ i, c i • b i).f j) := by
  intro R _ _ _ D k α m b hb c hc
  classical
  let f : R →+* ResidueField R := residue R
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom f))
  let h : (T ⊗ D.P.A).left ⟶ D.P.A.left := (snd T D.P.A).left
  let π' : (T ⊗ D.P.A).left ⟶ Spec (CommRingCat.of (ResidueField R)) := (fst T D.P.A).left
  have hp : h ≫ D.P.A.hom = π' ≫ Spec.map (CommRingCat.ofHom f) :=
    (Over.w (snd T D.P.A)).trans (Over.w (fst T D.P.A)).symm
  let P := GlobalTheory.FieldBaseChange.pullOver (π := D.P.A.hom) (π' := π') D.P.L (DegPre.famε k) hp
    (φ := DegPre.famφB D α) (φ' := fun i => h ≫ DegPre.famφB D α i) (fun _ => rfl)
  have hbasis := hb (ResidueField R) f (fun i => P (b i)) (fun i j => rfl)
  have hsmooth : Smooth π' := by
    have := D.P.isAb.smooth
    show Smooth (pullback.fst _ _)
    infer_instance
  have hred : IsReduced (T ⊗ D.P.A).left := isReduced_of_smooth π'
  have hclosed : ∀ y₀ : (T ⊗ D.P.A).left, D.P.A.hom (h y₀) = closedPoint R := fun y₀ => by
    have e : D.P.A.hom (h y₀) = Spec.map (CommRingCat.ofHom f) (π' y₀) := by
      rw [← Scheme.Hom.comp_apply, hp, Scheme.Hom.comp_apply]
    rw [e, Subsingleton.elim (π' y₀) (closedPoint (ResidueField R))]
    exact IsLocalRing.comap_closedPoint (residue R)
  by_contra H
  push Not at H
  let s : SecAb D k α := ∑ i, c i • b i
  have hP : P s = ∑ i, f (c i) • P (b i) := by
    simp only [s, map_sum, map_smulₛₗ]
  have hzero : P s = 0 := by
    refine GlobalTheory.FieldBaseChange.SecOver.ext _ _ fun j => ?_
    show ((T ⊗ D.P.A).left.presheaf.map _).hom ((h.app _).hom (s.f j)) = 0
    rw [← AlgebraicGeometry.basicOpen_eq_bot_iff]
    erw [Scheme.basicOpen_res]
    refine eq_bot_iff.2 fun y₀ hy₀ => H j (h y₀) (hclosed y₀) ?_
    have hy := hy₀.2
    erw [← Scheme.preimage_basicOpen h (s.f j)] at hy
    exact hy
  have e := (hbasis SecOps.secZero).unique
    (y₁ := fun i => (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).inv.hom (f (c i))) (y₂ := fun _ => 0)
    (fun j => by
      have := congrArg (GlobalTheory.FieldBaseChange.chartLin π' _ j) (hzero.symm.trans hP)
      rw [map_zero, map_sum] at this
      refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [map_smul]
      rfl)
    (fun j => by simp only [map_zero, zero_mul, Finset.sum_const_zero]; rfl)
  obtain ⟨i, hi⟩ := hc
  have h0 : f (c i) = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).hom.hom (congrFun e i)
    simpa using this
  exact hi ((residue_eq_zero_iff _).1 h0)

end GlobalTheory.IntFam
