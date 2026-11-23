import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOneOfPowOfClosedPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Published.AbVarRed

theorem torsionUnramified_of_hasGoodReduction : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω),
    IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], HasGoodReduction R K A →
    ∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m := by
  intro R K Ω _ _ _ _ _ _ _ _ V hV A _ _ hA m hm σ hσ x hx
  obtain ⟨G, _, hG, e, he⟩ := hA
  have : IsCommMonObj G := hG.comm
  have : Smooth G.hom := hG.smooth
  have : IsProper G.hom := hG.proper
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hP : IsGrpPullback A G (spMap (algebraMap R K)) (e.inv.left ≫ pullback.fst G.hom (spMap (algebraMap R K))) :=
    ((isGrpPullback_of_iso e.symm).comp (isGrpPullback_pullback G (spMap (algebraMap R K)))).congr
      (Category.id_comp _) rfl
  set φ := e.inv.left ≫ pullback.fst G.hom (spMap (algebraMap R K)) with hφ

  let T0 : Over (Sp R) := Over.mk ((ptOver K Ω).hom ≫ spMap (algebraMap R K))
  let Φ : (ptOver K Ω ⟶ A) → (T0 ⟶ G) := fun y => Over.homMk (y.left ≫ φ) (by
    change (y.left ≫ φ) ≫ G.hom = (ptOver K Ω).hom ≫ spMap (algebraMap R K)
    rw [Category.assoc, hP.1.w, ← Category.assoc, Over.w y])
  have Φmul : ∀ y y', Φ (y * y') = Φ y * Φ y' := fun y y' =>
    Over.OverMorphism.ext (hP.2 (ptOver K Ω) y y' (Φ y) (Φ y') rfl rfl).symm
  let ΦM : (ptOver K Ω ⟶ A) →* (T0 ⟶ G) := MonoidHom.mk' Φ Φmul
  have Φinj : Function.Injective Φ := fun y y' h =>
    Over.OverMorphism.ext (hP.1.hom_ext (congrArg Over.Hom.left h) ((Over.w y).trans (Over.w y').symm))

  have hmemV : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ V := fun r => by
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact this
  let rV : R →+* V := ((algebraMap K Ω).comp (algebraMap R K)).codRestrict V hmemV
  have hrV : (algebraMap V Ω).comp rV = (algebraMap K Ω).comp (algebraMap R K) := RingHom.ext fun _ => rfl

  obtain ⟨hσV, hσr⟩ := (mem_inertia_iff V σ).1 hσ
  have hmem : ∀ y ∈ V, σ y ∈ V := fun y hy => by
    have h := (ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := V) (x := y)).2 hy
    rw [hσV] at h
    exact h
  let σV : V →+* V := ((σ : Ω →+* Ω).comp (algebraMap V Ω)).codRestrict V fun y => hmem y y.2
  have F1 : (algebraMap V Ω).comp σV = (σ : Ω →+* Ω).comp (algebraMap V Ω) := RingHom.ext fun _ => rfl
  have F2 : σV.comp rV = rV := RingHom.ext fun r => Subtype.ext (σ.commutes (algebraMap R K r))
  have F3 : (residue V).comp σV = residue V := RingHom.ext fun y => by
    change residue V (σV y) = residue V y
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact hσr y y.2

  have hE : ValuativeCriterion.Existence G.hom := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) G.hom := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact h.1
  let S : ValuativeCommSq G.hom := ⟨V, Ω, (Φ x).left, spMap rV, ⟨by
    change (x.left ≫ φ) ≫ G.hom = spMap (algebraMap V Ω) ≫ spMap rV
    rw [Category.assoc, hP.1.w, ← Category.assoc, Over.w x, GlobalTheory.RedPts.spMap_comp, hrV]
    exact GlobalTheory.RedPts.spMap_comp _ _⟩⟩
  obtain ⟨l, hl1, hl2⟩ := (hE S).exists_lift.some
  change spMap (algebraMap V Ω) ≫ l = x.left ≫ φ at hl1
  change l ≫ G.hom = spMap rV at hl2
  let P : Over (Sp R) := Over.mk (spMap rV)
  let a : P ⟶ G := Over.homMk l hl2
  let b : P ⟶ G := Over.homMk (spMap σV ≫ l) (by
    change (spMap σV ≫ l) ≫ G.hom = spMap rV
    rw [Category.assoc, hl2, GlobalTheory.RedPts.spMap_comp, F2])
  let u : T0 ⟶ P := Over.homMk (spMap (algebraMap V Ω)) (by
    change spMap (algebraMap V Ω) ≫ spMap rV = (ptOver K Ω).hom ≫ spMap (algebraMap R K)
    rw [GlobalTheory.RedPts.spMap_comp, hrV]
    exact (GlobalTheory.RedPts.spMap_comp _ _).symm)
  have hua : u ≫ a = Φ x := Over.OverMorphism.ext hl1
  have hub : u ≫ b = Φ (galPts A σ x) := Over.OverMorphism.ext (by
    change spMap (algebraMap V Ω) ≫ spMap σV ≫ l = (galPts A σ x).left ≫ φ
    rw [galPts_left, ← Category.assoc, GlobalTheory.RedPts.spMap_comp, F1, ← GlobalTheory.RedPts.spMap_comp, Category.assoc, hl1,
      Category.assoc])

  let Z : Over (Sp R) := Over.mk (spMap ((residue V).comp rV))
  let j : Z ⟶ P := Over.homMk (spMap (residue V)) (GlobalTheory.RedPts.spMap_comp _ _)
  have hjb : j ≫ b = j ≫ a := Over.OverMorphism.ext (by
    change spMap (residue V) ≫ spMap σV ≫ l = spMap (residue V) ≫ l
    rw [← Category.assoc, GlobalTheory.RedPts.spMap_comp, F3])
  have hdom : IsDominant (spMap (algebraMap V Ω)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap V Ω) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V Ω)]; exact bot_le)⟩
  have hu : Function.Injective (GlobalTheory.RedPts.precomp G u) := fun c d h => Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp V) G.hom ((Over.w c).trans (Over.w d).symm)
      (spMap (algebraMap V Ω)) (congrArg Over.Hom.left h))
  have hz : (b * a⁻¹) ^ m = 1 := by
    apply hu
    rw [map_pow, map_one, map_mul, map_inv]
    change ((u ≫ b) * (u ≫ a)⁻¹) ^ m = 1
    rw [hua, hub]
    change (ΦM (galPts A σ x) * (ΦM x)⁻¹) ^ m = 1
    rw [← map_inv, ← map_mul, ← map_pow, mul_pow, inv_pow, ← map_pow, hx, map_one, inv_one, _root_.mul_one, map_one]
  have hjz : j ≫ (b * a⁻¹) = 1 := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hjb, mul_inv_cancel]
  have hn : IsUnit (m : V) := by
    have h1 : IsUnit (m : R) := by
      by_contra h
      apply hm
      rw [← map_natCast (residue R), residue_eq_zero_iff]
      exact h
    simpa using h1.map rV
  have h1 := GlobalTheory.RedPts.eq_one_of_pow_of_closedPoint G (spMap rV) hn (b * a⁻¹) hz j
    ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue V)⟩ hjz
  have hba : b = a := mul_inv_eq_one.1 h1
  apply Φinj
  rw [← hub, ← hua, hba]

end GlobalTheory.Published.AbVarRed
