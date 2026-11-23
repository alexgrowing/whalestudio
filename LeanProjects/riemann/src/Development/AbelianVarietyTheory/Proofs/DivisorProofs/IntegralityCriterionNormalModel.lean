import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointPlaceCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralMultipleExtension
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase.IntCritPf

open IsDedekindDomain TopologicalSpace GlobalTheory.Cartier GlobalTheory.CxPts

section

variable {F : Type} [Field F] [NumberField F] {X W : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp (𝓞 F)} {s : W ⟶ Sp F}
  {jB : W ⟶ X} {d : ℕ}

open GlobalTheory.TrueGeo.HorizPt in

theorem exists_horizPt (hq : IsArithVar q d) (pb : IsPullback jB s q (spMap (algebraMap (𝓞 F) F)))
    (U₀ : X.Opens) (z : X) (g : Γ(X, U₀)) (hz : z ∈ U₀) (hg : g ≠ 0) (hzg : z ∉ X.basicOpen g) :
    ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : Sp (AlgebraicClosure F) ⟶ W) (yt : Sp e.O ⟶ X),
      y ≫ s = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = y ≫ jB ∧
      ⊤ ≤ yt ⁻¹ᵁ U₀ ∧ yt (IsLocalRing.closedPoint e.O) ∉ X.basicOpen g ∧ below (y ≫ jB) ∈ X.basicOpen g := by
  have := hq.flat
  have : IsProper q := by
    obtain ⟨n, c, hc, h⟩ := hq.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle : U ≤ U₀ := hUW
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : CharZero Γ(X, U) := charZero (q ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(X, U) := (GlobalTheory.TrueGeo.HorizPt.strHom q U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(X, U) :=
    RingHom.FiniteType.comp (q.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  set g' : Γ(X, U) := X.presheaf.map (homOfLE hle).op g with hg'
  have hg0 : g' ≠ 0 := fun h => hg (map_injective_of_isIntegral X (homOfLE hle) (by rw [← hg', h, map_zero]))
  have hb : ∀ x : PrimeSpectrum Γ(X, U), hU.fromSpec x ∈ X.basicOpen g ↔ g' ∉ x.asIdeal := by
    intro x
    have h₁ : hU.fromSpec x ∈ U := by
      have := hU.range_fromSpec
      exact (Set.ext_iff.1 this _).1 ⟨x, rfl⟩
    have h₂ : hU.fromSpec x ∈ X.basicOpen g' ↔ g' ∉ x.asIdeal := by
      change x ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g' ↔ _
      rw [hU.fromSpec_preimage_basicOpen]
      rfl
    rw [← h₂, hg', Scheme.basicOpen_res]
    exact ⟨fun h => ⟨h₁, h⟩, fun h => h.2⟩
  have hp : g' ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    by_contra h
    have := (hb _).2 h
    rw [hU.fromSpec_primeIdealOf] at this
    exact hzg this
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨z, hzU⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(X, U) 𝔪 h𝔪 g' hg0
  let yt : Sp e.O ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ q =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := pb.lift_fst _ _ hw
  refine ⟨v, e, pb.lift _ _ hw, yt, pb.lift_snd _ _ hw, hy.symm, ?_, ?_, ?_⟩
  · intro x _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · intro h
    refine (hb (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O))).1 h ?_
    have := hle' hp
    rw [← h₂] at this
    exact this
  · change (pb.lift _ _ hw ≫ jB) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ _
    rw [hy]
    refine (hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype
      (IsLocalRing.closedPoint (AlgebraicClosure F))))).2 fun h => h₃ ?_
    have h' : ((φ g' : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h'
    exact Subtype.ext h'

open GlobalTheory.TrueGeo.RegCrit in

theorem regAt_of_integral_values (hq : IsArithVar q d) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X)
    (pb : IsPullback jB s q (spMap (algebraMap (𝓞 F) F))) (U : X.Opens) (f : X.functionField)
    (hf : ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (z : Sp (AlgebraicClosure F) ⟶ W) (yt : Sp e.O ⟶ X),
      z ≫ s = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ jB → ⊤ ≤ yt ⁻¹ᵁ U →
        e.w (valAt (z ≫ jB) f) ≤ 1) :
    ∀ x ∈ U, RegAt x f := by
  intro x hx
  have : IsProper q := by
    obtain ⟨n, c, hc, h⟩ := hq.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  by_contra hreg
  obtain ⟨z, hz, hzero⟩ := GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal X hn x f hreg
  have hf0 : f ≠ 0 := fun h => hreg (h ▸ regAt_zero x)
  have hzU : z ∈ U := hz.mem_open U.isOpen hx
  obtain ⟨W₀, hzW, g₀, hg₀⟩ := hzero.regAt.exists_fnOf
  have hzW' : z ∈ W₀ ⊓ U := ⟨hzW, hzU⟩
  obtain ⟨g, hg⟩ : ∃ g : Γ(X, W₀ ⊓ U), ∀ h, fnOf _ h g = f⁻¹ :=
    ⟨resG X inf_le_left g₀, fun h => (fnOf_resG _ h _).trans hg₀⟩
  have hg0 : g ≠ 0 := fun h => inv_ne_zero hf0 (by rw [← hg (gen_mem hzW'), h, map_zero])
  have hzg : z ∉ X.basicOpen g := fun h =>
    (zeroAt_iff.1 hzero).2 (hg (gen_mem hzW') ▸ (unitAt_fnOf_iff hzW' _ g).2 h)
  obtain ⟨v, e, y, yt, hy, hc, hW, hn', hu⟩ := exists_horizPt hq pb _ z g hzW' hg0 hzg
  have hle := hf v e y yt hy hc fun p hp => (hW hp).2
  have hu' : below (y ≫ jB) ∈ X.basicOpen g := hu
  have hb : below (y ≫ jB) ∈ W₀ ⊓ U := X.basicOpen_le g hu'
  have ht : ⊤ ≤ (y ≫ jB) ⁻¹ᵁ (W₀ ⊓ U) := fun p _ => by
    change (y ≫ jB) p ∈ W₀ ⊓ U
    rw [← hc]
    exact hW (x := spMap e.O.subtype p) trivial
  have hunit : UnitAt (below (y ≫ jB)) f⁻¹ := hg (gen_mem hb) ▸ (unitAt_fnOf_iff hb _ g).2 hu'
  have hfu : UnitAt (below (y ≫ jB)) f := inv_inv f ▸ hunit.inv
  have hmul := OfModel.valAt_mul (y ≫ jB) hfu.regAt hunit.regAt
  have hone : valAt (y ≫ jB) (1 : X.functionField) = 1 := by
    have := OfModel.valAt_algebraMap (y ≫ jB) 1
    rwa [map_one, map_one] at this
  have hev := OfModel.eval_pull e.O.subtype (𝟙 X) (y ≫ jB) yt (hc.trans (Category.comp_id _).symm)
    (U := W₀ ⊓ U) (W := W₀ ⊓ U) le_rfl ht hW g
  have hid : ((𝟙 X : X ⟶ X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl).hom g = g := by
    have : (𝟙 X : X ⟶ X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl = 𝟙 _ :=
      (Category.id_comp _).trans (X.presheaf.map_id _)
    rw [this]
    rfl
  rw [hid] at hev
  rw [mul_inv_cancel₀ hf0, hone, ← hg (gen_mem hb), OfModel.valAt_fnOf _ hb ht, hev] at hmul
  refine hn' ((isUnit_eval_iff yt hW g).1 (isUnit_of_one_le e _ ?_))
  have h₁ := congrArg e.w hmul
  rw [map_one, map_mul] at h₁
  exact h₁.le.trans (mul_le_of_le_one_left (e.w.nonneg _) hle)

theorem evalPt_app (z : Sp (AlgebraicClosure F) ⟶ W) (V : X.Opens) (hx : ⊤ ≤ z ⁻¹ᵁ (jB ⁻¹ᵁ V))
    (hx' : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ V) (a : Γ(X, V)) :
    TangentOrigin.evalPt (z ≫ jB) V hx' a = TangentOrigin.evalPt z (jB ⁻¹ᵁ V) hx (jB.app V a) := by
  unfold TangentOrigin.evalPt
  rw [Scheme.Hom.comp_appLE]
  rfl

end

end GlobalTheory.ArLieBase.IntCritPf

namespace GlobalTheory.ArLieBase.IntCritPf

open IsDedekindDomain TopologicalSpace GlobalTheory.Cartier GlobalTheory.CxPts

theorem intCrit : ∀ (F : Type) [Field F] [NumberField F] (X W : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (s : W ⟶ Sp F)
    (jB : W ⟶ X) (d : ℕ), IsArithVar q d → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    IsPullback jB s q (spMap (algebraMap (𝓞 F) F)) → IntCrit s jB := by
  intro F _ _ X W q s jB d hq hn pb V hV f hf
  haveI := hq.isIntegral
  by_cases hg : genericPoint X ∈ V
  swap
  · obtain rfl : V = ⊥ := eq_bot_iff.2 fun x hx => (hg (gen_mem hx)).elim
    have e : jB ⁻¹ᵁ (⊥ : X.Opens) = ⊥ := by
      ext x
      simp
    haveI : Subsingleton Γ(W, jB ⁻¹ᵁ (⊥ : X.Opens)) := by
      rw [e]
      infer_instance
    exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨N, hN, a, ha⟩ := GlobalTheory.GenericFibreInt.integ pb hV f
  have hunit : IsUnit (N : Γ(W, jB ⁻¹ᵁ V)) := by
    have : IsUnit (N : F) := (Nat.cast_ne_zero.2 hN).isUnit
    simpa using this.map (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX s (jB ⁻¹ᵁ V))
  have := hq.flat
  have : Nonempty V := ⟨⟨_, hg⟩⟩
  have : CharZero Γ(X, V) := GlobalTheory.TrueGeo.HorizPt.charZero (q ≫ spMap (Int.castRingHom (𝓞 F))) hV
  have hN0 : (N : X.functionField) ≠ 0 := by
    rw [← map_natCast (fnOf V hg)]
    exact fun h => Nat.cast_ne_zero.2 hN (fnOf_injective V hg (h.trans (map_zero _).symm))
  have hNK : (N : AlgebraicClosure F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (AlgebraicClosure F))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hN)
  set f' : X.functionField := fnOf V hg a * (N : X.functionField)⁻¹ with hf'
  have hbo : jB ⁻¹ᵁ X.basicOpen (N : Γ(X, V)) = jB ⁻¹ᵁ V := by
    rw [Scheme.preimage_basicOpen, map_natCast, Scheme.basicOpen_of_isUnit W hunit]
  have hreg : ∀ x ∈ V, RegAt x f' := by
    refine regAt_of_integral_values hq hn pb V f' fun v e z yt hz hc hyt => ?_
    have hx' : ⊤ ≤ (z ≫ jB) ⁻¹ᵁ V := fun p _ => by
      change (z ≫ jB) p ∈ V
      rw [← hc]
      exact hyt (x := spMap e.O.subtype p) trivial
    have hx : ⊤ ≤ z ⁻¹ᵁ (jB ⁻¹ᵁ V) := fun p hp => hx' hp
    have hb : below (z ≫ jB) ∈ V := hx' trivial
    have hbN : below (z ≫ jB) ∈ X.basicOpen (N : Γ(X, V)) := by
      have : below z ∈ jB ⁻¹ᵁ X.basicOpen (N : Γ(X, V)) := hbo ▸ hx trivial
      exact this
    have hNu : UnitAt (below (z ≫ jB)) (N : X.functionField) := by
      rw [← map_natCast (fnOf V hg)]
      exact (unitAt_fnOf_iff hb hg _).2 hbN
    have hreg' : RegAt (below (z ≫ jB)) f' := (regAt_fnOf hb hg a).mul hNu.inv.regAt
    have hmul := OfModel.valAt_mul (z ≫ jB) hreg' hNu.regAt
    rw [hf', mul_assoc, inv_mul_cancel₀ hN0, mul_one, OfModel.valAt_fnOf _ hb hx'] at hmul
    have hvN : valAt (z ≫ jB) (N : X.functionField) = N := by
      rw [← map_natCast (fnOf V hg), OfModel.valAt_fnOf _ hb hx', map_natCast]
    change TangentOrigin.evalPt (z ≫ jB) V hx' a = _ at hmul
    rw [hvN, evalPt_app z V hx hx' a, ← ha, map_mul, map_natCast, mul_comm] at hmul
    have hval : valAt (z ≫ jB) f' = TangentOrigin.evalPt z (jB ⁻¹ᵁ V) hx f :=
      (mul_right_cancel₀ hNK hmul).symm
    rw [hval]
    exact (e.mem_O _).1 (hf v e z yt hz hc hyt hx)
  obtain ⟨f₀, hf₀⟩ := exists_fnOf_eq hg hreg
  have h1 : (N : Γ(X, V)) * f₀ = a := by
    apply fnOf_injective V hg
    rw [map_mul, map_natCast, hf₀, hf', mul_comm, mul_assoc, inv_mul_cancel₀ hN0, mul_one]
  refine ⟨f₀, hunit.mul_left_cancel ?_⟩
  rw [ha, ← h1, map_mul, map_natCast]

end GlobalTheory.ArLieBase.IntCritPf
