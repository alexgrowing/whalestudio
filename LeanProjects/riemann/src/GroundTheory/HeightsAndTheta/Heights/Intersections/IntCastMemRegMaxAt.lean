import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreMore
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingLocal
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTer
import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingInj
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreFurther
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisAlt
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem regRing_mem_locRing {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    ((x : funField P) : FractionRing (MRing ι ⧸ P)) ∈ locRing P W :=
  x.2 W hW hPW

def regToLoc (P W : Ideal (MRing ι)) (hW : IsClosedPt W) (hPW : P ≤ W) : regRing P →+* locRing P W where
  toFun x := ⟨((x : funField P) : FractionRing (MRing ι ⧸ P)), regRing_mem_locRing hW hPW x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

theorem regToLoc_apply {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    regToLoc P W hW hPW x = ⟨((x : funField P) : FractionRing (MRing ι ⧸ P)), regRing_mem_locRing hW hPW x⟩ :=
  rfl

theorem regToLoc_coe {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    ((regToLoc P W hW hPW x : locRing P W) : FractionRing (MRing ι ⧸ P)) =
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) :=
  (congrArg Subtype.val (regToLoc_apply hW hPW x)).trans (Subtype.coe_mk _ _)

def regMaxAt (P W : Ideal (MRing ι)) (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) :
    Ideal (regRing P) :=
  (IsLocalRing.maximalIdeal (locRing P W)).comap (regToLoc P W hW hPW)

theorem not_mem_regMaxAt_iff {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W)
    (hloc : IsLocalRing (locRing P W)) (x : regRing P) :
    x ∉ regMaxAt P W hW hPW hloc ↔
      ∃ z ∈ locRing P W, ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1 := by
  have hc : ∀ b : locRing P W, ((regToLoc P W hW hPW x * b : locRing P W) : FractionRing (MRing ι ⧸ P)) =
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) * b := fun b => by
    rw [Subring.coe_mul, regToLoc_coe]
  simp only [regMaxAt, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    refine ⟨b.1, b.2, ?_⟩
    rw [← hc b, hb, Subring.coe_one]
  · rintro ⟨z, hz, h⟩
    refine IsUnit.of_mul_eq_one (a := regToLoc P W hW hPW x) ⟨z, hz⟩ (Subtype.ext ?_)
    rw [hc, Subring.coe_one]
    exact h

theorem intCast_mem_regMaxAt (hL : LocRingLocal.Statement) {P W : Ideal (MRing ι)} (hPp : P.IsPrime)
    (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) {n : ℤ} (hn : C n ∈ W) :
    (n : regRing P) ∈ regMaxAt P W hW hPW hloc := by
  by_contra h
  obtain ⟨z, hz, h⟩ := (not_mem_regMaxAt_iff hW hPW hloc _).1 h
  have h1W : (1 : MRing ι) ∉ W := fun h => hW.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hu := ((hL K ι P W hPp hW.1.1 hPW).2 (n : locRing P W) (C n) 1 0 (RegularityDenominator.isMultiHomog_C n)
    AvoidRing.isMultiHomog_one h1W (by simp [eq_intCast C n])).1
  refine hu (IsUnit.of_mul_eq_one (a := (n : locRing P W)) ⟨z, hz⟩ (Subtype.ext ?_)) hn
  simpa using h

theorem regMaxAt_isMaximal (hO : RegularityOrder.Statement) (hL : LocRingLocal.Statement) {P W : Ideal (MRing ι)}
    (hP : IsArithVar P 1) (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) :
    (regMaxAt P W hW hPW hloc).IsMaximal := by
  have : (regMaxAt P W hW hPW hloc).IsPrime := by unfold regMaxAt; infer_instance
  have : Module.Finite ℤ (regRing P) := (hO K ι P hP).2.1
  have hvert : W.comap (C : ℤ →+* MRing ι) ≠ ⊥ := fun hh =>
    arithVarZero K ι W ⟨hP.1, hW.1, hh, by rw [zero_add]; exact hW.2⟩
  obtain ⟨n, hnW, hn0⟩ := (Submodule.ne_bot_iff _).mp hvert
  have hn : n ∈ (regMaxAt P W hW hPW hloc).comap (algebraMap ℤ (regRing P)) := by
    rw [Ideal.mem_comap, algebraMap_int_eq, eq_intCast]
    exact intCast_mem_regMaxAt hL hP.2.1.1 hW hPW hloc hnW
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ) _
    (_root_.IsPrime.to_maximal_ideal fun h => hn0 (by rw [h] at hn; exact hn))

theorem RegularityMaximalSpectrum.proof (hO : RegularityOrder.Statement)
    (hZ : RegularityLocalize.Statement) (hI : LocRingInj.Statement) (hS : RegularityMaximalSurjective.Statement) :
    RegularityMaximalSpectrum.Statement := by
  classical
  have hL : LocRingLocal.Statement := LocRingLocal.proof LocRingFrac.proof
  intro K _ ι _ P hP
  have hPp : P.IsPrime := hP.2.1.1
  have hloc : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, IsLocalRing (locRing P W.1) :=
    fun W => (hL K ι P W.1 hPp W.2.1.1.1 W.2.2).1
  let m : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} → Ideal (regRing P) := fun W =>
    regMaxAt P W.1 W.2.1 W.2.2 (hloc W)
  have hm : ∀ W (x : regRing P), x ∉ m W ↔
      ∃ z ∈ locRing P W.1, ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1 :=
    fun W => not_mem_regMaxAt_iff W.2.1 W.2.2 (hloc W)

  have hsub : ∀ W W', m W = m W' → locRing P W.1 ≤ locRing P W'.1 := by
    intro W W' hWW' y hy
    obtain ⟨s, x, hsu, hys⟩ := hZ K ι P W.1 y hP W.2.1 W.2.2 hy
    obtain ⟨z, hz, hsz⟩ := (hm W' s).1 (hWW' ▸ (hm W s).2 hsu)
    rw [show y = ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z by rw [← hys, mul_assoc, hsz, mul_one]]
    exact mul_mem (regRing_mem_locRing W'.2.1 W'.2.2 x) hz
  let f : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} → MaximalSpectrum (regRing P) := fun W =>
    ⟨m W, regMaxAt_isMaximal hO hL hP W.2.1 W.2.2 (hloc W)⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun W W' h => Subtype.ext (hI K ι P W.1 W'.1 hPp W.2.1.1 W'.2.1.1 W.2.2 W'.2.2
      (le_antisymm (hsub W W' (congrArg MaximalSpectrum.asIdeal h))
        (hsub W' W (congrArg MaximalSpectrum.asIdeal h).symm))), ?_⟩
    rintro ⟨M, hM⟩
    obtain ⟨W, hWc, hPW, hW⟩ := hS K ι P hP M hM
    refine ⟨⟨W, hWc, hPW⟩, ?_⟩
    have hle : M ≤ m ⟨W, hWc, hPW⟩ := fun x hx => by
      by_contra hc
      obtain ⟨z, hz, h⟩ := (hm _ x).1 hc
      exact hW x hx z hz h
    exact MaximalSpectrum.ext (hM.eq_of_le (regMaxAt_isMaximal hO hL hP hWc hPW _).ne_top hle).symm
  refine ⟨Equiv.ofBijective f hbij, fun W y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨s, x, hsu, hys⟩ := hZ K ι P W.1 y hP W.2.1 W.2.2 hy
    exact ⟨x, s, (hm W s).2 hsu, hys⟩
  · rintro ⟨x, s, hs, hys⟩
    obtain ⟨z, hz, hsz⟩ := (hm W s).1 hs
    rw [show y = ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z by rw [← hys, mul_assoc, hsz, mul_one]]
    exact mul_mem (regRing_mem_locRing W.2.1 W.2.2 x) hz

end

end GroundTheory.Heights₂.Heights.Inter
