import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.BockOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.KummerTwistLemmas
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ReductionLemmas

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.TwSeq

open GlobalTheory.EtC

theorem pow_self {Q : ℕ} {A : Type} [CommRing A] (ζ : Prim Q A) : ζ.1 ^ Q = 1 := by
  obtain ⟨c, hc⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one Q ℤ
  have := congrArg (Polynomial.aeval ζ.1) hc
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero] at this
  exact this

def pw {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : Prim q A :=
  ⟨ζ.1 ^ (Q / q), isUnit_of_dvd_unit (Nat.cast_dvd_cast h) ζ.2.1, by
    obtain ⟨c, hc⟩ := CyclicComplexMaps.cyc_dvd Q q (NeZero.ne Q) h
    have := congrArg (Polynomial.aeval ζ.1) hc
    rw [Polynomial.aeval_comp, map_mul, ζ.2.2, zero_mul] at this
    simpa using this⟩

theorem pw_val {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : (pw h ζ).1 = ζ.1 ^ (Q / q) := rfl

theorem pw_map {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (ζ : Prim Q A) :
    (pw h ζ).map f = pw h (ζ.map f) := Subtype.ext (map_pow f _ _)

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  have h := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(U, ⊤))
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom
    (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ 1))) = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem redSheaf (hG : E.InGen) {Q q : ℕ} [NeZero Q] [NeZero q] (h : q ∣ Q) (i : ℤ) :
    ∃ π : tw Q i ⟶ (restr (ZMod.castHom h (ZMod q))).obj (tw q i), IsRedSh h i π ∧
      ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map π (twGen i ζ) =
        (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from twGen i (pw h ζ)) := by
  obtain ⟨π, hπ⟩ := KummerTwistLemmas.twLift i ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))
    (fun U ζ => (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from twGen i (pw h ζ)))
    (fun g ζ => by
      change Sec.res g (twGen i (pw h ζ)) = twGen i (pw h (ζ.map g.appTop.hom))
      rw [twGen_res, pw_map])
    (fun U ζ ξ a ha => by
      let a' : (ZMod q)ˣ := ZMod.unitsMap h a
      have hξ : (pw h ξ).1 = (pw h ζ).1 ^ (a' : ZMod q).val := by
        rw [pw_val, pw_val, ha, ← pow_mul, mul_comm, pow_mul]
        have h1 : ((pw h ζ).1) ^ q = 1 := pow_self (pw h ζ)
        rw [← pw_val h ζ, pow_eq_pow_mod _ h1, pow_eq_pow_mod ((a' : ZMod q).val) h1]
        have hv : (a' : ZMod q).val = (a : ZMod Q).val % q := by
          change (ZMod.castHom h (ZMod q) (a : ZMod Q)).val = _
          rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
        rw [hv, Nat.mod_mod]
      have := ((hG q i).2.2 U (pw h ζ) (pw h ξ) a' hξ)
      change twGen i (pw h ξ) = (ULift.up (ZMod.castHom h (ZMod q) ((a ^ i : (ZMod Q)ˣ) : ZMod Q)) : ULift.{1} (ZMod q)) • twGen i (pw h ζ)
      rw [this, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
      congr 1
      apply ULift.ext
      rw [ULift.down_natCast, ZMod.natCast_zmod_val]
      simp only [a', ZMod.unitsMap]
      rw [← map_zpow]
      rfl)
  refine ⟨π, fun U ζ ξ hξ => ?_, hπ⟩
  rw [hπ U ζ, show pw h ζ = ξ from Subtype.ext (show (pw h ζ).1 = ξ.1 from hξ.symm)]

end CrystallineSemistableComparison.TwSeq
