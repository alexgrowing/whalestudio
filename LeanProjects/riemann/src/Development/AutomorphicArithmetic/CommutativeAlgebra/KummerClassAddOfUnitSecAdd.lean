import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AutomorphicArithmetic.CommutativeAlgebra.KumSExact
import Development.AutomorphicArithmetic.CommutativeAlgebra.PicUnit
import Development.AutomorphicArithmetic.CommutativeAlgebra.EqOfUnitGlobalSectionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplittingStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

private theorem prim_pow (q : ℕ) {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

private theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun f => f.hom x) h

private theorem sec_res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U)
    (x y : Sec F U) : Sec.res g (x + y) = Sec.res g x + Sec.res g y :=
  map_add (F.obj.map g.op).hom x y

private theorem sec_map_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

private theorem sec_map_nsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ)
    (x : Sec F U) : Sec.map φ (c • x) = c • Sec.map φ x :=
  map_nsmul (φ.hom.app (op U)).hom c x

private theorem unitSec_pow_mul {W : Scheme.{0}} (u w : (Γ(W, ⊤))ˣ) (c : ℕ) :
    unitSec (u ^ c * w) = unitSec w + c • unitSec u := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ', mul_assoc, UpperTheory.PicD.unitSec_mul, ih, succ_nsmul]
    abel

private theorem kumT_pow_mul (q : ℕ) [NeZero q] (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (u w : (Γ(W, ⊤))ˣ)
    (hu : (u : Γ(W, ⊤)) = ζ.1) (c : ℕ) :
    kumT q W (u ^ c * w) = kumT q W w + c • resGen 1 ζ := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).2 W ζ (u ^ c * w) (u ^ (c + 1) * w)
      (by rw [pow_succ', mul_assoc, Units.val_mul, hu])
    rw [h, ih, succ_nsmul, add_assoc]

theorem UpperTheory.kummer_class_add_of_unitSec_add :
    ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}), IsUnit (q : Γ(V, ⊤)) → ∀ (v v' : (Γ(V, ⊤))ˣ) (a : Sec (tw q 1) V), unitSec v' = unitSec v + Sec.map (UpperTheory.Deg2.kap q) (show Sec (UpperTheory.Deg2.T q) V from a) → kumT q V v' = kumT q V v + Sec.map (resι _ (tw q 1)) a := by
  intro q _ V hq v v' a h
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) _ V).1 _ _ ?_
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q 1).1 V a
  refine ⟨S, hS, fun W g hg => ?_⟩
  show Sec.res g (kumT q V v') = Sec.res g (kumT q V v + Sec.map (resι _ (tw q 1)) a)
  have hK := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V g
  let b : Sec (UpperTheory.Deg2.T q) V := a
  let bW : Sec (UpperTheory.Deg2.T q) W := Sec.res g a
  have hb : Sec.res g (Sec.map (UpperTheory.Deg2.kap q) b) = Sec.map (UpperTheory.Deg2.kap q) bW :=
    (sec_map_res (UpperTheory.Deg2.kap q) g b).symm
  have h' : unitSec (Units.map g.appTop.hom.toMonoidHom v') = unitSec (Units.map g.appTop.hom.toMonoidHom v) +
      Sec.map (UpperTheory.Deg2.kap q) bW := by
    have h0 : unitSec v' = unitSec v + Sec.map (UpperTheory.Deg2.kap q) b := h
    have h1 := congrArg (Sec.res g) h0
    rw [sec_res_add, UpperTheory.PicD.unitSec_res, UpperTheory.PicD.unitSec_res, hb] at h1
    exact h1
  rw [sec_res_add, hK v hq, hK v' hq, ← sec_map_res]
  rcases hP W g hg with h0 | ⟨ζ, c, hc⟩
  · have h2 : Sec.map (UpperTheory.Deg2.kap q) bW = 0 := by
      have : bW = 0 := h0
      rw [this]
      exact sec_map_zero _
    rw [h0, sec_map_zero, add_zero]
    rw [h2, add_zero] at h'
    rw [UpperTheory.eq_of_unitGlobalSection_eq _ _ _ h']
  · have hun : IsUnit ζ.1 := isUnit_iff_exists_inv.2 ⟨ζ.1 ^ (q - 1), by
      rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos q)]
      exact prim_pow q ζ⟩
    obtain ⟨u, hu⟩ := hun
    have h2 : Sec.map (UpperTheory.Deg2.kap q) bW = c • unitSec u := by
      have : bW = c • (show Sec (UpperTheory.Deg2.T q) W from twGen 1 ζ) := hc
      rw [this, sec_map_nsmul, (UpperTheory.Deg2.kap_spec q).2.2.1 W ζ u hu]
    rw [h2, ← unitSec_pow_mul] at h'
    rw [UpperTheory.eq_of_unitGlobalSection_eq _ _ _ h', kumT_pow_mul q W ζ u _ hu c, hc, sec_map_nsmul]
    rfl
