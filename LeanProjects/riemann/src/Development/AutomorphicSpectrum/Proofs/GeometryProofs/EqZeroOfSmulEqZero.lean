import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyGen

variable {R : Type} [CommRing R] {Y : Scheme.{0}}

def SecMod (_p : Y ⟶ Sp R) (M : LB Y) : Type := M.Sec

variable {p : Y ⟶ Sp R} {M : LB Y}

theorem SecMod.ext {s t : SecMod p M} (h : ∀ i, LB.Sec.f s i = LB.Sec.f t i) : s = t := by
  obtain ⟨f, hf⟩ := s
  obtain ⟨g, hg⟩ := t
  obtain rfl : f = g := funext h
  rfl

def constHom (p : Y ⟶ Sp R) (U : Y.Opens) : R →+* Γ(Y, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem constHom_apply (U : Y.Opens) (a : R) : constHom p U a = constFn p U a := rfl

theorem res_constFn {U V : Y.Opens} (h : V ≤ U) (a : R) :
    (Y.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a := by
  have e : p.appLE ⊤ U (fun _ _ => trivial) ≫ Y.presheaf.map (homOfLE h).op = p.appLE ⊤ V (fun _ _ => trivial) :=
    Scheme.Hom.appLE_map p _ _
  exact congrArg (fun φ => CommRingCat.Hom.hom φ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) e

instance : Add (SecMod p M) where
  add s t := ⟨fun i => LB.Sec.f s i + LB.Sec.f t i, fun i j => by
    rw [map_add, map_add, LB.Sec.compat s, LB.Sec.compat t, mul_add]⟩

instance : Zero (SecMod p M) where
  zero := ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, MulZeroClass.mul_zero]⟩

instance : Neg (SecMod p M) where
  neg s := ⟨fun i => - LB.Sec.f s i, fun i j => by rw [map_neg, map_neg, LB.Sec.compat s, mul_neg]⟩

instance : AddCommGroup (SecMod p M) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := SecMod.ext fun i => _root_.add_assoc _ _ _
  zero_add a := SecMod.ext fun i => zero_add _
  add_zero a := SecMod.ext fun i => add_zero _
  neg_add_cancel a := SecMod.ext fun i => neg_add_cancel _
  add_comm a b := SecMod.ext fun i => add_comm _ _

theorem add_f (s t : SecMod p M) (i : M.ι) : LB.Sec.f (s + t : SecMod p M) i = LB.Sec.f s i + LB.Sec.f t i := rfl

theorem zero_f (i : M.ι) : LB.Sec.f (0 : SecMod p M) i = 0 := rfl

instance : Module R (SecMod p M) where
  smul a s := ⟨fun i => constFn p _ a * LB.Sec.f s i, fun i j => by
    rw [map_mul, map_mul, res_constFn, res_constFn, LB.Sec.compat s, mul_left_comm]⟩
  one_smul s := SecMod.ext fun i => by
    show constFn p _ 1 * _ = _
    rw [← constHom_apply, map_one, _root_.one_mul]
  mul_smul a b s := SecMod.ext fun i => by
    show constFn p _ (a * b) * _ = constFn p _ a * (constFn p _ b * _)
    rw [← constHom_apply, ← constHom_apply, ← constHom_apply, map_mul, _root_.mul_assoc]
  smul_zero a := SecMod.ext fun i => MulZeroClass.mul_zero _
  smul_add a s t := SecMod.ext fun i => mul_add _ _ _
  add_smul a b s := SecMod.ext fun i => by
    show constFn p _ (a + b) * _ = constFn p _ a * _ + constFn p _ b * _
    rw [← constHom_apply, ← constHom_apply, ← constHom_apply, map_add, add_mul]
  zero_smul s := SecMod.ext fun i => by
    show constFn p _ 0 * _ = 0
    rw [← constHom_apply, map_zero, MulZeroClass.zero_mul]

theorem smul_f (a : R) (s : SecMod p M) (i : M.ι) :
    LB.Sec.f (a • s : SecMod p M) i = constFn p _ a * LB.Sec.f s i := rfl

theorem eq_zero_of_smul_eq_zero [IsDomain R] [Flat p] {a : R} (ha : a ≠ 0) {s : SecMod p M}
    (h : a • s = 0) : s = 0 := by
  refine SecMod.ext fun i => fn_ext fun y hy => cst_regular p y ha ?_
  have e := congrArg (gs (𝟙 Y) y (M.U i)) (congrArg (fun s : SecMod p M => LB.Sec.f s i) h)
  simp only [smul_f, zero_f] at e
  rw [gs_mul _ y _ hy, gs_constFn p _ _ y hy, Category.id_comp] at e
  have z : gs (𝟙 Y) y (M.U i) (0 : Γ(Y, M.U i)) = 0 := by
    rw [gs_eq _ y _ hy]
    exact map_zero (CommRingCat.Hom.hom (Y.presheaf.germ (𝟙 Y ⁻¹ᵁ M.U i) y hy))
  show cst p y a * _ = cst p y a * gs (𝟙 Y) y (M.U i) (0 : Γ(Y, M.U i))
  rw [z, MulZeroClass.mul_zero]
  exact e.trans z

end GlobalTheory.CompanionTheory.Ar.Sl.KeyGen
