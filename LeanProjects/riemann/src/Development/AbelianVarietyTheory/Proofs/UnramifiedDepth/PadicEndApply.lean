import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PadicOrderAction

def padicEnd (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (hM : ∀ x : M, p • x = 0) :
    ℤ_[p] →+* AddMonoid.End M where
  toFun c := nsmulAddMonoidHom (PadicInt.toZMod c).val
  map_one' := by
    ext x
    change (PadicInt.toZMod (1 : ℤ_[p])).val • x = x
    rw [map_one, ZMod.val_one, one_nsmul]
  map_mul' a b := by
    ext x
    change (PadicInt.toZMod (a * b)).val • x = (PadicInt.toZMod a).val • (PadicInt.toZMod b).val • x
    rw [map_mul, ZMod.val_mul, ← nsmul_eq_mod_nsmul _ (hM x), mul_nsmul']
  map_zero' := by
    ext x
    change (PadicInt.toZMod (0 : ℤ_[p])).val • x = 0
    rw [map_zero, ZMod.val_zero, zero_nsmul]
  map_add' a b := by
    ext x
    change (PadicInt.toZMod (a + b)).val • x = (PadicInt.toZMod a).val • x + (PadicInt.toZMod b).val • x
    rw [map_add, ZMod.val_add, ← nsmul_eq_mod_nsmul _ (hM x), add_nsmul]

lemma padicEnd_apply (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (hM : ∀ x : M, p • x = 0)
    (c : ℤ_[p]) (x : M) : padicEnd p M hM c x = (PadicInt.toZMod c).val • x := rfl

def liftInt {A B C : Type} [CommRing A] [CommRing B] [Ring C] (φ : A →+* C) (ψ : B →+* C)
    (h : ∀ a b, φ a * ψ b = ψ b * φ a) : A ⊗[ℤ] B →+* C :=
  (Algebra.TensorProduct.lift φ.toIntAlgHom ψ.toIntAlgHom h).toRingHom

lemma liftInt_tmul {A B C : Type} [CommRing A] [CommRing B] [Ring C] (φ : A →+* C) (ψ : B →+* C)
    (h : ∀ a b, φ a * ψ b = ψ b * φ a) (a : A) (b : B) : liftInt φ ψ h (a ⊗ₜ[ℤ] b) = φ a * ψ b :=
  Algebra.TensorProduct.lift_tmul φ.toIntAlgHom ψ.toIntAlgHom h a b

variable {R₀ : Type} [CommRing R₀]

lemma pTorsion_nsmul_eq_zero (B : BX R₀) (p : ℕ) (S : LAlg R₀) (x : torP B p S) : p • x = 0 :=
  Subtype.ext ((mem_torP B p _).1 x.2)

def resEnd {B : BX R₀} {O : LAlg R₀} (e : OEnd B O) (p : ℕ) {S : LAlg R₀} (s : LHom O S) :
    AddMonoid.End (torP B p S) :=
  ((e.f s).comp (torP B p S).subtype).codRestrict (torP B p S) fun x => by
    rw [mem_torP, ← map_nsmul, pTorsion_nsmul_eq_zero, map_zero]

lemma resEnd_apply {B : BX R₀} {O : LAlg R₀} (e : OEnd B O) (p : ℕ) {S : LAlg R₀} (s : LHom O S)
    (x : torP B p S) : (resEnd e p s x : B.G S) = e.f s x := rfl

def ordEnd {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) : O₀ →+* AddMonoid.End (torP B p S) :=
  RingHom.mk' (α := O₀) (β := AddMonoid.End (torP B p S))
    { toFun := fun a => resEnd (f a) p s
      map_one' := AddMonoidHom.ext fun x => Subtype.ext (h x).1
      map_mul' := fun a b => AddMonoidHom.ext fun x => Subtype.ext ((h x).2 a b).2 }
    fun a b => AddMonoidHom.ext fun x => Subtype.ext ((h x).2 a b).1

def complEnd {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    [Fact p.Prime] {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) :
    ℤ_[p] ⊗[ℤ] O₀ →+* AddMonoid.End (torP B p S) :=
  liftInt (padicEnd p _ (pTorsion_nsmul_eq_zero B p S)) (ordEnd f p s h) fun c a =>
    AddMonoidHom.ext fun x => (map_nsmul (ordEnd f p s h a) (PadicInt.toZMod c).val x).symm

lemma complEnd_tmul {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    [Fact p.Prime] {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) (c : ℤ_[p]) (a : O₀) (x : torP B p S) :
    (complEnd f p s h (c ⊗ₜ[ℤ] a) x : B.G S) = (PadicInt.toZMod c).val • (f a).f s x := by
  have e : complEnd f p s h (c ⊗ₜ[ℤ] a) =
      padicEnd p _ (pTorsion_nsmul_eq_zero B p S) c * ordEnd f p s h a := liftInt_tmul _ _ _ c a
  rw [e]
  rfl

def complMat {g : ℕ} {O : Type} [CommRing O] {O₀ : Type} [CommRing O₀] (p : ℕ) [Fact p.Prime]
    [Algebra ℤ_[p] O] (dL : O₀ →+* Matrix (Fin g) (Fin g) O) :
    ℤ_[p] ⊗[ℤ] O₀ →+* Matrix (Fin g) (Fin g) O :=
  liftInt (algebraMap ℤ_[p] (Matrix (Fin g) (Fin g) O)) dL fun c a => Algebra.commutes c (dL a)

lemma complMat_tmul {g : ℕ} {O : Type} [CommRing O] {O₀ : Type} [CommRing O₀] (p : ℕ)
    [Fact p.Prime] [Algebra ℤ_[p] O] (dL : O₀ →+* Matrix (Fin g) (Fin g) O) (c : ℤ_[p]) (a : O₀) :
    complMat p dL (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] O c • dL a := by
  rw [complMat, liftInt_tmul, algebraMap_smul]
  exact (Algebra.smul_def c (dL a)).symm

def kerMul {R S : LAlg R₀} (π : LHom R S) (r : (R : Type)) (i : π.ker) : π.ker :=
  ⟨r * i, Ideal.mul_mem_left (RingHom.ker π.1) r i.2⟩

lemma padic_mul_eq {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (t : ℤ_[p] →+* R) (c : ℤ_[p])
    (i : R) (hi : p • i = 0) : t c * i = (PadicInt.toZMod c).val • i := by
  have h : c - ((PadicInt.toZMod c).val : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨d, hd⟩ := h
  have hc : c = d * p + ((PadicInt.toZMod c).val : ℤ_[p]) := by rw [hd]; ring
  rw [nsmul_eq_mul] at hi ⊢
  conv_lhs => rw [hc]
  rw [map_add, map_mul, map_natCast, map_natCast, add_mul, _root_.mul_assoc, hi, mul_zero, zero_add]

theorem main :
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} (B : BX R₀) (O : LAlg R₀) (gb : Module.Basis (Fin g) R₀ B.gg) (O₀ : Type) [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] (O : Type)] (dL : O₀ →+* Matrix (Fin g) (Fin g) (O : Type)),
    Function.Surjective (algebraMap R₀ (O : Type)) → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) →
    (∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (dL a k l) * i) →
      (f a).f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)) →
    ∃ (A : OAct B O p (ℤ_[p] ⊗[ℤ] O₀)) (ρL : ℤ_[p] ⊗[ℤ] O₀ →+* Matrix (Fin g) (Fin g) (O : Type)),
      (∀ c a, ρL (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] (O : Type) c • dL a) ∧
      (∀ a k l, ρL a k l = algebraMap R₀ (O : Type) (gb.repr (A.actL a (gb l)) k)) ∧
      ∀ c a (S : LAlg R₀) (s : LHom O S) (x : torP B p S), (A.act (c ⊗ₜ[ℤ] a) S s x : B.G S) = (PadicInt.toZMod c).val • (f a).f s x) := by
  intro R₀ _ g B O gb O₀ _ f p _ _ dL hs hf htg
  choose pre hpre using hs
  let L : ℤ_[p] ⊗[ℤ] O₀ → B.gg →ₗ[R₀] B.gg := fun a =>
    gb.constr R₀ fun l => ∑ k, pre (complMat p dL a k l) • gb k
  have hL : ∀ a l, L a (gb l) = ∑ k, pre (complMat p dL a k l) • gb k := fun a l =>
    gb.constr_basis R₀ _ l
  have key : ∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g)
      (i : π.ker) (hi : p • i = 0),
      (complEnd f p s (hf s) a ⟨B.tg π hπ (gb l ⊗ₜ i), tg_torP B p π hπ _ i hi⟩ : B.G R) =
        B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] kerMul π (s.1 (complMat p dL a k l)) i) := by
    intro a R S s π hπ l i hi
    induction a using TensorProduct.induction_on with
    | zero =>
      have : ∀ k, kerMul π (s.1 (complMat p dL 0 k l)) i = 0 := fun k =>
        Subtype.ext (by simp [kerMul])
      simp only [this]
      simp only [TensorProduct.tmul_zero, Finset.sum_const_zero, map_zero]
      rfl
    | tmul c a =>
      rw [complEnd_tmul]
      change _ • (f a).f s (B.tg π hπ (gb l ⊗ₜ i)) = _
      rw [htg a s π hπ l i (fun k => kerMul π (s.1 (dL a k l)) i) (fun k => rfl), ← map_nsmul,
        Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      refine (map_nsmul (TensorProduct.mk R₀ B.gg π.ker (gb k)) _ _).symm.trans ?_
      change gb k ⊗ₜ[R₀] _ = _
      congr 1
      apply Subtype.ext
      have hi' : p • (i : (R : Type)) = 0 := congrArg Subtype.val hi
      have h2 := padic_mul_eq (s.1.toRingHom.comp (algebraMap ℤ_[p] (O : Type))) c
        (s.1 (dL a k l) * i) (by rw [← mul_smul_comm, hi', mul_zero])
      change (PadicInt.toZMod c).val • (s.1 (dL a k l) * i) = s.1 (complMat p dL (c ⊗ₜ a) k l) * i
      rw [← h2, complMat_tmul, Matrix.smul_apply, smul_eq_mul, map_mul, _root_.mul_assoc]
      rfl
    | add a b ha hb =>
      have : ∀ k, kerMul π (s.1 (complMat p dL (a + b) k l)) i =
          kerMul π (s.1 (complMat p dL a k l)) i + kerMul π (s.1 (complMat p dL b k l)) i :=
        fun k => Subtype.ext (by simp [kerMul, add_mul])
      simp only [this, TensorProduct.tmul_add, Finset.sum_add_distrib]
      rw [map_add (B.tg π hπ), ← ha, ← hb, map_add]
      rfl
  have key2 : ∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g)
      (i : π.ker) (hi : p • i = 0),
      (complEnd f p s (hf s) a ⟨B.tg π hπ (gb l ⊗ₜ i), tg_torP B p π hπ _ i hi⟩ : B.G R) =
        B.tg π hπ (L a (gb l) ⊗ₜ[R₀] i) := by
    intro a R S s π hπ l i hi
    rw [key a s π hπ l i hi, hL, TensorProduct.sum_tmul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    change s.1 (complMat p dL a k l) * i = pre (complMat p dL a k l) • (i : (R : Type))
    rw [Algebra.smul_def, ← s.1.commutes, hpre]
  refine ⟨{ act := fun a S s => complEnd f p s (hf s) a
            act_one := fun S s x => by rw [map_one]; rfl
            act_mul := fun a b S s x => by rw [map_mul]; rfl
            act_add := fun a b S s x => by rw [map_add]; rfl
            act_nat := ?_
            actL := L
            act_tg := ?_ }, complMat p dL, complMat_tmul p dL, ?_,
            fun c a S s x => complEnd_tmul f p s (hf s) c a x⟩
  · intro a S S' s s' φ hφ x
    subst hφ
    change B.map φ (complEnd f p s (hf s) a x : B.G S) =
      (complEnd f p (φ.comp s) (hf _) a ⟨B.map φ x, map_torP B p φ x⟩ : B.G S')
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul c a => rw [complEnd_tmul, complEnd_tmul, map_nsmul, (f a).nat]
    | add a b ha hb =>
      rw [map_add, map_add]
      change B.map φ ((complEnd f p s (hf s) a x : B.G S) + (complEnd f p s (hf s) b x : B.G S)) = _
      rw [map_add, ha, hb]
      rfl
  · intro a R S s π hπ w i hi
    have hr : ∀ l, p • (gb.repr w l • i) = 0 := fun l => by rw [smul_comm, hi, smul_zero]
    have h1 : (⟨B.tg π hπ (w ⊗ₜ i), tg_torP B p π hπ w i hi⟩ : torP B p R) =
        ∑ l, ⟨B.tg π hπ (gb l ⊗ₜ (gb.repr w l • i)), tg_torP B p π hπ _ _ (hr l)⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      change B.tg π hπ (w ⊗ₜ i) = ∑ l, B.tg π hπ (gb l ⊗ₜ (gb.repr w l • i))
      rw [← map_sum]
      congr 1
      conv_lhs => rw [← gb.sum_repr w, TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun l _ => TensorProduct.smul_tmul _ _ _
    change (complEnd f p s (hf s) a ⟨B.tg π hπ (w ⊗ₜ i), tg_torP B p π hπ w i hi⟩ : B.G R) = _
    rw [h1, map_sum, AddSubmonoidClass.coe_finset_sum,
      Finset.sum_congr rfl fun l _ => key2 a s π hπ l _ (hr l), ← map_sum]
    congr 1
    conv_rhs => rw [← gb.sum_repr w, map_sum, TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, TensorProduct.smul_tmul]
  · intro a k l
    change complMat p dL a k l = algebraMap R₀ (O : Type) (gb.repr (L a (gb l)) k)
    rw [hL, gb.repr_sum_self, hpre]

end GlobalTheory.PadicOrderAction
