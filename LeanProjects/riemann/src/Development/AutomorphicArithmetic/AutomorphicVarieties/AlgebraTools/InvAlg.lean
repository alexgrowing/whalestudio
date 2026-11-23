import Mathlib

noncomputable section

namespace UpperTheory.V.AlgebraTools

structure TrInv (B E : Type*) [CommRing B] [Ring E] [Algebra B E] where
  st : E →ₗ[B] E
  st_mul : ∀ x y, st (x * y) = st y * st x
  st_st : ∀ x, st (st x) = x
  tr : E →ₗ[B] B
  tr_comm : ∀ x y, tr (x * y) = tr (y * x)
  tr_st : ∀ x, tr (st x) = tr x

def TrInv.matrix (B ι : Type*) [CommRing B] [Fintype ι] [DecidableEq ι] : TrInv B (Matrix ι ι B) where
  st := (Matrix.transposeLinearEquiv ι ι B B).toLinearMap
  st_mul x y := Matrix.transpose_mul x y
  st_st _ := rfl
  tr := Matrix.traceLinearMap ι B B
  tr_comm x y := Matrix.trace_mul_comm x y
  tr_st x := Matrix.trace_transpose x

structure OddForm (B N : Type*) [CommRing B] [AddCommGroup N] [Module B N] where
  be : N →ₗ[B] N →ₗ[B] B
  symm : ∀ b b', be b b' = be b' b
  assoc : ∀ b b' b'', be b b' • b'' = be b' b'' • b

namespace OddForm

variable {B N : Type*} [CommRing B] [AddCommGroup N] [Module B N]

instance : Inhabited (OddForm B N) := ⟨⟨0, fun _ _ => rfl, fun _ _ _ => by simp⟩⟩

def ofScalar (c : B) : OddForm B B where
  be := c • LinearMap.mul B B
  symm b b' := by simp [mul_comm]
  assoc b b' b'' := by simp; ring

@[nolint unusedArguments]
def Ext (_ : OddForm B N) : Type _ := B × N

variable (Φ : OddForm B N)

instance : AddCommGroup Φ.Ext := inferInstanceAs (AddCommGroup (B × N))
instance : Module B Φ.Ext := inferInstanceAs (Module B (B × N))

def el (a : B) (b : N) : Φ.Ext := (a, b)

variable {Φ}

def Ext.ev (z : Φ.Ext) : B := Prod.fst z

def Ext.od (z : Φ.Ext) : N := Prod.snd z

@[ext] theorem Ext.ext {z w : Φ.Ext} (h : z.ev = w.ev) (h' : z.od = w.od) : z = w := Prod.ext h h'

instance : One Φ.Ext := ⟨Φ.el 1 0⟩
instance : Mul Φ.Ext := ⟨fun z w => Φ.el (z.ev * w.ev + Φ.be z.od w.od) (z.ev • w.od + w.ev • z.od)⟩

@[simp] theorem ev_el (a : B) (b : N) : (Φ.el a b).ev = a := rfl
@[simp] theorem od_el (a : B) (b : N) : (Φ.el a b).od = b := rfl
@[simp] theorem ev_add (z w : Φ.Ext) : (z + w).ev = z.ev + w.ev := rfl
@[simp] theorem od_add (z w : Φ.Ext) : (z + w).od = z.od + w.od := rfl
@[simp] theorem ev_zero : (0 : Φ.Ext).ev = 0 := rfl
@[simp] theorem od_zero : (0 : Φ.Ext).od = 0 := rfl
@[simp] theorem ev_one : (1 : Φ.Ext).ev = 1 := rfl
@[simp] theorem od_one : (1 : Φ.Ext).od = 0 := rfl
@[simp] theorem ev_smul (c : B) (z : Φ.Ext) : (c • z).ev = c * z.ev := rfl
@[simp] theorem od_smul (c : B) (z : Φ.Ext) : (c • z).od = c • z.od := rfl
@[simp] theorem ev_mul (z w : Φ.Ext) : (z * w).ev = z.ev * w.ev + Φ.be z.od w.od := rfl
@[simp] theorem od_mul (z w : Φ.Ext) : (z * w).od = z.ev • w.od + w.ev • z.od := rfl

instance : CommRing Φ.Ext :=
  { (inferInstance : AddCommGroup Φ.Ext), (inferInstance : One Φ.Ext), (inferInstance : Mul Φ.Ext) with
    mul_assoc := fun x y z => by
      ext
      · simp; ring
      · simp only [od_mul, ev_mul, add_smul, smul_add, smul_smul]
        rw [Φ.assoc x.od y.od z.od, mul_comm z.ev x.ev, mul_comm z.ev y.ev]; abel
    one_mul := fun x => by ext <;> simp
    mul_one := fun x => by ext <;> simp
    zero_mul := fun x => by ext <;> simp
    mul_zero := fun x => by ext <;> simp
    left_distrib := fun x y z => by
      ext
      · simp; ring
      · simp [add_smul]; abel
    right_distrib := fun x y z => by
      ext
      · simp; ring
      · simp [add_smul]; abel
    mul_comm := fun x y => by
      ext
      · simp [mul_comm, Φ.symm x.od]
      · simp [add_comm] }

instance : Algebra B Φ.Ext :=
  Algebra.ofModule
    (fun c x y => by
      ext
      · simp; ring
      · simp [smul_smul, mul_comm, add_comm])
    (fun c x y => by
      ext
      · simp; ring
      · simp [smul_smul, mul_comm, add_comm])

instance [Module.Finite B N] : Module.Finite B Φ.Ext := inferInstanceAs (Module.Finite B (B × N))

def red (Φ : OddForm B N) : Ideal B := Ideal.span {c | ∃ b b', c = Φ.be b b'}

end OddForm

variable {B E : Type*} [CommRing B] [Ring E] [Algebra B E]

def corner (B : Type*) [CommRing B] [Algebra B E] (e e' : E) : Submodule B E :=
  LinearMap.range ((LinearMap.mulLeft B e).comp (LinearMap.mulRight B e'))

def cornerProj (B : Type*) [CommRing B] [Algebra B E] (e e' : E) : E →ₗ[B] corner B e e' :=
  ((LinearMap.mulLeft B e).comp (LinearMap.mulRight B e')).rangeRestrict

structure TrInv.Units (T : TrInv B E) (ι : Type*) [Fintype ι] (o : ι → ι) where
  ep : ι → E
  x : ι → E
  o_o : ∀ i, o (o i) = o i
  coi : CompleteOrthogonalIdempotents ep
  st_ep : ∀ i, T.st (ep i) = ep i
  tr_ep : ∀ i, T.tr (ep i) = 1
  rank_one : ∀ i y, ∃ b : B, ep i * y * ep i = b • ep i
  x_mem : ∀ i, ep (o i) * x i * ep i = x i
  x_base : ∀ i, x (o i) = ep (o i)
  x_st : ∀ i, x i * T.st (x i) = ep (o i)
  st_mul_x_eq : ∀ i, T.st (x i) * x i = ep i

def TrInv.matrixUnits (B ι : Type*) [CommRing B] [Fintype ι] [DecidableEq ι] (o : ι → ι) (ho : ∀ i, o (o i) = o i) :
    (TrInv.matrix B ι).Units ι o where
  ep i := Matrix.single i i 1
  x i := Matrix.single (o i) i 1
  o_o := ho
  coi :=
    { idem := fun i => by simp [IsIdempotentElem]
      ortho := fun i j h => Matrix.single_mul_single_of_ne _ _ _ _ h _
      complete := by
        ext i j
        simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
        by_cases h : i = j
        · subst h; simp
        · rw [if_neg h]; exact Finset.sum_eq_zero fun k _ => if_neg fun hk => h (hk.1.symm.trans hk.2) }
  st_ep i := Matrix.transpose_single _ _ _
  tr_ep i := by simp [TrInv.matrix]
  rank_one i y := ⟨y i i, by simp [Matrix.single_mul_mul_single]⟩
  x_mem i := by simp
  x_base i := by rw [ho]
  x_st i := by simp [TrInv.matrix]
  st_mul_x_eq i := by simp [TrInv.matrix]

namespace TrInv.Units

variable {T : TrInv B E} {ι : Type*} [Fintype ι] {o : ι → ι} (U : T.Units ι o)

theorem corner_eq (i : ι) (y : E) : U.ep i * y * U.ep i = T.tr (U.ep i * y * U.ep i) • U.ep i := by
  obtain ⟨b, hb⟩ := U.rank_one i y
  rw [hb, map_smul, U.tr_ep, smul_eq_mul, mul_one]

def oddForm (p q : ι) : OddForm B (corner B (U.ep p) (U.ep q)) where
  be := LinearMap.mk₂ B (fun b b' => T.tr (b.1 * T.st b'.1))
    (fun _ _ _ => by simp [add_mul]) (fun _ _ _ => by simp) (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp)
  symm b b' := by
    simp only [LinearMap.mk₂_apply]
    rw [← T.tr_st, T.st_mul, T.st_st]
  assoc := by
    rintro ⟨_, y, rfl⟩ ⟨_, y', rfl⟩ ⟨_, y'', rfl⟩
    apply Subtype.ext
    have hp := (U.coi.idem p).eq
    have hq := (U.coi.idem q).eq
    have hp' : ∀ z, U.ep p * (U.ep p * z) = U.ep p * z := fun z => by rw [← mul_assoc, hp]
    have hq' : ∀ z, U.ep q * (U.ep q * z) = U.ep q * z := fun z => by rw [← mul_assoc, hq]
    have h1 := U.corner_eq p (y * U.ep q * T.st y')
    have h2 := U.corner_eq q (T.st y' * U.ep p * y'')
    have h3 : T.tr (U.ep p * (y' * U.ep q) * T.st (U.ep p * (y'' * U.ep q))) =
        T.tr (U.ep q * (T.st y' * U.ep p * y'') * U.ep q) := by
      rw [← T.tr_st, T.st_mul, T.st_st, T.tr_comm]
      simp only [T.st_mul, U.st_ep, mul_assoc, hp']
    have h4 : T.tr (U.ep p * (y * U.ep q) * T.st (U.ep p * (y' * U.ep q))) =
        T.tr (U.ep p * (y * U.ep q * T.st y') * U.ep p) := by
      simp only [T.st_mul, U.st_ep, mul_assoc, hq']
    simp only [LinearMap.mk₂_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      SetLike.val_smul]
    rw [h3, h4]
    calc _ = (T.tr (U.ep p * (y * U.ep q * T.st y') * U.ep p) • U.ep p) * (y'' * U.ep q) := by
          rw [smul_mul_assoc]
      _ = U.ep p * y * (U.ep q * (T.st y' * U.ep p * y'') * U.ep q) := by
          rw [← h1]; simp only [mul_assoc]
      _ = _ := by rw [h2, mul_smul_comm, ← h2, mul_assoc (U.ep p)]

def vr (p q : ι) (y : E) : Matrix ι ι (U.oddForm p q).Ext := Matrix.of fun i j =>
  (U.oddForm p q).el (T.tr (U.x i * y * T.st (U.x j)))
    (cornerProj B (U.ep p) (U.ep q) (U.x i * y * T.st (U.x j)) +
      cornerProj B (U.ep p) (U.ep q) (T.st (U.x i * y * T.st (U.x j))))

end TrInv.Units

end UpperTheory.V.AlgebraTools
