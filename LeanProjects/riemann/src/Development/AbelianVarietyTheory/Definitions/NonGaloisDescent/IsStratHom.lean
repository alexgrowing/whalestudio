import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime]

structure BK (K : FinExt l) where

  a : ℕ
  [a_ne : NeZero a]

  Ep : Polynomial (Wq l a)
  monic : Ep.Monic
  deg_pos : 0 < Ep.natDegree
  dvd_coeff : ∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i
  coeff_zero : ∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w
  not_expand : ∃ i, ¬ l ∣ i ∧ Ep.coeff i ≠ 0

  str : ↥(OL K) ≃+* ((Wq l a)⟦X⟧ ⧸ Ideal.span {(Ep : (Wq l a)⟦X⟧)})
  isUnit_δ : IsUnit ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧))
  complete : IsAdicComplete (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)}) (Wq l a)⟦X⟧

  flat : OCb l

  ev : (Wq l a)⟦X⟧ →+* Ainf l
  ev_X : ev X = WittVector.teichmuller l flat
  ev_C : ∀ w, ev (C w) = wA l a w
  ev_frob : ∀ x, ev (frobS l a x) = WittVector.frobenius (ev x)
  span_ev : Ideal.span {ev (Ep : (Wq l a)⟦X⟧)} = RingHom.ker (Per.θ l)
  θ_ev : ∀ (r : ↥(OL K)) (x : (Wq l a)⟦X⟧), Ideal.Quotient.mk _ x = str r → Per.θ l (ev x) = intToOC K r
  gal_w : ∀ (g : ↥(GK K)) (w : Wq l a), Per.σA (g : GQ l) (wA l a w) = wA l a w

attribute [instance] BK.a_ne

namespace BK

variable {K : FinExt l} (bk : BK K)

abbrev S : Type := (Wq l bk.a)⟦X⟧

abbrev E : bk.S := (bk.Ep : (Wq l bk.a)⟦X⟧)

theorem E_ne_zero : bk.E ≠ 0 := fun h => bk.monic.ne_zero (Polynomial.coe_eq_zero_iff.1 h)

def prism : Obj l ↥(OL K) where
  A := bk.S
  D := deltaS l bk.a
  I := Ideal.span {bk.E}
  inv := invertible_span_singleton (mem_nonZeroDivisors_of_ne_zero bk.E_ne_zero)
  complete := bk.complete
  l_mem := Delta.l_mem_of_isUnit hl.out.pos _ bk.isUnit_δ
  bdd := ⟨0, fun x ⟨m, hm⟩ => by
    have h := congrArg bk.str.symm hm
    rw [map_mul, map_pow, map_natCast, map_zero] at h
    have h2 := (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
    rw [pow_zero, one_mul]
    exact bk.str.symm.injective (h2.trans (map_zero _).symm)⟩
  str := bk.str.toRingHom

def toP : bk.S ≃+* bk.prism.A := RingEquiv.refl _

variable {bk} in

def hf {B : Obj l ↥(OL K)} (f : Hom bk.prism B) : bk.S →+* B.A := f.f

def ι : Hom bk.prism (ainfObj K) where
  f := bk.ev
  f_δ := (deltaS l bk.a).map_δ_of_map_φ (ainfDelta l) ainf_torsionFree bk.ev bk.ev_frob
  f_I x hx := by
    obtain ⟨y, rfl⟩ := (Ideal.mem_span_singleton' (α := bk.S)).1 hx
    change bk.ev (y * bk.E) ∈ RingHom.ker (Per.θ l)
    rw [← bk.span_ev, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  f_str r x h := ((isAinf_ainfObj K).mk_eq_str_iff r (bk.ev x)).2 (bk.θ_ev r x h)

abbrev J : Ideal bk.S := Ideal.span {(l : bk.S)} ⊔ Ideal.span {bk.E}

def ρ₀ : ℝ≥0 := (l : ℝ≥0) ^ (-(1 / (bk.Ep.natDegree : ℝ)))

def evW : bk.S →+* WCb l := (inclW l).comp bk.ev

def FixFlat (g : ↥(GK K)) : Prop := Per.σF (g : GQ l) bk.flat = bk.flat

def IsPer (τ : Ainf l) : Prop :=
  WittVector.frobenius τ = bk.ev bk.E * τ ∧ ∃ (ε : OCb l) (η : (Ainf l)ˣ), GlobalTheory.MemLoc.IsEps ε ∧
    WittVector.frobenius τ = η * (WittVector.teichmuller l ε - 1)

def OE : Subring (WCb l) where
  carrier := {w | ∀ n : ℕ, ∃ (m : ℕ) (s : bk.S) (y : WCb l), bk.evW X ^ m * w = bk.evW s + (l : WCb l) ^ n * y}
  zero_mem' _ := ⟨0, 0, 0, by simp⟩
  one_mem' _ := ⟨0, 1, 0, by simp⟩
  neg_mem' hw n := by
    obtain ⟨m, s, y, h⟩ := hw n
    exact ⟨m, -s, -y, by rw [map_neg]; linear_combination -h⟩
  add_mem' hw hw' n := by
    obtain ⟨m, s, y, h⟩ := hw n
    obtain ⟨m', s', y', h'⟩ := hw' n
    refine ⟨m + m', X ^ m' * s + X ^ m * s', bk.evW X ^ m' * y + bk.evW X ^ m * y', ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow]
    linear_combination bk.evW X ^ m' * h + bk.evW X ^ m * h'
  mul_mem' {w w'} hw hw' n := by
    obtain ⟨m, s, y, h⟩ := hw n
    obtain ⟨m', s', y', h'⟩ := hw' n
    refine ⟨m + m', s * s', bk.evW s * y' + y * (bk.evW X ^ m' * w'), ?_⟩
    rw [map_mul]
    linear_combination (bk.evW X ^ m' * w') * h + bk.evW s * h'

abbrev DS (ρ : ℝ≥0) : Type := Disc l (X : bk.S) ρ

abbrev DA (ρ : ℝ≥0) : Type := Disc l (bk.ev X) ρ

abbrev iA : Ainf l →+* bk.DA bk.ρ₀ := toDisc l (bk.ev X) bk.ρ₀

abbrev iS : bk.S →+* bk.DA bk.ρ₀ := bk.iA.comp bk.ev

end BK

abbrev Digits (l : ℕ) : Type := {α : ℕ →₀ ℕ // ∀ i, α i < l}

structure Env {K : FinExt l} (bk : BK K) (B : Obj l ↥(OL K)) (d p : B.A) where

  Q : Obj l ↥(OL K)

  inl : Hom B Q

  inr : Hom bk.prism Q
  univ : ∀ (C : Obj l ↥(OL K)) (f : Hom B C) (g : Hom bk.prism C), ∃! h : Hom Q C, h.comp inl = f ∧ h.comp inr = g

  w : Q.A
  w_eq : BK.hf inr X = inl.f p + inl.f d * w
  I_eq : Q.I = Ideal.span {inl.f d}

  tb : TopBasis inl.f (Ideal.span {(l : B.A)} ⊔ B.I) (Digits l)
  tb_b : ∀ α, tb.b α = α.1.prod fun i n => (Q.D.δ^[i] w) ^ n

def IsFrame {K : FinExt l} (bk : BK K) (B : Obj l ↥(OL K)) (d p : B.A) : Prop :=
  B.I = Ideal.span {d} ∧ Ideal.Quotient.mk B.I p = B.str (bk.str.symm (Ideal.Quotient.mk _ X))

structure Strat {K : FinExt l} (bk : BK K) (d : ℕ) where

  a : ℕ

  b : ℕ

  A : Matrix (Fin d) (Fin d) bk.S

  A' : Matrix (Fin d) (Fin d) bk.S
  A_mul : A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S)

  ε : ∀ {B : Obj l ↥(OL K)}, Hom bk.prism B → Hom bk.prism B → Matrix (Fin d) (Fin d) B.A
  ε_refl : ∀ {B} (f : Hom bk.prism B), ε f f = 1
  ε_trans : ∀ {B} (f g h : Hom bk.prism B), ε f g * ε g h = ε f h
  ε_nat : ∀ {B B'} (k : Hom B B') (f g : Hom bk.prism B), (ε f g).map k.f = ε (k.comp f) (k.comp g)
  ε_φ : ∀ {B} (f g : Hom bk.prism B), BK.hf g bk.E ^ a • (A.map (BK.hf f) * (ε f g).map B.D.φ) =
    BK.hf f bk.E ^ a • (ε f g * A.map (BK.hf g))

structure Framed {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d) (M : FCrys l ↥(OL K))
    (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) : Prop where
  tr : ∀ {B} (f g : Hom bk.prism B) (j : Fin d), M.tr g (e j) = ∑ i, S.ε f g i j • M.tr f (e i)
  Φ : ∀ j : Fin d, IsFrac (bk.toP bk.E)
    (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (S.A i j) • e i) S.a

structure IsStratHom {K : FinExt l} {bk : BK K} {d d' : ℕ} (S : Strat bk d) (S' : Strat bk d')
    (Y : Matrix (Fin d') (Fin d) bk.S) : Prop where
  φ : bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A)
  ε : ∀ {B} (f g : Hom bk.prism B), S'.ε f g * Y.map (BK.hf g) = Y.map (BK.hf f) * S.ε f g

abbrev zW {m n : Type} (M : Matrix m n ℤ_[l]) : Matrix m n (WCb l) := M.map (algebraMap ℤ_[l] (WCb l))

structure MReal {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (T : Matrix (Fin d) (Fin d) (WCb l)) : Prop where
  unit : IsUnit T
  φ : bk.evW bk.E ^ S.a • T.map (frobW l) = T * S.A.map bk.evW
  gal : ∀ g : ↥(GK K), zW (ρ g) * T.map (galW l (g : GQ l)) =
    T * (S.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l)

structure Seed {K : FinExt l} (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) where

  N : ℕ

  c₁ : ℕ

  c₂ : ℕ

  c₃ : ℕ

  F : Matrix (Fin d) (Fin d) (Wq l bk.a)

  F' : Matrix (Fin d) (Fin d) (Wq l bk.a)
  F_mul : F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a))

  X : Matrix (Fin d) (Fin d) bk.S

  X' : Matrix (Fin d) (Fin d) bk.S
  X_mul : X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) bk.S)
  nopole : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j,
    BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j

  W : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)

  W' : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)
  W_mul : W * W' = bk.iA τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))
  φ : ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap WittVector.frobenius Φ →
    ((l : bk.DA bk.ρ₀) ^ c₁) • (W * X'.map bk.iS).map Φ =
      bk.iS (frobS l bk.a bk.E) ^ N • (W * X'.map bk.iS * F.map (bk.iS.comp C))
  gal : ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G →
    bk.iA (bk.ev bk.E * τ) ^ N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (W * X'.map bk.iS).map G) =
      bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) ^ N • (W * X'.map bk.iS)

structure Height {K : FinExt l} {bk : BK K} {d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {τ : Ainf l}
    (s : Seed bk d ρ τ) where

  Y : Matrix (Fin d) (Fin d) (Ainf l)
  unit : IsUnit (Y.map (inclW l))

  Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)
  Z_unit : IsUnit Z
  W_mul : ∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev i → s.W * Z.map i = Y.map bk.iA

  a : ℕ

  b : ℕ

  A : Matrix (Fin d) (Fin d) bk.S

  A' : Matrix (Fin d) (Fin d) bk.S
  A_mul : A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S)
  φ : bk.ev bk.E ^ a • Y.map WittVector.frobenius = Y * A.map bk.ev

def Strat.unit {K : FinExt l} (bk : BK K) (d : ℕ) : Strat bk d where
  a := 0
  b := 0
  A := 1
  A' := 1
  A_mul := by simp
  ε _ _ := 1
  ε_refl _ := rfl
  ε_trans _ _ _ := mul_one _
  ε_nat k _ _ := Matrix.map_one _ (map_zero _) (map_one _)
  ε_φ f g := by
    rw [pow_zero, pow_zero, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.BSP
