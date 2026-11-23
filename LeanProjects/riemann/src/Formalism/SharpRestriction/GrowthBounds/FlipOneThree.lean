import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GrowthBounds.ObjSeg
import Formalism.SharpRestriction.GrowthBounds.ObjBridge
import Formalism.SharpRestriction.GrowthBounds.ColumnSystems
import Formalism.MahlerMeasure.WithMargin

noncomputable section

namespace Formalism.MainNotions.flipOneThree

open MvPolynomial Finset Formalism.MainNotions.G

def lgA (p a r : ℕ) : ℝ := Real.logb p (8 * a + r) + 1

def kappaOneExponent (p a r : ℕ) : ℝ := (r : ℝ) ^ 2 * lgA p a r

def kappaZeroExponent (p a Nt r : ℕ) : ℝ := 2 * Nt * ((r : ℝ) + 1) * Real.logb p a

def depthD (C : ℝ) (p a Nt N₁ r : ℕ) (Y : ℝ) : ℝ :=
  C * Y ^ 2 * (N₁ : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 * lgA p a r + 2 * kappaZeroExponent p a Nt r

structure Inst where
  L : Formalism.MainNotions.ColumnSystems.Loc
  hm : L.m ≠ 0
  W : Type
  Qq : Type
  O : Type
  Kf : Type
  [ringW : CommRing W]
  [domW : IsDomain W]
  [dvrW : IsDiscreteValuationRing W]
  [fieldQ : Field Qq]
  [algW : Algebra W Qq]
  [ring : CommRing O]
  [dom : IsDomain O]
  [dvr : IsDiscreteValuationRing O]
  [fieldK : Field Kf]
  [algO : Algebra O Kf]
  ι : Qq →+* Kf
  σ : Qq ≃+* Qq
  jO : W →+* O
  w : O
  std : UnramifiedQuadraticSetting L.p L.n' W Qq O Kf ι σ jO w
  j : Fin (numSeg L.TT)
  m : ℝ
  xa : ℝ
  xb : ℝ

attribute [instance] Inst.ringW Inst.domW Inst.dvrW Inst.fieldQ Inst.algW Inst.ring Inst.dom Inst.dvr Inst.fieldK
  Inst.algO

namespace Inst

variable (X : Inst)

abbrev p : ℕ := X.L.p

abbrev r : ℕ := X.L.m

abbrev s : ℕ := segS X.L.TT X.j

abbrev Nt : ℕ := X.L.TT.card

abbrev N₁ : ℕ := X.L.N1

abbrev S (C0 CE1 CE2 : ℝ) : SegData X.s := X.L.seg C0 CE1 CE2 X.j

def setting : UniformizedDVR X.p X.O := dvrOfStd X.std

abbrev LA (aT' : Fin X.L.n' → ℕ) : Formalism.MainNotions.ColumnSystems.Loc := { X.L with aT := aT' }

def winA : Finset ℕ := Finset.Icc X.L.a ⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊

def InWinA (aT' : Fin X.L.n' → ℕ) : Prop := Formalism.MainNotions.ColumnSystems.InWin X.xa X.xb (X.LA aT')

end Inst

instance Inst.fact (X : Inst) : Fact X.p.Prime := ⟨X.std.1.prime⟩
instance Inst.neZero (X : Inst) : NeZero X.L.m := ⟨X.hm⟩
instance Inst.neZeroLA (X : Inst) (aT' : Fin X.L.n' → ℕ) : NeZero (X.LA aT').m := ⟨X.hm⟩

theorem admissible_dvr_of_unramified_quadratic_setting {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w) :
    AdmissibleDVR p n' O := by
  refine ⟨h.1.prime, h.1.five_le, h.1.two_le, h.1.even, ?_⟩
  have hmax : (Ideal.span {(p : W)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible h.1.p_unif
  let _ : Field (W ⧸ Ideal.span {(p : W)}) := Ideal.Quotient.field _
  have hp : (p : O) ∈ IsLocalRing.maximalIdeal O := (dvrOfStd h).p_mem
  let f : W →+* FF O := (IsLocalRing.residue O).comp j
  have hf : ∀ a ∈ Ideal.span {(p : W)}, f a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have : f (p : W) = 0 := by
      simp only [f, map_natCast]
      have := (IsLocalRing.residue_eq_zero_iff (p : O)).2 hp
      simpa using this
    rw [map_mul, this, mul_zero]
  let g : (W ⧸ Ideal.span {(p : W)}) →+* FF O := Ideal.Quotient.lift _ f hf
  refine ⟨g.fieldRange, ?_⟩
  rw [← h.1.res_card]
  exact (Nat.card_congr (Equiv.ofInjective g g.injective)).symm

theorem Inst.instance_ring_standard (X : Inst) : AdmissibleDVR X.L.p X.L.n' X.O := admissible_dvr_of_unramified_quadratic_setting X.std

def HI (C0 CYb Cde Ck CD Cb Cc : ℝ) (X : Inst) : Prop :=
  Formalism.MainNotions.ColumnSystems.WindowHypotheses C0 CYb Cde Ck CD Cb X.L ∧
  Formalism.MainNotions.ColumnSystems.CBound Cc X.L ∧
  0 ≤ X.xa ∧ X.xa ≤ 2 * X.L.J0 C0 ∧ 0 ≤ X.xb ∧ X.xb ≤ 2 * X.L.J0 C0 ∧
  (∀ s ∈ X.L.TT, X.L.bl ≤ X.L.bT s ∧ (X.L.bT s : ℝ) ≤ X.L.bh + X.xb) ∧
  X.L.k * X.L.Y ^ 2 * Real.log X.L.a ≤ X.L.a / X.L.b' ∧
  0 ≤ X.m ∧ X.m ≤ X.L.b' / (X.L.k * X.L.Q * X.L.Y)

def Inst.Plain (X : Inst) : Prop := X.xa = 0 ∧ X.xb = 0

def meanKapT (C0 CE1 CE2 : ℝ) (X : Inst) (D : ℝ) : ℝ :=
  (∑ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∑ aPlus ∈ X.winA,
      kapT X.O X.p X.r (X.S C0 CE1 CE2) X.m D aTop aPlus) /
    (X.winA.card : ℝ) ^ (X.s + 1)

def Inst.BlockLetters (C0 CE1 CE2 : ℝ) (X : Inst) (LL : ChainLetters (2 * X.s + 1)) : Prop :=
  ∃ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∃ aPlus ∈ X.winA,
    ∃ b : SegBlock X.s X.r, Kept X.p X.r (X.S C0 CE1 CE2) aTop b ∧
      ∃ (j : Fin (blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b).T.t → ℕ) (jp : ℕ),
        (blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b).LevelOK j jp ∧
        LL = (blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b).lettersAt j jp

def chOps {R : Type} [Field R] {N r : ℕ} (LL : ChainLetters N) (j : ℕ) :
    GLOps r R (MvPolynomial (Fin N × Fin r) R) :=
  Formalism.MainNotions.G.glOps R r (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j}

def chOps' {R : Type} [Field R] {N r : ℕ} (LL : ChainLetters N) (j : ℕ) :
    GLOps (r - 1) R (MvPolynomial (Fin N × Fin r) R) :=
  fun a b => glAct R (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j}
    (Fin.castLE (Nat.sub_le r 1) a) (Fin.castLE (Nat.sub_le r 1) b)

def PTool (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) {n N r : ℕ}
    (LL : ChainLetters N) (E : GLOps n (KK O) (MvPolynomial (Fin N × Fin r) (KK O))) (e1 : ℕ) : Prop :=
  ∀ T : Set (Fin n → ℤ), (∃ e, IsIsoProjSet E T e) ∧ ∀ e, IsIsoProjSet E T e →
    (∀ F ∈ chPol (KK O) r LL, ∀ G ∈ chPol (KK O) r LL, fock (e F) G = fock F (e G)) ∧
    (∀ F ∈ chPol (KK O) r LL, F ∈ IntPol O (Fin N × Fin r) → ((p : KK O) ^ e1) • e F ∈ IntPol O (Fin N × Fin r)) ∧
    (∀ F ∈ chPol (KK O) r LL, F ∈ bbSpec O p (Fin N × Fin r) 1 →
      ((p : KK O) ^ e1) • e F ∈ bbSpec O p (Fin N × Fin r) 1)

def adm1 (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) (X : Inst) : Prop :=
  HI C0 CYb Cde Ck CD Cb Cc X → ∀ LL, X.BlockLetters C0 CE1 CE2 LL →
    (∀ j ≤ 2 * X.s + 1,
      PTool X.O X.p LL (chOps (r := X.r) LL j) ⌈kappaOneExponent X.p X.L.a X.r⌉₊ ∧
      PTool X.O X.p LL (chOps' (r := X.r) LL j) ⌈kappaOneExponent X.p X.L.a X.r⌉₊) ∧
    ∀ j j', j ≤ j' → j' ≤ 2 * X.s + 1 →
      (∀ T T' e e', IsIsoProjSet (chOps (r := X.r) (R := KK X.O) LL j) T e →
        IsIsoProjSet (chOps (r := X.r) (R := KK X.O) LL j') T' e' → e * e' = e' * e) ∧
      (∀ T T' e e', IsIsoProjSet (chOps (r := X.r) (R := KK X.O) LL j) T e →
        IsIsoProjSet (chOps' (r := X.r) (R := KK X.O) LL j') T' e' → e * e' = e' * e) ∧
      (∀ T T' e e', IsIsoProjSet (chOps' (r := X.r) (R := KK X.O) LL j) T e →
        IsIsoProjSet (chOps' (r := X.r) (R := KK X.O) LL j') T' e' → e * e' = e' * e)

def adm2 (_D : Formalism.BasicNotions.D7) (X : Inst) : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK X.O) V] [Module X.O V] [IsScalarTower X.O (KK X.O) V]
    (E : GLOps (n + 1) (KK X.O) V) (lam : Fin (n + 1) → ℤ) (v : V),
    n + 1 ≤ X.r → FiniteDimensional (KK X.O) V → IsIrrHW E lam v → ellWt lam ≤ 8 * X.L.a →
    (∀ x ∈ Nabla (O := X.O) E lam v, ((X.p : KK X.O) ^ ⌈kappaOneExponent X.p X.L.a X.r⌉₊) • x ∈ Delta (O := X.O) E v) ∧
    ∀ M : Submodule X.O V, UZLattice (O := X.O) E M → v ∈ M →
      (∀ x ∈ M, x ∈ weightSp E lam → ∃ c : X.O, x = c • v) →
      Delta (O := X.O) E v ≤ M ∧ (M : Set V) ⊆ Nabla (O := X.O) E lam v

def adm3 (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) (X : Inst) : Prop :=
  HI C0 CYb Cde Ck CD Cb Cc X → ∀ LL, X.BlockLetters C0 CE1 CE2 LL → ∀ j ≤ 2 * X.s + 1, ∀ la : Fin X.r → ℤ,
    Dominant (fun a : Fin (X.r - 1) => la (Fin.castLE (Nat.sub_le X.r 1) a)) →
    ∃ P : Module.End (KK X.O) (MvPolynomial (Fin (2 * X.s + 1) × Fin X.r) (KK X.O)),
      P * P = P ∧
      LinearMap.range P = weightSp (chOps (r := X.r) (R := KK X.O) LL j) la ⊓
        ⨅ (a : Fin (X.r - 1)) (b : Fin (X.r - 1)) (_ : a < b), LinearMap.ker (chOps' (r := X.r) (R := KK X.O) LL j a b) ∧
      LinearMap.ker P ⊓ weightSp (chOps (r := X.r) (R := KK X.O) LL j) la =
        (⨆ (a : Fin (X.r - 1)) (b : Fin (X.r - 1)) (_ : b < a), LinearMap.range (chOps' (r := X.r) (R := KK X.O) LL j a b)) ⊓
          weightSp (chOps (r := X.r) (R := KK X.O) LL j) la ∧
      (∀ F ∈ weightSp (chOps (r := X.r) (R := KK X.O) LL j) la, ∀ G ∈ weightSp (chOps (r := X.r) (R := KK X.O) LL j) la,
        fock (P F) G = fock F (P G)) ∧
      ∀ F ∈ chPol (KK X.O) X.r LL, F ∈ IntPol X.O (Fin (2 * X.s + 1) × Fin X.r) →
        F ∈ weightSp (chOps (r := X.r) (R := KK X.O) LL j) la →
        ((X.p : KK X.O) ^ ⌈kappaOneExponent X.p X.L.a X.r⌉₊) • P F ∈ IntPol X.O (Fin (2 * X.s + 1) × Fin X.r)

noncomputable def g0r (R : Type) [CommRing R] (r : ℕ) : Formalism.MainNotions.G.GLCoord R (r + 1) :=
  algebraMap (MvPolynomial (Fin (r + 1) × Fin (r + 1)) R) (Formalism.MainNotions.G.GLCoord R (r + 1))
    (MvPolynomial.X (0, Fin.last r))

def chiB {A : Type} [CommRing A] {r : ℕ} (c : ℤ) (ka : Fin r → ℤ) (u : Fin (r + 1) → Aˣ) : Aˣ :=
  u 0 ^ c * ∏ i : Fin r, u i.succ ^ ka i

noncomputable def evalG {R : Type} [CommRing R] {n : ℕ} {A : Type} [CommRing A] [Algebra R A]
    (g : Matrix (Fin n) (Fin n) A)
    (hg : IsUnit (MvPolynomial.aeval (fun x : Fin n × Fin n => g x.1 x.2) (Formalism.MainNotions.G.genMat R n).det)) :
    Formalism.MainNotions.G.GLCoord R n →+* A :=
  IsLocalization.Away.lift (Formalism.MainNotions.G.genMat R n).det (g := (MvPolynomial.aeval (fun x : Fin n × Fin n => g x.1 x.2) :
    MvPolynomial (Fin n × Fin n) R →ₐ[R] A).toRingHom) hg

def HB (R : Type) [CommRing R] (r : ℕ) (c : ℤ) (ka : Fin r → ℤ) : Set (Formalism.MainNotions.G.GLCoord R (r + 1)) :=
  {f | ∀ (A : Type) [CommRing A] [Algebra R A] (b g : Matrix (Fin (r + 1)) (Fin (r + 1)) A)
      (u : Fin (r + 1) → Aˣ)
      (hg : IsUnit (MvPolynomial.aeval (fun x : Fin (r + 1) × Fin (r + 1) => g x.1 x.2)
        (Formalism.MainNotions.G.genMat R (r + 1)).det))
      (hbg : IsUnit (MvPolynomial.aeval (fun x : Fin (r + 1) × Fin (r + 1) => (b * g) x.1 x.2)
        (Formalism.MainNotions.G.genMat R (r + 1)).det)),
      (∀ i j, i < j → b i j = 0) → (∀ i, b i i = u i) →
      evalG (R := R) (b * g) hbg f = (chiB c ka u : A) * evalG (R := R) g hg f}

def ArchimedeanSignatureMatching (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r : ℕ) (c : ℤ) (ka : Fin r → ℤ)
    (f : Formalism.MainNotions.G.GLCoord O (r + 1)), 1 ≤ r → f ∈ HB O r c ka → g0r O r ∣ f →
    ∃ f₁ ∈ HB O r (c - 1) ka, f = g0r O r * f₁

def adm5 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r : ℕ) (c : ℤ) (ka : Fin r → ℤ)
    (f h : Formalism.MainNotions.G.GLCoord O (r + 1)) (a : O), 1 ≤ r → f ∈ HB O r c ka → a ≠ 0 →
    g0r O r ∣ f - algebraMap O _ a * h → ∃ f' ∈ HB O r c ka, g0r O r ∣ h - f'

def adm6 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (r : ℕ) (c : ℤ) (ka : Fin r → ℤ) (h1 : 1 ≤ r), ka ⟨0, by omega⟩ ≤ c →
    Module.finrank K (Submodule.span K
        ((Ideal.Quotient.mk (Ideal.span {g0r K r})) '' HB K r c ka)) +
        Module.finrank K (Submodule.span K (HB K r (c - 1) ka)) =
      Module.finrank K (Submodule.span K (HB K r c ka)) ∧
    Module.finrank K (Submodule.span K
        ((Ideal.Quotient.mk (Ideal.span {g0r K r})) '' HB K r c ka)) =
      ∑ ka' ∈ Fintype.piFinset (fun i : Fin (r - 1) => Finset.Icc (ka ⟨i + 1, by omega⟩) (ka ⟨i, by omega⟩)),
        Module.finrank K (Submodule.span K (HB K (r - 1) c ka'))

noncomputable def resMat (O : Type) [CommRing O] (r : ℕ) :
    Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) (MvPolynomial (Fin (r + 1)) (Formalism.MainNotions.G.GLCoord O (r + 1))) :=
  fun i j =>
    Fin.cases (motive := fun _ => MvPolynomial (Fin (r + 1)) (Formalism.MainNotions.G.GLCoord O (r + 1)))
      (Fin.cases (motive := fun _ => MvPolynomial (Fin (r + 1)) (Formalism.MainNotions.G.GLCoord O (r + 1))) 1
        (fun j' => MvPolynomial.X j') j)
      (fun i' => Fin.cases (motive := fun _ => MvPolynomial (Fin (r + 1)) (Formalism.MainNotions.G.GLCoord O (r + 1))) 0
        (fun j' => MvPolynomial.C (algebraMap (MvPolynomial (Fin (r + 1) × Fin (r + 1)) O) _
          (MvPolynomial.X (i', j')))) j) i

def adm7 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r : ℕ) (c : ℤ) (ka : Fin (r + 1) → ℤ),
    IsUnit (MvPolynomial.aeval (fun x : Fin (r + 1 + 1) × Fin (r + 1 + 1) => resMat O r x.1 x.2)
      (Formalism.MainNotions.G.genMat O (r + 1 + 1)).det) ∧
    ∀ hM : IsUnit (MvPolynomial.aeval (fun x : Fin (r + 1 + 1) × Fin (r + 1 + 1) => resMat O r x.1 x.2)
      (Formalism.MainNotions.G.genMat O (r + 1 + 1)).det),
      (∀ f ∈ HB O (r + 1) c ka, ∀ f' ∈ HB O (r + 1) c ka,
        evalG (R := O) (resMat O r) hM f = evalG (R := O) (resMat O r) hM f' → f = f') ∧
      (∀ f ∈ HB O (r + 1) c ka, ∀ m,
        (evalG (R := O) (resMat O r) hM f).coeff m ∈ HB O r (ka 0) (fun i => ka i.succ)) ∧
      (∀ f ∈ HB O (r + 1) c ka, ∀ (a : O) (F : MvPolynomial (Fin (r + 1)) (Formalism.MainNotions.G.GLCoord O (r + 1))), a ≠ 0 →
        (∀ m, F.coeff m ∈ HB O r (ka 0) (fun i => ka i.succ)) →
        evalG (R := O) (resMat O r) hM f = algebraMap O _ a * F →
        ∃ f' ∈ HB O (r + 1) c ka, evalG (R := O) (resMat O r) hM f' = F) ∧
      (∀ f ∈ HB O (r + 1) c ka, ∀ e : ℕ,
        g0r O (r + 1) ^ e ∣ f ↔ MvPolynomial.X (Fin.last r) ^ e ∣ evalG (R := O) (resMat O r) hM f)

def adm8 (_D : Formalism.BasicNotions.D7) (X : Inst) : Prop :=
  ∀ (N : ℕ) (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (hJ : ∀ k, J k ≤ N),
    YjtZ X.O (r := X.r) LL J M =
      Submodule.span X.O {F | ∃ (P : PPath X.r N (⟨LL.vec⟩ : Letters (Fin N)) LL.deg) (I : ℤ → Finset (Fin X.r)),
        (∀ k, ((P.mu ⟨J k, by have := hJ k; omega⟩ ⟨0, Nat.pos_of_ne_zero X.hm⟩ : ℤ) : WithTop ℤ) ≤ M k) ∧
        IsSt P.mu I ∧ F = Psi (KK X.O) P.mu I}

def adm9 (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs : ℝ) (X : Inst) : Prop :=
  HI C0 CYb Cde Ck CD Cb Cc X → ∀ aT' : Fin X.L.n' → ℕ, X.InWinA aT' → ∀ m : ℝ, 0 ≤ m →
    (1 - kappaMarginBound Ckap X.L.N X.L.k X.L.Q m X.L.N1 X.L.b' X.L.Y (X.L.E0 C0 CE1 CE2) X.L.a (X.L.La C0)) *
        (dimHH (m := X.L.m) X.Kf X.L.TT aT' X.L.bT : ℝ) ≤
      gaussianNumber (X.L.p ^ X.L.n') (X.L.m + 1) *
        ∏ j, (segRank X.O X.L.p X.L.m (X.L.seg C0 CE1 CE2 j) (segATop X.L.TT aT' j) (segAPlus X.L.TT aT' j) m : ℝ) ∧
    (m ≤ X.L.b' / (X.L.k * X.L.Q * X.L.Y) →
      kappaMarginBound Ckap X.L.N X.L.k X.L.Q m X.L.N1 X.L.b' X.L.Y (X.L.E0 C0 CE1 CE2) X.L.a (X.L.La C0) ≤
        Cs * X.L.N * X.L.N1 / X.L.Y)

def adm10 (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) (X : Inst) : Prop :=
  HI C0 CYb Cde Ck CD Cb Cc X → ∀ aT' : Fin X.L.n' → ℕ, X.InWinA aT' →
    ∀ (j : Fin (numSeg X.L.TT)) (rz ry : Fin (segS X.L.TT j) → Fin (X.L.m + 1) → ℕ),
      DigitsOK X.L.p (X.L.seg C0 CE1 CE2 j) (segATop X.L.TT aT' j) (Formalism.MainNotions.ColumnSystems.digitBlock rz ry) →
      Formalism.MainNotions.ColumnSystems.rankOnDigits X.O C0 CE1 CE2 (X.LA aT') j 0 rz ry ≤
        Formalism.MainNotions.ColumnSystems.dimMM (X.L.m + 1) ((X.L.seg C0 CE1 CE2 j).A0 X.L.p)
                  (fun i => coarseA X.L.p (X.L.seg C0 CE1 CE2 j) (Formalism.MainNotions.ColumnSystems.digitBlock rz ry) i)
                  (fun i => coarseC X.L.p (X.L.seg C0 CE1 CE2 j) (segATop X.L.TT aT' j) (Formalism.MainNotions.ColumnSystems.digitBlock rz ry) i) *
          Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) ((X.L.seg C0 CE1 CE2 j).bPlus : ℤ)

def adm11 (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) (X : Inst) : Prop :=
  HI C0 CYb Cde Ck CD Cb Cc X → ∀ aT' : Fin X.L.n' → ℕ, X.InWinA aT' →
    ∀ m : ℝ, 0 ≤ m → m ≤ X.L.b' / (X.L.k * X.L.Q * X.L.Y) →
    ∀ rz ry : Fin (segS X.L.TT X.j) → Fin (X.L.m + 1) → ℕ,
      DigitsOK X.L.p (X.S C0 CE1 CE2) (segATop X.L.TT aT' X.j) (Formalism.MainNotions.ColumnSystems.digitBlock rz ry) →
      ((Formalism.MainNotions.ColumnSystems.dimMM (X.L.m + 1) ((X.S C0 CE1 CE2).A0 X.L.p)
                  (fun i => coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock rz ry) i)
                  (fun i => coarseC X.L.p (X.S C0 CE1 CE2) (segATop X.L.TT aT' X.j) (Formalism.MainNotions.ColumnSystems.digitBlock rz ry) i) *
          Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) ((X.S C0 CE1 CE2).bPlus : ℤ) : ℕ) : ℝ) / 2 ≤
        (Formalism.MainNotions.ColumnSystems.rankOnDigits X.O C0 CE1 CE2 (X.LA aT') X.j m rz ry : ℝ) ∧
      Formalism.MainNotions.ColumnSystems.rankOnDigits X.O C0 CE1 CE2 (X.LA aT') X.j m rz ry ≤
        Formalism.MainNotions.ColumnSystems.dimMM (X.L.m + 1) ((X.S C0 CE1 CE2).A0 X.L.p)
                  (fun i => coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock rz ry) i)
                  (fun i => coarseC X.L.p (X.S C0 CE1 CE2) (segATop X.L.TT aT' X.j) (Formalism.MainNotions.ColumnSystems.digitBlock rz ry) i) *
          Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) ((X.S C0 CE1 CE2).bPlus : ℤ)

def admitted (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs : ℝ) (X : Inst) : Prop :=
  adm1 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X ∧ adm2 D X ∧ adm3 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧
    adm6 D ∧ adm7 D ∧ adm8 D X ∧ adm9 D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X ∧
    adm10 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X ∧ adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X

def Conclusion1 (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc C : ℝ) (X : Inst) : Prop :=
  HI C0 CYb Cde Ck CD Cb Cc X →
    meanKapT C0 CE1 CE2 X (depthD C X.p X.L.a X.Nt X.N₁ X.r X.L.Y) ≤
      C * (((X.S C0 CE1 CE2).t : ℝ) + 1) * X.N₁ / X.L.Y

def IntegralityFromMetric (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C : ℝ) : Prop :=
  ∀ X : Inst, admitted D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → Conclusion1 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X

def TransportedAlt (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ Cc : ℝ, 0 ≤ Cc → ∃ T0 : ℝ, 0 < T0 ∧ ∀ C0 : ℝ, T0 ≤ C0 →
    ∃ T1 : ℝ, 0 < T1 ∧ ∀ CE1 CE2 : ℝ, T1 ≤ CE1 → T1 ≤ CE2 →
      ∃ T2 : ℝ, 0 < T2 ∧ ∀ CYb Cde Ck CD Cb : ℝ, T2 ≤ CYb → T2 ≤ Cde → T2 ≤ Ck → T2 ≤ CD → T2 ≤ Cb →
        P C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def LocalLiftingAinfEtale (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∃ C : ℝ, 0 < C ∧ ∀ X : Inst, Conclusion1 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X

def IntegralityFromMetricForLargeConstants (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs : ℝ, ∃ C : ℝ, 0 < C ∧
    IntegralityFromMetric D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C

open Classical in

def DegreeDichotomy (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (n del₀ h : ℕ) (E : ℝ) (c : Fin n → Fin n → ℕ → K) (lead : K) (roots : Multiset K) (t₀ d : ℤ) (Y₀ : ℕ)
    (La₀ : ℝ) (U V : ℤ → Matrix (Fin n) (Fin n) K) (dg : ℤ → Fin n → K),
    IsCoprime d (p : ℤ) → 0 < Y₀ → Y₀ ≤ p ^ h → del₀ + 1 ≤ p ^ h → 1 ≤ E → lead ≠ 0 →
    (∀ i j k, ‖c i j k‖ ≤ 1) →
    (Formalism.GM.binMatK K del₀ c).det = Polynomial.C lead * (roots.map (fun ζ => Polynomial.X - Polynomial.C ζ)).prod →
    (∀ j ∈ Finset.range Y₀, (∀ a b, ‖U (Formalism.GM.progr t₀ d j) a b‖ ≤ 1) ∧ (∀ a b, ‖V (Formalism.GM.progr t₀ d j) a b‖ ≤ 1) ∧
      ‖(U (Formalism.GM.progr t₀ d j)).det‖ = 1 ∧ ‖(V (Formalism.GM.progr t₀ d j)).det‖ = 1 ∧
      (Formalism.GM.binMatK K del₀ c).map (Polynomial.eval ((Formalism.GM.progr t₀ d j : ℤ) : K)) =
        U (Formalism.GM.progr t₀ d j) * Matrix.diagonal (dg (Formalism.GM.progr t₀ d j)) * V (Formalism.GM.progr t₀ d j)) →
    -Real.logb p ‖lead‖ + (roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) * La₀ →
    (∑ j ∈ Finset.range Y₀,
        ((Finset.univ.filter (fun i => ‖dg (Formalism.GM.progr t₀ d j) i‖ ≤ (p : ℝ) ^ (-E))).card : ℝ)) / (Y₀ : ℝ) ≤
      (n : ℝ) * ((del₀ : ℝ) / Y₀ + (La₀ + (del₀ : ℝ) * h / Y₀) / E)

def lgR (p : ℕ) (a : ℝ) (r : ℕ) : ℝ := Real.logb p (8 * a + r) + 1

structure InstM where
  p : ℕ
  hp : p.Prime
  s : ℕ
  r : ℕ
  hr : r ≠ 0
  LL : Formalism.GM.M.Letters (2 * s + 1)
  T : Formalism.GM.M.TieData
  a : ℝ
  E : ℝ
  Yl : Fin T.t → ℕ
  n₀ : Fin T.t → ℕ
  dd : Fin T.t → ℕ
  ρ : Fin r

instance InstM.fact (X : InstM) : Fact X.p.Prime := ⟨X.hp⟩
instance InstM.neZeroR (X : InstM) : NeZero X.r := ⟨X.hr⟩

def InstM.lg (X : InstM) : ℝ := lgR X.p X.a X.r

def InstM.κ₁ (X : InstM) : ℝ := (X.r : ℝ) ^ 2 * X.lg

def InstM.κ (X : InstM) : ℝ := 3 * ((X.s : ℝ) + 2) * (X.r : ℝ) ^ 2 * X.lg

def InstM.prog (X : InstM) : Finset (Fin X.T.t → ℕ) :=
  Fintype.piFinset (fun i => (Finset.range (X.Yl i)).image (fun j => X.n₀ i + X.dd i * j))

def InstM.top (X : InstM) : Fin X.T.t → ℕ := fun i => X.n₀ i + X.dd i * (X.Yl i - 1)

def InstM.LLt (X : InstM) : Formalism.GM.M.Letters (2 * X.s + 1) := X.LL.setTies X.T X.top

def InstM.degAt (X : InstM) (j : ℕ) : ℕ := if h : j < 2 * X.s + 1 then X.LLt.deg ⟨j, h⟩ else 0

def InstM.Si (X : InstM) (i : Fin X.T.t) : ℕ := X.T.S X.LLt i

def InstM.Chain (X : InstM) : Prop := ∀ x, X.LL.vec x = decide ((x : ℕ) % 2 = 0)

def InstM.Conds (X : InstM) : Prop := ∀ k, X.T.J k = 2 * X.s + 1 ∨ ∃ i, X.T.J k = X.T.pos i + 1

def InstM.Size (X : InstM) : Prop :=
  (X.LLt.total : ℝ) ≤ 8 * X.a + X.r ∧
  ∀ i, ((X.degAt (X.T.pos i) + X.degAt (X.T.pos i + 1) + X.r + X.T.z i + 1 : ℕ) : ℝ) ≤ 8 * X.a + X.r ∧
    (X.Yl i : ℝ) ≤ 8 * X.a + X.r ∧ ((2 * X.Si i + 1 : ℕ) : ℝ) ≤ 8 * X.a + X.r

def InstM.eps (X : InstM) (i : Fin X.T.t) : ℝ :=
  2 * (X.Si i : ℝ) / X.Yl i + (2 * X.κ + 2 * (X.Si i : ℝ) * X.lg / X.Yl i) / X.E

def InstM.D1 (X : InstM) : ℝ := (X.T.t : ℝ) * (X.E + X.κ) + X.κ

def InstM.Hyp (X : InstM) : Prop :=
  X.p ≠ 2 ∧ 2 ≤ X.r ∧ (X.ρ : ℕ) = X.r - 1 ∧ X.T.Admissible X.LL ∧ X.Chain ∧ X.Conds ∧
  1 ≤ X.a ∧ 1 ≤ X.E ∧ (∀ i, 1 ≤ X.Yl i ∧ 0 < X.dd i ∧ IsCoprime (X.dd i : ℤ) X.p) ∧
  (∀ i, X.Si i ≤ X.n₀ i) ∧ X.Size

def PolynomialHypothesis (_D : Formalism.BasicNotions.D7) (X : InstM) : Prop :=
  X.Hyp → ∀ n ∈ X.prog, Formalism.GM.M.HypP X.p (X.LL.setTies X.T n) X.ρ ⌊X.κ₁⌋₊

def WeightHypothesis (_D : Formalism.BasicNotions.D7) (X : InstM) : Prop :=
  X.Hyp → ∀ n ∈ X.prog, Formalism.GM.M.HypW X.p (r := X.r) (X.LL.setTies X.T n) ⌊X.κ₁⌋₊

def EvenHypothesis (_D : Formalism.BasicNotions.D7) (X : InstM) : Prop :=
  X.Hyp → ∀ n ∈ X.prog, Formalism.GM.M.HypE X.p (X.LL.setTies X.T n) X.ρ ⌊X.κ₁⌋₊

def AdmAlt (D : Formalism.BasicNotions.D7) (X : InstM) : Prop :=
  PolynomialHypothesis D X ∧ WeightHypothesis D X ∧ EvenHypothesis D X ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D

def OrderBoundDigits (_D : Formalism.BasicNotions.D7) (X : InstM) : Prop :=
  X.Hyp → ∀ n ∈ X.prog, ∀ i,
    Formalism.GM.M.GramDeterminantGradedHypothesis X.p ((X.LL.setTies X.T n).takeD (X.T.pos i + 1)) X.T.J (X.T.thrUpTo i) X.ρ
      (((X.s : ℝ) + 4) * X.κ₁)

def ModelLatticeRank (_D : Formalism.BasicNotions.D7) (X : InstM) : Prop :=
  X.Hyp →
    (∑ n ∈ X.prog,
        (Formalism.GM.M.bad X.p (fun F G => Formalism.GM.M.fockN X.p (X.LL.setTies X.T n) (X.T.phis X.p (X.LL.setTies X.T n) F) G)
          (Formalism.GM.M.YZ X.p (r := X.r) (X.LL.setTies X.T n) X.T.J X.T.thr) ⌊X.D1⌋ : ℝ)) / X.prog.card ≤
      ∑ i, X.eps i *
        ((∑ n ∈ X.prog,
            (Module.finrank ℚ_[X.p]
              (Formalism.GM.M.Y X.p (r := X.r) (X.LL.setTies X.T (Function.update n i (X.top i))) X.T.J X.T.thr) : ℝ)) /
          X.prog.card)

def DegreeDichotomyWithModelBounds (D : Formalism.BasicNotions.D7) : Prop :=
  DegreeDichotomy D ∧ ∀ X : InstM, AdmAlt D X → OrderBoundDigits D X ∧ ModelLatticeRank D X

def DichotomyAndModelBounds (D : Formalism.BasicNotions.D7) : Prop := DegreeDichotomyWithModelBounds D

def Conclusion1Family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc C : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x) (X : Inst), Conclusion1 (Fm.D x i) C0 CYb Cde Ck CD Cb CE1 CE2 Cc C X

def FamilyGlobalDerivation {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), IntegralityFromMetric (Fm.D x i) C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C

def IntegralityFromMetricUniformOverFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs : ℝ, ∃ C : ℝ, 0 < C ∧
    FamilyGlobalDerivation Fm C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C

def IntegralityFromMetricUniformInEpsilon (Fm : Formalism.MainNotions.DFamP) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs : ℝ, ∃ C : ℝ, 0 < C ∧
    ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), FamilyGlobalDerivation (Fm ε h0 h1) C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs C

def ModelLatticeRankFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ x (i : Fm.Ix x) (X : InstM), ModelLatticeRank (Fm.D x i) X

def DegreeDichotomyWithModelBoundsFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ x (i : Fm.Ix x), DegreeDichotomyWithModelBounds (Fm.D x i)

def DichotomyAndModelBoundsFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := DegreeDichotomyWithModelBoundsFamily Fm

end Formalism.MainNotions.flipOneThree

end
