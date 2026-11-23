import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.GammaSemisimpleLocalOfConsequences
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LagrangeIdealLifts.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

noncomputable section

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def JSet (jumps : Finset ℤ) (M : ℕ) : Finset ℤ :=
  ((jumps ×ˢ Finset.Icc (1 : ℤ) M).image (fun p : ℤ × ℤ => p.1 + p.2)).filter (fun j => j ≠ 0) ∪
    Finset.Icc (1 : ℤ) M

def eWA (l H : ℕ) : ℕ :=
  ⌊(H : ℝ) * l / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l ((H : ℝ) + 1)⌋₊

def eWB (l s H : ℕ) : ℕ := 2 * H * s + padicValNat l (2 * H).factorial

def aA (l M : ℕ) : ℕ := M / (l - 1) + 1

def eUA (l M : ℕ) (J : Finset ℤ) : ℕ :=
  (∑ j ∈ J, padicValInt l j) + aA l M + padicValNat l (aA l M).factorial

def ePA (l M H : ℕ) (jumps : Finset ℤ) : ℕ := 2 * eWA l H + eUA l M (JSet jumps M)

def ePB (l s M H : ℕ) (jumps : Finset ℤ) : ℕ :=
  2 * eWB l s H + Formalism.LIFT.eU l M s (JSet jumps M)

def cH (l H : ℕ) : ℕ := ⌈1 + Real.logb l ((H : ℝ) + 1)⌉₊

def Hmax (n : ℕ) (Mi hi : ZMod n → ℕ) : ℕ := (Finset.range n).sup fun k => Mi k + hi k

def Mmax (n : ℕ) (Mi : ZMod n → ℕ) : ℕ := (Finset.range n).sup fun k => Mi k

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def lp (_W : LocWach PD LL O v n) (k : ℕ) : LetA O n := ((PD.p : ℕ) : LetA O n) ^ k

def Over (W : LocWach PD LL O v n) (τ : K →ₐ[Qp] LL) (i : ZMod n) : Prop :=
  τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i

def JumpsLet (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ) : Prop :=
  ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Over W τ i →
    JumpsInV PD T.ρ τ (Set.Icc (-(Mi i : ℤ)) (hi i))

def jumpSet (_W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (M h : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc (-(M : ℤ)) h).filter fun a => ∃ τ : K →ₐ[Qp] LL, IsJumpV PD T.ρ τ a

def Sur (_W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) : Prop :=
  IsCrys PD T₁.ρ ∧ IsCrys PD T₂.ρ ∧ F.Onto

def CaseA (W : LocWach PD LL O v n) : Prop :=
  Function.Bijective (algebraMap K₀ K) ∧ W.s = 1 ∧ PD.p ≠ 2

def CaseB (W : LocWach PD LL O v n) : Prop :=
  W.GKs = ⊤ ∧ Module.finrank K₀ K = (PD.p - 1) * PD.p ^ (W.s - 1)

def IntermediateUnramifiedOdd (W : LocWach PD LL O v n) (e : ℕ) : Prop :=
  W.s = 1 ∧ PD.p ≠ 2 ∧ Module.finrank K₀ K = e

def Nimg (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (i : ZMod n) : Submodule (LetA O n) (W.DD T₂) :=
  (W.Nl T₁ i).map ((W.map F).restrictScalars (LetA O n))

def Kills (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (i : ZMod n) (a : LetA O n) : Prop :=
  ∀ y ∈ W.Nl T₂ i, a • y ∈ Nimg W F i

def KillsΔ (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (i : ZMod n) (a : LetA O n) : Prop :=
  ∀ y ∈ W.Nl T₂ i, (∀ δ ∈ W.DelF, W.γD T₂ δ y = y) → a • y ∈ Nimg W F i

def sI (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (i : ZMod n) : ℕ := sInf {k : ℕ | Kills W F i (letπ ^ k)}

def AI (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (i : ZMod n) : ℕ := ⌈(sI W F i : ℝ) / ((PD.p : ℝ) - 1)⌉₊

def rI (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (i : ZMod n) : ℕ := sInf {r : ℕ | KillsΔ W F i (lp W r)}

def coreWX (W : LocWach PD LL O v n) : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ),
    Sur W F → JumpsLet W T₁ Mi hi → ∀ i, Kills W F i (W.X ^ Hmax n Mi hi)

def coreWB (W : LocWach PD LL O v n) : Prop :=
  CaseB W → ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ),
    Sur W F → JumpsLet W T₁ Mi hi → ∀ i, Kills W F i (lp W (eWB PD.p W.s (Hmax n Mi hi)))

def coreWA (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ),
    Sur W F → JumpsLet W T₁ Mi hi → ∀ i, Kills W F i (lp W (eWA PD.p (Hmax n Mi hi)))

def coreWK1 (W : LocWach PD LL O v n) : Prop :=
  ∀ e : ℕ, IntermediateUnramifiedOdd W e → ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ),
    Sur W F → JumpsLet W T₁ Mi hi → ∀ i,
      (∀ π' u : LetA O n, IsUnit u → π' = u * letπ ^ ((PD.p - 1) / e) →
        KillsΔ W F i (π' ^ ⌈((e * Hmax n Mi hi : ℕ) : ℝ) / ((PD.p : ℝ) - 1)⌉₊)) ∧
      Kills W F i (lp W (2 * ⌈((e * Hmax n Mi hi : ℕ) : ℝ) / ((PD.p : ℝ) - 1)⌉₊ +
        padicValNat PD.p (2 * ⌈((e * Hmax n Mi hi : ℕ) : ℝ) / ((PD.p : ℝ) - 1)⌉₊).factorial))

def WachQuotientAnnihilator (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ),
    Sur W F → JumpsLet W T₁ Mi hi → ∀ (i : ZMod n) (a j : ℕ),
      ((sI W F i : ℝ) - j) * PD.p / ((PD.p : ℝ) - 1) ^ 2 + cH PD.p (Hmax n Mi hi) ≤ a →
        Kills W F i (lp W a * letπ ^ j)

def WachExponentRecursion (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ),
    Sur W F → JumpsLet W T₁ Mi hi → ∀ i : ZMod n,
      (sI W F (i - 1) : ℝ) ≤ ((Mi i + hi i : ℕ) : ℝ) + cH PD.p (Hmax n Mi hi) + 3 +
        (sI W F i : ℝ) / ((PD.p : ℝ) - 1)

def coreWR (W : LocWach PD LL O v n) (C : ℝ) : Prop :=
  CaseA W → ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ),
    Sur W F → JumpsLet W T₁ Mi hi → ∀ i : ZMod n,
      ((sI W F i : ℝ) ≤ ∑' a : ℕ, (((Mi (i + ((a + 1 : ℕ) : ZMod n)) +
          hi (i + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ) + cH PD.p (Hmax n Mi hi) + 3) *
          ((PD.p : ℝ) - 1) ^ (-(a : ℤ))) ∧
      KillsΔ W F i (W.π₀ ^ AI W F i) ∧
      ((rI W F i : ℝ) ≤ (sI W F i : ℝ) * PD.p / ((PD.p : ℝ) - 1) ^ 2 + cH PD.p (Hmax n Mi hi)) ∧
      KillsΔ W F i (lp W (rI W F i)) ∧
      KillsΔ W F i ((W.π₀ + ((PD.p : ℕ) : LetA O n)) ^ (AI W F i + rI W F i)) ∧
      ((AI W F i : ℝ) ≤ (Hmax n Mi hi : ℝ) / ((PD.p : ℝ) - 1) + 1) ∧
      ((AI W F i + rI W F i : ℕ) : ℝ) ≤
        (Hmax n Mi hi : ℝ) * (2 * PD.p - 1) / ((PD.p : ℝ) - 1) ^ 2 + cH PD.p (Hmax n Mi hi) + 1 ∧
      (PD.p = 5 → ((AI W F i + rI W F i : ℕ) : ℝ) ≤
        0.57 * (Hmax n Mi hi : ℝ) + cH PD.p (Hmax n Mi hi) + 1) ∧
      (PD.p = 7 → ((AI W F i + rI W F i : ℕ) : ℝ) ≤
        0.37 * (Hmax n Mi hi : ℝ) + cH PD.p (Hmax n Mi hi) + 1) ∧
      (PD.p = 11 → ((AI W F i + rI W F i : ℕ) : ℝ) ≤
        0.21 * (Hmax n Mi hi : ℝ) + cH PD.p (Hmax n Mi hi) + 1) ∧
      ∀ (j : ℕ) (Gc : ℝ), 0 ≤ Gc → (∀ a : ℕ, 1 ≤ a → a ≤ j →
          ((Mi (i + (a : ZMod n)) + hi (i + (a : ZMod n)) : ℕ) : ℝ) ≤ 2 * Gc) →
        (rI W F i : ℝ) ≤ C * (Gc / PD.p + (Hmax n Mi hi : ℝ) / ((PD.p : ℝ) - 1) ^ (j + 1) +
          (1 + Real.log ((Hmax n Mi hi : ℝ) + 1)))

def coreWS (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ),
    Sur W F → JumpsLet W T₁ Mi hi → ∀ i : ZMod n,
      sI W F i ≤ Hmax n Mi hi ∧
      ∀ (j : ℕ) (Gc : ℝ), 0 ≤ Gc → (∀ a : ℕ, 1 ≤ a → a ≤ j →
          ((Mi (i + (a : ZMod n)) + hi (i + (a : ZMod n)) : ℕ) : ℝ) ≤ 2 * Gc) →
        (sI W F i : ℝ) ≤ (2 * Gc + cH PD.p (Hmax n Mi hi) + 3) * ((PD.p : ℝ) - 1) / ((PD.p : ℝ) - 2) +
          (Hmax n Mi hi : ℝ) / ((PD.p : ℝ) - 1) ^ j

theorem ws_step (b q x x' y w : ℝ) (j : ℕ) (hq : 2 ≤ q) (h1 : x ≤ w + x' / q) (hw : w ≤ b)
    (h2 : x' ≤ b * q / (q - 1) + y / q ^ j) : x ≤ b * q / (q - 1) + y / q ^ (j + 1) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have h3 : x' / q ≤ (b * q / (q - 1) + y / q ^ j) / q := div_le_div_of_nonneg_right h2 hq0.le
  have h4 : (b * q / (q - 1) + y / q ^ j) / q = b / (q - 1) + y / q ^ (j + 1) := by
    field_simp
    ring
  have h5 : b + b / (q - 1) = b * q / (q - 1) := by
    field_simp
    ring
  linarith

theorem coreWS_of (W : LocWach PD LL O v n) (hX : coreWX W) (h2 : WachExponentRecursion W) : coreWS W := by
  intro hA T₁ T₂ F Mi hi hS hJ
  have hH : ∀ i : ZMod n, sI W F i ≤ Hmax n Mi hi := by
    intro i
    apply Nat.sInf_le
    have h := hX T₁ T₂ F Mi hi hS hJ i
    have hXπ : W.X = letπ := by simp [LocWach.X, hA.2.1]
    rwa [hXπ] at h
  intro i
  refine ⟨hH i, ?_⟩
  intro j Gc hG
  have hp3 : 3 ≤ PD.p := by
    have h1 := PD.hp.two_le
    have h2 := hA.2.2
    omega
  have hq : (2 : ℝ) ≤ (PD.p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (PD.p : ℝ) := by exact_mod_cast hp3
    linarith
  have hpq : (PD.p : ℝ) - 2 = ((PD.p : ℝ) - 1) - 1 := by ring
  rw [hpq]
  induction j generalizing i with
  | zero =>
    intro _
    have h1 : (sI W F i : ℝ) ≤ Hmax n Mi hi := by exact_mod_cast hH i
    have hc : (0 : ℝ) ≤ (cH PD.p (Hmax n Mi hi) : ℝ) := Nat.cast_nonneg _
    have h3 : 0 ≤ (2 * Gc + cH PD.p (Hmax n Mi hi) + 3) * ((PD.p : ℝ) - 1) / (((PD.p : ℝ) - 1) - 1) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    simp only [pow_zero, div_one]
    linarith
  | succ j ih =>
    intro hB
    have hw := h2 hA T₁ T₂ F Mi hi hS hJ (i + 1)
    rw [add_sub_cancel_right] at hw
    have hB1 := hB 1 le_rfl (by omega)
    rw [Nat.cast_one] at hB1
    have hi' := ih (i + 1) (fun a ha1 ha2 => by
      have h := hB (a + 1) (by omega) (by omega)
      have e : i + ((a + 1 : ℕ) : ZMod n) = i + 1 + (a : ZMod n) := by push_cast; ring
      rwa [e] at h)
    exact ws_step _ _ _ _ _ _ j hq hw (by linarith) hi'

def coreLiftA (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ),
    Sur W F → JumpsLet W T₁ Mi hi →
      F.LiftF PD (ePA PD.p (Mmax n Mi) (Hmax n Mi hi) (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)))

def coreLiftB (W : LocWach PD LL O v n) : Prop :=
  CaseB W → ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ),
    Sur W F → JumpsLet W T₁ Mi hi →
      F.LiftF PD (ePB PD.p W.s (Mmax n Mi) (Hmax n Mi hi) (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)))

def uγ (W : LocWach PD LL O v n) : Oˣ := W.χΓ W.gam

def coreLiftR (W : LocWach PD LL O v n) : Prop :=
  ∀ (T₁ : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T₁.ρ → JumpsLet W T₁ Mi hi →
    (CaseB W → ∃ k : ℕ, Associated
      (∏ j ∈ JSet (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) (Mmax n Mi),
        (1 - (((uγ W) ^ (-j) : Oˣ) : O))) (((PD.p : ℕ) : O) ^ k)) ∧
    (CaseA W → ∃ (w : Oˣ) (k : ℤ),
      (∏ j ∈ JSet (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) (Mmax n Mi),
        (-(algebraMap O LL (1 - (((uγ W) ^ (-j) : Oˣ) : O)) / (PD.p : LL)))) =
        algebraMap O LL (w : O) * (PD.p : LL) ^ k)

def coreLiftO (W : LocWach PD LL O v n) (CA CB CK : ℝ) : Prop :=
  ∀ (T₁ : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T₁.ρ → JumpsLet W T₁ Mi hi →
    (CaseA W → (ePA PD.p (Mmax n Mi) (Hmax n Mi hi) (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) : ℝ) ≤
      CA * (1 + (Hmax n Mi hi : ℝ) / PD.p + (1 + Real.logb PD.p ((Hmax n Mi hi : ℝ) + 1)))) ∧
    (CaseB W → (ePB PD.p W.s (Mmax n Mi) (Hmax n Mi hi)
        (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) : ℝ) ≤ CB * ((Hmax n Mi hi : ℝ) * W.s + 1)) ∧
    (CaseB W → W.s = 1 → (ePB PD.p W.s (Mmax n Mi) (Hmax n Mi hi)
        (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) : ℝ) ≤ CK * (Hmax n Mi hi : ℝ))

end Local

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Local2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def coreL (_W : LocWach PD LL O v n) : Prop :=
  ∀ (S₁ S₂ : Finset ℤ) (sg : ℕ) (c : ℤ → O), Disjoint S₁ S₂ →
    (∀ a ∈ S₁ ∪ S₂, ∀ b ∈ S₁ ∪ S₂, a ≠ b →
      v (algebraMap O LL (c a - c b)) = ((sg + padicValInt PD.p (a - b) : ℕ) : WithTop ℚ)) →
    ∀ E : ℕ, (∀ a ∈ S₁,
      v (algebraMap O LL ((∏ b ∈ S₂, (Polynomial.X - Polynomial.C (c b))).eval (c a))) +
        v (algebraMap O LL ((Polynomial.derivative
          (∏ b ∈ S₁, (Polynomial.X - Polynomial.C (c b)))).eval (c a))) ≤ (E : WithTop ℚ)) →
      Polynomial.C (((PD.p : ℕ) : O) ^ E) ∈
        Ideal.span ({∏ b ∈ S₁, (Polynomial.X - Polynomial.C (c b)),
          ∏ b ∈ S₂, (Polynomial.X - Polynomial.C (c b))} : Set (Polynomial O))

def u₁ (W : LocWach PD LL O v n) : O := ((uγ W : Oˣ) : O) ^ (PD.p - 1)

def InNΔi (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) : Prop :=
  x ∈ W.NΔ T ∧ x ∈ W.Nl T i

def IsFrameΔ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) {d : ℕ}
    (b : Fin d → W.DD T) : Prop :=
  (∀ m, InNΔi W T i (b m)) ∧ ∀ x, InNΔi W T i x → ∃! a : Fin d → LetA O n,
    (∀ m, a m ∈ W.AΔ ∧ letE i * a m = a m) ∧ x = ∑ m, a m • b m

def vecB (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T)
    (y : Fin d → O) : W.DD T := ∑ m, y m • b m

def IsSol (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) {d : ℕ}
    (b : Fin d → W.DD T) (z : W.DD T) (c : ℕ → Fin d → LL) : Prop :=
  ∀ (R k : ℕ) (y : ℕ → Fin d → O),
    (∀ r < R, ∀ m, algebraMap O LL (y r m) = (PD.p : LL) ^ k * c r m) →
    ∃ x, InNΔi W T i x ∧
      W.γ T (∑ r ∈ Finset.range R, W.π₀ ^ r • vecB W T b (y r)) -
        (∑ r ∈ Finset.range R, W.π₀ ^ r • vecB W T b (y r)) - ((PD.p : ℕ) : O) ^ k • z =
        W.π₀ ^ R • x

def Bd (_W : LocWach PD LL O v n) (r : ℕ) (x : LL) : Prop :=
  (((-(((r + padicValNat PD.p r.factorial : ℕ) : ℚ)) : ℚ)) : WithTop ℚ) ≤ v x

def coreH (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ i : ZMod n,
    (∀ (r : ℕ) (x : W.DD T), InNΔi W T i x → ∃ x', InNΔi W T i x' ∧
      W.γ T (W.π₀ ^ r • x) - W.π₀ ^ r • x = (u₁ W ^ r - 1) • (W.π₀ ^ r • x) + W.π₀ ^ (r + 1) • x') ∧
    (∀ r : ℕ, 1 ≤ r →
      v (algebraMap O LL (u₁ W ^ r - 1)) = ((1 + padicValNat PD.p r : ℕ) : WithTop ℚ)) ∧
    (∀ (d : ℕ) (b : Fin d → W.DD T), IsFrameΔ W T i b →
      ∀ z : W.DD T, (∃ z', InNΔi W T i z' ∧ z = W.π₀ • z') → ∀ c₀ : Fin d → O,
        (∃ c : ℕ → Fin d → LL, IsSol W T i b z c ∧ c 0 = fun m => algebraMap O LL (c₀ m)) ∧
        ∀ c : ℕ → Fin d → LL, IsSol W T i b z c → c 0 = (fun m => algebraMap O LL (c₀ m)) →
          ∀ r m, Bd W r (c r m)) ∧
    (∀ r : ℕ, ((r + padicValNat PD.p r.factorial : ℕ) : ℚ) ≤ r * PD.p / ((PD.p : ℚ) - 1)) ∧
    (∀ (d : ℕ) (b : Fin d → W.DD T), IsFrameΔ W T i b → ∀ sol : Fin d → ℕ → Fin d → LL,
      (∀ k, IsSol W T i b 0 (sol k) ∧ sol k 0 = Pi.single k 1) →
        (∀ k r m, Bd W r (sol k r m)) ∧
        ∀ m k r, Bd W r (PowerSeries.coeff r
          ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
            Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ m k)))

def toLL : LetA O n →+* (ZMod n → PowerSeries LL) :=
  RingHom.pi fun i => (PowerSeries.map (algebraMap O LL)).comp
    (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i)

def qp (W : LocWach PD LL O v n) : LetA O n := W.π₀ + ((PD.p : ℕ) : LetA O n)

def pk (W : LocWach PD LL O v n) (k : ℕ) : LetA O n := (W.φA ^ k) (qp W)

def JJ (W : LocWach PD LL O v n) (j y M' : ℕ) : LetA O n :=
  W.π₀ ^ M' * ∏ k ∈ Finset.range j, pk W k ^ y

def InLA0 (W : LocWach PD LL O v n) (σ : ℚ) (x : ZMod n → PowerSeries LL) : Prop :=
  ∃ d : LL, ∃ a ∈ W.AΔ, (((-σ : ℚ)) : WithTop ℚ) ≤ v d ∧ x = d • toLL a

def InWachLocalised (W : LocWach PD LL O v n) (x : ZMod n → PowerSeries LL) : Prop :=
  ∃ k : ℕ, ∃ a ∈ W.AΔ, x = ((PD.p : LL) ^ k)⁻¹ • toLL a

def sigT (l j y M' : ℕ) : ℚ := ((y : ℚ) + M' / (l : ℚ) ^ (j - 1)) * l / ((l : ℚ) - 1) ^ 2 + 1

def coreTr (W : LocWach PD LL O v n) : Prop :=
  CaseA W →
    (∀ k : ℕ, ∃ a ∈ W.AΔ, ∃ b ∈ W.AΔ,
      pk W k = ((PD.p : ℕ) : LetA O n) * a + W.π₀ ^ (PD.p ^ k) * b) ∧
    (∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, pk W k ^ ((PD.p - 1) * r)) ∧
    (∀ j y M' r : ℕ, 1 ≤ j → ∀ c : LL,
      v c = (((-((r : ℚ) * PD.p / ((PD.p : ℚ) - 1))) : ℚ) : WithTop ℚ) →
      ∃ x₁ x₂, InLA0 W (sigT PD.p j y M') x₁ ∧ InWachLocalised W x₂ ∧
        c • toLL (((W.φA ^ j) W.π₀) ^ r) = x₁ + toLL (JJ W j y M') * x₂) ∧
    (∀ j y M' : ℕ, 1 ≤ j → ∀ N : ℕ, ∃ r₀ : ℕ, ∀ r ≥ r₀, ∀ c : LL,
      v c = (((-((r : ℚ) * PD.p / ((PD.p : ℚ) - 1))) : ℚ) : WithTop ℚ) →
      ∃ x₁ x₂, (∃ a ∈ W.AΔ, x₁ = ((PD.p : LL) ^ N) • toLL a) ∧ InWachLocalised W x₂ ∧
        c • toLL (((W.φA ^ j) W.π₀) ^ r) = x₁ + toLL (JJ W j y M') * x₂)

end Local2

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Ext

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsExtOf (W : LocWach PD LL O v n) {T Tp : LocLat G Qp LL O} (ι : LatHom T.L Tp.L)
    (π : LatHom Tp.L W.one.L) (c : G → T.V) : Prop :=
  IsSESLat (Qp := Qp) ι π ∧ ∃ et ∈ Tp.L.T, Submodule.span O {π.f et} = W.one.L.T ∧
    ∀ g, ι.f (c g) = Tp.ρ g et - et

def InImgA (W : LocWach PD LL O v n) {Tp : LocLat G Qp LL O} (π : LatHom Tp.L W.one.L) (k : ℕ) :
    Prop :=
  ∃ e ∈ W.N W.one, W.N W.one = Submodule.span (LetA O n) {e} ∧ W.φD W.one e = e ∧
    (∀ g, W.γD W.one g e = e) ∧ ∃ x ∈ W.N Tp, W.map π x = ((PD.p : ℕ) : O) ^ k • e

def coreExt (W : LocWach PD LL O v n) : Prop :=
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L) (Mi hi : ZMod n → ℕ),
    IsCrys PD T.ρ → IsCrys PD Tp.ρ → JumpsLet W T Mi hi →
    ∀ (c : G → T.V) (hc : c ∈ latticeCocycles T.L), IsExtOf W ι π c → ∀ k : ℕ, InImgA W π k →
      ∃ (y z : W.DD T) (h : (y, z) ∈ W.divisibleCocycles T), W.Q ^ Mmax n Mi • y ∈ W.N T ∧
        (∃ z' ∈ W.N T, z = W.X • z') ∧
        W.cl T ⟨(y, z), h⟩ = ((PD.p : ℕ) : O) ^ k •
          Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (Submodule.Quotient.mk (⟨c, hc⟩ : ↥(latticeCocycles T.L)) : LatticeCohomology T.L)

def coreExtΔ (W : LocWach PD LL O v n) : Prop :=
  CaseA W →
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L) (Mi hi : ZMod n → ℕ),
    IsCrys PD T.ρ → IsCrys PD Tp.ρ → JumpsLet W T Mi hi →
    ∀ (c : G → T.V) (hc : c ∈ latticeCocycles T.L), IsExtOf W ι π c → ∀ k : ℕ, InImgA W π k →
      ∃ (y z : W.DD T) (h : (y, z) ∈ W.wachCocyclesDelta T), qp W ^ Mmax n Mi • y ∈ W.N T ∧
        (∃ z' ∈ W.NΔ T, z = W.π₀ • z') ∧
        W.clK T ⟨(y, z), h⟩ = ((PD.p : ℕ) : O) ^ k •
          (Submodule.Quotient.mk (⟨c, hc⟩ : ↥(latticeCocycles T.L)) : LatticeCohomology T.L)

def xList (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (M h Y : ℕ) : List ℤ :=
  (((jumpSet W T M h) ×ˢ Finset.Icc (1 : ℤ) Y).image (fun p : ℤ × ℤ => p.1 + p.2)).sort (· ≤ ·)

def coreDss (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T.ρ → JumpsLet W T Mi hi →
    ∀ (ug : Oˣ), ug ^ (PD.p - 1) = (W.χΓ W.gam) ^ (PD.p - 1) →
      v (algebraMap O LL ((ug : O) - 1)) = 1 →
    ∀ cO : ℤ → O, (∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - ((ug ^ (-x) : Oˣ) : O)) →
    ∀ (Y : ℕ) (y₀ : W.DD T), qp W ^ Y • y₀ ∈ W.N T → (∀ δ ∈ W.DelF, W.γD T δ y₀ = y₀) →
      ∃ seq : ℕ → W.DD T, seq 0 = y₀ ∧
        (∀ k : ℕ, k < (xList W T (Mmax n Mi) (Mmax n hi) Y).length →
          W.π₀ • (seq (k + 1) + cO ((xList W T (Mmax n Mi) (Mmax n hi) Y).getD k 0) • seq k) =
            W.γD T W.gam (seq k) - seq k) ∧
        seq (xList W T (Mmax n Mi) (Mmax n hi) Y).length ∈ W.N T

variable (PD LL O) in

def coreJumps : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := Qp) ι π → IsCrys PD T₀.ρ → IsCrys PD T₁.ρ → IsCrys PD T₂.ρ →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      IsJumpV PD T₁.ρ τ a ↔ IsJumpV PD T₀.ρ τ a ∨ IsJumpV PD T₂.ρ τ a

end Ext

section Desc

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B] [Algebra K₀' BdR] [Algebra K' BdR]
    [IsScalarTower Qp K' BdR] [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

@[reducible] def resLoc (ι : G →* G') (hι : Continuous ι) (T : LocLat G' Qp LL O) : LocLat G Qp LL O where
  V := T.V
  ρ := T.ρ.comp ι
  cont := fun x => (T.cont x).comp hι
  L :=
    { T := T.L.T
      stable := fun _g x hx => T.L.stable _ x hx
      fg := T.L.fg
      free := T.L.free
      span := T.L.span }

def resHom (ι : G →* G') (hι : Continuous ι) {T₁ T₂ : LocLat G' Qp LL O} (F : LatHom T₁.L T₂.L) :
    LatHom (resLoc ι hι T₁).L (resLoc ι hι T₂).L where
  f := F.f
  equiv := fun _g x => F.equiv _ x
  cont := F.cont
  T_le := F.T_le

def coreDesc (W : LocWach PD LL O v n) (PD' : PeriodData G' Qp K₀' K' B BdR) (ι : G →* G')
    (hι : Continuous ι) (g : ℕ) : Prop :=
  ι.range.Normal → ∀ (T₁ T₂ : LocLat G' Qp LL O) (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ),
    Sur W (resHom ι hι F) → JumpsLet W (resLoc ι hι T₁) Mi hi →
    (CaseA W → F.LiftF PD' (ePA PD.p (Mmax n Mi) (Hmax n Mi hi)
        (jumpSet W (resLoc ι hι T₁) (Mmax n Mi) (Mmax n hi)) + padicValNat PD.p g)) ∧
    (CaseB W → F.LiftF PD' (ePB PD.p W.s (Mmax n Mi) (Hmax n Mi hi)
        (jumpSet W (resLoc ι hι T₁) (Mmax n Mi) (Mmax n hi)) + padicValNat PD.p g))

def resFun (ι : G →* G') (T : LocLat G' Qp LL O) : (G' → T.V) →ₗ[O] (G → T.V) :=
  LinearMap.funLeft O T.V ι

theorem resFun_Z1T (ι : G →* G') (hι : Continuous ι) (T : LocLat G' Qp LL O) (c : G' → T.V)
    (hc : c ∈ latticeCocycles T.L) : resFun ι T c ∈ latticeCocycles (resLoc ι hι T).L := by
  obtain ⟨⟨hcont, hcoc⟩, hT⟩ := hc
  refine ⟨⟨hcont.comp hι, fun g h => ?_⟩, ?_⟩
  · simp only [resFun, LinearMap.funLeft_apply, map_mul, hcoc]
    rfl
  · intro g _
    exact hT (ι g) (Set.mem_univ _)

theorem resFun_B1T (ι : G →* G') (hι : Continuous ι) (T : LocLat G' Qp LL O) (c : G' → T.V)
    (hc : c ∈ latticeCoboundaries T.L) : resFun ι T c ∈ latticeCoboundaries (resLoc ι hι T).L := by
  obtain ⟨x, hx, rfl⟩ := hc
  exact ⟨x, hx, by funext g; rfl⟩

def resH1 (ι : G →* G') (hι : Continuous ι) (T : LocLat G' Qp LL O) :
    LatticeCohomology T.L →ₗ[O] LatticeCohomology (resLoc ι hι T).L :=
  Submodule.mapQ _ _
    (((resFun ι T).comp (latticeCocycles T.L).subtype).codRestrict (latticeCocycles (resLoc ι hι T).L)
      (fun c => resFun_Z1T ι hι T c c.2))
    (by
      intro c hc
      simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
      exact resFun_B1T ι hι T c hc)

def coreCor (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR) (LL O : Type)
    [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL] (ι : G →* G')
    (hι : Continuous ι) (g : ℕ) : Prop :=
  (∀ (T : LocLat G' Qp LL O) (κ : LatticeCohomology T.L), κ ∈ latticeFiniteCohomology PD' T.L →
    resH1 ι hι T κ ∈ latticeFiniteCohomology PD (resLoc ι hι T).L) ∧
  ∃ cor : ∀ T : LocLat G' Qp LL O, LatticeCohomology (resLoc ι hι T).L →ₗ[O] LatticeCohomology T.L,
    (∀ (T : LocLat G' Qp LL O) (κ : LatticeCohomology T.L), cor T (resH1 ι hι T κ) = (g : O) • κ) ∧
    (∀ (T : LocLat G' Qp LL O) (κ : LatticeCohomology (resLoc ι hι T).L), κ ∈ latticeFiniteCohomology PD (resLoc ι hι T).L →
      cor T κ ∈ latticeFiniteCohomology PD' T.L) ∧
    (∀ (T₁ T₂ : LocLat G' Qp LL O) (F : LatHom T₁.L T₂.L) (κ : LatticeCohomology (resLoc ι hι T₁).L),
      cor T₂ ((resHom ι hι F).H1map κ) = F.H1map (cor T₁ κ))

end Desc

def ConclusionL (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreL ((HW l).W K s LL h)

def WachKillsQuotients (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreWX ((HW l).W K s LL h)

def WachKillsCaseB (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreWB ((HW l).W K s LL h)

def WachKillsCaseA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreWA ((HW l).W K s LL h)

def WachKillsIntermediateField (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreWK1 ((HW l).W K s LL h)

def ConclusionW (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := WachKillsQuotients D HW F ∧ WachKillsCaseB D HW F ∧ WachKillsCaseA D HW F ∧ WachKillsIntermediateField D HW F

def WachAnnihilatorAll (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachQuotientAnnihilator ((HW l).W K s LL h)

def WachExponentRecursionAll (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachExponentRecursion ((HW l).W K s LL h)

def WachResultConstant (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreWR ((HW l).W K s LL h) C

def WachExponentUpperBound (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreWS ((HW l).W K s LL h)

theorem wach_exponent_bound_of_kills (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (hX : WachKillsQuotients D HW F) (h2 : WachExponentRecursionAll D HW F) : WachExponentUpperBound D HW F :=
  fun l _ K s LL h => coreWS_of _ (hX l K s LL h) (h2 l K s LL h)

def ConclusionH (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreH ((HW l).W K s LL h)

def ExistsUnitClasses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreTr ((HW l).W K s LL h)

def LiftTheoremCaseA (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreLiftA ((HW l).W K s LL h)

def LiftTheoremCaseB (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreLiftB ((HW l).W K s LL h)

def LiftBracketR (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreLiftR ((HW l).W K s LL h)

def LiftExponentShapes (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreLiftO ((HW l).W K s LL h) CA CB CK

def LiftGaloisDescent (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (hKK : K'.1 ≤ K.1) (hle : GK K ≤ GK K')
    (_hN : (GKin hKK).Normal) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreDesc ((HW l).W K s LL h) ((D.loc l).PD K') (Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _)
      (Module.finrank ℚ_[l] ↥K.1 / Module.finrank ℚ_[l] ↥K'.1) ∧
    (CaseB ((HW l).W K s LL h) → s = 1 → K0 K ≤ K'.1 →
      padicValNat l (Module.finrank ℚ_[l] ↥K.1 / Module.finrank ℚ_[l] ↥K'.1) = 0)

def LiftTheoremAllCases (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop :=
  LiftTheoremCaseA D HW F ∧ LiftTheoremCaseB D HW F ∧ LiftBracketR D HW F ∧ LiftExponentShapes D HW F CA CB CK ∧ LiftGaloisDescent D HW F

def aux₃ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) : Prop :=
  ConclusionL D HW F ∧ ConclusionW D HW F ∧ WachAnnihilatorAll D HW F ∧ WachExponentRecursionAll D HW F ∧ WachResultConstant D HW F C ∧ ConclusionH D HW F ∧ ExistsUnitClasses D HW F ∧ LiftTheoremAllCases D HW F CA CB CK

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P2 D HW F

def adm3 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm

def ArchimedeanSignatureMatching (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm

def adm5 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F

def adm7 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P7 D HW F

def adm8 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P8 D HW F

def adm9 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def adm10 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.WachCharacterisation D HW F

def adm11 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.gammaSemisimpleQuotientGlobal D HW F

def adm12 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F

def adm13 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.Pr2b D HW F

def adm14 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.Pr2c D HW F

def adm15 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.Pr2d D HW F

def adm16 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.lem3 D HW F

def adm17 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreExt ((HW l).W K s LL h)

def adm18 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreExtΔ ((HW l).W K s LL h)

def adm19 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreDss ((HW l).W K s LL h)

def adm20 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (_hKK : K'.1 ≤ K.1) (hle : GK K ≤ GK K')
    (LL : FinExt l),
    coreCor ((D.loc l).PD K) ((D.loc l).PD K') ↥LL.1 ↥(OL LL) (Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _)
      (Module.finrank ℚ_[l] ↥K.1 / Module.finrank ℚ_[l] ↥K'.1)

def adm21 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ((HW l).W K s LL h).ClNat ∧ (s = 1 → l ≠ 2 → ((HW l).W K s LL h).ClKNat)

def adm22 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), FontaineLe ((D.loc l).PD K) ↥LL.1

def adm23 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), coreJumps ((D.loc l).PD K) ↥LL.1 ↥(OL LL)

def admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  adm1 D HW F ∧ adm2 D HW F ∧ adm3 D HW F Cm ∧ ArchimedeanSignatureMatching D HW F Cm ∧ adm5 D HW F ∧ adm6 D HW F ∧ adm7 D HW F ∧ adm8 D HW F ∧
    adm9 D HW F ∧ adm10 D HW F ∧ adm11 D HW F ∧ adm12 D HW F ∧ adm13 D HW F ∧ adm14 D HW F ∧ adm15 D HW F ∧ adm16 D HW F ∧
    adm17 D HW F ∧ adm18 D HW F ∧ adm19 D HW F ∧ adm20 D HW F ∧ adm21 D HW F ∧ adm22 D HW F ∧ adm23 D HW F

def Stmt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (C CA CB CK : ℝ) : Prop := admitted D HW F Cm → aux₃ D HW F C CA CB CK

def RealisationStatementAll : Prop := ∃ C CA CB CK : ℝ, ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Stmt D HW F Cm C CA CB CK

end Formalism.MainNotions.LiftingTheory
