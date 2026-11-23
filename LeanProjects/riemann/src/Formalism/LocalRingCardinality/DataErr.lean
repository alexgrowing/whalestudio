import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.LocalRingCardinality.DataForced
import Formalism.LocalRingCardinality.DataLevelD

noncomputable section

namespace Formalism.BasicNotions

open Formalism.FrobeniusOrbits Formalism.MainNotions.G NumberField IsDedekindDomain
open scoped BigOperators

structure ErrC where
  c6 : ℝ
  dig : ℝ
  g : ℝ

def ErrC.Large (c : ErrC) : Prop := 12 ≤ c.c6 ∧ 3 ≤ c.dig ∧ 10 ≤ c.g

structure ErrX (D : D7) where

  piG : Fin 2 → 𝓞 D.host.E
  piG_K : ∀ i, ((piG i : 𝓞 D.host.E) : D.host.E) ∈ D.host.K
  piG_norm : ∀ i, ((piG i : 𝓞 D.host.E) : D.host.E) * D.host.conj (piG i : D.host.E) = (D.host.g i : D.host.E)

  piT : D.what₂.Word → 𝓞 D.host.E
  piT_K : ∀ u, ((piT u : 𝓞 D.host.E) : D.host.E) ∈ D.host.K
  piT_norm : ∀ u, ((piT u : 𝓞 D.host.E) : D.host.E) * D.host.conj (piT u : D.host.E) = ((D.mem u).A.T : D.host.E)
  piT_cong : ∀ u, (piT u - 1) ∈
    Ideal.span {((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E)}

  vPl : ∀ u, (D.mem u).A.vT → HeightOneSpectrum (𝓞 D.host.F)
  vPl_inj : ∀ u, Function.Injective (vPl u)
  norm_mem_place_ideal : ∀ u v, ((D.mem u).A.T : 𝓞 D.host.F) ∈ (vPl u v).asIdeal

def tauLL (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.LL :=
  D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x)

open scoped TensorProduct in

def PiGLevel (D : D7) (lev : LevelData D) (X : ErrX D) : Prop :=
  letI := D.host.cmStar
  ∀ u (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal),
    Valued.v (((lev u).splitG i v h) ((D.host.conj (X.piG i : D.host.E)) ⊗ₜ[D.host.F] (1 : v.adicCompletion D.host.F))).1 < 1

open scoped TensorProduct in

def PiTLevel (D : D7) (lev : LevelData D) (X : ErrX D) : Prop :=
  letI := D.host.cmStar
  ∀ u (v : (D.mem u).A.vT) (z : intV D.host.E (X.vPl u v)),
    (z : D.host.E ⊗[D.host.F] (X.vPl u v).adicCompletion D.host.F) =
      ((X.piT u : 𝓞 D.host.E) : D.host.E) ⊗ₜ[D.host.F] (1 : (X.vPl u v).adicCompletion D.host.F) →
    ∀ y : (lev u).fM (X.vPl u v) (X.norm_mem_place_ideal u v), z • y = 0

open scoped TensorProduct in

theorem piT_mem_intV (D : D7) (X : ErrX D) (u : D.what₂.Word) (v : (D.mem u).A.vT) :
    ((X.piT u : 𝓞 D.host.E) : D.host.E) ⊗ₜ[D.host.F] (1 : (X.vPl u v).adicCompletion D.host.F) ∈
      intV D.host.E (X.vPl u v) :=
  Subring.subset_closure (Or.inl ⟨⟨_, ⟨X.piT u, rfl⟩⟩, rfl⟩)

def SeenDef (D : D7) (X : ErrX D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T →
    ((D.fm u).seenP w = true ↔ ∀ τ : D.what₂.Tau, (0 : WithTop ℤ) < D.what₂.places.val w (tauLL D τ (X.piT u : D.host.E)))

def TauOfDef (D : D7) (X : ErrX D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ (v : (D.mem u).A.vT) (x : 𝓞 D.host.F),
    x ∈ (X.vPl u v).asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL D ((D.fm u).tauOf w v) (algebraMap D.host.F D.host.E (x : D.host.F)))

def GamMult (D : D7) (n : ℕ) : Prop :=
  ∀ u μ i, i ≤ D.R.m → ∀ c : (D.chTw u μ).cls i, Nat.card ((D.chTw u μ).stab i c) ∣ n

def DGamDef (D : D7) : Prop :=
  ∀ u μ, GamMult D (D.chTw u μ).DGam ∧ (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam

theorem DGamDef.one {D : D7} (h : DGamDef D) (u u' : D.what₂.Word) (μ : D.what₂.Tup) :
    (D.chTw u' μ).DGam = (D.mem u).C.DGam := by
  rw [← D.memberColumns_twistedChain_base u]
  exact (h u' μ).2.trans (h u D.what₂.mu0).2.symm

def nuAbs (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  ∑ i ∈ Finset.range (D.R.N (j - 1)), DV.nuRow D u j τ i

def tauPib {D : D7} (X : ErrX D) (i : Fin 2) (τ : D.what₂.Tau) : D.what₂.LL :=
  tauLL D τ (D.host.conj (X.piG i : D.host.E))

def vNN {D : D7} (X : ErrX D) (i : Fin 2) (u : D.what₂.Word) (j : ℕ) (w : D.what₂.places.Pl) : ℝ :=
  (∑ τ : D.what₂.Tau, nuAbs D u j τ * (vAdd (D.plEq w) (tauPib X i τ) : ℝ)) / (D.what₂.places.ramIdx w : ℝ)

def EatG {D : D7} (L : SizeData₂ D) (X : ErrX D) (c : ErrC) (i : Fin 2) (u : D.what₂.Word) (j : ℕ)
    (w : D.what₂.places.Pl) : ℝ :=
  FTypeG D j + vNN X i u j w +
    c.g * (D.R.f : ℝ) * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz)

open Classical in

def Wtau (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℕ :=
  (Finset.range (D.R.m + 1)).sup fun i => Finset.univ.sup fun a : Fin (D.R.N i) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else (((D.fm u).lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs

def EatT (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) : ℝ :=
  if (D.fm u).seenP w then
    2 * (∑ τ : D.what₂.Tau, (Wtau D u τ : ℝ)) + (D.R.f : ℝ) * Nm D +
      ((topsOf D.host D.eTau).card : ℝ) * ((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1) / 4
  else 0

open Classical in

def ctD (D : D7) (u : D.what₂.Word) (j : ℕ) (t : HH D) : ℝ :=
  nuAbs D u j (tauPl D (false, t)) -
    (if t ∈ D.host.TT then DV.nuRow D u j (tauPl D (false, t)) 0 - DV.nuRow D u j (tauPl D (false, t)) 1 else 0) +
    (if t ∈ D.host.TT then DV.nuRow D u j (tauPl D (true, t)) 0 else 0)

def EatD (D : D7) (j : ℕ) : ℝ :=
  FRamD D j + (Finset.univ.sup' ⟨D.u₀, Finset.mem_univ _⟩ fun u : D.what₂.Word => ∑ t : HH D, ctD D u j t) / 2

def exch (D : D7) : ℝ := (D.R.f : ℝ) * D.R.k * Nm D

def EatC {D : D7} (L : SizeData₂ D) (c : ErrC) (j p : ℕ) : ℝ :=
  c.dig * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a +
    (∑ τ : D.what₂.Tau, wj D j τ) / ((p : ℝ) ^ 2 - 1)

open Classical in

def kindA (D : D7) (p : ℕ) : Finset (Bool × HH D) := Finset.univ.filter fun z => ¬ IsSg D p ∧ z.1 = false

open Classical in

def kindBC (D : D7) (p : ℕ) : Finset (Bool × HH D) := Finset.univ.filter fun z => IsSg D p ∨ z.1 = true

open Classical in

def topsBC (D : D7) (p : ℕ) : Finset (Bool × HH D) := (kindBC D p).filter fun z => IsTopPl D z

open Classical in

def EatX {D : D7} (L : SizeData₂ D) (c : ErrC) (j p : ℕ) : ℝ :=
  if IsCs D p then
    ((D.R.k : ℝ) - 1) * (∑ z ∈ kindBC D p, wPl D j z) / (p : ℝ) ^ 3 +
      c.c6 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a
  else 0

theorem EatX_of_not {D : D7} (L : SizeData₂ D) (c : ErrC) (j : ℕ) {p : ℕ} (h : ¬ IsCs D p) : EatX L c j p = 0 := if_neg h

def EatI {D : D7} (L : SizeData₂ D) (K : Consts) (c : ErrC) (j p : ℕ) : ℝ :=
  max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ)) +
    gam p * ((topsBC D p).card : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) +
    c.c6 * (∑ z ∈ kindBC D p, wPl D j z) / (p : ℝ) +
    ((kindBC D p).card : ℝ) * (D.R.N (j - 1) : ℝ) * (D.R.N j : ℝ) *
      (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) +
    (K.dl1 * ((kindBC D p).card : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
      K.dl2 * ((topsBC D p).card : ℝ) * Real.logb p (2 * L.sc.a) ^ 2) +
    EatX L c j p

open Classical in

def Eval {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (u : D.what₂.Word) (j : ℕ)
    (w : D.what₂.places.Pl) : ℝ :=
  let p := D.what₂.places.resChar w
  if p = (D.mem u).A.T then EatT D u w else
  (padicValNat p (D.mem u).C.DGam : ℝ) +
    (if p = D.host.g 0 then EatG L X c 0 u j w
     else if p = D.host.g 1 then EatG L X c 1 u j w
     else if D.host.cls p = PrimeClass.ramD then EatD D j
     else if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then
       (if IsResidueClassZero D p ∧ hP D p = 0 then EatC L c j p else EatI L K c j p)
     else 0)

def SizeData₂.EDef {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) : Prop :=
  ∀ u, ∀ j ∈ SizeData₂.lifts D, ∀ w, L.E u j w = Eval L X K c u j w

theorem Eval_above {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (u : D.what₂.Word) (j : ℕ)
    (w : D.what₂.places.Pl) (hX : L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ))
    (hT : D.what₂.places.resChar w ≠ (D.mem u).A.T)
    (hg : D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ))
    (hd : D.what₂.places.resChar w ≠ D.host.d) (hG : ¬ D.what₂.places.resChar w ∣ (D.mem u).C.DGam) :
    Eval L X K c u j w = 0 := by
  have h0 : D.what₂.places.resChar w ≠ D.host.g 0 := fun h => hg (by simp [h])
  have h1 : D.what₂.places.resChar w ≠ D.host.g 1 := fun h => hg (by simp [h])
  have h2 : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD := fun h => hd (cls_ramD h)
  have h3 : ¬ ((IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
      (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n) := fun h => absurd h.2 (not_le.2 hX)
  unfold Eval
  simp only [if_neg h0, if_neg h1, if_neg hT, if_neg h2, if_neg h3, padicValNat.eq_zero_of_not_dvd hG]
  simp

def SizeData₂.withEval {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC)
    (hs : ∀ u j w, w ∉ L.supp → Eval L X K c u j w = 0) : SizeData₂ D :=
  { L with
    E := fun u j w => Eval L X K c u j w
    E_supp := hs }

theorem SizeData₂.withEval_EDef {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC)
    (hs : ∀ u j w, w ∉ L.supp → Eval L X K c u j w = 0) : (L.withEval X K c hs).EDef X K c :=
  fun _ _ _ _ => rfl

theorem SizeData₂.EDef.zeroAbove {D : D7} {L : SizeData₂ D} {X : ErrX D} {K : Consts} {c : ErrC} (h : L.EDef X K c)
    (u : D.what₂.Word) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (w : D.what₂.places.Pl)
    (hX : L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ)) (hT : D.what₂.places.resChar w ≠ (D.mem u).A.T)
    (hg : D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ))
    (hd : D.what₂.places.resChar w ≠ D.host.d) (hG : ¬ D.what₂.places.resChar w ∣ (D.mem u).C.DGam) :
    L.E u j w = 0 := by
  rw [h u j hj w]; exact Eval_above L X K c u j w hX hT hg hd hG

structure ErrDefs (D : D7) (L : SizeData₂ D) (X : ErrX D) (lev : LevelData D) (K : Consts) (c : ErrC) : Prop where
  large : c.Large
  piG_lev : PiGLevel D lev X
  piT_lev : PiTLevel D lev X
  seen : SeenDef D X
  tauOf : TauOfDef D X
  dgam : DGamDef D
  edef : L.EDef X K c

end Formalism.BasicNotions

end
