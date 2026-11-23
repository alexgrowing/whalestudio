import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

def inN (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {n : ℕ} (hn : V.rank = n) (g : GA D V) :
    D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ => (inB θ V B g τ).reindex (finCongr hn) (finCongr hn)

def castP {p q a b : ℕ} (hp : p = a) (hq : q = b) : PolF D q p →ₐ[ℂ] FP D.what₂.Tau a b :=
  MvPolynomial.rename fun v => (v.1, Fin.cast hq v.2.1, Fin.cast hp v.2.2)

structure RealD (c : Comm D) where

  N : ℕ → ℕ
  hN : ∀ j, j ≤ D.R.m → (c.X j).rank = N j

  NT : ℕ
  hT : c.T.rank = NT

  fr : ∀ j, c.Fr j ≃ FrN D (N j)

  lam : ∀ j, D.what₂.Tau → DomWeight (N j)
  n : ℕ → D.what₂.Tau → ℕ
  sS : ℕ → D.what₂.Tau → ℤ
  sD : ℕ → D.what₂.Tau → ℤ
  sc : ℕ → D.what₂.Tau → ℂ

  BT : D.what₂.Tau → Matrix (Fin c.T.rank) (Fin c.T.rank) ℂ
  sg : D.what₂.Tau → DomWeight NT

  J : SmT c.MT → GA D c.T → FrN D NT → ℂ

  low : ∀ n, n = D.R.m → ((FrN D (N n) → ℂ) →ₗ[ℂ] (FrN D NT → ℂ))

namespace RealD

variable {c : Comm D} (ρ : RealD c)

abbrev r (j : ℕ) (hj : j ≤ D.R.m) (g : GA D (c.X j)) := inN c.θ (c.X j) (c.x j).B (ρ.hN j hj) g

abbrev rT (g : GA D c.T) := inN c.θ c.T ρ.BT ρ.hT g

structure Is : Prop where
  uni : ∀ j hj, OntoUni fun k : GinfC (c.X j) => ρ.r j hj k.1
  uniT : OntoUni fun k : GinfC c.T => ρ.rT k.1
  rk : ∀ j, j < D.R.m → 0 < ρ.N j ∧ ρ.N j ≤ ρ.N (j + 1)
  sc : ∀ j τ, ρ.sc j τ ≠ 0
  n : ∀ j, j < D.R.m → ∀ τ, (ρ.n j τ : ℤ) = shiftOf (ρ.lam j) τ + ρ.sS j τ
  J : ∀ v, ρ.J v 1 ∈ ValC _ ρ.sg ∧ ∀ k ∈ GinfC c.T, ∀ z z', IsTr (ρ.rT k) z z' → ρ.J v k z' = ρ.J v 1 z
  low : ∀ n (h : n = D.R.m), ∃ hN : ρ.N n = ρ.NT + 1,
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (ρ.lam n τ) (ρ.sg τ)) ∧ BrEqv hN _ _ (ρ.lam n) ρ.sg (ρ.low n h) ∧
    (∃ Φ ∈ ValC _ (ρ.lam n), ρ.low n h Φ ≠ 0) ∧
    ∀ k ∈ GinfC c.T, ∀ τ, GlobalTheory.BranchFormula.IsBlock hN (ρ.r n h.le ((c.oT n h).emb (k, 1)) τ) (ρ.rT k τ) 1

end RealD

structure ClsK {c : Comm D} (ρ : RealD c) (t : Tup c) where
  cl : ∀ j, t.Ch j → Type
  [fin : ∀ j β, Fintype (cl j β)]
  U : ∀ j, t.Ch j → Subgroup (GA D (c.X j))
  chi : ∀ j β, U j β →* ℂˣ
  h : ∀ j β, cl j β → GA D (c.X j)

  val : ∀ j β, t.Col j → cl j β → FrN D (ρ.N j) → ℂ

  abelian₂ : ∀ j α γ, cl j α → cl (j + 1) γ → (FP D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) →ₗ[ℂ] ℂ)

attribute [instance] ClsK.fin

namespace ClsK

variable {c : Comm D} {ρ : RealD c} {t : Tup c} (A : ClsK ρ t)

structure Forms : Prop where
  reps : ∀ j, j ≤ D.R.m → ∀ β, IsReps (c.X j) (A.U j β) (A.h j β)
  chi : ∀ j, j ≤ D.R.m → ∀ β, Continuous fun κ => ((A.chi j β κ : ℂˣ) : ℂ)
  valC : ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram j, ∀ β a, A.val j β ψ a ∈ ValC _ (ρ.lam j)

  rd : ∀ j hj, ∀ ψ ∈ t.Ram j, ∀ β y, ∀ γ ∈ GQ (c.X j), ∀ a, ∀ k ∈ GinfC (c.X j), ∀ (κ : A.U j β) y',
    IsTr (ρ.r j hj k) (ρ.fr j y) y' → t.rd j β ψ y (γ * (A.h j β a * k) * κ.1) = (A.chi j β κ : ℂ) * A.val j β ψ a y'

def Real (_A : ClsK ρ t) : Prop :=
  ∀ j (hj : j + 1 ≤ D.R.m) α γ, ∀ k ∈ GinfC (c.X j), ∀ k' ∈ GinfC (c.X (j + 1)), ∀ P P',
    castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P' =
      mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k τ)⁻¹) (ρ.r (j + 1) hj k')
        (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P) →
    t.kom j (k, k') ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) =
      (∏ τ, (ρ.r j (Nat.le_of_succ_le hj) k τ).det ^ ρ.sS j τ * (ρ.r (j + 1) hj k' τ).det ^ (-ρ.sD j τ)) •
        (t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P'

def Lev : Prop :=
  ∀ j, j < D.R.m → ∀ α γ (κ : A.U j α) (κ' : A.U (j + 1) γ),
    t.kom j (κ.1, κ'.1) (comb c.ψ _ _ (t.dd j α γ) (c.vac j)) =
      (((A.chi j α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) γ κ' : ℂˣ) : ℂ)) • comb c.ψ _ _ (t.dd j α γ) (c.vac j)

def Core : Prop :=
  ∀ j (hj : j + 1 ≤ D.R.m) α γ a a' P,
    (volLev (c.x j).vol (A.U j α) : ℂ) *
        thetaKO (t.kom j) (A.h j α a) (A.h (j + 1) γ a') ((t.ker j α γ).pt c.ψ c.θ (c.x j) (c.x (j + 1)) P) =
      t.cK j * A.abelian₂ j α γ a a' (mvZ (fun _ => 1) (fun τ => ρ.sc j τ • 1)
        (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) P))

def Kval : Prop :=
  ∀ j, j < D.R.m → ∀ (hab : ρ.N j ≤ ρ.N (j + 1)), ∀ ψ ∈ t.Ram j,
    ∀ F : ∀ α, A.cl j α → PY D.what₂.Tau (ρ.N j), (∀ α a, F α a ∈ Vn (ρ.lam j) (ρ.n j)) →
      (∀ α a y, A.val j α ψ a y = evalAt y.1 (F α a) * ∏ τ, (y.1 τ).det ^ (-ρ.sS j τ)) →
      ∀ γ a' y', A.val (j + 1) γ (t.K j ψ) a' y' =
        ∑ α, ∑ a, ((stabOrd (A.U j α) (A.h j α a) : ℕ) : ℂ)⁻¹ * A.abelian₂ j α γ a a' (subY hab y'.1 (F α a)) *
          ∏ τ, (y'.1 τ).det ^ (-ρ.sD j τ)

def Is : Prop := A.Forms ∧ A.Real ∧ A.Lev ∧ A.Core ∧ A.Kval

end ClsK

structure ClsT {c : Comm D} (ρ : RealD c) (t : Tup c) where
  cl : Type
  [fin : Fintype cl]
  U : Subgroup (GA D c.T)
  h : cl → GA D c.T

  ell : ∀ n, n = D.R.m → t.Ch n → cl → t.CT → ((FrN D ρ.NT → ℂ) →ₗ[ℂ] ℂ)

attribute [instance] ClsT.fin

structure ClsT.Is {c : Comm D} {ρ : RealD c} {t : Tup c} (A : ClsT ρ t) : Prop where
  reps : IsReps c.T A.U A.h

  inv : ∀ n (h : n = D.R.m), ∀ ψ ∈ t.Ram n, ∀ (G : t.CT) v y β g, ∀ κ ∈ A.U,
    trc (t.eT n h β) (G.1 v) (g * κ) * t.rd n β ψ y ((c.oT n h).emb (g * κ, 1)) =
      trc (t.eT n h β) (G.1 v) g * t.rd n β ψ y ((c.oT n h).emb (g, 1))

  top : ∀ n (h : n = D.R.m) (G : t.CT) v β a, ∀ k ∈ GinfC c.T,
    trc (t.eT n h β) (G.1 v) (A.h a * k) = A.ell n h β a G (ρ.J v k)

  tail : ∀ n (h : n = D.R.m), ∀ ψ ∈ t.Ram n, ∀ G : t.CT,
    (volLev c.volT A.U : ℂ) * ∑ β, ∑ a, ((stabOrd A.U (A.h a) : ℕ) : ℂ)⁻¹ *
        A.ell n h β a G (ρ.low n h fun z => t.rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (A.h a, 1))) =
      t.cP * t.tail n h ψ G

def ClsPinD {c : Comm D} {𝒯 : Type} (t : 𝒯 → Tup c) : Prop :=
  ∃ ρ : RealD c, ρ.Is ∧ ∀ s, (∃ A : ClsK ρ (t s), A.Is) ∧ ∃ A : ClsT ρ (t s), A.Is

namespace Sized

theorem inN_rank (θ : InfFam D) (V : HSp D) (B) (g : GA D V) : inN θ V B rfl g = inB θ V B g := by
  funext τ; ext i j; simp [inN]

theorem castP_rank {p q : ℕ} (P : PolF D q p) : castP (D := D) (rfl : p = p) (rfl : q = q) P = P := by
  have : (fun v : FVar D q p => ((v.1, Fin.cast rfl v.2.1, Fin.cast rfl v.2.2) : FVar D q p)) = id := by funext v; rfl
  unfold castP
  rw [this]; exact MvPolynomial.rename_id_apply P

theorem castP_bijective {p q a b : ℕ} (hp : p = a) (hq : q = b) : Function.Bijective (castP (D := D) hp hq) := by
  subst hp; subst hq
  have : (castP (D := D) (rfl : p = p) (rfl : q = q) : _ → _) = id := funext castP_rank
  rw [this]; exact Function.bijective_id

end Sized

example {p q a b : ℕ} (hp : p = a) (hq : q = b) (τ : D.what₂.Tau) (i : Fin q) (k : Fin p) :
    castP (D := D) hp hq (MvPolynomial.X (τ, i, k)) = MvPolynomial.X (τ, Fin.cast hq i, Fin.cast hp k) := by
  unfold castP; exact MvPolynomial.rename_X _ _

def RealC.toD {c : Comm D} (ρ : RealC c) : RealD c :=
  ⟨fun j => (c.X j).rank, fun _ _ => rfl, c.T.rank, rfl, ρ.fr, ρ.lam, ρ.n, ρ.sS, ρ.sD, ρ.sc, ρ.BT, ρ.sg, ρ.J, ρ.low⟩

theorem RealC.toD_r {c : Comm D} (ρ : RealC c) (j hj g) : ρ.toD.r j hj g = c.r j g := Sized.inN_rank _ _ _ _

theorem RealC.toD_rT {c : Comm D} (ρ : RealC c) (g) : ρ.toD.rT g = inB c.θ c.T ρ.BT g := Sized.inN_rank _ _ _ _

theorem RealC.Is.toD {c : Comm D} {ρ : RealC c} (h : ρ.Is) : ρ.toD.Is where
  uni j hj := by simp only [RealC.toD_r]; exact h.uni j hj
  uniT := by simp only [RealC.toD_rT]; exact h.uniT
  rk := h.rk
  sc := h.sc
  n := h.n
  J v := by simp only [RealC.toD_rT]; exact h.J v
  low n hn := by simp only [RealC.toD_rT, RealC.toD_r]; exact h.low n hn

def ClsDat.toK {c : Comm D} {t : Tup c} (A : ClsDat t) (ρ : RealC c) : ClsK ρ.toD t := ⟨A.cl, A.U, A.chi, A.h, A.val, A.abelian₂⟩

def ClsDat.toT {c : Comm D} {t : Tup c} (A : ClsDat t) (ρ : RealC c) : ClsT ρ.toD t := ⟨A.clT, A.UT, A.hT, A.ell⟩

theorem ClsDat.Is.toK {c : Comm D} {t : Tup c} {A : ClsDat t} {ρ : RealC c} (hA : A.Is ρ) : (A.toK ρ).Is := by
  refine ⟨⟨hA.reps, hA.chi, hA.valC, ?_⟩, ?_, hA.lev, ?_, hA.kval⟩
  · intro j hj; simp only [RealC.toD_r]; exact hA.rd j hj
  · intro j hj α γ k hk k' hk' P P' hP
    have e1 := Sized.castP_rank (D := D) P
    have e2 := Sized.castP_rank (D := D) P'
    have hP' : P' = mvZ (fun τ => (c.r j k τ)⁻¹) (c.r (j + 1) k') P := by
      simp only [RealC.toD_r] at hP
      exact e2.symm.trans (hP.trans (congrArg _ e1))
    simp only [RealC.toD_r]
    rw [hP']; exact hA.real j hj α γ k hk k' hk' P
  · intro j hj α γ a a' P
    have e1 := Sized.castP_rank (D := D) P
    exact (hA.core j hj α γ a a' P).trans
      (congrArg (fun Q => t.cK j * A.abelian₂ j α γ a a' (mvZ (fun _ => 1) (fun τ => ρ.sc j τ • 1) Q)) e1.symm)

theorem ClsDat.Is.toT {c : Comm D} {t : Tup c} {A : ClsDat t} {ρ : RealC c} (hA : A.Is ρ) : (A.toT ρ).Is :=
  ⟨hA.repsT, hA.invT, hA.top, hA.tail⟩

theorem ClsPin.toD {c : Comm D} {𝒯 : Type} {t : 𝒯 → Tup c} (h : ClsPin t) : ClsPinD t := by
  obtain ⟨ρ, hρ, H⟩ := h
  refine ⟨ρ.toD, hρ.toD, fun s => ?_⟩
  obtain ⟨A, hA⟩ := H s
  exact ⟨⟨_, hA.toK⟩, ⟨_, hA.toT⟩⟩

@[reducible] def Comm.onFrames (c : Comm D) (N : ℕ → ℕ) : Comm D := { c with Fr := fun j => FrN D (N j) }

@[reducible] def Tup.onFrames {c : Comm D} (t : Tup c) {N : ℕ → ℕ} (fr : ∀ j, j ≤ D.R.m → (c.Fr j ≃ FrN D (N j))) :
    Tup (c.onFrames N) where
  om := t.om
  omT := t.omT
  pt := t.pt
  ptT := t.ptT
  sBF := t.sBF
  sFB := t.sFB
  CC := t.CC
  CT := t.CT
  io := t.io
  ioT := t.ioT
  kom := t.kom
  Ch := t.Ch
  dd := t.dd
  e := t.e
  eT := t.eT
  Col := t.Col
  Ram := t.Ram
  S := t.S
  K := t.K
  rd := fun j β ψ z => if hj : j ≤ D.R.m then t.rd j β ψ ((fr j hj).symm z) else 0
  tail := t.tail
  cI := t.cI
  cV := t.cV
  cK := t.cK
  cP := t.cP

def ClsPinF {c : Comm D} {𝒯 : Type} (t : 𝒯 → Tup c) : Prop :=
  ∃ (N : ℕ → ℕ) (fr : ∀ j, j ≤ D.R.m → (c.Fr j ≃ FrN D (N j))), ClsPinD fun s => (t s).onFrames fr

section Frames

variable {c : Comm D} {N : ℕ → ℕ} (fr : ∀ j, j ≤ D.R.m → (c.Fr j ≃ FrN D (N j)))

theorem Tup.onFrames_rd (t : Tup c) {j : ℕ} (hj : j ≤ D.R.m) (β ψ) (z : FrN D (N j)) :
    (t.onFrames fr).rd j β ψ z = t.rd j β ψ ((fr j hj).symm z) := dif_pos hj

theorem Tup.onFrames_rd_apply (t : Tup c) {j : ℕ} (hj : j ≤ D.R.m) (β ψ) (y : c.Fr j) :
    (t.onFrames fr).rd j β ψ (fr j hj y) = t.rd j β ψ y := by
  rw [t.onFrames_rd fr hj, Equiv.symm_apply_apply]

theorem Comm.onFrames_is (N : ℕ → ℕ) : (c.onFrames N).Is ↔ c.Is :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9⟩, fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9⟩⟩

theorem Tup.onFrames_is (t : Tup c) : (t.onFrames fr).Is ↔ t.Is :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14⟩,
    fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14⟩⟩

variable {𝒯 : Type} {t : 𝒯 → Tup c}

theorem KerX.of_onFrames (h : KerX fun s => (t s).onFrames fr) : KerX t := by
  intro j hj y P
  obtain ⟨a, ha⟩ := h j hj (fr j hj.le y) P
  refine ⟨a.equivMapDomain (fr (j + 1) hj).symm, fun s ψ hψ γ => ?_⟩
  have h1 := ha s ψ hψ γ
  simp only [dif_pos hj.le, Equiv.symm_apply_apply] at h1
  refine h1.trans (congrArg _ ?_)
  have h2 := Finsupp.sum_equivMapDomain (fr (j + 1) hj).symm a fun y' x => x • (t s).rd (j + 1) γ ((t s).K j ψ) y'
  refine Eq.trans ?_ h2.symm
  exact Finset.sum_congr rfl fun z _ => congrArg _ ((t s).onFrames_rd fr hj γ _ z)

theorem PerX.of_onFrames (h : PerX fun s => (t s).onFrames fr) : PerX t := by
  intro n hn y v
  obtain ⟨a, ha⟩ := h n hn (fr n hn.le y) v
  refine ⟨a, fun s ψ hψ F => ?_⟩
  have h1 := ha s ψ hψ F
  simp only [dif_pos hn.le, Equiv.symm_apply_apply] at h1
  exact h1

theorem RdX.of_onFrames (h : RdX fun s => (t s).onFrames fr) : RdX t := by
  intro j hj
  obtain ⟨χ, hχ⟩ := h j hj
  refine ⟨χ, fun s ψ hψ α y => ?_⟩
  have h1 := hχ s ψ hψ α (fr j hj y)
  rw [(t s).onFrames_rd_apply fr hj] at h1
  exact h1

end Frames

@[reducible] def RealD.onFrames {c : Comm D} (ρ : RealD c) : RealD (c.onFrames ρ.N) :=
  ⟨ρ.N, ρ.hN, ρ.NT, ρ.hT, fun _ => Equiv.refl _, ρ.lam, ρ.n, ρ.sS, ρ.sD, ρ.sc, ρ.BT, ρ.sg, ρ.J, ρ.low⟩

theorem ClsPinF.laws {c : Comm D} {𝒯 : Type} {t : 𝒯 → Tup c} (hc : c.Is) (ht : ∀ s, (t s).Is) (h : ClsPinF t) :
    ((∀ (c : Comm D) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → KerX t) → KerX t) ∧
    ((∀ (c : Comm D) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → PerX t) → PerX t) ∧
    ((∀ (c : Comm D) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → RdX t) → RdX t) := by
  obtain ⟨N, fr, h⟩ := h
  have h1 := (Comm.onFrames_is N).2 hc
  have h2 := fun s => ((t s).onFrames_is fr).2 (ht s)
  exact ⟨fun H => .of_onFrames fr (H _ _ h1 h2 h), fun H => .of_onFrames fr (H _ _ h1 h2 h), fun H => .of_onFrames fr (H _ _ h1 h2 h)⟩

@[reducible] def Comm.cutFr (c : Comm D) : Comm D := { c with Fr := fun j => {_y : c.Fr j // j ≤ D.R.m} }

@[reducible] def Tup.cutFr {c : Comm D} (t : Tup c) : Tup c.cutFr where
  om := t.om
  omT := t.omT
  pt := t.pt
  ptT := t.ptT
  sBF := t.sBF
  sFB := t.sFB
  CC := t.CC
  CT := t.CT
  io := t.io
  ioT := t.ioT
  kom := t.kom
  Ch := t.Ch
  dd := t.dd
  e := t.e
  eT := t.eT
  Col := t.Col
  Ram := t.Ram
  S := t.S
  K := t.K
  rd := fun j β ψ y => t.rd j β ψ y.1
  tail := t.tail
  cI := t.cI
  cV := t.cV
  cK := t.cK
  cP := t.cP

example (c : Comm D) : IsEmpty (c.cutFr.Fr (D.R.m + 1)) := ⟨fun y => absurd y.2 (Nat.not_succ_le_self _)⟩

example (c : Comm D) (N : ℕ → ℕ) (hN : ∀ j, j ≤ D.R.m → (c.X j).rank = N j) : Nonempty (RealD (c.onFrames N)) :=
  ⟨⟨N, hN, c.T.rank, rfl, fun _ => Equiv.refl _, fun _ _ => ⟨0, fun _ _ _ => le_rfl⟩, 0, 0, 0, 1, 1,
    fun _ => ⟨0, fun _ _ _ => le_rfl⟩, 0, fun _ _ => 0⟩⟩

example {c : Comm D} {𝒯 : Type} {t : 𝒯 → Tup c} (h : ClsPinF t) : (c.X D.R.m).rank = c.T.rank + 1 := by
  obtain ⟨_, _, ρ, hρ, -⟩ := h
  obtain ⟨hN, -⟩ := hρ.low _ rfl
  exact (ρ.hN _ le_rfl).trans (hN.trans (congrArg (· + 1) ρ.hT.symm))

end GlobalTheory.SeeSaw

end
