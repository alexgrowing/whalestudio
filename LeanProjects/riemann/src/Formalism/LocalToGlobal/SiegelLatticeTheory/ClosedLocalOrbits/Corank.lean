import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.LemmaN

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Corank

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def ScalRel (Λ : Submodule (𝓞 E) S.V) (g k : ℕ) {T T' : E} (F : LFlag S r T) (F' F'' : LFlag S r T') : Prop :=
  ∃ β : S.V ≃ₗ[E] S.V, IsPair Λ F F' F'' β g ∧ s0 Λ F F' F'' β k = 1 ∧ IsScalar Λ F F' F'' β

def s0T (Λ : Submodule (𝓞 E) S.V) (g k : ℕ) {T T' : E} (F : LFlag S r T) (F' F'' : LFlag S r T') : ℕ :=
  if h : ∃ β : S.V ≃ₗ[E] S.V, IsPair Λ F F' F'' β g then s0 Λ F F' F'' (Classical.choose h) k else 0

theorem isPair_refl (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    IsPair Λ F F' F' (LinearEquiv.refl E S.V) g := by
  refine ⟨⟨fun x y => rfl, ?_⟩, fun j => ?_, rfl, fun x' _ l _ => Iff.rfl⟩
  · simp [Formalism.HermitianLatticesTheory.gmap]
  · simp

end Gen

def CorankPosG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r k : ℕ),
    finrank E S.V = k + 2 * r + 1 →
    ∀ Λ : Submodule (𝓞 E) S.V, Submodule.IsLattice E Λ →
    ∀ (T T' : E) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V),
      IsLift Λ F → IsLift Λ F' → Gval F F' ≠ 0 → 1 ≤ s0 Λ F F' F'' β k

def ScalarEquivG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r k g : ℕ),
    finrank E S.V = k + 2 * r + 1 →
    ∀ Λ : Submodule (𝓞 E) S.V, Submodule.IsLattice E Λ →
    ∀ (T T' : E), T ≠ 0 → T' ≠ 0 → ∀ F : LFlag S r T, IsLift Λ F →
      Equivalence (fun x y : {F' : LFlag S r T' // IsLift Λ F' ∧ Gval F F' ≠ 0} => ScalRel Λ g k F x.1 y.1)

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem finrank_VS : finrank D.host.E (VS D).V = D.R.k + 2 * D.R.rS + 1 := by
  have h1 := (D.sp.Y 0).rank_eq
  have h2 := D.sp.Y_rank 0 (Nat.zero_le _)
  obtain ⟨j, hj⟩ := D.R.m_even
  have h3 := D.R.two_le_m
  simp only [VS] at *
  rw [h1, h2]
  simp only [Ranks.rankY, Ranks.r, Ranks.rS]
  omega

structure Pair (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) where
  lam : Submodule (𝓞 D.host.E) (VS D).V
  mem : lam ∈ what₂
  fst : Carrier (PD D lam (lf D F0) u')
  snd : Carrier (PD D lam (lf D F0) u')
  G_fst : Gval (lf D F0) fst.1 ≠ 0
  G_snd : Gval (lf D F0) snd.1 ≠ 0
  beta : (VS D).V ≃ₗ[D.host.E] (VS D).V
  isPair : IsPair lam (lf D F0) fst.1 snd.1 beta (gS D)

variable {D}

section PairAttr

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def Pair.pfst (p : Pair D u u' F0 what₂) : Term D u u' F0 what₂ := ⟨p.lam, p.mem, TermDef.mk _ _ _ p.fst⟩

def Pair.psnd (p : Pair D u u' F0 what₂) : Term D u u' F0 what₂ := ⟨p.lam, p.mem, TermDef.mk _ _ _ p.snd⟩

def Pair.s0 (p : Pair D u u' F0 what₂) : ℕ := Lat.s0 p.lam (lf D F0) p.fst.1 p.snd.1 p.beta D.R.k

def Pair.scalarPair (p : Pair D u u' F0 what₂) : Prop :=
  p.s0 = 1 ∧ IsScalar p.lam (lf D F0) p.fst.1 p.snd.1 p.beta

def Pair.isScalar (p : Pair D u u' F0 what₂) : Prop :=
  IsScalar p.lam (lf D F0) p.fst.1 p.snd.1 p.beta

theorem Pair.scalarPair_iff (p : Pair D u u' F0 what₂) : p.scalarPair ↔ p.s0 = 1 ∧ p.isScalar :=
  Iff.rfl

def reflPair (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂)
    (x : Carrier (PD D Λ (lf D F0) u')) (hx : Gval (lf D F0) x.1 ≠ 0) : Pair D u u' F0 what₂ :=
  ⟨Λ, hΛ, x, x, hx, hx, LinearEquiv.refl _ _, isPair_refl _ _ _ _⟩

theorem reflPair_terms (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂)
    (x : Carrier (PD D Λ (lf D F0) u')) (hx : Gval (lf D F0) x.1 ≠ 0) :
    (reflPair Λ hΛ x hx).pfst = ⟨Λ, hΛ, TermDef.mk _ _ _ x⟩ ∧ (reflPair Λ hΛ x hx).psnd = ⟨Λ, hΛ, TermDef.mk _ _ _ x⟩ :=
  ⟨rfl, rfl⟩

end PairAttr

variable (D)

def ScalRelD {u : D.what₂.Word} (u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (x y : {x : Carrier (PD D Λ (lf D F0) u') // Gval (lf D F0) x.1 ≠ 0}) : Prop :=
  ScalRel Λ (gS D) D.R.k (lf D F0) x.1.1 y.1.1

def CorankPos (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
    IsRowReps D F0 what₂ → ∀ p : Pair D u u' F0 what₂, 1 ≤ p.s0

def ScalarEquiv (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → Equivalence (ScalRelD D u' F0 Λ)

def BetaL (u u' : D.what₂.Word) : Prop :=
  (∀ i, 3 ≤ D.host.g i ∧ LemmaN.Unram D.host.E (D.host.g i)) →
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ x y : Carrier (PD D Λ (lf D F0) u'),
      Gval (lf D F0) x.1 ≠ 0 → Gval (lf D F0) y.1 ≠ 0 →
      ∀ β₁ β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V,
        IsPair Λ (lf D F0) x.1 y.1 β₁ (gS D) → IsPair Λ (lf D F0) x.1 y.1 β₂ (gS D) →
        ∀ v ∈ orth (VS D) (Xsp x.1), β₁ v - β₂ v ∈ Xsp y.1

def BetaFree (u u' : D.what₂.Word) : Prop :=
  (∀ i, 3 ≤ D.host.g i ∧ LemmaN.Unram D.host.E (D.host.g i)) →
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ x y : Carrier (PD D Λ (lf D F0) u'),
      Gval (lf D F0) x.1 ≠ 0 → Gval (lf D F0) y.1 ≠ 0 →
      ∀ β₁ β₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V,
        IsPair Λ (lf D F0) x.1 y.1 β₁ (gS D) → IsPair Λ (lf D F0) x.1 y.1 β₂ (gS D) →
        Lat.s0 Λ (lf D F0) x.1 y.1 β₁ D.R.k = Lat.s0 Λ (lf D F0) x.1 y.1 β₂ D.R.k ∧
        (IsScalar Λ (lf D F0) x.1 y.1 β₁ ↔ IsScalar Λ (lf D F0) x.1 y.1 β₂)

def ScalarRepFree (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ x y y' : {x : Carrier (PD D Λ (lf D F0) u') // Gval (lf D F0) x.1 ≠ 0},
      Rel Λ (lf D F0) (PD D Λ (lf D F0) u') y.1 y'.1 → ScalRelD D u' F0 Λ x y → ScalRelD D u' F0 Λ x y'

def TermScal {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (t₁ t₂ : Term D u u' F0 what₂) : Prop :=
  ∃ p : Pair D u u' F0 what₂, p.pfst = t₁ ∧ p.psnd = t₂ ∧ p.scalarPair

def ScalarEquivT (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
    IsRowReps D F0 what₂ →
      Equivalence (fun t₁ t₂ : {t : Term D u u' F0 what₂ // t.G ≠ 0} => TermScal D t₁.1 t₂.1)

def ScalarDr (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
    IsRowReps D F0 what₂ → ∀ p : Pair D u u' F0 what₂, p.scalarPair →
      (Dr (lf D F0) p.fst.1 = 0 ↔ Dr (lf D F0) p.snd.1 = 0)

variable {D}

theorem corankPos_of_G (h : CorankPosG) (u u' : D.what₂.Word) : CorankPos D u u' := by
  intro F0 what₂ hrows p
  have hΛ := hrows.1 p.lam p.mem
  exact h D.host.E (VS D) D.R.rS D.R.k (finrank_VS D) p.lam hΛ.2.1.1 _ _ (lf D F0) p.fst.1 p.snd.1 p.beta
    hΛ.2.1.2.2.1 p.fst.2.1 p.G_fst

theorem tu_ne_zero (u : D.what₂.Word) : ((Tu D u : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero

theorem scalarEquiv_of_G (h : ScalarEquivG) (u u' : D.what₂.Word) : ScalarEquiv D u u' := by
  intro F0 Λ hΛ
  have hlat : Submodule.IsLattice D.host.E Λ := hΛ.2.1.1
  have hlift : IsLift Λ (lf D F0) := hΛ.2.1.2.2.1
  have e := h D.host.E (VS D) D.R.rS D.R.k (gS D) (finrank_VS D) Λ hlat ((Tu D u : ℕ) : D.host.E)
    ((Tu D u' : ℕ) : D.host.E) (tu_ne_zero u) (tu_ne_zero u') (lf D F0) hlift
  refine ⟨fun x => ?_, fun {x y} hxy => ?_, fun {x y z} h1 h2 => ?_⟩
  · exact e.refl ⟨x.1.1, x.1.2.1, x.2⟩
  · exact e.symm (x := ⟨x.1.1, x.1.2.1, x.2⟩) (y := ⟨y.1.1, y.1.2.1, y.2⟩) hxy
  · exact e.trans (x := ⟨x.1.1, x.1.2.1, x.2⟩) (y := ⟨y.1.1, y.1.2.1, y.2⟩) (z := ⟨z.1.1, z.1.2.1, z.2⟩) h1 h2

theorem scalarEquivT_of {D : D7} {u u' : D.what₂.Word} (hEq : TermEqIff D u u') (hE : ScalarEquiv D u u')
    (hR : ScalarRepFree D u u') : ScalarEquivT D u u' := by
  intro F0 what₂ hrows
  refine ⟨fun t => ?_, fun {t₁ t₂} h => ?_, fun {t₁ t₂ t₃} h₁ h₂ => ?_⟩
  · obtain ⟨⟨lam, mem, cls⟩, hG⟩ := t
    have hΛ := hrows.1 lam mem
    have hx : Gval (lf D F0) (Quot.out cls).1 ≠ 0 := hG
    obtain ⟨β, hp, hs, hsc⟩ := (hE F0 lam hΛ).refl ⟨Quot.out cls, hx⟩
    refine ⟨⟨lam, mem, Quot.out cls, Quot.out cls, hx, hx, β, hp⟩, ?_, ?_, hs, hsc⟩
    · simp only [Pair.pfst]; congr 1; exact Quot.out_eq cls
    · simp only [Pair.psnd]; congr 1; exact Quot.out_eq cls
  · obtain ⟨p, h1, h2, hs, hsc⟩ := h
    have hΛ := hrows.1 p.lam p.mem
    obtain ⟨β, hp, hs', hsc'⟩ := (hE F0 p.lam hΛ).symm (x := ⟨p.fst, p.G_fst⟩) (y := ⟨p.snd, p.G_snd⟩)
      ⟨p.beta, p.isPair, hs, hsc⟩
    exact ⟨⟨p.lam, p.mem, p.snd, p.fst, p.G_snd, p.G_fst, β, hp⟩, h2, h1, hs', hsc'⟩
  · obtain ⟨p, hp1, hp2, hps, hpsc⟩ := h₁
    obtain ⟨q, hq1, hq2, hqs, hqsc⟩ := h₂
    have hpq : p.psnd = q.pfst := hp2.trans hq1.symm
    obtain ⟨lp, mp, p1, p2, gp1, gp2, bp, ip⟩ := p
    obtain ⟨lq, mq, q1, q2, gq1, gq2, bq, iq⟩ := q
    simp only [Pair.psnd, Pair.pfst, Term.mk.injEq] at hpq
    obtain ⟨rfl, hcls⟩ := hpq
    have hcls' : TermDef.mk lp (lf D F0) (PD D lp (lf D F0) u') p2 = TermDef.mk lp (lf D F0) (PD D lp (lf D F0) u') q1 :=
      eq_of_heq hcls
    have hΛ := hrows.1 lp mp
    have hrel := (hEq F0 lp hΛ p2 q1).1 hcls'
    have a1 : ScalRelD D u' F0 lp ⟨p1, gp1⟩ ⟨p2, gp2⟩ := ⟨bp, ip, hps, hpsc⟩
    have a2 : ScalRelD D u' F0 lp ⟨p1, gp1⟩ ⟨q1, gq1⟩ := hR F0 lp hΛ ⟨p1, gp1⟩ ⟨p2, gp2⟩ ⟨q1, gq1⟩ hrel a1
    have a3 : ScalRelD D u' F0 lp ⟨q1, gq1⟩ ⟨q2, gq2⟩ := ⟨bq, iq, hqs, hqsc⟩
    obtain ⟨β, hb, hs, hsc⟩ := (hE F0 lp hΛ).trans a2 a3
    exact ⟨⟨lp, mp, p1, q2, gp1, gq2, β, hb⟩, hp1, hq2, hs, hsc⟩

end D7

end Formalism.L2.SG.Corank
