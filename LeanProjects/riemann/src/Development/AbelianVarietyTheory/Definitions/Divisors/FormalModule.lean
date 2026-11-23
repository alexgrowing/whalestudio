import Mathlib

noncomputable section

open PowerSeries

namespace GlobalTheory.FOM

section Basic

variable {R : Type*} [CommRing R]

abbrev atX (f : PowerSeries R) : MvPowerSeries (Fin 2) R := f.subst (MvPowerSeries.X (0 : Fin 2))

abbrev atY (f : PowerSeries R) : MvPowerSeries (Fin 2) R := f.subst (MvPowerSeries.X (1 : Fin 2))

def IsHom (F G : FormalGroup R) (f : PowerSeries R) : Prop :=
  constantCoeff f = 0 ∧ f.subst F.toPowerSeries = G.toPowerSeries.subst ![atX f, atY f]

def addF (F : FormalGroup R) (f g : PowerSeries R) : PowerSeries R :=
  F.toPowerSeries.subst ![f, g]

end Basic

structure FormalModule (O : Type*) [CommRing O] (R : Type*) [CommRing R] [Algebra O R] where
  F : FormalGroup R
  comm : F.IsComm
  act : O → PowerSeries R
  act_hom : ∀ a, IsHom F F (act a)
  act_lin : ∀ a, coeff 1 (act a) = algebraMap O R a
  act_one : act 1 = X
  act_mul : ∀ a b, act (a * b) = (act a).subst (act b)
  act_add : ∀ a b, act (a + b) = addF F (act a) (act b)

variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] [Algebra O R]

def IsModHom (M N : FormalModule O R) (f : PowerSeries R) : Prop :=
  IsHom M.F N.F f ∧ ∀ a : O, f.subst (M.act a) = (N.act a).subst f

def WDeg (m : Ideal R) (f : PowerSeries R) (d : ℕ) : Prop :=
  (∀ n < d, coeff n f ∈ m) ∧ IsUnit (coeff d f)

def HasHeight (m : Ideal R) (M : FormalModule O R) (ϖ : O) (q h : ℕ) : Prop :=
  WDeg m (M.act ϖ) (q ^ h)

def chainComp {h : ℕ} (f : Fin h → PowerSeries R) : PowerSeries R :=
  (List.finRange h).foldl (fun g i => (f i).subst g) X

structure IsoChain (m : Ideal R) (ϖ : O) (q h : ℕ) where
  M : Fin (h + 1) → FormalModule O R
  f : Fin h → PowerSeries R
  hom : ∀ i : Fin h, IsModHom (M i.castSucc) (M i.succ) (f i)
  deg : ∀ i : Fin h, WDeg m (f i) q
  closed : M (Fin.last h) = M 0
  comp : chainComp f = (M 0).act ϖ

end GlobalTheory.FOM

namespace GlobalTheory.FOM

section Image

variable {O : Type*} [CommRing O] {R S : Type*} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]

def IsImage (φ : R →+* S) (M : FormalModule O R) (N : FormalModule O S) : Prop :=
  N.F.toPowerSeries = MvPowerSeries.map φ M.F.toPowerSeries ∧
    ∀ a : O, N.act a = PowerSeries.map φ (M.act a)

def IsChainImage {mR : Ideal R} {mS : Ideal S} {ϖ : O} {q h : ℕ} (φ : R →+* S)
    (C : IsoChain (O := O) mR ϖ q h) (D : IsoChain (O := O) mS ϖ q h) : Prop :=
  (∀ i, IsImage φ (C.M i) (D.M i)) ∧ ∀ i, D.f i = PowerSeries.map φ (C.f i)

def IsStar (m : Ideal R) (u : PowerSeries R) : Prop :=
  ∀ n : ℕ, coeff n u - coeff n (X : PowerSeries R) ∈ m

def StarIso {m : Ideal R} {ϖ : O} {q h : ℕ} (C D : IsoChain (O := O) m ϖ q h) : Prop :=
  ∃ u : Fin (h + 1) → PowerSeries R, (∀ i, IsStar m (u i)) ∧ (∀ i, IsModHom (C.M i) (D.M i) (u i)) ∧
    u (Fin.last h) = u 0 ∧ ∀ i : Fin h, (D.f i).subst (u i.castSucc) = (u i.succ).subst (C.f i)

end Image

section Ring

variable (Ob : Type*) [CommRing Ob]

def relIdeal (h : ℕ) (w : Ob) : Ideal (MvPowerSeries (Fin h) Ob) :=
  Ideal.span {(∏ i : Fin h, MvPowerSeries.X i) - MvPowerSeries.C w}

abbrev IwRing (h : ℕ) (w : Ob) : Type _ := MvPowerSeries (Fin h) Ob ⧸ relIdeal Ob h w

variable [IsLocalRing Ob]

def iwRed (h : ℕ) (hh : 1 ≤ h) (w : Ob) (hw : w ∈ IsLocalRing.maximalIdeal Ob) :
    IwRing Ob h w →+* IsLocalRing.ResidueField Ob :=
  Ideal.Quotient.lift (relIdeal Ob h w) ((IsLocalRing.residue Ob).comp MvPowerSeries.constantCoeff) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have h0 : MvPowerSeries.constantCoeff (∏ i : Fin h, (MvPowerSeries.X i : MvPowerSeries (Fin h) Ob)) = 0 := by
      rw [map_prod]
      exact Finset.prod_eq_zero (i := ⟨0, hh⟩) (Finset.mem_univ _) (by simp)
    simp [map_mul, map_sub, h0, (IsLocalRing.residue_eq_zero_iff w).mpr hw]
    exact Or.inr (by omega))

def iwMax (h : ℕ) (hh : 1 ≤ h) (w : Ob) (hw : w ∈ IsLocalRing.maximalIdeal Ob) : Ideal (IwRing Ob h w) :=
  RingHom.ker (iwRed Ob h hh w hw)

end Ring

end GlobalTheory.FOM
