import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HeckeJ
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Local

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def heckeScalar (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) : ℂ :=
  (((R.C.mu0 i).val P : ℂˣ) : ℂ) ^ (-(k : ℤ)) * ((Nat.card (kP P) : ℕ) : ℂ) ^ (-((k * (D.R.nV / 2) : ℕ) : ℤ))

def GoodPlace (P : Pl D.host.E) : Prop :=
  Bridge.SplitOff P (R.Sb : Set (Pl D.host.E)) ∧ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal

def IsCosetSys (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i))) : Prop :=
  ∃ α : GA D (Wc D i), IsHeckeAt (Wc D i) P k α ∧ Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc

def ReadAs (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i)))
    (hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) : Prop :=
  HeckeJ.IsHkJ (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (heckeOn (R.MW i (sg0 D A)) Rc) (heckeScalar R i P k) hL

def RationalHeckeAt (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) : Prop :=
  ∃ hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL),
    (∀ Rc, IsCosetSys R i P k Rc → ReadAs R i P k Rc hL) ∧ ∀ x ∈ (R.FW i).WK, hL x ∈ (R.FW i).WK

def RationalHecke (i : Fin D.R.m) : Prop :=
  ∀ P : Pl D.host.E, GoodPlace R P → ∀ k : ℕ, k ≤ D.R.r → RationalHeckeAt R i P k

theorem readAs_iff (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i)))
    (hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL)) :
    ReadAs R i P k Rc hL ↔ ∀ x, (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (hL x)) =
      heckeScalar R i P k • heckeOn (R.MW i (sg0 D A)) Rc ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) x)) := Iff.rfl

theorem RationalHeckeAt.row {i : Fin D.R.m} {P : Pl D.host.E} {k : ℕ} (h : RationalHeckeAt R i P k)
    {α : GA D (Wc D i)} (hα : IsHeckeAt (Wc D i) P k α) {Rc : Finset (GA D (Wc D i))}
    (hR : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc) :
    HeckeJ.HkJRow (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i (sg0 D A)).e (heckeOn (R.MW i (sg0 D A)) Rc)
      (heckeScalar R i P k) (R.FW i).WK := by
  obtain ⟨hL, h1, h2⟩ := h
  exact ⟨hL, h1 Rc ⟨α, hα, hR⟩, h2⟩

theorem heckeScalar_zero (i : Fin D.R.m) (P : Pl D.host.E) : heckeScalar R i P 0 = 1 := by
  simp [heckeScalar]

theorem readAs_id (i : Fin D.R.m) (P : Pl D.host.E) : ReadAs R i P 0 {1} LinearMap.id := by
  intro x
  rw [heckeScalar_zero, one_smul]
  ext v g
  simp [heckeOn, postOn, heckeLin]

end Local

section Comparison₂

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def RationalHeckeUnpinned : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → ∀ i : Fin D.R.m, RationalHecke R i

def FramePinned (i : Fin D.R.m) : Prop :=
  ∃ O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0), OMPins T R κ v₀ O i ∧ CTie T R κ v₀ O i

def RationalHeckeTie : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → ∀ i : Fin D.R.m, FramePinned T R κ v₀ i → RationalHecke R i

theorem RationalHeckeUnpinned.tie (h : RationalHeckeUnpinned T R F κ v₀) : RationalHeckeTie T R F κ v₀ :=
  fun hc ht i _ => h hc ht i

end Comparison₂

def RationalHeckeTieAll : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    RationalHeckeTie T R F κ v₀

end GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars
