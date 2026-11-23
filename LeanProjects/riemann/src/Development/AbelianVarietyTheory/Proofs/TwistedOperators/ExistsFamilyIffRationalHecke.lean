import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeTieCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.FWT
  Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Local

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def IndexPlace (P : PlE D.host) : Prop :=
  IsSplitPl D.host P ∧ Bridge.SplitOff P (R.Sb : Set (Pl D.host.E)) ∧ (∃ i', P ∉ D.ntw.S0 i') ∧
    ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal

variable {WL : ℕ → Type} [∀ j, AddCommGroup (WL j)] [∀ j, Module D.what₂.LL (WL j)]
  (e : ∀ i : Fin D.R.m, WL ((i : ℕ) + 1) ≃ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL))

def FamilyTie (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (WL j)) : Prop :=
  ∀ (i : Fin D.R.m) (k : ℕ) (P : PlE D.host), IsSplitPl D.host P → Bridge.SplitOff P (R.Sb : Set (Pl D.host.E)) →
    (∃ i', P ∉ D.ntw.S0 i') → ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → k ≤ D.R.r →
    ∀ (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))), IsHeckeAt (Wc D i) P k α →
      Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
      ∀ x : WL ((i : ℕ) + 1), (LinearMap.id : WL ((i : ℕ) + 1) →ₗ[D.what₂.LL] WL ((i : ℕ) + 1)) x = x →
        (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (e i (hL ((i : ℕ) + 1) k P x))) =
          (((((R.C.mu0 i).val P : ℂˣ) : ℂ))⁻¹ ^ k * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
            heckeOn (R.MW i (sg0 D A)) Rc ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (e i x)))

def FamilyKeeps (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (WL j)) : Prop :=
  ∀ (i : Fin D.R.m) (k : ℕ) (P : PlE D.host), IndexPlace R P → k ≤ D.R.r →
    ∀ x : WL ((i : ℕ) + 1), e i x ∈ (R.FW i).WK → e i (hL ((i : ℕ) + 1) k P x) ∈ (R.FW i).WK

theorem isSplitPl_iff (P : PlE D.host) :
    IsSplitPl D.host P ↔ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal := by
  have hc : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = (GlobalTheory.SplitOffPlaces.conjSpec P).asIdeal := by
    rw [Formalism.L2.Col.conjIdeal_eq]; rfl
  rw [hc]
  constructor
  · rintro ⟨x, hx, h⟩ he
    refine h (Formalism.L2.Col.cO D.host.E x) (bridge_star_holds D.R D.host _) ?_
    rw [← he] at hx
    exact hx
  · intro hne
    by_contra h
    refine hne (P.isMaximal.eq_of_le (GlobalTheory.SplitOffPlaces.conjSpec P).isPrime.ne_top fun x hx => ?_).symm
    by_contra hx'
    refine h ⟨x, hx, fun y hy hyP => hx' ?_⟩
    have : y = Formalism.L2.Col.cO D.host.E x := RingOfIntegers.ext (hy.trans (bridge_star_holds D.R D.host _).symm)
    rw [this] at hyP
    exact hyP

theorem level_notMem {P : PlE D.host} (h : ∃ i', P ∉ D.ntw.S0 i') :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  obtain ⟨i', hi⟩ := h
  intro hm
  rw [Nat.cast_mul] at hm
  rcases P.isPrime.mem_or_mem hm with h | h
  · exact hi (D.ntw.placesOver_subset_exceptional i' 0 h)
  · exact hi (D.ntw.placesOver_subset_exceptional i' 1 h)

theorem scalar_eq (i : Fin D.R.m) (P : PlE D.host) (k : ℕ) :
    (((R.C.mu0 i).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹ = heckeScalar R i P k := by
  rw [heckeScalar, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_pow]

theorem exists_family (t : ∀ i : Fin D.R.m, ℕ → PlE D.host → Module.End D.what₂.LL (Fin (R.nW i) → D.what₂.LL)) :
    ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (WL j),
      ∀ (i : Fin D.R.m) k P, (e i).conj (hL ((i : ℕ) + 1) k P) = t i k P := by
  refine ⟨fun j => match j with
    | 0 => fun _ _ => 0
    | n + 1 => fun k P => if h : n < D.R.m then (e ⟨n, h⟩).symm.conj (t ⟨n, h⟩ k P) else 0, fun i k P => ?_⟩
  simp only [dif_pos i.2]
  exact (e i).conj.apply_symm_apply (t i k P)

end Local

section Comparison₂

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  {WL : ℕ → Type} [∀ j, AddCommGroup (WL j)] [∀ j, Module D.what₂.LL (WL j)]
  (e : ∀ i : Fin D.R.m, WL ((i : ℕ) + 1) ≃ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL))

end Comparison₂

end GlobalTheory.HeckeTieCompare
