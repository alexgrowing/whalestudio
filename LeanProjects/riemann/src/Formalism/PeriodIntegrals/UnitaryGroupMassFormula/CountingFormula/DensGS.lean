import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensAtGoodOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DensSplit

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

def SplitCount : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    (∃ e : E ≃ₐ[F] F × F, ∀ x, e (M.L.cj x) = (e x).swap) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
        ∃ (Ph : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) 𝓀[F])
          (Gm : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝓀[F]),
          IsUnit Ph.det ∧ Gm.rank = Fintype.card ι ∧
          H.dens ϖ Λ G₀ * (Nat.card 𝓀[F] : ℝ) ^
              ((2 * Module.finrank E V * Fintype.card ι : ℤ) - (Fintype.card ι : ℤ) ^ 2) =
            (Formalism.L2.SG.DensExact.countSplit 𝓀[F] (Module.finrank E V) (Fintype.card ι) Ph Gm : ℝ)

theorem locDensSplit_of (h : SplitCount) : LocDensSplit := by
  intro F E _ _ _ _ _ _ _ M hF hc0 he V _ _ H Λ hΛ ϖ hϖ ι _ _ G₀ hG1 hG2 hG3 hle
  obtain ⟨Ph, Gm, hPh, hrk, heq⟩ := h F E M hF hc0 he V H Λ hΛ ϖ hϖ ι G₀ hG1 hG2 hG3 hle
  haveI := hF
  haveI : Fintype 𝓀[F] := Fintype.ofFinite _
  have hd := bilinearDensityFormula 𝓀[F] (Module.finrank E V) (Fintype.card ι) Ph Gm hPh
  rw [hrk, Nat.sub_self, ← Nat.card_eq_fintype_card (α := 𝓀[F])] at hd
  rw [← hd, ← heq]
  have hq : (Nat.card 𝓀[F] : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := 𝓀[F])).ne'
  have hz : ((2 * Module.finrank E V * Fintype.card ι : ℤ) - (Fintype.card ι : ℤ) ^ 2) =
      ((2 * Module.finrank E V * Fintype.card ι : ℕ) : ℤ) - ((Fintype.card ι ^ 2 : ℕ) : ℤ) := by
    first | (push_cast; ring) | push_cast
  rw [hz, zpow_sub₀ hq, zpow_natCast, zpow_natCast, mul_div_assoc,
    div_self (div_ne_zero (pow_ne_zero _ hq) (pow_ne_zero _ hq)), mul_one]

def OSplit : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E), IsNonarchimedeanLocalField F →
    ∀ (e : E ≃ₐ[F] F × F) (x : E), x ∈ L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]

def IsSplitCoord {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} (e : E ≃ₐ[F] F × F)
    {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) {n : ℕ}
    (π : V ≃+ (Fin n → F) × (Fin n → F)) (Ph : Matrix (Fin n) (Fin n) 𝒪[F]) : Prop :=
  (∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2)) ∧
  (∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) ∧
  IsUnit Ph.det ∧
  ∀ x y : V, e (H.h x y) =
    (∑ k, ∑ l, (π x).1 k * (Ph k l : F) * (π y).2 l, ∑ k, ∑ l, (π y).1 k * (Ph k l : F) * (π x).2 l)

def CoordData : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    ∀ (e : E ≃ₐ[F] F × F), (∀ x, e (M.L.cj x) = (e x).swap) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ →
      ∃ (π : V ≃+ (Fin (Module.finrank E V) → F) × (Fin (Module.finrank E V) → F))
        (Ph : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) 𝒪[F]), IsSplitCoord e H Λ π Ph

def CountBij : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    ∀ (e : E ≃ₐ[F] F × F), (∀ x, e (M.L.cj x) = (e x).swap) →
    (∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V)
      (π : V ≃+ (Fin (Module.finrank E V) → F) × (Fin (Module.finrank E V) → F))
      (Ph : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) 𝒪[F]), IsSplitCoord e H Λ π Ph →
      ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        ∃ Gm : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝓀[F], Gm.rank = Fintype.card ι ∧
          H.dens ϖ Λ G₀ * (Nat.card 𝓀[F] : ℝ) ^
              ((2 * Module.finrank E V * Fintype.card ι : ℤ) - (Fintype.card ι : ℤ) ^ 2) =
            (Formalism.L2.SG.DensExact.countSplit 𝓀[F] (Module.finrank E V) (Fintype.card ι)
              (Ph.map (IsLocalRing.residue 𝒪[F])) Gm : ℝ)

theorem splitCount_of (hO : OSplit) (hC : CoordData) (hB : CountBij) : SplitCount := by
  intro F E _ _ _ _ _ _ _ M hF hc0 ⟨e, he⟩ V _ _ H Λ hΛ ϖ hϖ ι _ _ G₀ hG1 hG2 hG3 _
  obtain ⟨π, Ph, hπ⟩ := hC F E M hF hc0 e he V H Λ hΛ
  obtain ⟨Gm, hGm, heq⟩ := hB F E M hF hc0 e he (hO F E M.L hF e) V H Λ π Ph hπ ϖ hϖ ι G₀ hG1 hG2 hG3
  obtain ⟨-, -, hu, -⟩ := hπ
  refine ⟨Ph.map (IsLocalRing.residue 𝒪[F]), Gm, ?_, hGm, heq⟩
  have hdet : (Ph.map (IsLocalRing.residue 𝒪[F])).det = IsLocalRing.residue 𝒪[F] Ph.det :=
    (RingHom.map_det _ _).symm
  rw [hdet]
  exact hu.map _

theorem locDensSplit_of' (hO : OSplit) (hC : CoordData) (hB : CountBij) : LocDensSplit := locDensSplit_of (splitCount_of hO hC hB)

end PI.UnitaryGroupMassFormula.CntFormula
