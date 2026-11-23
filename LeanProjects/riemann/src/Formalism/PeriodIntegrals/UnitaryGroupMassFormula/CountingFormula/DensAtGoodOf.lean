import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LocalModelsSplitCofinite

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocDens : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
        ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
          H.dens ϖ Λ G₀ = Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) η
            (Module.finrank E V) (Fintype.card ι) 0

def ETwo : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E),
    (∀ x : E, x ≠ 0 → IsUnit x) ∨ ∃ e : E ≃ₐ[F] F × F, ∀ x, e (L.cj x) = (e x).swap

def LocDensSplit : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    (∃ e : E ≃ₐ[F] F × F, ∀ x, e (M.L.cj x) = (e x).swap) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
          H.dens ϖ Λ G₀ = Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) 1
            (Module.finrank E V) (Fintype.card ι) 0

def LocDensField : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    (∀ x : E, x ≠ 0 → IsUnit x) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
          H.dens ϖ Λ G₀ = Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) (-1)
            (Module.finrank E V) (Fintype.card ι) 0

theorem locDens_of (h0 : ETwo) (hS : LocDensSplit) (hF : LocDensField) : LocDens := by
  intro F E _ _ _ _ _ _ _ M hl hc V _ _ H Λ hΛ ϖ hϖ ι _ _ G₀ h1 h2 h3 h4
  rcases h0 F E M.L with hE | hE
  · exact ⟨-1, Or.inr rfl, hF F E M hl hc hE V H Λ hΛ ϖ hϖ ι G₀ h1 h2 h3 h4⟩
  · exact ⟨1, Or.inl rfl, hS F E M hl hc hE V H Λ hΛ ϖ hϖ ι G₀ h1 h2 h3 h4⟩

theorem star_eq_conjF (D : Formalism.BasicNotions.D7) (x : D.host.E) : star x = D.conjF x := by
  rw [D.conjF_eq]
  have := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  change D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj]
  exact (D.host.toHostAx.conjE_apply D.host.φ₀ x).symm

theorem ga_herm (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (Z : MatZ D) (a b) :
    Ga (Tn u) (Tn u') Z b a = star (Ga (Tn u) (Tn u') Z a b) := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Ga, Matrix.fromBlocks, Matrix.conjTranspose_apply, and_comm] <;> split_ifs <;> simp [Tn]

theorem gaPlus_herm (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D) (hA : Agree δ M p)
    (hs : (M p).split = none) (u u' : D.what₂.Word) (Z : MatZ D) (a b) :
    GaPlus M δ p (Tn u) (Tn u') Z b a = (M p).L.cj (GaPlus M δ p (Tn u) (Tn u') Z a b) := by
  have hcj : (M p).L.cj = (D.s.atP p).cj := hA.2.2.1
  simp only [GaPlus, hs, GaLoc, Matrix.of_apply]
  rw [map_mul, map_mul, hcj, (D.s.atP p).cj_ιE, ← star_eq_conjF, ← ga_herm, ← hcj, (M p).L.cj_cj]
  ring

theorem densAtGood_at (h : LocDens) (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (L : LocSp D M)
    (u u' : D.what₂.Word) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (hϖ : ∀ p, Irreducible (ϖ p))
    (Z : MatZ D) (p : PlF D) (hG : GoodAt L δ (Tn u) (Tn u') Z p) :
    ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
      densP L δ ϖ (Tn u) (Tn u') Z p =
        Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[(D.s.atP p).Fp]) η D.R.r (2 * (D.R.rS + 1)) 0 := by
  obtain ⟨hs, hSD, hI, hdet⟩ := hG
  have hl : IsNonarchimedeanLocalField (D.s.atP p).Fp := (D.s.atP p).lf
  have hc : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
  have hcard : Fintype.card (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) = 2 * (D.R.rS + 1) := by
    rw [Fintype.card_sum, Fintype.card_fin]; ring
  have hr : Module.finrank (D.s.atP p).Ep (L.V p) = D.R.r := L.rank p
  have hm : Fintype.card (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) ≤ Module.finrank (D.s.atP p).Ep (L.V p) := by
    rw [hcard, hr]; have := tuple_short D; omega
  have hh := gaPlus_herm D δ M p (hA p) hs u u' Z
  obtain ⟨η, hη, he⟩ := h (D.s.atP p).Fp (D.s.atP p).Ep (M p) hl hc (L.V p) (L.H p) (lattice₂ L p (VS D).L0) hSD
    (ϖ p) (hϖ p) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (GaPlus M δ p (Tn u) (Tn u') Z) hI hh
    hdet hm
  refine ⟨η, hη, ?_⟩
  rw [hr, hcard] at he
  exact he

theorem densAtGood_of (h : LocDens) : DensAtGood :=
  fun D δ M hA L u u' _ _ _ _ ϖ hϖ Z p hG => densAtGood_at h D δ M hA L u u' ϖ hϖ Z p hG

theorem densAtGood_of' (h0 : ETwo) (hS : LocDensSplit) (hF : LocDensField) : DensAtGood :=
  densAtGood_of (locDens_of h0 hS hF)

end PI.UnitaryGroupMassFormula.CntFormula
