import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix

namespace GlobalTheory.FrameModel

variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]

def embVal (hv : v.Integers O) {Λ : Type} [CommRing Λ] (α : Λ) :
    (Λ →+* O) → v.valuationSubring :=
  fun σ => ⟨algebraMap O C (σ α), (Valuation.mem_valuationSubring_iff _ _).2 (hv.map_le_one _)⟩

theorem coe_embVal (hv : v.Integers O) {Λ : Type} [CommRing Λ] (α : Λ) (σ : Λ →+* O) :
    (embVal v hv α σ : C) = algebraMap O C (σ α) := rfl

def modelLattice {S : Type} {h N : ℕ} (Φ : (Fin h → C) ≃ₗ[C] (S → Fin N → C))
    (L : Submodule O (Fin h → O)) : Submodule v.valuationSubring (S → Fin N → C) :=
  Submodule.span v.valuationSubring ((fun t => Φ (incl C h t)) '' (L : Set (Fin h → O)))

theorem mem_span_valuationSubring_iff (hv : v.Integers O) {W : Type} [AddCommGroup W] [Module C W]
    [Module O W] [IsScalarTower O C W] [Module v.valuationSubring W]
    [IsScalarTower v.valuationSubring C W] (s : Set W) (x : W) :
    x ∈ Submodule.span v.valuationSubring s ↔ x ∈ Submodule.span O s := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      obtain ⟨o, ho⟩ := hv.exists_of_le_one ((Valuation.mem_valuationSubring_iff _ _).1 c.2)
      have : c • x = o • x := by
        rw [← algebraMap_smul C c x, ← algebraMap_smul C o x, ho]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ hx
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul o x _ hx =>
      let c : v.valuationSubring :=
        ⟨algebraMap O C o, (Valuation.mem_valuationSubring_iff _ _).2 (hv.map_le_one _)⟩
      have : o • x = c • x := by
        rw [← algebraMap_smul C c x, ← algebraMap_smul C o x]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ hx

theorem mem_modelLattice (hv : v.Integers O) {S : Type} {h N : ℕ}
    (Φ : (Fin h → C) ≃ₗ[C] (S → Fin N → C)) (L : Submodule O (Fin h → O)) (w : S → Fin N → C) :
    w ∈ modelLattice v Φ L ↔ ∃ t ∈ L, Φ (incl C h t) = w := by
  unfold modelLattice
  rw [mem_span_valuationSubring_iff v hv]
  have : (fun t => Φ (incl C h t)) '' (L : Set (Fin h → O)) =
      (L.map ((Φ.toLinearMap.restrictScalars O) ∘ₗ incl C h) : Set (S → Fin N → C)) := by
    rw [Submodule.map_coe]; rfl
  rw [this, Submodule.span_eq, Submodule.mem_map]
  rfl

theorem mem_eig_iff {Λ : Type} [CommRing Λ] {h : ℕ} (ρ : Λ → Matrix (Fin h) (Fin h) O)
    (τ : Λ →+* O) (x : Fin h → C) :
    x ∈ eig C ρ τ ↔ ∀ l, (ρ l).map (algebraMap O C) *ᵥ x = algebraMap O C (τ l) • x := by
  simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

theorem mem_eig_iff_support (hv : v.Integers O) {Λ : Type} [CommRing Λ] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (x : Fin h → C) : x ∈ eig C ρ τ ↔ ∀ σ, σ ≠ τ → Φ x σ = 0 := by
  rw [mem_eig_iff]
  constructor
  · intro hx σ hσ
    obtain ⟨l, hl⟩ : ∃ l, σ l ≠ τ l := by
      by_contra hc
      push Not at hc
      exact hσ (RingHom.ext hc)
    have e := hΦ l x σ
    rw [hx l, map_smul, Pi.smul_apply, ← sub_eq_zero, ← sub_smul, smul_eq_zero] at e
    rcases e with e | e
    · exact absurd (hv.hom_inj (sub_eq_zero.1 e)).symm hl
    · exact e
  · intro hx l
    apply Φ.injective
    funext σ
    rw [hΦ, map_smul, Pi.smul_apply]
    by_cases hσ : σ = τ
    · rw [hσ]
    · rw [hx σ hσ, smul_zero, smul_zero]

theorem mem_freeLattice_iff (hv : v.Integers O) {Λ : Type} [CommRing Λ] (α : Λ) {h N : ℕ}
    (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ z, (∀ i, z i ∈ (algebraMap O C).range) ↔
      ∀ i, ∃ f : Polynomial O, ∀ σ, Φ z σ i = algebraMap O C (f.eval (σ α)))
    (w : (Λ →+* O) → Fin N → C) :
    w ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice (embVal v hv α) N ↔
      ∃ t : Fin h → O, Φ (incl C h t) = w := by
  let j : O →+* v.valuationSubring := (algebraMap O C).codRestrict v.valuationSubring
    fun o => (Valuation.mem_valuationSubring_iff _ _).2 (hv.map_le_one _)
  have hj : Function.Surjective j := fun c => by
    obtain ⟨o, ho⟩ := hv.exists_of_le_one ((Valuation.mem_valuationSubring_iff _ _).1 c.2)
    exact ⟨o, Subtype.ext ho⟩
  have key : ∀ (f : Polynomial O) (σ : Λ →+* O),
      (((f.map j).eval (embVal v hv α σ) : v.valuationSubring) : C) =
        algebraMap O C (f.eval (σ α)) := by
    intro f σ
    have : embVal v hv α σ = j (σ α) := rfl
    rw [this, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rfl
  constructor
  · intro hw
    have : ∀ i, Φ.symm w i ∈ (algebraMap O C).range := by
      rw [hΦ]
      intro i
      obtain ⟨f, hf⟩ := hw i
      obtain ⟨g, rfl⟩ := Polynomial.map_surjective j hj f
      exact ⟨g, fun σ => by rw [Φ.apply_symm_apply, hf, key]⟩
    choose t ht using this
    refine ⟨t, ?_⟩
    have : incl C h t = Φ.symm w := funext ht
    rw [this, Φ.apply_symm_apply]
  · rintro ⟨t, rfl⟩ i
    obtain ⟨f, hf⟩ := (hΦ (incl C h t)).1 (fun i => ⟨t i, rfl⟩) i
    exact ⟨f.map j, fun σ => by rw [hf, key]⟩

theorem mulVec_incl {h k : ℕ} (X : Matrix (Fin k) (Fin h) O) (t : Fin h → O) :
    X.map (algebraMap O C) *ᵥ incl C h t = incl C k (X *ᵥ t) := by
  funext i
  show _ = algebraMap O C ((X *ᵥ t) i)
  rw [RingHom.map_mulVec]
  rfl

theorem incl_injective (hv : v.Integers O) (h : ℕ) :
    Function.Injective (incl C h : (Fin h → O) → (Fin h → C)) := by
  intro u u' e
  funext i
  exact hv.hom_inj (congrFun e i)

theorem exists_smul_eq_incl (hv : v.Integers O) {h : ℕ} (y : Fin h → C) :
    ∃ (o : O) (t : Fin h → O), algebraMap O C o ≠ 0 ∧ incl C h t = algebraMap O C o • y := by
  haveI : IsDomain O := hv.hom_inj.isDomain
  haveI : IsFractionRing O C := hv.isFractionRing
  obtain ⟨o, ho⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) y
  choose t ht using ho
  refine ⟨o, t, fun e => nonZeroDivisors.coe_ne_zero o (hv.hom_inj (by rw [e, map_zero])), ?_⟩
  funext i
  show algebraMap O C (t i) = _
  rw [ht i, Pi.smul_apply, algebraMap_smul]

theorem mem_iSup_eig_iff (hv : v.Integers O) {Λ : Type} [CommRing Λ] [Finite (Λ →+* O)] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (x : Fin h → C) :
    x ∈ (⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ σ.1) ↔ Φ x τ = 0 := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.iSup_induction' with
    | mem σ x hx => exact (mem_eig_iff_support v hv ρ Φ hΦ σ.1 x).1 hx τ σ.2.symm
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, Pi.add_apply, hx, hy, add_zero]
  · intro hx
    letI := Fintype.ofFinite (Λ →+* O)
    have e : x = ∑ σ, Φ.symm (Pi.single σ (Φ x σ)) := by
      rw [← map_sum, Finset.univ_sum_single, Φ.symm_apply_apply]
    rw [e]
    refine sum_mem fun σ _ => ?_
    by_cases hσ : σ = τ
    · rw [hσ, hx, Pi.single_zero, map_zero]
      exact zero_mem _
    · refine Submodule.mem_iSup_of_mem (⟨σ, hσ⟩ : {σ : Λ →+* O // σ ≠ τ}) ?_
      rw [mem_eig_iff_support v hv ρ Φ hΦ]
      intro s hs
      rw [Φ.apply_symm_apply, Pi.single_eq_of_ne hs]

theorem exists_eig_apply_eq (hv : v.Integers O) {Λ : Type} [CommRing Λ] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (w : Fin N → C) : ∃ x ∈ eig C ρ τ, Φ x τ = w := by
  classical
  refine ⟨Φ.symm (Pi.single τ w), ?_, by rw [Φ.apply_symm_apply, Pi.single_eq_same]⟩
  rw [mem_eig_iff_support v hv ρ Φ hΦ]
  intro s hs
  rw [Φ.apply_symm_apply, Pi.single_eq_of_ne hs]

theorem eq_zero_of_apply_eq_zero (hv : v.Integers O) {Λ : Type} [CommRing Λ] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (x : Fin h → C) (hx : x ∈ eig C ρ τ) (h0 : Φ x τ = 0) : x = 0 := by
  apply Φ.injective
  funext σ
  rw [map_zero, Pi.zero_apply]
  by_cases hσ : σ = τ
  · rw [hσ, h0]
  · exact (mem_eig_iff_support v hv ρ Φ hΦ τ x).1 hx σ hσ

theorem mem_eigPart_iff (hv : v.Integers O) {Λ : Type} [CommRing Λ] [Finite (Λ →+* O)] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (L : Submodule O (Fin h → O)) (x : Fin h → C) :
    x ∈ eigPart C ρ τ L ↔ x ∈ eig C ρ τ ∧ ∃ t ∈ L, Φ (incl C h t) τ = Φ x τ := by
  unfold eigPart
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_sup]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, r, hr, rfl⟩
    rw [Submodule.restrictScalars_mem, mem_iSup_eig_iff v hv ρ Φ hΦ] at hr
    exact ⟨t, ht, by rw [map_add, Pi.add_apply, hr, add_zero]⟩
  · rintro ⟨t, ht, e⟩
    refine ⟨_, ⟨t, ht, rfl⟩, x - incl C h t, ?_, by abel⟩
    rw [Submodule.restrictScalars_mem, mem_iSup_eig_iff v hv ρ Φ hΦ, map_sub, Pi.sub_apply, e,
      sub_self]

end GlobalTheory.FrameModel
