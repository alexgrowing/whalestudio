import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinRepsProjectiveFinrankLeNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellGeneratorsSmulMemOtherCellConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellGeneratorMemConeOfSmulCombinationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosSmulEqOfLinearIndependentConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveBalancedFormEqOfSameRayStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.CellClass

section Transport

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [AddCommGroup X₁] [Module O X₁]

theorem isCell_pull_equiv [Module.Finite O X] [Module.Finite O X₁] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsCell bar φ γ) (e : X ≃ₗ[O] X₁) : IsCell bar φ fun i => pull e.toLinearMap (γ i) :=
  ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, (linearOn_pull_iff e.surjective).2 h.linear,
    IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩

def pullLin (r : X →ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pull r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pull_injective {r : X →ₗ[O] X₁} (hr : Function.Surjective r) : Function.Injective (pull r : LinearMap.BilinForm ℤ X₁ → LinearMap.BilinForm ℤ X) := by
  intro β β' h
  refine LinearMap.ext₂ fun a b => ?_
  obtain ⟨a, rfl⟩ := hr a
  obtain ⟨b, rfl⟩ := hr b
  exact LinearMap.congr_fun₂ h a b

theorem linearIndependent_pull_equiv {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X₁} (h : LinearIndependent ℤ γ)
    (e : X ≃ₗ[O] X₁) : LinearIndependent ℤ fun i => pull e.toLinearMap (γ i) :=
  h.map' (pullLin e.toLinearMap) (LinearMap.ker_eq_bot.2 (pull_injective e.surjective))

theorem isPrim_pull_equiv (e : X ≃ₗ[O] X₁) {β : LinearMap.BilinForm ℤ X₁} (hβ : β ∈ balForms bar X₁)
    (h : IsPrim bar (⟨β, hβ⟩ : balForms bar X₁)) :
    IsPrim bar (⟨pull e.toLinearMap β, pull_mem _ hβ⟩ : balForms bar X) := by
  intro k β' hk
  refine h k ⟨pull e.symm.toLinearMap β'.1, pull_mem _ β'.2⟩ (Subtype.ext (LinearMap.ext₂ fun a b => ?_))
  have := LinearMap.congr_fun₂ (congrArg Subtype.val hk) (e.symm a) (e.symm b)
  simpa using this

end Transport

theorem perModule {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E))
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (hX : IsPolyFanOn H.bar φ X) :
    ∃ T : Set (LinearMap.BilinForm ℤ X), T.Finite ∧ ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X)
      (h : IsCell H.bar φ δ), LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
      ∃ e : X ≃ₗ[𝓞 E] X, ∀ i, pull e.toLinearMap (δ i) ∈ T := by
  classical
  obtain ⟨S, hS, hcov⟩ := hX.finite
  let U : LinearMap.BilinForm ℤ X → Set (LinearMap.BilinForm ℤ X) := fun s =>
    {t | ∃ ht : t ∈ balForms H.bar X, IsPrim H.bar (⟨t, ht⟩ : balForms H.bar X) ∧
      ∃ p r : ℕ, 0 < p ∧ 0 < r ∧ p • t = r • s}
  have hU : ∀ s, (U s).Subsingleton := by
    rintro s t ⟨ht, hpt, p, r, hp, hr, he⟩ t' ⟨ht', hpt', p', r', hp', hr', he'⟩
    have key : (r' * p) • t = (r * p') • t' := by
      rw [mul_smul, he, mul_smul, he', smul_comm]
    have := GlobalTheory.T.primitiveBalancedForm_eq_of_same_ray H.bar ⟨t, ht⟩ ⟨t', ht'⟩ (r' * p) (r * p') hpt hpt' (by positivity) (by positivity)
      (Subtype.ext (by simpa using key))
    exact congrArg Subtype.val this
  refine ⟨⋃ s ∈ S, U s, hS.biUnion fun s _ => (hU s).finite, fun m δ h hli hprim => ?_⟩
  have hB : ∑ i, (1 : ℝ) • toReal (δ i) ∈ psdCone H.bar X :=
    ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X m δ (fun _ => 1) h.mem h.nonneg (fun _ => zero_le_one)
  obtain ⟨e, m', γ, c, hγ, hγS, hc, hsum⟩ := hcov _ hB
  set γ' : Fin m' → LinearMap.BilinForm ℤ X := fun j => pull e.symm.toLinearMap (γ j) with hγ'def
  have hγ' : IsCell H.bar φ γ' := isCell_pull_equiv hγ e.symm
  have hsum' : ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ' j) := by
    refine LinearMap.ext₂ fun y z => ?_
    have := LinearMap.congr_fun₂ hsum (e.symm y) (e.symm z)
    simpa [LinearMap.sum_apply, γ'] using this
  refine ⟨e, fun i => ?_⟩
  obtain ⟨k, a, hk, hka⟩ := GlobalTheory.T.cell_generators_smul_mem_other_cellCone H.bar φ δ γ' c h hγ' hc hsum' i
  obtain ⟨j, p, r, hp, hr, hpr⟩ :=
    GlobalTheory.T.exists_pos_smul_eq_of_linearIndependent_cone' δ γ' i k a hli hk hka (GlobalTheory.T.cell_generator_mem_cone_of_smul_combination H.bar φ δ γ' i k a h hγ' hk hka)
  refine Set.mem_biUnion (hγS j) ⟨pull_mem _ (h.mem i), isPrim_pull_equiv e (h.mem i) (hprim i), p, r, hp, hr, ?_⟩
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ hpr (e y) (e z)
  simpa [γ'] using this

theorem multCellsAmong_of_isPolyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ : InvFun (𝓞 E)), IsPolyFan H.bar q φ → ∀ M : ℕ, ∃ n : ℕ, MultCellsAmong H.bar q φ M n := by
  intro E _ _ _ H q φ hφ M
  classical
  obtain ⟨n, R, hR, hcls⟩ := GlobalTheory.T.exists_fin_reps_projective_finrank_le_numberField E q
  have key : ∀ k, letI := (hR k).1; ∃ T : Set (LinearMap.BilinForm ℤ (R k)), T.Finite ∧
      ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ (R k)) (h : IsCell H.bar φ δ), LinearIndependent ℤ δ →
        (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar (R k))) →
        ∃ e : (R k) ≃ₗ[𝓞 E] (R k), ∀ i, pull e.toLinearMap (δ i) ∈ T := fun k => by
    letI := (hR k).1
    haveI := (hR k).2.1
    exact perModule H φ (R k) (hφ (R k) (hR k).2.2)
  choose T hTfin hT using key
  haveI : ∀ k, Finite (T k) := fun k => (hTfin k).to_subtype
  let D := Σ k : Fin n, Σ m : Fin (Nat.card (T k) + 1), (Fin m → T k)
  let g : D → FormFamily (𝓞 E) := fun d => ⟨R d.1, d.2.1, fun i => (d.2.2 i : LinearMap.BilinForm ℤ (R d.1))⟩
  obtain ⟨N, ⟨eq⟩⟩ := Finite.exists_equiv_fin D
  refine ⟨N, fun k' => g (eq.symm k'), fun X _ _ _ _ hX m δ hδ => ?_⟩
  obtain ⟨hcell, hli, hprim, -⟩ := hδ
  obtain ⟨k, ⟨f⟩⟩ := hcls X hX
  letI := (hR k).1
  let δ' : Fin m → LinearMap.BilinForm ℤ (R k) := fun i => pull f.symm.toLinearMap (δ i)
  have hcell' : IsCell H.bar φ δ' := isCell_pull_equiv hcell f.symm
  have hli' : LinearIndependent ℤ δ' := linearIndependent_pull_equiv hli f.symm
  have hprim' : ∀ i, IsPrim H.bar (⟨δ' i, hcell'.mem i⟩ : balForms H.bar (R k)) := fun i =>
    isPrim_pull_equiv f.symm (hcell.mem i) (hprim i)
  obtain ⟨e, he⟩ := hT k m δ' hcell' hli' hprim'
  let t : Fin m → T k := fun i => ⟨_, he i⟩
  have ht : Function.Injective t := fun i j hij =>
    hli'.injective (pull_injective e.surjective (congrArg Subtype.val hij))
  have hm : m < Nat.card (T k) + 1 := by
    have := Nat.card_le_card_of_injective t ht
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  refine ⟨eq ⟨k, ⟨m, hm⟩, t⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  refine ⟨f.trans e.symm, Equiv.refl (Fin m), fun i => LinearMap.ext₂ fun y z => ?_⟩
  simp [g, t, δ']

end GlobalTheory.PolFan.CellClass
