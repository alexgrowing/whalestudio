import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TensEigSecond

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

noncomputable def contr (v : V ⊗[ℂ] W) : Module.Dual ℂ V →ₗ[ℂ] W where
  toFun l := TensorProduct.lid ℂ W (LinearMap.rTensor W l v)
  map_add' l m := by simp [LinearMap.rTensor_add]
  map_smul' c l := by simp [LinearMap.rTensor_smul]

theorem contr_apply (v : V ⊗[ℂ] W) (l : Module.Dual ℂ V) :
    contr v l = TensorProduct.lid ℂ W (LinearMap.rTensor W l v) := rfl

theorem contr_tmul (a : V) (b : W) (l : Module.Dual ℂ V) : contr (a ⊗ₜ[ℂ] b) l = l a • b := by
  simp [contr_apply]

theorem contr_add (v w : V ⊗[ℂ] W) (l : Module.Dual ℂ V) : contr (v + w) l = contr v l + contr w l := by
  simp [contr_apply]

theorem contr_smul (c : ℂ) (v : V ⊗[ℂ] W) (l : Module.Dual ℂ V) : contr (c • v) l = c • contr v l := by
  simp [contr_apply]

theorem contr_map (A : Module.End ℂ V) (B : Module.End ℂ W) (v : V ⊗[ℂ] W) (l : Module.Dual ℂ V) :
    B (contr v (l ∘ₗ A)) = contr (TensorProduct.map A B v) l := by
  induction v using TensorProduct.induction_on with
  | zero => simp [contr_apply]
  | tmul a b => simp [contr_tmul]
  | add x y hx hy => simp only [map_add, contr_add, hx, hy]

theorem exists_finiteDimensional (v : V ⊗[ℂ] W) :
    ∃ T : Submodule ℂ W, FiniteDimensional ℂ T ∧ ∀ l, contr v l ∈ T := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨⊥, inferInstance, fun l => by simp [contr_apply]⟩
  | tmul a b =>
    exact ⟨ℂ ∙ b, inferInstance, fun l => by
      rw [contr_tmul]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)⟩
  | add x y hx hy =>
    obtain ⟨T, hT, h⟩ := hx
    obtain ⟨T', hT', h'⟩ := hy
    exact ⟨T ⊔ T', inferInstance, fun l => by
      rw [contr_add]; exact Submodule.add_mem_sup (h l) (h' l)⟩

theorem exists_contr_ne_zero {v : V ⊗[ℂ] W} (hv : v ≠ 0) : ∃ l, contr v l ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hv
  let b := Module.Free.chooseBasis ℂ V
  have key : ∀ (w : V ⊗[ℂ] W) i, TensorProduct.equivFinsuppOfBasisLeft b w i = contr w (b.coord i) := by
    intro w i
    induction w using TensorProduct.induction_on with
    | zero => simp [contr_apply]
    | tmul a c => simp [contr_tmul, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, contr_add, hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisLeft (N := W) b).injective
  ext i : 1
  rw [key, hcon]
  simp

theorem core {Y : Type} (A : Module.End ℂ V) (B : Y → Module.End ℂ W) (a : ℂ) (ha : a ≠ 0) (mu : Y → ℂ)
    (hmu : ∀ y, mu y ≠ 0) (v : V ⊗[ℂ] W) (hv : v ≠ 0)
    (h : ∀ y, TensorProduct.map A (B y) v = (a * mu y) • v) :
    ∃ (l : Module.Dual ℂ V) (c : ℂ), c ≠ 0 ∧ contr v l ≠ 0 ∧
      ∀ y, B y (contr v l) = (c * mu y) • contr v l := by
  obtain ⟨l₀, hl₀⟩ := exists_contr_ne_zero hv
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y0⟩⟩
  · exact ⟨l₀, 1, one_ne_zero, hl₀, fun y => isEmptyElim y⟩
  have key : ∀ y l, B y (contr v (l ∘ₗ A)) = (a * mu y) • contr v l := by
    intro y l
    rw [contr_map, h, contr_smul]
  let S := LinearMap.range (contr v)
  obtain ⟨T, hT, hST⟩ := exists_finiteDimensional v
  have hSfd : FiniteDimensional ℂ S :=
    Submodule.finiteDimensional_of_le (S₂ := T) (by rintro _ ⟨l, rfl⟩; exact hST l)
  let b : Module.Dual ℂ V →ₗ[ℂ] W := contr v ∘ₗ A.dualMap
  have hb : ∀ l, b l = contr v (l ∘ₗ A) := fun l => rfl
  let S' := LinearMap.range b
  have hle : S' ≤ S := LinearMap.range_comp_le_range _ _
  have hS'fd : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle
  have hne : a * mu y0 ≠ 0 := mul_ne_zero ha (hmu y0)
  have hmap : S ≤ S'.map (B y0) := by
    rintro _ ⟨l, rfl⟩
    refine ⟨b ((a * mu y0)⁻¹ • l), ⟨_, rfl⟩, ?_⟩
    rw [hb, key, map_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hfr : Module.finrank ℂ S ≤ Module.finrank ℂ S' :=
    (Submodule.finrank_mono hmap).trans (Submodule.finrank_map_le _ _)
  have hSS' : S' = S := Submodule.eq_of_le_of_finrank_le hle hfr
  have hrep : ∀ s ∈ S, ∃ l, s = contr v (l ∘ₗ A) := by
    intro s hs
    rw [← hSS'] at hs
    obtain ⟨l, rfl⟩ := hs
    exact ⟨l, hb l⟩
  have hform : ∀ s ∈ S, ∀ y, mu y0 • B y s = mu y • B y0 s := by
    intro s hs y
    obtain ⟨l, rfl⟩ := hrep s hs
    rw [key, key, smul_smul, smul_smul]
    congr 1
    ring
  have hinv : ∀ s ∈ S, B y0 s ∈ S := by
    intro s hs
    obtain ⟨l, rfl⟩ := hrep s hs
    rw [key]
    exact S.smul_mem _ ⟨l, rfl⟩
  let R : Module.End ℂ S := (B y0).restrict hinv
  have hsurj : Function.Surjective R := by
    rintro ⟨s, hs⟩
    obtain ⟨t, ht, rfl⟩ := hmap hs
    exact ⟨⟨t, hle ht⟩, rfl⟩
  have hinj : Function.Injective R := LinearMap.injective_iff_surjective.mpr hsurj
  have hnt : Nontrivial S :=
    ⟨⟨⟨contr v l₀, ⟨l₀, rfl⟩⟩, 0, fun e => hl₀ (congrArg Subtype.val e)⟩⟩
  obtain ⟨γ, hγ⟩ := Module.End.exists_eigenvalue R
  obtain ⟨u, hu⟩ := hγ.exists_hasEigenvector
  have hRu : R u = γ • u := hu.apply_eq_smul
  have hu0 : u ≠ 0 := hu.2
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    apply hu0
    apply hinj
    rw [hRu]
    simp
  have hBu : B y0 (u : W) = γ • (u : W) := congrArg Subtype.val hRu
  obtain ⟨l, hl⟩ := u.2
  refine ⟨l, γ / mu y0, div_ne_zero hγ0 (hmu y0), ?_, fun y => ?_⟩
  · rw [hl]
    exact fun e => hu0 (Subtype.ext e)
  · rw [hl]
    have e := hform u u.2 y
    rw [hBu] at e
    have e2 : B y (u : W) = (mu y0)⁻¹ • mu y0 • B y (u : W) := by
      rw [smul_smul, inv_mul_cancel₀ (hmu y0), one_smul]
    rw [e2, e, smul_smul, smul_smul]
    congr 1
    field_simp [hmu y0]

theorem tensEigR : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEigR := by
  intro V W X Y _ _ _ _ A B lam mu v hv hX hlam hmu hAB
  obtain ⟨x0⟩ := hX
  exact core (A x0) B (lam x0) (hlam x0) mu hmu v hv (hAB x0)

end GlobalTheory.CompanionTheory.TensEigSecond
