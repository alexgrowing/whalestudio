import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntLinearFormCuttingSubcell

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.StarLab

variable {O : Type} [CommRing O]

def IsCentreRay (w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X → X → ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ∃ β : LinearMap.BilinForm ℤ X, w.evalZ β = 1 ∧ ∀ a b, t * B a b = β a b

theorem isCentreRay_comp (w : InvFun O) {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] [Module.Projective O X₁] {r : X →ₗ[O] X₁}
    (hr : Function.Surjective r) (B : X₁ → X₁ → ℝ) :
    IsCentreRay w X (fun a b => B (r a) (r b)) ↔ IsCentreRay w X₁ B := by
  constructor
  · rintro ⟨t, ht, β, hw, hβ⟩
    obtain ⟨s, hs⟩ := Module.projective_lifting_property r LinearMap.id hr
    have hs' : ∀ x, r (s x) = x := fun x => LinearMap.congr_fun hs x
    refine ⟨t, ht, pull s β, ?_, fun x y => ?_⟩
    · have e : pull r (pull s β) = β := LinearMap.ext₂ fun a b => by
        have h1 := hβ (s (r a)) (s (r b))
        have h2 := hβ a b
        simp only [hs'] at h1
        simp only [pull_apply]
        exact_mod_cast h1.symm.trans h2
      rw [← evalZ_pull w hr, e, hw]
    · have := hβ (s x) (s y)
      simp only [hs'] at this
      simpa only [pull_apply] using this
  · rintro ⟨t, ht, β, hw, hβ⟩
    exact ⟨t, ht, pull r β, by rw [evalZ_pull w hr, hw], fun a b => by simp only [pull_apply, hβ]⟩

open Classical in

def starLab (lab w : InvFun O) : InvFun O where
  toFun n B := if IsCentreRay w (Fin n → O) B then -1 else Real.exp (lab.toFun n B) - 1
  inv n m r hr B := by
    simp only [isCentreRay_comp w hr B, lab.inv n m r hr B]
  zero B := by
    have : ¬ IsCentreRay w (Fin 0 → O) B := by
      rintro ⟨t, -, β, hw, -⟩
      rw [InvFun.evalZ, w.eval_of_subsingleton] at hw
      norm_num at hw
    rw [if_neg this, lab.zero, Real.exp_zero, sub_self]

open Classical in

theorem starLab_eval (lab w : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (B : X → X → ℝ) :
    (starLab lab w).eval X B = if IsCentreRay w X B then -1 else Real.exp (lab.eval X B) - 1 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [(starLab lab w).eval_eq hr, lab.eval_eq hr]
  simp only [starLab, isCentreRay_comp w hr B]

variable {X : Type} [AddCommGroup X]

open Classical in

theorem starLab_evalZ_of_eq_one (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    {β : LinearMap.BilinForm ℤ X} (h : w.evalZ β = 1) : (starLab lab w).evalZ β = -1 := by
  rw [InvFun.evalZ, starLab_eval, if_pos ⟨1, one_pos, β, h, fun a b => one_mul _⟩]

theorem starLab_evalZ_of_not (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    {β : LinearMap.BilinForm ℤ X} (h : ¬ IsCentreRay w X (fun a b => (β a b : ℝ))) :
    (starLab lab w).evalZ β = Real.exp (lab.evalZ β) - 1 := by
  rw [InvFun.evalZ, starLab_eval, if_neg h]; rfl

theorem isCentreRay_smul_iff (w : InvFun O) [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X) {k : ℕ}
    (hk : 0 < k) :
    IsCentreRay w X (fun a b => ((((k : ℤ) • β) a b : ℤ) : ℝ)) ↔ IsCentreRay w X (fun a b => (β a b : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · rintro ⟨t, ht, β', hw, h⟩
    refine ⟨t * k, mul_pos ht hk', β', hw, fun a b => ?_⟩
    rw [← h a b]; simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]; ring
  · rintro ⟨t, ht, β', hw, h⟩
    refine ⟨t / k, div_pos ht hk', β', hw, fun a b => ?_⟩
    rw [← h a b]; simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]; field_simp

theorem starLab_evalZ_smul (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    (β : LinearMap.BilinForm ℤ X) {k : ℕ} (hk : 0 < k) (hlab : lab.evalZ ((k : ℤ) • β) = lab.evalZ β) :
    (starLab lab w).evalZ ((k : ℤ) • β) = (starLab lab w).evalZ β := by
  unfold InvFun.evalZ at hlab ⊢
  rw [starLab_eval, starLab_eval, hlab]
  by_cases hc : IsCentreRay w X (fun a b => (β a b : ℝ))
  · rw [if_pos ((isCentreRay_smul_iff w β hk).2 hc), if_pos hc]
  · rw [if_neg (mt (isCentreRay_smul_iff w β hk).1 hc), if_neg hc]

theorem exists_of_isCentreRay {bar : O → O} (w : InvFun O) [Module O X] [Module.Finite O X]
    {β : LinearMap.BilinForm ℤ X} (hb : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y)
    (h : IsCentreRay w X (fun a b => (β a b : ℝ))) :
    ∃ t : ℝ, 0 < t ∧ ∃ β' : LinearMap.BilinForm ℤ X, β' ∈ balForms bar X ∧ (∀ y, 0 ≤ β' y y) ∧ w.evalZ β' = 1 ∧
      toReal β' = t • toReal β := by
  obtain ⟨t, ht, β', hw, h⟩ := h
  simp only at h
  refine ⟨t, ht, β', ⟨fun y z => ?_, fun a y z => ?_⟩, fun y => ?_, hw, LinearMap.ext₂ fun a b => ?_⟩
  · have : (β' y z : ℝ) = β' z y := by rw [← h, ← h, hb.1 y z]
    exact_mod_cast this
  · have : (β' (a • y) z : ℝ) = β' y (bar a • z) := by rw [← h, ← h, hb.2 a y z]
    exact_mod_cast this
  · have : (0 : ℝ) ≤ β' y y := by rw [← h]; exact mul_nonneg ht.le (by exact_mod_cast hp y)
    exact_mod_cast this
  · simp [← h]

theorem InRCone.of_toReal_eq_smul {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {β β' : LinearMap.BilinForm ℤ X}
    (hβ : InRCone γ β) {t : ℝ} (ht : 0 ≤ t) (e : toReal β' = t • toReal β) : InRCone γ β' := by
  obtain ⟨c, hc, e'⟩ := hβ
  refine ⟨fun i => t * c i, fun i => mul_nonneg ht (hc i), ?_⟩
  rw [e, e', Finset.smul_sum]
  simp only [smul_smul]

theorem exists_isFaceCut {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hh : ∀ j, 0 ≤ h (γ j)) : ∃ (m' : ℕ) (s : Fin m' ↪ Fin m), IsFaceCut γ s h := by
  classical
  let e := Fintype.equivFin {j : Fin m // h (γ j) = 0}
  refine ⟨_, e.symm.toEmbedding.trans (Function.Embedding.subtype _), hh, fun j => ⟨fun hj => ⟨e ⟨j, hj⟩, by simp⟩, ?_⟩⟩
  rintro ⟨i, rfl⟩
  exact (e.symm i).2

theorem inRCone_face {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' ↪ Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hf : IsFaceCut γ s h) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β)
    (h0 : h β = 0) : InRCone (fun j => γ (s j)) β := by
  classical
  obtain ⟨c, hc, e⟩ := hβ
  have h1 := apply_eq_of_toReal_eq e h
  rw [h0, Int.cast_zero] at h1
  have hz : ∀ i, c i * (h (γ i) : ℝ) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hc i) (by exact_mod_cast hf.1 i))).1 h1.symm i
      (Finset.mem_univ _)
  have hc0 : ∀ i, i ∉ Set.range s → c i = 0 := fun i hi => by
    have hpos : (h (γ i) : ℝ) ≠ 0 := by exact_mod_cast fun h' => hi ((hf.2 i).1 h')
    exact (mul_eq_zero.1 (hz i)).resolve_right hpos
  refine ⟨fun j => c (s j), fun j => hc _, ?_⟩
  rw [e]
  have hm := Finset.sum_map Finset.univ s (fun i => c i • toReal (γ i))
  rw [← hm]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
  rw [hc0 i (fun ⟨j, hj⟩ => hi (Finset.mem_map.2 ⟨j, Finset.mem_univ _, hj⟩)), zero_smul]

theorem IsFaceCut.apply_eq_zero {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' ↪ Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hf : IsFaceCut γ s h) {β : LinearMap.BilinForm ℤ X}
    (hβ : InRCone (fun j => γ (s j)) β) : h β = 0 := by
  obtain ⟨c, hc, e⟩ := hβ
  have h1 := apply_eq_of_toReal_eq e h
  simp only [(hf.2 _).2 ⟨_, rfl⟩, Int.cast_zero, mul_zero, Finset.sum_const_zero] at h1
  exact_mod_cast h1

theorem inRCone_of_sub {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (s : Fin m' → Fin m)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone (fun j => γ (s j)) β) : InRCone γ β :=
  inRCone_trans (fun j => inRCone_self γ (s j)) hβ

theorem isTwInv_starLab {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {lab w : InvFun (𝓞 E)}
    (hl : IsTwInv H lab) (hw : IsTwInv H w) : IsTwInv H (starLab lab w) := by
  intro σ hσ n B
  let e : (Fin n → 𝓞 E) ≃ₗ[ℤ] (Fin n → 𝓞 E) :=
    AddEquiv.toIntLinearEquiv (AddEquiv.piCongrRight fun _ => σ.toAddEquiv)
  have he : ∀ a, e a = fun i => σ (a i) := fun a => rfl
  have hwt : ∀ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E),
      w.evalZ (β.compl₁₂ e.toLinearMap e.toLinearMap) = w.evalZ β := fun β => by
    simp only [InvFun.evalZ, InvFun.eval_pi, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, he]
    exact hw σ hσ n (fun a b => (β a b : ℝ))
  have key : IsCentreRay w (Fin n → 𝓞 E) (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) ↔
      IsCentreRay w (Fin n → 𝓞 E) B := by
    constructor
    · rintro ⟨t, ht, β, h1, h2⟩
      refine ⟨t, ht, β.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap, ?_, fun a b => ?_⟩
      · rw [← hwt, ← h1]
        congr 1
        ext a b
        simp
      · have := h2 (e.symm a) (e.symm b)
        simp only [← he, LinearEquiv.apply_symm_apply] at this
        simpa using this
    · rintro ⟨t, ht, β, h1, h2⟩
      exact ⟨t, ht, β.compl₁₂ e.toLinearMap e.toLinearMap, by rw [hwt, h1], fun a b => by
        simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, he, h2]⟩
  have hlab := hl σ hσ n B
  simp only [starLab]
  by_cases hc : IsCentreRay w (Fin n → 𝓞 E) B
  · rw [if_pos (key.2 hc), if_pos hc]
  · rw [if_neg (mt key.1 hc), if_neg hc, hlab]

end GlobalTheory.PolFan.StarLab
