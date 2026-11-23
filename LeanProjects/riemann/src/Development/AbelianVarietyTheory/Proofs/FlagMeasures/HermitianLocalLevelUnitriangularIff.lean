import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponents
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.FirstColumn

section Abstract

variable {K A : Type} [Field K] [CommRing A] {n : ℕ}

theorem columns_iff (sp : A ≃+* K × K) (I : Subring A) (Λ : Submodule I (Fin n → A)) (O : Subring K) (g : ℕ)
    (hint : ∀ x, x ∈ I ↔ (sp x).1 ∈ O ∧ (sp x).2 ∈ O)
    (hΛ : ∀ y : Fin n → A, y ∈ Λ ↔ (∃ y₁ ∈ Λ, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧
      ∃ y₂ ∈ Λ, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2)
    (c : Fin n → Fin n → A) (hc : ∀ j, c j ∈ Λ) (hc2 : ∀ j a, (sp (c j a)).2 = 0)
    (fr fri : Matrix (Fin n) (Fin n) K) (hinv : fri * fr = 1) (hinv' : fr * fri = 1)
    (hfr0 : fr = Matrix.of (fun a j => (sp (c j a)).1))
    (hfr : ∀ x : Fin n → K, (∃ y ∈ Λ, ∀ a, (sp (y a)).1 = x a) ↔ ∀ a, (fri *ᵥ x) a ∈ O)
    (y : Matrix (Fin n) (Fin n) A) (hy : ∀ x ∈ Λ, y *ᵥ x ∈ Λ) :
    (∀ a b, (fri * y.map ((RingHom.fst K K).comp sp.toRingHom) * fr) a b ∈ O) ∧
    ((∀ i : Fin n, InModL Λ g (c '' {j | j.1 < i.1}) ((y - 1) *ᵥ c i)) ↔
      ∀ a b : Fin n, b ≤ a → ∃ w ∈ O,
        (fri * y.map ((RingHom.fst K K).comp sp.toRingHom) * fr) a b - (if a = b then 1 else 0) = (g : K) * w) := by
  set φ : A →+* K := (RingHom.fst K K).comp sp.toRingHom with hφ
  set ψ : A →+* K := (RingHom.snd K K).comp sp.toRingHom with hψ
  have hφa : ∀ x, φ x = (sp x).1 := fun _ => rfl
  have hψa : ∀ x, ψ x = (sp x).2 := fun _ => rfl
  set M := fri * y.map φ * fr with hM

  have hcol : ∀ j, (φ ∘ c j) = fr *ᵥ Pi.single j 1 := by
    intro j
    funext a
    rw [Matrix.mulVec_single_one, hfr0]
    rfl
  have hgen : ∀ (Z : Matrix (Fin n) (Fin n) A) (i : Fin n),
      fri *ᵥ (φ ∘ (Z *ᵥ c i)) = fun a => (fri * Z.map φ * fr) a i := by
    intro Z i
    have h1 : φ ∘ (Z *ᵥ c i) = Z.map φ *ᵥ (fr *ᵥ Pi.single i 1) := by
      funext a
      rw [← hcol i]
      exact RingHom.map_mulVec φ Z (c i) a
    rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  have hbasis : ∀ j, fri *ᵥ (φ ∘ c j) = Pi.single j 1 := by
    intro j
    rw [hcol j, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hmap1 : (y - 1).map φ = y.map φ - 1 := by
    ext a b
    simp [Matrix.one_apply, apply_ite φ]
  have hD : ∀ i, fri *ᵥ (φ ∘ ((y - 1) *ᵥ c i)) = fun a => M a i - if a = i then 1 else 0 := by
    intro i
    rw [hgen, hmap1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hinv]
    funext a
    simp [Matrix.sub_apply, Matrix.one_apply, hM]
  have hMO : ∀ a b, M a b ∈ O := by
    intro a b
    have h := (hfr (φ ∘ (y *ᵥ c b))).1 ⟨y *ᵥ c b, hy _ (hc b), fun _ => rfl⟩ a
    rw [hgen] at h
    exact h
  refine ⟨hMO, ?_, ?_⟩
  · intro h a b hba
    have hspan : ∀ s ∈ Submodule.span I (c '' {j | j.1 < b.1}), (fri *ᵥ (φ ∘ s)) a = 0 := by
      intro s hs
      induction hs using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, hj, rfl⟩ := hx
        rw [hbasis j]
        have : a ≠ j := by
          intro h'
          subst h'
          exact absurd hba (not_le.2 hj)
        simp [Pi.single_apply, this]
      | zero =>
        have : (φ ∘ (0 : Fin n → A)) = 0 := by funext; simp
        rw [this]
        simp
      | add x x' _ _ hx hx' =>
        have : (φ ∘ (x + x')) = φ ∘ x + φ ∘ x' := by funext; simp
        rw [this, Matrix.mulVec_add, Pi.add_apply, hx, hx', add_zero]
      | smul r x _ hx =>
        have : (φ ∘ (r • x)) = φ (r : A) • (φ ∘ x) := by
          funext b
          simp [Subring.smul_def]
        rw [this, Matrix.mulVec_smul, Pi.smul_apply, hx, smul_zero]
    obtain ⟨s, hs, z, hz, e⟩ := h b
    have hs0 := hspan s hs
    refine ⟨(fri *ᵥ (φ ∘ z)) a, (hfr _).1 ⟨z, hz, fun _ => rfl⟩ a, ?_⟩
    have h1 : φ ∘ ((y - 1) *ᵥ c b) = φ ∘ s + (g : K) • (φ ∘ z) := by
      rw [e]
      funext b
      simp
    have h2 := congrFun (hD b) a
    rw [h1, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, hs0, zero_add] at h2
    simpa using h2.symm
  · intro h i
    have h' : ∀ a : Fin n, ∃ w ∈ O, (i ≤ a → M a i - (if a = i then 1 else 0) = (g : K) * w) ∧ (a < i → w = 0) := by
      intro a
      by_cases hia : i ≤ a
      · obtain ⟨w, hw, e⟩ := h a i hia
        exact ⟨w, hw, fun _ => e, fun h'' => absurd h'' (not_lt.2 hia)⟩
      · exact ⟨0, O.zero_mem, fun h'' => absurd h'' hia, fun _ => rfl⟩
    choose W hWO hW hW0 using h'
    have hri : ∀ j, sp.symm (M j i, 0) ∈ I := by
      intro j
      rw [hint]
      simp only [RingEquiv.apply_symm_apply]
      exact ⟨hMO j i, O.zero_mem⟩
    have hz0 : ∀ a, ψ (sp.symm ((fr *ᵥ W) a, 0)) = 0 := by
      intro a
      simp [hψa]
    set z : Fin n → A := fun a => sp.symm ((fr *ᵥ W) a, 0) with hz
    have hzΛ : z ∈ Λ := by
      rw [hΛ]
      refine ⟨?_, 0, Λ.zero_mem, fun b => ?_⟩
      · obtain ⟨y₁, hy₁, e⟩ := (hfr (fr *ᵥ W)).2 (fun a => by
          rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
          exact hWO a)
        exact ⟨y₁, hy₁, fun b => by rw [e b]; simp [hz]⟩
      · simp [hz]
    set s : Fin n → A := ∑ j ∈ Finset.univ.filter (· < i), (⟨sp.symm (M j i, 0), hri j⟩ : I) • c j with hs
    have hsm : s ∈ Submodule.span I (c '' {j | j.1 < i.1}) := by
      refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_, rfl⟩)
      simpa using hj
    have hs1 : φ ∘ s = fr *ᵥ (fun b => if b < i then M b i else 0) := by
      funext a
      show φ (s a) = _
      rw [hs, Finset.sum_apply, map_sum, Finset.sum_filter]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : b < i
      · rw [if_pos hb, if_pos hb]
        show φ ((sp.symm (M b i, 0) : A) * c b a) = _
        rw [map_mul, hφa, RingEquiv.apply_symm_apply, hfr0, mul_comm]
        rfl
      · rw [if_neg hb, if_neg hb, mul_zero]
    have hs2 : ∀ a, ψ (s a) = 0 := by
      intro a
      rw [hs, Finset.sum_apply, map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      show ψ ((sp.symm (M j i, 0) : A) * c j a) = 0
      rw [map_mul, hψa (c j a), hc2, mul_zero]
    have hcolD : φ ∘ ((y - 1) *ᵥ c i) = fr *ᵥ (fun b => if b < i then M b i else 0) + (g : K) • (fr *ᵥ W) := by
      have h1 : (fun a => M a i - if a = i then (1 : K) else 0) = (fun b => if b < i then M b i else 0) + (g : K) • W := by
        funext a
        by_cases hia : i ≤ a
        · have := hW a hia
          simp [not_lt.2 hia, this]
        · have hai := not_le.1 hia
          simp [hai, hW0 a hai, ne_of_lt hai]
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← h1, ← hD i, Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
    refine ⟨s, hsm, z, hzΛ, ?_⟩
    funext a
    apply sp.injective
    refine Prod.ext ?_ ?_
    · have h1 : φ (((y - 1) *ᵥ c i) a) = (fr *ᵥ (fun b => if b < i then M b i else 0)) a + (g : K) * (fr *ᵥ W) a :=
        congrFun hcolD a
      have h2 : φ (s a) = (fr *ᵥ (fun b => if b < i then M b i else 0)) a := congrFun hs1 a
      have h3 : φ (z a) = (fr *ᵥ W) a := by simp [hz, hφa]
      show φ (((y - 1) *ᵥ c i) a) = φ (s a + (g : A) * z a)
      rw [map_add, map_mul, map_natCast, h1, h2, h3]
    · have h1 : ψ (((y - 1) *ᵥ c i) a) = 0 := by
        rw [RingHom.map_mulVec]
        have : ψ ∘ c i = 0 := by
          funext b
          exact hc2 i b
        rw [this, Matrix.mulVec_zero]
        rfl
      show ψ (((y - 1) *ᵥ c i) a) = ψ (s a + (g : A) * z a)
      rw [h1, map_add, map_mul, hs2 a, hz0 a, mul_zero, add_zero]

end Abstract

section Residue

theorem inJ_red_iff (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g : ℕ)
    (hg : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) =
      Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)})
    {n : ℕ} (t : ℕ) (X : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hX : ∀ a b, X a b ∈ v.adicCompletionIntegers F) :
    InJ n t n false (redM F v X) ↔ ∀ a b : Fin n, b ≤ a → ∃ w ∈ (v.adicCompletionIntegers F).toSubring,
      X a b - (if a = b then 1 else 0) = (g : v.adicCompletion F) * w := by
  have hiff : ∀ a b, (∃ w ∈ (v.adicCompletionIntegers F).toSubring,
      X a b - (if a = b then 1 else 0) = (g : v.adicCompletion F) * w) ↔
      redM F v X a b = if a = b then 1 else 0 := by
    intro a b
    have hred : redM F v X a b = IsLocalRing.residue _ ⟨X a b, hX a b⟩ := dif_pos (hX a b)
    obtain ⟨d, hd1, hd2⟩ : ∃ d : v.adicCompletionIntegers F,
        IsLocalRing.residue (v.adicCompletionIntegers F) d = (if a = b then 1 else 0) ∧
        (d : v.adicCompletion F) = if a = b then 1 else 0 := by
      by_cases h : a = b
      · exact ⟨1, by simp [h], by simp [h]⟩
      · exact ⟨0, by simp [h], by simp [h]⟩
    rw [hred, ← hd1, ← hd2, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hg,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨w, hw, e⟩
      refine ⟨⟨w, hw⟩, ?_⟩
      apply Subtype.ext
      show w * (g : v.adicCompletion F) = X a b - d
      rw [e, mul_comm]
    · rintro ⟨w, e⟩
      refine ⟨w, w.2, ?_⟩
      have h := congrArg Subtype.val e
      have h' : (w : v.adicCompletion F) * (g : v.adicCompletion F) = X a b - d := h
      rw [← h', mul_comm]
  have hblk : ∀ x : Fin n, blkOf n t x = x := fun x => if_pos x.2
  constructor
  · rintro ⟨h1, h2, -, -⟩ a b hba
    rw [hiff]
    rcases eq_or_lt_of_le hba with e | e
    · subst e
      rw [if_pos rfl]
      exact h2 b b.2
    · rw [if_neg e.ne']
      exact h1 a b (by rw [hblk, hblk]; exact e)
  · intro h
    refine ⟨fun x y hxy => ?_, fun x _ => ?_, fun x y hy => absurd y.2 (by omega), fun h' => by cases h'⟩
    · have hlt : y < x := by
        rw [hblk, hblk] at hxy
        exact hxy
      have h3 := (hiff x y).1 (h x y hlt.le)
      rwa [if_neg hlt.ne'] at h3
    · have h3 := (hiff x x).1 (h x x le_rfl)
      rwa [if_pos rfl] at h3

end Residue

theorem unitriangular_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (c : Fin n → Fin n → E ⊗[F] v.adicCompletion F) (fr : GL (Fin n) (v.adicCompletion F)), (∀ j, c j ∈ loc v L) → (∀ j a, (sp (c j a)).2 = 0) → (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Matrix.of (fun a j => (sp (c j a)).1) → (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a) ↔ ∀ a, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x a ∈ v.adicCompletionIntegers F) → ∀ (t : ℕ), ∀ y ∈ levelVL cm.sig J v L, (∀ a b, ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b ∈ v.adicCompletionIntegers F) ∧ ((∀ i : Fin n, InModL (loc v L) g (c '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ c i)) ↔ InJ n t n false (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
  intro F E _ _ _ _ _ _ cm n J hH hJ v sp hsig halg hint g hg L hL c fr hc hc2 hfr0 hfr t y hy
  have hsplit := (GlobalTheory.St.G.split_components F E cm n J hH hJ v sp hsig halg).1 L
  have hy' : ∀ x ∈ loc v L, y.1 *ᵥ x ∈ loc v L := fun x hx => (hy.2 x).1 hx
  have hinv : ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * fr.1 = 1 :=
    Units.inv_mul fr
  have hinv' : fr.1 * ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 :=
    Units.mul_inv fr
  obtain ⟨h1, h2⟩ := columns_iff sp (intV E v) (loc v L) (v.adicCompletionIntegers F).toSubring g hint hsplit c hc hc2
    fr.1 _ hinv hinv' hfr0 hfr y.1 hy'
  exact ⟨h1, h2.trans (inJ_red_iff F v g hg t _ h1).symm⟩

end GlobalTheory.St.G.FirstColumn

end
