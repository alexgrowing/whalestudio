import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
open Matrix

namespace GlobalTheory.BesselChar.JointSplit

variable {A R₁ R₂ : Type} [CommRing A] [CommRing R₁] [CommRing R₂]

theorem fwd (f : A →+* R₁) (g : A →+* R₂) (hinj : ∀ y, f y = 0 → g y = 0 → y = 0)
    (hsurj : ∀ a b, ∃ y, f y = a ∧ g y = b) {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) A)
    (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A) (h : GlobalTheory.BesselChar.Unip E K M) :
    GlobalTheory.BesselChar.Unip (E.map f) (K.map f) (M.map f) := by
  obtain ⟨⟨T, hT, hMT⟩, h2⟩ := h
  refine ⟨⟨T.map f, fun j i hij => by simp [hT j i hij], ?_⟩, fun y₁ hy₁ => ?_⟩
  · rw [← Matrix.map_mul, hMT, Matrix.map_add _ (map_add f), Matrix.map_mul]
  · choose l hl1 hl2 using hsurj
    obtain ⟨y, hfy, hgy⟩ : ∃ y : Fin n → A, (fun i => f (y i)) = y₁ ∧ (fun i => g (y i)) = 0 :=
      ⟨fun i => l (y₁ i) 0, funext fun i => hl1 _ _, funext fun i => hl2 _ _⟩
    have hKy : K *ᵥ y = 0 := by
      funext i
      apply hinj
      · have := congrFun (GlobalTheory.BesselChar.mulVec_map f K y) i
        rw [hfy, hy₁] at this
        exact this.symm
      · have := congrFun (GlobalTheory.BesselChar.mulVec_map g K y) i
        rw [hgy, Matrix.mulVec_zero] at this
        exact this.symm
    obtain ⟨a, ha⟩ := h2 y hKy
    refine ⟨fun i => f (a i), ?_⟩
    subst hfy
    rw [GlobalTheory.BesselChar.mulVec_map, GlobalTheory.BesselChar.mulVec_map, ha]
    funext i
    simp only [Pi.add_apply, map_add]

theorem bwd (f : A →+* R₁) (g : A →+* R₂) (hinj : ∀ y, f y = 0 → g y = 0 → y = 0)
    (hsurj : ∀ a b, ∃ y, f y = a ∧ g y = b) {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) A)
    (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A)
    (h1 : GlobalTheory.BesselChar.Unip (E.map f) (K.map f) (M.map f))
    (h2 : GlobalTheory.BesselChar.Unip (E.map g) (K.map g) (M.map g)) : GlobalTheory.BesselChar.Unip E K M := by
  choose l hl1 hl2 using hsurj
  have l00 : l 0 0 = 0 := hinj _ (hl1 0 0) (hl2 0 0)
  have extM : ∀ {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) A), X.map f = Y.map f → X.map g = Y.map g → X = Y := by
    intro p q X Y hf hg
    ext i j
    rw [← sub_eq_zero]
    apply hinj
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun hf i) j
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun hg i) j
  have extV : ∀ {p : ℕ} (x z : Fin p → A), (fun i => f (x i)) = (fun i => f (z i)) →
      (fun i => g (x i)) = (fun i => g (z i)) → x = z := by
    intro p x z hf hg
    funext i
    rw [← sub_eq_zero]
    apply hinj
    · rw [map_sub, sub_eq_zero]; exact congrFun hf i
    · rw [map_sub, sub_eq_zero]; exact congrFun hg i
  obtain ⟨⟨T₁, hT₁, e₁⟩, k₁⟩ := h1
  obtain ⟨⟨T₂, hT₂, e₂⟩, k₂⟩ := h2
  let T : Matrix (Fin ρ) (Fin ρ) A := Matrix.of fun i j => l (T₁ i j) (T₂ i j)
  have hTf : T.map f = T₁ := by ext i j; exact hl1 _ _
  have hTg : T.map g = T₂ := by ext i j; exact hl2 _ _
  refine ⟨⟨T, fun j i hij => ?_, ?_⟩, fun y hy => ?_⟩
  · show l (T₁ j i) (T₂ j i) = 0
    rw [hT₁ j i hij, hT₂ j i hij, l00]
  · apply extM
    · rw [Matrix.map_mul, Matrix.map_add _ (map_add f), Matrix.map_mul, hTf, e₁]
    · rw [Matrix.map_mul, Matrix.map_add _ (map_add g), Matrix.map_mul, hTg, e₂]
  · have hy₁ : K.map f *ᵥ (fun i => f (y i)) = 0 := by
      rw [GlobalTheory.BesselChar.mulVec_map, hy]; funext i; exact map_zero f
    have hy₂ : K.map g *ᵥ (fun i => g (y i)) = 0 := by
      rw [GlobalTheory.BesselChar.mulVec_map, hy]; funext i; exact map_zero g
    obtain ⟨a₁, ha₁⟩ := k₁ _ hy₁
    obtain ⟨a₂, ha₂⟩ := k₂ _ hy₂
    have ea₁ : (fun i => f (l (a₁ i) (a₂ i))) = a₁ := funext fun i => hl1 _ _
    have ea₂ : (fun i => g (l (a₁ i) (a₂ i))) = a₂ := funext fun i => hl2 _ _
    refine ⟨fun i => l (a₁ i) (a₂ i), extV _ _ ?_ ?_⟩
    · rw [← GlobalTheory.BesselChar.mulVec_map, ha₁]
      conv_lhs => rw [← ea₁, GlobalTheory.BesselChar.mulVec_map]
      funext i
      simp only [Pi.add_apply, map_add]
    · rw [← GlobalTheory.BesselChar.mulVec_map, ha₂]
      conv_lhs => rw [← ea₂, GlobalTheory.BesselChar.mulVec_map]
      funext i
      simp only [Pi.add_apply, map_add]

theorem unip_iff_of_joint : ∀ {A R₁ R₂ : Type} [CommRing A] [CommRing R₁] [CommRing R₂] (f : A →+* R₁) (g : A →+* R₂), (∀ y, f y = 0 → g y = 0 → y = 0) → (∀ a b, ∃ y, f y = a ∧ g y = b) → ∀ {n ρ : ℕ} (E : Matrix (Fin n) (Fin ρ) A) (K : Matrix (Fin ρ) (Fin n) A) (M : Matrix (Fin n) (Fin n) A), GlobalTheory.BesselChar.Unip E K M ↔ GlobalTheory.BesselChar.Unip (E.map f) (K.map f) (M.map f) ∧ GlobalTheory.BesselChar.Unip (E.map g) (K.map g) (M.map g) := by
  intro A R₁ R₂ _ _ _ f g hinj hsurj n ρ E K M
  refine ⟨fun h => ⟨fwd f g hinj hsurj E K M h, fwd g f (fun y hg hf => hinj y hf hg)
    (fun a b => (hsurj b a).imp fun _ h => h.symm) E K M h⟩, fun h => bwd f g hinj hsurj E K M h.1 h.2⟩

end GlobalTheory.BesselChar.JointSplit
