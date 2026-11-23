import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleMembershipLocalStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul)
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.PerfdLat (piMap piMap_apply)

namespace GlobalTheory.LatGlue

variable {Y : Scheme.{0}} {h : ℕ}

theorem piMap_resG_piMap_resG {U W W' : Y.Opens} (h₁ : W ≤ U) (h₂ : W' ≤ W) (u : Fin h → Γ(Y, U)) :
    piMap (resG Y h₂) (Fin h) (piMap (resG Y h₁) (Fin h) u) = piMap (resG Y (h₂.trans h₁)) (Fin h) u := by
  funext l
  simp only [piMap_apply]
  exact GlobalTheory.LB.resG_resG h₁ h₂ (u l)

theorem piMap_mem_span_image {U W W' : Y.Opens} (h₁ : W ≤ U) (h₂ : W' ≤ W) (S : Set (Fin h → Γ(Y, U)))
    {v : Fin h → Γ(Y, W)} (hv : v ∈ Submodule.span Γ(Y, W) (piMap (resG Y h₁) (Fin h) '' S)) :
    piMap (resG Y h₂) (Fin h) v ∈ Submodule.span Γ(Y, W') (piMap (resG Y (h₂.trans h₁)) (Fin h) '' S) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    exact Submodule.subset_span ⟨u, hu, (piMap_resG_piMap_resG h₁ h₂ u).symm⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul a x _ hx =>
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ hx

theorem exists_mem_span_of_mem_localSpan {I : Type} {V : I → Y.Opens}
    {P : ∀ i, Submodule Γ(Y, V i) (Fin h → Γ(Y, V i))}
    (hV : ∀ (i j : I) (y : Y), y ∈ V i → y ∈ V j → ∃ k, y ∈ V k ∧ V k ≤ V i ∧ V k ≤ V j)
    (hP : ∀ (i k : I) (hle : V k ≤ V i),
      P k = Submodule.span Γ(Y, V k) (piMap (resG Y hle) (Fin h) '' (P i : Set (Fin h → Γ(Y, V i)))))
    (i : I) {W : Y.Opens} (hle : W ≤ V i) {y : Y} (hy : y ∈ W) {v : Fin h → Γ(Y, W)} (hv : v ∈ localSpan V P W) :
    ∃ (W' : Y.Opens) (h' : W' ≤ W), y ∈ W' ∧ piMap (resG Y h') (Fin h) v ∈
      Submodule.span Γ(Y, W') (piMap (resG Y (h'.trans hle)) (Fin h) '' (P i : Set (Fin h → Γ(Y, V i)))) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, u, hu, rfl⟩ := hx
    obtain ⟨k, hyk, hki, hkj⟩ := hV i j y (hle hy) (hj hy)
    refine ⟨W ⊓ V k, inf_le_left, ⟨hy, hyk⟩, ?_⟩
    have m : piMap (resG Y hkj) (Fin h) u ∈ P k := by
      rw [hP j k hkj]
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    rw [hP i k hki] at m
    have m' := piMap_mem_span_image hki (inf_le_right : W ⊓ V k ≤ V k) _ m
    rw [piMap_resG_piMap_resG] at m' ⊢
    exact m'
  | zero => exact ⟨W, le_rfl, hy, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨W₁, h₁, hy₁, m₁⟩ := hx
    obtain ⟨W₂, h₂, hy₂, m₂⟩ := hz
    refine ⟨W₁ ⊓ W₂, inf_le_left.trans h₁, ⟨hy₁, hy₂⟩, ?_⟩
    have e₁ := piMap_mem_span_image _ (inf_le_left : W₁ ⊓ W₂ ≤ W₁) _ m₁
    have e₂ := piMap_mem_span_image _ (inf_le_right : W₁ ⊓ W₂ ≤ W₂) _ m₂
    rw [piMap_resG_piMap_resG] at e₁ e₂
    rw [map_add]
    exact add_mem e₁ e₂
  | smul a x _ hx =>
    obtain ⟨W₁, h₁, hy₁, m₁⟩ := hx
    refine ⟨W₁, h₁, hy₁, ?_⟩
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ m₁

theorem mem_glueSub_sec_iff_of_isAffineOpen (Y : Scheme.{0}) (h : ℕ) (I : Type) (V : I → Y.Opens)
    (P : ∀ i, Submodule Γ(Y, V i) (Fin h → Γ(Y, V i)))
    (hV : ∀ (i j : I) (y : Y), y ∈ V i → y ∈ V j → ∃ k, y ∈ V k ∧ V k ≤ V i ∧ V k ≤ V j)
    (hP : ∀ (i k : I) (hle : V k ≤ V i),
      P k = Submodule.span Γ(Y, V k) (piMap (resG Y hle) (Fin h) '' (P i : Set (Fin h → Γ(Y, V i)))))
    (i : I) (W : Y.Opens) (hW : IsAffineOpen W) (hle : W ≤ V i) (s : Γ(freeModule Y (Fin h), W)) :
    s ∈ (glueSub V P).sec W ↔ coords Y h W s ∈
      Submodule.span Γ(Y, W) (piMap (resG Y hle) (Fin h) '' (P i : Set (Fin h → Γ(Y, V i)))) := by
  rw [mem_glueSub_sec]
  constructor
  · intro hs
    refine GlobalTheory.T.submodule_membership_local Y h W hW _ _ fun y hy => ?_
    obtain ⟨W₁, h₁, hy₁, m₁⟩ := hs y hy
    obtain ⟨W₂, h₂, hy₂, m₂⟩ := exists_mem_span_of_mem_localSpan hV hP i (h₁.trans hle) hy₁ m₁
    refine ⟨W₂, h₂.trans h₁, hy₂, ?_⟩
    rw [coords_resM, piMap_resG_piMap_resG] at m₂
    refine Submodule.span_mono ?_ m₂
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨piMap (resG Y hle) (Fin h) u, Submodule.subset_span ⟨u, hu, rfl⟩, piMap_resG_piMap_resG _ _ u⟩
  · intro hs y hy
    refine ⟨W, le_rfl, hy, ?_⟩
    rw [resM_self]
    refine Submodule.span_mono ?_ hs
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨i, hle, u, hu, rfl⟩

end GlobalTheory.LatGlue
