import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def Cls0 : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
  (α β : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0),
  ev α.1 0 0 (by simp) X (𝟙 X) = ev β.1 0 0 (by simp) X (𝟙 X) → CohomologyClass.mk α = CohomologyClass.mk β

def OneEx : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
  ∃ c : Ht q (sp A) 0 0, ∃ α : Cocycle ((chains (ZMod q)).obj (sp A)) (res (ZMod q) (tw q 0)) 0,
    CohomologyClass.mk α = c ∧
    ∀ (U : Scheme.{0}) (x : Sx (sp A) 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ

theorem etale_kummer_degree_zero_cohomology_of_twist_section_class_and_root_ex (hT : TwSec) (hC : Cls0) (hO : OneEx) : H0 := by
  intro h9 q _ A _ hA hq
  obtain ⟨hne, hb⟩ := hT q A hA hq
  obtain ⟨ζ⟩ := hne
  have hb0 := hb 0 ζ
  obtain ⟨_, e, -, he⟩ := h9 (ZMod q) (tw q 0)
  have hone : one q (sp A) = e (Spec (CommRingCat.of A)) (twGen 0 ζ) := by
    obtain ⟨α, hα, hv⟩ := pick_spec (hO q A hA hq)
    have hα' : CohomologyClass.mk α = one q (sp A) := hα
    obtain ⟨β, hβ, hβv⟩ := he (Spec (CommRingCat.of A)) (twGen 0 ζ)
    rw [← hα', ← hβ]
    exact hC _ _ _ α β ((hv _ (𝟙 _) ζ).trans hβv.symm)
  have hlin : ∀ t : ZMod q, t • one q (sp A) =
      e (Spec (CommRingCat.of A)) ((ULift.up t : ULift.{1} (ZMod q)) • twGen 0 ζ) := by
    intro t
    rw [hone]
    have h1 : t = ((t.val : ℕ) : ZMod q) := (ZMod.natCast_zmod_val t).symm
    have h2 : (ULift.up t : ULift.{1} (ZMod q)) = ((t.val : ℕ) : ULift.{1} (ZMod q)) := by
      apply ULift.ext
      rw [ULift.down_natCast]; exact h1
    rw [h2, Nat.cast_smul_eq_nsmul, map_nsmul]
    conv_lhs => rw [h1]
    rw [Nat.cast_smul_eq_nsmul]
  have hfun : (fun t : ZMod q => t • one q (sp A)) =
      (e (Spec (CommRingCat.of A))) ∘ (fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • twGen 0 ζ) := funext hlin
  rw [hfun]
  exact (e _).bijective.comp hb0

end LateralTheory.KummerTheory
