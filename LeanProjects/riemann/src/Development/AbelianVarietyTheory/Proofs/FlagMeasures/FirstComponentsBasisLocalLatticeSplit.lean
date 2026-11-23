import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem basis_of_span_mod_uniformiser {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ}
    (L₁ : Submodule O (Fin n → K)) (hfg : L₁.FG)
    (hspan : Submodule.span K (L₁ : Set (Fin n → K)) = ⊤)
    (C : Fin n → Fin n → K) (hC : ∀ j, C j ∈ L₁) (g : O)
    (hg : IsLocalRing.maximalIdeal O = Ideal.span {g})
    (hmod : ∀ x ∈ L₁, ∃ s ∈ Submodule.span O (Set.range C), ∃ z ∈ L₁, x = s + (g : K) • z) :
    ∃ fr : GL (Fin n) K, (fr : Matrix (Fin n) (Fin n) K) = Matrix.of (fun a j => C j a) ∧
      ∀ x : Fin n → K, x ∈ L₁ ↔ ∀ a, ((fr⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x a ∈ O := by
  classical
  set M : Matrix (Fin n) (Fin n) K := Matrix.of (fun a j => C j a) with hM
  set N : Submodule O (Fin n → K) := Submodule.span O (Set.range C) with hN
  have hsm : ∀ (c : O) (y : Fin n → K), c • y = (c : K) • y := fun c y => rfl
  have hNL : N ≤ L₁ := Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hC j)
  have hLN : L₁ ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O) hfg ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · intro x hx
      obtain ⟨s, hs, z, hz, rfl⟩ := hmod x hx
      refine Submodule.add_mem_sup hs ?_
      rw [← hsm]
      exact Submodule.smul_mem_smul (by rw [hg]; exact Ideal.mem_span_singleton_self g) hz
  have hCspan : Submodule.span K (Set.range C) = ⊤ := by
    rw [eq_top_iff, ← hspan, ← Submodule.span_span_of_tower O K (Set.range C)]
    exact Submodule.span_mono (fun x hx => hLN hx)
  have hMT : M.col = C := by ext j a; rfl
  have hsurj : Function.Surjective M.mulVec := by
    have h := Matrix.range_mulVecLin M
    rw [hMT, hCspan, LinearMap.range_eq_top] at h
    exact h
  have hunit : IsUnit M := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
  have hMv : ∀ w : Fin n → K, M *ᵥ w = ∑ j, w j • C j := by
    intro w; ext a
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hinvM : ((hunit.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M = 1 := hunit.unit.inv_mul
  have hMinv : M * ((hunit.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := hunit.unit.mul_inv
  refine ⟨hunit.unit, rfl, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp (hLN hx)
    have hx' : x = M *ᵥ (fun j => (c j : K)) := by
      rw [hMv, ← hc]; simp only [hsm]
    intro a
    rw [hx', Matrix.mulVec_mulVec, hinvM, Matrix.one_mulVec]
    exact (c a).2
  · apply hNL
    set w := ((hunit.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x with hw
    have hx' : x = M *ᵥ w := by rw [hw, Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
    rw [hx', hMv]
    refine (Submodule.mem_span_range_iff_exists_fun O).mpr ⟨fun j => ⟨w j, hx j⟩, ?_⟩
    simp only [hsm]

theorem first_components_basis :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (c : Fin n → Fin n → E ⊗[F] v.adicCompletion F) (S : Set (Fin n → E ⊗[F] v.adicCompletion F)), (∀ j, c j ∈ loc v L) → (∀ x ∈ S, ∀ a, (sp (x a)).1 = 0) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range c ∪ S) y) → ∃ fr : GL (Fin n) (v.adicCompletion F), (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Matrix.of (fun a j => (sp (c j a)).1) ∧ ∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a) ↔ ∀ a, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x a ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ _ cm n J _ _ v sp _ hsp1 hint g hg L hL c S hc hS hmod
  classical
  let πv : (Fin n → E ⊗[F] v.adicCompletion F) → (Fin n → v.adicCompletion F) := fun y a => (sp (y a)).1
  let ι : (Fin n → E) → (Fin n → E ⊗[F] v.adicCompletion F) := fun l i => l i ⊗ₜ[F] (1 : v.adicCompletion F)
  have hfstO : ∀ r : intV E v, (sp (r : E ⊗[F] v.adicCompletion F)).1 ∈ v.adicCompletionIntegers F :=
    fun r => ((hint r).mp r.2).1
  have hπsmul : ∀ (r : intV E v) (y : Fin n → E ⊗[F] v.adicCompletion F),
      πv (r • y) = (⟨_, hfstO r⟩ : v.adicCompletionIntegers F) • πv y := by
    intro r y; funext a
    change (sp ((r : E ⊗[F] v.adicCompletion F) * y a)).1 = (sp (r : E ⊗[F] v.adicCompletion F)).1 * (sp (y a)).1
    rw [map_mul, Prod.fst_mul]
  have hproj : ∀ (T : Set (Fin n → E ⊗[F] v.adicCompletion F)) (y), y ∈ Submodule.span (intV E v) T →
      πv y ∈ Submodule.span (v.adicCompletionIntegers F) (πv '' T) := by
    intro T y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have h0 : πv 0 = 0 := by funext a; simp [πv]
      rw [h0]; exact zero_mem _
    | add x y _ _ hx hy =>
      have h0 : πv (x + y) = πv x + πv y := by funext a; simp [πv]
      rw [h0]; exact add_mem hx hy
    | smul r x _ hx =>
      rw [hπsmul]; exact Submodule.smul_mem _ _ hx
  have hιπ_add : ∀ x y : Fin n → E, πv (ι (x + y)) = πv (ι x) + πv (ι y) := by
    intro x y; funext a; simp [πv, ι, TensorProduct.add_tmul]
  have hιπ_zero : πv (ι 0) = 0 := by funext a; simp [πv, ι]
  have hιπ_smul : ∀ (e : E) (x : Fin n → E), πv (ι (e • x)) = (sp (e ⊗ₜ[F] (1 : v.adicCompletion F))).1 • πv (ι x) := by
    intro e x; funext a
    change (sp ((e * x a) ⊗ₜ[F] (1 : v.adicCompletion F))).1 =
      (sp (e ⊗ₜ[F] (1 : v.adicCompletion F))).1 * (sp (x a ⊗ₜ[F] (1 : v.adicCompletion F))).1
    rw [show (e * x a) ⊗ₜ[F] (1 : v.adicCompletion F) =
      (e ⊗ₜ[F] (1 : v.adicCompletion F)) * (x a ⊗ₜ[F] (1 : v.adicCompletion F)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one], map_mul, Prod.fst_mul]
  have hφO : ∀ e : 𝓞 E, (sp ((e : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 ∈ v.adicCompletionIntegers F := by
    intro e
    have hm : (e : E) ⊗ₜ[F] (1 : v.adicCompletion F) ∈ intV E v := by
      unfold intV tensInt
      exact Subring.subset_closure (Or.inl ⟨⟨(e : E), by unfold intOE; exact RingHom.mem_range.mpr ⟨e, rfl⟩⟩, rfl⟩)
    exact hfstO ⟨_, hm⟩
  have hι : ∀ l ∈ L, ι l ∈ loc v L := fun l hl => Submodule.subset_span ⟨l, hl, rfl⟩
  let L₁ : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F) :=
    { carrier := {x | ∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a}
      add_mem' := by
        rintro x x' ⟨y, hy, hyx⟩ ⟨y', hy', hyx'⟩
        exact ⟨y + y', add_mem hy hy', fun a => by simp [hyx, hyx']⟩
      zero_mem' := ⟨0, zero_mem _, fun a => by simp⟩
      smul_mem' := by
        rintro r x ⟨y, hy, hyx⟩
        have h1r : ((1 : E) ⊗ₜ[F] (r : v.adicCompletion F)) ∈ intV E v :=
          (hint _).mpr ⟨by rw [hsp1]; exact r.2, by rw [hsp1]; exact r.2⟩
        refine ⟨(⟨_, h1r⟩ : intV E v) • y, Submodule.smul_mem _ _ hy, fun a => ?_⟩
        change (sp (((1 : E) ⊗ₜ[F] (r : v.adicCompletion F)) * y a)).1 = (r : v.adicCompletion F) * x a
        rw [map_mul, Prod.fst_mul, hsp1, hyx a] }
  let C : Fin n → Fin n → v.adicCompletion F := fun j => πv (c j)
  have hC : ∀ j, C j ∈ L₁ := fun j => ⟨c j, hc j, fun a => rfl⟩
  have hfg : L₁.FG := by
    obtain ⟨s, hs⟩ := (Module.Finite.iff_fg (N := L)).mp hL.1
    refine ⟨s.image (fun l => πv (ι l)), le_antisymm ?_ ?_⟩
    · rw [Finset.coe_image, Submodule.span_le]
      rintro _ ⟨l, hl, rfl⟩
      exact ⟨ι l, hι l (hs ▸ Submodule.subset_span hl), fun a => rfl⟩
    · rintro x ⟨y, hy, hyx⟩
      have hx : x = πv y := funext fun a => (hyx a).symm
      rw [hx]
      refine (Submodule.span_le.mpr ?_) (hproj (ι '' (L : Set (Fin n → E))) y hy)
      rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      rw [← hs] at hl
      induction hl using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨x, hx, rfl⟩)
      | zero => rw [hιπ_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [hιπ_add]; exact add_mem hx hy
      | smul e x _ hx =>
        have h0 : πv (ι (e • x)) = (⟨_, hφO e⟩ : v.adicCompletionIntegers F) • πv (ι x) :=
          hιπ_smul (e : E) x
        rw [h0]; exact Submodule.smul_mem _ _ hx
  have hspan : Submodule.span (v.adicCompletion F) (L₁ : Set (Fin n → v.adicCompletion F)) = ⊤ := by
    have key : ∀ x ∈ Submodule.span E (L : Set (Fin n → E)),
        πv (ι x) ∈ Submodule.span (v.adicCompletion F) (L₁ : Set (Fin n → v.adicCompletion F)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨ι x, hι x hx, fun a => rfl⟩
      | zero => rw [hιπ_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [hιπ_add]; exact add_mem hx hy
      | smul e x _ hx => rw [hιπ_smul]; exact Submodule.smul_mem _ _ hx
    rw [Submodule.eq_top_iff']
    intro x
    rw [pi_eq_sum_univ x]
    refine Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ ?_)
    have h := key (fun j => if a = j then (1 : E) else 0) (by rw [hL.2]; trivial)
    convert h using 1
    funext j
    by_cases h' : a = j <;> simp [πv, ι, hsp1, h']
  have hmod' : ∀ x ∈ L₁, ∃ s ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range C), ∃ z ∈ L₁,
      x = s + (((g : ℕ) : v.adicCompletionIntegers F) : v.adicCompletion F) • z := by
    rintro x ⟨y, hy, hyx⟩
    obtain ⟨s, hs, z, hz, hyz⟩ := hmod y hy
    refine ⟨πv s, ?_, πv z, ⟨z, hz, fun a => rfl⟩, ?_⟩
    · refine (Submodule.span_le.mpr ?_) (hproj _ s hs)
      rintro _ ⟨w, hw, rfl⟩
      rcases hw with ⟨j, rfl⟩ | hw
      · exact Submodule.subset_span ⟨j, rfl⟩
      · have h0 : πv w = 0 := funext fun a => hS w hw a
        rw [h0]; exact zero_mem _
    · funext a
      rw [← hyx a, hyz]
      simp [πv]
  obtain ⟨fr, hfr, hmem⟩ :=
    basis_of_span_mod_uniformiser (v.adicCompletionIntegers F) L₁ hfg hspan C hC _ hg hmod'
  exact ⟨fr, hfr, hmem⟩

end GlobalTheory.St.G
