import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.OverCompare

def genSums (F : Type) {E : Type} [Field F] [Field E] [Algebra F E] {k m : ℕ}
    (l : Fin m → Fin k → E) (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R) :
    AddSubgroup (Fin k → E ⊗[F] R) where
  carrier := {u | ∃ t : Fin m → R, (∀ j, t j ∈ S₂) ∧ u = fun i => ∑ j, l j i ⊗ₜ[F] t j}
  zero_mem' := ⟨0, fun _ => zero_mem _, by funext i; simp⟩
  add_mem' := by
    rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
    refine ⟨t + t', fun j => add_mem (ht j) (ht' j), ?_⟩
    funext i
    simp [TensorProduct.tmul_add, Finset.sum_add_distrib]
  neg_mem' := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨-t, fun j => neg_mem (ht j), ?_⟩
    funext i
    simp [TensorProduct.tmul_neg, Finset.sum_neg_distrib]

theorem tmul_mem_genSums {F E : Type} [Field F] [Field E] [Algebra F E] {k m : ℕ}
    (l : Fin m → Fin k → E) (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)
    {x : Fin k → E} (hx : x ∈ Submodule.span ℤ (Set.range l)) {s : R} (hs : s ∈ S₂) :
    (fun i => x i ⊗ₜ[F] s) ∈ genSums F l R S₂ := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
  refine ⟨fun j => c j • s, fun j => zsmul_mem hs _, ?_⟩
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TensorProduct.smul_tmul]

theorem exists_int_generators {E : Type} [Field E] [NumberField E] {k : ℕ}
    (Λ : Submodule (𝓞 E) (Fin k → E)) [Module.Finite (𝓞 E) Λ] :
    ∃ (m : ℕ) (l : Fin m → Fin k → E), (∀ j, l j ∈ Λ) ∧
      ∀ x ∈ Λ, x ∈ Submodule.span ℤ (Set.range l) := by
  have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  refine ⟨m, fun j => (s j : Fin k → E), fun j => (s j).2, fun x hx => ?_⟩
  have h : (⟨x, hx⟩ : Λ) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h
  refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simpa using this

theorem exists_generators_mem_latS_iff :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∃ (m : ℕ) (l : Fin m → Fin k → E), (∀ j, l j ∈ Λ) ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R) (u : Fin k → E ⊗[F] R), u ∈ latS (F := F) R (tensInt (F := F) R (intOE E) S₂) Λ ↔ ∃ t : Fin m → R, (∀ j, t j ∈ S₂) ∧ u = fun i => ∑ j, l j i ⊗ₜ[F] t j := by
  intro F E _ _ _ _ _ k Λ hΛ
  obtain ⟨m, l, hl, hgen⟩ := exists_int_generators Λ
  refine ⟨m, l, hl, fun R _ _ S₂ u => ⟨fun hu => ?_, ?_⟩⟩
  · show u ∈ genSums F l R S₂
    have hst : ∀ s ∈ tensInt (F := F) R (intOE E) S₂, ∀ v ∈ genSums F l R S₂,
        s • v ∈ genSums F l R S₂ := by
      intro s hs
      induction hs using Subring.closure_induction with
      | mem x hx =>
        rintro _ ⟨t, ht, rfl⟩
        rcases hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨y, rfl⟩
        · have e : ((algebraMap (𝓞 E) E a) ⊗ₜ[F] (1 : R)) • (fun i => ∑ j, l j i ⊗ₜ[F] t j) =
              ∑ j, fun i => (a • l j) i ⊗ₜ[F] t j := by
            funext i
            simp [Finset.mul_sum, Algebra.smul_def]
          rw [show ((algebraMap (𝓞 E) E a) ⊗ₜ[F] (1 : R)) • (fun i => ∑ j, l j i ⊗ₜ[F] t j) =
              ∑ j, fun i => (a • l j) i ⊗ₜ[F] t j from e]
          exact sum_mem fun j _ =>
            tmul_mem_genSums l R S₂ (hgen _ (Λ.smul_mem a (hl j))) (ht j)
        · refine ⟨fun j => (y : R) * t j, fun j => mul_mem y.2 (ht j), ?_⟩
          funext i
          simp [Finset.mul_sum]
      | zero => intro v _; rw [zero_smul]; exact zero_mem _
      | one => intro v hv; rwa [one_smul]
      | add x y _ _ hx hy => intro v hv; rw [add_smul]; exact add_mem (hx v hv) (hy v hv)
      | neg x _ hx => intro v hv; rw [neg_smul]; exact neg_mem (hx v hv)
      | mul x y _ _ hx hy => intro v hv; rw [mul_smul]; exact hx _ (hy v hv)
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact tmul_mem_genSums l R S₂ (hgen y hy) (one_mem _)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact hst a a.2 x hx
  · rintro ⟨t, ht, rfl⟩
    have e : (fun i => ∑ j, l j i ⊗ₜ[F] t j) =
        ∑ j, (⟨(1 : E) ⊗ₜ[F] t j, Subring.subset_closure (Or.inr ⟨⟨t j, ht j⟩, rfl⟩)⟩ :
          tensInt (F := F) R (intOE E) S₂) • (fun i => inclE (F := F) R (l j i)) := by
      funext i
      simp [inclE, Subring.smul_def]
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨l j, hl j, rfl⟩)

end GlobalTheory.OverCompare
