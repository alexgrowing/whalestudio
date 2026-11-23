import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexISupMapEqPowStatement
open NumberField ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory

open scoped ComplexOrder

theorem deg_iSup_map_of_gram : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (hW : HermFam K W) (hV : HermFam K V) (p : ℕ) (M : Fin p → (W →ₗ[K] V)) (ℓ : Submodule (𝓞 K) W)
  (y : Matrix (Fin p) (Fin p) K), ℓ.FG → latRank K ℓ = 1 → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (∀ (s : K →+* ℂ) a b, ∀ c ∈ ℓ, hV.form s (M b c) (M a c) = s (y a b) * hW.form s c c) →
  y.det ≠ 0 ∧ deg hV (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) =
    p * deg hW ℓ - (∑ s : K →+* ℂ, Real.log ‖s y.det‖) / (2 * Module.finrank ℚ K) := by
  intro K _ _ W V _ _ _ _ _ _ _ _ hW hV p M ℓ y hfg hrk hinj hind hgram
  have hr : Module.finrank K (Submodule.span K (ℓ : Set W)) = 1 := hrk
  haveI : FiniteDimensional K (Submodule.span K (ℓ : Set W)) :=
    Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  obtain ⟨c, hcℓ, hc0⟩ : ∃ c ∈ ℓ, c ≠ 0 := by
    by_contra hne
    push_neg at hne
    have h0 : Submodule.span K (ℓ : Set W) = ⊥ := by
      rw [Submodule.span_eq_bot]; intro x hx; exact hne x hx
    rw [h0, finrank_bot] at hr; exact zero_ne_one hr
  have hspan : (ℓ : Set W) ⊆ Submodule.span K {c} := by
    have hle : Submodule.span K {c} ≤ Submodule.span K (ℓ : Set W) :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr hcℓ)
    have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hr, finrank_span_singleton hc0])
    rw [heq]; exact Submodule.subset_span
  have hfℓ : IsFrame K ℓ ![c] := by
    refine ⟨fun i => by fin_cases i; simpa using hcℓ, ?_, ?_⟩
    · exact linearIndependent_unique_iff.mpr (by simpa using hc0)
    · intro x hx
      refine Submodule.span_mono ?_ (hspan hx)
      rintro _ rfl; exact ⟨0, rfl⟩
  set v : Fin p → V := fun a => M a c with hvdef
  have hvS : ∀ a, v a ∈ ℓ.map ((M a).restrictScalars (𝓞 K)) := fun a => ⟨c, hcℓ, rfl⟩
  have hfS : IsFrame K (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) v := by
    refine ⟨fun a => (le_iSup (fun a => ℓ.map ((M a).restrictScalars (𝓞 K))) a) (hvS a), ?_, ?_⟩
    · exact iSupIndep.linearIndependent _ hind (fun a => Submodule.subset_span (hvS a))
        (fun a h => hc0 (hinj a (h.trans (map_zero (M a)).symm)))
    · intro x hx
      have hle : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) ≤
          (Submodule.span K (Set.range v)).restrictScalars (𝓞 K) := by
        refine iSup_le fun a => ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp (hspan hz)
        rw [Submodule.restrictScalars_mem, LinearMap.restrictScalars_apply, LinearMap.map_smul]
        exact Submodule.smul_mem _ k (Submodule.subset_span ⟨a, rfl⟩)
      exact hle hx
  have hSfg : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).FG :=
    Submodule.fg_iSup _ (fun a => hfg.map _)
  have hidx : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex
      (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
      ((Submodule.span (𝓞 K) {c}).toAddSubgroup.relIndex ℓ.toAddSubgroup) ^ p := by
    have h1 : Submodule.span (𝓞 K) (Set.range v) =
        ⨆ a, (Submodule.span (𝓞 K) {c}).map ((M a).restrictScalars (𝓞 K)) := by
      rw [Submodule.span_range_eq_iSup]
      congr 1; funext a
      rw [Submodule.map_span, Set.image_singleton]; rfl
    rw [h1]
    exact GlobalTheory.T.relIndex_iSup_map_eq_relIndex_pow K W V p M ℓ _ ((Submodule.span_singleton_le_iff_mem _ _).mpr hcℓ) hinj hind
  have hgr : ∀ s : K →+* ℂ, hV.gram s v = hW.form s c c • (s.mapMatrix y).transpose := by
    intro s; ext i j
    simp [HermFam.gram, v, hgram s j i c hcℓ, mul_comm]
  have hdet : ∀ s : K →+* ℂ, (hV.gram s v).det = (hW.form s c c) ^ p * s y.det := by
    intro s; rw [hgr, Matrix.det_smul, Matrix.det_transpose, RingHom.map_det, Fintype.card_fin]
  have hpos : ∀ s : K →+* ℂ, 0 < (hV.gram s v).det := fun s => (hV.posDef s p v hfS.2.1).det_pos
  have hA1 : ∀ s : K →+* ℂ, 0 < hW.form s c c := fun s => by
    have := (hW.posDef s 1 ![c] hfℓ.2.1).det_pos
    simpa [Matrix.det_fin_one] using this
  have hAeq : ∀ s : K →+* ℂ, hW.form s c c = (((hW.form s c c).re : ℝ) : ℂ) := fun s =>
    Complex.ext (by simp) (by simp [← (Complex.pos_iff.mp (hA1 s)).2])
  have hkey : ∀ s : K →+* ℂ, 0 < (s y.det).re ∧ (s y.det).im = 0 ∧
      (hV.gram s v).det.re = (hW.form s c c).re ^ p * (s y.det).re := by
    intro s
    have h1 := Complex.pos_iff.mp (hpos s)
    have hA := (Complex.pos_iff.mp (hA1 s)).1
    rw [hdet s, hAeq s, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.im_ofReal_mul] at h1
    have hApow : 0 < (hW.form s c c).re ^ p := pow_pos hA p
    refine ⟨pos_of_mul_pos_right h1.1 hApow.le, ?_, ?_⟩
    · exact (mul_eq_zero.mp h1.2.symm).resolve_left hApow.ne'
    · rw [hdet s, hAeq s, ← Complex.ofReal_pow, Complex.re_ofReal_mul]; simp
  have hlogV : ∀ s : K →+* ℂ, Real.log (hV.gram s v).det.re =
      p * Real.log (hW.form s c c).re + Real.log ‖s y.det‖ := by
    intro s
    obtain ⟨hre, him, heq⟩ := hkey s
    have hn : ‖s y.det‖ = (s y.det).re := by
      rw [← Complex.abs_re_eq_norm.mpr him, abs_of_pos hre]
    rw [heq, hn, Real.log_mul (pow_pos (Complex.pos_iff.mp (hA1 s)).1 p).ne' hre.ne', Real.log_pow]
  have hlogW : ∀ s : K →+* ℂ, Real.log (hW.gram s ![c]).det.re = Real.log (hW.form s c c).re := by
    intro s; simp [HermFam.gram, Matrix.det_fin_one]
  refine ⟨?_, ?_⟩
  · obtain ⟨s⟩ : Nonempty (K →+* ℂ) := inferInstance
    intro h; have := (hkey s).1; rw [h, map_zero] at this; simp at this
  · rw [arakelovDegree_eq_degreeOfFamily hV hSfg hfS, arakelovDegree_eq_degreeOfFamily hW hfg hfℓ]
    unfold degreeOfFamily
    have hrg : Set.range ![c] = {c} := by ext x; simp [eq_comm]
    rw [hrg, hidx, Nat.cast_pow, Real.log_pow, Finset.sum_congr rfl (fun s _ => hlogV s),
      Finset.sum_congr rfl (fun s _ => hlogW s), Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

end GlobalTheory
