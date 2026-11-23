import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFamilyBaseChangeExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeFrameBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLatticeIndexBaseChangePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineLatticeBaseChangeStatement
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.LatExt

open Module

theorem form_zero_right {F V : Type} [Field F] [AddCommGroup V] [Module F V] (h : HermFam F V) (σ : F →+* ℂ) (x : V) :
    h.form σ x 0 = 0 := by
  have := h.smul_right σ 0 x 0
  simpa using this

theorem form_sum_right {F V ι : Type} [Field F] [AddCommGroup V] [Module F V] (h : HermFam F V) (σ : F →+* ℂ) (x : V)
    (s : Finset ι) (g : ι → V) : h.form σ x (∑ i ∈ s, g i) = ∑ i ∈ s, h.form σ x (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using form_zero_right h σ x
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_right, ih]

theorem sum_single {F : Type} [Field F] {m : ℕ} (y : Fin m → F) : y = ∑ j, y j • Pi.single j (1 : F) := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem form_expand {F : Type} [Field F] {m : ℕ} (h : HermFam F (Fin m → F)) (σ : F →+* ℂ) (x y : Fin m → F) :
    h.form σ x y = ∑ j, σ (y j) * starRingEnd ℂ (∑ i, σ (x i) * h.form σ (Pi.single j 1) (Pi.single i 1)) := by
  have hr : ∀ u w : Fin m → F, h.form σ u w = ∑ j, σ (w j) * h.form σ u (Pi.single j 1) := fun u w => by
    conv_lhs => rw [sum_single w]
    rw [form_sum_right]
    exact Finset.sum_congr rfl fun j _ => h.smul_right σ _ _ _
  rw [hr x y]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hr, h.conj_symm]

theorem formBC : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (m : ℕ)
    (h : HermFam K (Fin m → K)) (h' : HermFam K' (Fin m → K')), IsBC h h' → ∀ (σ : K' →+* ℂ) (x y : Fin m → K),
    h'.form σ (fun i => algebraMap K K' (x i)) (fun i => algebraMap K K' (y i)) = h.form (σ.comp (algebraMap K K')) x y := by
  intro K K' _ _ _ _ _ m h h' hh σ x y
  rw [form_expand h', form_expand h]
  have e := hh σ
  simp only [e, RingHom.comp_apply]

theorem map_mem_span {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] {m : ℕ}
    (L : Submodule (𝓞 K) (Fin m → K)) {z : Fin m → K} (hz : z ∈ Submodule.span K (L : Set (Fin m → K))) :
    (fun i => algebraMap K K' (z i)) ∈ Submodule.span K' (latBC K' L : Set (Fin m → K')) := by
  induction hz using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
  | zero =>
    have e : (fun i => algebraMap K K' ((0 : Fin m → K) i)) = 0 := by funext i; simp
    rw [e]; exact zero_mem _
  | add x y _ _ hx hy =>
    have e : (fun i => algebraMap K K' ((x + y) i)) = (fun i => algebraMap K K' (x i)) + fun i => algebraMap K K' (y i) := by
      funext i; simp
    rw [e]; exact add_mem hx hy
  | smul a x _ hx =>
    have e : (fun i => algebraMap K K' ((a • x) i)) = algebraMap K K' a • fun i => algebraMap K K' (x i) := by
      funext i; simp
    rw [e]; exact Submodule.smul_mem _ _ hx

theorem fgBC : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), L.FG → (latBC K' L).FG := by
  intro K K' _ _ _ _ _ m L ⟨S, hS⟩
  classical
  refine ⟨S.image (fun v i => algebraMap K K' (v i)), le_antisymm ?_ ?_⟩
  · rw [Finset.coe_image]
    exact Submodule.span_mono (Set.image_mono (by rw [← hS]; exact Submodule.subset_span))
  · unfold latBC
    rw [Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    rw [SetLike.mem_coe, ← hS] at hl
    rw [Finset.coe_image]
    induction hl using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have e : (fun i => algebraMap K K' ((0 : Fin m → K) i)) = 0 := by funext i; simp
      show (fun i => algebraMap K K' ((0 : Fin m → K) i)) ∈ _
      rw [e]; exact zero_mem _
    | add x y _ _ hx hy =>
      show (fun i => algebraMap K K' ((x + y) i)) ∈ _
      have e : (fun i => algebraMap K K' ((x + y) i)) = (fun i => algebraMap K K' (x i)) + fun i => algebraMap K K' (y i) := by
        funext i; simp
      rw [e]; exact add_mem hx hy
    | smul a x _ hx =>
      show (fun i => algebraMap K K' ((a • x) i)) ∈ _
      have hc : algebraMap (𝓞 K') K' (algebraMap (𝓞 K) (𝓞 K') a) = algebraMap K K' (algebraMap (𝓞 K) K a) := rfl
      have e : (fun i => algebraMap K K' ((a • x) i)) = algebraMap (𝓞 K) (𝓞 K') a • fun i => algebraMap K K' (x i) := by
        funext i
        rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, hc]
      rw [e]; exact Submodule.smul_mem _ _ hx

theorem fullBC : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), Full L → Full (latBC K' L) := by
  intro K K' _ _ _ _ _ m L ⟨hfg, hsp⟩
  refine ⟨fgBC K K' m L hfg, eq_top_iff.2 ?_⟩
  rw [← (Pi.basisFun K' (Fin m)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have h1 := map_mem_span (K' := K') L (z := Pi.single i 1) (by rw [hsp]; trivial)
  have e : (fun j => algebraMap K K' ((Pi.single i (1 : K) : Fin m → K) j)) = Pi.single i 1 := by
    funext j; by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  rw [e] at h1
  simpa using h1

theorem sumExt (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (F : (K →+* ℂ) → ℝ) :
    ∑ σ : K' →+* ℂ, F (σ.comp (algebraMap K K')) = (finrank K K' : ℝ) * ∑ σ : K →+* ℂ, F σ := by
  classical
  have h0 : ∀ τ : K →+* ℂ, Nat.card {σ : K' →+* ℂ // σ.comp (algebraMap K K') = τ} = finrank K K' := fun τ => by
    letI : Algebra K ℂ := τ.toAlgebra
    haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
    rw [← AlgHom.card K K' ℂ, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr ⟨fun σ => { σ.1 with commutes' := fun x => RingHom.congr_fun σ.2 x },
      fun φ => ⟨φ.toRingHom, RingHom.ext fun x => φ.commutes x⟩, fun σ => rfl, fun φ => rfl⟩
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun σ : K' →+* ℂ => σ.comp (algebraMap K K')), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => F τ) (fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2]),
    Finset.sum_const, nsmul_eq_mul, ← h0 τ, Nat.card_eq_fintype_card, Fintype.card_subtype, mul_comm]

theorem ext_deg_rank_line : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (m : ℕ) (h : HermFam K (Fin m → K)) (L : Submodule (𝓞 K) (Fin m → K)), L.FG → (∃ h' : HermFam K' (Fin m → K'), IsBC h h') ∧ (Full L → Full (latBC K' L)) ∧ ∀ h' : HermFam K' (Fin m → K'), IsBC h h' → deg h' (latBC K' L) = deg h L ∧ latRank K' (latBC K' L) = latRank K L ∧ ∀ x : Fin m → K, latBC K' (lineLat L x) = lineLat (latBC K' L) (fun i => algebraMap K K' (x i)) := by
  intro K K' _ _ _ _ _ m h L hL
  refine ⟨GlobalTheory.T.hermitian_family_base_change_exists K K' m h, fullBC K K' m L, fun h' hh' => ?_⟩
  obtain ⟨v, hv⟩ := exists_isFrame L hL
  have hv' := GlobalTheory.T.lattice_frame_base_change K K' m L _ v hv
  have hL' := fgBC K K' m L hL
  refine ⟨?_, hv'.card_eq.symm, GlobalTheory.T.line_lattice_base_change K K' m L hL⟩
  rw [arakelovDegree_eq_degreeOfFamily h' hL' hv', arakelovDegree_eq_degreeOfFamily h hL hv]
  unfold degreeOfFamily
  rw [GlobalTheory.T.frame_lattice_index_base_change_pow K K' m L _ v hL hv]
  have hg : ∀ σ : K' →+* ℂ, h'.gram σ (fun j i => algebraMap K K' (v j i)) = h.gram (σ.comp (algebraMap K K')) v :=
    fun σ => by ext a b; exact formBC K K' m h h' hh' σ (v a) (v b)
  simp only [hg]
  rw [sumExt K K' (fun σ => Real.log (h.gram σ v).det.re), ← Module.finrank_mul_finrank ℚ K K', Nat.cast_pow,
    Real.log_pow]
  haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  have hd : (0 : ℝ) < finrank K K' := by exact_mod_cast Module.finrank_pos
  have hq : (0 : ℝ) < finrank ℚ K := by exact_mod_cast Module.finrank_pos
  push_cast
  field_simp

end GlobalTheory.LatExt
