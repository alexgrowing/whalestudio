import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeExtendedLatticeGaloisLeStatement
open NumberField GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.SlopeMaxExt

open Module Matrix

section One

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {N : (K →+* ℂ) → V → ℝ} {L : Submodule (𝓞 K) V}

omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem fg_of_le (hL : L.FG) {M : Submodule (𝓞 K) V} (hM : M ≤ L) : M.FG := by
  haveI : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL
  exact isNoetherian_submodule.1 inferInstance M hM

theorem exists_slope_eq (hN : HasGram N) (hL : L.FG) (h0 : L ≠ ⊥) :
    ∃ M : Submodule (𝓞 K) V, M ≤ L ∧ M ≠ ⊥ ∧ slope_sq N M = slopeMax_sq N L := by
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  obtain ⟨hLat, -, -⟩ := Formalism.HN.plLat K V _ b X (fun v => (hG v).1) L hL
  obtain ⟨-, -, ⟨M, hM, hM0, hMs⟩, -, -⟩ := Formalism.HN.muChar _ _ _ _ L hLat h0
  refine ⟨M, hM.1, hM0, ?_⟩
  rw [slope_sq_eq hG (fg_of_le hL hM.1), (slopeMax_slopeMin_eq hG hL h0).1]
  simp only [Formalism.HN.muDef, Formalism.HN.muMaxDef, hMs]

theorem slope_le_slopeMax (hN : HasGram N) (hL : L.FG) {M : Submodule (𝓞 K) V} (hM : M ≤ L) (hM0 : M ≠ ⊥) :
    slope_sq N M ≤ slopeMax_sq N L := by
  letI : StarRing K := starRingOfComm
  have h0 : L ≠ ⊥ := fun h => hM0 (eq_bot_iff.2 (h ▸ hM))
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  have l1 := (Formalism.HN.plLat K V _ b X (fun v => (hG v).1) M (fg_of_le hL hM)).1
  have l2 := (Formalism.HN.plLat K V _ b X (fun v => (hG v).1) L hL).1
  have m1 := Formalism.HN.muChar _ _ _ _ _ l1 hM0
  have m2 := (Formalism.HN.muChar _ _ _ _ _ l2 h0).1
  have key := (m1.1 _).2 fun P hP => (m2 _).1 le_rfl P (hP.trans hM)
  have := m1.2.2.2.2
  rw [slope_sq_eq hG (fg_of_le hL hM), (slopeMax_slopeMin_eq hG hL h0).1]
  unfold Formalism.HN.muDef Formalism.HN.muMaxDef
  linarith

end One

section Two

variable {K K' V V' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V']
  (ι : V →ₛₗ[algebraMap K K'] V')

omit [NumberField K] [NumberField K'] in

theorem map_mem_of_mem_span {s : Set V} {P : Submodule (𝓞 K') V'} (hs : ∀ x ∈ s, ι x ∈ P) {x : V}
    (hx : x ∈ Submodule.span (𝓞 K) s) : ι x ∈ P := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => rw [map_zero]; exact P.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact P.add_mem hx hy
  | smul a x _ hx =>
    have : ι (a • x) = algebraMap (𝓞 K) (𝓞 K') a • ι x := by
      rw [← algebraMap_smul K a, map_smulₛₗ, ← algebraMap_smul K' (algebraMap (𝓞 K) (𝓞 K') a)]
      rfl
    rw [this]; exact P.smul_mem _ hx

omit [NumberField K] [NumberField K'] in

theorem fg_span_image {L : Submodule (𝓞 K) V} (hL : L.FG) :
    (Submodule.span (𝓞 K') (ι '' (L : Set V))).FG := by
  obtain ⟨s, rfl⟩ := hL
  refine Submodule.fg_def.2 ⟨ι '' s, s.finite_toSet.image _, le_antisymm ?_ ?_⟩
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact map_mem_of_mem_span ι (fun y hy => Submodule.subset_span (Set.mem_image_of_mem _ hy)) hx

omit [NumberField K] [NumberField K'] [IsScalarTower (𝓞 K) K V] [IsScalarTower (𝓞 K') K' V'] in

theorem span_image_ne_bot
    (hli : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k)))
    {L : Submodule (𝓞 K) V} (h0 : L ≠ ⊥) : Submodule.span (𝓞 K') (ι '' (L : Set V)) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have h1 := (hli 1 (fun _ => x) (linearIndependent_unique_iff.2 hx0)).ne_zero 0
  intro h
  exact h1 (Submodule.span_eq_bot.1 h _ ⟨x, hx, rfl⟩)

end Two

theorem exists_frame {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (τ : K →+* ℂ) {t : ℝ} (ht : 0 < t) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, IsUnit Y.det ∧ ∀ x, Formalism.HermitianLatticesTheory.cnorm (Y⁻¹ *ᵥ fun i => τ (b.repr x i)) =
      t * Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk τ) x := by
  have hs : ∀ u : Fin n → ℂ, Formalism.HermitianLatticesTheory.cnorm ((t : ℂ) • u) = t * Formalism.HermitianLatticesTheory.cnorm u := fun u => by
    unfold Formalism.HermitianLatticesTheory.cnorm
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht.le]
  have key : ∀ Z : Matrix (Fin n) (Fin n) ℂ, IsUnit Z.det →
      (∀ x, Formalism.HermitianLatticesTheory.cnorm (Z *ᵥ fun i => τ (b.repr x i)) = Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk τ) x) →
      ∃ Y : Matrix (Fin n) (Fin n) ℂ, IsUnit Y.det ∧ ∀ x, Formalism.HermitianLatticesTheory.cnorm (Y⁻¹ *ᵥ fun i => τ (b.repr x i)) =
        t * Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk τ) x := fun Z hZ h => by
    have hu : IsUnit ((t : ℂ) • Z).det := by
      rw [det_smul]
      exact (IsUnit.pow _ (Ne.isUnit (by exact_mod_cast ht.ne'))).mul hZ
    refine ⟨((t : ℂ) • Z)⁻¹, isUnit_nonsing_inv_det _ hu, fun x => ?_⟩
    rw [nonsing_inv_nonsing_inv _ hu, smul_mulVec, hs, h]
  have hi := isUnit_nonsing_inv_det _ (hX (InfinitePlace.mk τ))
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · refine key _ hi fun x => ?_
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
    rw [h]
  · refine key ((starRingEnd ℂ).mapMatrix (X (InfinitePlace.mk τ))⁻¹) ?_ fun x => ?_
    · rw [← RingHom.map_det]; exact hi.map _
    · unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt Formalism.HermitianLatticesTheory.cnorm
      rw [h]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.norm_conj]
      simp [Matrix.mulVec, dotProduct]

def coordExt {K V : Type} (F : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) : V →ₛₗ[algebraMap K F] (Fin n → F) where
  toFun x i := algebraMap K F (b.repr x i)
  map_add' x y := by funext i; simp
  map_smul' a x := by funext i; simp

theorem coordExt_li {K V : Type} (F : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (m : ℕ) (e : Fin m → V) (he : LinearIndependent K e) :
    LinearIndependent F fun k => coordExt F b (e k) :=
  (linearIndependent_algebraMap_comp_iff (S := F) (v := fun k => b.equivFun (e k))).2
    (he.map' b.equivFun.toLinearMap b.equivFun.ker)

theorem slopeMax_sq_span_le : ∀ (K K' V V' : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field K'] [NumberField K'] [Algebra K K'] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V'] (N : (K →+* ℂ) → V → ℝ) (N' : (K' →+* ℂ) → V' → ℝ) (ι : V →ₛₗ[algebraMap K K'] V') (L : Submodule (𝓞 K) V) (c : (K' →+* ℂ) → ℝ) (B : ℝ), HasGram N → HasGram N' → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → (∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k))) → L.FG → L ≠ ⊥ → (∀ σ', 0 < c σ' ∧ |Real.log (c σ')| ≤ B) → (∀ σ' x, N' σ' (ι x) = c σ' * N (σ'.comp (algebraMap K K')) x) → slopeMax_sq N' (Submodule.span (𝓞 K') (ι '' (L : Set V))) ≤ slopeMax_sq N L + 2 * B := by
  intro K K' V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ N N' ι L c B hN hN' hc hli hL h0 hcB hι
  haveI : IsTotallyComplex K' := isTotallyComplex_of_algebra K K'
  haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  haveI : IsAlgClosure K (AlgebraicClosure K') := ⟨inferInstance, Algebra.IsAlgebraic.trans K K' _⟩
  let F : Type := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  haveI : IsGalois K F := inferInstance
  haveI : NumberField F := NumberField.of_module_finite K F
  have hL' := fg_span_image ι hL
  obtain ⟨M, hM, hM0, hMs⟩ := exists_slope_eq hN' hL' (span_image_ne_bot ι hli h0)
  have hMfg := fg_of_le hL' hM
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN'
  letI : StarRing K' := starRingOfComm
  let N₁ : (K' →+* ℂ) → V' → ℝ := fun σ x => N' (InfinitePlace.mk σ).embedding x
  have hG₁ : IsGram b X N₁ := fun v => ⟨(hG v).1, fun x => by
    simp only [N₁, InfinitePlace.mk_embedding]; exact (hG v).2 x⟩
  have hc₁ : ∀ σ x, N₁ ((starRingEnd ℂ).comp σ) x = N₁ σ x := fun σ x => by
    have : InfinitePlace.mk ((starRingEnd ℂ).comp σ) = InfinitePlace.mk σ := InfinitePlace.mk_conjugate_eq σ
    simp only [N₁, this]
  choose Y hY hYn using fun τ : K' →+* ℂ => exists_frame b X (fun v => (hG v).1) τ
    (inv_pos.2 (hcB (InfinitePlace.mk τ).embedding).1)
  let N₂ : (F →+* ℂ) → (Fin n → F) → ℝ := fun σ y =>
    Formalism.HermitianLatticesTheory.cnorm ((Y (σ.comp (algebraMap K' F)))⁻¹ *ᵥ fun i => σ (y i))
  have hG₂ : IsGram (Pi.basisFun F (Fin n)) (fun u => Y (u.embedding.comp (algebraMap K' F))) N₂ :=
    fun u => ⟨hY _, fun y => by
      unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
      simp only [N₂, Pi.basisFun_repr]⟩
  have hN₂ : HasGram N₂ := ⟨⟨n, ⟨(_, _), hG₂⟩⟩⟩
  let φ := coordExt F b
  have hφ : ∀ (σ : F →+* ℂ) x, N₂ σ (φ x) = (c (InfinitePlace.mk (σ.comp (algebraMap K' F))).embedding)⁻¹ *
      N₁ (σ.comp (algebraMap K' F)) x := fun σ x => (hYn _ x).trans (by rw [(hG _).2])
  let ψ : V →ₛₗ[algebraMap K F] (Fin n → F) :=
    { toFun := fun x => φ (ι x)
      map_add' := fun x y => by simp
      map_smul' := fun a x => by
        rw [map_smulₛₗ, map_smulₛₗ, ← IsScalarTower.algebraMap_apply] }
  have h1 := GlobalTheory.SlopeExt.slope_sq_sub_le_slope_sq_span K' F V' (Fin n → F) N₁ N₂ φ M B ⟨⟨n, ⟨(b, X), hG₁⟩⟩⟩ hN₂ hc₁
    (coordExt_li F b) hMfg hM0 (fun σ x => by
      rw [hφ]
      refine mul_le_mul_of_nonneg_right ?_ ?_
      · obtain ⟨h1, h2⟩ := hcB (InfinitePlace.mk (σ.comp (algebraMap K' F))).embedding
        rw [← Real.exp_log h1, ← Real.exp_neg]
        exact Real.exp_le_exp.2 ((neg_le_abs _).trans h2)
      · show 0 ≤ N' _ x
        rw [← (hG _).2]; exact Real.sqrt_nonneg _)
  have h2 := GlobalTheory.T.maxSlope_extendedLattice_galois_le K F V (Fin n → F) N N₂ ψ L hN hN₂ hc
    (fun m e he => coordExt_li F b m _ (hli m e he)) hL h0 (fun σ x => by
      show N₂ σ (φ (ι x)) = _
      rw [hφ]
      show _ * N' _ (ι x) = _
      rw [hι, inv_mul_cancel_left₀ (hcB _).1.ne', IsScalarTower.algebraMap_eq K K' F, ← RingHom.comp_assoc]
      rcases InfinitePlace.embedding_mk_eq (σ.comp (algebraMap K' F)) with h | h
      · rw [h]
      · rw [h]; exact hc ((σ.comp (algebraMap K' F)).comp (algebraMap K K')) x)
  have h3 : slope_sq N₂ (Submodule.span (𝓞 F) (φ '' (M : Set V'))) ≤
      slopeMax_sq N₂ (Submodule.span (𝓞 F) (ψ '' (L : Set V))) := by
    refine slope_le_slopeMax hN₂ (fg_span_image ψ hL) (Submodule.span_le.2 ?_)
      (span_image_ne_bot φ (coordExt_li F b) hM0)
    rintro _ ⟨x, hx, rfl⟩
    refine map_mem_of_mem_span φ ?_ (hM hx)
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  have h4 : slope_sq N₁ M = slope_sq N' M := by rw [slope_sq_eq hG₁ hMfg, slope_sq_eq hG hMfg]
  linarith

end GlobalTheory.SlopeMaxExt
