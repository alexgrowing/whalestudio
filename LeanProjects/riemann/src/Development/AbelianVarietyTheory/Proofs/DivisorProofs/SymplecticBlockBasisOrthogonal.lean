import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThKTorus.FrameCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem incM_vecMulVec {n d : ℕ} (u : Fin n → E) (w : Fin d → E) :
    incM F (Matrix.vecMulVec u w) = Matrix.vecMulVec (incV F u) (incV F w) := by
  ext r l
  simp [incM, incV, Matrix.vecMulVec_apply, map_mul]

theorem mul_vecMulVec_eq {n d : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin n) (Fin n) R) (u : Fin n → R)
    (w : Fin d → R) : A * Matrix.vecMulVec u w = Matrix.vecMulVec (A *ᵥ u) w := by
  ext r l
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

omit [NumberField E] in

theorem mul_incM_of_cols {n d : ℕ} (A : Matrix (Fin n) (Fin n) (AE F E)) (m : Matrix (Fin n) (Fin d) E)
    (h : ∀ l, A *ᵥ incV F (fun r => m r l) = incV F (fun r => m r l)) : A * incM F m = incM F m := by
  ext r l
  have := congrFun (h l) r
  rw [Matrix.mulVec, dotProduct] at this
  rw [Matrix.mul_apply]
  exact this

omit [NumberField E] in

theorem mulVec_eq_tAd {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE F E)) (v : Fin n → AE F E) (s : ℝ)
    (h : (A - 1) *ᵥ v = realAd F (s - 1) • v) : A *ᵥ v = tAd F s • v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add] at h
  rw [h, tAd, add_smul, one_smul, add_comm]

end GlobalTheory.ThKTorus.FrameCoords

open GlobalTheory.ThKTorus.FrameCoords

theorem GlobalTheory.ThKTorus.exists_frameCo_of_basis : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d q : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) (x y : Fin q → Fin n → E)
    (b : Module.Basis ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F (Matrix (Fin n) (Fin d) E))
    (blk : Fin q → Finset (Fin n × Fin d)),
    (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) →
    (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inl l)) = 0) →
    (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inr l)) = 0) →
    (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inr l)) = if k = l then 1 else 0) →
    (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inl l)) = if k = l then -1 else 0) →
    (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inl k) = Matrix.vecMulVec (y i) w) →
    (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inr k) = Matrix.vecMulVec (x i) w) →
    (∀ k, (∀ i, k ∉ blk i) → ∀ (l : Fin d) (i : Fin q),
        form σ J (fun r => b (.inl k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inl k) r l) (y i) = 0 ∧
        form σ J (fun r => b (.inr k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inr k) r l) (y i) = 0) →
    ∃ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F K)) (Fin n × Fin d),
      (∀ m : Matrix (Fin n) (Fin d) E, ∃ u v : Fin n × Fin d → F,
        co.e (incM F m) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) ∧
      IsFrameCo σ J K x y co blk := by
  intro F E _ _ _ _ _ σ n d q J K x y b blk hdis h11 h22 h12 h21 hyl hxr hoff
  classical
  let b' : Module.Basis ((Fin n × Fin d) ⊕ (Fin n × Fin d)) (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    (b.baseChange (AF F)).map (GlobalTheory.RatDarboux.matBC (AF F))
  have hb'v : ∀ j, b' j = incM F (b j) := fun j => by
    simp only [b', Module.Basis.map_apply, Module.Basis.baseChange_apply, GlobalTheory.RatDarboux.matBC_one]
    rfl
  have hb' : ∀ i j, GlobalTheory.RatDarboux.sympBil (cA σ) (-1) (incM F J) (incM F K) (b' i) (b' j) =
      algebraMap F (AF F) (symp σ (-1) J K (b i) (b j)) := fun i j => by
    rw [hb'v, hb'v]
    exact GlobalTheory.RatDarboux.symp_map (AF F) σ J K _ _
  obtain ⟨co, hco⟩ := GlobalTheory.RatDarboux.exists_darboux_of_basis
    (GlobalTheory.RatDarboux.sympBil (cA σ) (-1) (incM F J) (incM F K)) b'
    (fun i j => by rw [hb', h11, map_zero])
    (fun i j => by rw [hb', h22, map_zero])
    (fun i => by rw [hb', h12, if_pos rfl, map_one])
    (fun i j h => by rw [hb', h12, if_neg h, map_zero])
    (fun i => by rw [hb', h21, if_pos rfl, map_neg, map_one])
    (fun i j h => by rw [hb', h21, if_neg h, map_zero])
  refine ⟨co, fun m => ⟨fun k => b.repr m (.inl k), fun k => b.repr m (.inr k), ?_⟩, hdis, ?_⟩
  · have hx : ∀ i, b'.repr (incM F m) i = algebraMap F (AF F) (b.repr m i) := fun i => by
      rw [show incM F m = GlobalTheory.RatDarboux.matBC (AF F) ((1 : AF F) ⊗ₜ[F] m) from (GlobalTheory.RatDarboux.matBC_one _ m).symm]
      simp [b', Algebra.smul_def]
    rw [hco]
    simp only [hx]
  · intro t a _ hT z
    let c : (Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F :=
      Sum.elim (fun k => ∏ i, if k ∈ blk i then tAd F (t i)⁻¹ else 1)
        (fun k => ∏ i, if k ∈ blk i then tAd F (t i) else 1)
    have hprod : ∀ (s : Fin q → ℝ) (i : Fin q) (k : Fin n × Fin d), k ∈ blk i →
        (∏ i', if k ∈ blk i' then tAd F (s i') else 1) = tAd F (s i) := fun s i k hi => by
      rw [Finset.prod_eq_single i (fun i' _ hne => if_neg fun h' =>
        Finset.disjoint_left.1 (hdis i i' hne.symm) hi h') (fun h => absurd (Finset.mem_univ i) h), if_pos hi]
    have hone : ∀ (s : Fin q → ℝ) (k : Fin n × Fin d), (∀ i, k ∉ blk i) →
        (∏ i', if k ∈ blk i' then tAd F (s i') else 1) = 1 := fun s k hk =>
      Finset.prod_eq_one fun i _ => if_neg (hk i)
    have hfix : ∀ k, (∀ i, k ∉ blk i) → ∀ j, (j = Sum.inl k ∨ j = Sum.inr k) → mat a * b' j = b' j := by
      intro k hk j hj
      rw [hb'v]
      refine mul_incM_of_cols _ _ fun l => ?_
      have h0 := hT.2.2 (fun r => b j r l)
        (fun i => by rcases hj with rfl | rfl; exacts [(hoff k hk l i).1, (hoff k hk l i).2.2.1])
        (fun i => by rcases hj with rfl | rfl; exacts [(hoff k hk l i).2.1, (hoff k hk l i).2.2.2])
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
      exact h0
    have hc : ∀ j, mat a * b' j = c j • b' j := by
      rintro (k | k)
      · by_cases hk : ∃ i, k ∈ blk i
        · obtain ⟨i, hi⟩ := hk
          obtain ⟨w, hw⟩ := hyl i k hi
          have hcv : c (.inl k) = tAd F (t i)⁻¹ := hprod (fun i => (t i)⁻¹) i k hi
          rw [hcv, hb'v, hw, incM_vecMulVec, mul_vecMulVec_eq, mulVec_eq_tAd _ _ _ (hT.2.1 i)]
          ext r l
          simp [Matrix.vecMulVec_apply, smul_mul_assoc]
        · push_neg at hk
          have hcv : c (.inl k) = 1 := hone (fun i => (t i)⁻¹) k hk
          rw [hcv, one_smul]
          exact hfix k hk _ (.inl rfl)
      · by_cases hk : ∃ i, k ∈ blk i
        · obtain ⟨i, hi⟩ := hk
          obtain ⟨w, hw⟩ := hxr i k hi
          have hcv : c (.inr k) = tAd F (t i) := hprod t i k hi
          rw [hcv, hb'v, hw, incM_vecMulVec, mul_vecMulVec_eq, mulVec_eq_tAd _ _ _ (hT.1 i)]
          ext r l
          simp [Matrix.vecMulVec_apply, smul_mul_assoc]
        · push_neg at hk
          have hcv : c (.inr k) = 1 := hone t k hk
          rw [hcv, one_smul]
          exact hfix k hk _ (.inr rfl)
    have hrep : ∀ w j, b'.repr (mat a * w) j = c j * b'.repr w j := by
      intro w j
      conv_lhs => rw [← b'.sum_repr w]
      rw [Matrix.mul_sum]
      simp_rw [Matrix.mul_smul, hc, smul_smul]
      rw [b'.repr_sum_self]
      exact mul_comm _ _
    have hw : ∀ v : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F), ∀ k,
        b'.repr (co.e.symm v) (.inl k) = v.1 k ∧ b'.repr (co.e.symm v) (.inr k) = v.2 k := by
      intro v k
      have := hco (co.e.symm v)
      rw [LinearEquiv.apply_symm_apply] at this
      exact ⟨(congrFun (congrArg Prod.fst this) k).symm, (congrFun (congrArg Prod.snd this) k).symm⟩
    constructor
    · rw [hco]
      ext k
      · simp only [hrep, (hw _ k).1, c, Sum.elim_inl, blkScale]
      · simp only [hrep, (hw _ k).2, mul_zero, Pi.zero_apply]
    · rw [hco]
      ext k
      · simp only [hrep, (hw _ k).1, mul_zero, Pi.zero_apply]
      · simp only [hrep, (hw _ k).2, c, Sum.elim_inr, blkScale]
