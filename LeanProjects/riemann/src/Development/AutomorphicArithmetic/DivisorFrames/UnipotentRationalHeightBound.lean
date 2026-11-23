import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.CompactAdeleNormBounded
import Development.AutomorphicArithmetic.DivisorFrames.SkewUnitaryReductionTheory
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLeviClosureMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationUnramifiedIdentity
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

section
open GlobalTheory.LeviDecomp GlobalTheory.StabCosetDomain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  have hNN : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ) *
      Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
    rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
  have hN : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) :=
    ⟨⟨_, _, hNN, hNN⟩, rfl⟩
  have h1 := Matrix.rank_of_isUnit _ hN
  have h2 : (Aᵀ * M * A.map star).rank ≤ M.rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [hA, h1] at h2
  simp only [Fintype.card_sum, Fintype.card_fin, hrs] at h2
  have h3 : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := M.rank_le_width
    simp only [Matrix.rank, Fintype.card_fin] at h2 this
    rw [Module.finrank_fin_fun]; omega
  have hu : IsUnit M := (Matrix.mulVec_surjective_iff_isUnit).mp (LinearMap.range_eq_top.mp h3)
  exact ((Matrix.isUnit_iff_isUnit_det M).mp hu).ne_zero

private theorem det_ne_zero_skew {B : Base F E} {m : ℕ} {X : Spc F E m} {r s : ℕ} (hX : X.IsSkew σ B r s) :
    X.J.det ≠ 0 := by
  obtain w := Classical.arbitrary (InfinitePlace F)
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  rw [Matrix.det_smul, show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det (B.emb w).1 X.J).symm,
    h0, map_zero, mul_zero]

private theorem bdd {X ι : Type} [TopologicalSpace X] [Finite ι] {K : Set X} (hK : IsCompact K) (f : ι → X → AE F E)
    (hf : ∀ i, Continuous (f i)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ p ∈ K, ∀ i, ∀ ξ : E, ξ ≠ 0 → ∀ u : (AE F E)ˣ, inclR (F := F) (AF F) ξ * u.1 = f i p →
      (absE F E u : ℝ) ≤ c := by
  obtain ⟨c, hc⟩ := UpperTheory.compact_adele_norm_bounded F E (⋃ i, f i '' K) (isCompact_iUnion fun i => hK.image (hf i))
  refine ⟨max c 0, le_max_right _ _, fun p hp i ξ hξ u hu => le_trans ?_ (le_max_left _ _)⟩
  have h := hc (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 ξ hξ) * u)
    (Set.mem_iUnion.2 ⟨i, p, hp, hu.symm⟩)
  rwa [map_mul, GlobalTheory.Doubling.absE_inclR, one_mul] at h

private theorem incV_mulVec {n k : ℕ} (g : Matrix (Fin n) (Fin k) E) (x : Fin k → E) :
    incV F (g *ᵥ x) = incM F g *ᵥ incV F x :=
  funext fun i => RingHom.map_mulVec (inclR (F := F) (AF F)) g x i

private theorem rat_act {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {γ : UA σ J} (hγ : γ ∈ ratU σ J) :
    ∃ g : Matrix (Fin n) (Fin n) E, (∀ x, incV F (g *ᵥ x) = mat γ *ᵥ incV F x) ∧ ∀ x y, g *ᵥ x = g *ᵥ y → x = y := by
  obtain ⟨g, hg, -⟩ := rat_desc γ hγ
  have h1 : ∀ x, incV F (g *ᵥ x) = mat γ *ᵥ incV F x := fun x => by rw [incV_mulVec, hg]; rfl
  exact ⟨g, h1, fun x y h => eq_of_mulVec γ (h1 x).symm (by rw [h, h1])⟩

private theorem exists_minor {n : ℕ} {v v' : Fin n → E} (hv : v ≠ 0) (h : ∀ c : E, v' ≠ c • v) :
    ∃ j l, v j * v' l - v l * v' j ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  have hj' : v j ≠ 0 := hj
  refine h (v' j / v j) (funext fun l => ?_)
  have := hc j l
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination this

private theorem smul_inv_act {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {m : UA σ J} {t : AE F E} {x : Fin n → AE F E}
    (h : mat m *ᵥ x = t • x) : t • (mat m⁻¹ *ᵥ x) = x := by
  rw [← Matrix.mulVec_smul, ← h, Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]

private theorem indep {B : Base F E} {d d₁ r₁ s₁ i₀ i₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    (hW₁ : W₁.IsSkew σ B r₁ s₁) (hH : H'.IsAdapted σ B W W₁ i₀ i₁) {z : Fin d₁ → E} (hz : z ≠ 0) (c : E) :
    H'.ι *ᵥ z ≠ c • H'.x := by
  intro h
  have h1 := (hH.orth z).2
  have h2 := hH.xy
  unfold form at h1 h2
  rw [h, smul_dotProduct, h2, smul_eq_mul, mul_one] at h1
  rw [h1, zero_smul] at h
  apply hz
  refine Matrix.eq_zero_of_vecMul_eq_zero (det_ne_zero_skew hW₁) ?_
  rw [← hH.gram, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, h, Matrix.zero_vecMul,
    Matrix.zero_vecMul]

end

open GlobalTheory.LeviDecomp in
theorem UpperTheory.unipotent_rational_height_bound :
    GlobalTheory.Published.SiegelSetUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁)
                 (r s r₁ s₁ i₀ i₁ : ℕ), B.IsGood σ → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
                 ∃ M : ℕ, ∀ C : Set (UA σ W.J), IsCompact C → ∃ c : ℝ, ∀ γ ∈ ratU σ W.J, ∀ u ∈ unip σ W H',
                   ∀ (t : (AE F E)ˣ) (h₁ : UA σ W₁.J) (m : UA σ W.J), IsLevi (W₁ := W₁) H' t h₁ m → ∀ κ ∈ C, γ = u * m * κ →
                     ∃ δ ∈ ratU σ W₁.J, (ht (δ * h₁) : ℝ) * (absE F E t : ℝ) ^ M ≤ c := by
  intro hP F E _ _ _ _ _ σ B d d₁ W W₁ H' r s r₁ s₁ i₀ i₁ hB hW hW₁ hH
  obtain ⟨q, x, Cc, C₀, A, hx, hCc, hS⟩ := UpperTheory.skew_unitary_reduction_theory hP F E σ B d₁ W₁ r₁ s₁ hB hW₁
  refine ⟨q * A, fun C hC => ?_⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hm : Continuous fun g : UA σ W.J => mat g⁻¹ :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_inv
  have hm' : Continuous fun g : UA σ W₁.J => mat g⁻¹ :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_inv
  let a : UA σ W.J → Fin d → AE F E := fun k => mat k⁻¹ *ᵥ incV F H'.x
  let b : Fin q → UA σ W.J × UA σ W₁.J → Fin d → AE F E := fun i p =>
    mat p.1⁻¹ *ᵥ (incM F H'.ι *ᵥ (mat p.2⁻¹ *ᵥ incV F (x i)))
  have ha : Continuous a := hm.matrix_mulVec continuous_const
  have hb : ∀ i, Continuous (b i) := fun i => (hm.comp continuous_fst).matrix_mulVec
    (continuous_const.matrix_mulVec ((hm'.comp continuous_snd).matrix_mulVec continuous_const))
  obtain ⟨c₂, hc₂0, hc₂⟩ := bdd hC (fun j k => a k j) fun j => (continuous_apply j).comp ha
  obtain ⟨c₁, hc₁0, hc₁⟩ := bdd (hC.prod hCc)
    (fun (i : Fin q × Fin d × Fin d) p => a p.1 i.2.1 * b i.1 p i.2.2 - a p.1 i.2.2 * b i.1 p i.2.1) fun i =>
      (((continuous_apply _).comp (ha.comp continuous_fst)).mul ((continuous_apply _).comp (hb _))).sub
        (((continuous_apply _).comp (ha.comp continuous_fst)).mul ((continuous_apply _).comp (hb _)))
  refine ⟨max C₀ 0 * ((c₂ + c₁) ^ q) ^ A, fun γ hγ u hu t h₁ m hL κ hκ hγe => ?_⟩
  obtain ⟨δ, hδ, τ, a₁, κ₁, hτ, hκ₁, hδe, hht⟩ := hS h₁
  refine ⟨δ, hδ, ?_⟩
  obtain ⟨g, hg, hginj⟩ := rat_act (inv_mem hγ)
  obtain ⟨g₁, hg₁, hg₁inj⟩ := rat_act (inv_mem hδ)
  obtain ⟨hu1, hu2⟩ := prop_of_mem_unip H' (inv_mem hu)
  have hγi : ∀ y, mat γ⁻¹ *ᵥ y = mat κ⁻¹ *ᵥ (mat m⁻¹ *ᵥ (mat u⁻¹ *ᵥ y)) := fun y => by
    rw [hγe, mul_inv_rev, mul_inv_rev, mat_mul', mat_mul', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hV : t.1 • incV F (g *ᵥ H'.x) = a κ := by
    rw [hg, hγi, hu1, ← Matrix.mulVec_smul, smul_inv_act hL.1]
  have hx0 : H'.x ≠ 0 := fun h0 => by
    have := hH.xy
    rw [h0] at this
    simp [form] at this
  have hv : g *ᵥ H'.x ≠ 0 := fun h0 => hx0 (hginj _ _ (by rw [h0, Matrix.mulVec_zero]))
  have ht2 : (absE F E t : ℝ) ≤ c₂ := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    exact hc₂ κ hκ j _ hj t (by rw [mul_comm]; exact congrFun hV j)
  have hι := inv_intertwine (mat_inv_mul' m) (mat_mul_inv' h₁) hL.2.2
  have ht1 : ∀ i, (absE F E t : ℝ) * (absE F E (τ i) : ℝ) ≤ c₁ := fun i => by
    have hz : g₁ *ᵥ x i ≠ 0 := fun h0 => hx i (hg₁inj _ _ (by rw [h0, Matrix.mulVec_zero]))
    obtain ⟨j, l, hjl⟩ := exists_minor (v' := g *ᵥ (H'.ι *ᵥ (g₁ *ᵥ x i))) hv fun c h =>
      indep hW₁ hH hz c (hginj _ _ (by rw [h, Matrix.mulVec_smul]))
    obtain ⟨c, hc⟩ := hu2 (mat δ⁻¹ *ᵥ incV F (x i))
    have e1 : (τ i).1 • (mat h₁⁻¹ *ᵥ (mat δ⁻¹ *ᵥ incV F (x i))) = mat κ₁⁻¹ *ᵥ incV F (x i) := by
      rw [Matrix.mulVec_mulVec, ← mat_mul', ← mul_inv_rev, hδe, mul_inv_rev, mat_mul', ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_smul, smul_inv_act (hτ i)]
    have e2 : mat κ⁻¹ *ᵥ (mat m⁻¹ *ᵥ incV F H'.x) = incV F (g *ᵥ H'.x) := by rw [hg, hγi, hu1]
    have hV' : (τ i).1 • incV F (g *ᵥ (H'.ι *ᵥ (g₁ *ᵥ x i))) =
        b i (κ, κ₁) + ((τ i).1 * c) • incV F (g *ᵥ H'.x) := by
      rw [hg (H'.ι *ᵥ _), hγi, incV_mulVec H'.ι, hg₁, hc, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, e2, smul_add, smul_smul, Matrix.mulVec_mulVec _ (mat m⁻¹), hι, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, e1]
    have h := hc₁ (κ, κ₁) ⟨hκ, hκ₁⟩ (i, j, l) _ hjl (t * τ i) (by
      have p1 := congrFun hV j
      have p2 := congrFun hV l
      have p3 := congrFun hV' j
      have p4 := congrFun hV' l
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, incV] at p1 p2 p3 p4
      simp only [map_sub, map_mul, Units.val_mul]
      rw [← p1, ← p2]
      linear_combination (t.1 * inclR (F := F) (AF F) ((g *ᵥ H'.x) j)) * p4 - (t.1 * inclR (F := F) (AF F) ((g *ᵥ H'.x) l)) * p3)
    rwa [map_mul, NNReal.coe_mul] at h
  have hT : (0 : ℝ) ≤ absE F E t := NNReal.coe_nonneg _
  have hp : (∏ i, (1 + (absE F E (τ i) : ℝ))) * (absE F E t : ℝ) ^ q ≤ (c₂ + c₁) ^ q := by
    calc _ = ∏ i, ((1 + (absE F E (τ i) : ℝ)) * (absE F E t : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ _i : Fin q, (c₂ + c₁) :=
          Finset.prod_le_prod (fun i _ => by positivity) fun i _ => by nlinarith [ht1 i]
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hP0 : (0 : ℝ) ≤ ∏ i, (1 + (absE F E (τ i) : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  calc _ ≤ (max C₀ 0 * (∏ i, (1 + (absE F E (τ i) : ℝ))) ^ A) * (absE F E t : ℝ) ^ (q * A) :=
        mul_le_mul_of_nonneg_right (hht.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hP0 _)))
          (pow_nonneg hT _)
    _ = max C₀ 0 * ((∏ i, (1 + (absE F E (τ i) : ℝ))) * (absE F E t : ℝ) ^ q) ^ A := by
        rw [mul_pow, pow_mul, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hP0 (pow_nonneg hT _)) hp _) (le_max_right _ _)
