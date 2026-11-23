import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HaarOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg

noncomputable section

open MeasureTheory NumberField Topology Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical ENNReal
open Matrix

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH

section Om

variable (I : AutInst)

def Ksub : Subgroup I.Gf := (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

theorem Ksub_coe : ((Ksub I : Subgroup I.Gf) : Set I.Gf) = I.Kset := rfl

theorem hs_continuous {n : ℕ} : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => Formalism.REAL.hs M) := by
  unfold Formalism.REAL.hs
  refine continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ => ?_))
  exact ((continuous_id.matrix_elem i j).norm).pow 2

theorem omCover_holds : OmCover I := by
  intro Ω hΩ
  have hKo : IsOpen ((Ksub I : Subgroup I.Gf) : Set I.Gf) := (Ksub_coe I) ▸ kset_open I
  have hf : IsCompact (Prod.snd '' Ω) := hΩ.image continuous_snd
  obtain ⟨A, -, hA⟩ := hf.elim_nhds_subcover (fun a => (fun w => w * a⁻¹) ⁻¹' ((Ksub I : Subgroup I.Gf) : Set I.Gf))
    (fun a _ => (hKo.preimage (continuous_mul_const a⁻¹)).mem_nhds (by
      show a * a⁻¹ ∈ ((Ksub I : Subgroup I.Gf) : Set I.Gf)
      rw [mul_inv_cancel]; exact (Ksub I).one_mem))
  choose L hLc hL using fun v => (Formalism.REAL.polar_decomposition_holds I.n (I.ε v)).2.2
  have hcm : ∀ v, Continuous fun w : I.GA => uMat (w.1 v) := fun v =>
    Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply v).comp continuous_fst))
  have hfc : ∀ v, Continuous fun w : I.GA => Real.sqrt (Formalism.REAL.hs (L v (uMat (w.1 v)))) := by
    intro v
    have h1 : Continuous fun w : I.GA => L v (uMat (w.1 v)) :=
      (hLc v).comp_continuous (hcm v) (fun w => (w.1 v).2)
    exact (hs_continuous.comp h1).sqrt
  have hbd : ∀ v, ∃ C, ∀ w ∈ Ω, ‖Real.sqrt (Formalism.REAL.hs (L v (uMat (w.1 v))))‖ ≤ C :=
    fun v => hΩ.exists_bound_of_continuousOn (hfc v).continuousOn
  choose C hC using hbd
  refine ⟨fun v => max (C v) 0, Ksub I, A, fun v => le_max_right _ _, le_of_eq (Ksub_coe I), ?_⟩
  intro w hw
  have hw' := hA ⟨w, hw, rfl⟩
  rcases Set.mem_iUnion₂.1 hw' with ⟨a, ha, hwa⟩
  refine Set.mem_iUnion₂.2 ⟨a, ha, ?_⟩
  have e1 : (w * ((1, a) : I.GA)⁻¹).1 = w.1 := by simp
  have e2 : (w * ((1, a) : I.GA)⁻¹).2 = w.2 * a⁻¹ := by simp
  show (∀ v, Formalism.MainNotions.BridgeLemma.cartanDistance (I.ε v) ((w * ((1, a) : I.GA)⁻¹).1 v) ≤ max (C v) 0) ∧
    (w * ((1, a) : I.GA)⁻¹).2 ∈ ((Ksub I : Subgroup I.Gf) : Set I.Gf)
  rw [e1, e2]
  refine ⟨fun v => ?_, hwa⟩
  have hle : Formalism.MainNotions.BridgeLemma.cartanDistance (I.ε v) (w.1 v) ≤ Real.sqrt (Formalism.REAL.hs (L v (uMat (w.1 v)))) := by
    unfold Formalism.MainNotions.BridgeLemma.cartanDistance
    refine csInf_le ⟨0, ?_⟩ ⟨uMat (w.1 v) * NormedSpace.exp (-(L v (uMat (w.1 v)))), L v (uMat (w.1 v)),
      (hL v _ (w.1 v).2).2, (hL v _ (w.1 v).2).1, ?_, rfl⟩
    · rintro t ⟨k, X, -, -, -, rfl⟩
      exact Real.sqrt_nonneg _
    · rw [mul_assoc, Formalism.REAL.matrix_exp_neg_mul_exp, mul_one]
  refine hle.trans ((le_trans (le_abs_self _) ?_).trans (le_max_left _ _))
  rw [← Real.norm_eq_abs]
  exact hC v w hw

end Om

section NO

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem noCount_holds : (NOinf X u).Countable := by
  have h1 : ((Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I : Subgroup X.B.I.GA) : Set X.B.I.GA).Countable :=
    Set.countable_coe_iff.1 (Formalism.MainNotions.LeviCoordinates.rr_GF_countable X.B.I)
  rw [Formalism.MainNotions.LeviCoordinates.rr_GF_coe] at h1
  refine (h1.image Prod.fst).mono ?_
  rintro s ⟨γ, hγ, h1, -⟩
  exact ⟨γ, hγ, h1⟩

end NO

section PureH

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_sum_right' {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (c : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, c i * hJ ε x (y i) := by
  unfold hJ
  simp [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul]

theorem hJ_sub_right' (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  unfold hJ
  simp [Matrix.mulVec_sub]

theorem hJ_zero_right' (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  unfold hJ
  simp

theorem hJ_conj' (x y : Fin n → ℂ) : hJ ε x y = starRingEnd ℂ (hJ ε y x) := by
  unfold hJ Formalism.REAL.Jm
  simp only [Matrix.mulVec_diagonal, dotProduct, map_sum, map_mul, Pi.star_apply, RCLike.star_def,
    Complex.conj_conj]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp <;> ring

theorem hJ_inUJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (x y : Fin n → ℂ) :
    hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by
  unfold hJ
  unfold Formalism.REAL.inUJ at hg
  rw [Matrix.star_mulVec, ← dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

private theorem frame_expand_lemma {p k : ℕ} (e f : Fin p → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z ≠ 0)
    (hww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (w a) = 0) (hfw : ∀ c a, hJ ε (f c) (w a) = 0) (hzw : ∀ a, hJ ε z (w a) = 0)
    (hcard : 2 * p + 1 + k = n) (y : Fin n → ℂ) :
    y = ∑ a, hJ ε (f a) y • e a + ∑ a, hJ ε (e a) y • f a + (hJ ε z y / hJ ε z z) • z +
      ∑ b, hJ ε (w b) y • w b := by
  classical
  have hadd : ∀ x y y' : Fin n → ℂ, hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
    intro x y y'; unfold hJ; simp [Matrix.mulVec_add]
  have hsmul : ∀ (x : Fin n → ℂ) (c : ℂ) (y : Fin n → ℂ), hJ ε x (c • y) = c * hJ ε x y := by
    intro x c y; unfold hJ; simp [Matrix.mulVec_smul]
  have hsum : ∀ (m : ℕ) (x : Fin n → ℂ) (c : Fin m → ℂ) (y : Fin m → Fin n → ℂ),
      hJ ε x (∑ i, c i • y i) = ∑ i, c i * hJ ε x (y i) :=
    fun m x c y => hJ_sum_right' ε Finset.univ x c y
  have hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0 := by
    intro a b; rw [hJ_conj', hef]; split_ifs <;> simp
  have hze : ∀ a, hJ ε z (e a) = 0 := by intro a; rw [hJ_conj', hez]; simp
  have hzf : ∀ a, hJ ε z (f a) = 0 := by intro a; rw [hJ_conj', hfz]; simp
  have hwe : ∀ c a, hJ ε (w c) (e a) = 0 := by intro c a; rw [hJ_conj', hew]; simp
  have hwf : ∀ c a, hJ ε (w c) (f a) = 0 := by intro c a; rw [hJ_conj', hfw]; simp
  have hwz : ∀ c, hJ ε (w c) z = 0 := by intro c; rw [hJ_conj', hzw]; simp
  have ex1 : ∀ c (x1 x2 : Fin p → ℂ) (x3 : ℂ) (x4 : Fin k → ℂ),
      hJ ε (f c) (∑ a, x1 a • e a + ∑ a, x2 a • f a + x3 • z + ∑ b, x4 b • w b) = x1 c := by
    intro c x1 x2 x3 x4
    simp only [hadd, hsmul, hsum, hfe, hff, hfz, hfw, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, zero_add]
  have ex2 : ∀ c (x1 x2 : Fin p → ℂ) (x3 : ℂ) (x4 : Fin k → ℂ),
      hJ ε (e c) (∑ a, x1 a • e a + ∑ a, x2 a • f a + x3 • z + ∑ b, x4 b • w b) = x2 c := by
    intro c x1 x2 x3 x4
    simp only [hadd, hsmul, hsum, hee, hef, hez, hew, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, zero_add]
  have ex3 : ∀ (x1 x2 : Fin p → ℂ) (x3 : ℂ) (x4 : Fin k → ℂ),
      hJ ε z (∑ a, x1 a • e a + ∑ a, x2 a • f a + x3 • z + ∑ b, x4 b • w b) = x3 * hJ ε z z := by
    intro x1 x2 x3 x4
    simp only [hadd, hsmul, hsum, hze, hzf, hzw, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  have ex4 : ∀ c (x1 x2 : Fin p → ℂ) (x3 : ℂ) (x4 : Fin k → ℂ),
      hJ ε (w c) (∑ a, x1 a • e a + ∑ a, x2 a • f a + x3 • z + ∑ b, x4 b • w b) = x4 c := by
    intro c x1 x2 x3 x4
    simp only [hadd, hsmul, hsum, hwe, hwf, hwz, hww, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, zero_add]
  let Ψ : ((Fin p → ℂ) × (Fin p → ℂ) × ℂ × (Fin k → ℂ)) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x => ∑ a, x.1 a • e a + ∑ a, x.2.1 a • f a + x.2.2.1 • z + ∑ b, x.2.2.2 b • w b
      map_add' := by
        intro x x'
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
        abel
      map_smul' := by
        intro r x
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
          Finset.smul_sum, mul_smul] }
  have hinj : Function.Injective Ψ := by
    intro x x' h
    have h' : (∑ a, x.1 a • e a + ∑ a, x.2.1 a • f a + x.2.2.1 • z + ∑ b, x.2.2.2 b • w b) =
        ∑ a, x'.1 a • e a + ∑ a, x'.2.1 a • f a + x'.2.2.1 • z + ∑ b, x'.2.2.2 b • w b := h
    have h1 : x.1 = x'.1 := funext fun c => by
      have := congrArg (hJ ε (f c)) h'; rwa [ex1, ex1] at this
    have h2 : x.2.1 = x'.2.1 := funext fun c => by
      have := congrArg (hJ ε (e c)) h'; rwa [ex2, ex2] at this
    have h3 : x.2.2.1 = x'.2.2.1 := by
      have := congrArg (hJ ε z) h'; rw [ex3, ex3] at this; exact mul_right_cancel₀ hzz this
    have h4 : x.2.2.2 = x'.2.2.2 := funext fun c => by
      have := congrArg (hJ ε (w c)) h'; rwa [ex4, ex4] at this
    exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
  have hdim : Module.finrank ℂ ((Fin p → ℂ) × (Fin p → ℂ) × ℂ × (Fin k → ℂ)) =
      Module.finrank ℂ (Fin n → ℂ) := by
    simp only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
    omega
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj y
  have hx' : (∑ a, x.1 a • e a + ∑ a, x.2.1 a • f a + x.2.2.1 • z + ∑ b, x.2.2.2 b • w b) = y := hx
  subst hx'
  simp only [ex1, ex2, ex3, ex4, mul_div_cancel_right₀ _ hzz]

theorem frame_bounded {p k : ℕ} (e f : Fin p → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z ≠ 0)
    (hww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (w a) = 0) (hfw : ∀ c a, hJ ε (f c) (w a) = 0) (hzw : ∀ a, hJ ε z (w a) = 0)
    (hcard : 2 * p + 1 + k = n) :
    ∃ C : ℝ, ∀ g : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inUJ ε g → (∀ a, g *ᵥ e a = e a) →
      (∀ a, g *ᵥ f a = f a) → g *ᵥ z = z → ∀ i j, ‖g i j‖ ≤ C := by
  classical
  have hw : ∀ g : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inUJ ε g → (∀ a, g *ᵥ e a = e a) →
      (∀ a, g *ᵥ f a = f a) → g *ᵥ z = z → ∀ b i, ‖(g *ᵥ w b) i‖ ≤ ∑ c, ‖w c i‖ := by
    intro g hg he hf hz b i
    have h1 : ∀ a, hJ ε (f a) (g *ᵥ w b) = 0 := fun a => by
      have := hJ_inUJ ε hg (f a) (w b); rw [hf a] at this; rw [this]; exact hfw a b
    have h2 : ∀ a, hJ ε (e a) (g *ᵥ w b) = 0 := fun a => by
      have := hJ_inUJ ε hg (e a) (w b); rw [he a] at this; rw [this]; exact hew a b
    have h3 : hJ ε z (g *ᵥ w b) = 0 := by
      have := hJ_inUJ ε hg z (w b); rw [hz] at this; rw [this]; exact hzw b
    have hexp := frame_expand_lemma ε e f z w hee hff hef hez hfz hzz hww hew hfw hzw hcard (g *ᵥ w b)
    simp only [h1, h2, h3, zero_smul, Finset.sum_const_zero, zero_div, zero_add] at hexp
    have hnorm : ∑ c, hJ ε (w c) (g *ᵥ w b) * starRingEnd ℂ (hJ ε (w c) (g *ᵥ w b)) = 1 := by
      have h := hJ_inUJ ε hg (w b) (w b)
      rw [hww b b, if_pos rfl] at h
      rw [← h]
      conv_rhs => arg 3; rw [hexp]
      rw [hJ_sum_right']
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hJ_conj' ε (g *ᵥ w b) (w c)]
    have hre : ∑ c, ‖hJ ε (w c) (g *ᵥ w b)‖ ^ 2 = 1 := by
      have := congrArg Complex.re hnorm
      simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_sum, Complex.ofReal_re,
        Complex.one_re] at this
      exact this
    have hd : ∀ c, ‖hJ ε (w c) (g *ᵥ w b)‖ ≤ 1 := by
      intro c
      have hc : ‖hJ ε (w c) (g *ᵥ w b)‖ ^ 2 ≤ 1 := by
        rw [← hre]
        exact Finset.single_le_sum (f := fun c => ‖hJ ε (w c) (g *ᵥ w b)‖ ^ 2)
          (fun c _ => sq_nonneg _) (Finset.mem_univ c)
      nlinarith [norm_nonneg (hJ ε (w c) (g *ᵥ w b))]
    rw [hexp, Finset.sum_apply]
    calc ‖∑ c, (hJ ε (w c) (g *ᵥ w b) • w c) i‖ ≤ ∑ c, ‖(hJ ε (w c) (g *ᵥ w b) • w c) i‖ :=
          norm_sum_le _ _
      _ ≤ ∑ c, ‖w c i‖ := Finset.sum_le_sum fun c _ => by
          rw [Pi.smul_apply, smul_eq_mul, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hd c)
  let T : Fin n → Fin n → ℝ := fun i j =>
    ∑ a, ‖hJ ε (f a) (Pi.single j 1)‖ * ‖e a i‖ + ∑ a, ‖hJ ε (e a) (Pi.single j 1)‖ * ‖f a i‖ +
      ‖hJ ε z (Pi.single j 1) / hJ ε z z‖ * ‖z i‖ + ∑ b, ‖hJ ε (w b) (Pi.single j 1)‖ * ∑ c, ‖w c i‖
  have hT : ∀ i j, 0 ≤ T i j := fun i j => by positivity
  refine ⟨∑ i, ∑ j, T i j, ?_⟩
  intro g hg he hf hz i j
  have hB : ‖g i j‖ ≤ T i j := by
    have hexp := frame_expand_lemma ε e f z w hee hff hef hez hfz hzz hww hew hfw hzw hcard
      (Pi.single j (1 : ℂ))
    have hgij : g i j = (g *ᵥ Pi.single j (1 : ℂ)) i := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    conv_lhs => rw [hgij, hexp]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, he, hf, hz, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
    · exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    · exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    · exact le_of_eq (norm_mul _ _)
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hw g hg he hf hz b i) (norm_nonneg _)
  calc ‖g i j‖ ≤ T i j := hB
    _ ≤ ∑ j', T i j' := Finset.single_le_sum (fun j' _ => hT i j') (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', T i' j' := Finset.single_le_sum (f := fun i' => ∑ j', T i' j')
        (fun i' _ => Finset.sum_nonneg fun j' _ => hT i' j') (Finset.mem_univ i)

theorem frame_compact {p k : ℕ} (e f : Fin p → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z ≠ 0)
    (hww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (w a) = 0) (hfw : ∀ c a, hJ ε (f c) (w a) = 0) (hzw : ∀ a, hJ ε z (w a) = 0)
    (hcard : 2 * p + 1 + k = n) {Q : Set (Matrix (Fin n) (Fin n) ℂ)} (hQ : IsClosed Q)
    (hsub : ∀ g ∈ Q, Formalism.REAL.inUJ ε g ∧ (∀ a, g *ᵥ e a = e a) ∧ (∀ a, g *ᵥ f a = f a) ∧ g *ᵥ z = z) :
    IsCompact Q := by
  obtain ⟨C, hC⟩ := frame_bounded ε e f z w hee hff hef hez hfz hzz hww hew hfw hzw hcard
  have hK : IsCompact ((Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : ℂ) C) :
      Set (Matrix (Fin n) (Fin n) ℂ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset hQ ?_
  intro g hg
  obtain ⟨h1, h2, h3, h4⟩ := hsub g hg
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  exact fun i j => hC g h1 h2 h3 h4 i j

end PureH

theorem hJ_rv_sc (I : AutInst) (v : InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
  have key : Formalism.REAL.Jm (I.ε v) *ᵥ rv I v y =
      (I.P v)ᴴ *ᵥ ((I.J.map (I.φ v)) *ᵥ fun i => I.φ v (y i)) := by
    rw [← I.P_spec v]
    unfold rv
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one]
  have hx : star (rv I v x) ᵥ* (I.P v)ᴴ = star fun i => I.φ v (x i) := by
    rw [← Matrix.star_mulVec]
    unfold rv
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  unfold hJ
  rw [key, dotProduct_mulVec, hx]
  unfold Formalism.UG.hform
  simp only [map_sum, map_mul, dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.map_apply,
    starRingEnd_apply, PI.UnitaryGroupMassFormula.LCG.ap_star, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

section HFin

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem hJ_crd (v : InfinitePlace X.B.I.F) (a b : (VS D).V) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd a)) (rv X.B.I v (X.crd b)) = X.B.I.φ v (X.ιE.symm ((VS D).hT a b)) := by
  rw [hJ_rv_sc, ← Cut.hform_crd X a b, RingEquiv.symm_apply_apply]

theorem card_frame : 2 * D.R.rS + 1 + D.R.k = X.B.I.n := by
  have h1 := X.n_eq
  have h2 := Formalism.MainNotions.S.dimS_eq D.R
  omega

theorem hv_compact (v : InfinitePlace X.B.I.F) :
    IsCompact {g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ | Formalism.REAL.inUJ (X.B.I.ε v) g ∧
      ∀ x ∈ fixSet X u, g *ᵥ rv X.B.I v x = rv X.B.I v x} := by
  have hUJc : IsClosed {g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ | Formalism.REAL.inUJ (X.B.I.ε v) g} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  have hQ : IsClosed {g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ | Formalism.REAL.inUJ (X.B.I.ε v) g ∧
      ∀ x ∈ fixSet X u, g *ᵥ rv X.B.I v x = rv X.B.I v x} := by
    have e : {g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ | Formalism.REAL.inUJ (X.B.I.ε v) g ∧
        ∀ x ∈ fixSet X u, g *ᵥ rv X.B.I v x = rv X.B.I v x} =
        {g | Formalism.REAL.inUJ (X.B.I.ε v) g} ∩ ⋂ x ∈ fixSet X u, {g | g *ᵥ rv X.B.I v x = rv X.B.I v x} := by
      ext g
      simp
    rw [e]
    exact hUJc.inter (isClosed_biInter fun x _ =>
      isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
  have hT : (((D.mem u).A.T : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  refine frame_compact (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
    (rv X.B.I v (X.zR u)) (X.wfr u v) ?_ ?_ ?_ ?_ ?_ ?_ (X.wfr_on u v) (fun c a => ((X.wfr_perp u v a).1 c).1)
    (fun c a => ((X.wfr_perp u v a).1 c).2) (fun a => (X.wfr_perp u v a).2) (card_frame X) hQ ?_
  · intro a b
    refine (hJ_crd X v (X.eX a) (X.eX b)).trans ?_
    rw [X.ee]
    simp
  · intro a b
    refine (hJ_crd X v (X.fY a) (X.fY b)).trans ?_
    rw [X.ff]
    simp
  · intro a b
    refine (hJ_crd X v (X.eX a) (X.fY b)).trans ?_
    rw [X.ef]
    split_ifs <;> simp
  · intro a
    refine (hJ_crd X v (X.eX a) (X.zu u)).trans ?_
    rw [(X.zu_orth u a).1]
    simp
  · intro a
    refine (hJ_crd X v (X.fY a) (X.zu u)).trans ?_
    rw [(X.zu_orth u a).2]
    simp
  · rw [show hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) =
        X.B.I.φ v (X.ιE.symm ((VS D).hT (X.zu u) (X.zu u))) from hJ_crd X v (X.zu u) (X.zu u), X.zu_norm]
    simpa using hT
  · intro g hg
    refine ⟨hg.1, fun a => hg.2 _ (Or.inl (Or.inl ⟨a, rfl⟩)), fun a => hg.2 _ (Or.inl (Or.inr ⟨a, rfl⟩)),
      hg.2 _ (Or.inr rfl)⟩

theorem hinf_compact : IsCompact ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) := by
  have e : ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) = Set.univ.pi fun v =>
      (fun g : Formalism.REAL.UJ (X.B.I.ε v) => uMat g) ⁻¹' {g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ |
        Formalism.REAL.inUJ (X.B.I.ε v) g ∧ ∀ x ∈ fixSet X u, g *ᵥ rv X.B.I v x = rv X.B.I v x} := by
    ext s
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_preimage, Set.mem_setOf_eq]
    show (∀ v, ∀ x ∈ fixSet X u, uMat (s v) *ᵥ rv X.B.I v x = rv X.B.I v x) ↔ _
    constructor
    · intro hs v
      exact ⟨(s v).2, hs v⟩
    · intro hs v
      exact (hs v).2
  rw [e]
  exact isCompact_univ_pi fun v =>
    ((Formalism.REAL.uJEmb X.B.I.n (X.B.I.ε v)).1).isCompact_preimage (hv_compact X u v)

theorem hFinite_holds : X.muH u Set.univ < ⊤ := by
  have hc := hinf_compact X u
  obtain ⟨-, hfin, -⟩ := haarOnSet_isHaar_inst X.B.I (Hinf X u) hc.isClosed (X.muH u) (X.muH_haar u)
  have h0 : X.muH u ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf)ᶜ = 0 := (X.muH_haar u).2.2.1
  calc X.muH u Set.univ = X.muH u (((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) ∪
        ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf)ᶜ) := by rw [Set.union_compl_self]
    _ ≤ X.muH u ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) +
        X.muH u ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf)ᶜ := measure_union_le _ _
    _ < ⊤ := by rw [h0, add_zero]; exact hfin _ hc

end HFin

section Col

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem piU_norm (g : Hinf X u) (ξ : X.Vpi u) : ‖piRep X u g ξ‖ = ‖ξ‖ := by
  have hg := hinf_le_sinf X u _ g.2
  exact ((X.piU u (g : X.B.I.Ginf)).toLinearMap.isometryOfInner
    (fun x y => (X.piU_rep u).2.2.1 _ hg x y)).norm_map ξ

theorem colBound_of (hK : X.LevelSubgroupCharacter) (hCF : Cut.ClassFin X u hK) : ColBound X u hK := by
  classical
  intro T
  unfold Cut.ClassFin at hCF
  have hsurj : ∀ c : Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK),
      ∃ g : Hfin X u, DoubleCoset.mk (iotaF X u).range (Ku X u hK) g = c := by
    intro c
    induction c using Quotient.inductionOn' with
    | h g => exact ⟨g, rfl⟩
  choose sr hsr using hsurj
  haveI := Fintype.ofFinite (Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK))
  let Lc : Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK) → (X.Vpi u →ₗ[ℂ] ℂ) := fun c =>
    (LinearMap.proj (R := ℂ) (φ := fun _ : Hinf X u × Hfin X u => ℂ) ((1 : Hinf X u), sr c)).comp
      (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ))
  refine ⟨∑ c, ‖LinearMap.toContinuousLinearMap (Lc c)‖, fun h ξ => ?_⟩
  obtain ⟨⟨γ', κ⟩, hrep⟩ := Formalism.UG.P.exists_rep (iotaF X u).range (Ku X u hK) sr hsr h
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.1 γ'.2
  set c := DoubleCoset.mk (iotaF X u).range (Ku X u hK) h with hc
  obtain ⟨hF, hE⟩ := T.2
  have e1 : ((1 : Hinf X u), h) = (iotaI X u γ, iotaF X u γ) * (((iotaI X u γ)⁻¹, sr c) * (1, (κ : Hfin X u))) := by
    refine Prod.ext (by simp) ?_
    simp only [Prod.snd_mul]
    rw [hγ, hrep, mul_assoc]
  have e2 : (((iotaI X u γ)⁻¹, sr c) : Hinf X u × Hfin X u) = ((1 : Hinf X u), sr c) * ((iotaI X u γ)⁻¹, 1) := by
    refine Prod.ext (by simp) (by simp)
  have hval : (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ ((1 : Hinf X u), h) =
      (psiK X u hK κ : ℂ) * Lc c (piRep X u (iotaI X u γ)⁻¹ ξ) := by
    rw [e1, (hF ξ).1 γ, (hF ξ).2, e2, ← hE]
    rfl
  have hpsi : ‖(psiK X u hK κ : ℂ)‖ = 1 := hK.2.2.2.2 _ κ.2
  rw [hval, norm_mul, hpsi, one_mul]
  have h1 : ‖Lc c (piRep X u (iotaI X u γ)⁻¹ ξ)‖ ≤ ‖LinearMap.toContinuousLinearMap (Lc c)‖ * ‖ξ‖ := by
    have := (LinearMap.toContinuousLinearMap (Lc c)).le_opNorm (piRep X u (iotaI X u γ)⁻¹ ξ)
    rw [piU_norm] at this
    exact this
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact Finset.single_le_sum (f := fun c => ‖LinearMap.toContinuousLinearMap (Lc c)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ c)

end Col

def SCompactC : Prop := ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), SCompact X u

def SinfSectionC : Prop := ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), SinfSection X u

end Formalism.L2.SG.Pf
