import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JointHarm

theorem vhol_diff_prod {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {s : Set E} (u : Finset κ)
    (f : κ → E → ℂ) (h : ∀ i, DifferentiableOn ℂ (f i) s) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ u, f i z) s := by
  induction u using Finset.induction_on with
  | empty => simpa using differentiableOn_const _
  | insert a u ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

theorem vhol_diff_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} {s : Set E}
    (A : E → Matrix (Fin n) (Fin n) ℂ) (h : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) s) :
    DifferentiableOn ℂ (fun z => (A z).det) s := by
  simp only [Matrix.det_apply']
  refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul ?_ _
  exact vhol_diff_prod _ (fun i z => A z (σ i) i) fun i => h _ _

theorem vhol_diff_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} {s : Set E}
    (A : E → Matrix (Fin n) (Fin n) ℂ) (h : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) s)
    (h0 : ∀ z ∈ s, (A z).det ≠ 0) (i j : Fin n) :
    DifferentiableOn ℂ (fun z => (A z)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine ((vhol_diff_det A h).inv h0).mul (vhol_diff_det _ fun a b => ?_)
  by_cases ha : a = j
  · simp only [Matrix.updateRow_apply, if_pos ha]
    exact differentiableOn_const _
  · simp only [Matrix.updateRow_apply, if_neg ha]
    exact h a b

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem vhol_diff_fock {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {s : Set E}
    (U : E → ι → Matrix (Fin n) (Fin n) ℂ) (h : ∀ τ i j, DifferentiableOn ℂ (fun z => U z τ i j) s)
    (x y : Pol ℂ ι n) :
    DifferentiableOn ℂ (fun z => fockL x (Formalism.GradedWeylDivisibility.blockAct ℂ (U z) y)) s := by
  induction y using MvPolynomial.induction_on generalizing x with
  | C a =>
    simp only [MvPolynomial.algHom_C]
    exact differentiableOn_const _
  | add p q hp hq =>
    simp only [map_add]
    exact (hp x).add (hq x)
  | mul_X p v hp =>
    have e1 : ∀ z, Formalism.GradedWeylDivisibility.blockAct ℂ (U z) (p * MvPolynomial.X v) =
        ∑ b : Fin n, U z v.1 v.2.1 b • (MvPolynomial.X (v.1, (b, v.2.2)) * Formalism.GradedWeylDivisibility.blockAct ℂ (U z) p) := by
      intro z
      rw [map_mul, blockAct_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [MvPolynomial.smul_eq_C_mul]; ring
    simp only [e1, map_sum, map_smul, ← fockL_pderiv_X, smul_eq_mul]
    exact DifferentiableOn.fun_sum fun b _ => (h _ _ _).mul (hp _)

theorem vhol_aniso {σ : Type} (x : MvPolynomial σ ℂ) (hx : fockL x x = 0) : x = 0 := by
  rw [fockL_apply, fockS] at hx
  have e : ∀ m, star (x.coeff m) * x.coeff m * (mfact m : ℂ) =
      ((Complex.normSq (x.coeff m) * (mfact m : ℝ) : ℝ) : ℂ) := by
    intro m
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    simp
  simp only [e] at hx
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)] at hx
  ext m
  by_contra hm
  have h1 := hx m (MvPolynomial.mem_support_iff.2 hm)
  have h2 : 0 < mfact m := Finset.prod_pos fun k _ => Nat.factorial_pos _
  rcases mul_eq_zero.1 h1 with h | h
  · exact hm (Complex.normSq_eq_zero.1 h)
  · exact h2.ne' (by exact_mod_cast h)

theorem vhol_one (lam : ι → DomWeight n) : vact lam 1 = 1 := by
  unfold vact
  simp only [Pi.one_apply, Matrix.det_one, _root_.one_zpow, Finset.prod_const_one, one_smul, inv_one, blockAct_one]
  rfl

theorem vhol_mul (lam : ι → DomWeight n) (a b : ι → Matrix (Fin n) (Fin n) ℂ) :
    vact lam (a * b) = vact lam a * vact lam b := by
  apply LinearMap.ext
  intro F
  have := congrArg (fun φ => φ F) (blockAct_comp (fun τ => (a τ)⁻¹) (fun τ => (b τ)⁻¹))
  simp only [AlgHom.comp_apply] at this
  simp only [vact, Pi.mul_apply, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_inv_rev,
    Module.End.mul_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, this]
  rw [mul_comm]

theorem vhol_adj (lam : ι → DomWeight n) (a : ι → Matrix (Fin n) (Fin n) ℂ) (x y : Pol ℂ ι n) :
    fockL (vact lam a x) y = fockL x (vact lam (fun τ => (a τ)ᴴ) y) := by
  simp only [vact, LinearMap.smul_apply, AlgHom.toLinearMap_apply, LinearMap.map_smulₛₗ, map_smul,
    fockL_blockAct_adj, Matrix.conjTranspose_nonsing_inv, Matrix.det_conjTranspose, starRingEnd_apply, star_prod,
    star_zpow₀, RingHom.id_apply]

theorem vhol_units (lam : ι → DomWeight n) (G : ι → GL (Fin n) ℂ) :
    vact lam (fun τ => (G τ : Matrix (Fin n) (Fin n) ℂ)) = actP lam (invTrK G) := by
  unfold vact actP trAct
  rw [detTw_eq]
  simp only [invTrK_coe, Matrix.transpose_transpose, Matrix.det_transpose, Matrix.coe_units_inv,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', _root_.zpow_neg, _root_.inv_zpow]

theorem vhol_ext (lam : ι → DomWeight n) (τ : ι) (g : GL (Fin n) ℂ) (c : ℂ)
    (h : sqAct ℂ n (lam τ) (inside₂ ℂ n g) (extremal ℂ n (lam τ)) = c • extremal ℂ n (lam τ)) :
    vact lam (Pi.mulSingle τ (g : Matrix (Fin n) (Fin n) ℂ)) (ten fun τ => extremal ℂ n (lam τ)) =
      c • ten fun τ => extremal ℂ n (lam τ) := by
  have e : (Pi.mulSingle τ (g : Matrix (Fin n) (Fin n) ℂ) : ι → Matrix (Fin n) (Fin n) ℂ) =
      fun σ => ((Pi.mulSingle τ g : ι → GL (Fin n) ℂ) σ : Matrix (Fin n) (Fin n) ℂ) := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ; simp
    · simp [hσ]
  rw [e, vhol_units, actTen]
  unfold ten
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ),
    ← Finset.mul_prod_erase _ (fun σ => Formalism.GradedWeylDivisibility.blockEmb ℂ σ (extremal ℂ n (lam σ))) (Finset.mem_univ τ),
    ← smul_mul_assoc]
  congr 1
  · rw [← map_smul, ← h]
    show Formalism.GradedWeylDivisibility.blockEmb ℂ τ (sqAct ℂ n (lam τ) (inside₂ ℂ n ((Pi.mulSingle τ g : ι → GL (Fin n) ℂ) τ)) _) = _
    rw [Pi.mulSingle_eq_same]
  · refine Finset.prod_congr rfl fun σ hσ => ?_
    refine congrArg (Formalism.GradedWeylDivisibility.blockEmb ℂ σ) ?_
    refine (factSqHighestWeight ℂ n (lam σ)).2 _ ?_ ?_
    · rw [invTrK_coe, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hσ)]
      simpa using Matrix.blockTriangular_one
    · intro a
      rw [invTrK_coe, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hσ)]
      simp

theorem vhol_lo_inv (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g) (h : IsLoUni g) :
    (g⁻¹)ᵀ.BlockTriangular id ∧ ∀ a, g⁻¹ a a = 1 := by
  have h1 : gᵀ.BlockTriangular id := fun i j hij => (h j i).1 hij
  have hu : IsUnit gᵀ := (Matrix.isUnit_transpose g).2 hg
  obtain ⟨inst⟩ := hu.nonempty_invertible
  have h2 : (gᵀ)⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular h1
  rw [← Matrix.transpose_nonsing_inv] at h2
  refine ⟨h2, fun a => ?_⟩
  have h3 := congrFun (congrFun (Matrix.mul_nonsing_inv g ((Matrix.isUnit_iff_isUnit_det g).1 hg)) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, (h a a).2 rfl, one_mul, Matrix.one_apply_eq] at h3
  · exact h3
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with hlt | hlt
    · have : g⁻¹ b a = 0 := h2 (i := a) (j := b) hlt
      rw [this, mul_zero]
    · rw [(h a b).1 hlt, zero_mul]
  · simp

theorem vact_isHolFam_isBotFam : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n),
    IsHolFam (fun _ => allPos n) fockL (vact lam) ∧
    IsBotFam (fun _ => allPos n) (vact lam) (fun τ j => -((lam τ).w j : ℝ)) (ten fun τ => extremal ℂ n (lam τ)) ∧
    (ten fun τ => extremal ℂ n (lam τ)) ≠ 0 ∧ (ten fun τ => extremal ℂ n (lam τ)) ∈ VV ℂ lam := by
  intro ι _ n lam
  refine ⟨⟨vhol_aniso, vhol_one lam, fun a b _ _ => vhol_mul lam a b, fun τ =>
    ⟨vhol_aniso, ?_, fun a _ b _ => ?_, fun g _ x y => ?_, fun x y => ?_⟩⟩, fun τ => ⟨fun g hg hl => ?_, fun θ => ?_⟩,
    ?_, ?_⟩
  · show vact lam (Pi.mulSingle τ 1) = 1
    rw [Pi.mulSingle_one, vhol_one]
  · show vact lam (Pi.mulSingle τ (a * b)) = _
    rw [Pi.mulSingle_mul, vhol_mul]
  · show fockL (vact lam (Pi.mulSingle τ g) x) y = fockL x (vact lam (Pi.mulSingle τ gᴴ) y)
    rw [vhol_adj]
    refine congrArg (fun u => fockL x (vact lam u y)) ?_
    funext σ
    by_cases hσ : σ = τ
    · subst hσ; simp
    · simp [hσ]
  · have h1 : ∀ σ i j, DifferentiableOn ℂ (fun g : Fin n → Fin n → ℂ =>
        (Pi.mulSingle τ (Matrix.of g) : ι → Matrix (Fin n) (Fin n) ℂ) σ i j)
        {g | Matrix.of g ∈ GlobalTheory.Dec.KC (allPos n)} := by
      intro σ i j
      by_cases hσ : σ = τ
      · subst hσ
        simp only [Pi.mulSingle_eq_same, Matrix.of_apply]
        fun_prop
      · simp only [Pi.mulSingle_eq_of_ne hσ]
        exact differentiableOn_const _
    have h0 : ∀ σ, ∀ g ∈ {g : Fin n → Fin n → ℂ | Matrix.of g ∈ GlobalTheory.Dec.KC (allPos n)},
        ((Pi.mulSingle τ (Matrix.of g) : ι → Matrix (Fin n) (Fin n) ℂ) σ).det ≠ 0 := by
      intro σ g hg
      by_cases hσ : σ = τ
      · subst hσ
        rw [Pi.mulSingle_eq_same]
        exact ((Matrix.isUnit_iff_isUnit_det _).1 hg.1).ne_zero
      · rw [Pi.mulSingle_eq_of_ne hσ]
        simp
    simp only [vact, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_eq_mul]
    refine DifferentiableOn.mul (vhol_diff_prod _ (fun σ (g : Fin n → Fin n → ℂ) =>
      ((Pi.mulSingle τ (Matrix.of g) : ι → Matrix (Fin n) (Fin n) ℂ) σ).det ^ (-(lam σ).detShift)) fun σ => ?_)
      (vhol_diff_fock _ (fun σ => vhol_diff_inv _ (h1 σ) (h0 σ)) x y)
    exact (vhol_diff_det _ (h1 σ)).zpow (Or.inl (h0 σ))
  · obtain ⟨h2, h3⟩ := vhol_lo_inv g hg.1 hl
    obtain ⟨G, rfl⟩ := hg.1
    have := vhol_ext lam τ G 1 (by
      rw [one_smul]
      refine (factSqHighestWeight ℂ n (lam τ)).2 _ ?_ ?_
      · simpa [inside₂] using h2
      · simpa [inside₂] using h3)
    rwa [one_smul] at this
  · let t : Fin n → ℂˣ := fun a => Units.mk0 (Complex.exp ((θ a : ℂ) * Complex.I)) (Complex.exp_ne_zero _)
    have e1 : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := rfl
    have e2 : inside₂ ℂ n (diagGL ℂ n t) = diagGL ℂ n t⁻¹ := by
      apply Units.ext
      exact Matrix.diagonal_transpose _
    show vact lam (Pi.mulSingle τ _) _ = _
    rw [← e1]
    apply vhol_ext
    rw [e2, (factSqHighestWeight ℂ n (lam τ)).1]
    congr 1
    rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, Units.coe_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [t, Pi.inv_apply, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, Units.val_mk0,
      ← Complex.exp_neg, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  · refine Finset.prod_ne_zero_iff.2 fun τ _ h => Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl (lam τ).natW ?_
    exact MvPolynomial.rename_injective (fun v : Fin n × Fin n => (τ, v)) (fun _ _ h => congrArg Prod.snd h)
      (h.trans (map_zero _).symm)
  · exact Submodule.subset_span ⟨fun τ => extremal ℂ n (lam τ),
      fun τ => Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (natW_antitone (lam τ)), rfl⟩

end GlobalTheory.JointHarm

end
