import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeLeSmoothVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorMatrixCoeffHolomorphicType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeEqZeroOfTorusLawAtOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameBorelActsExtremalVectorByWeight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolLowOnce

open GlobalTheory.HolDict.HolTo GlobalTheory.HolDict.CoefExt

section General

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Hm : Mt n} {σ : Mt n → (H →L[ℂ] H)} {v : H}

theorem smFn_coef (hσ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH Hm) σ) (hv : SmoothVec (lieH Hm) σ v) (l : H) :
    SmFn (fun _ : Unit => Hm) fun u => ⟪l, σ (u ()) v⟫_ℂ := by
  intro k τs Xs hX u hu
  have hmem : ∀ t : Fin k → ℝ, (List.ofFn fun i =>
      (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : Unit → Mt n)).prod ∈ UG (fun _ : Unit => Hm) := fun t =>
    prod_mem_UG _ fun v hv => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
      exact single_mem_UG (fun _ : Unit => Hm) _ (hX i) _
  simp only [Pi.mul_apply, hσ.2 _ (hu ()) _ (hmem _ ()), ContinuousLinearMap.comp_apply]
  simp only [prod_single_apply, if_true]
  have h1 := hv k Xs hX
  exact (((innerSL ℂ l).comp (σ (u ()))).restrictScalars ℝ).contDiff.comp h1

theorem der_coef (hσ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH Hm) σ) (hv : SmoothVec (lieH Hm) σ v) (l : H) {X : Mt n}
    (hX : X ∈ lieH Hm) {u : Unit → Mt n} (hu : u ∈ UG (fun _ : Unit => Hm)) :
    der () X (fun u => ⟪l, σ (u ()) v⟫_ℂ) u = ⟪l, σ (u ()) (dRep σ X v)⟫_ℂ := by
  unfold der
  have e : (fun t : ℝ => ⟪l, σ ((u * (Pi.mulSingle () (NormedSpace.exp (t • X)) : Unit → Mt n)) ()) v⟫_ℂ) =
      fun t : ℝ => ⟪l, σ (u ()) (σ (NormedSpace.exp (t • X)) v)⟫_ℂ := by
    funext t
    rw [Pi.mul_apply, hσ.2 _ (hu ()) _ (single_mem_UG (fun _ : Unit => Hm) () hX t ()), Pi.mulSingle_eq_same]
    rfl
  rw [e]
  exact ((((innerSL ℂ l).comp (σ (u ()))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_of_smooth hv hX)).deriv

theorem derC_coef {q : ℕ} {x₀ : Mt n} (h : OrthFr Hm q x₀)
    (hσ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH Hm) σ) (hv : SmoothVec (lieH Hm) σ v) (l : H) (Z : Mt n) {u : Unit → Mt n}
    (hu : u ∈ UG (fun _ : Unit => Hm)) :
    derC (fun _ : Unit => Hm) () Z (fun u => ⟪l, σ (u ()) v⟫_ℂ) u = ⟪l, σ (u ()) (dRepC Hm σ Z v)⟫_ℂ := by
  obtain ⟨h1, h2⟩ := conj_facts (herm_of_orth h) (dets_ne h).1 Z
  have hA : (1 / 2 : ℂ) • (Z + conjH Hm Z) ∈ lieH Hm := by
    show _ = _
    rw [conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h1, h2]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    abel_nf
    simp
  have hB : (1 / (2 * Complex.I) : ℂ) • (Z - conjH Hm Z) ∈ lieH Hm := by
    show _ = _
    rw [conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
    have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
    rw [this, neg_smul, ← smul_neg, ← smul_add]
    abel_nf
    simp
  unfold derC dRepC
  rw [der_coef hσ hv l hA hu, der_coef hσ hv l hB hu, map_add, map_smul, inner_add_right, inner_smul_right]

theorem inner_iso (T : H →L[ℂ] H) (hT : ∀ x, ‖T x‖ = ‖x‖) (x y : H) : ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨T.toLinearMap, hT⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y

theorem eq_zero_of_orth [CompleteSpace H] {q : ℕ} {x₀ : Mt n} {w : Fin n → ℤ} (h : OrthFr Hm q x₀)
    (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) (hirr : IsIrredOn (Formalism.QuantumDeterminants.UH Hm) σ) (hv : SmoothVec (lieH Hm) σ v) (hv0 : v ≠ 0)
    (hk : ∀ a c : Fin n, a ≤ c → dRepC Hm σ (x₀ * Matrix.single a c 1 * x₀⁻¹) v = if a = c then (w a : ℂ) • v else 0)
    (l : H) (hmem : ∀ s, torEl (fun _ : Unit => x₀) s () ∈ Formalism.QuantumDeterminants.UH Hm)
    (hl : ∀ s, σ (torEl (fun _ : Unit => x₀) s ()) l = torCh (fun _ : Unit => w) s • l) (h0 : ⟪l, v⟫_ℂ = 0) : l = 0 := by
  have hf : HolFn (fun _ : Unit => Hm) (fun _ => q) (fun _ => x₀) (fun _ => w) fun u => ⟪l, σ (u ()) v⟫_ℂ := by
    refine GlobalTheory.HolDict.holFn_of_killed _ _ _ _ _ _ (fun _ => h) _ (smFn_coef hσ.1 hv l) ?_
    rintro ⟨⟩ a c hac u hu
    rw [derC_coef h hσ.1 hv l _ hu, hk a c hac]
    split_ifs
    · rw [map_smul, inner_smul_right]
    · simp
  have hz := GlobalTheory.HolDict.Uniq.eq_zero_of_torus_law _ _ _ _ _ _ (fun _ => h) _ hf (fun u hu s => by
    have hn : (starRingEnd ℂ) (torCh (fun _ : Unit => w) s) * torCh (fun _ : Unit => w) s = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp [torCh, norm_prod, norm_zpow, Complex.norm_exp_ofReal_mul_I]
    have e := inner_iso _ (hσ.2.1 _ (hmem s)) l (σ (u ()) v)
    rw [hl, inner_smul_left] at e
    simp only [Pi.mul_apply]
    rw [hσ.1.2 _ (hmem s) _ (hu ()), ← e, ← mul_assoc, mul_comm (torCh _ s), hn, one_mul]
    rfl) (by
      simp only [Pi.one_apply]
      rw [hσ.1.1]
      exact h0)
  let P : Submodule ℂ H := ⨅ g ∈ Formalism.QuantumDeterminants.UH Hm, LinearMap.ker ((innerSL ℂ l).comp (σ g)).toLinearMap
  have hP : ∀ y, y ∈ P ↔ ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ⟪l, σ g y⟫_ℂ = 0 := fun y => by
    simp only [P, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  have hcl : IsClosed (P : Set H) := by
    have : (P : Set H) = ⋂ g ∈ Formalism.QuantumDeterminants.UH Hm, {y | ⟪l, σ g y⟫_ℂ = 0} := by
      ext y
      simp only [SetLike.mem_coe, hP, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_biInter fun g _ => isClosed_eq (by fun_prop) continuous_const
  have hone : (1 : Mt n) ∈ Formalism.QuantumDeterminants.UH Hm := by
    show _ = _
    simp
  rcases hirr P hcl (fun g hg y hy => (hP _).2 fun g' hg' => by
    have hgg : g' * g ∈ Formalism.QuantumDeterminants.UH Hm := by
      have e1 : gᴴ * Hm * g = Hm := hg
      have e2 : g'ᴴ * Hm * g' = Hm := hg'
      show _ = _
      rw [conjTranspose_mul]
      calc gᴴ * g'ᴴ * Hm * (g' * g) = gᴴ * (g'ᴴ * Hm * g') * g := by simp only [Matrix.mul_assoc]
        _ = Hm := by rw [e2, e1]
    have := (hP y).1 hy _ hgg
    rwa [hσ.1.2 _ hg' _ hg] at this) with hb | ht
  · have : v ∈ P := (hP v).2 fun g hg => hz (fun _ => g) fun _ => hg
    rw [hb] at this
    exact absurd this hv0
  · have := (hP l).1 (ht ▸ Submodule.mem_top) 1 hone
    rw [hσ.1.1] at this
    exact inner_self_eq_zero.1 this

theorem torEl_mem {q : ℕ} {x₀ : Mt n} (h : OrthFr Hm q x₀) (s : Unit → Fin n → ℝ) :
    torEl (fun _ : Unit => x₀) s () ∈ Formalism.QuantumDeterminants.UH Hm := by
  have hx : IsUnit x₀.det := (dets_ne h).2.isUnit
  have hx' : IsUnit x₀ᴴ.det := by rw [det_conjTranspose]; exact hx.star
  set d : Mt n := diagonal fun a => Complex.exp ((s () a : ℂ) * Complex.I) with hd
  have e : dᴴ * (x₀ᴴ * Hm * x₀) * d = x₀ᴴ * Hm * x₀ := by
    rw [h.2, hd, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext a
    simp only [Pi.star_apply, Complex.star_def]
    rw [mul_right_comm, mul_comm ((starRingEnd ℂ) _), Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    simp
  show (x₀ * d * x₀⁻¹)ᴴ * Hm * (x₀ * d * x₀⁻¹) = Hm
  calc (x₀ * d * x₀⁻¹)ᴴ * Hm * (x₀ * d * x₀⁻¹) = (x₀ᴴ)⁻¹ * (dᴴ * (x₀ᴴ * Hm * x₀) * d) * x₀⁻¹ := by
        simp only [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc]
    _ = Hm := by
      rw [e, Matrix.mul_assoc x₀ᴴ, Matrix.nonsing_inv_mul_cancel_left _ _ hx', Matrix.mul_nonsing_inv_cancel_right _ _ hx]

theorem wt_int {ε : Fin n → Bool} {μ : Fin n → ℝ} (h1 : σ 1 = 1) (hv0 : v ≠ 0) (hv : IsWtOn (Formalism.REAL.Kset ε) σ μ v)
    (a : Fin n) : ∃ m : ℤ, (m : ℝ) = μ a := by
  have h := hv (Pi.single a (2 * Real.pi)) (diag_mem _)
  have e : (diagonal fun b => Complex.exp ((((Pi.single a (2 * Real.pi) : Fin n → ℝ) b : ℝ) : ℂ) * Complex.I)) = (1 : Mt n) := by
    rw [← diagonal_one]
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      simp
    · simp [hb]
  rw [e, h1, Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp), Pi.single_eq_same] at h
  have h2 : Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 :=
    (smul_left_injective ℂ hv0 (h.symm.trans (one_smul ℂ v).symm))
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h2
  refine ⟨m, ?_⟩
  have h3 : ((μ a : ℝ) : ℂ) * (2 * Real.pi * Complex.I) = m * (2 * Real.pi * Complex.I) := by
    rw [← hm]; push_cast; ring
  exact_mod_cast (mul_right_cancel₀ Complex.two_pi_I_ne_zero h3).symm

theorem exists_ext_mem {ε : Fin n → Bool} {Λ : Fin n → ℝ} (hU : IsURepOn (UJset ε) σ) {S : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) : ∃ w ∈ S, ‖w‖ = 1 ∧ IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Λ (revNeg ε a)) w := by
  obtain ⟨v, hvS, hv0, hv⟩ := hS.2.2.2.1
  have hK := pM_mem (revNeg ε) (eps_revNeg ε)
  have hn : ‖σ (pM (revNeg ε)) v‖ = ‖v‖ := hU.2.1 _ (kset_uj hK) v
  have hp : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • σ (pM (revNeg ε)) v, Submodule.smul_mem _ _ (hS.2.1 _ hK v hvS), ?_,
    isWtOn_smul (isWtOn_perm hU _ (eps_revNeg ε) hv) _⟩
  rw [norm_smul, hn, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hp]

end General

theorem torus_wt {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {w : D.what₂.Tau → Fin V.rank → ℤ}
    (hw : WtIs M w) (τ : D.what₂.Tau) {l : M.H τ} (hl : IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) (extWt M τ) l)
    (s : Unit → Fin V.rank → ℝ) (hx : (x0Mat M τ).det ≠ 0) :
    M.rep τ (torEl (fun _ : Unit => x0Mat M τ) s ()) l = torCh (fun _ : Unit => w τ) s • l := by
  set e := Equiv.ofBijective _ (arr_bijective (nNeg_le (M.ε τ))) with he
  have hfr : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 := torus_x0Mat M τ fun a => Complex.exp ((s () (e.symm a) : ℂ) * Complex.I)
  have h2 : ∀ c, e.symm (arr (nNeg (M.ε τ)) c) = c := fun c => e.symm_apply_apply c
  simp only [h2] at h1
  have h3 : M.fr τ * torEl (fun _ : Unit => x0Mat M τ) s () * (M.fr τ)⁻¹ =
      diagonal fun a => Complex.exp ((s () (e.symm a) : ℂ) * Complex.I) := by
    unfold torEl
    rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hx.isUnit, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hfr, Matrix.mul_nonsing_inv_cancel_right _ _ hfr]
  unfold DSModel.rep torCh
  rw [h3, hl (fun a => s () (e.symm a)) (diagonal_mem_Kset _ _), Fintype.prod_unique]
  congr 1
  rw [← e.sum_comp]
  simp only [← Complex.exp_int_mul, ← Complex.exp_sum, Equiv.symm_apply_apply]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h4 : extWt M τ (e c) = (w τ c : ℝ) := (hw τ c).symm
  rw [h4]
  push_cast
  ring

theorem lowSm_and_lowIrr : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), HolShape M →
    LowSm M ∧ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M := by
  intro D V S M hM
  choose S₀ hS₀ hsm using GlobalTheory.SmoothLowType.exists_lowK_le_sm D V S M
  have hU := fun τ => (M.ds τ).2.2.1
  choose v hvS hv1 hvw using fun τ => exists_ext_mem (hU τ) (hS₀ τ)
  have hv0 : ∀ τ, v τ ≠ 0 := fun τ h => by simpa [h] using hv1 τ
  choose w hw using fun τ c => wt_int (hU τ).1.1 (hv0 τ) (hvw τ) (arr (nNeg (M.ε τ)) c)
  have hW : WtIs M w := hw
  have hle : ∀ τ, S₀ τ ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := fun τ =>
    le_sSup (s := {S | IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S}) (hS₀ τ)
  have hE : IsExtVec M fun τ => ⟨v τ, hsm τ (hvS τ)⟩ := fun τ => ⟨hv1 τ, hle τ (hvS τ), hvw τ⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  have key : ∀ τ, lowKSub (M.ε τ) (M.lam τ) (M.σ τ) = S₀ τ := fun τ => by
    refine le_antisymm (sSup_le fun T hT => ?_) (hle τ)
    have hT : IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) T := hT
    obtain ⟨v', hv'T, hv'1, hv'w⟩ := exists_ext_mem (hU τ) hT
    obtain ⟨hc, hR, hI, hx⟩ := GlobalTheory.HolDict.ModelRep.model_rep D V S M τ
    obtain ⟨ho, -⟩ := hx hM
    obtain ⟨hs, hk⟩ := GlobalTheory.HolDict.VKill.borel_extVec D θ V S M w _ hθ hM hW hE τ
    have hl : IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) (extWt M τ) (v' - ⟪v τ, v'⟫_ℂ • v τ) := fun t ht => by
      rw [map_sub, map_smul, hv'w t ht, hvw τ t ht, smul_sub, smul_comm]
      rfl
    have hz : v' - ⟪v τ, v'⟫_ℂ • v τ = 0 :=
      eq_zero_of_orth ho hR hI hs (hv0 τ) hk _ (torEl_mem ho) (fun s => torus_wt M hW τ hl s (dets_ne ho).2) (by
        rw [← inner_conj_symm, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv1]
        simp)
    have hv'S : v' ∈ S₀ τ := by
      rw [sub_eq_zero.1 hz]
      exact Submodule.smul_mem _ _ (hvS τ)
    rcases hT.2.2.1 (T ⊓ S₀ τ) inf_le_left (fun g hg y hy => ⟨hT.2.1 g hg y hy.1, (hS₀ τ).2.1 g hg y hy.2⟩) with h | h
    · have : v' ∈ T ⊓ S₀ τ := ⟨hv'T, hv'S⟩
      rw [h, Submodule.mem_bot] at this
      simp [this] at hv'1
    · exact h ▸ inf_le_right
  exact ⟨fun τ => key τ ▸ hsm τ, fun τ => key τ ▸ hS₀ τ⟩

end GlobalTheory.HolLowOnce
