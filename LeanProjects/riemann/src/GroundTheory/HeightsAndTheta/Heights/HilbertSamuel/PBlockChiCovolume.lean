import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Matrix SupBoundCount

noncomputable section

namespace BlockChiCovolume

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem gram_symm (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (k l : Fin r) :
    blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) l k =
      blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) k l := by
  rw [blockGram_eq d n f hf, blockGram_eq d n f hf]
  simp only [pairRe_comm]

theorem quad_nonneg (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (a : Fin r → ℝ) :
    0 ≤ a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a) := by
  rw [gram_quad d n f hf]
  have h : ∀ z, 0 ≤ ‖comb f a z‖ ^ 2 / d.A.h z ^ (2 * n) := fun z =>
    div_nonneg (sq_nonneg _) ((even_two_mul n).pow_nonneg _)
  have h1 := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (blockPt d x)‖ ^ 2 / d.A.h (blockPt d x) ^ (2 * n)) fun x => h _
  have h2 := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (conjPt (blockPt d x))‖ ^ 2 / d.A.h (conjPt (blockPt d x)) ^ (2 * n)) fun x => h _
  exact mul_nonneg (by norm_num) (add_nonneg h1 h2)

theorem entry_of_quad {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (hG : ∀ k l, G l k = G k l) (k l : Fin r) :
    G k l = ((Pi.single k 1 + Pi.single l 1) ⬝ᵥ (G *ᵥ (Pi.single k 1 + Pi.single l 1)) -
      Pi.single k 1 ⬝ᵥ (G *ᵥ Pi.single k 1) - Pi.single l 1 ⬝ᵥ (G *ᵥ Pi.single l 1)) / 2 := by
  simp [mulVec_add, dotProduct_add, add_dotProduct, hG l k]
  ring

theorem cast_single_add {r : ℕ} (k l : Fin r) :
    (fun j => (((Pi.single k 1 + Pi.single l 1 : Fin r → ℤ) j : ℤ) : ℝ)) = Pi.single k 1 + Pi.single l 1 := by
  funext j
  simp only [Pi.add_apply, Int.cast_add, Pi.single_apply]
  split_ifs <;> simp

theorem cast_single {r : ℕ} (k : Fin r) :
    (fun j => (((Pi.single k 1 : Fin r → ℤ) j : ℤ) : ℝ)) = Pi.single k 1 := by
  funext j
  simp only [Pi.single_apply]
  split_ifs <;> simp

end BlockChiCovolume

open BlockChiCovolume in

theorem BlockChiCovolume.proof : BlockChiCovolume.Statement := by
  intro D K _ _ ι _ Ω _ _ d n E hE r ψ hψ hnorm _ _
  have hex := exists_isSecBasisM d.y d.k₀ n
  rw [blockChi, dif_pos hex]
  have hb := hex.choose_spec
  generalize hex.choose = p at hb ⊢
  obtain ⟨hbf, hli, hspan⟩ := hb
  choose f hf hfb using hbf
  have hbeq : p.2 = fun j => map (Int.castRingHom ℚ) (f j) := funext hfb
  rw [hbeq] at hli hspan ⊢
  beta_reduce at hli hspan
  obtain ⟨w, hw⟩ : ∃ w : Fin p.1 → Ω, w = fun j => aeval d.y (map (Int.castRingHom ℚ) (f j)) := ⟨_, rfl⟩
  rw [← hw] at hli hspan
  have hEN : E = (Submodule.span ℤ (Set.range w)).toAddSubgroup := hE.trans hspan.symm
  let eN : E ≃+ Submodule.span ℤ (Set.range w) :=
    (AddEquiv.addSubgroupCongr hEN).trans (AddEquiv.refl _)
  let bE : Module.Basis (Fin p.1) ℤ E := (Module.Basis.span hli).map eN.symm.toIntLinearEquiv
  have hrange : LinearMap.range ψ.toIntLinearMap = imageLattice ψ := by
    ext v
    simp [imageLattice]
  let B : Module.Basis (Fin p.1) ℤ (imageLattice ψ) :=
    (bE.map (LinearEquiv.ofInjective ψ.toIntLinearMap hψ)).map (LinearEquiv.ofEq _ _ hrange)
  let ε : Fin p.1 → E := fun j => ⟨w j, hEN ▸ Submodule.subset_span ⟨j, rfl⟩⟩
  have hB : ∀ j, (B j : EuclideanSpace ℝ (Fin r)) = ψ (ε j) := by
    intro j
    rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.map_apply]
    show ψ (bE j) = ψ (ε j)
    congr 1
    apply Subtype.ext
    rw [Module.Basis.map_apply]
    have h : ((Module.Basis.span hli j : Submodule.span ℤ (Set.range w)) : Ω) = w j :=
      congrArg Subtype.val (Module.Basis.span_apply hli j)
    exact h
  set G := blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) with hG
  have key : ∀ m : Fin p.1 → ℤ,
      ‖ψ (∑ j, m j • ε j)‖ ^ 2 = (fun j => (m j : ℝ)) ⬝ᵥ (G *ᵥ fun j => (m j : ℝ)) := by
    intro m
    rw [hnorm _ (∑ j, m j • f j) (isMultiHomog_zsum f m hf), blockL2Norm_sum_eq_sqrt_gram d n f hf m,
      Real.sq_sqrt (quad_nonneg d n f hf _)]
    simp [ε, hw, aeval_map_int, map_sum]
  have hgram : Matrix.gram ℝ (fun i => (B i : EuclideanSpace ℝ (Fin r))) = G := by
    ext k l
    rw [entry_of_quad G (gram_symm d n f hf) k l, ← cast_single_add, ← cast_single, ← cast_single, ← key, ← key,
      ← key]
    simp only [Matrix.gram, of_apply, hB]
    simp [Pi.single_apply, add_smul, Finset.sum_add_distrib]
    rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
    ring
  have hdet : 0 ≤ G.det := hgram ▸ (Matrix.posSemidef_gram ℝ _).det_nonneg
  rw [covolume_eq_sqrt_det_gram (imageLattice ψ) B, hgram, Real.log_sqrt hdet]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
