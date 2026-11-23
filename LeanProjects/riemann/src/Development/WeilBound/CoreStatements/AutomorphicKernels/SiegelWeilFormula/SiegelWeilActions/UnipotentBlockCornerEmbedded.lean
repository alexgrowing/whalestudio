import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PartialDerivativeAlgebra
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ShiftCoordinatesColumn

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq PositivityTheory.SiegelWeilFormula.Act.C5

namespace PositivityTheory.SiegelWeilFormula.Act.C6

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

variable (L) in

def sExp (e : AE F E) (b : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks 1 (∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(e * cA σ (b j))))) 0 1

theorem fixed_in_F (hcm : IsCMExt F E σ) (z : E) (hz : σ z = z) : ∃ f : F, algebraMap F E f = z := by
  obtain ⟨_, htc, hdeg, hconj⟩ := hcm
  classical
  have hz' : z ∈ AlgHom.equalizer σ (AlgHom.id F E) := (AlgHom.mem_equalizer _ _ _).2 hz
  have hS : AlgHom.equalizer σ (AlgHom.id F E) = ⊥ := by
    have hp : (Module.finrank F E).Prime := by
      rw [hdeg]
      exact Nat.prime_two
    have := Subalgebra.isSimpleOrder_of_finrank_prime F E hp
    rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
    · exact h
    · exfalso
      have hid : ∀ x, σ x = x := fun x => by
        have hx : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := h ▸ Algebra.mem_top
        exact (AlgHom.mem_equalizer _ _ _).1 hx
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
      have hreal : NumberField.ComplexEmbedding.IsReal w.embedding := by
        rw [NumberField.ComplexEmbedding.isReal_iff]
        ext x
        rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
        have hx := hconj w.embedding x
        rw [hid x] at hx
        exact hx.symm
      exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (htc.isComplex w))
        (NumberField.InfinitePlace.isReal_iff.2 hreal)
  rw [hS] at hz'
  exact Algebra.mem_bot.1 hz'

theorem nq_cM (h : Hyp L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b (cM c)) := by
  rw [cM_frame h c]
  have hne' : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
  refine ⟨fun k => ?_, fun k l hl1 hl2 hk => ?_⟩
  · rcases k with k | k
    · simp [uA, Matrix.sum_apply, Matrix.one_apply, hne']
    · simp
  · rcases k with k | k <;> rcases l with l | l
    · have hk' : L.i₀ ≠ k := fun e => hk (by rw [e])
      simp [uA, Matrix.sum_apply, Matrix.one_apply, hk']
    · have hk' : L.i₀ ≠ k := fun e => hk (by rw [e])
      simp [aB, hk']
    · simp
    · have hl' : L.i₀ ≠ l := fun e => hl2 (by rw [e])
      by_cases hkl : l = k
      · subst hkl
        simp [uA, Matrix.sum_apply, hl']
      · simp [uA, Matrix.sum_apply, hl', Ne.symm hkl]

namespace B

variable (L) in

def sb (e : AE F E) (b : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ j, (Matrix.single L.i₀ (L.em j) (b j) + Matrix.single (L.em j) L.i₀ (-(e * cA σ (b j))))

theorem sExp_eq (e : AE F E) (b : Fin L.n → AE F E) : sExp L e b = Matrix.fromBlocks 1 (sb L e b) 0 1 := rfl

theorem hne (j : Fin L.n) : L.em j ≠ L.i₀ := by
  exact (L.rng (L.em j)).2 ⟨j, rfl⟩

theorem siegel_block_corner_zero (e : AE F E) (b : Fin L.n → AE F E) : sb L e b L.i₀ L.i₀ = 0 := by
  simp [sb, Matrix.sum_apply, Matrix.add_apply, hne]

theorem siegel_block_corner_embedded (e : AE F E) (b : Fin L.n → AE F E) (k : Fin L.n) : sb L e b L.i₀ (L.em k) = b k := by
  have h1 : ∀ j, L.i₀ ≠ L.em j := fun j => (hne j).symm
  simp [sb, Matrix.sum_apply, Matrix.single_apply, Matrix.add_apply, hne, h1, L.inj.eq_iff]

theorem siegel_block_row_embedded (e : AE F E) (b : Fin L.n → AE F E) (k : Fin L.n) :
    sb L e b (L.em k) L.i₀ = -(e * cA σ (b k)) := by
  have h1 : ∀ j, L.i₀ ≠ L.em j := fun j => (hne j).symm
  simp [sb, Matrix.sum_apply, Matrix.single_apply, Matrix.add_apply, hne, h1, L.inj.eq_iff]

theorem sb_em_em (e : AE F E) (b : Fin L.n → AE F E) (j k : Fin L.n) : sb L e b (L.em j) (L.em k) = 0 := by
  have h1 : ∀ j, L.i₀ ≠ L.em j := fun j => (hne j).symm
  simp [sb, Matrix.sum_apply, Matrix.add_apply, h1]

theorem unipotent_block_corner_one (u : Fin L.n → AE F E) : uA L u L.i₀ L.i₀ = 1 := by
  simp [uA, Matrix.sum_apply, Matrix.add_apply, hne]

theorem unipotent_block_corner_embedded (u : Fin L.n → AE F E) (k : Fin L.n) : uA L u L.i₀ (L.em k) = u k := by
  have h1 : ∀ j, L.i₀ ≠ L.em j := fun j => (hne j).symm
  simp [uA, Matrix.sum_apply, Matrix.single_apply, Matrix.add_apply, h1, L.inj.eq_iff]

theorem uA_em_em (u : Fin L.n → AE F E) (j k : Fin L.n) : uA L u (L.em j) (L.em k) = if j = k then 1 else 0 := by
  have h1 : ∀ j, L.i₀ ≠ L.em j := fun j => (hne j).symm
  simp [uA, Matrix.sum_apply, Matrix.add_apply, Matrix.one_apply, h1, L.inj.eq_iff]

theorem centre_block_corner (a : AF F) : aB L δ a L.i₀ L.i₀ = a • inclR (F := F) (AF F) δ := by
  simp [aB]

theorem centre_block_corner_zero (a : AF F) (k : Fin L.n) : aB L δ a L.i₀ (L.em k) = 0 := by
  simp [aB, (hne k).symm]

end B

open B in
theorem nq_sExp (e : AE F E) (b : Fin L.n → AE F E) : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (sExp L e b) := by
  rw [sExp_eq]
  refine ⟨fun k => ?_, fun k l hl1 hl2 hk => ?_⟩
  · rcases k with k | k <;> simp [Matrix.one_apply]
  · rcases k with k | k <;> rcases l with l | l
    · simp [Matrix.one_apply]
    · have hk' : k ≠ L.i₀ := fun e => hk (by rw [e])
      have hl' : l ≠ L.i₀ := fun e => hl2 (by rw [e])
      obtain ⟨j, rfl⟩ := (L.rng k).1 hk'
      obtain ⟨j', rfl⟩ := (L.rng l).1 hl'
      simp [sb_em_em]
    · simp
    · simp [Matrix.one_apply]

open B in
theorem U_sExp {ε : ℤˣ} (hσ : ∀ a, σ (σ a) = a) (b : Fin L.n → AE F E) :
    M.U (cA σ).toRingHom (((ε : ℤ) : AE F E)) (sExp L (((ε : ℤ) : AE F E)) b) := by
  unfold M.U
  rw [sExp_eq]
  unfold kunf.jw
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp
  have hee := kfour.eps_sq (F := F) (E := E) ε
  have hcc : ∀ x, cA σ (cA σ x) = x := cA_inv' hσ
  have hce : cA σ (((ε : ℤ) : AE F E)) = ((ε : ℤ) : AE F E) := kfour.cA_int _
  ext r c
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.zero_apply, smul_eq_mul]
  by_cases hr : r = L.i₀ <;> by_cases hc : c = L.i₀
  · subst hr
    subst hc
    simp [siegel_block_corner_zero]
  · subst hr
    obtain ⟨k, rfl⟩ := (L.rng c).1 hc
    rw [siegel_block_corner_embedded, siegel_block_row_embedded]
    ring
  · subst hc
    obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    rw [siegel_block_row_embedded, siegel_block_corner_embedded, map_neg, map_mul, hce, hcc]
    linear_combination (-(b k)) * hee
  · obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨j, rfl⟩ := (L.rng c).1 hc
    simp [sb_em_em]

theorem delta_par (h : Hyp L nb uM nb' w₁ cM δ) {ε : ℤˣ} (hε : kfour.FrameEq σ d.Y d.b ε) :
    σ δ = -(((ε : ℤ) : E) * δ) := by
  have hx : inFrame d.b (cM (0, 1)) = kfour.nM (aB L δ 1) := by
    rw [cM_frame h (0, 1)]
    have h0 : uA L (0 : Fin L.n → AE F E) = 1 := by simp [uA]
    have h0' : uA L (-(0 : Fin L.n → AE F E)) = 1 := by simp [uA]
    simp only [h0, h0', Matrix.transpose_one]
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have hc : (aB L δ 1)ᵀ = -((((ε : ℤ) : AE F E)) • (aB L δ 1).map (cA σ)) := kfour.cond_of_inFrame hε _ _ hx
  have he := congrFun (congrFun hc L.i₀) L.i₀
  simp only [aB, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply_same, Matrix.neg_apply,
    Matrix.smul_apply, one_smul, smul_eq_mul, kfour.cA_inclR'] at he
  apply kfour.inclR_injective (F := F)
  rw [map_neg, map_mul, kfour.inclR_int, he, mul_neg, neg_neg, ← mul_assoc, kfour.eps_sq, one_mul]

private theorem isHecke_div_and_resEtaPow_div {M : Type} [AddCommMonoid M] (f : Fin d.n → M) :
    ∑ i, f i = f L.i₀ + ∑ k, f (L.em k) := by
  classical
  have hsplit : (Finset.univ : Finset (Fin d.n)) = insert L.i₀ (Finset.univ.map ⟨L.em, L.inj⟩) := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_map, Function.Embedding.coeFn_mk, true_and, true_iff]
    by_cases hi : i = L.i₀
    · exact Or.inl hi
    · obtain ⟨k, rfl⟩ := (L.rng i).1 hi
      exact Or.inr ⟨k, rfl⟩
  rw [hsplit, Finset.sum_insert, Finset.sum_map]
  · rfl
  · simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk, not_exists]
    exact fun k h => (L.rng (L.em k)).2 ⟨k, rfl⟩ h

open B in

theorem row_sC (h : Hyp L nb uM nb' w₁ cM δ) (e : AE F E) (b u : Fin L.n → AE F E) (a : AF F) :
    (∀ j, (sExp L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inl (L.em j)) = u j) ∧
    (∀ j, (sExp L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inr (L.em j)) = b j) ∧
    (sExp L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inr L.i₀) =
      a • inclR (F := F) (AF F) δ - ∑ j, b j * cA σ (u j) ∧
    (sExp L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) (Sum.inl L.i₀) = 1 := by
  have key : ∀ c, (sExp L e b * inFrame d.b (cM (u, a))) (Sum.inl L.i₀) c =
      inFrame d.b (cM (u, a)) (Sum.inl L.i₀) c + ∑ k, b k * inFrame d.b (cM (u, a)) (Sum.inr (L.em k)) c := by
    intro c
    have e1 : ∑ r : Fin d.n, sExp L e b (Sum.inl L.i₀) (Sum.inl r) *
        inFrame d.b (cM (u, a)) (Sum.inl r) c = inFrame d.b (cM (u, a)) (Sum.inl L.i₀) c := by
      rw [sExp_eq]
      simp [Matrix.one_apply]
    have e2 : ∑ r : Fin d.n, sExp L e b (Sum.inl L.i₀) (Sum.inr r) *
        inFrame d.b (cM (u, a)) (Sum.inr r) c = ∑ k, b k * inFrame d.b (cM (u, a)) (Sum.inr (L.em k)) c := by
      rw [isHecke_div_and_resEtaPow_div (L := L) (fun r => sExp L e b (Sum.inl L.i₀) (Sum.inr r) * inFrame d.b (cM (u, a)) (Sum.inr r) c), sExp_eq]
      simp [siegel_block_corner_zero, siegel_block_corner_embedded]
    rw [Matrix.mul_apply, Fintype.sum_sum_type, e1, e2]
  have hc : ∀ j k, cA σ (uA L (-u) (L.em j) (L.em k)) = if j = k then 1 else 0 := by
    intro j k
    rw [uA_em_em]
    split_ifs <;> simp
  refine ⟨fun j => ?_, fun j => ?_, ?_, ?_⟩
  · rw [key, cM_frame h (u, a)]
    simp [unipotent_block_corner_embedded]
  · rw [key, cM_frame h (u, a)]
    simp [centre_block_corner_zero, hc]
  · rw [key, cM_frame h (u, a)]
    simp [centre_block_corner, unipotent_block_corner_embedded, sub_eq_add_neg, Finset.sum_neg_distrib]
  · rw [key, cM_frame h (u, a)]
    simp [unipotent_block_corner_one]

namespace W

variable (L) in

def Wm (a b : AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 - Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 +
    Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) a + Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) b

theorem Wm_mul (a b a' b' : AE F E) (h1 : a * a' = 1) (h2 : b * b' = 1) : Wm L a b * Wm L b' a' = 1 := by
  ext r c
  rcases r with r | r <;> rcases c with c | c <;>
    by_cases hr : r = L.i₀ <;> by_cases hc : c = L.i₀ <;>
    simp_all [Wm, Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply, eq_comm]

theorem Wm_row_out (a b : AE F E) {k : Fin d.n} (hk : k ≠ L.i₀) (m : Fin d.n ⊕ Fin d.n) :
    Wm L a b (Sum.inr k) m = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr k) m := by
  have hk' : L.i₀ ≠ k := Ne.symm hk
  simp [Wm, hk']

theorem Wm_row_y (a b : AE F E) (m : Fin d.n ⊕ Fin d.n) :
    Wm L a b (Sum.inr L.i₀) m = if m = Sum.inl L.i₀ then b else 0 := by
  rcases m with l | l
  · by_cases hl : l = L.i₀
    · subst hl
      simp [Wm]
    · simp [Wm, Ne.symm hl, hl]
  · by_cases hl : l = L.i₀
    · subst hl
      simp [Wm]
    · simp [Wm, Ne.symm hl]

theorem Wm_col_out (a b : AE F E) {l : Fin d.n} (hl : l ≠ L.i₀) (m : Fin d.n ⊕ Fin d.n) :
    Wm L a b m (Sum.inl l) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) m (Sum.inl l) := by
  have hl' : L.i₀ ≠ l := Ne.symm hl
  simp [Wm, hl']

theorem weyl_matrix_column (a b : AE F E) (m : Fin d.n ⊕ Fin d.n) :
    Wm L a b m (Sum.inl L.i₀) = if m = Sum.inr L.i₀ then b else 0 := by
  rcases m with l | l
  · by_cases hl : l = L.i₀
    · subst hl
      simp [Wm]
    · simp [Wm, Ne.symm hl, hl]
  · by_cases hl : l = L.i₀
    · subst hl
      simp [Wm]
    · simp [Wm, Ne.symm hl, hl]

theorem mul_row_out (a b : AE F E) {k : Fin d.n} (hk : k ≠ L.i₀)
    (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (c : Fin d.n ⊕ Fin d.n) :
    (Wm L a b * M) (Sum.inr k) c = M (Sum.inr k) c := by
  rw [Matrix.mul_apply]
  simp_rw [Wm_row_out a b hk]
  rw [← Matrix.mul_apply, Matrix.one_mul]

theorem mul_row_y (a b : AE F E) (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (c : Fin d.n ⊕ Fin d.n) : (Wm L a b * M) (Sum.inr L.i₀) c = b * M (Sum.inl L.i₀) c := by
  rw [Matrix.mul_apply]
  simp_rw [Wm_row_y]
  simp [ite_mul]

theorem mul_col_out (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (a b : AE F E) {l : Fin d.n}
    (hl : l ≠ L.i₀) (r : Fin d.n ⊕ Fin d.n) : (M * Wm L a b) r (Sum.inl l) = M r (Sum.inl l) := by
  rw [Matrix.mul_apply]
  simp_rw [Wm_col_out a b hl]
  rw [← Matrix.mul_apply, Matrix.mul_one]

theorem mul_Wm_apply_inl_i0 (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (a b : AE F E)
    (r : Fin d.n ⊕ Fin d.n) : (M * Wm L a b) r (Sum.inl L.i₀) = M r (Sum.inr L.i₀) * b := by
  rw [Matrix.mul_apply]
  simp_rw [weyl_matrix_column]
  simp [mul_ite]

end W

open W in

theorem w1_conj_sExp_mem_par2 (h : Hyp L nb uM nb' w₁ cM δ) {e : AE F E} {b : Fin L.n → AE F E} {s : d.G}
    (hs : inFrame d.b s = sExp L e b) : w₁ * s * w₁⁻¹ ∈ par2 σ d.Y := by
  obtain ⟨a, b', ha, hb, hw⟩ := h.wf
  rw [PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame]
  have hW : inFrame d.b w₁ = Wm L (inclR (F := F) (AF F) a) (inclR (F := F) (AF F) b') := hw
  have hWi : inFrame d.b w₁⁻¹ = Wm L (inclR (F := F) (AF F) b'⁻¹) (inclR (F := F) (AF F) a⁻¹) := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hW]
    apply Matrix.inv_eq_right_inv
    apply Wm_mul
    · rw [← map_mul, mul_inv_cancel₀ ha, map_one]
    · rw [← map_mul, mul_inv_cancel₀ hb, map_one]
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hW, hWi, hs, Matrix.mul_assoc]
  ext k l
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  by_cases hk : k = L.i₀
  · subst hk
    rw [mul_row_y]
    by_cases hl : l = L.i₀
    · subst hl
      rw [mul_Wm_apply_inl_i0, B.sExp_eq]
      simp [B.siegel_block_corner_zero]
    · rw [mul_col_out _ _ _ hl, B.sExp_eq]
      simp [Ne.symm hl]
  · rw [mul_row_out _ _ hk]
    by_cases hl : l = L.i₀
    · subst hl
      rw [mul_Wm_apply_inl_i0, B.sExp_eq]
      simp [hk]
    · rw [mul_col_out _ _ _ hl, B.sExp_eq]
      simp

end PositivityTheory.SiegelWeilFormula.Act.C6

end
