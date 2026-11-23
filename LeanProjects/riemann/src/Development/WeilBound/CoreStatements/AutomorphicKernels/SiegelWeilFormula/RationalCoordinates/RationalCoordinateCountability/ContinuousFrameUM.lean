import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinNormSumRationalInvariant
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCj

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {R : RD d} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

variable (L) in

def kom (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (p : (Fin L.n → AE F E) × nA σ L.Y L.b) : d.G :=
  L.j (nb' p.2) * uM p.1 * (L.j (nb' p.2))⁻¹ * (uM p.1)⁻¹

variable (L) in

def tau (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (δ : E) (p : (Fin L.n → AE F E) × nA σ L.Y L.b) :
    (Fin L.n → AE F E) × AF F :=
  (fun k => inFrame d.b (kom L uM nb' p) (Sum.inl L.i₀) (Sum.inr (L.em k)),
    ellA δ (inFrame d.b (kom L uM nb' p) (Sum.inl L.i₀) (Sum.inr L.i₀)))

variable (L) in

def Du (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := (uA L (-u))ᵀ.map (cA σ)

theorem frame_uM (h : Hyp L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (uA L u) 0 0 (Du L u) := by
  obtain ⟨a', ha⟩ := h.uM u
  rw [ha, lr_of ha (uA_mul_neg L u)]
  rfl

theorem Du_mul (u : Fin L.n → AE F E) : Du (σ := σ) L u * Du L (-u) = 1 := by
  unfold Du
  rw [← Matrix.map_mul, ← Matrix.transpose_mul, neg_neg, uA_mul_neg L u]
  ext i j
  simp [Matrix.one_apply, Matrix.map_apply]

theorem uM_neg' (h : Hyp L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) : uM (-u) = (uM u)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right (KAway.inFrame_inj d ?_)
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, frame_uM h, frame_uM h, GlobalTheory.EisBL.DoubledParabolic.inFrame_one, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, uA_mul_neg, Du_mul, Matrix.fromBlocks_one]

theorem continuous_uA : Continuous (uA (σ := σ) L) := by
  unfold uA
  refine continuous_const.add (continuous_finsetSum _ fun j _ => ?_)
  have e : (fun b : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (b j)) =
      fun b => b j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext b; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]; exact (continuous_apply j).smul continuous_const

theorem continuous_frame_uM : Continuous fun u : Fin L.n → AE F E =>
    (Matrix.fromBlocks (uA L u) 0 0 (Du (σ := σ) L u) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) := by
  refine Continuous.matrix_fromBlocks continuous_uA continuous_const continuous_const ?_
  unfold Du
  exact ((continuous_uA.comp continuous_neg).matrix_transpose).matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)

theorem frame_kom (h : Hyp L nb uM nb' w₁ cM δ) (p : (Fin L.n → AE F E) × nA σ L.Y L.b) :
    inFrame d.b (kom L uM nb' p) = inFrame d.b (L.j (nb' p.2)) * Matrix.fromBlocks (uA L p.1) 0 0 (Du L p.1) *
      inFrame d.b (L.j (nb' (-p.2))) * Matrix.fromBlocks (uA L (-p.1)) 0 0 (Du L (-p.1)) := by
  unfold kom
  rw [← uM_neg' h, ← map_inv, ← kunf.nb_neg h.nb', GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul,
    GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, frame_uM h, frame_uM h]

theorem continuous_kom (h : Hyp L nb uM nb' w₁ cM δ) : Continuous fun p => inFrame d.b (kom L uM nb' p) := by
  have hj : Continuous fun β : nA σ L.Y L.b => inFrame d.b (L.j (nb' β)) :=
    (GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame d.b).comp (L.cont.comp (kunf.continuous_nb h.nb'))
  simp only [frame_kom h]
  exact (((hj.comp continuous_snd).matrix_mul (continuous_frame_uM.comp continuous_fst)).matrix_mul
    ((hj.comp continuous_neg).comp continuous_snd)).matrix_mul ((continuous_frame_uM.comp continuous_neg).comp continuous_fst)

theorem continuous_tau (h : Hyp L nb uM nb' w₁ cM δ) : Continuous (tau L uM nb' δ) := by
  have hk := continuous_kom h
  refine Continuous.prodMk (continuous_pi fun k => hk.matrix_elem _ _) ?_
  exact (IsModuleTopology.continuous_of_linearMap (R := AF F) (ellA δ)).comp (hk.matrix_elem _ _)

theorem Du_neg_row (u : Fin L.n → AE F E) (k : Fin d.n) :
    Du (σ := σ) L (-u) L.i₀ k = if k = L.i₀ then 1 else 0 := by
  unfold Du
  rw [neg_neg, Matrix.map_apply, Matrix.transpose_apply]
  by_cases hk : k = L.i₀
  · subst hk
    simp [uA, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, fun j => ComplexParameterFamilyContinuity.em_ne L j]
  · simp [uA, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, hk, Ne.symm hk]

theorem ellA_self (hδ : δ ≠ 0) : ellA (F := F) δ (inclR (F := F) (AF F) δ) = 1 := by
  have hex : ∃ ℓ : E →ₗ[F] F, δ ≠ 0 → ℓ δ = 1 := by
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual F E, φ δ ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hδ ((Module.forall_dual_apply_eq_zero_iff F δ).1 hne)
    exact ⟨(φ δ)⁻¹ • φ, fun _ => by simp [hφ]⟩
  have hℓ := Classical.epsilon_spec hex hδ
  simp [ellA, inclR, LinearMap.baseChange_tmul, Algebra.TensorProduct.rid_tmul, Algebra.algebraMap_eq_smul_one, hℓ]

theorem sM_zero' : sM R L 0 = 1 := by
  apply KAway.inFrame_inj d
  rw [inFrame_sM', GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have : sB R L 0 = 0 := by simp [sB]
  rw [this, bMat, Matrix.fromBlocks_one]

theorem cM_zero' (h : Hyp L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) : cM (u, 0) = uM u := by
  apply KAway.inFrame_inj d
  rw [inFrame_cM h, frame_uM h]
  simp [aB, Du]

theorem move (h : Hyp L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (β'' : nA σ L.Y L.b) (b : Fin L.n → AE F E) (a : AF F) :
    L.j (nb' β'') * (sM R L b * cM (u, a)) =
      sM R L (b + (tau L uM nb' δ (u, β'')).1) * cM (u, a + (tau L uM nb' δ (u, β'')).2) * L.j (nb' β'') := by
  obtain ⟨B, A, hBA⟩ := j_move (R := R) h u β''
  suffices hτ : tau L uM nb' δ (u, β'') = (B, A) by rw [hτ]; exact hBA b a
  have e0 := hBA 0 0
  rw [sM_zero', one_mul, cM_zero' h, zero_add, zero_add] at e0
  have hk : kom L uM nb' (u, β'') = sM R L B * cM (u, A) * (uM u)⁻¹ := by
    show L.j (nb' β'') * uM u * (L.j (nb' β''))⁻¹ * (uM u)⁻¹ = _
    rw [e0, mul_inv_cancel_right]
  have hf : inFrame d.b (kom L uM nb' (u, β'')) =
      Matrix.fromBlocks 1 (aB L δ A * Du L (-u) + sB R L B) 0 1 := by
    rw [hk, ← uM_neg' h, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inFrame_sM', inFrame_cM h, frame_uM h, bMat]
    rw [show (uA L (-u))ᵀ.map (cA σ) = Du L u from rfl]
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul,
      Matrix.mul_one, uA_mul_neg, Du_mul]
    rw [Matrix.add_mul, Matrix.mul_assoc, Du_mul, Matrix.mul_one]
  have hrow : ∀ k, (aB L δ A * Du (σ := σ) L (-u)) L.i₀ k = if k = L.i₀ then A • inclR (F := F) (AF F) δ else 0 := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single L.i₀]
    · rw [Du_neg_row]; simp [aB]
    · intro m _ hm; simp [aB, Matrix.single_apply, Ne.symm hm]
    · simp
  refine Prod.ext (funext fun k => ?_) ?_
  · show inFrame d.b (kom L uM nb' (u, β'')) (Sum.inl L.i₀) (Sum.inr (L.em k)) = B k
    rw [hf, Matrix.fromBlocks_apply₁₂, Matrix.add_apply, hrow, if_neg (ComplexParameterFamilyContinuity.em_ne L k), zero_add, sB_i0em]
  · show ellA δ (inFrame d.b (kom L uM nb' (u, β'')) (Sum.inl L.i₀) (Sum.inr L.i₀)) = A
    rw [hf, Matrix.fromBlocks_apply₁₂, Matrix.add_apply, hrow, if_pos rfl, sB_i0i0, add_zero, map_smul, ellA_self h.δ0,
      smul_eq_mul, mul_one]

end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK

end
