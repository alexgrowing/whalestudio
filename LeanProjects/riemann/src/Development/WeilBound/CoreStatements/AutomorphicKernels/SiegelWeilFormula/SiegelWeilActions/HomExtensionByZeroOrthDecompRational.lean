import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ProjectedBlockUpperSum

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5.JC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ}

abbrev Mt (d : SD σ) : Type := Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)

def ext0 (L : LD d) (x : Fin L.n → AE F E) (i : Fin d.n) : AE F E :=
  ∑ k, (if L.em k = i then (1 : AE F E) else 0) * x k

theorem extend_zero_embedding (L : LD d) (x : Fin L.n → AE F E) (k : Fin L.n) : ext0 L x (L.em k) = x k := by
  simp [ext0, L.inj.eq_iff]

theorem extend_zero_last_column (L : LD d) (x : Fin L.n → AE F E) : ext0 L x L.i₀ = 0 := by
  simp [ext0, ComplexParameterFamilyContinuity.em_ne]

def vV (L : LD d) (u b : Fin L.n → AE F E) : Fin d.n ⊕ Fin d.n → AE F E := Sum.elim (ext0 L u) (ext0 L b)

def IsPad (L : LD d) (M : Mt d) : Prop :=
  ∀ u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)), ∀ v, M u v = (1 : Mt d) u v ∧ M v u = (1 : Mt d) v u

theorem isPad_j (L : LD d) (g : G2 σ L.Y) : IsPad L (inFrame d.b (L.j g)) := L.j_out g

variable {L : LD d}

theorem pad_col {M : Mt d} (hM : IsPad L M) : M *ᵥ Pi.single (Sum.inl L.i₀) 1 = Pi.single (Sum.inl L.i₀) 1 := by
  funext r
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [(hM _ (by simp) r).2]
  simp [Matrix.one_apply]

theorem pad_row {M : Mt d} (hM : IsPad L M) : Pi.single (Sum.inr L.i₀) 1 ᵥ* M = Pi.single (Sum.inr L.i₀) 1 := by
  funext r
  simp only [Matrix.vecMul, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [(hM _ (by simp) r).1]
  simp [Matrix.one_apply, eq_comm]

theorem pad_vecMul_inl {M : Mt d} (hM : IsPad L M) (x : Fin d.n ⊕ Fin d.n → AE F E) :
    (x ᵥ* M) (Sum.inl L.i₀) = x (Sum.inl L.i₀) := by
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_congr rfl fun r _ => by rw [(hM _ (by simp) r).2]]
  simp [Matrix.one_apply]

theorem pad_vecMul_inr {M : Mt d} (hM : IsPad L M) (x : Fin d.n ⊕ Fin d.n → AE F E) :
    (x ᵥ* M) (Sum.inr L.i₀) = x (Sum.inr L.i₀) := by
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_congr rfl fun r _ => by rw [(hM _ (by simp) r).2]]
  simp [Matrix.one_apply]

theorem pad_single_vecMul {M : Mt d} (hM : IsPad L M) (a : AE F E) :
    Pi.single (Sum.inr L.i₀) a ᵥ* M = Pi.single (Sum.inr L.i₀) a := by
  rw [Matrix.single_vecMul]
  funext r
  simp only [Pi.smul_apply, Matrix.row_apply, smul_eq_mul]
  rw [(hM _ (by simp) r).1]
  by_cases h : r = Sum.inr L.i₀
  · subst h; simp [Matrix.one_apply]
  · simp [Matrix.one_apply, h, Pi.single_apply, Ne.symm h]

def hN (L : LD d) (vf wf : Fin d.n ⊕ Fin d.n → AE F E) : Mt d :=
  1 + Matrix.vecMulVec (Pi.single (Sum.inl L.i₀) 1) vf + Matrix.vecMulVec wf (Pi.single (Sum.inr L.i₀) 1)

theorem conj_hN {J K : Mt d} (hKJ : K * J = 1) (hJ : IsPad L J) (vf wf : Fin d.n ⊕ Fin d.n → AE F E) :
    J * hN L vf wf = hN L (vf ᵥ* K) (J *ᵥ wf) * J := by
  simp only [hN, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, pad_col hJ, pad_row hJ, Matrix.vecMul_vecMul, hKJ, Matrix.vecMul_one]

def W (R : RD d) : Mt d := kunf.jw d.n (((R.ε : ℤ) : AE F E))

def cv (σ : E →ₐ[F] E) {ι : Type} (x : ι → AE F E) : ι → AE F E := fun r => cA σ (x r)

theorem e_mul_e (R : RD d) : (((R.ε : ℤ) : AE F E)) * ((R.ε : ℤ) : AE F E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

theorem W_transpose (R : RD d) : (W R)ᵀ = (((R.ε : ℤ) : AE F E)) • W R := by
  have he := e_mul_e R
  ext (i | i) (j | j) <;> simp [W, kunf.jw, Matrix.one_apply] <;> split_ifs <;> simp_all [eq_comm]

theorem W_mul_alt (R : RD d) : W R * W R = (((R.ε : ℤ) : AE F E)) • (1 : Mt d) := by
  simp only [W, kunf.jw, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    zero_add, add_zero]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]

theorem W_mulVec_inl (R : RD d) (y : Fin d.n ⊕ Fin d.n → AE F E) (i : Fin d.n) :
    (W R *ᵥ y) (Sum.inl i) = y (Sum.inr i) := by
  simp [W, kunf.jw, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

theorem W_mulVec_inr (R : RD d) (y : Fin d.n ⊕ Fin d.n → AE F E) (i : Fin d.n) :
    (W R *ᵥ y) (Sum.inr i) = ((R.ε : ℤ) : AE F E) * y (Sum.inl i) := by
  simp [W, kunf.jw, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

theorem JW {R : RD d} {J K : Mt d} (hKJ : K * J = 1) (hK : Kᵀ * W R * K.map (cA σ) = W R) :
    J * W R = W R * (K.map (cA σ))ᵀ := by
  have he : ((R.ε : ℤ) : AE F E) * ((R.ε : ℤ) : AE F E) = 1 := e_mul_e R
  have hJt : Jᵀ * Kᵀ = 1 := by rw [← Matrix.transpose_mul, hKJ, Matrix.transpose_one]
  have h1 : W R * K.map (cA σ) = Jᵀ * W R := by
    calc W R * K.map (cA σ) = (Jᵀ * Kᵀ) * W R * K.map (cA σ) := by rw [hJt, Matrix.one_mul]
      _ = Jᵀ * (Kᵀ * W R * K.map (cA σ)) := by simp only [Matrix.mul_assoc]
      _ = Jᵀ * W R := by rw [hK]
  have h2 : (K.map (cA σ))ᵀ * W R = W R * J := by
    have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, W_transpose, Matrix.mul_smul,
      Matrix.smul_mul] at h3
    have h4 := congrArg (fun M : Mt d => ((R.ε : ℤ) : AE F E) • M) h3
    simpa only [smul_smul, he, one_smul] using h4
  have hWW := W_mul_alt R
  calc J * W R = ((R.ε : ℤ) : AE F E) • (((R.ε : ℤ) : AE F E) • (J * W R)) := by rw [smul_smul, he, one_smul]
    _ = ((R.ε : ℤ) : AE F E) • ((W R * W R) * J * W R) := by rw [hWW, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
    _ = ((R.ε : ℤ) : AE F E) • (W R * ((K.map (cA σ))ᵀ * W R) * W R) := by rw [h2]; simp only [Matrix.mul_assoc]
    _ = ((R.ε : ℤ) : AE F E) • (W R * (K.map (cA σ))ᵀ * (W R * W R)) := by simp only [Matrix.mul_assoc]
    _ = W R * (K.map (cA σ))ᵀ := by rw [hWW, Matrix.mul_smul, Matrix.mul_one, smul_smul, he, one_smul]

theorem cv_vecMul (x : Fin d.n ⊕ Fin d.n → AE F E) (K : Mt d) : cv σ (x ᵥ* K) = (K.map (cA σ))ᵀ *ᵥ cv σ x := by
  funext s
  simp [cv, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, mul_comm]

def qf (R : RD d) (x : Fin d.n ⊕ Fin d.n → AE F E) : AE F E := x ⬝ᵥ (W R *ᵥ cv σ x)

theorem qf_vecMul {R : RD d} {K : Mt d} (hKW : K * W R * (K.map (cA σ))ᵀ = W R) (x : Fin d.n ⊕ Fin d.n → AE F E) :
    qf R (x ᵥ* K) = qf R x := by
  unfold qf
  rw [cv_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hKW]

def hh (L : LD d) (u b : Fin L.n → AE F E) : AE F E := ∑ j, b j * cA σ (u j)

def wf (R : RD d) (L : LD d) (u b : Fin L.n → AE F E) : Fin d.n ⊕ Fin d.n → AE F E :=
  -(((R.ε : ℤ) : AE F E)) • (W R *ᵥ cv σ (vV L u b))

theorem jeA_eq (R : RD d) : eA R = ((R.ε : ℤ) : AE F E) := by
  simp [eA]

theorem uA_apply (u : Fin L.n → AE F E) (i k : Fin d.n) :
    uA L u i k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k + if i = L.i₀ then ext0 L u k else 0 := by
  by_cases hi : i = L.i₀
  · subst hi
    simp [uA, ext0, Matrix.sum_apply, Matrix.single_apply]
  · simp [uA, Matrix.sum_apply, Matrix.single_apply, Ne.symm hi, hi]

theorem D_apply (u : Fin L.n → AE F E) (l k : Fin d.n) :
    ((uA L (-u))ᵀ.map (cA σ)) l k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) l k +
      if k = L.i₀ then -cA σ (ext0 L u l) else 0 := by
  rw [Matrix.map_apply, Matrix.transpose_apply, uA_apply]
  by_cases hk : k = L.i₀
  · subst hk
    simp [ext0, Matrix.one_apply, eq_comm, map_sum, Finset.sum_neg_distrib]
  · simp [Matrix.one_apply, hk, eq_comm]

theorem sB_apply (R : RD d) (b : Fin L.n → AE F E) (i l : Fin d.n) :
    sB R L b i l = (if i = L.i₀ then ext0 L b l else 0) +
      if l = L.i₀ then -(((R.ε : ℤ) : AE F E) * cA σ (ext0 L b i)) else 0 := by
  unfold sB
  simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Finset.sum_add_distrib, jeA_eq]
  rcases idx L i with rfl | ⟨p, rfl⟩ <;> rcases idx L l with rfl | ⟨q, rfl⟩ <;>
    simp [ext0, ComplexParameterFamilyContinuity.em_ne, (ComplexParameterFamilyContinuity.em_ne L _).symm, L.inj.eq_iff, map_sum, apply_ite, eq_comm]

theorem aB_apply (δ : E) (a : AF F) (i k : Fin d.n) :
    aB L δ a i k = if i = L.i₀ ∧ k = L.i₀ then a • inclR (F := F) (AF F) δ else 0 := by
  simp [aB, Matrix.single_apply, eq_comm]

variable {R : RD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem frameN (h : Hyp L nb uM nb' w₁ cM δ) (u b : Fin L.n → AE F E) (a : AF F) :
    inFrame d.b (sM R L b * cM (u, a)) =
      hN L (vV L u b + Pi.single (Sum.inr L.i₀) (a • inclR (F := F) (AF F) δ - hh L u b)) (wf R L u b) := by
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inFrame_sM', inFrame_cM h, bMat, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add]
  ext (i | i) (k | k)
  all_goals simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, hN, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.one_apply, Pi.add_apply, vV, wf,
    Pi.smul_apply, smul_eq_mul, W_mulVec_inl, W_mulVec_inr, cv, Sum.elim_inl, Sum.elim_inr]
  · rw [uA_apply]
    by_cases hi : i = L.i₀ <;> simp [hi, Pi.single_apply, Matrix.one_apply]
  · rw [aB_apply, Matrix.mul_apply, sum_split L]
    simp only [D_apply]
    rcases idx L i with rfl | ⟨p, rfl⟩ <;> rcases idx L k with rfl | ⟨q, rfl⟩ <;>
      simp [sB_apply, D_apply, extend_zero_embedding, extend_zero_last_column, ComplexParameterFamilyContinuity.em_ne, (ComplexParameterFamilyContinuity.em_ne L _).symm, Pi.single_apply, Matrix.one_apply,
        L.inj.eq_iff, hh, Finset.sum_neg_distrib, sub_eq_add_neg]
  · simp [Pi.single_apply]
  · rw [D_apply]
    have he := e_mul_e R
    by_cases hk : k = L.i₀ <;> simp [hk, Pi.single_apply, Matrix.one_apply, ← mul_assoc, he]

def cmp (L : LD d) (M : Mt d) (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) :
    (Fin L.n → AE F E) × (Fin L.n → AE F E) :=
  (fun k => (vV L p.2 p.1 ᵥ* M) (Sum.inr (L.em k)), fun k => (vV L p.2 p.1 ᵥ* M) (Sum.inl (L.em k)))

theorem vV_cmp {M : Mt d} (hM : IsPad L M) (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) :
    vV L p.2 p.1 ᵥ* M = vV L (cmp L M p).2 (cmp L M p).1 := by
  funext r
  rcases r with i | i <;> rcases idx L i with rfl | ⟨k, rfl⟩
  · rw [pad_vecMul_inl hM]; simp [vV, extend_zero_last_column]
  · simp only [vV, cmp, Sum.elim_inl, extend_zero_embedding]
  · rw [pad_vecMul_inr hM]; simp [vV, extend_zero_last_column]
  · simp only [vV, cmp, Sum.elim_inr, extend_zero_embedding]

theorem cmp_cmp {J K : Mt d} (hK : IsPad L K) (hKJ : K * J = 1) (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) :
    cmp L J (cmp L K p) = p := by
  have e := vV_cmp hK p
  have e2 : cmp L J (cmp L K p) = (fun k => (vV L (cmp L K p).2 (cmp L K p).1 ᵥ* J) (Sum.inr (L.em k)),
      fun k => (vV L (cmp L K p).2 (cmp L K p).1 ᵥ* J) (Sum.inl (L.em k))) := rfl
  rw [e2, ← e, Matrix.vecMul_vecMul, hKJ, Matrix.vecMul_one]
  ext k <;> simp [vV, extend_zero_embedding]

theorem matrixExtendByZero_add (L : LD d) (x y : Fin L.n → AE F E) : ext0 L (x + y) = ext0 L x + ext0 L y := by
  funext i
  simp [ext0, mul_add, Finset.sum_add_distrib]

theorem vV_add (u b u' b' : Fin L.n → AE F E) : vV L (u + u') (b + b') = vV L u b + vV L u' b' := by
  funext r
  rcases r with i | i <;> simp [vV, matrixExtendByZero_add]

theorem cmp_add (L : LD d) (M : Mt d) (p q : (Fin L.n → AE F E) × (Fin L.n → AE F E)) :
    cmp L M (p + q) = cmp L M p + cmp L M q := by
  ext k <;> simp [cmp, vV_add, Matrix.add_vecMul]

theorem continuous_wittExtendByZero (L : LD d) (i : Fin d.n) : Continuous fun x : Fin L.n → AE F E => ext0 L x i := by
  unfold ext0
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k)

theorem continuous_vV (L : LD d) (r : Fin d.n ⊕ Fin d.n) :
    Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => vV L p.2 p.1 r := by
  rcases r with i | i
  · exact (continuous_wittExtendByZero L i).comp continuous_snd
  · exact (continuous_wittExtendByZero L i).comp continuous_fst

theorem continuous_vVM (L : LD d) (M : Mt d) (s : Fin d.n ⊕ Fin d.n) :
    Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => (vV L p.2 p.1 ᵥ* M) s := by
  simp only [Matrix.vecMul, dotProduct]
  exact continuous_finsetSum _ fun r _ => (continuous_vV L r).mul continuous_const

theorem continuous_cmp (L : LD d) (M : Mt d) : Continuous (cmp L M) :=
  (continuous_pi fun _ => continuous_vVM L M _).prodMk (continuous_pi fun _ => continuous_vVM L M _)

def cmpEquiv (L : LD d) {J K : Mt d} (hJ : IsPad L J) (hK : IsPad L K) (hKJ : K * J = 1) (hJK : J * K = 1) :
    ((Fin L.n → AE F E) × (Fin L.n → AE F E)) ≃ₜ+ ((Fin L.n → AE F E) × (Fin L.n → AE F E)) where
  toFun := cmp L K
  invFun := cmp L J
  left_inv p := cmp_cmp hK hKJ p
  right_inv p := cmp_cmp hJ hJK p
  map_add' p q := cmp_add L K p q
  continuous_toFun := continuous_cmp L K
  continuous_invFun := continuous_cmp L J

theorem Kmul (L : LD d) (γ' : G2 σ L.Y) : inFrame d.b (L.j γ')⁻¹ * inFrame d.b (L.j γ') = 1 := by
  rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]

theorem Jmul (L : LD d) (γ' : G2 σ L.Y) : inFrame d.b (L.j γ') * inFrame d.b (L.j γ')⁻¹ = 1 := by
  rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]

theorem isPad_inv (L : LD d) (γ' : G2 σ L.Y) : IsPad L (inFrame d.b (L.j γ')⁻¹) := by
  rw [← map_inv]; exact isPad_j L _

theorem K_law (R : RD d) (L : LD d) (γ' : G2 σ L.Y) :
    (inFrame d.b (L.j γ')⁻¹)ᵀ * W R * (inFrame d.b (L.j γ')⁻¹).map (cA σ) = W R :=
  kunf.frame_eq R.hε _

theorem KWK (R : RD d) (L : LD d) (γ' : G2 σ L.Y) :
    inFrame d.b (L.j γ')⁻¹ * W R * ((inFrame d.b (L.j γ')⁻¹).map (cA σ))ᵀ = W R := by
  rw [Matrix.mul_assoc, ← JW (Kmul L γ') (K_law R L γ'), ← Matrix.mul_assoc, Kmul, Matrix.one_mul]

theorem qf_vV (R : RD d) (u b : Fin L.n → AE F E) :
    qf R (vV L u b) = cA σ (hh L u b) + ((R.ε : ℤ) : AE F E) * hh L u b := by
  simp only [qf, dotProduct, Fintype.sum_sum_type, W_mulVec_inl, W_mulVec_inr, cv, vV, Sum.elim_inl, Sum.elim_inr]
  rw [sum_split L, sum_split L]
  simp only [extend_zero_last_column, extend_zero_embedding, map_zero, zero_mul, mul_zero, zero_add, hh, map_sum, map_mul, cc d, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

def QQ (L : LD d) (δ : E) (M : Mt d) (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) : AF F :=
  ellA δ (hh L (cmp L M p).2 (cmp L M p).1 - hh L p.2 p.1)

theorem continuous_hh (L : LD d) :
    Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => hh L p.2 p.1 := by
  unfold hh
  exact continuous_finsetSum _ fun j _ => ((continuous_apply j).comp continuous_fst).mul
    ((GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ).comp ((continuous_apply j).comp continuous_snd))

theorem continuous_QQ (L : LD d) (δ : E) (M : Mt d) : Continuous (QQ L δ M) := by
  have hl : Continuous (ellA (F := F) δ) := IsModuleTopology.continuous_of_linearMap _
  have h1 : Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => hh L (cmp L M p).2 (cmp L M p).1 :=
    (continuous_hh L).comp (continuous_cmp L M)
  exact hl.comp (h1.sub (continuous_hh L))

theorem conj_eq (h : Hyp L nb uM nb' w₁ cM δ) (γ' : G2 σ L.Y) (b u : Fin L.n → AE F E) (a : AF F) :
    L.j γ' * (sM R L b * cM (u, a)) =
      sM R L (cmp L (inFrame d.b (L.j γ')⁻¹) (b, u)).1 *
        cM ((cmp L (inFrame d.b (L.j γ')⁻¹) (b, u)).2, a + QQ L δ (inFrame d.b (L.j γ')⁻¹) (b, u)) * L.j γ' := by
  have hK : IsPad L (inFrame d.b (L.j γ')⁻¹) := isPad_inv L γ'
  have hJ : IsPad L (inFrame d.b (L.j γ')) := isPad_j L γ'
  have hKJ := Kmul L γ'
  have eV : vV L u b ᵥ* inFrame d.b (L.j γ')⁻¹ =
      vV L (cmp L (inFrame d.b (L.j γ')⁻¹) (b, u)).2 (cmp L (inFrame d.b (L.j γ')⁻¹) (b, u)).1 := vV_cmp hK (b, u)
  have hq : qf R (vV L (cmp L (inFrame d.b (L.j γ')⁻¹) (b, u)).2 (cmp L (inFrame d.b (L.j γ')⁻¹) (b, u)).1) =
      qf R (vV L u b) := by
    rw [← eV]; exact qf_vecMul (KWK R L γ') _
  rw [qf_vV, qf_vV] at hq
  have hy : cA σ (hh L (cmp L (inFrame d.b (L.j γ')⁻¹) (b, u)).2 (cmp L (inFrame d.b (L.j γ')⁻¹) (b, u)).1 - hh L u b) =
      -(((R.ε : ℤ) : AE F E)) *
        (hh L (cmp L (inFrame d.b (L.j γ')⁻¹) (b, u)).2 (cmp L (inFrame d.b (L.j γ')⁻¹) (b, u)).1 - hh L u b) := by
    rw [map_sub]; linear_combination hq
  have hQ := eig h _ hy
  apply kunf.inFrame_injective d.b
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul d.b (L.j γ') (sM R L b * cM (u, a)), GlobalTheory.EisBL.DoubledParabolic.inFrame_mul d.b _ (L.j γ'),
    frameN h, frameN h, conj_hN hKJ hJ]
  congr 2
  · rw [Matrix.add_vecMul, eV, pad_single_vecMul hK]
    congr 2
    rw [QQ, add_smul, hQ]
    ring
  · simp only [wf, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    rw [JW hKJ (K_law R L γ'), ← Matrix.mulVec_mulVec, ← cv_vecMul, eV]

theorem mem_ratV_iff (L : LD d) (x : Fin L.n → AE F E) :
    x ∈ L.ratV ↔ ∀ k, x k ∈ (inclR (F := F) (E := E) (AF F)).range := by
  constructor
  · intro hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy => obtain ⟨z, rfl⟩ := hy; exact fun k => ⟨z k, rfl⟩
    | zero => exact fun k => zero_mem _
    | add y z _ _ hy hz => exact fun k => add_mem (hy k) (hz k)
    | neg y _ hy => exact fun k => neg_mem (hy k)
  · intro hx
    refine AddSubgroup.subset_closure ⟨fun k => (RingHom.mem_range.1 (hx k)).choose, funext fun k => ?_⟩
    exact (RingHom.mem_range.1 (hx k)).choose_spec

theorem inFrame_rat_mem {n : ℕ} {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) {x : G2 σ Y} (hx : x ∈ rat2 σ Y)
    (i j : Fin n ⊕ Fin n) : inFrame b x i j ∈ (inclR (F := F) (E := E) (AF F)).range := by
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hx)
  have hm : mat2 x = (g.1).map (inclR (F := F) (AF F)) := by
    show (x : GL (Fin n ⊕ Fin n) (AE F E)).1 = _
    rw [← hg]; rfl
  have e : inFrame b x = ((b⁻¹).1 * g.1 * b.1).map (inclR (F := F) (AF F)) := by
    rw [inFrame, hm, Matrix.map_mul, Matrix.map_mul]; rfl
  rw [e, Matrix.map_apply]
  exact ⟨_, rfl⟩

theorem idx2 (L : LD d) (r : Fin d.n ⊕ Fin d.n) :
    r = Sum.inl L.i₀ ∨ r = Sum.inr L.i₀ ∨ ∃ p, r = Sum.map L.em L.em p := by
  rcases r with i | i <;> rcases idx L i with rfl | ⟨p, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨Sum.inl p, rfl⟩)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨Sum.inr p, rfl⟩)

theorem j_em (L : LD d) (g : G2 σ L.Y) (p q : Fin L.n ⊕ Fin L.n) :
    inFrame d.b (L.j g) (Sum.map L.em L.em p) (Sum.map L.em L.em q) = inFrame L.b g p q := by
  have := congrFun (congrFun (L.j_in g) p) q
  simpa [Matrix.submatrix_apply] using this

theorem j_entries_rat (L : LD d) {g : G2 σ L.Y} (hg : g ∈ rat2 σ L.Y) (r s : Fin d.n ⊕ Fin d.n) :
    inFrame d.b (L.j g) r s ∈ (inclR (F := F) (E := E) (AF F)).range := by
  have hP := isPad_j L g
  have hone : ∀ r s, (1 : Mt d) r s ∈ (inclR (F := F) (E := E) (AF F)).range := fun r s => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rcases idx2 L r with rfl | rfl | ⟨p, rfl⟩
  · rw [(hP _ (by simp) s).1]; exact hone _ _
  · rw [(hP _ (by simp) s).1]; exact hone _ _
  · rcases idx2 L s with rfl | rfl | ⟨q, rfl⟩
    · rw [(hP _ (by simp) _).2]; exact hone _ _
    · rw [(hP _ (by simp) _).2]; exact hone _ _
    · rw [j_em]; exact inFrame_rat_mem L.b hg p q

theorem homExtensionByZeroOrthDecomp_rational (L : LD d) {x : Fin L.n → AE F E} (hx : ∀ k, x k ∈ (inclR (F := F) (E := E) (AF F)).range)
    (i : Fin d.n) : ext0 L x i ∈ (inclR (F := F) (E := E) (AF F)).range := by
  unfold ext0
  refine Subring.sum_mem _ fun k _ => Subring.mul_mem _ ?_ (hx k)
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem cmp_rat {M : Mt d} (hM : ∀ r s, M r s ∈ (inclR (F := F) (E := E) (AF F)).range)
    {p : (Fin L.n → AE F E) × (Fin L.n → AE F E)} (hp1 : ∀ k, p.1 k ∈ (inclR (F := F) (E := E) (AF F)).range)
    (hp2 : ∀ k, p.2 k ∈ (inclR (F := F) (E := E) (AF F)).range) :
    (∀ k, (cmp L M p).1 k ∈ (inclR (F := F) (E := E) (AF F)).range) ∧
      ∀ k, (cmp L M p).2 k ∈ (inclR (F := F) (E := E) (AF F)).range := by
  have hv : ∀ r, vV L p.2 p.1 r ∈ (inclR (F := F) (E := E) (AF F)).range := by
    rintro (i | i)
    · exact homExtensionByZeroOrthDecomp_rational L hp2 i
    · exact homExtensionByZeroOrthDecomp_rational L hp1 i
  have hs : ∀ s, (vV L p.2 p.1 ᵥ* M) s ∈ (inclR (F := F) (E := E) (AF F)).range := fun s => by
    simp only [Matrix.vecMul, dotProduct]
    exact Subring.sum_mem _ fun r _ => Subring.mul_mem _ (hv r) (hM r s)
  exact ⟨fun k => hs _, fun k => hs _⟩

theorem cmpEquiv_apply (L : LD d) {J K : Mt d} (hJ : IsPad L J) (hK : IsPad L K) (hKJ : K * J = 1) (hJK : J * K = 1)
    (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) : cmpEquiv L hJ hK hKJ hJK p = cmp L K p := rfl

theorem vV_vecMul_apply (M : Mt d) (u b : Fin L.n → AE F E) (s : Fin d.n ⊕ Fin d.n) :
    (vV L u b ᵥ* M) s = ∑ k, u k * M (Sum.inl (L.em k)) s + ∑ k, b k * M (Sum.inr (L.em k)) s := by
  simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, vV, Sum.elim_inl, Sum.elim_inr]
  rw [sum_split L, sum_split L]
  simp [extend_zero_last_column, extend_zero_embedding]

end PositivityTheory.SiegelWeilFormula.Act.C5.JC

namespace PositivityTheory.SiegelWeilFormula.Act.C5

open JC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem j_conj' (h : Hyp L nb uM nb' w₁ cM δ) (γ' : G2 σ L.Y) :
    ∃ (Λ : ((Fin L.n → AE F E) × (Fin L.n → AE F E)) ≃ₜ+ ((Fin L.n → AE F E) × (Fin L.n → AE F E)))
      (Q : (Fin L.n → AE F E) × (Fin L.n → AE F E) → AF F), Continuous Q ∧
      (∀ b u a, L.j γ' * (sM R L b * cM (u, a)) = sM R L (Λ (b, u)).1 * cM ((Λ (b, u)).2, a + Q (b, u)) * L.j γ') ∧
      (γ' ∈ rat2 σ L.Y → ∀ w, w ∈ (L.ratV.prod L.ratV : AddSubgroup _) ↔ Λ w ∈ (L.ratV.prod L.ratV : AddSubgroup _)) := by
  refine ⟨cmpEquiv L (isPad_j L γ') (isPad_inv L γ') (Kmul L γ') (Jmul L γ'), QQ L δ (inFrame d.b (L.j γ')⁻¹),
    continuous_QQ L δ _, fun b u a => conj_eq h γ' b u a, fun hr w => ?_⟩
  have hK : ∀ r s, inFrame d.b (L.j γ')⁻¹ r s ∈ (inclR (F := F) (E := E) (AF F)).range := fun r s => by
    have := j_entries_rat L (inv_mem hr) r s
    rwa [map_inv] at this
  have hJ : ∀ r s, inFrame d.b (L.j γ') r s ∈ (inclR (F := F) (E := E) (AF F)).range := j_entries_rat L hr
  rw [cmpEquiv_apply, AddSubgroup.mem_prod, AddSubgroup.mem_prod, mem_ratV_iff, mem_ratV_iff, mem_ratV_iff,
    mem_ratV_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact cmp_rat hK h1 h2
  · rintro ⟨h1, h2⟩
    have := cmp_rat hJ h1 h2
    rwa [cmp_cmp (isPad_inv L γ') (Kmul L γ')] at this

theorem j_move' (h : Hyp L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (β'' : nA σ L.Y L.b) :
    ∃ (B : Fin L.n → AE F E) (A : AF F), ∀ b a, L.j (nb' β'') * (sM R L b * cM (u, a)) =
      sM R L (b + B) * cM (u, a + A) * L.j (nb' β'') := by
  have hK : inFrame d.b (L.j (nb' β''))⁻¹ = inFrame d.b (L.j (nb' (-β''))) := by
    rw [kunf.nb_neg h.nb' β'', map_inv]
  have hfr : inFrame L.b (nb' (-β'')) = Matrix.fromBlocks 1 (-β''.1) 0 1 := by
    rw [h.nb' (-β'')]; rfl
  have k11 : ∀ p q, inFrame d.b (L.j (nb' β''))⁻¹ (Sum.inl (L.em p)) (Sum.inl (L.em q)) =
      (1 : Matrix (Fin L.n) (Fin L.n) (AE F E)) p q := fun p q => by
    have := j_em L (nb' (-β'')) (Sum.inl p) (Sum.inl q)
    rw [hfr] at this
    rw [hK]; simpa using this
  have k21 : ∀ p q, inFrame d.b (L.j (nb' β''))⁻¹ (Sum.inr (L.em p)) (Sum.inl (L.em q)) = 0 := fun p q => by
    have := j_em L (nb' (-β'')) (Sum.inr p) (Sum.inl q)
    rw [hfr] at this
    rw [hK]; simpa using this
  have k12 : ∀ p q, inFrame d.b (L.j (nb' β''))⁻¹ (Sum.inl (L.em p)) (Sum.inr (L.em q)) = -β''.1 p q := fun p q => by
    have := j_em L (nb' (-β'')) (Sum.inl p) (Sum.inr q)
    rw [hfr] at this
    rw [hK]; simpa using this
  have k22 : ∀ p q, inFrame d.b (L.j (nb' β''))⁻¹ (Sum.inr (L.em p)) (Sum.inr (L.em q)) =
      (1 : Matrix (Fin L.n) (Fin L.n) (AE F E)) p q := fun p q => by
    have := j_em L (nb' (-β'')) (Sum.inr p) (Sum.inr q)
    rw [hfr] at this
    rw [hK]; simpa using this
  set B : Fin L.n → AE F E := fun k => -∑ k', u k' * β''.1 k' k with hB
  have hc : ∀ b, cmp L (inFrame d.b (L.j (nb' β''))⁻¹) (b, u) = (b + B, u) := fun b => by
    ext k
    · show (vV L u b ᵥ* _) (Sum.inr (L.em k)) = b k + B k
      rw [vV_vecMul_apply]
      simp only [k12, k22, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, hB, mul_neg, Finset.sum_neg_distrib]
      ring
    · show (vV L u b ᵥ* _) (Sum.inl (L.em k)) = u k
      rw [vV_vecMul_apply]
      simp only [k11, k21, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, Finset.sum_const_zero, add_zero]
  refine ⟨B, ellA δ (hh L u B), fun b a => ?_⟩
  have e := conj_eq (R := R) h (nb' β'') b u a
  have hQ : QQ L δ (inFrame d.b (L.j (nb' β''))⁻¹) (b, u) = ellA δ (hh L u B) := by
    rw [QQ, hc]
    congr 1
    simp only [hh, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  rw [hc, hQ] at e
  exact e

end PositivityTheory.SiegelWeilFormula.Act.C5

end
