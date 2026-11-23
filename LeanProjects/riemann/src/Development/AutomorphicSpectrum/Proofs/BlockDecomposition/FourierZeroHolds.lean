import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalAdelicMatricesSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousTraceMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionIsotropicRestrictionNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

namespace GlobalTheory.CompanionTheory.FourierN

variable {D : D7} {n : ℕ}

def hermSub (D : D7) (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) D.host.E) where
  carrier := {b | (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.map_add _ (map_add _), Matrix.transpose_add, ha, hb]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.map_neg _ (map_neg _), Matrix.transpose_neg, ha]

def pr (a : Matrix (Fin n) (Fin n) D.host.E) (x : Mx D n n) : AF D.host.F :=
  halfTr (Matrix.trace (HMul.hMul (a.map (incA D)) x : Mx D n n))

theorem halfTr_add (z w : AE D) : halfTr (z + w) = halfTr z + halfTr w := by
  simp only [halfTr, map_add, mul_add]

theorem halfTr_zero : halfTr (0 : AE D) = 0 := by
  simp only [halfTr, map_zero, mul_zero]

theorem pr_add_right (a : Matrix (Fin n) (Fin n) D.host.E) (x y : Mx D n n) :
    pr a (x + y) = pr a x + pr a y := by
  simp only [pr, ← halfTr_add, ← Matrix.trace_add]
  congr 2
  exact Matrix.mul_add _ _ _

theorem pr_add_left (a b : Matrix (Fin n) (Fin n) D.host.E) (x : Mx D n n) :
    pr (a + b) x = pr a x + pr b x := by
  simp only [pr, ← halfTr_add, ← Matrix.trace_add]
  congr 2
  rw [Matrix.map_add _ (map_add _)]
  exact Matrix.add_mul _ _ _

theorem pr_zero_left (x : Mx D n n) : pr (0 : Matrix (Fin n) (Fin n) D.host.E) x = 0 := by
  have h := pr_add_left (0 : Matrix (Fin n) (Fin n) D.host.E) 0 x
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem continuous_halfTr : Continuous (halfTr : AE D → AF D.host.F) := by
  have h : Continuous fun z : AE D => Algebra.trace (AF D.host.F) (AE D) z := by
    simpa using GlobalTheory.Core.Rk.SplitPsi.continuous_trace_mul D 1
  exact continuous_const.mul h

theorem continuous_pr (a : Matrix (Fin n) (Fin n) D.host.E) : Continuous (pr a : Mx D n n → AF D.host.F) :=
  continuous_halfTr.comp (Continuous.matrix_trace (continuous_const.matrix_mul continuous_id))

theorem trA_cA (z : AE D) : trA (cA D z) = trA z := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have hb : Function.Bijective (D.sp.cm.sig : D.host.E →ₐ[D.host.F] D.host.E) :=
    Algebra.IsAlgebraic.algHom_bijective _
  have ht : ∀ e : D.host.E, Algebra.trace D.host.F D.host.E (D.sp.cm.sig e) = Algebra.trace D.host.F D.host.E e :=
    fun e => Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective _ hb) e
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    show Algebra.trace (AF D.host.F) (AE D) (a ⊗ₜ[D.host.F] (D.sp.cm.sig e)) = Algebra.trace (AF D.host.F) (AE D) (a ⊗ₜ[D.host.F] e)
    rw [GlobalTheory.LatVac.trace_tmul, GlobalTheory.LatVac.trace_tmul, ht]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem halfTr_add_cA (z : AE D) : halfTr (z + cA D z) = trA z := by
  simp only [halfTr, map_add, trA_cA]
  rw [← two_mul, ← mul_assoc, ← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
  norm_num

theorem trace_adj (M : Mx D n n) : Matrix.trace (adj M) = cA D (Matrix.trace M) := by
  rw [adj, Matrix.trace_transpose]
  exact (AddMonoidHom.map_trace (cA D).toAddMonoidHom M).symm

theorem pr_sym (γ : Matrix (Fin n) (Fin n) D.host.E) {x : Mx D n n} (hx : adj x = x) :
    pr (γ + γᴴ) x = trA (Matrix.trace (HMul.hMul (rat γ) x : Mx D n n)) := by
  have e1 : Matrix.trace (HMul.hMul (adj (rat γ)) x : Mx D n n) =
      cA D (Matrix.trace (HMul.hMul (rat γ) x : Mx D n n)) := by
    rw [← trace_adj, adj_mul, hx]
    exact Matrix.trace_mul_comm _ _
  have e2 : (γ + γᴴ).map (incA D) = rat γ + adj (rat γ) := by
    rw [Matrix.map_add _ (map_add _)]
    exact congrArg (rat γ + ·) (rat_conjTranspose γ)
  rw [pr, e2, show HMul.hMul (rat γ + adj (rat γ)) x = (HMul.hMul (rat γ) x + HMul.hMul (adj (rat γ)) x : Mx D n n) from Matrix.add_mul _ _ _,
    Matrix.trace_add, e1, halfTr_add_cA]

theorem mem_hermSub_sym (γ : Matrix (Fin n) (Fin n) D.host.E) : γ + γᴴ ∈ hermSub D n := by
  show ((γ + γᴴ).map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = γ + γᴴ
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.conjTranspose_apply, map_add]
  have hs : ∀ e : D.host.E, D.sp.cm.sig e = star e := fun e => rfl
  simp only [hs, star_add, star_star]
  rw [add_comm]

theorem rat_ker {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (x : hermA D n)
    (h : ∀ a ∈ hermSub D n, ψ (-pr a x.1) = 1) : x ∈ ratHerm D n := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have hx : adj x.1 = x.1 := x.2
  have key : ∀ i j (e : D.host.E), ψ (Algebra.trace (AF D.host.F) (AE D) (incA D e * x.1 i j)) = 1 := by
    intro i j e
    have h1 := h _ (mem_hermSub_sym (Matrix.single j i e))
    rw [pr_sym _ hx, GlobalTheory.GramAnnih.rat_single] at h1
    have h2 : Matrix.trace (HMul.hMul (Matrix.single j i (incA D e)) x.1 : Mx D n n) = incA D e * x.1 i j := by
      rw [show (HMul.hMul (Matrix.single j i (incA D e)) x.1 : Mx D n n) = Matrix.single j i (incA D e) * x.1 from rfl,
        Matrix.trace_single_mul, smul_eq_mul]
    rw [h2] at h1
    have h3 := AddChar.map_neg_eq_inv ψ (trA (incA D e * x.1 i j))
    rw [h1] at h3
    exact inv_eq_one.1 h3.symm
  have hent : ∀ i j, ∃ e : D.host.E, x.1 i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := fun i j =>
    GlobalTheory.RatAnnih.tensor_rat (x.1 i j) fun e =>
      (GlobalTheory.SWQ.Annihilator.self_annihilator D.host.F inferInstance ψ hψ).2 _ fun c =>
        (congrArg ψ (GlobalTheory.RatAnnih.trace_mul_algebraMap (x.1 i j) e c)).trans (key i j (c • e))
  choose M hM using hent
  exact ⟨Matrix.of M, Matrix.ext fun i j => (hM i j).symm⟩

theorem ker_of_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (x : hermA D n)
    (hx : x ∈ ratHerm D n) (a : Matrix (Fin n) (Fin n) D.host.E) : ψ (-pr a x.1) = 1 := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  obtain ⟨η, hη⟩ := hx
  have hη' : x.1 = rat η := hη.symm
  have e : Matrix.trace (rat (D := D) (a * η)) = (1 : AF D.host.F) ⊗ₜ[D.host.F] Matrix.trace (a * η) :=
    (AddMonoidHom.map_trace (incA D) _).symm
  have e2 : -pr a x.1 = algebraMap D.host.F (AF D.host.F)
      (-((1 / 2) * Algebra.trace D.host.F D.host.E (Matrix.trace (a * η)))) := by
    rw [pr, hη', show (HMul.hMul (a.map (incA D)) (rat η) : Mx D n n) = rat (a * η) from (rat_mul a η).symm, e,
      halfTr, trA, GlobalTheory.LatVac.trace_tmul, one_mul, map_neg, map_mul]
  rw [e2]
  exact hψ.2.2.1 _

theorem continuous_adj' : Continuous (adj : Mx D n n → Mx D n n) :=
  (continuous_id.matrix_map GlobalTheory.AnnihBox.continuous_cA').matrix_transpose

theorem isClosed_hermA : IsClosed ((hermA D n : AddSubgroup (Mx D n n)) : Set (Mx D n n)) := by
  obtain ⟨-, -, -, i4, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  exact isClosed_eq continuous_adj' continuous_id

def sym (y : Mx D n n) : Mx D n n := incA D 2⁻¹ • (y + adj y)

theorem cA_half : cA D (incA D (2⁻¹ : D.host.E)) = incA D 2⁻¹ := by
  show incA D (D.sp.cm.sig 2⁻¹) = _
  rw [map_inv₀, map_ofNat]

theorem adj_smul' (c : AE D) (M : Mx D n n) : adj (c • M) = cA D c • adj M := by
  ext i j
  simp [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem adj_sym (y : Mx D n n) : adj (sym y) = sym y := by
  rw [sym, adj_smul', cA_half, adj_add, adj_adj, add_comm]

theorem sym_add (x y : Mx D n n) : sym (x + y) = sym x + sym y := by
  simp only [sym, adj_add]
  rw [← smul_add, add_add_add_comm]

theorem sym_herm {x : Mx D n n} (hx : adj x = x) : sym x = x := by
  have e : incA D (2⁻¹ : D.host.E) + incA D 2⁻¹ = 1 := by
    rw [← map_add, show (2⁻¹ : D.host.E) + 2⁻¹ = 1 by norm_num, map_one]
  rw [sym, hx, smul_add, ← add_smul, e, one_smul]

theorem sym_rat (η : Matrix (Fin n) (Fin n) D.host.E) : sym (rat η) ∈ ratMx D n n := by
  refine ⟨(2⁻¹ : D.host.E) • (η + ηᴴ), ?_⟩
  show rat ((2⁻¹ : D.host.E) • (η + ηᴴ)) = sym (rat η)
  rw [sym, ← rat_conjTranspose]
  ext i j
  simp [rat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  exact (mul_add _ _ _).symm

theorem continuous_sym : Continuous (sym : Mx D n n → Mx D n n) := by
  show Continuous fun y : Mx D n n => (incA D 2⁻¹ : AE D) • (y + adj y)
  exact (continuous_const : Continuous fun _ : Mx D n n => (incA D 2⁻¹ : AE D)).smul
    (continuous_id.add (continuous_adj' (D := D) (n := n)))

theorem exists_compact_cover : ∃ K : Set (hermA D n), IsCompact K ∧ ∀ x, ∃ γ ∈ ratHerm D n, γ + x ∈ K := by
  obtain ⟨-, -, -, -, -, K₀, hK₀, hcov⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  refine ⟨Subtype.val ⁻¹' (sym '' K₀),
    (isClosed_hermA (D := D) (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage (hK₀.image continuous_sym), fun x => ?_⟩
  obtain ⟨γ, ⟨η, hη⟩, hk⟩ := hcov x.1
  have hη' : γ = rat η := hη.symm
  refine ⟨⟨sym γ, adj_sym γ⟩, ?_, γ + x.1, hk, ?_⟩
  · show sym γ ∈ ratMx D n n
    rw [hη']
    exact sym_rat η
  · rw [sym_add, sym_herm (x := x.1) x.2]
    rfl

theorem discrete_ratHerm : DiscreteTopology (ratHerm D n) := by
  obtain ⟨-, -, -, -, i5, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  let φ : ratHerm D n → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D n n := fun a => ⟨a.1.1, a.2⟩
  have hc : Continuous φ := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective φ := fun a b h => by
    have e : a.1.1 = b.1.1 := Subtype.mk.inj h
    exact Subtype.ext (Subtype.ext e)
  exact DiscreteTopology.of_continuous_injective hc hi

theorem mat_injective : Function.Injective (mat : G D n → Mx D (n + n) (n + n)) :=
  fun _ _ h => matHom_injective _ _ _ (Units.ext h)

theorem nb_add {nb : hermA D n → G D n} (h : IsNMap nb) (a b : hermA D n) : nb (a + b) = nb a * nb b := by
  apply mat_injective
  show mat (nb (a + b)) = mat (nb a) * mat (nb b)
  rw [h, h, h, submatrix_fromBlocks_mul]
  simp [add_comm]

theorem nb_zero {nb : hermA D n → G D n} (h : IsNMap nb) : nb 0 = 1 := by
  apply mat_injective
  show mat (nb 0) = 1
  rw [h]
  exact block_matrix_one

theorem continuous_block_matrix : Continuous fun b : hermA D n => (blk4 1 b.1 0 1 : Mx D (n + n) (n + n)) :=
  (Continuous.matrix_fromBlocks continuous_const continuous_subtype_val continuous_const continuous_const).matrix_submatrix _ _

theorem continuous_nb {nb : hermA D n → G D n} (h : IsNMap nb) : Continuous nb := by
  rw [(isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous_iff, Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have e : (Units.val ∘ (matHom (AF D.host.F) D.sp.cm.sig (Jst D n)) ∘ nb) = fun b : hermA D n => (blk4 1 b.1 0 1 : Mx D (n + n) (n + n)) :=
      funext fun b => h b
    rw [e]
    exact continuous_block_matrix
  · have hinv : ∀ b, (nb b)⁻¹ = nb (-b) := fun b => by
      rw [inv_eq_iff_mul_eq_one, ← nb_add h, add_neg_cancel, nb_zero h]
    have e : (fun b : hermA D n => (((matHom (AF D.host.F) D.sp.cm.sig (Jst D n) ∘ nb) b)⁻¹ : GL _ _).1) =
        fun b : hermA D n => (blk4 1 (-b.1) 0 1 : Mx D (n + n) (n + n)) := funext fun b => by
      rw [Function.comp_apply, ← map_inv, hinv]
      exact h (-b)
    rw [e]
    exact (Continuous.matrix_fromBlocks continuous_const continuous_subtype_val.neg continuous_const
      continuous_const).matrix_submatrix _ _

theorem blk4_map_alt {R S : Type} (f : R → S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  ext i j
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem nb_rat {nb : hermA D n → G D n} (h : IsNMap nb) (γ : hermA D n) (hγ : γ ∈ ratHerm D n) : nb γ ∈ GF D n := by
  obtain ⟨η, hη⟩ := hγ
  have hη' : rat η = γ.1 := hη
  let x : GL (Fin (n + n)) D.host.E := ⟨blk4 1 η 0 1, blk4 1 (-η) 0 1,
    by simp [submatrix_fromBlocks_mul, block_matrix_one], by simp [submatrix_fromBlocks_mul, block_matrix_one]⟩
  have hm : x.1.map (incA D) = blk4 1 γ.1 0 1 := by
    simp only [x, blk4_map_alt]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)]
    congr 1
  refine ⟨x, ?_, Units.ext (hm.trans (h γ).symm)⟩
  apply rat_injective (D := D)
  have h2 : adj (mat (nb γ)) * JR (AF D.host.F) (Jst D n) * mat (nb γ) = JR (AF D.host.F) (Jst D n) := (nb γ).2
  rw [h γ, ← hm] at h2
  erw [rat_mul, rat_mul]
  exact h2

set_option synthInstance.maxHeartbeats 400000 in

theorem fourierZero : PositivityTheory.PfSWUS.FourierZero := by
  intro D n ψ hψ nb lam 𝓖 hC f hf hinv hco
  obtain ⟨hnb, hlam, hFD, -⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (hermA D n) := isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : DiscreteTopology (ratHerm D n) := discrete_ratHerm
  obtain ⟨K, hK, hcov⟩ := exists_compact_cover (D := D) (n := n)
  funext g
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (hermA D n) (ratHerm D n) K hK hcov
    (hermSub D n) (fun a x => ψ (-pr a.1 x.1))
    (fun a => hψ.1.comp ((continuous_pr a.1).neg.comp continuous_subtype_val))
    (fun a x y => by
      show ψ (-pr a.1 (x.1 + y.1)) = _
      rw [pr_add_right, neg_add, AddChar.map_add_eq_mul])
    (fun a b x => by
      show ψ (-pr (a.1 + b.1) x.1) = _
      rw [pr_add_left, neg_add, AddChar.map_add_eq_mul])
    (fun x => by
      show ψ (-pr 0 x.1) = 1
      rw [pr_zero_left, neg_zero, AddChar.map_zero_eq_one])
    (fun a x => hψ.2.1 _)
    (fun x => ⟨fun h => rat_ker hψ x (fun a ha => h ⟨a, ha⟩), fun hx a => ker_of_rat hψ x hx a.1⟩)
    lam 𝓖 hlam hFD (fun b => f (nb b * g))
    (hf.comp ((continuous_nb hnb).mul continuous_const))
    (fun γ hγ x => by
      show f (nb (γ + x) * g) = f (nb x * g)
      rw [nb_add hnb, mul_assoc]
      exact hinv _ (nb_rat hnb γ hγ) _)
    (fun a => (integral_congr_ae (.of_forall fun x => mul_comm _ _)).trans (hco ⟨a.1, a.2⟩ g))
  have h0 := congrFun key 0
  simpa [nb_zero hnb] using h0

end GlobalTheory.CompanionTheory.FourierN
