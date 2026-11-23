import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinRationalInvariantReindex
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BMatK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTerm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BlockDiagonalPreservesFormIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PhzEqFlatK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentNilpotentMulEqZero

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
variable {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem first_orbit_mul_fixed {γ r : d.G}
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (γ * r) ↔ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ := by
  have e : ∀ i, inFrame d.b (γ * r) (Sum.inr i) (Sum.inl L.i₀) = inFrame d.b γ (Sum.inr i) (Sum.inl L.i₀) := by
    intro i
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
    simp only [hx, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit, e]
theorem first_orbit_parabolic_invariant {p g : d.G} (hp : p ∈ par2 σ d.Y) : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (p * g) ↔ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L g := by
  have h21 : ∀ {q : d.G}, q ∈ par2 σ d.Y → ∀ i j, inFrame d.b q (Sum.inr i) (Sum.inl j) = 0 := by
    intro q hq i j
    have := (kunf.mem_stabiliser_iff_frame_lower_block d.ok.frame q).1 hq
    have := congrFun (congrFun this i) j
    simpa [Matrix.toBlocks₂₁] using this
  have key : ∀ {q γ : d.G}, q ∈ par2 σ d.Y → _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ → _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (q * γ) := by
    intro q γ hq hγ i
    have hγ' : ∀ k, inFrame d.b γ (Sum.inr k) (Sum.inl L.i₀) = 0 := hγ
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [h21 hq, hγ']
  refine ⟨fun h => ?_, key hp⟩
  have := key (inv_mem hp) h
  rwa [inv_mul_cancel_left] at this
theorem eisenstein_second_term_reindex {M : Type} [AddCommMonoid M] [TopologicalSpace M] (H : ℂ → M) {s₁ : ℂ} {f : d.G → ℂ}
    (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, H (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (r * g))) =
      ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, H (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * g)) := by
  classical
  let γr : rat2 σ d.Y := ⟨r, hr⟩
  let e0 := GlobalTheory.Eis.rmulEquiv (par2 σ d.Y) (rat2 σ d.Y) γr
  have hrep : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 q) = p * (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q * r) := by
    intro q
    have h1 : e0 q = GlobalTheory.AutomorphicL2Unitary.mk _ (Quotient.out q * γr) := by
      show GlobalTheory.AutomorphicL2Unitary.rmul _ γr q = _
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    have h2 : GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) (Quotient.out q * γr) =
        GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) (Quotient.out (e0 q)) := by
      rw [← h1]; exact (Quotient.out_eq _).symm
    obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h2
    refine ⟨((γ : rat2 σ d.Y) : d.G), Subgroup.mem_subgroupOf.1 γ.2, (γ : rat2 σ d.Y).2, ?_⟩
    have := congrArg Subtype.val hγ
    show ((Quotient.out (e0 q) : rat2 σ d.Y) : d.G) = _
    rw [← this]
    rfl
  have hS : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) ↔ ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 q)) := by
    intro q
    obtain ⟨p, hp, -, he⟩ := hrep q
    rw [he, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.first_orbit_parabolic_invariant hp, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.first_orbit_mul_fixed hx]
  let e : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)} ≃ {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)} := e0.subtypeEquiv hS
  have hterm : ∀ q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)},
      _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (r * g)) = _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q).1 * g) := by
    intro q
    obtain ⟨p, hp, hpr, he⟩ := hrep q.1
    show _ = _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 q.1) * g)
    rw [he, mul_assoc, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_rat_k hf z hp hpr]
  rw [tsum_congr fun q => congrArg H (hterm q)]
  exact e.tsum_eq (fun q => H (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * g)))
theorem eisenstein_term_right_invariant {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) (r * g) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) g :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_second_term_reindex id hf z hr hx g
theorem eisenstein_norm_sum_invariant_right {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (r * g))‖ₑ =
      ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * g)‖ₑ :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_second_term_reindex (fun w => ‖w‖ₑ) hf z hr hx g
def eO_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Matrix (Fin d.n) (Fin d.n) (AE F E) := Matrix.single L.i₀ L.i₀ 1
theorem em_ne'_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (j : Fin L.n) : L.i₀ ≠ L.em j := (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j).symm
theorem eO_mul_eO_k : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k]
theorem eO_single_k (x : AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L * Matrix.single L.i₀ L.i₀ x = Matrix.single L.i₀ L.i₀ x := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k]
theorem single_eO_k (x : AE F E) : Matrix.single L.i₀ L.i₀ x * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L = Matrix.single L.i₀ L.i₀ x := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k]
theorem wf_blocks_k (α β : AE F E) :
    (1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 - Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 +
      Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) α + Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) β :
        Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      Matrix.fromBlocks (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L) (Matrix.single L.i₀ L.i₀ α) (Matrix.single L.i₀ L.i₀ β) (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L) := by
  ext (i | i) (j | j) <;> simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k, Matrix.single, Matrix.one_apply]
theorem wf_mul_k (α β α' β' : AE F E) (ha : α * α' = 1) (hb : β * β' = 1) :
    Matrix.fromBlocks (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L) (Matrix.single L.i₀ L.i₀ α) (Matrix.single L.i₀ L.i₀ β) (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L) *
      Matrix.fromBlocks (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L) (Matrix.single L.i₀ L.i₀ β') (Matrix.single L.i₀ L.i₀ α') (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L) = 1 := by
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  have h1 : (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L) * (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L) = 1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L := by
    rw [mul_sub, sub_mul, sub_mul, one_mul, mul_one, one_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_mul_eO_k]; abel
  congr 1
  · rw [h1, Matrix.single_mul_single_same, ha, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k]; abel
  · simp only [mul_sub, sub_mul, one_mul, mul_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_single_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.single_eO_k]; abel
  · simp only [mul_sub, sub_mul, one_mul, mul_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_single_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.single_eO_k]; abel
  · rw [h1, Matrix.single_mul_single_same, hb, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k]; abel
theorem det_one_add_col_k (N : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hN : ∀ i j, j ≠ L.i₀ → N i j = 0)
    (h0 : N L.i₀ L.i₀ = 0) : (1 + N).det = 1 := by
  have e : N = Matrix.replicateCol Unit (fun i => N i L.i₀) * Matrix.replicateRow Unit (Pi.single L.i₀ (1 : AE F E)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Finset.univ_unique,
      Finset.sum_singleton]
    by_cases hj : j = L.i₀
    · subst hj; simp
    · rw [hN i j hj]; simp [hj]
  rw [e, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [h0]
theorem section_unipotent_invariant_weyl (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    (b : Fin L.n → AE F E) (g : d.G) : _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * g)) = _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * g) := by
  classical
  obtain ⟨a₁, b₁, ha₁, hb₁, hW⟩ := h.wf
  set α : AE F E := inclR (F := F) (AF F) a₁
  set β : AE F E := inclR (F := F) (AF F) b₁
  set α' : AE F E := inclR (F := F) (AF F) a₁⁻¹
  set β' : AE F E := inclR (F := F) (AF F) b₁⁻¹
  have hα : α * α' = 1 := by rw [← map_mul, mul_inv_cancel₀ ha₁, map_one]
  have hβ : β * β' = 1 := by rw [← map_mul, mul_inv_cancel₀ hb₁, map_one]
  set W := Matrix.fromBlocks (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L) (Matrix.single L.i₀ L.i₀ α) (Matrix.single L.i₀ L.i₀ β) (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L)
  set W' := Matrix.fromBlocks (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L) (Matrix.single L.i₀ L.i₀ β') (Matrix.single L.i₀ L.i₀ α') (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L)
  have hW1 : inFrame d.b w₁ = W := by rw [hW, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.wf_blocks_k]
  have hWW : W * W' = 1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.wf_mul_k α β α' β' hα hβ
  have hWi : inFrame d.b w₁⁻¹ = W' := by
    have h1 : inFrame d.b w₁⁻¹ * W = 1 := by rw [← hW1, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
    calc inFrame d.b w₁⁻¹ = inFrame d.b w₁⁻¹ * (W * W') := by rw [hWW, Matrix.mul_one]
      _ = W' := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  set S := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b
  set p : d.G := w₁ * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * w₁⁻¹
  have hP : inFrame d.b p = W * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k S * W' := by
    simp only [p, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hW1, hWi, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k]
    rfl
  have hS0 : S L.i₀ L.i₀ = 0 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0i0_k b
  have h1e : (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L) * (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L) = 1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L := by
    rw [mul_sub, sub_mul, sub_mul, one_mul, mul_one, one_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_mul_eO_k]; abel
  have h21 : (inFrame d.b p).toBlocks₂₁ = 0 := by
    rw [hP]
    simp only [W, W', _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁, Matrix.mul_one, Matrix.mul_zero,
      add_zero]
    rw [add_mul, Matrix.single_mul_mul_single, hS0, mul_sub, mul_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.single_eO_k, sub_mul, one_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_single_k]
    simp
  set N := (1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k L) * S * Matrix.single L.i₀ L.i₀ α'
  have h11 : (inFrame d.b p).toBlocks₁₁ = 1 + N := by
    rw [hP]
    simp only [W, W', _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, Matrix.mul_one, Matrix.mul_zero,
      add_zero]
    rw [h1e, add_mul, Matrix.single_mul_single_same, hα, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k]
    simp only [N]; abel
  have hN : ∀ i j, j ≠ L.i₀ → N i j = 0 := fun i j hj => by
    simp only [N]; exact Matrix.mul_single_apply_of_ne _ _ _ _ _ hj _
  have hN0 : N L.i₀ L.i₀ = 0 := by
    simp only [N, Matrix.mul_single_apply_same, sub_mul, one_mul, Matrix.sub_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eO_k, Matrix.single_mul_apply_same,
      one_mul, sub_self]
  have hp : p ∈ par2 σ d.Y := (kunf.mem_stabiliser_iff_frame_lower_block d.ok.frame p).2 h21
  obtain ⟨t, ht⟩ := GlobalTheory.ThK.Dbl.mem_parabolic_GL2_iff.1 hp
  obtain ⟨-, t₀, ht₀⟩ := d.ok.frame
  have htv := ((kunf.isPar_frame ht₀ p t).1 ht).2
  have hdet : Matrix.GeneralLinearGroup.det t = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, htv, Matrix.det_mul, Matrix.det_mul, h11, det_one_add_col_k N hN hN0,
      mul_one, Units.val_one, ← Matrix.det_mul, kunf.incM_GL_mul_inv, Matrix.det_one]
  have hg : w₁ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * g) = p * (w₁ * g) := by simp only [p]; group
  rw [hg, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_par_k hf z ht hdet]
theorem ratV_incl_k {v : Fin L.n → AE F E} (hv : v ∈ L.ratV) :
    ∃ x : Fin L.n → E, v = fun i => inclR (F := F) (AF F) (x i) := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv => obtain ⟨x, hx⟩ := hv; exact ⟨x, by rw [← hx]; rfl⟩
  | zero => exact ⟨0, by ext i; simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨x, rfl⟩ := hv; obtain ⟨x', rfl⟩ := hw; exact ⟨x + x', by ext i; simp⟩
  | neg v _ hv => obtain ⟨x, rfl⟩ := hv; exact ⟨-x, by ext i; simp⟩
theorem hz_uA_i0i0_k (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u L.i₀ L.i₀ = 1 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.sum_apply, Matrix.single, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L]
theorem hz_uA_i0em_k (u : Fin L.n → AE F E) (l : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u L.i₀ (L.em l) = u l := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.sum_apply, Matrix.single, Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.em_ne'_k L, L.inj.eq_iff]
theorem unipotent_block_entry_zero (u : Fin L.n → AE F E) (k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u (L.em k) L.i₀ = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.sum_apply, Matrix.single, Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.em_ne'_k L]
theorem hz_uA_emem_k (u : Fin L.n → AE F E) (k l : Fin L.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u (L.em k) (L.em l) = if k = l then 1 else 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.sum_apply, Matrix.single, Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.em_ne'_k L, L.inj.eq_iff]
def Dm_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u))ᵀ.map (cA σ)
theorem hz_D_i0i0_k (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Dm_k L u L.i₀ L.i₀ = 1 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Dm_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.hz_uA_i0i0_k]
theorem hz_D_i0em_k (u : Fin L.n → AE F E) (l : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Dm_k L u L.i₀ (L.em l) = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Dm_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.unipotent_block_entry_zero]
theorem derivation_block_entry (u : Fin L.n → AE F E) (k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Dm_k L u (L.em k) L.i₀ = -cA σ (u k) := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Dm_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.hz_uA_i0em_k]
theorem hz_D_emem_k (u : Fin L.n → AE F E) (k l : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Dm_k L u (L.em k) (L.em l) = if k = l then 1 else 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Dm_k, Matrix.map_apply, Matrix.transpose_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.hz_uA_emem_k]
  by_cases hkl : k = l
  · subst hkl; simp
  · simp [hkl, Ne.symm hkl]
theorem hz_aB_i0i0_k (x : AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ x L.i₀ L.i₀ = x • inclR (F := F) (AF F) δ := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single]
theorem hz_aB_i0em_k (x : AF F) (l : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ x L.i₀ (L.em l) = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.em_ne'_k L]
theorem centre_block_entry_zero (x : AF F) (k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ x (L.em k) L.i₀ = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.em_ne'_k L]
theorem hz_aB_emem_k (x : AF F) (k l : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ x (L.em k) (L.em l) = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.em_ne'_k L]
theorem hz_uA_add_k (u v : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L v = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (u + v) := by
  have e := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotent_nilpotent_mul_eq_zero L u v
  change (1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u) * (1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L v) = 1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L (u + v)
  rw [mul_add, add_mul, add_mul, one_mul, one_mul, mul_one, e, add_zero]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart, Pi.add_apply, Matrix.single_add, Finset.sum_add_distrib]
  abel
theorem heis'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) :
    ∃ Z : (Fin L.n → AE F E) → (Fin L.n → AE F E) → AF F, Continuous (Function.uncurry Z) ∧
      (∀ u₀ b, u₀ ∈ L.ratV → b ∈ L.ratV → Z u₀ b ∈ (algebraMap F (AF F)).range) ∧
      ∀ u₀ a₀ b u a, cM (u₀, a₀) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u₀ + u, a₀ + a + Z u₀ b) := by
  classical
  let y : (Fin L.n → AE F E) → (Fin L.n → AE F E) → AE F E := fun u₀ b =>
    ∑ l, b l * cA σ (u₀ l) - ∑ k, u₀ k * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R * cA σ (b k))
  refine ⟨fun u₀ b => ellA δ (y u₀ b), ?_, ?_, ?_⟩
  · have hl : Continuous (ellA (F := F) (E := E) δ) := IsModuleTopology.continuous_of_linearMap _
    have hc := GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ
    show Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => ellA δ (y p.1 p.2)
    refine hl.comp ((continuous_finset_sum _ fun l _ => ?_).sub (continuous_finset_sum _ fun k _ => ?_))
    · exact ((continuous_apply l).comp continuous_snd).mul (hc.comp ((continuous_apply l).comp continuous_fst))
    · exact ((continuous_apply k).comp continuous_fst).mul
        (continuous_const.mul (hc.comp ((continuous_apply k).comp continuous_snd)))
  · intro u₀ b hu hb
    obtain ⟨x0, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.ratV_incl_k hu
    obtain ⟨xb, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.ratV_incl_k hb
    have e : y (fun i => inclR (F := F) (AF F) (x0 i)) (fun i => inclR (F := F) (AF F) (xb i)) =
        inclR (F := F) (AF F) (∑ l, xb l * σ (x0 l) - ∑ k, x0 k * (((R.ε : ℤ) : E) * σ (xb k))) := by
      simp only [y, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k, map_sub, map_sum, map_mul, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR]
    show ellA δ (y _ _) ∈ _
    rw [e]
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C5.ellA_inclR_k h _
  · intro u₀ a₀ b u a
    have hC : ∀ c, inFrame d.b (cM c) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2) 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Dm_k L c.1) := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h
    have hM := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k (R := R) (L := L) b
    apply _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eq_of_upper_k
    · rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hC, hC, hM]
      simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, Matrix.fromBlocks_multiply]
    · rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hC, hM]
      simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, Matrix.fromBlocks_multiply]
    · rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hC, hC, hC, hM]
      simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      exact _root_.PositivityTheory.SiegelWeilFormula.Act.C5.hz_uA_add_k u₀ u
    · rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hC, hC, hC, hM]
      simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      have hZ : ellA δ (y u₀ b) • inclR (F := F) (AF F) δ = y u₀ b := by
        refine _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eig_k (R := R) h _ ?_
        have he := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eps_mul_k R
        simp only [y, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_eq_k, map_sub, map_sum, map_mul, map_intCast, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cc_k d, mul_sub, Finset.mul_sum]
        simp only [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        linear_combination (-(u₀ l * cA σ (b l))) * he
      ext i j
      rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L i with rfl | ⟨k, rfl⟩ <;> rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L j with rfl | ⟨l, rfl⟩ <;>
        simp only [Matrix.add_apply, Matrix.mul_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sum_split_k L, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.hz_uA_i0i0_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.hz_uA_i0em_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.unipotent_block_entry_zero, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.hz_uA_emem_k,
          _root_.PositivityTheory.SiegelWeilFormula.Act.C5.hz_D_i0i0_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.hz_D_i0em_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.derivation_block_entry, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.hz_D_emem_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.hz_aB_i0i0_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.hz_aB_i0em_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.centre_block_entry_zero, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.hz_aB_emem_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0i0_k,
          _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0em_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.section_entry_embedded_row, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_emem_k, Pi.add_apply, map_add, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add,
          mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
      rw [add_smul, add_smul, hZ]
      simp only [y, mul_neg, mul_add, neg_add, Finset.sum_neg_distrib, Finset.sum_add_distrib]
      ring
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
