import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.FockOrbit

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.PointAtPlaceHom

section General

variable {G σ : Type} [TopologicalSpace G]

def CoefCont (F : G → MvPolynomial σ ℂ) : Prop := ∀ m, Continuous fun k => MvPolynomial.coeff m (F k)

theorem CoefCont.const (P : MvPolynomial σ ℂ) : CoefCont fun _ : G => P := fun _ => continuous_const

theorem CoefCont.add {F F' : G → MvPolynomial σ ℂ} (h : CoefCont F) (h' : CoefCont F') :
    CoefCont fun k => F k + F' k := fun m => by
  simp only [MvPolynomial.coeff_add]
  exact (h m).add (h' m)

theorem CoefCont.mul {F F' : G → MvPolynomial σ ℂ} (h : CoefCont F) (h' : CoefCont F') :
    CoefCont fun k => F k * F' k := fun m => by
  simp only [MvPolynomial.coeff_mul]
  exact continuous_finset_sum _ fun p _ => (h _).mul (h' _)

theorem CoefCont.smul {s : G → ℂ} {F : G → MvPolynomial σ ℂ} (hs : Continuous s) (h : CoefCont F) :
    CoefCont fun k => s k • F k := fun m => by
  simp only [MvPolynomial.coeff_smul, smul_eq_mul]
  exact hs.mul (h m)

theorem CoefCont.sum {ι : Type} [Fintype ι] {F : ι → G → MvPolynomial σ ℂ} (h : ∀ i, CoefCont (F i)) :
    CoefCont fun k => ∑ i, F i k := fun m => by
  simp only [MvPolynomial.coeff_sum]
  exact continuous_finset_sum _ fun i _ => h i m

theorem CoefCont.aeval {τ : Type} {g : G → τ → MvPolynomial σ ℂ} (h : ∀ v, CoefCont fun k => g k v)
    (P : MvPolynomial τ ℂ) : CoefCont fun k => MvPolynomial.aeval (g k) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using CoefCont.const _
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (h v)

theorem exists_monomials [Finite σ] (N : ℕ) : ∃ (n : ℕ) (e : Fin n → σ →₀ ℕ), ∀ P : MvPolynomial σ ℂ,
    P.totalDegree ≤ N → P = ∑ i, MvPolynomial.coeff (e i) P • MvPolynomial.monomial (e i) (1 : ℂ) := by
  let T := (Finsupp.finite_of_degree_le (σ := σ) N).toFinset
  refine ⟨T.card, fun i => (T.equivFin.symm i : σ →₀ ℕ), fun P hP => ?_⟩
  rw [T.equivFin.symm.sum_comp (fun d : T => MvPolynomial.coeff (d : σ →₀ ℕ) P •
    MvPolynomial.monomial (d : σ →₀ ℕ) (1 : ℂ)),
    Finset.sum_coe_sort T fun d => MvPolynomial.coeff d P • MvPolynomial.monomial d (1 : ℂ)]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [P.as_sum]
  refine Finset.sum_subset (fun d hd => ?_) fun d _ hd => ?_
  · simp only [T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact (MvPolynomial.le_totalDegree hd).trans hP
  · rw [MvPolynomial.notMem_support_iff.1 hd, map_zero]

theorem exists_coefFam [Group G] [Finite σ] (ρ : G → Module.End ℂ (MvPolynomial σ ℂ))
    (hm : ∀ a b P, ρ (a * b) P = ρ a (ρ b P)) (hd : ∀ a P, (ρ a P).totalDegree ≤ P.totalDegree)
    (hc : ∀ P, CoefCont fun k => ρ k P) (φ : MvPolynomial σ ℂ) :
    ∃ (n : ℕ) (φs : Fin n → MvPolynomial σ ℂ) (c : Fin n → G → ℂ), IsCoefFam c ∧ ∀ k, ρ k φ = ∑ i, c i k • φs i := by
  obtain ⟨n, e, he⟩ := exists_monomials (σ := σ) φ.totalDegree
  refine ⟨n, fun i => MvPolynomial.monomial (e i) 1, fun i k => MvPolynomial.coeff (e i) (ρ k φ),
    ⟨fun i => hc φ _, fun k₀ i => ⟨fun j => MvPolynomial.coeff (e i) (ρ k₀ (MvPolynomial.monomial (e j) 1)),
      fun k => ?_⟩⟩, fun k => he _ (hd k φ)⟩
  beta_reduce
  rw [hm]
  conv_lhs => rw [he _ (hd k φ)]
  simp only [map_sum, map_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end General

theorem signBlockDeterminant_ne_zero_of_mem_maxCompact {n : ℕ} {ε : Fin n → Bool} (e : Bool) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Formalism.REAL.Kset ε) : signBlockDeterminant ε e k ≠ 0 := by
  have hd : k.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det k).1 (Unitary.isUnit_coe (U := ⟨k, hk.1⟩)) |>.ne_zero
  rw [Matrix.twoBlockTriangular_det k (fun i => ε i = e) (fun i hi j hj => by
    have h := congrFun (congrFun hk.2 i) j
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    cases e <;> simp only [Bool.not_eq_true, Bool.not_eq_false] at hi <;> simp [hi, hj] at h <;>
      first | linear_combination (1 / 2 : ℂ) * h | linear_combination (-1 / 2 : ℂ) * h)] at hd
  have := left_ne_zero_of_mul hd
  unfold signBlockDeterminant
  convert this
  rfl

theorem continuous_signBlockDeterminant {n : ℕ} (ε : Fin n → Bool) (e : Bool) : Continuous (signBlockDeterminant ε e) :=
  (continuous_id.matrix_submatrix _ _).matrix_det

theorem continuous_toMK {n : ℕ} (ε : Fin n → Bool) : Continuous fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k :=
  ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).continuous

variable {D : D7}

theorem unframe_mem {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S') (τ : D.what₂.Tau)
    {k : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hk : k ∈ Formalism.REAL.Kset (M'.ε τ)) :
    (M'.fr τ)⁻¹ * k * M'.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
  have hJ : kᴴ * Formalism.REAL.Jm (M'.ε τ) * k = Formalism.REAL.Jm (M'.ε τ) := (Formalism.REAL.maximal_compact_facts _ _).1 k hk
  have hJ' : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ,
      kᴴ * (Formalism.REAL.Jm (M'.ε τ) * (k * A)) = Formalism.REAL.Jm (M'.ε τ) * A := fun A => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ]
  have e1 : ((M'.fr τ)⁻¹)ᴴ * (M'.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd]; simp
  have e2 : ∀ A : Matrix (Fin W.rank) (Fin W.rank) ℂ, ((M'.fr τ)⁻¹)ᴴ * ((M'.fr τ)ᴴ * A) = A := fun A => by
    rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
  change ((M'.fr τ)⁻¹ * k * M'.fr τ)ᴴ * gramAt D W τ * ((M'.fr τ)⁻¹ * k * M'.fr τ) = gramAt D W τ
  rw [← M'.fr_gram τ]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, e2, Matrix.mul_nonsing_inv_cancel_left _ _ hd, hJ']

theorem elt_mul {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S')
    (τ : D.what₂.Tau) {a b : Matrix (Fin W.rank) (Fin W.rank) ℂ} (ha : a ∈ Formalism.REAL.Kset (M'.ε τ))
    (hb : b ∈ Formalism.REAL.Kset (M'.ε τ)) : elt θ M' τ (a * b) = elt θ M' τ a * elt θ M' τ b := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
  rw [elt, elt, elt, ← atTau_mul hθ W τ (unframe_mem M' τ ha) (unframe_mem M' τ hb)]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]

theorem elt_one' {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (τ : D.what₂.Tau) : elt θ M τ 1 = 1 := by
  rw [elt, Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), atTau_one hθ]

theorem coefCont_subst {G : Type} [TopologicalSpace G] {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool)
    (ε' : Fin b → Bool) (g : Matrix (Fin a) (Fin a) ℂ) {k : G → Matrix (Fin b) (Fin b) ℂ} (hk : Continuous k)
    (P : PolF D b a) : CoefCont fun x => subst τ ε ε' g (k x) P := by
  unfold subst
  refine CoefCont.aeval (fun v => ?_) P
  split_ifs
  all_goals first
    | exact CoefCont.const _
    | refine CoefCont.sum fun l => CoefCont.sum fun m => CoefCont.smul ?_ (CoefCont.const _)
  · exact (hk.matrix_elem _ _).mul continuous_const
  · exact ((hk.matrix_elem _ _).mul continuous_const).star

theorem fock_orbit_coefFam : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ), IsInfFam θ → Function.Injective (ptOf ψ θ M M' f) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.CompactFock ψ θ M M' ω f τ aS aT → ∀ φ : PolF D W.rank V.rank, ∃ (n : ℕ) (φs : Fin n → PolF D W.rank V.rank) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ), IsCoefFam c ∧ ∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (ptOf ψ θ M M' f φ) = ptOf ψ θ M M' f (∑ i, c i k • φs i) := by
  intro D V W S S' M M' θ ψ ω f τ aS aT hθ hpt hC φ
  obtain ⟨x, y, -, -, hc⟩ := hC
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f
  have hp : ptOf ψ θ M M' f = pt := rfl
  rw [hp] at hpt hc ⊢
  let s : Formalism.REAL.KG (M'.ε τ) → ℂ := fun k => signBlockDeterminant (M.ε τ) true 1 ^ x true * signBlockDeterminant (M.ε τ) false 1 ^ x false *
    (signBlockDeterminant (M'.ε τ) true (Formalism.REAL.toMK k) ^ y true * signBlockDeterminant (M'.ε τ) false (Formalism.REAL.toMK k) ^ y false)
  let ρ : Formalism.REAL.KG (M'.ε τ) → Module.End ℂ (PolF D W.rank V.rank) := fun k =>
    s k • (subst τ (M.ε τ) (M'.ε τ) ((1 : Matrix (Fin V.rank) (Fin V.rank) ℂ).map (starRingEnd ℂ))
      (Formalism.REAL.toMK k)).toLinearMap
  have key : ∀ k P, ω (1, elt θ M' τ (Formalism.REAL.toMK k)) (pt P) = pt (ρ k P) := fun k P => by
    have := hc 1 ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩ (Formalism.REAL.toMK k) k.2 P
    rw [elt_one' hθ, ← map_smul] at this
    exact this
  have hz : ∀ e, Continuous fun k : Formalism.REAL.KG (M'.ε τ) => signBlockDeterminant (M'.ε τ) e (Formalism.REAL.toMK k) ^ y e := fun e =>
    ((continuous_signBlockDeterminant _ e).comp (continuous_toMK _)).zpow₀ _ fun k => Or.inl (signBlockDeterminant_ne_zero_of_mem_maxCompact e k.2)
  have hs : Continuous s := continuous_const.mul ((hz true).mul (hz false))
  obtain ⟨n, φs, c, h1, h2⟩ := exists_coefFam ρ (fun a b P => hpt (by
      have e : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
      rw [← key, ← key, ← key, e, elt_mul hθ M' τ a.2 b.2, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk,
        mul_one]))
    (fun a P => (MvPolynomial.totalDegree_smul_le _ _).trans
      (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _))
    (fun P => CoefCont.smul hs (coefCont_subst τ _ _ _ (continuous_toMK _) P)) φ
  exact ⟨n, φs, c, h1, fun k => by rw [key, h2]⟩

end GlobalTheory.Chain.IoLift.FockOrbit

end
