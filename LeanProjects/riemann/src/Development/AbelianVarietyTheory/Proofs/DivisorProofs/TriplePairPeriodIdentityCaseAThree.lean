import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerActionLocallyConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairLocalSchwartzAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ConeFourier
open scoped GlobalTheory.VacAny

section Abstract

variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  {M : Type} [AddCommGroup M] [Module K M] [TopologicalSpace M] [IsModuleTopology K M] [Module.Finite K M]

private theorem exists_ball {ι : Type} [Fintype ι] (b : Module.Basis ι K M) {R : ℝ} (hR : 0 < R) :
    ∃ L : AddSubgroup M, IsCompact (L : Set M) ∧ IsOpen (L : Set M) ∧ ∀ x, x ∈ L ↔ ‖b.equivFun x‖ ≤ R := by
  have h1 : Continuous b.equivFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  haveI := IsModuleTopology.toContinuousAdd K M
  have h2 : Continuous b.equivFun.symm := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  let N := IsUltrametricDist.closedBall_openAddSubgroup (ι → K) hR
  have hN : (N : Set (ι → K)) = Metric.closedBall 0 R := rfl
  refine ⟨(N : AddSubgroup (ι → K)).comap b.equivFun.toLinearMap.toAddMonoidHom, ?_, N.isOpen.preimage h1, fun x => ?_⟩
  · have := (isCompact_closedBall (0 : ι → K) R).image h2
    convert this using 1
    ext x
    constructor
    · intro hx
      exact ⟨b.equivFun x, hx, b.equivFun.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      change b.equivFun (b.equivFun.symm y) ∈ Metric.closedBall (0 : ι → K) R
      rwa [LinearEquiv.apply_symm_apply]
  · exact mem_closedBall_zero_iff

variable (K) in
include K in

private theorem exists_open_sub {U : Set M} (hU : U ∈ 𝓝 (0 : M)) : ∃ N : AddSubgroup M, IsOpen (N : Set M) ∧ (N : Set M) ⊆ U := by
  let b := Module.finBasis K M
  haveI := IsModuleTopology.toContinuousAdd K M
  have h2 : Continuous b.equivFun.symm := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  have h3 : b.equivFun.symm ⁻¹' U ∈ 𝓝 0 := h2.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨ε, hε, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 h3
  obtain ⟨L, -, ho, hL⟩ := exists_ball b hε
  refine ⟨L, ho, fun x hx => ?_⟩
  have := hb (mem_closedBall_zero_iff.2 ((hL x).1 hx))
  rwa [Set.mem_preimage, LinearEquiv.symm_apply_apply] at this

private theorem exists_ann_abs (Q : M →ₗ[K] M →ₗ[K] K) (hQ : ∀ x, (∀ y, Q x y = 0) → x = 0) (ψ : AddChar K ℂ)
    (hψ : IsLocallyConstant ψ) (h1 : ψ ≠ 1) {U : Set M} (hU : U ∈ 𝓝 (0 : M)) :
    ∃ L : AddSubgroup M, IsCompact (L : Set M) ∧ IsOpen (L : Set M) ∧ {x | ∀ y ∈ L, ψ (Q x y) = 1} ⊆ U ∧
      IsOpen {x | ∀ y ∈ L, ψ (Q x y) = 1} ∧ IsClosed {x | ∀ y ∈ L, ψ (Q x y) = 1} := by
  classical
  let b := Module.finBasis K M
  haveI := IsModuleTopology.toContinuousAdd K M
  let f : M →ₗ[K] (Fin (Module.finrank K M) → K) := LinearMap.pi fun i => Q.flip (b i)
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    refine hQ x fun y => ?_
    have : Q x = 0 := b.ext fun i => congrFun hx i
    rw [this]; rfl
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective hf
  have h2 : Continuous g := IsModuleTopology.continuous_of_linearMap g
  have h3 : g ⁻¹' U ∈ 𝓝 0 := h2.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨ε, hε, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 h3
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push Not at h
    exact h1 (AddChar.ext _ _ h)
  obtain ⟨L, hc, ho, hL⟩ := exists_ball b (R := ‖t‖ / ε + 1) (by positivity)
  have hcont : Continuous fun p : M × M => Q p.1 p.2 := IsModuleTopology.continuous_bilinear_of_finite_left Q
  have hlc : IsLocallyConstant fun p : M × M => ψ (Q p.1 p.2) := hψ.comp_continuous hcont
  have hev := fun x₀ => GlobalTheory.SchrLocConst.eventually_forall_eq _ hlc hc x₀
  refine ⟨L, hc, ho, fun x hx => ?_, ?_, ?_⟩
  · have hx' : f x ∈ Metric.closedBall 0 ε := by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hε.le]
      intro i
      by_contra hlt
      push Not at hlt
      have hne : f x i ≠ 0 := norm_pos_iff.1 (hε.trans hlt)
      have hm : (t / f x i) • b i ∈ L := by
        rw [hL, pi_norm_le_iff_of_nonneg (by positivity)]
        intro j
        have hle : ‖t / f x i‖ ≤ ‖t‖ / ε + 1 := by
          rw [norm_div]
          have : ‖t‖ / ‖f x i‖ ≤ ‖t‖ / ε := by gcongr
          linarith
        simp only [map_smul, Module.Basis.equivFun_apply, Module.Basis.repr_self, Pi.smul_apply, Finsupp.single_apply]
        split_ifs
        · simpa using hle
        · simp only [smul_zero, norm_zero]; positivity
      have := hx _ hm
      rw [map_smul, smul_eq_mul, show Q x (b i) = f x i from rfl, div_mul_cancel₀ _ hne] at this
      exact ht this
    have := hb hx'
    rwa [Set.mem_preimage, ← LinearMap.comp_apply, hg] at this
  · rw [isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [hev x] with x' h y hy
    exact (h y hy).trans (hx y hy)
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [hev x] with x' h h'
    exact hx fun y hy => (h y hy).symm.trans (h' y hy)

end Abstract

private theorem exists_charSum {Γ : Type} [AddCommGroup Γ] [TopologicalSpace Γ] [IsTopologicalAddGroup Γ] (L L' : AddSubgroup Γ)
    (hL : IsCompact (L : Set Γ)) (hL' : IsOpen (L' : Set Γ)) :
    ∃ (ι : Type) (S : Finset ι) (s : ι → Γ), S.Nonempty ∧ ∀ χ : AddChar Γ ℂ, (∀ y ∈ L', χ y = 1) →
      ((∀ y ∈ L, χ y = 1) → ∑ i ∈ S, χ (s i) = S.card) ∧ ((∃ y ∈ L, χ y ≠ 1) → ∑ i ∈ S, χ (s i) = 0) := by
  classical
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
  haveI : Finite (L ⧸ L'.addSubgroupOf L) :=
    AddSubgroup.quotient_finite_of_isOpen _ (hL'.preimage continuous_subtype_val)
  haveI := Fintype.ofFinite (L ⧸ L'.addSubgroupOf L)
  refine ⟨L ⧸ L'.addSubgroupOf L, Finset.univ, fun q => (q.out : L), Finset.univ_nonempty, fun χ hχ => ⟨fun h => ?_, ?_⟩⟩
  · simp [h _ (Subtype.prop _)]
  · rintro ⟨y, hy, hne⟩
    have key : ∀ a : L, χ ((Quotient.out (a : L ⧸ L'.addSubgroupOf L) : L) : Γ) = χ a := fun a => by
      obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add (L'.addSubgroupOf L) a
      rw [hh, AddSubgroup.coe_add, AddChar.map_add_eq_mul, show χ ((h : L) : Γ) = 1 from hχ _ h.2, mul_one]
    let χ' : AddChar (L ⧸ L'.addSubgroupOf L) ℂ :=
      { toFun := fun q => χ ((q.out : L) : Γ)
        map_zero_eq_one' := by rw [← QuotientAddGroup.mk_zero, key]; simp
        map_add_eq_mul' := fun p q => by
          induction p using QuotientAddGroup.induction_on
          induction q using QuotientAddGroup.induction_on
          rw [← QuotientAddGroup.mk_add, key, key, key, AddSubgroup.coe_add, AddChar.map_add_eq_mul] }
    refine (AddChar.sum_eq_zero_iff_ne_zero (ψ := χ')).2 fun h0 => hne ?_
    have := DFunLike.congr_fun h0 ((⟨y, hy⟩ : L) : L ⧸ L'.addSubgroupOf L)
    exact (key ⟨y, hy⟩).symm.trans this

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (E) in

private def liftE (v : Pl F) : Fv F v ⊗[F] E →ₗ[F] AE F E := TensorProduct.map (GlobalTheory.LatVac.liftV v) LinearMap.id

private def ptAt {n d : ℕ} (v : Pl F) (y : Fin n → Fv F v ⊗[F] E) (w : Fin d → E) : Matrix (Fin n) (Fin d) (AE F E) :=
  Matrix.vecMulVec (fun i => liftE E v (y i)) (incV F w)

private theorem at_liftE (v : Pl F) (z : Fv F v ⊗[F] E) : At (evFin F v) (liftE E v z) := by
  intro u hu
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t x =>
    rw [liftE, TensorProduct.map_tmul, TensorProduct.smul_tmul', GlobalTheory.LatVac.at_liftV v t u hu, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

private theorem compFin_liftE (v : Pl F) (z : Fv F v ⊗[F] E) : compFin F E v (liftE E v z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t x => exact congrArg (· ⊗ₜ[F] x) (GlobalTheory.LatVac.evFin_liftV v t)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem at_smul {M : Type} [AddCommGroup M] [Module (AF F) M] (v : Pl F) (a : Fv F v) (z : M) :
    At (evFin F v) (GlobalTheory.LatVac.liftV v a • z) := fun u hu => by
  rw [smul_smul, ← smul_eq_mul, GlobalTheory.LatVac.at_liftV v a u hu, zero_smul]

private theorem eq_of_at {v : Pl F} {z z' : AE F E} (hz : At (evFin F v) z) (hz' : At (evFin F v) z')
    (h : compFin F E v z = compFin F E v z') : z = z' := by
  obtain ⟨h1, h2⟩ := at_evFin_iff.1 hz
  obtain ⟨h1', h2'⟩ := at_evFin_iff.1 hz'
  refine GlobalTheory.Doubling.adele_ext (fun w => by rw [h1, h1']) fun w => ?_
  by_cases hw : w = v
  · subst hw; exact h
  · rw [h2 w hw, h2' w hw]

private theorem liftE_smul (v : Pl F) (a : Fv F v) (z : Fv F v ⊗[F] E) :
    liftE E v (a • z) = GlobalTheory.LatVac.liftV v a • liftE E v z :=
  eq_of_at (at_liftE v _) (at_smul v a _) (by rw [compFin_smul, compFin_liftE, compFin_liftE, GlobalTheory.LatVac.evFin_liftV])

private theorem liftE_compFin (v : Pl F) (z : AE F E) : liftE E v (compFin F E v z) = GlobalTheory.LatVac.liftV v 1 • z :=
  eq_of_at (at_liftE v _) (at_smul v 1 _) (by rw [compFin_smul, compFin_liftE, GlobalTheory.LatVac.evFin_liftV, one_smul])

private theorem ptAt_add {n d : ℕ} (v : Pl F) (y y' : Fin n → Fv F v ⊗[F] E) (w : Fin d → E) :
    ptAt v (y + y') w = ptAt v y w + ptAt v y' w := by
  ext i j
  simp [ptAt, Matrix.vecMulVec_apply, map_add, add_mul]

private theorem ptAt_smul {n d : ℕ} (v : Pl F) (a : Fv F v) (y : Fin n → Fv F v ⊗[F] E) (w : Fin d → E) :
    ptAt v (a • y) w = GlobalTheory.LatVac.liftV v a • ptAt v y w := by
  ext i j
  simp only [ptAt, Matrix.vecMulVec_apply, Pi.smul_apply, liftE_smul, Matrix.smul_apply, smul_mul_assoc]

private theorem ptAt_compFin {n d : ℕ} (v : Pl F) (y : Fin n → AE F E) (w : Fin d → E) :
    ptAt v (fun i => compFin F E v (y i)) w = GlobalTheory.LatVac.liftV v 1 • Matrix.vecMulVec y (incV F w) := by
  ext i j
  simp only [ptAt, Matrix.vecMulVec_apply, liftE_compFin, Matrix.smul_apply, smul_mul_assoc]

private theorem at_ptAt {n d : ℕ} (v : Pl F) (y : Fin n → Fv F v ⊗[F] E) (w : Fin d → E) : At (evFin F v) (ptAt v y w) := by
  intro u hu
  ext i j
  simp only [ptAt, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
  rw [← smul_mul_assoc, at_liftE v (y i) u hu, zero_mul]

private theorem mul_ptAt {n d : ℕ} (v : Pl F) (A : Matrix (Fin n) (Fin n) (AE F E)) (y : Fin n → Fv F v ⊗[F] E) (w : Fin d → E) :
    A * ptAt v y w = Matrix.vecMulVec (A *ᵥ fun i => liftE E v (y i)) (incV F w) := by
  ext i j
  simp [ptAt, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

private theorem symp_add_left {σ : E →ₐ[F] E} {n d : ℕ} (JX : Matrix (Fin n) (Fin n) (AE F E)) (JW : Matrix (Fin d) (Fin d) (AE F E))
    (ξ : AE F E) (x x' y : Matrix (Fin n) (Fin d) (AE F E)) :
    symp (R := AF F) (cA σ) ξ JX JW (x + x') y = symp (R := AF F) (cA σ) ξ JX JW x y + symp (R := AF F) (cA σ) ξ JX JW x' y := by
  simp only [symp, hTens, Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

private theorem symp_add_right {σ : E →ₐ[F] E} {n d : ℕ} (JX : Matrix (Fin n) (Fin n) (AE F E)) (JW : Matrix (Fin d) (Fin d) (AE F E))
    (ξ : AE F E) (x y y' : Matrix (Fin n) (Fin d) (AE F E)) :
    symp (R := AF F) (cA σ) ξ JX JW x (y + y') = symp (R := AF F) (cA σ) ξ JX JW x y + symp (R := AF F) (cA σ) ξ JX JW x y' := by
  simp only [symp, hTens, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

private def pairAt (σ : E →ₐ[F] E) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (v : Pl F)
    (w' w : Fin d → E) : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] Fv F v :=
  LinearMap.mk₂ (Fv F v)
    (fun x y => evFin F v (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) (ptAt v x w') (ptAt v y w)))
    (fun x x' y => by rw [ptAt_add, symp_add_left, map_add])
    (fun a x y => by
      rw [ptAt_smul, ← one_smul (AF F) (ptAt v y w), GlobalTheory.LatVac.symp_smul_smul, one_smul, mul_one, map_mul,
        GlobalTheory.LatVac.evFin_liftV, smul_eq_mul])
    (fun x y y' => by rw [ptAt_add, symp_add_right, map_add])
    (fun a x y => by
      rw [ptAt_smul, ← one_smul (AF F) (ptAt v x w'), GlobalTheory.LatVac.symp_smul_smul, one_smul, one_mul, map_mul,
        GlobalTheory.LatVac.evFin_liftV, smul_eq_mul])

private theorem pairAt_apply (σ : E →ₐ[F] E) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (v : Pl F)
    (w' w : Fin d → E) (x y : Fin n → Fv F v ⊗[F] E) : pairAt σ JX JW v w' w x y =
      evFin F v (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) (ptAt v x w') (ptAt v y w)) := rfl

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {n d : ℕ}

private theorem hTens_eq (JA : Matrix (Fin n) (Fin n) A) (JB : Matrix (Fin d) (Fin d) A) (x y : Matrix (Fin n) (Fin d) A) :
    hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring

private theorem hTens_mul {JA : Matrix (Fin n) (Fin n) A} (JB : Matrix (Fin d) (Fin d) A) (g : UG c JA)
    (x y : Matrix (Fin n) (Fin d) A) : hTens c JA JB (g.1.1 * x) (g.1.1 * y) = hTens c JA JB x y := by
  have hg : g.1.1ᵀ * JA * g.1.1.map c = JA := g.2
  rw [hTens_eq, hTens_eq, Matrix.transpose_mul, show (g.1.1 * y).map c = g.1.1.map c * y.map c from
    Matrix.map_mul (f := c.toRingHom)]
  conv_rhs => rw [← hg]
  simp only [Matrix.mul_assoc]

private theorem hTens_vec (JA : Matrix (Fin n) (Fin n) A) (JB : Matrix (Fin d) (Fin d) A) (x : Fin n → A) (w : Fin d → A)
    (y : Matrix (Fin n) (Fin d) A) :
    hTens c JA JB (Matrix.vecMulVec x w) y = ∑ k, (∑ i, x i * JA i k) * ∑ j, ∑ l, w j * JB j l * c (y k l) := by
  simp only [hTens, Matrix.vecMulVec_apply, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

end Alg

private theorem symp_shift_eq {σ : E →ₐ[F] E} {n d : ℕ}
    (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (k : UA σ JX) (l : (AE F E)ˣ) (x₀ : Fin n → E)
    (w' w : Fin d → E) (v : Pl F) (y : Fin n → Fv F v ⊗[F] E) :
    evFin F v (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) ((l : AE F E) • Matrix.vecMulVec (incV F x₀) (incV F w'))
      (mat k * ptAt v y w)) =
    pairAt σ JX JW v w' w (fun i => compFin F E v ((l : AE F E) * (mat k⁻¹ *ᵥ incV F x₀) i)) y := by
  rw [pairAt_apply, ptAt_compFin]
  conv_rhs => rw [← one_smul (AF F) (ptAt v y w), GlobalTheory.LatVac.symp_smul_smul, mul_one, map_mul, GlobalTheory.LatVac.evFin_liftV, one_mul]
  have e : (l : AE F E) • Matrix.vecMulVec (incV F x₀) (incV F w') =
      mat k * Matrix.vecMulVec (fun i => (l : AE F E) * (mat k⁻¹ *ᵥ incV F x₀) i) (incV F w') := by
    rw [Matrix.mul_vecMulVec, show (fun i => (l : AE F E) * (mat k⁻¹ *ᵥ incV F x₀) i) = (l : AE F E) • (mat k⁻¹ *ᵥ incV F x₀) from rfl,
      Matrix.mulVec_smul, Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_mul_inv, Matrix.one_mulVec, Matrix.smul_vecMulVec]
  rw [e, symp, symp]
  exact congrArg (fun t => evFin F v (Algebra.trace (AF F) (AE F E) (-1 * t))) (hTens_mul (cA σ) _ k _ _)

private theorem locCo_form {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux Bf κ) (v : Pl F) (u u' : W) :
    evFin F v (Bf u u') = (GlobalTheory.LatVac.locCo co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v u').2 -
      (GlobalTheory.LatVac.locCo co v u').1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v u).2 := by
  rw [co.form, map_sub]
  simp [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul]

private theorem conj_conj {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

private theorem cA_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    change a ⊗ₜ[F] σ (σ x) = _
    rw [conj_conj h]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem form_swap {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin d → E) : form σ J y x = -σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hJ, conj_conj h, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem pairAt_nondeg {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (v : Pl F) {w' w : Fin d → E} (hw : form σ W.J w' w = -1) (x : Fin n → Fv F v ⊗[F] E)
    (hx : ∀ y, pairAt σ X.J W.J v w' w x y = 0) : x = 0 := by
  classical
  have hw' : ∑ j, ∑ l, incV F w' j * incM F W.J j l * cA σ (incV F w l) = -1 := by
    have := congrArg (inclR (F := F) (AF F)) hw
    rw [map_neg, map_one] at this
    rw [← this]
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, mul_assoc]
    rfl
  have h1 : ∀ u, evFin F v (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (ptAt v x w') u) = 0 := by
    intro u
    let y : Fin n → AE F E := fun k => -cA σ (∑ j, ∑ l, incV F w' j * incM F W.J j l * cA σ (u k l))
    have h2 := hx fun i => compFin F E v (y i)
    rw [pairAt_apply, ptAt_compFin, ← one_smul (AF F) (ptAt v x w'), GlobalTheory.LatVac.symp_smul_smul, one_mul, map_mul,
      GlobalTheory.LatVac.evFin_liftV, one_mul] at h2
    rw [← h2, symp, symp, ptAt, hTens_vec, hTens_vec]
    congr 3
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have : ∀ j l, incV F w' j * incM F W.J j l * cA σ (Matrix.vecMulVec y (incV F w) k l) =
        cA σ (y k) * (incV F w' j * incM F W.J j l * cA σ (incV F w l)) := fun j l => by
      rw [Matrix.vecMulVec_apply, map_mul]; ring
    simp only [this, ← Finset.mul_sum]
    rw [hw']
    simp only [y, map_neg, cA_cA h, mul_neg, mul_one, neg_neg]
  have h3 : ∀ a : AF F, evFin F v a = 0 → GlobalTheory.LatVac.liftV v 1 * a = 0 := fun a ha => by
    rw [mul_comm]; exact GlobalTheory.LatVac.at_liftV v 1 a ha
  have h4 : ptAt v x w' = 0 := by
    rw [← partFin_of_at (at_ptAt v x w'), partFin]
    apply M.co.e.injective
    rw [map_smul, map_zero]
    refine Prod.ext (funext fun k => h3 _ ?_) (funext fun k => h3 _ ?_)
    · have := h1 (M.co.e.symm (0, Pi.single k 1))
      rw [M.co.form, LinearEquiv.apply_symm_apply] at this
      simpa using this
    · have := h1 (M.co.e.symm (Pi.single k 1, 0))
      rw [M.co.form, LinearEquiv.apply_symm_apply] at this
      simpa using this
  obtain ⟨j, hj⟩ : ∃ j, w' j ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [form, dotProduct, hc] at hw
  funext i
  have h5 : liftE E v (x i) * inclR (F := F) (AF F) (w' j) = 0 := congrFun (congrFun h4 i) j
  rw [((Ne.isUnit hj).map _).mul_left_eq_zero] at h5
  rw [← compFin_liftE v (x i), h5, map_zero, Pi.zero_apply]

private theorem omega_schr (hA : ActsEx) {σ : E →ₐ[F] E}
    (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ) (hP : IsPair B M χX χW om r s r' s') (v : Pl F) (k : UA σ X.J) (hk : k ∈ UAt σ X (evFin F v))
    (u : Matrix (Fin n) (Fin d) (AE F E)) (hu : At (evFin F v) u) (φ : (Fin n × Fin d → Fv F v) → ℂ)
    (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) :
    locOp v (om (k, 1)) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ) =
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (mat k * u)) (locOp v (om (k, 1)) φ) := by
  have h1W : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := (UAtSub σ W (evFin F v)).one_mem
  have hφ₁ := GlobalTheory.SchrSB.schr_mem_SB B.ψ hP.base.std.1 v (GlobalTheory.LatVac.locCo M.co v u) φ hφ
  have hat : At (evFin F v) (mat k * u) := fun a ha => by rw [← Matrix.mul_smul, hu a ha, Matrix.mul_zero]
  refine (GlobalTheory.IntertwLocal.local_intertw F E σ B n d X W M χX χW om r s r' s' hP v (k, 1) u φ _ _ _ _ hφ hφ₁
    (locOp_mem v _ φ) (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ) (acts_locOp_om hA hP hk h1W hφ)
    (acts_locOp_om hA hP hk h1W hφ₁) ?_).symm
  rw [GlobalTheory.StabHaar.mat_one, Matrix.transpose_one, Matrix.mul_one]
  exact GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ hat _

private theorem psi_lc {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ) (v : Pl F) : IsLocallyConstant (GlobalTheory.LatVac.psiAt ψ v) :=
  GlobalTheory.SchrSB.isLocallyConstant_addChar _ (GlobalTheory.SchrSB.continuous_psiAt ψ hψ v)

private theorem exists_ann {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (v : Pl F) {w' w : Fin d → E} (hw : form σ W.J w' w = -1) {U : Set (Fin n → Fv F v ⊗[F] E)} (hU : U ∈ 𝓝 0) :
    ∃ L : AddSubgroup (Fin n → Fv F v ⊗[F] E), IsCompact (L : Set (Fin n → Fv F v ⊗[F] E)) ∧
      IsOpen (L : Set (Fin n → Fv F v ⊗[F] E)) ∧
      {x | ∀ y ∈ L, GlobalTheory.LatVac.psiAt ψ v (pairAt σ X.J W.J v w' w x y) = 1} ⊆ U ∧
      IsOpen {x | ∀ y ∈ L, GlobalTheory.LatVac.psiAt ψ v (pairAt σ X.J W.J v w' w x y) = 1} ∧
      IsClosed {x | ∀ y ∈ L, GlobalTheory.LatVac.psiAt ψ v (pairAt σ X.J W.J v w' w x y) = 1} := by
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : ProperSpace (Fv F v) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  exact exists_ann_abs _ (pairAt_nondeg h M v hw) _ (psi_lc hψ.1 v) (GlobalTheory.PsiNontriv.psiAt_ne_one _ hψ v) hU

private theorem exists_fix {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    (v : Pl F) (w' w : Fin d → E) (a : Fin n → Fv F v ⊗[F] E) (φ : (Fin n × Fin d → Fv F v) → ℂ)
    (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) : ∃ N : AddSubgroup (Fin n → Fv F v ⊗[F] E),
      IsOpen (N : Set (Fin n → Fv F v ⊗[F] E)) ∧ ∀ y ∈ N,
        GlobalTheory.LatVac.psiAt ψ v (-pairAt σ X.J W.J v w' w a y) •
          schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v (ptAt v y w)) φ = φ := by
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : ProperSpace (Fv F v) := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hχl := psi_lc hψ v
  have hχ0 : ∀ᶠ y in 𝓝 (0 : Fv F v), GlobalTheory.LatVac.psiAt ψ v y = 1 := by simpa using hχl.eventually_eq 0
  let T : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun y => GlobalTheory.LatVac.locCo M.co v (ptAt v y w)
      map_add' := fun y y' => by rw [ptAt_add, map_add]
      map_smul' := fun t y => by
        rw [ptAt_smul]
        refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
          simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV] }
  have hT : Continuous T := IsModuleTopology.continuous_of_linearMap T
  have hQ : Continuous (pairAt σ X.J W.J v w' w a) := IsModuleTopology.continuous_of_linearMap _
  have h1 := ((GlobalTheory.SchrLocConst.schr_isLocallyConstant _ hχ0 φ hφ).comp_continuous hT).eventually_eq 0
  have h2 := (hχl.comp_continuous hQ.neg).eventually_eq 0
  obtain ⟨N, hNo, hN⟩ := exists_open_sub (Fv F v) (h1.and h2)
  refine ⟨N, hNo, fun y hy => ?_⟩
  obtain ⟨e1, e2⟩ := hN hy
  simp only [Function.comp_apply, map_zero, neg_zero, AddChar.map_zero_eq_one, Pi.neg_apply] at e1 e2
  rw [e2, one_smul]
  refine e1.trans ?_
  funext x
  simp [schr]

private theorem schr_comm {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) • schr ψ w' (schr ψ w φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul]
  have e1 : x + w.1 + w'.1 = x + w'.1 + w.1 := by abel
  rw [e1]
  simp only [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [add_dotProduct]
  ring

private theorem integ_add_smul (hA : ActsEx) {σ : E →ₐ[F] E} {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}
    {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s')
    (hψ : Continuous B.ψ) (v : Pl F) (ev : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ)
    (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) {k : UA σ X.J} (hk : k ∈ UAt σ X (evFin F v)) (l : (AE F E)ˣ)
    (a b : ℂ) {φ φ' : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hφ' : φ' ∈ SB (Fin n × Fin d → Fv F v)) :
    GlobalTheory.ConeBump.integ B M om v ev u (a • φ + b • φ') k l =
      a • GlobalTheory.ConeBump.integ B M om v ev u φ k l + b • GlobalTheory.ConeBump.integ B M om v ev u φ' k l := by
  have hT : IsLinearMap ℂ (M.co.rho B.ψ (partFin v (u l))) :=
    ⟨fun f g => funext fun x => mul_add _ _ _, fun c f => funext fun x => mul_left_comm _ _ _⟩
  have hk' : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (om (k, 1)) φ φ₁ :=
    fun φ hφ => ((hA F E σ B n d X W M χX χW om r s r' s' hP v).1 k hk 1 (UAtSub σ W (evFin F v)).one_mem φ hφ).exists
  simp only [GlobalTheory.ConeBump.integ]
  rw [locOp_lin (om (k, 1)).isLinear hk' a b hφ hφ', locOp_lin hT
    (fun f hf => ⟨_, locOp_mem v _ f, (locOp_rho M.co hψ v (u l) hf).1⟩) a b (locOp_mem _ _ _) (locOp_mem _ _ _),
    map_add, map_smul, map_smul]

private theorem integ_sum (hA : ActsEx) {σ : E →ₐ[F] E} {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}
    {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s')
    (hψ : Continuous B.ψ) (v : Pl F) (ev : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ)
    (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) {k : UA σ X.J} (hk : k ∈ UAt σ X (evFin F v)) (l : (AE F E)ˣ)
    {ι : Type} (S : Finset ι) (c : ι → ℂ) (g : ι → (Fin n × Fin d → Fv F v) → ℂ) (hg : ∀ i, g i ∈ SB (Fin n × Fin d → Fv F v)) :
    GlobalTheory.ConeBump.integ B M om v ev u (∑ i ∈ S, c i • g i) k l = ∑ i ∈ S, c i • GlobalTheory.ConeBump.integ B M om v ev u (g i) k l := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h := integ_add_smul hA hP hψ v ev u hk l 0 0 (zero_mem (SB _)) (zero_mem (SB _))
    simpa using h
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    have h := integ_add_smul hA hP hψ v ev u hk l (c i) 1 (φ' := ∑ j ∈ S, c j • g j) (hg i) (Submodule.sum_mem _ fun j _ => (SB _).smul_mem (c j) (hg j))
    simpa using h

end GlobalTheory.ConeFourier
end

open GlobalTheory.ConeFourier in
open scoped GlobalTheory.VacAny in
theorem _root_.GlobalTheory.T.triple_pair_period_identity_case_a_three : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (v : Pl F), ∀ U ∈ 𝓝 (0 : Fin (b + 2) → Fv F v ⊗[F] E), ∃ V ⊆ U, IsOpen V ∧ IsClosed V ∧
      (0 : Fin (b + 2) → Fv F v ⊗[F] E) ∈ V ∧ ∀ φ₀ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ∃ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), ∀ k ∈ UAt σ G.V (evFin F v), ∀ l ∈ idelesAt E (evFin F v),
        GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ k l =
          (V.indicator (fun _ => (1 : ℂ)) (GlobalTheory.ConeBump.disp v H.x k l)) • GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ₀ k l := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e hE ei ev hei hev hloc v U hU
  have hψ : Continuous B.ψ := hT.base.std.1
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hKP.base
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  obtain ⟨L, hLc, hLo, hVU, hVo, hVc⟩ := exists_ann hT.base.cm G.M hT.base.std v
    (w' := H'.y) (w := H'.x) (by rw [form_swap hT.base.cm hT.geo.hW.skew, hC.hH'.xy, map_one]) hU
  refine ⟨_, hVU, hVo, hVc, fun y _ => by
    rw [map_zero, LinearMap.zero_apply, AddChar.map_zero_eq_one], fun φ₀ hφ₀ => ?_⟩
  set ψv := GlobalTheory.LatVac.psiAt B.ψ v with hψv
  set Q := pairAt σ G.V.J G.W.J v H'.y H'.x with hQ
  set a₀ : Fin (b + 2) → Fv F v ⊗[F] E := fun i => compFin F E v (incV F H.x i) with ha₀
  set f : (Fin (b + 2) → Fv F v ⊗[F] E) → (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ :=
    fun y => ψv (-Q a₀ y) • schr ψv (GlobalTheory.LatVac.locCo G.M.co v (ptAt v y H'.x)) φ₀ with hf
  have hsch : ∀ y, schr ψv (GlobalTheory.LatVac.locCo G.M.co v (ptAt v y H'.x)) φ₀ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) :=
    fun y => GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ v _ φ₀ hφ₀
  have hfSB : ∀ y, f y ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) := fun y => (SB _).smul_mem _ (hsch y)

  have key : ∀ y, ∀ k ∈ UAt σ G.V (evFin F v), ∀ l : (AE F E)ˣ,
      GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') (f y) k l =
        ψv (Q (GlobalTheory.ConeBump.disp v H.x k l) y) • GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ₀ k l := by
    intro y k hk l
    have hsm : GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') (f y) k l =
        ψv (-Q a₀ y) • GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H')
          (schr ψv (GlobalTheory.LatVac.locCo G.M.co v (ptAt v y H'.x)) φ₀) k l := by
      have h := integ_add_smul hA hP hψ v (ev v) (shiftA H H') hk l (ψv (-Q a₀ y)) 0 (hsch y) (hsch y)
      simpa [hf] using h
    have hω := locOp_mem v (om (k, 1)) φ₀
    have hmem : mat k * ptAt v y H'.x ∈ isoA H H' := Or.inl ⟨_, mul_ptAt v (mat k) y H'.x⟩
    have hat : At (evFin F v) (mat k * ptAt v y H'.x) := fun u hu => by
      rw [← Matrix.mul_smul, at_ptAt v y H'.x u hu, Matrix.mul_zero]
    have h1 : GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') (schr ψv (GlobalTheory.LatVac.locCo G.M.co v (ptAt v y H'.x)) φ₀) k l =
        ψv (evFin F v (symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (shiftA H H' l) (mat k * ptAt v y H'.x))) •
          GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ₀ k l := by
      simp only [GlobalTheory.ConeBump.integ]
      rw [(locOp_rho G.M.co hψ v (shiftA H H' l) (locOp_mem v _ _)).2, (locOp_rho G.M.co hψ v (shiftA H H' l) hω).2,
        omega_schr hA B G.M _ _ om _ _ _ _ hP v k hk _ (at_ptAt v y H'.x) φ₀ hφ₀, schr_comm, map_smul,
        GlobalTheory.ThK.EvLocInv.ev_schr_of_mem B G.M G₁.M H.ι H'.ι (isoA H H') e hE hψ hT.geo.hM hT₁.geo.hM ei ev hei hev hloc v
          _ hmem hat _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ v _ _ hω), ← locCo_form]
    rw [hsm, h1, shiftA, symp_shift_eq, smul_smul, ← AddChar.map_add_eq_mul, neg_add_eq_sub, ← LinearMap.sub_apply, ← map_sub]
    rfl
  obtain ⟨N, hNo, hN⟩ := exists_fix G.M B.ψ hψ v H'.y H'.x a₀ φ₀ hφ₀
  obtain ⟨ι, S, rp, hSne, hS⟩ := exists_charSum L (N ⊓ L) hLc (hNo.inter hLo)
  refine ⟨∑ s ∈ S, (S.card : ℂ)⁻¹ • f (rp s), Submodule.sum_mem _ fun s _ => (SB _).smul_mem _ (hfSB _), fun k hk l hl => ?_⟩
  rw [integ_sum hA hP hψ v (ev v) (shiftA H H') hk l S _ (fun s => f (rp s)) fun s => hfSB _]
  simp only [key _ k hk l, smul_smul]
  set D := GlobalTheory.ConeBump.disp v H.x k l
  set I := GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ₀ k l
  let χ : AddChar (Fin (b + 2) → Fv F v ⊗[F] E) ℂ := ψv.compAddMonoidHom (Q D).toAddMonoidHom
  have hχ : ∀ y, χ y = ψv (Q D y) := fun y => rfl
  funext p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hI : I p = 0
  · simp [hI]
  have htriv : ∀ y ∈ N ⊓ L, χ y = 1 := by
    intro y hy
    have h := key y k hk l
    rw [show f y = φ₀ from hN y hy.1] at h
    have hp := congrFun h p
    simp only [Pi.smul_apply, smul_eq_mul] at hp
    rw [hχ]
    have : (ψv (Q D y) - 1) * I p = 0 := by rw [sub_mul, ← hp]; ring
    rcases mul_eq_zero.1 this with h' | h'
    · exact sub_eq_zero.1 h'
    · exact absurd h' hI
  have e1 : ∑ s ∈ S, (S.card : ℂ)⁻¹ * ψv (Q D (rp s)) * I p = (S.card : ℂ)⁻¹ * (∑ s ∈ S, χ (rp s)) * I p := by
    rw [Finset.mul_sum, Finset.sum_mul]
    rfl
  have hcard : (S.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.2 hSne).ne'
  rw [e1]
  by_cases hall : ∀ y ∈ L, χ y = 1
  · rw [(hS χ htriv).1 hall, Set.indicator_of_mem (show D ∈ {x | ∀ y ∈ L, ψv (Q x y) = 1} from fun y hy => hall y hy),
      inv_mul_cancel₀ hcard]
  · push Not at hall
    obtain ⟨y, hy, hne⟩ := hall
    rw [(hS χ htriv).2 ⟨y, hy, hne⟩, Set.indicator_of_notMem (show D ∉ {x | ∀ y ∈ L, ψv (Q x y) = 1} from fun h => hne (h y hy))]
    simp
