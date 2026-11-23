import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralHarmonicNeZeroAndIsHomogeneous
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SumFinsuppAntidiagProdPowDivMultiFactorial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BlockProdEx

section Minors

open MvPolynomial Formalism.L2.Pj

variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k]
  (col : ∀ σ, ∀ s : Fin (r σ), Fin (s + 1) → Fin n)

def minor (R : Type) [CommRing R] (σ : T) (s : Fin (r σ)) : MvPolynomial (Letter T r n) R :=
  (Matrix.of fun i j : Fin (s + 1) =>
    (X ⟨σ, Fin.castLE s.isLt i, col σ s j⟩ : MvPolynomial (Letter T r n) R)).det

def minorsP (R : Type) [CommRing R] (a : T → ℕ → ℕ) : MvPolynomial (Letter T r n) R :=
  ∏ σ, ∏ s : Fin (r σ), minor r n col R σ s ^ (a σ s - a σ (s + 1))

theorem minorMonomial_map {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (a : T → ℕ → ℕ) :
    MvPolynomial.map φ (minorsP r n col R a) = minorsP r n col R' a := by
  simp only [minorsP, map_prod, map_pow, minor, RingHom.map_det]
  refine Finset.prod_congr rfl fun σ _ => Finset.prod_congr rfl fun s _ => ?_
  congr 2
  ext1 i j
  simp

theorem minorMonomial_coeff_mem (a : T → ℕ → ℕ) (O : Subring k) (m : Letter T r n →₀ ℕ) :
    (minorsP r n col k a).coeff m ∈ O := by
  rw [← minorMonomial_map r n col (Int.castRingHom k), coeff_map]
  exact intCast_mem O _

omit [Fintype T] in
theorem minor_ne_zero (hcol : ∀ σ s, Function.Injective (col σ s)) (σ : T) (s : Fin (r σ)) :
    minor r n col k σ s ≠ 0 := by
  classical
  intro h
  have h1 : MvPolynomial.eval (fun ℓ : Letter T r n =>
      if ∃ j : Fin (s + 1), (j : ℕ) = ℓ.2.1 ∧ ℓ.2.2 = col σ s j then (1 : k) else 0)
      (minor r n col k σ s) = 1 := by
    simp only [minor, RingHom.map_det]
    rw [show (MvPolynomial.eval _).mapMatrix _ = (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) k) from ?_,
      Matrix.det_one]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eval_X, Matrix.one_apply,
      (hcol σ s).eq_iff, Fin.val_castLE, Fin.val_inj, exists_eq_left]
    exact if_congr eq_comm rfl rfl
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem minorMonomial_ne_zero (hcol : ∀ σ s, Function.Injective (col σ s)) (a : T → ℕ → ℕ) :
    minorsP r n col k a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun σ _ => Finset.prod_ne_zero_iff.2 fun s _ =>
    pow_ne_zero _ (minor_ne_zero r n k col hcol σ s)

theorem minorMonomial_mem_harmonic (cc : T → T) (isX : T → Prop)
    (hdis : ∀ τ, isX τ → ∀ s s' i j, col τ s i ≠ col (cc τ) s' j) (a : T → ℕ → ℕ) :
    minorsP r n col k a ∈ harmK r n k cc isX (fun _ => 1) := by
  classical
  let S : Set (Letter T r n) := {v | ∃ s j, col v.1 s j = v.2.2}
  have hS : minorsP r n col k a ∈ MvPolynomial.supported k S := by
    refine Subalgebra.prod_mem _ fun t _ => Subalgebra.prod_mem _ fun s _ => Subalgebra.pow_mem _ ?_ _
    rw [minor, Matrix.det_apply']
    refine Subalgebra.sum_mem _ fun g _ => Subalgebra.mul_mem _ (intCast_mem _ _)
      (Subalgebra.prod_mem _ fun a _ => ?_)
    exact Algebra.subset_adjoin ⟨_, ⟨_, _, rfl⟩, rfl⟩
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
  intro τ hτ i i'
  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, Derivation.coeFn_coe]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
  by_cases hbb : b = b'
  · subst hbb
    by_cases hb : ∃ s j, col (cc τ) s j = b
    · obtain ⟨s', j', hj'⟩ := hb
      rw [minorHarm_pderiv_comm, minorHarm_pderiv_eq_zero hS, map_zero, smul_zero]
      rintro ⟨s, j, hj⟩
      exact hdis τ hτ s s' j j' (hj.trans hj'.symm)
    · rw [minorHarm_pderiv_eq_zero hS (v := ⟨cc τ, i', b⟩) hb, map_zero, smul_zero]
  · rw [Matrix.one_apply_ne hbb, zero_smul]

omit [Fintype T] in
theorem rowShift_minor (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : k) (σ' : T) (s : Fin (r σ')) :
    rowShift r n k σ i i' t (minor r n col k σ' s) = minor r n col k σ' s := by
  classical
  rw [minor, AlgHom.map_det]
  by_cases h : ∃ u : Fin (s + 1), (⟨σ', Fin.castLE s.isLt u⟩ : Σ σ, Fin (r σ)) = ⟨σ, i⟩
  · obtain ⟨u, hu⟩ := h
    obtain ⟨rfl, hu'⟩ := Sigma.mk.inj_iff.1 hu
    have hu'' : Fin.castLE s.isLt u = i := eq_of_heq hu'
    subst hu''
    have hi' : (i' : ℕ) < u := hi
    let u' : Fin (s + 1) := ⟨i', hi'.trans u.isLt⟩
    have hne : u ≠ u' := fun e => by
      have := congrArg Fin.val e
      simp only [u'] at this
      omega
    refine Eq.trans ?_ (Matrix.det_updateRow_add_smul_self _ hne (C t))
    congr 1
    ext1 x y
    by_cases hx : x = u
    · subst hx
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X,
        Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [if_pos ⟨_, rfl⟩]
      rfl
    · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X,
        Matrix.updateRow_ne hx]
      rw [if_neg]
      rintro ⟨b, hb⟩
      have := eq_of_heq (Sigma.mk.inj_iff.1 hb).2
      exact hx (Fin.castLE_injective s.isLt (congrArg Prod.fst this))
  · congr 1
    ext1 x y
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X]
    rw [if_neg]
    rintro ⟨b, hb⟩
    obtain ⟨rfl, hb'⟩ := Sigma.mk.inj_iff.1 hb
    exact h ⟨x, by rw [show Fin.castLE s.isLt x = i from congrArg Prod.fst (eq_of_heq hb')]⟩

theorem minorMonomial_rowInvariant (a : T → ℕ → ℕ) : RowInv r n k (minorsP r n col k a) := by
  intro σ i i' hi t
  simp only [minorsP, map_prod, map_pow, rowShift_minor r n k col σ i i' hi t]

omit [Fintype T] in
theorem minor_weighted (w : (Σ σ, Fin (r σ)) → ℕ) (σ : T) (s : Fin (r σ)) :
    (minor r n col k σ s).IsWeightedHomogeneous (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
      (∑ j : Fin (s + 1), w ⟨σ, Fin.castLE s.isLt j⟩) := by
  rw [minor, Matrix.det_apply']
  refine IsWeightedHomogeneous.sum _ _ _ fun g _ => ?_
  have h := IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
    (Finset.univ : Finset (Fin (s + 1)))
    (fun j => (X ⟨σ, Fin.castLE s.isLt (g j), col σ s j⟩ : MvPolynomial (Letter T r n) k))
    (fun j => w ⟨σ, Fin.castLE s.isLt (g j)⟩) (fun j _ => isWeightedHomogeneous_X _ _ _)
  rw [Equiv.sum_comp g (fun j => w ⟨σ, Fin.castLE s.isLt j⟩)] at h
  have h2 := (isWeightedHomogeneous_C (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
    (((Equiv.Perm.sign g : ℤˣ) : ℤ) : k)).mul h
  simpa using h2

theorem minorMonomial_rowDegree (a : T → ℕ → ℕ) (ha : ∀ σ, Antitone (a σ)) (h0 : ∀ σ, a σ (r σ) = 0) :
    RowDeg r n k a (minorsP r n col k a) := by
  classical
  intro m hm σ i
  let w : (Σ σ, Fin (r σ)) → ℕ := fun ℓ => if ℓ = ⟨σ, i⟩ then 1 else 0
  have h := IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) Finset.univ _ _
    fun σ' _ => IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) Finset.univ _ _
      fun (s : Fin (r σ')) _ => (minor_weighted r n k col w σ' s).pow (a σ' s - a σ' (s + 1))
  have h1 := h (mem_support_iff.1 hm)
  have hL : Finsupp.weight (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) m = ∑ b : Fin n, m ⟨σ, i, b⟩ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma,
      Finset.sum_eq_single σ, Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp [w]
    · intro j _ hj
      simp [w, hj]
    · simp
    · intro σ' _ hσ
      simp [w, hσ]
    · simp
  rw [← hL, h1, Finset.sum_eq_single σ]
  · have e : ∀ s : Fin (r σ), (a σ s - a σ (s + 1)) • ∑ j : Fin (s + 1), w ⟨σ, Fin.castLE s.isLt j⟩ =
        if (i : ℕ) ≤ s then a σ s - a σ (s + 1) else 0 := by
      intro s
      split_ifs with his
      · rw [Finset.sum_eq_single ⟨i, Nat.lt_succ_of_le his⟩]
        · simp [w]
        · intro j _ hj
          simp only [w]
          rw [if_neg]
          intro e
          have e' : Fin.castLE s.isLt j = i := eq_of_heq (Sigma.mk.inj_iff.1 e).2
          exact hj (Fin.ext (congrArg Fin.val e' :))
        · simp
      · rw [Finset.sum_eq_zero, smul_zero]
        intro j _
        simp only [w]
        rw [if_neg]
        intro e
        have := congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.1 e).2)
        have := j.isLt
        simp only [Fin.val_castLE] at *
        omega
    rw [Finset.sum_congr rfl fun s _ => e s,
      Fin.sum_univ_eq_sum_range (fun s => if (i : ℕ) ≤ s then a σ s - a σ (s + 1) else 0),
      ThetaClaimsCompare.gaps_sum _ (ha σ) _ _ i.isLt.le, h0, Nat.sub_zero]
  · intro σ' _ hσ
    simp [w, hσ]
  · simp

theorem minorMonomial_isHomogeneous (a : T → ℕ → ℕ) :
    (minorsP r n col k a).IsHomogeneous (∑ σ, ∑ s : Fin (r σ), (s + 1) * (a σ s - a σ (s + 1))) := by
  have h := IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => (1 : ℕ)) Finset.univ _ _
    fun σ' _ => IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => (1 : ℕ)) Finset.univ _ _
      fun (s : Fin (r σ')) _ => (minor_weighted r n k col (fun _ => 1) σ' s).pow (a σ' s - a σ' (s + 1))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    mul_comm (a _ _ - a _ _)] at h
  exact h

theorem minors_polynomial_coefficient_norm_le_pow (a : T → ℕ → ℕ) (N : ℕ) (hN : ∀ σ, r σ ≤ N) :
    MvPoly.l1Norm (minorsP r n col ℂ a) ≤
      (N : ℝ) ^ (∑ σ, ∑ s : Fin (r σ), (s + 1) * (a σ s - a σ (s + 1))) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  refine (MvPoly.l1Norm_prod_le _ _).trans
    (Finset.prod_le_prod (fun _ _ => MvPoly.l1Norm_nonneg _) fun σ _ => ?_)
  rw [← Finset.prod_pow_eq_pow_sum]
  simp only [pow_mul]
  refine MvPoly.l1Norm_prod_pow_le _ _ _ _ fun s _ => ?_
  refine (MvPoly.l1Norm_det_le_pow _ (R := 1) fun i j => by simp).trans ?_
  rw [Fintype.card_fin, mul_one]
  refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _
  exact_mod_cast (Nat.succ_le_of_lt s.isLt).trans (hN σ)

theorem exists_cols (h : ∑ σ, r σ * (r σ + 1) ≤ 2 * n) :
    ∃ e : (Σ x : (Σ σ, Fin (r σ)), Fin (x.2 + 1)) → Fin n, Function.Injective e := by
  have hc : Fintype.card (Σ x : (Σ σ, Fin (r σ)), Fin (x.2 + 1)) ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_sigma, Fintype.sum_sigma, Fintype.card_fin]
    simp only [Fintype.card_fin]
    have : ∀ m : ℕ, 2 * ∑ s : Fin m, ((s : ℕ) + 1) = m * (m + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [mul_add, ih]; ring
    rw [← Finset.sum_congr rfl fun σ _ => this (r σ), ← Finset.mul_sum] at h
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  exact ⟨e, e.injective⟩

end Minors

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

section Count

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem inPsi_conjugate_of_not {τ : E →+* ℂ} (h : ¬ InPsi H τ) : InPsi H (ComplexEmbedding.conjugate τ) := by
  have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h2 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h1, H.sqrt_neg_disc_sq]; simp
  have h3 := (sq_eq_sq_iff_eq_or_eq_neg.1 h2).resolve_left h
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq, h3, map_neg, (ThetaClaimsCompare.rt0_conj_neg_ne_zero H).1, neg_neg]

theorem sum_mult_le (Dw : Datum H) :
    ∑ τ : E →+* ℂ, Dw.mult τ * (Dw.mult τ + 1) ≤ I2.PT.f E * (Dw.p + Dw.q) * (Dw.p + Dw.q + 1) := by
  have h1 := Equiv.sum_comp (ComplexEmbedding.involutive_conjugate (K := E)).toPerm
    (fun τ => Dw.mult τ * (Dw.mult τ + 1))
  have h2 : ∑ τ : E →+* ℂ, (Dw.mult τ * (Dw.mult τ + 1) +
      Dw.mult (ComplexEmbedding.conjugate τ) * (Dw.mult (ComplexEmbedding.conjugate τ) + 1)) ≤
      ∑ _τ : E →+* ℂ, (Dw.p + Dw.q) * (Dw.p + Dw.q + 1) := by
    refine Finset.sum_le_sum fun τ _ => ?_
    by_cases h : InPsi H τ
    · rw [ThetaClaimsCompare.mult_of_inPsi h,
        ThetaClaimsCompare.mult_of_not_inPsi (ThetaClaimsCompare.not_inPsi_conjugate h)]
      nlinarith [Nat.zero_le (Dw.p * Dw.q)]
    · rw [ThetaClaimsCompare.mult_of_not_inPsi h,
        ThetaClaimsCompare.mult_of_inPsi (inPsi_conjugate_of_not h)]
      nlinarith [Nat.zero_le (Dw.p * Dw.q)]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card E ℂ, smul_eq_mul] at h2
  simp only [Function.Involutive.coe_toPerm] at h1
  rw [h1] at h2
  have h3 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hm := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  have h4 : Module.finrank ℚ E = 2 * I2.PT.f E := by
    unfold I2.PT.f
    rw [h3] at hm
    omega
  rw [h4, Nat.mul_assoc] at h2
  rw [Nat.mul_assoc]
  omega

theorem isBlockProd_minorsP (Dw : Datum H) {n : ℕ} (K : Type) [CommRing K]
    (e : (Σ x : (Σ σ, Fin (Dw.mult σ)), Fin (x.2 + 1)) → Fin n) (he : Function.Injective e)
    (a : (E →+* ℂ) → ℕ → ℕ) :
    IsBlockProd (Dw := Dw) (minorsP Dw.mult n (fun σ s j => e ⟨⟨σ, s⟩, j⟩) K a) := by
  classical
  let I := {x : (Σ σ, Fin (Dw.mult σ)) // 1 ≤ a x.1 x.2 - a x.1 (x.2 + 1)}
  let bk : I → Bk Dw n := fun x =>
    { τ := x.1.1, i := x.1.2 + 1, hi := x.1.2.isLt, c := a x.1.1 x.1.2 - a x.1.1 (x.1.2 + 1), hc := x.2,
      col := fun j => e ⟨x.1, j⟩,
      col_inj := fun j j' h => eq_of_heq (Sigma.mk.inj_iff.1 (he h)).2 }
  refine ⟨Fintype.card I, fun j => bk ((Fintype.equivFin I).symm j), fun j j' hj u u' h => ?_, ?_⟩
  · exact hj ((Fintype.equivFin I).symm.injective (Subtype.ext (congrArg Sigma.fst (he h))))
  · rw [Equiv.prod_comp (Fintype.equivFin I).symm (fun x => (bk x).poly K), minorsP, ← Fintype.prod_sigma']
    rw [← Finset.prod_filter_of_ne (p := fun x : (Σ σ, Fin (Dw.mult σ)) => 1 ≤ a x.1 x.2 - a x.1 (x.2 + 1))]
    · exact Finset.prod_subtype _ (by simp) _
    · intro x _ hx
      by_contra h0
      exact hx (by rw [show a x.1 x.2 - a x.1 (x.2 + 1) = 0 by omega, pow_zero])

end Count

theorem exists_blockProd_mem_harmA :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ i k, i ≤ k → a (τ, k) ≤ a (τ, i)) → I2.PT.f E * (Dw.p + Dw.q) * (Dw.p + Dw.q + 1) ≤ 2 * n → ∃ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmA c a n ∧ IsBlockProd P ∧ P.totalDegree = Formalism.L2.Pj.DF Dw a ∧ ∀ σ : c.F →+* ℂ, ∑ m ∈ P.support, ‖σ (P.coeff m)‖ ≤ ((Dw.p + Dw.q : ℕ) : ℝ) ^ Formalism.L2.Pj.DF Dw a := by
  intro E _ _ _ H Dw l c a n ha hn
  obtain ⟨e, he⟩ := exists_cols Dw.mult n ((sum_mult_le Dw).trans hn)
  let col : ∀ σ, ∀ s : Fin (Dw.mult σ), Fin (s + 1) → Fin n := fun σ s j => e ⟨⟨σ, s⟩, j⟩
  let b : (E →+* ℂ) → ℕ → ℕ := fun τ i => ThetaClaimsCompare.trunc Dw a (τ, i)
  have hinj : ∀ σ s, Function.Injective (col σ s) :=
    fun σ s j j' h => eq_of_heq (Sigma.mk.inj_iff.1 (he h)).2
  have hdis : ∀ τ, InPsi H τ → ∀ s s' i j, col τ s i ≠ col (ComplexEmbedding.conjugate τ) s' j := by
    intro τ h s s' i j hij
    have h1 : τ = ComplexEmbedding.conjugate τ := congrArg (fun x => x.1.1) (he hij)
    exact ThetaClaimsCompare.not_inPsi_conjugate h (h1 ▸ h)
  have hdeg : RowDeg Dw.mult n c.F b (minorsP Dw.mult n col c.F b) :=
    minorMonomial_rowDegree _ _ _ _ _ (ThetaClaimsCompare.antitone_trunc fun τ i j hij => ha τ i j hij)
      fun τ => if_neg (lt_irrefl _)
  have hne := minorMonomial_ne_zero Dw.mult n c.F col hinj b
  have hD : (minorsP Dw.mult n col c.F b).totalDegree = Formalism.L2.Pj.DF Dw a := by
    rw [← ThetaClaimsCompare.df_trunc]
    exact (isHomogeneous_of_rowDeg hdeg).totalDegree hne
  refine ⟨minorsP Dw.mult n col c.F b, ?_, isBlockProd_minorsP Dw c.F e he b, hD, fun σ => ?_⟩
  · rw [← ThetaClaimsCompare.harmA_trunc]
    exact ⟨⟨minorMonomial_mem_harmonic _ _ _ _ _ _ hdis _, minorMonomial_rowInvariant _ _ _ _ _, hdeg⟩, minorMonomial_coeff_mem _ _ _ _ _ _⟩
  · rw [← MvPoly.l1Norm_map, minorMonomial_map, ← hD, (minorMonomial_isHomogeneous Dw.mult n c.F col b).totalDegree hne]
    refine minors_polynomial_coefficient_norm_le_pow _ _ _ _ _ fun τ => ?_
    unfold Datum.mult
    split_ifs <;> omega

end GlobalTheory.BlockProdEx
