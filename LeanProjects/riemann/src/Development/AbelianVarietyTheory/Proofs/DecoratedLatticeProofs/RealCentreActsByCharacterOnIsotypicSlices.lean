import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CentreTarget

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

theorem mulVec_eq_smul (σ : R →+* R) (J : Matrix (Fin n) (Fin n) R) (hJ : ∀ i j, σ (J i j) = J j i)
    (b : Matrix (Fin n) (Fin n) R) (hb : ∀ g : GL (Fin n) R, g ∈ Formalism.UG.UJ σ J → g.1 * b = b * g.1)
    (h2 : IsUnit (2 : R)) (v : Fin n → R) (hv : ∀ i, σ (v i) = v i) (hq : IsUnit ((v ᵥ* J) ⬝ᵥ v)) :
    ∃ c : R, b *ᵥ v = c • v := by
  obtain ⟨u, hu⟩ := hq.exists_left_inv
  have hw : ∀ i, σ ((v ᵥ* J) i) = (J *ᵥ v) i := fun i => by
    simp only [vecMul, mulVec, dotProduct, map_sum, map_mul, hv, hJ]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hσq : σ ((v ᵥ* J) ⬝ᵥ v) = (v ᵥ* J) ⬝ᵥ v := by
    conv_rhs => rw [← dotProduct_mulVec, dotProduct_comm]
    simp only [dotProduct, map_sum, map_mul, hv, hw]
  have hσu : σ u = u := by
    have h := congrArg σ hu
    rw [map_mul, hσq, map_one] at h
    linear_combination u * h - σ u * hu
  set P : Matrix (Fin n) (Fin n) R := vecMulVec v (v ᵥ* J) with hP
  have hPP : P * P = ((v ᵥ* J) ⬝ᵥ v) • P := by
    rw [hP, vecMulVec_mul_vecMulVec, vecMulVec_smul]
  have hrr : (1 - (2 * u) • P) * (1 - (2 * u) • P) = 1 := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hPP, smul_smul, smul_smul, mul_assoc (2 * u), mul_assoc 2 u (_ ⬝ᵥ _), hu]
    module
  have hPJ : Formalism.UG.cT σ (1 - (2 * u) • P) * J = J * (1 - (2 * u) • P) := by
    have e : Formalism.UG.cT σ (1 - (2 * u) • P) = 1 - (2 * u) • vecMulVec (J *ᵥ v) v := by
      ext i j
      simp only [Formalism.UG.cT, hP, transpose_apply, map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub,
        map_mul, vecMulVec_apply, hv, hw, hσu, map_ofNat, Matrix.one_apply, apply_ite σ, map_one, map_zero, eq_comm (a := j)]
      ring
    rw [e, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hP,
      vecMulVec_mul, mul_vecMulVec]
  have h := hb ⟨1 - (2 * u) • P, 1 - (2 * u) • P, hrr, hrr⟩ (by
    show Formalism.UG.cT σ (1 - (2 * u) • P) * J * (1 - (2 * u) • P) = J
    rw [hPJ, Matrix.mul_assoc, hrr, Matrix.mul_one])
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    sub_right_inj] at h
  have h' := congrArg (· *ᵥ v) h
  simp only [smul_mulVec, ← mulVec_mulVec, hP, vecMulVec_mulVec, mulVec_smul, op_smul_eq_smul, smul_smul] at h'
  obtain ⟨t, ht⟩ := h2.exists_left_inv
  refine ⟨t * (2 * u * ((v ᵥ* J) ⬝ᵥ (b *ᵥ v))), ?_⟩
  rw [mul_smul, h', smul_smul, mul_assoc 2 u, hu, mul_one, ht, one_smul]

theorem eq_smul_one (b : Matrix (Fin n) (Fin n) R) (h1 : ∀ i, ∃ c : R, b *ᵥ Pi.single i 1 = c • Pi.single i 1)
    (h2 : ∀ i j, i ≠ j → ∃ c : R, b *ᵥ (Pi.single i 1 + Pi.single j 1) = c • (Pi.single i 1 + Pi.single j 1))
    (i₀ : Fin n) : b = b i₀ i₀ • (1 : Matrix (Fin n) (Fin n) R) := by
  have off : ∀ i j, i ≠ j → b i j = 0 := fun i j hij => by
    obtain ⟨c, hc⟩ := h1 j
    simpa [hij] using congrFun hc i
  have dg : ∀ i, b i i = b i₀ i₀ := fun i => by
    by_cases hi : i = i₀
    · rw [hi]
    · obtain ⟨c, hc⟩ := h2 i i₀ hi
      have a1 := congrFun hc i
      have a2 := congrFun hc i₀
      simp [mulVec_add, hi, Ne.symm hi, off i i₀ hi, off i₀ i (Ne.symm hi)] at a1 a2
      rw [a1, a2]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [dg]
  · simp [hij, off i j hij]

theorem map_smul_one {R' : Type} [CommRing R'] (φ : R →+* R') (c : R) :
    (c • (1 : Matrix (Fin n) (Fin n) R)).map φ = φ c • 1 := by
  ext i j
  simp only [map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply, apply_ite φ, map_one, map_zero]

theorem map_eq_one_of {R' : Type} [CommRing R'] (φ : R →+* R') {c : R} (i : Fin n)
    (h : (c • (1 : Matrix (Fin n) (Fin n) R)).map φ = 1) : φ c = 1 := by
  rw [map_smul_one] at h
  simpa using congrFun (congrFun h i) i

theorem cT_scalar (σ : R →+* R) (J : Matrix (Fin n) (Fin n) R) (c : R) :
    Formalism.UG.cT σ (c • (1 : Matrix (Fin n) (Fin n) R)) * J * (c • (1 : Matrix (Fin n) (Fin n) R)) = (c * σ c) • J := by
  rw [Formalism.UG.cT, map_smul_one, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, smul_smul]

theorem mul_conj_eq_one (σ : R →+* R) (J : Matrix (Fin n) (Fin n) R) {c : R} (i : Fin n)
    (h1 : IsUnit ((Pi.single i 1 ᵥ* J) ⬝ᵥ Pi.single i 1))
    (hu : Formalism.UG.cT σ (c • (1 : Matrix (Fin n) (Fin n) R)) * J * (c • (1 : Matrix (Fin n) (Fin n) R)) = J) :
    c * σ c = 1 := by
  rw [cT_scalar] at hu
  rw [dotProduct_single, mul_one, single_vecMul, one_smul] at h1
  exact h1.mul_right_cancel ((congrFun (congrFun hu i) i).trans (one_mul _).symm)

theorem exists_scalar (σ : R →+* R) (J : Matrix (Fin n) (Fin n) R) {c : R} (hc : c * σ c = 1) :
    ∃ g ∈ Formalism.UG.UJ σ J, g.1 = c • 1 ∧ g⁻¹.1 = σ c • 1 := by
  refine ⟨⟨c • 1, σ c • 1, ?_, ?_⟩, ?_, rfl, rfl⟩
  · rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, hc, one_smul]
  · rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_comm, hc, one_smul]
  · exact (cT_scalar σ J c).trans (by rw [hc, one_smul])

theorem mul_scalar_comm (M : Matrix (Fin n) (Fin n) R) (c : R) :
    M * (c • (1 : Matrix (Fin n) (Fin n) R)) = (c • (1 : Matrix (Fin n) (Fin n) R)) * M := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

end Alg

variable {D : D7}

open scoped ComplexOrder in

theorem norm_ne_zero {V : HSp D} {x : DefSp V} (hx : x.Is) (v : Fin V.rank → ℚ) (hv : v ≠ 0) :
    ((fun i => (v i : D.host.E)) ᵥ* V.gram) ⬝ᵥ (fun i => (v i : D.host.E)) ≠ 0 := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  intro h0
  have hp := ((hx.cart τ).2.2.dotProduct_mulVec_pos (x := fun i => (v i : ℂ))
    (fun h => hv (funext fun i => by simpa using congrFun h i))).ne'
  have h1 : star (fun i => (v i : ℂ)) ⬝ᵥ (gramAt D V τ *ᵥ fun i => (v i : ℂ)) = 0 := by
    have := congrArg (tauE D τ) h0
    rw [← dotProduct_mulVec] at this
    simpa [dotProduct, mulVec, gramAt] using this
  rcases hx.pm τ with e | e
  · rw [e, Matrix.mul_one] at hp
    exact hp h1
  · rw [e, Matrix.mul_neg, Matrix.mul_one, neg_mulVec, dotProduct_neg, h1, neg_zero] at hp
    exact hp rfl

theorem norm_unit {V : HSp D} {x : DefSp V} (hx : x.Is) (v : Fin V.rank → ℚ) (hv : v ≠ 0) :
    IsUnit (((fun i => incA D (v i)) ᵥ* JR (AF D.host.F) V.gram) ⬝ᵥ fun i => incA D (v i)) := by
  have := (norm_ne_zero hx v hv).isUnit.map (incA D)
  convert this using 1
  simp only [dotProduct, vecMul, map_sum, map_mul, JR, map_apply]

theorem sigR_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem cA_incA (e : D.host.E) : cA D (incA D e) = incA D (star e) := by
  exact sigR_inclR _ _ e

theorem mt_central {V : HSp D} {x : DefSp V} (hx : x.Is) {b : GA D V} (hb : b ∈ Subgroup.center (GA D V))
    (i₀ : Fin V.rank) : Formalism.L2.Theta.mt V b = Formalism.L2.Theta.mt V b i₀ i₀ • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have key : ∀ v : Fin V.rank → ℚ, v ≠ 0 → ∃ c : AE D, Formalism.L2.Theta.mt V b *ᵥ (fun i => incA D (v i)) = c • fun i => incA D (v i) := by
    intro v hv
    refine mulVec_eq_smul (cA D) (JR (AF D.host.F) V.gram) (fun i j => ?_) _ (fun g hg => ?_) ?_ _ (fun i => ?_)
      (norm_unit hx v hv)
    · show cA D (incA D (V.gram i j)) = incA D (V.gram j i)
      rw [cA_incA]
      exact congrArg _ (V.herm.eq _ _)
    · exact congrArg (Formalism.L2.Theta.mt V) (Subgroup.mem_center_iff.1 hb (⟨g, hg⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram))
    · have := (two_ne_zero : (2 : D.host.E) ≠ 0).isUnit.map (incA D)
      rwa [map_ofNat] at this
    · rw [cA_incA, star_ratCast]
  refine eq_smul_one _ (fun i => ?_) (fun i j hij => ?_) i₀
  · have := key (Pi.single i 1) (by simp)
    have e : (fun k => incA D ((Pi.single i 1 : Fin V.rank → ℚ) k : ℚ)) = Pi.single i 1 := by
      funext k
      by_cases hk : k = i <;> simp [hk]
    rwa [e] at this
  · have := key (Pi.single i 1 + Pi.single j 1) (fun h => by simpa [hij] using congrFun h i)
    have e : (fun k => incA D ((Pi.single i 1 + Pi.single j 1 : Fin V.rank → ℚ) k : ℚ)) =
        Pi.single i 1 + Pi.single j 1 := by
      funext k
      simp only [Pi.add_apply, Rat.cast_add, map_add, Pi.single_apply, apply_ite (Rat.cast : ℚ → D.host.E), Rat.cast_one,
        Rat.cast_zero, apply_ite (incA D), map_one, map_zero]
    rwa [e] at this

theorem mt_mul (V : HSp D) (g g' : GA D V) :
    Formalism.L2.Theta.mt V (g * g') = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g' := rfl

theorem mt_inj (V : HSp D) {g g' : GA D V} (h : Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V g') : g = g' :=
  Subtype.ext (Units.ext h)

theorem mem_GinfC (V : HSp D) (g : GA D V) : g ∈ GinfC V ↔ (Formalism.L2.Theta.mt V g).map (finPart D) = 1 :=
  ⟨fun h => congrArg Units.val (MonoidHom.mem_ker.1 h), fun h => MonoidHom.mem_ker.2 (Units.ext h)⟩

theorem mem_center_of {V : HSp D} {g : GA D V} {c : AE D} (e : Formalism.L2.Theta.mt V g = c • 1) :
    g ∈ Subgroup.center (GA D V) :=
  Subgroup.mem_center_iff.2 fun h => mt_inj V <|
    (mt_mul V h g).trans (((congrArg (Formalism.L2.Theta.mt V h * ·) e).trans ((mul_scalar_comm _ c).trans
      (congrArg (· * Formalism.L2.Theta.mt V h) e).symm)).trans (mt_mul V g h).symm)

theorem exists_central_realPoint_same_scalar_other_group (A : HSp D) {S : HSp D} {y : DefSp S} (hy : y.Is) {b : GA D S} (hb : b ∈ GinfC S)
    (hc : b ∈ Subgroup.center (GA D S)) (i₀ : Fin S.rank) :
    ∃ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) ∧ ∃ c c' : AE D, c * c' = 1 ∧ Formalism.L2.Theta.mt S b = c • 1 ∧ Formalism.L2.Theta.mt A a⁻¹ = c' • 1 := by
  obtain ⟨c, e⟩ : ∃ c : AE D, Formalism.L2.Theta.mt S b = c • 1 := ⟨_, mt_central hy hc i₀⟩
  have hu : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt S b) * JR (AF D.host.F) S.gram * Formalism.L2.Theta.mt S b =
      JR (AF D.host.F) S.gram := (show HR (AF D.host.F) D.sp.cm.sig S.gram from b).2
  have h1 := norm_unit hy (Pi.single i₀ 1) (by simp)
  have e1 : (fun k => incA D ((Pi.single i₀ 1 : Fin S.rank → ℚ) k : ℚ)) = Pi.single i₀ 1 := by
    funext k
    by_cases hk : k = i₀ <;> simp [hk]
  rw [e1] at h1
  rw [e] at hu
  have hcc : c * cA D c = 1 := mul_conj_eq_one _ _ i₀ h1 hu
  have h2 : finPart D c = 1 := by
    refine map_eq_one_of (finPart D) i₀ ?_
    rw [← e]
    exact (mem_GinfC S b).1 hb
  obtain ⟨g, hg, g1, g2⟩ := exists_scalar (cA D) (JR (AF D.host.F) A.gram) hcc
  obtain ⟨a, a1, a2⟩ : ∃ a : GA D A, Formalism.L2.Theta.mt A a = c • 1 ∧ Formalism.L2.Theta.mt A a⁻¹ = cA D c • 1 :=
    ⟨(⟨g, hg⟩ : HR (AF D.host.F) D.sp.cm.sig A.gram), g1, g2⟩
  refine ⟨a, ?_, ?_, c, cA D c, hcc, e, a2⟩
  · refine (mem_GinfC A a).2 ?_
    rw [a1]
    exact (map_smul_one _ c).trans (by rw [h2, one_smul])
  · exact mem_center_of a1

theorem compAt_smul_one (θ : InfFam D) (τ : D.what₂.Tau) (n : ℕ) (c : AE D) :
    compAt θ τ (c • (1 : Matrix (Fin n) (Fin n) (AE D))) = θ τ (infPart D c) • 1 := by
  ext i j
  simp only [compAt, map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply, apply_ite (infPart D),
    apply_ite (θ τ), map_one, map_zero]

theorem weilOperator_equal_scalars_acts_by_scalar_fock {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {A S : HSp D} {x : DefSp A} {y : DefSp S}
    (hx : x.Is) (hy : y.Is) {k : KerDat A S} (hk : k.Is ψ θ x y) {a : GA D A} {b : GA D S} {c c' : AE D}
    (hcc : c * c' = 1) (hb : Formalism.L2.Theta.mt S b = c • 1) (ha : Formalism.L2.Theta.mt A a⁻¹ = c' • 1) :
    ∃ l : ℂ, ∀ P, k.om (a, b) (pureTensorO ψ θ A S x.s y.s x.B y.B k.vac P) =
      l • pureTensorO ψ θ A S x.s y.s x.B y.B k.vac P := by
  obtain ⟨χA, χS, hW⟩ := hk.weil
  have h3 : ∀ w, actO A S a b w = w := fun w => by
    unfold actO
    rw [hb, ha, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm, hcc, one_smul]
  have h4 : ∀ τ (z : Matrix (Fin S.rank) (Fin A.rank) ℂ), compAt θ τ (Formalism.L2.Theta.mt S b) * z * compAt θ τ (Formalism.L2.Theta.mt A a⁻¹) = z :=
    fun τ z => by
      rw [hb, ha, compAt_smul_one, compAt_smul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, ← map_mul, ← map_mul, mul_comm, hcc, map_one, map_one, one_smul]
  have hv := GlobalTheory.WeilVacMove.isVacO_om D ψ θ A S χA χS k.om hW hθ x.s x.s y.s y.s x.L x.L y.L y.L a b
    (fun τ => by rcases hx.pm τ with e | e <;> simp [e]) (fun τ => by rcases hy.pm τ with e | e <;> simp [e])
    (fun u => ⟨fun h => ⟨u, h, (h3 u).symm⟩, fun ⟨u₀, h, e⟩ => by rwa [e, h3]⟩) k.vac hk.vac
  obtain ⟨l, -, hl⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ hW.std hθ A S x.s y.s hx.sig hy.sig hx.cart hy.cart x.L y.L
    hx.sd hy.sd _ _ hk.vac hv
  refine ⟨l, fun P => ?_⟩
  rw [← GlobalTheory.FiniteFock.pureTensorO_smul, ← hl]
  open GlobalTheory.OrientedHeis in
  refine (pureTensorL_intertwine (IsThetaFunO ψ A S) theta_zero (fun _ _ => theta_add) (fun c _ => theta_smul c) _ _
    (k.om (a, b)) (fun i f hf => ?_) k.vac hk.vac.2.theta P).2
  obtain ⟨τ, i, j⟩ := i
  open GlobalTheory.OrientedHeis in
  refine ⟨theta_smul _ (theta_sub (theta_dRho hθ hW.std τ _ hf) (theta_smul _ (theta_dRho hθ hW.std τ _ hf))), ?_⟩
  simp only [aPlusAll, aPlus, crea]
  rw [map_smul, map_sub, map_smul, GlobalTheory.OrientedHeis.om_dRho hW hθ a b τ _ hf, GlobalTheory.OrientedHeis.om_dRho hW hθ a b τ _ hf,
    h4, h4]

theorem centre_target_char : ∀ (D : D7), BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (χ₁ : GA D A → ℂ) (C₁ : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₁ → (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k.om (a, 1) (fun u => C₁ u v) = χ₁ a • fun u => C₁ u v) → ∃ χ₃ : GA D S → ℂ, ∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ v, k.om (1, b) (fun u => C₁ u v) = χ₃ b • fun u => C₁ u v := by
  intro D _ hC _ ψ θ hθ A S A' x y z hx hy _ k k' hk _ χ₁ C₁ hV hχ
  obtain ⟨W, -, hW⟩ := hC ψ θ hθ A S x y hx hy k hk χ₁
  have key : ∀ b : GA D S, ∃ t : ℂ, b ∈ GinfC S → b ∈ Subgroup.center (GA D S) →
      ∀ v, k.om (1, b) (fun u => C₁ u v) = t • fun u => C₁ u v := by
    intro b
    by_cases hb : b ∈ GinfC S ∧ b ∈ Subgroup.center (GA D S)
    · rcases isEmpty_or_nonempty (Fin S.rank) with h0 | ⟨⟨i₀⟩⟩
      · have e : b = 1 := Subtype.ext (Units.ext (Subsingleton.elim _ _))
        refine ⟨1, fun _ _ v => ?_⟩
        rw [e, Prod.mk_one_one, map_one, one_smul, Module.End.one_apply]
      · obtain ⟨a, ha, hac, c, c', hcc, e1, e2⟩ := exists_central_realPoint_same_scalar_other_group A hy hb.1 hb.2 i₀
        obtain ⟨l, hl⟩ := weilOperator_equal_scalars_acts_by_scalar_fock hθ hx hy hk hcc e1 e2
        refine ⟨l * χ₁ a⁻¹, fun _ _ v => ?_⟩
        obtain ⟨P, -, hP⟩ := hW _ (hV.left v).1 (hV.left v).2 fun a ha hac => hχ a ha hac v
        have h1 := hl P
        rw [← hP] at h1
        have e : ((1, b) : GA D A × GA D S) = (a⁻¹, 1) * (a, b) := by simp
        rw [e, map_mul, Module.End.mul_apply, h1, map_smul, hχ _ (inv_mem ha) (inv_mem hac), smul_smul]
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hb⟩
  choose χ₃ h using key
  exact ⟨χ₃, h⟩

end GlobalTheory.CentreTarget

end
