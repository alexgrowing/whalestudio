import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndSt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.HarmonicChartValues
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.TotalDegreeEqOfMemHarmA
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicSumTriangularFrameChange
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InvariantOperatorValueTriangularChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsTriangularReframeExistsAndUnique
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqZeroOfFischSelf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NabUniqCompare

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem chartVal_eq [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
    (C : ChartAt Xo c y) (k : ℕ) {n : ℕ} (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S)
    (P : MvPolynomial (LtN Dw n) c.F) :
    Formalism.MainNotions.ModuliIntegralCharts.H1.chartVal C k f P = GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues.chartVal Xo c C k f P := rfl

theorem pderiv_swap {σ R : Type} [CommRing R] (i j : σ) (P : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hp, MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem isHarmonic_iff_cmType {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) :
    IsHarmonic c P ↔ P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) := by
  have e : P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) ↔
      ∀ τ : E →+* ℂ, InPsi H τ → ∀ (i : Fin (Dw.mult τ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))),
        ∑ b : Fin n, MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
          (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0 := by
    simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker, lap,
      LinearMap.sum_apply, LinearMap.smul_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  rw [e]
  refine ⟨fun h τ _ => h τ, fun h τ => ?_⟩
  by_cases hτ : InPsi H τ
  · exact h τ hτ
  · have key : ∀ σ : E →+* ℂ, σ = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) →
        ∀ (i : Fin (Dw.mult σ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))),
        ∑ b : Fin n, MvPolynomial.pderiv (⟨σ, i, b⟩ : LtN Dw n)
          (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0 := by
      rintro σ rfl i i'
      rw [← h _ ((GlobalTheory.ThetaRuleCheck.inPsi_conjugate_iff τ).2 hτ) i' i]
      exact Finset.sum_congr rfl fun b _ => pderiv_swap _ _ _
    exact key τ (by ext x; simp)

def IsTopHarmonic {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  IsHarmonic c P ∧ RowInv Dw.mult n c.F P ∧
    ∃ a : (E →+* ℂ) × ℕ → ℕ, RowDeg Dw.mult n c.F (fun τ i => a (τ, i)) P

theorem mem_harmA_iff {n : ℕ} (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) :
    P ∈ harmA c a n ↔ IsHarmonic c P ∧ RowInv Dw.mult n c.F P ∧
      RowDeg Dw.mult n c.F (fun τ i => a (τ, i)) P ∧ ∀ m, IsIntegral ℤ (P.coeff m) := by
  rw [isHarmonic_iff_cmType]
  exact ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩

def colSumL {S : Type} [CommRing S] [Algebra c.F S] {n : ℕ} (v : Fin n → (Lt1 Dw →₀ ℕ) → S) :
    MvPolynomial (LtN Dw n) c.F →ₗ[c.F] S :=
  (MvPolynomial.basisMonomials (LtN Dw n) c.F).constr c.F fun m => ∏ b : Fin n, v b (colOf m b)

theorem colSumL_apply {S : Type} [CommRing S] [Algebra c.F S] {n : ℕ} (v : Fin n → (Lt1 Dw →₀ ℕ) → S)
    (P : MvPolynomial (LtN Dw n) c.F) : colSumL c v P = colSum c v P := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum, colSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : (MvPolynomial.monomial m (P.coeff m) : MvPolynomial (LtN Dw n) c.F) =
      P.coeff m • MvPolynomial.basisMonomials (LtN Dw n) c.F m := by
    simp [MvPolynomial.smul_monomial]
  rw [this, map_smul, colSumL, Module.Basis.constr_basis, Algebra.smul_def]

def UniqueOn (Q : ∀ n : ℕ, MvPolynomial (LtN Dw n) c.F → Prop) : Prop :=
  ∀ [StarRing (𝓞 E)] (nab nab' : NabV Xo c), IsNab Xo c nab → IsNab Xo c nab' →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k n : ℕ)
      (F : Fin n → SecAt Xo c y k) (P : MvPolynomial (LtN Dw n) c.F), Q n P →
        sysVal Xo c nab y k F P = sysVal Xo c nab' y k F P

theorem nabUnique_iff : NabUnique Xo c ↔ UniqueOn Xo c fun _ P => IsHarmonic c P := Iff.rfl

theorem UniqueOn.mono {Q Q' : ∀ n : ℕ, MvPolynomial (LtN Dw n) c.F → Prop} (h : UniqueOn Xo c Q)
    (hQ : ∀ n P, Q' n P → Q n P) : UniqueOn Xo c Q' :=
  fun nab nab' h1 h2 S _ _ y k n F P hP => h nab nab' h1 h2 S y k n F P (hQ n P hP)

theorem uniqueOn_span_iff (Q : ∀ n : ℕ, MvPolynomial (LtN Dw n) c.F → Prop) :
    (UniqueOn Xo c fun n P => P ∈ Submodule.span c.F {P' | Q n P'}) ↔ UniqueOn Xo c Q := by
  refine ⟨fun h => h.mono Xo c fun n P hP => Submodule.subset_span hP, ?_⟩
  intro h _ nab nab' h1 h2 S _ _ y k n F P hP
  unfold sysVal
  rw [← colSumL_apply, ← colSumL_apply]
  refine LinearMap.eqOn_span ?_ hP
  intro P' hP'
  rw [colSumL_apply, colSumL_apply]
  exact h nab nab' h1 h2 S y k n F P' hP'

theorem span_harmA_eq (n : ℕ) :
    Submodule.span c.F {P : MvPolynomial (LtN Dw n) c.F | ∃ a, P ∈ harmA c a n} =
      Submodule.span c.F {P | IsTopHarmonic c P} := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    rintro P ⟨a, ha⟩
    rw [mem_harmA_iff] at ha
    exact ⟨ha.1, ha.2.1, a, ha.2.2.1⟩
  · refine Submodule.span_le.2 ?_
    rintro P ⟨h1, h2, a, h3⟩
    obtain ⟨N, hN, hP, -⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P
      ⟨(isHarmonic_iff_cmType c P).1 h1, h2, h3⟩
    have hN' : (N : c.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have := Submodule.smul_mem _ (N : c.F)⁻¹ (Submodule.subset_span
      (s := {P : MvPolynomial (LtN Dw n) c.F | ∃ a, P ∈ harmA c a n}) ⟨a, hP⟩)
    rwa [inv_smul_smul₀ hN'] at this

theorem thExprUniqSt_iff_harmA : Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), UniqueOn Xo c fun n P => ∃ a, P ∈ harmA c a n := by
  constructor
  · rintro h E _ _ _ H Dw l Xo c _ nab nab' h1 h2 S _ _ y k n F P ⟨a, ha⟩
    letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
    exact h E H Dw l Xo c nab nab' h1 h2 S y k n F a P ha
  · intro h E _ _ _ H Dw l Xo c _ nab nab' h1 h2 S _ _ _ y k n F a P ha
    exact h E H Dw l Xo c nab nab' h1 h2 S y k n F P ⟨a, ha⟩

theorem thExprUniqSt_iff_span : Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l),
      UniqueOn Xo c fun n P => P ∈ Submodule.span c.F {P' : MvPolynomial (LtN Dw n) c.F | IsTopHarmonic c P'} := by
  rw [thExprUniqSt_iff_harmA]
  refine forall₅_congr fun E _ _ _ H => forall₄_congr fun Dw l Xo c => ?_
  rw [← uniqueOn_span_iff]
  simp only [span_harmA_eq]

theorem thExprUniqSt_iff_top : Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), UniqueOn Xo c fun _ P => IsTopHarmonic c P := by
  rw [thExprUniqSt_iff_span]
  exact forall₅_congr fun E _ _ _ H => forall₄_congr fun Dw l Xo c => uniqueOn_span_iff Xo c _

theorem thExprUniqSt_of_nabUnique
    (h : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), NabUnique Xo c) : Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt :=
  thExprUniqSt_iff_top.2 fun E _ _ _ H Dw l Xo c =>
    @UniqueOn.mono E _ _ _ H Dw l Xo c (fun _ P => IsHarmonic c P) _ (@h E _ _ _ H Dw l Xo c) fun _ _ hP => hP.1

theorem X_later_harmonic_not_mem_span {n : ℕ} (τ : E →+* ℂ) (i i' : Fin (Dw.mult τ)) (h : i' < i) (b : Fin n) :
    IsHarmonic c (MvPolynomial.X ⟨τ, i, b⟩ : MvPolynomial (LtN Dw n) c.F) ∧
      (MvPolynomial.X ⟨τ, i, b⟩ : MvPolynomial (LtN Dw n) c.F) ∉
        Submodule.span c.F {P' : MvPolynomial (LtN Dw n) c.F | IsTopHarmonic c P'} := by
  classical
  constructor
  · intro σ j j'
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs <;> simp
  · intro hP
    have := LinearMap.eqOn_span (f := (rowShift Dw.mult n c.F τ i i' 1).toLinearMap) (g := LinearMap.id)
      (fun P' hP' => hP'.2.1 τ i i' h 1) hP
    simp only [rowShift, AlgHom.toLinearMap_apply, MvPolynomial.aeval_X, LinearMap.id_apply] at this
    rw [if_pos ⟨b, rfl⟩] at this
    simp at this

section Reframe

open GlobalTheory.RowSpan GlobalTheory.RowTriangular ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ in
open scoped TensorProduct in

theorem colSum_nabVal_rowAct [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {d : ℕ}
    (B : Germ.FB S d (𝓞 E)) (hg : Germ.PS S 2 d) (k : ℕ) {n : ℕ} (f : Fin n → MvPowerSeries (Fin 1 × Fin d) S)
    (u u' : Lt1 Dw → Fin d → S) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) c.F)
    (hu : ∀ τ i e, u' ⟨τ, i⟩ e = ∑ j, algebraMap c.F S (g τ i j) * u ⟨τ, j⟩ e)
    (P : MvPolynomial (LtN Dw n) c.F) :
    colSum c (fun b α => B.nabVal S hg H.w0 k (f b) u' (MvPolynomial.monomial α 1)) P =
      colSum c (fun b α => B.nabVal S hg H.w0 k (f b) u (MvPolynomial.monomial α 1)) (rowAct g P) := by
  classical
  let Ψ : MvPolynomial (Lt1 Dw) S →ₐ[S] Module.End S (PS S 1 d) :=
    GlobalTheory.Wick.commEval S (fun ℓ => dEnd (B.FK S) (u ℓ)) fun i j => LinearMap.ext fun g => by
      simp only [Module.End.mul_apply, dEnd_apply]
      exact GlobalTheory.FormalConnection.invariantDerivations_commute_formal_connection S d (𝓞 E) S B _ _ g
  have hΨ : ∀ ℓ, Ψ (MvPolynomial.X ℓ) = dEnd (B.FK S) (u ℓ) := fun ℓ => GlobalTheory.Wick.commEval_X _ _ ℓ
  let s : Fin n → PS S 1 d := fun b => f b * FB.expS S ((k : S) • B.hL S hg H.w0)
  let lam : Fin n → MvPolynomial (Lt1 Dw) S →ₗ[S] S := fun b =>
    (MvPowerSeries.coeff 0) ∘ₗ (LinearMap.applyₗ (s b)) ∘ₗ Ψ.toLinearMap
  let T := ⨂[S] _ : Fin n, MvPolynomial (Lt1 Dw) S
  let sg : Fin n → (MvPolynomial (Lt1 Dw) S →ₐ[S] T) := fun b =>
    PiTensorProduct.singleAlgHom (R := S) (A := fun _ : Fin n => MvPolynomial (Lt1 Dw) S) b
  let φ : c.F →+* T := (algebraMap S T).comp (algebraMap c.F S)
  have key : ∀ (w : Lt1 Dw → Fin d → S) (x : Lt1 Dw → MvPolynomial (Lt1 Dw) S),
      (∀ ℓ, Ψ (x ℓ) = dEnd (B.FK S) (w ℓ)) → ∀ Q : MvPolynomial (LtN Dw n) c.F,
      colSum c (fun b α => B.nabVal S hg H.w0 k (f b) w (MvPolynomial.monomial α 1)) Q =
      prodForm lam (MvPolynomial.eval₂Hom φ (fun ℓ : LtN Dw n => sg ℓ.2.2 (x ⟨ℓ.1, ℓ.2.1⟩)) Q) := by
    intro w x hx Q
    rw [colSum, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq', map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have e : ∏ ℓ : LtN Dw n, sg ℓ.2.2 (x ⟨ℓ.1, ℓ.2.1⟩) ^ m ℓ = ∏ b, sg b (∏ ℓ, x ℓ ^ colOf m b ℓ) := by
      simp only [map_prod, map_pow]
      rw [Finset.prod_comm]
      simp only [Fintype.prod_sigma, Fintype.prod_prod_type]
      rfl
    rw [e, RingHom.comp_apply, ← Algebra.smul_def (A := T), map_smul, prodForm_prod, smul_eq_mul]
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [FB.nabVal, dpoly_monomial, dmon_eq _ Ψ w x hx]
    rfl
  rw [key u MvPolynomial.X hΨ,
    key u' (fun ℓ => ∑ j, algebraMap c.F S (g ℓ.1 ℓ.2 j) • MvPolynomial.X ⟨ℓ.1, j⟩) (fun ℓ => by
      rw [dEnd_comb (B.FK S) (fun j => algebraMap c.F S (g ℓ.1 ℓ.2 j)) (fun j => u ⟨ℓ.1, j⟩) (u' ℓ) (hu ℓ.1 ℓ.2)]
      simp only [map_sum, map_smul, hΨ])]
  congr 1
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ℓ hp =>
    rw [map_mul, map_mul, map_mul, hp, rowAct_X]
    congr 1
    simp only [MvPolynomial.eval₂Hom_X', map_sum, map_mul, MvPolynomial.eval₂Hom_C, map_smul]
    exact Finset.sum_congr rfl fun j _ => Algebra.smul_def (A := T) _ _

theorem basis_of_isUnit {T : Type} [Fintype T] {r : T → ℕ} {S : Type} [CommRing S] {d : ℕ}
    (u : (Σ τ : T, Fin (r τ)) → Fin d → S) (g : ∀ τ : T, Matrix (Fin (r τ)) (Fin (r τ)) S)
    (hdet : ∀ τ, IsUnit (g τ).det)
    (hb : ∀ v : Fin d → S, ∃! a : (Σ τ : T, Fin (r τ)) → S, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) (v : Fin d → S) :
    ∃! a : (Σ τ : T, Fin (r τ)) → S, ∀ e, ∑ ℓ, a ℓ * (∑ j, g ℓ.1 ℓ.2 j * u ⟨ℓ.1, j⟩ e) = v e := by
  classical
  have key : ∀ (a : (Σ τ : T, Fin (r τ)) → S) e, ∑ ℓ, a ℓ * (∑ j, g ℓ.1 ℓ.2 j * u ⟨ℓ.1, j⟩ e) =
      ∑ ℓ : (Σ τ : T, Fin (r τ)), Matrix.vecMul (fun i => a ⟨ℓ.1, i⟩) (g ℓ.1) ℓ.2 * u ℓ e := by
    intro a e
    rw [Fintype.sum_sigma, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
    simp only [_root_.mul_assoc]
    exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (i j : Fin (r τ)) => a ⟨τ, i⟩ * (g τ i j * u ⟨τ, j⟩ e))
  simp only [key]
  obtain ⟨b, hb1, hb2⟩ := hb v
  refine ⟨fun ℓ => Matrix.vecMul (fun i => b ⟨ℓ.1, i⟩) (g ℓ.1)⁻¹ ℓ.2, fun e => ?_, fun a ha => ?_⟩
  · rw [← hb1 e]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    congr 1
    show Matrix.vecMul (Matrix.vecMul (fun i => b ⟨ℓ.1, i⟩) (g ℓ.1)⁻¹) _ _ = _
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hdet _), Matrix.vecMul_one]
  · have := hb2 _ ha
    subst this
    funext ℓ
    show _ = Matrix.vecMul (Matrix.vecMul (fun i => a ⟨ℓ.1, i⟩) (g ℓ.1)) _ _
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (hdet _), Matrix.vecMul_one]

abbrev ValAt {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Type :=
  ∀ k : ℤ, LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)) → (Lt1 Dw →₀ ℕ) → S

def PinAt [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : ValAt Xo c y) : Prop :=
  ∀ [Algebra ℚ S], ∃ C : ChartAt Xo c y,
    (∀ (k : ℕ) (F : SecAt Xo c y k), ∃ f, IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) ∧
    ∀ (k : ℕ) (F : SecAt Xo c y k) (f : MvPowerSeries (Fin 1 × Fin C.d) S),
      IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
        ∀ α : Lt1 Dw →₀ ℕ, v k F α = C.B.nabVal S C.h H.w0 k f C.uvec (MvPolynomial.monomial α 1)

theorem exists_isNab_eq [StarRing (𝓞 E)] {nab : NabV Xo c} (h : IsNab Xo c nab) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) (v : ValAt Xo c y) (hv : PinAt Xo c y v) :
    ∃ nab₁ : NabV Xo c, IsNab Xo c nab₁ ∧ nab₁ y = v := by
  classical
  let Pt : Type 1 := Σ (R : Type) (_ : CommRing R) (_ : Algebra c.F R), FrPt Xo c R
  let Val : Pt → Type := fun p => @ValAt E _ _ _ H Dw l Xo c p.1 p.2.1 p.2.2.1 p.2.2.2
  let Pin : ∀ p : Pt, Val p → Prop := fun p => @PinAt E _ _ _ H Dw l Xo c _ p.1 p.2.1 p.2.2.1 p.2.2.2
  let N₀ : ∀ p : Pt, Val p := fun p => @nab p.1 p.2.1 p.2.2.1 p.2.2.2
  let N₁ : ∀ p : Pt, Val p := Function.update N₀ ⟨S, _, _, y⟩ v
  have hN : ∀ p, Pin p (N₁ p) := (Function.forall_update_iff N₀ Pin).2
    ⟨hv, fun p _ _ => @h.2 p.1 p.2.1 p.2.2.1 _ p.2.2.2⟩
  exact ⟨fun {R} _ _ z => N₁ ⟨R, _, _, z⟩, ⟨h.1, fun R _ _ _ z => hN ⟨R, _, _, z⟩⟩,
    Function.update_self _ _ _⟩

open GlobalTheory.RowSpan in

theorem exists_isNab_rowAct [StarRing (𝓞 E)] {nab : NabV Xo c} (h : IsNab Xo c nab) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) (ho u' h1 h2 h3 s' h4)
    (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) c.F) (hdet : ∀ τ, IsUnit (g τ).det)
    (hcomb : ∀ τ i, IsCombAt y.x (y.u τ) (fun j => algebraMap c.F S (g τ i j)) (u' τ i)) :
    ∃ nab₁ : NabV Xo c, IsNab Xo c nab₁ ∧ ∀ (k n : ℕ) (F : Fin n → SecAt Xo c y k)
      (P : MvPolynomial (LtN Dw n) c.F), sysVal Xo c nab y k F (rowAct g P) =
        sysVal Xo c nab₁ (⟨y.x, ho, u', h1, h2, h3, s', h4⟩ : FrPt Xo c S) k F P := by
  set y' : FrPt Xo c S := ⟨y.x, ho, u', h1, h2, h3, s', h4⟩ with hy'
  let one : (Lt1 Dw →₀ ℕ) → (LtN Dw 1 →₀ ℕ) := fun α => Finsupp.equivFunOnFinite.symm fun ℓ => α ⟨ℓ.1, ℓ.2.1⟩
  have hone : ∀ (w : (Lt1 Dw →₀ ℕ) → S) α,
      colSum c (fun _ : Fin 1 => w) (MvPolynomial.monomial (one α) 1) = w α := by
    intro w α
    classical
    rw [colSum, MvPolynomial.support_monomial, if_neg one_ne_zero]
    simp only [Finset.sum_singleton, MvPolynomial.coeff_monomial, if_true, map_one, one_mul, Fin.prod_univ_one]
    congr 1
    ext ℓ
    rfl
  let v : ValAt Xo c y' := fun k F α =>
    colSum c (fun _ : Fin 1 => nab y k F) (rowAct g (MvPolynomial.monomial (one α) 1))
  have hv : ∀ [Algebra ℚ S] (C : ChartAt Xo c y) (k : ℕ) (F : SecAt Xo c y k)
      (f : MvPowerSeries (Fin 1 × Fin C.d) S),
      (∀ α, nab y k F α = C.B.nabVal S C.h H.w0 k f C.uvec (MvPolynomial.monomial α 1)) →
      ∀ α, v k F α = C.B.nabVal S C.h H.w0 k f
        (fun ℓ e => ∑ j, algebraMap c.F S (g ℓ.1 ℓ.2 j) * C.uvec ⟨ℓ.1, j⟩ e) (MvPolynomial.monomial α 1) := by
    intro _ C k F f hf α
    have := colSum_nabVal_rowAct c C.B C.h k (fun _ : Fin 1 => f) C.uvec
      (fun ℓ e => ∑ j, algebraMap c.F S (g ℓ.1 ℓ.2 j) * C.uvec ⟨ℓ.1, j⟩ e) g (fun _ _ _ => rfl)
      (MvPolynomial.monomial (one α) 1)
    rw [hone] at this
    rw [this, ← funext hf]
  have hpin : PinAt Xo c y' v := by
    intro _
    obtain ⟨C, hex, hval⟩ := h.2 S y
    let uv : Lt1 Dw → Fin C.d → S := fun ℓ e => ∑ j, algebraMap c.F S (g ℓ.1 ℓ.2 j) * C.uvec ⟨ℓ.1, j⟩ e
    let D : ChartAt Xo c y' :=
      ⟨C.d, C.B, uv, C.x, C.e, C.wP, C.h,
        ⟨C.chart.zero, C.chart.trunc, C.chart.law, C.chart.act, fun ℓ => by
          have := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x _
            (fun j => GlobalTheory.TriangularFrame.isTanAt_jetTan y.x (C.x 1) (C.chart.zero 1) ((0 : Fin 1), j)) (y.u ℓ.1)
            (Matrix.of fun e j => C.uvec ⟨ℓ.1, j⟩ e) (fun j => algebraMap c.F S (g ℓ.1 ℓ.2 j)) (u' ℓ.1 ℓ.2)
            (fun i => C.chart.tan ⟨ℓ.1, i⟩) (hcomb ℓ.1 ℓ.2)
          have e : (Matrix.of fun e j => C.uvec ⟨ℓ.1, j⟩ e).mulVec (fun j => algebraMap c.F S (g ℓ.1 ℓ.2 j)) =
              uv ℓ := by
            funext e
            simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, uv]
            exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
          rw [e] at this
          exact this,
          basis_of_isUnit C.uvec (fun τ => (algebraMap c.F S).mapMatrix (g τ))
            (fun τ => by rw [← RingHom.map_det]; exact (hdet τ).map _) C.chart.basis⟩,
        ⟨C.frame.gen, C.frame.ph1, C.frame.ph2, C.frame.sy, C.frame.ad⟩, C.prim, C.gauge, C.rig0⟩
    exact ⟨D, hex, fun k F f hf => hv C k F f (hval k F f hf)⟩
  obtain ⟨nab₁, hn, e⟩ := exists_isNab_eq Xo c h y' v hpin
  refine ⟨nab₁, hn, fun k n F P => ?_⟩
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  obtain ⟨C, hex, hval⟩ := h.2 S y
  choose f hf using fun b => hex k (F b)
  have := colSum_nabVal_rowAct c C.B C.h k f C.uvec
    (fun ℓ e => ∑ j, algebraMap c.F S (g ℓ.1 ℓ.2 j) * C.uvec ⟨ℓ.1, j⟩ e) g (fun _ _ _ => rfl) P
  refine Eq.trans (congrArg (fun w => colSum c w (rowAct g P)) ?_)
    (this.symm.trans (congrArg (fun w => colSum c w P) ?_))
  · funext b α
    exact hval k (F b) (f b) (hf b) α
  · funext b α
    exact (hv C k (F b) (f b) (hval k (F b) (f b) (hf b)) α).symm.trans
      (congrArg (fun w : ValAt Xo c y' => w k (F b) α) e).symm

open GlobalTheory.RowSpan in

theorem uniqueOn_top_iff :
    (UniqueOn Xo c fun _ P => IsTopHarmonic c P) ↔ UniqueOn Xo c fun _ P => IsHarmonic c P := by
  refine ⟨fun h => ?_, fun h => h.mono Xo c fun _ _ hP => hP.1⟩
  intro _ nab nab' h1 h2 S _ _ y k n F P hP
  let U : Submodule c.F (MvPolynomial (LtN Dw n) c.F) :=
    ⨅ (nab : NabV Xo c) (nab' : NabV Xo c) (_ : IsNab Xo c nab) (_ : IsNab Xo c nab') (y : FrPt Xo c S)
      (F : Fin n → SecAt Xo c y k),
      LinearMap.eqLocus (colSumL c fun b α => nab y k (F b) α) (colSumL c fun b α => nab' y k (F b) α)
  have hU : ∀ Q, Q ∈ U ↔ ∀ (nab nab' : NabV Xo c), IsNab Xo c nab → IsNab Xo c nab' → ∀ (y : FrPt Xo c S)
      (F : Fin n → SecAt Xo c y k), sysVal Xo c nab y k F Q = sysVal Xo c nab' y k F Q := by
    intro Q
    simp only [U, Submodule.mem_iInf, LinearMap.mem_eqLocus, colSumL_apply, sysVal]
  refine (hU P).1 (harmK_le_of_top (U := U) ComplexEmbedding.conjugate (InPsi H) ?_ ?_
    ((isHarmonic_iff_cmType c P).1 hP)) nab nab' h1 h2 y F
  · intro g hg Q hQ
    rw [hU] at hQ ⊢
    intro nab nab' h1 h2 y F
    obtain ⟨⟨x', ho, u', e1, e2, e3, s', e4⟩, hx, hcomb⟩ := GlobalTheory.Reg.ReframeEx.exists_reframe y
      (fun τ => ((algebraMap c.F S).mapMatrix (g τ)).transpose)
      (fun τ => by rw [Matrix.det_transpose, ← RingHom.map_det]; exact (hg τ).map _)
    dsimp only at hx
    subst hx
    obtain ⟨n₁, hn₁, v₁⟩ := exists_isNab_rowAct Xo c h1 y ho u' e1 e2 e3 s' e4 g hg hcomb
    obtain ⟨n₂, hn₂, v₂⟩ := exists_isNab_rowAct Xo c h2 y ho u' e1 e2 e3 s' e4 g hg hcomb
    rw [v₁, v₂]
    exact hQ n₁ n₂ hn₁ hn₂ ⟨y.x, ho, u', e1, e2, e3, s', e4⟩ F
  · rintro Q hQ hI ⟨a, ha⟩
    exact (hU Q).2 fun nab nab' h1 h2 y F => h nab nab' h1 h2 S y k n F Q
      ⟨(isHarmonic_iff_cmType c Q).2 hQ, hI, fun p => a p.1 p.2, ha⟩

end Reframe

theorem thExprUniqSt_iff_nabUnique : Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), NabUnique Xo c :=
  thExprUniqSt_iff_top.trans (forall₅_congr fun _ _ _ _ _ => forall₄_congr fun _ _ Xo c => uniqueOn_top_iff Xo c)

theorem comparison :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
      (y : FrPt Xo c S) (C : ChartAt Xo c y) (k n : ℕ) (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S)
      (P : MvPolynomial (LtN Dw n) c.F),
      Formalism.MainNotions.ModuliIntegralCharts.H1.chartVal C k f P = GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues.chartVal Xo c C k f P) ∧
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), NabUnique Xo c ↔ UniqueOn Xo c fun n P => ∃ a, P ∈ harmA c a n) ∧
    (Formalism.MainNotions.ModuliIntegralCharts.H1.ThExprUniqSt ↔
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
        (Xo : Moduli Dw l) (c : Coeff l), NabUnique Xo c) :=
  ⟨fun _ _ _ _ _ _ _ Xo c _ _ _ _ _ _ C k _ f P => chartVal_eq Xo c C k f P,
    fun _ _ _ _ _ _ _ Xo c => by
      rw [nabUnique_iff, ← uniqueOn_top_iff, ← uniqueOn_span_iff,
        ← uniqueOn_span_iff Xo c fun n P => ∃ a, P ∈ harmA c a n]
      simp only [span_harmA_eq],
    thExprUniqSt_iff_nabUnique⟩

end GlobalTheory.NabUniqCompare
