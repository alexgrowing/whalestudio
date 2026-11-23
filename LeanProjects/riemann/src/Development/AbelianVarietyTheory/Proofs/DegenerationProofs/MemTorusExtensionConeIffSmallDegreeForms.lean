import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomogenisation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VanishingIdealConePrimeHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByWeightZeroStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormVanishesOfTorsionTorusExtensionStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.FibCone

theorem hilb_eq_finrank_quotPiece {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) :
    hilb C d = Module.finrank k (quotPiece (MvPolynomial.vanishingIdeal k C) (d : ℤ)) := by
  rw [quotPiece_natCast]
  let ev : MvPolynomial J k →ₐ[k] (C → k) :=
    AlgHom.pi fun v : C => MvPolynomial.aeval v.1
  have hker : ∀ a ∈ MvPolynomial.vanishingIdeal k C, ev a = 0 := fun a ha =>
    funext fun v => ha v.1 v.2
  let φ := Ideal.Quotient.liftₐ (MvPolynomial.vanishingIdeal k C) ev hker
  have hφ : Function.Injective φ.toLinearMap := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 fun v hv => congrFun (show ev x = 0 from hx) ⟨v, hv⟩
  rw [(Submodule.equivMapOfInjective _ hφ _).finrank_eq, ← Submodule.map_comp]
  rfl

theorem eval_eq_zero_of_hilb_le : (∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J] (C : Set (J → k)) (g N : ℕ), (MvPolynomial.vanishingIdeal k C).IsPrime → (MvPolynomial.vanishingIdeal k C).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) → (∃ i, MvPolynomial.X i ∉ MvPolynomial.vanishingIdeal k C) → ringKrullDim (MvPolynomial J k ⧸ MvPolynomial.vanishingIdeal k C) = (g + 1 : ℕ) → (∀ d, 1 ≤ d → hilb C d ≤ (N * d) ^ g) → ∀ v : J → k, (∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → Pf ∈ MvPolynomial.vanishingIdeal k C → MvPolynomial.eval v Pf = 0) → ∀ Pf ∈ MvPolynomial.vanishingIdeal k C, MvPolynomial.eval v Pf = 0) := by
  intro k _ _ J _ C g N hP hPh hne hdim hb v hv Pf hPf
  by_contra h0
  obtain ⟨d, hd, f, hf, hfd, hfv⟩ :=
    exists_form_degree_le_hilbertDegree_eval_ne_zero hPh hne v ⟨Pf, hPf, h0⟩
  refine hfv (hv d f (hd.trans ?_) hfd hf)
  have hH := isHilbertPoly_idealHilbertPoly hPh
  have hg : (idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).natDegree = g := by
    rw [ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly hPh hne] at hdim
    have := Nat.cast_injective hdim
    omega
  have h1 : 0 ≤ (Polynomial.C ((N : ℚ) ^ g) * Polynomial.X ^ g -
      idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).coeff g := by
    apply coeff_nonneg_of_eventually_eval_nat
    · refine (Polynomial.degree_sub_le _ _).trans (max_le (Polynomial.degree_C_mul_X_pow_le _ _) ?_)
      exact Polynomial.degree_le_of_natDegree_le hg.le
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually hH.eventually_eq,
        Filter.eventually_ge_atTop 1] with n hn h1n
      have := hb n h1n
      rw [hilb_eq_finrank_quotPiece, mul_pow] at this
      rw [Int.cast_natCast] at hn
      rw [Polynomial.eval_sub, Polynomial.eval_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
        ← hn, sub_nonneg]
      exact_mod_cast this
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, _root_.mul_one,
    sub_nonneg] at h1
  have h2 := cast_hilbertDegree hPh
  rw [Polynomial.leadingCoeff, hg] at h2
  have h3 : (hilbertDegree (MvPolynomial.vanishingIdeal k C) : ℚ) ≤ (N : ℚ) ^ g * g.factorial := by
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
  exact_mod_cast h3

theorem isIntegral_G {k : Type} [Field k] (Φ : FibPre k) : IsIntegral Φ.G.left := by
  have h : IsSemiAbelian Φ.G := GlobalTheory.isSemiAbelian_of_isGt _ Φ.E Φ.G ⟨Φ.D⟩
  have := h.smooth
  have := h.geomConnected
  have : GeometricallyIntegral Φ.G.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ Φ.G
  exact GeometricallyIntegral.isIntegral_of_subsingleton Φ.G.hom

theorem exists_ne_zero_of_mem_cone {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) (H : LB X) {J : Type}
    (s : J → H.Sec) (J₀ : Set J) (hH : H.IsLB) (hc : ⨆ i ∈ J₀, Out.nonzeroLocus (s i) = ⊤) (v : J → k)
    (hv : v ∈ cone p H s) : ∃ i ∈ J₀, v i ≠ 0 := by
  obtain ⟨x, -, hx⟩ := hv
  let pt : Sp k := IsLocalRing.closedPoint k
  have hm : x pt ∈ (⨆ i ∈ J₀, Out.nonzeroLocus (s i)) := by rw [hc]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, hi, hm⟩ := hm
  refine ⟨i, hi, ?_⟩
  have hu := (((GlobalTheory.ZH.CrdCalc.crd_calculus X H J s hH).1 k x).2.2 v i hx).2 (by
    intro y _
    have : y = pt := Subsingleton.elim (α := PrimeSpectrum k) _ _
    subst this
    exact hm)
  exact hu.ne_zero

theorem mem_cone_iff : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → SmoothOfRelativeDimension g Φ.G.hom → (∀ d, 1 ≤ d → hilb (cone Φ.G.hom (Φ.H 1) F) d ≤ (N * d) ^ g) → ∀ v : J → k, v ∈ cone Φ.G.hom (Φ.H 1) F ↔ ((∃ i, cls i = 0 ∧ v i ≠ 0) ∧ ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ w, Crd (Φ.H 1) F x.left w ∧ MvPolynomial.eval w Pf = 0) → MvPolynomial.eval v Pf = 0)) := by
  intro hL hL2 k _ _ Φ g N N' q J _ cls F π hB hG hg hN hsm hh v
  have hH := Φ.H_isLB 1
  have himm := GlobalTheory.T.immBy_weight_zero' hL hL2 k Φ g N N' q J cls F π hB hG hg
  constructor
  · intro hv
    exact ⟨exists_ne_zero_of_mem_cone _ _ F _ hH himm.1 v hv, fun d Pf hd hP ht =>
      GlobalTheory.T.form_vanishes_of_torsion_torusExtension hL hL2 k Φ g N N' q J cls F π hB hG hg hN d Pf hd hP ht v hv⟩
  · rintro ⟨h0, hv⟩
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.vanishing_ideal_cone_prime_homogeneous k _ Φ.G.hom (Φ.H 1) J F _ hH himm (isIntegral_G Φ) g hsm
    refine GlobalTheory.ZH.ConeClosed.mem_cone_of_vanishing k _ Φ.G.hom (Φ.H 1) J F _ hH himm v h0 ?_
    refine eval_eq_zero_of_hilb_le k J _ g N h1 h2 h3 h4 hh v fun d Pf hd hP hI => hv d Pf hd hP ?_
    intro x _
    obtain ⟨w, hw⟩ := ((GlobalTheory.ZH.CrdCalc.crd_calculus _ (Φ.H 1) J F hH).1 k x.left).1
    refine ⟨w, hw, ?_⟩
    have := (MvPolynomial.mem_vanishingIdeal_iff.1 hI) w ⟨x.left, Over.w x, hw⟩
    simpa [MvPolynomial.aeval_eq_eval] using this

end GlobalTheory.ZH.FibCone
