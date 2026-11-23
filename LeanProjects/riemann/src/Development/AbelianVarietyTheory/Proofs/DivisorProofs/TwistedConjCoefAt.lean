import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefScale
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexLinearExtensionCoefficientMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapUniqueBijectiveComplexExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPrimeMemExceptionalSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteSideRealisationsCoefMapDifferRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientPolynomialGLFunctionNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGeneration

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

open GlobalTheory.ConjTwist

theorem scale_pow_eq_of_isScale {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {c c' : ℂ}
    (h : IsScale Rl v₀ B c) (h' : IsScale Rl v₀ B c') : ∃ k : ℕ, k ≠ 0 ∧ c' ^ k = c ^ k := by
  obtain ⟨gR, cR0, cL0, hT, u, hu, hF⟩ := h
  obtain ⟨gR', cR0', cL0', hT', u', hu', hF'⟩ := h'
  have huu : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  subst huu
  obtain ⟨a, ⟨k, hk, hak⟩, ha⟩ := GlobalTheory.T.definiteSideRealisations_coefMap_differ_rootOfUnity _ _ _ _ _ _ _ _ _ _ _ _ _ hT hT' j
  obtain ⟨F, x, hx⟩ := GlobalTheory.T.exists_coefficientPolynomial_GLFunction_ne_zero (FWT.lamV D j)
  have e1 := hF' F
  rw [ha] at e1
  erw [LinearMap.map_smul, LinearMap.map_smul, hF F] at e1
  have e2 := congrFun e1 x
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hc : c' = D.what₂.embLL a * c := by
    have h3 : D.what₂.embLL a * c * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x =
        c' * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x := by
      rw [mul_assoc]; exact e2
    exact (mul_right_cancel₀ hx h3).symm
  refine ⟨k, hk, ?_⟩
  rw [hc, mul_pow, ← map_pow, hak, map_one, one_mul]

theorem coefFn_map_eq {D : D7} {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n)
    (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) : coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F) = coefFn σ lam F := by
  funext x
  simp only [coefFn, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map, RingHom.id_comp]

theorem exists_fixed_of_mem_span {D : D7} (j : Fin D.R.m) {W M : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup M] [Module ℂ M]
    (Φ : W →ₗ[ℂ] M) (c : VsV D j ℂ →ₗ[ℂ] W) (a₀ : ℂ) (S : Set (VV (↥D.LL0) (lamV D j))) {P : M}
    (hP : P ∈ Submodule.span (smallInt D)
      {P | ∃ Fv ∈ S, P = Φ (c (a₀ • GlobalTheory.CoefModel.mapVV (Formalism.L2.Host.embLL0 D) (lamV D j) Fv))}) :
    ∃ y : VsV D j ℂ, P = a₀ • Φ (c y) ∧
      ∀ τ : ℂ ≃+* ℂ, (∀ z, τ (Formalism.L2.Host.embLL0 D z) = Formalism.L2.Host.embLL0 D z) → ConjVec j τ y y := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨Fv, -, rfl⟩ := hP
    refine ⟨GlobalTheory.CoefModel.mapVV (Formalism.L2.Host.embLL0 D) (lamV D j) Fv, by rw [c.map_smul, Φ.map_smul], fun τ hτ => ?_⟩
    change MvPolynomial.map _ _ = MvPolynomial.map _ (MvPolynomial.map _ _)
    rw [MvPolynomial.map_map, show (τ : ℂ →+* ℂ).comp (Formalism.L2.Host.embLL0 D) = Formalism.L2.Host.embLL0 D from RingHom.ext hτ]
  | zero => exact ⟨0, by rw [c.map_zero, Φ.map_zero, smul_zero], fun τ _ => (map_zero _).symm⟩
  | add P₁ P₂ _ _ h1 h2 =>
    obtain ⟨y1, rfl, c1⟩ := h1
    obtain ⟨y2, rfl, c2⟩ := h2
    refine ⟨y1 + y2, by rw [c.map_add, Φ.map_add, smul_add], fun τ hτ => ?_⟩
    have e1 := c1 τ hτ
    have e2 := c2 τ hτ
    unfold ConjVec at e1 e2 ⊢
    rw [Submodule.coe_add, map_add, ← e1, ← e2]
  | smul a P₁ _ h1 =>
    obtain ⟨y1, rfl, c1⟩ := h1
    refine ⟨(a : ℂ) • y1, ?_, fun τ hτ => ?_⟩
    · rw [c.map_smul, Φ.map_smul, smul_comm a₀]
      rfl
    · have e1 := c1 τ hτ
      unfold ConjVec at e1 ⊢
      obtain ⟨o, ho⟩ := a.2
      have ha : (τ : ℂ →+* ℂ) (a : ℂ) = a := by rw [← ho]; exact hτ _
      rw [Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← e1, ha]

set_option maxHeartbeats 4000000 in

theorem coefAt_of_twAdm : TwAdm → CoefAt := by
  intro hA
  refine AtTw.imp (AtTw.and hA lowAt_holds) fun Fm x hx i p hr hm w _ j H => ?_
  obtain ⟨⟨-, -, hin⟩, hlow⟩ := H
  have hR := ratHyp0_at_point Fm x hx i p hr hm _ hin hlow j
  intro ρ ν hρ hp hN
  obtain ⟨hν0, c₀, hsc, n, hn, hνn⟩ := hN
  obtain ⟨-, -, -, -, u, hu, -⟩ := id hsc
  obtain ⟨c, hc⟩ := GlobalTheory.ExtCoeff.exists_extC _ _ _ _ _ _ _ j Unit (fun _ => p.P.A3.A.μ0) (p.O j)
  have hB := hρ.base ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hBo := baseOf_of_realPin hR.core.lev hρ hp ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have H1 := GlobalTheory.CoefLatConj.coefLat_conj (Fm.D x i) _ _ _ p.P.A3.A p.T p.R.toRealDat (F2 p) p.κ p.v₀ p.O hR.core hR.fw hR.io j
    hR.pins c hc u hu _ hB hBo
  obtain ⟨κ, hκ0, hκ, H2⟩ := H1
  have hspan := (H2.2 _ (Formalism.L2.Host.embLL0 _) (labLL0 _) (smallInt _) (smallInt_isCoefRing _)).1

  have hO : OMPins p.T p.R.toRealDat p.κ p.v₀ p.O j := hR.pins
  have hfield := hO.2.lift.field
  have hc0 := hO.2.lift.c0
  obtain ⟨gramR, c0R, c0L, hft, hbc⟩ := hc0
  have hcL : ∀ F : VV (Fm.D x i).what₂.LL (lamV (Fm.D x i) j),
      c (GlobalTheory.CoefModel.mapVV (Fm.D x i).what₂.embLL (lamV (Fm.D x i) j) F) = c0L j F := fun F => by
    obtain ⟨v', hv', hv0⟩ := hbc F
    refine (hc v' _ ?_).trans hv0
    change MvPolynomial.map (Fm.D x i).what₂.embLL _ = _
    rw [hv', MvPolynomial.map_map, hfield]
  have hκs : IsScale p.R p.v₀ (baseW (Fm.ex x hx i) w j ρ) κ := ⟨gramR, c0R, c0L, hft, u, hu, fun F =>
    (congrArg (fun z => harmFn _ _ _ (p.R.ioP j (PiTensorProduct.tprod ℂ u) z)) (hcL F)).symm.trans
      ((hκ _).trans (congrArg (κ • ·) (coefFn_map_eq _ _ _)))⟩
  obtain ⟨k, hk, hkk⟩ := scale_pow_eq_of_isScale p.R p.v₀ _ hsc hκs
  have hφc : phs p j * c₀ ≠ 0 := fun h0 => hν0 ((pow_eq_zero_iff hn).1 (hνn.trans (by rw [h0, zero_pow hn])))
  have hφ : phs p j ≠ 0 := left_ne_zero_of_mul hφc
  refine ⟨c, u, ν / (phs p j * κ), hc, hu, ⟨n * k, Nat.pos_of_ne_zero (Nat.mul_ne_zero hn hk), ?_⟩, ?_⟩
  · have e : ν ^ (n * k) = (phs p j * κ) ^ (n * k) := by
      rw [pow_mul, hνn, ← pow_mul, mul_pow, mul_pow, mul_comm n k, pow_mul c₀, pow_mul κ, hkk]
    rw [div_pow, e, div_self (pow_ne_zero _ (mul_ne_zero hφ hκ0))]
  · intro h₀ P hP
    obtain ⟨y, hPy, hy⟩ := exists_fixed_of_mem_span j (p.R.ioP j (PiTensorProduct.tprod ℂ u)) c κ⁻¹ _
      ((hspan (finPt _ h₀)).le hP)
    refine ⟨y, ?_, hy⟩
    have e : ν * κ⁻¹ = ν / (phs p j * κ) * phs p j := by field_simp
    exact (congrArg (ν • ·) hPy).trans ((smul_smul ν κ⁻¹ _).trans (congrArg (· • _) e))

end GlobalTheory.BigOn.Exp.TwConj
