import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLiftDatumOfConjugateLiftDatumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointConjugateThetaLiftEqVectorValuedLiftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassSumInnerEqSumVectorThetaLiftsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarInnerProductFormulaUnitCoefficientStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalarProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem inner_gW (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : G) (x y : (R.HW i σ).H) :
    ⟪R.gW i σ g x, R.gW i σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  LinearIsometry.inner_map_map ⟨R.gW i σ g, GlobalTheory.gW_norm_eq R hC.models.HW hC.models.gW hC.models.νW i σ g⟩ x y

theorem adjoint_projH (hC : GlobalTheory.Hk3.Core R F) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    LinearMap.adjoint (GlobalTheory.LiftLower.projH R i σ) = GlobalTheory.LiftLower.projH R i σ := by
  have hc : ∀ g, starRingEnd ℂ (RealDat.eC (A := A) σ g) = RealDat.eC (A := A) σ g⁻¹ := by
    intro g
    unfold RealDat.eC
    rw [coeff_idemOf, coeff_idemOf, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have h1 := (hX χ hχ).map_inv σ 1
    have h2 := (hX χ hχ).map_inv σ g⁻¹
    rw [inv_one] at h1
    simp only [map_mul, map_div₀, map_natCast]
    rw [h2, ← h1]
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  unfold GlobalTheory.LiftLower.projH
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hc]
  refine Finset.sum_nbij' (fun g => g⁻¹) (fun g => g⁻¹) (by simp) (by simp) (by simp) (by simp) fun g _ => ?_
  rw [← inner_gW hC i σ g⁻¹, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem projH_projH (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    GlobalTheory.LiftLower.projH R i σ (GlobalTheory.LiftLower.projH R i σ x) = GlobalTheory.LiftLower.projH R i σ x := by
  classical
  have h1 : ∀ g, ∑ a, RealDat.eC (A := A) σ a * RealDat.eC (A := A) σ (a⁻¹ * g) = RealDat.eC (A := A) σ g := by
    intro g
    unfold RealDat.eC
    conv_rhs => rw [← idemOf_mul_self A.X hX]
    rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp), map_sum]
    simp only [map_mul]
  unfold GlobalTheory.LiftLower.projH
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_congr rfl fun g _ => by rw [← h1 g, Finset.sum_smul]]
  rw [Finset.sum_comm (f := fun g a => (RealDat.eC (A := A) σ a * RealDat.eC (A := A) σ (a⁻¹ * g)) • R.gW i σ g x)]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_nbij' (fun g => a * g) (fun g => a⁻¹ * g) (by simp) (by simp) (by simp) (by simp) fun g _ => ?_
  rw [inv_mul_cancel_left, map_mul, Module.End.mul_apply, mul_comm]

theorem eq_of_ext {V : HSp D} {c : CoefA V} (hc : c.Is) {H : HMod (Bridge.Gf V → c.W)} (hinj : Function.Injective H.e) {z z' : H.H}
    (h : ∀ x w, inner ℂ (c.ext (H.e z) x) w = inner ℂ (c.ext (H.e z') x) w) : z = z' := by
  refine hinj (funext fun u => ?_)
  have e : c.ext (H.e z) (GlobalTheory.AdelicScalar.finLift V u) = c.ext (H.e z') (GlobalTheory.AdelicScalar.finLift V u) :=
    ext_inner_right ℂ fun w => h _ w
  exact (GlobalTheory.AdelicScalar.ext_finLift c hc (H.e z) u).symm.trans (e.trans (GlobalTheory.AdelicScalar.ext_finLift c hc (H.e z') u))

end GlobalTheory.ConjScalarProof

namespace GlobalTheory.ConjScalarProof
set_option maxHeartbeats 1000000 in
open GlobalTheory.LiftLower in

theorem conjScalarAt_of_sourceLevelLaw_fock_zeta : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R → GlobalTheory.ConjScalar.ConjScalarAt R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hCore hX hSL hIPF hFC hFZ hRC
  intro gramR c0R c0L hT i σ hσ μ' η' c c₁ H j th hD ev
  have hμ := hD.1
  have hη := hD.2.1
  have hf := hD.2.2.1
  have hL := hD.2.2.2
  have hL2 := (GlobalTheory.GalLift.isConjLift_iff R i σ μ' η' c H th).1 hL
  obtain ⟨ω, hL3⟩ := hL2
  obtain ⟨f₀, f, B, io, thP, hL4⟩ := hL3
  have hLD := hL4.1
  have hP := hL4.2
  have h38 := GlobalTheory.T.adelicLiftDatum_of_conjugate_liftDatum R F hCore gramR c0R c0L hT i σ c c₁ H j hσ hf μ' η' hμ hη ω f₀ f B io thP hLD
  obtain ⟨s, m, h39⟩ := h38
  have hC := h39.1
  have hν := h39.2.1
  have hy := h39.2.2.1
  have hH := h39.2.2.2
  have hth := hLD.2.2.2
  have hio := hC.2.2.2.2.2.2.2.2.2.2
  have hc : c.Is := hC.2.2.2.2.2.2.2.2.2.1
  have hv0 := hio.2.2
  let v := hv0.choose
  have hv : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1 := hv0.choose_spec.choose_spec.1
  let K : ℂ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)
  have hKdef : K = ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ) := rfl
  have hK0 : K ≠ 0 := by
    rw [hKdef, Finset.prod_ne_zero_iff]
    intro ρ _
    have h1 := GlobalTheory.AdelicScalar.one_le_dimK i σ ρ
    exact_mod_cast (show (dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) ≠ 0 by positivity)
  have hKc : starRingEnd ℂ K = K := by
    rw [hKdef, map_prod]
    exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _
  have hadj : ∀ (y : (R.HW i σ).H) (h : GA D (Vc D i)) (w : c.W), inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w = K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) fun ρ => v ρ) h :=
    GlobalTheory.T.adjoint_conjugateThetaLift_eq_vectorValuedLift R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv thP th hth hP
  have hpp : ∀ y, projH R i σ (projH R i σ y) = projH R i σ y := projH_projH hX i σ
  have hsa : LinearMap.adjoint (projH R i σ) = projH R i σ := adjoint_projH hCore hX i σ
  have hinj : Function.Injective H.e := hH.1
  have hadjP : ∀ y, LinearMap.adjoint th (projH R i σ y) = LinearMap.adjoint th y := fun y =>
    eq_of_ext (V := Vc D i) (c := c) (H := H) hc hinj fun x w =>
      (hadj (projH R i σ y) x w).trans ((congrArg (fun z => K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e z fun ρ => v ρ) x) (hpp y)).trans (hadj y x w).symm)
  have hfix : ∀ u, projH R i σ (th u) = th u := fun u => ext_inner_right ℂ fun y =>
    (LinearMap.adjoint_inner_right (projH R i σ) (th u) y).symm.trans
      ((congrArg (fun A => inner ℂ (th u) (A y)) hsa).trans ((LinearMap.adjoint_inner_right th u (projH R i σ y)).symm.trans
        ((congrArg (inner ℂ u) (hadjP y)).trans (LinearMap.adjoint_inner_right th u y))))
  have hW : ∀ y, (R.HW i σ).e y ∈ R.Wall i σ := fun y => GlobalTheory.AdelicScalar.HMod_mem (hCore.models.HW i σ) y
  have hz : ∀ y h w, inner ℂ (c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h := by
    intro y h w
    have e1 : c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) = K⁻¹ • c.ext (H.e (LinearMap.adjoint th y)) :=
      (congrArg c.ext (H.e.map_smul K⁻¹ _)).trans (c.ext.map_smul K⁻¹ _)
    have e2 : starRingEnd ℂ K⁻¹ = K⁻¹ := by simp only [map_inv₀, hKc]
    calc inner ℂ (c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) h) w
        = inner ℂ (K⁻¹ • c.ext (H.e (LinearMap.adjoint th y)) h) w := congrArg (fun Fn => inner ℂ (Fn h) w) e1
      _ = starRingEnd ℂ K⁻¹ * inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w := inner_smul_left _ _ _
      _ = K⁻¹ * (K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h) := by simp only [e2, hadj y h w]
      _ = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h := inv_mul_cancel_left₀ hK0 _
  have hG := GlobalTheory.T.exists_scalar_innerProductFormula_unitCoefficient R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv ev
  let C := hG.choose
  have hC2 := hG.choose_spec
  let b := stdOrthonormalBasis ℂ c.W
  have key : ∀ u, th u ∈ partH R i σ ev → ∀ y₂,
      inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y₂) = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y₂ := by
    intro u hu y₂
    have e1 := GlobalTheory.T.classSum_inner_eq_sum_vectorThetaLifts R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv
      _ (hW (projH R i σ (th u))) _ (hW (projH R i σ y₂)) _ _ (hz (th u)) (hz y₂) b
    have hu' : projH R i σ (th u) ∈ partH R i σ ev := (hfix u).symm ▸ hu
    have e2 : inner ℂ (projH R i σ (th u)) (projH R i σ y₂) = inner ℂ (th u) y₂ :=
      (congrArg (fun z => inner ℂ z (projH R i σ y₂)) (hfix u)).trans
        ((congrArg (fun A => inner ℂ (th u) (A y₂)) hsa.symm).trans
          ((LinearMap.adjoint_inner_right (projH R i σ) (th u) y₂).trans (congrArg (fun z => inner ℂ z y₂) (hfix u))))
    have e4 : inner ℂ (K⁻¹ • LinearMap.adjoint th (th u)) (K⁻¹ • LinearMap.adjoint th y₂) =
        (Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂) := by
      refine e1.trans ?_
      rw [Finset.sum_congr rfl fun k _ => hC2 _ hu' (projH R i σ y₂) (b k) (b.orthonormal.1 k), e2, Finset.sum_const,
        Finset.card_fin, nsmul_eq_mul]
    have e3 : ∀ y, LinearMap.adjoint th y = K • (K⁻¹ • LinearMap.adjoint th y) := fun y =>
      (smul_inv_smul₀ hK0 _).symm
    calc inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y₂)
        = inner ℂ (K • (K⁻¹ • LinearMap.adjoint th (th u))) (K • (K⁻¹ • LinearMap.adjoint th y₂)) :=
          congrArg₂ (inner ℂ) (e3 _) (e3 _)
      _ = starRingEnd ℂ K * (K * inner ℂ (K⁻¹ • LinearMap.adjoint th (th u)) (K⁻¹ • LinearMap.adjoint th y₂)) :=
          (inner_smul_left _ _ _).trans (congrArg (fun z => starRingEnd ℂ K * z) (inner_smul_right _ _ _))
      _ = K * (K * ((Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂))) :=
          (congrArg (fun z => starRingEnd ℂ K * (K * z)) e4).trans
            (congrArg (fun k => k * (K * ((Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂)))) hKc)
      _ = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y₂ := by ring
  refine ⟨(K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re, fun u hu => ?_⟩
  by_cases h0 : th u = 0
  · simp only [h0, map_zero, smul_zero]
  have hre : (((K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re : ℝ) : ℂ) = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) := by
    have e0 : ((‖LinearMap.adjoint th (th u)‖ : ℝ) : ℂ) ^ 2 = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * ((‖th u‖ : ℝ) : ℂ) ^ 2 :=
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (LinearMap.adjoint th (th u))).symm.trans
        ((key u hu (th u)).trans (congrArg (fun z => (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * z) (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (th u))))
    have hn : ((‖th u‖ : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast norm_ne_zero_iff.2 h0)
    have e' : (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) = ((‖LinearMap.adjoint th (th u)‖ ^ 2 / ‖th u‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [eq_div_iff hn]
      exact e0.symm
    exact (congrArg (fun z : ℂ => ((z.re : ℝ) : ℂ)) e').trans ((congrArg (fun r : ℝ => (r : ℂ)) (Complex.ofReal_re _)).trans e'.symm)
  refine ext_inner_right ℂ fun y => ?_
  calc inner ℂ (th (LinearMap.adjoint th (th u))) y = inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y) :=
        (LinearMap.adjoint_inner_right th _ y).symm
    _ = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y := key u hu y
    _ = inner ℂ ((((K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re : ℝ) : ℂ) • th u) y :=
      (congrArg (fun z => z * inner ℂ (th u) y) ((Complex.conj_ofReal _).trans hre)).symm.trans (inner_smul_left _ _ _).symm

end GlobalTheory.ConjScalarProof
