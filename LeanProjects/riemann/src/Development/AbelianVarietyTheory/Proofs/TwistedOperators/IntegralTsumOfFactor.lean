import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOfClassSums
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyDefiniteMass
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockNormMinorProductDeltaAtEmbeddingPosStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows

namespace GlobalTheory.LiftScalarL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem tprod_split {α κ : Type} (g : α → κ → ℝ) (hm : ∀ p : α → Prop, Multipliable fun a : {v // p v} × κ => g a.1.1 a.2)
    (S : Finset α) : (∏' a : {v // v ∉ S} × κ, g a.1.1 a.2) * ∏' a : {v // v ∈ S} × κ, g a.1.1 a.2 =
      ∏' a : {v // v ∉ (∅ : Finset α)} × κ, g a.1.1 a.2 := by
  let e : ∀ p : α → Prop, {v // p v} × κ ≃ {x : α × κ | p x.1} := fun p =>
    ⟨fun a => ⟨(a.1.1, a.2), a.1.2⟩, fun x => (⟨x.1.1, x.2⟩, x.1.2), fun _ => rfl, fun _ => rfl⟩
  have h : ∀ p : α → Prop, HasProd ((fun x : α × κ => g x.1 x.2) ∘ (↑) : {x : α × κ | p x.1} → ℝ)
      (∏' a : {v // p v} × κ, g a.1.1 a.2) := fun p => (e p).hasProd_iff.1 (hm p).hasProd
  have h1 : HasProd (fun x : α × κ => g x.1 x.2) _ := HasProd.compl_mul (s := {x : α × κ | x.1 ∈ S}) (h (· ∉ S)) (h (· ∈ S))
  let e0 : {v // v ∉ (∅ : Finset α)} × κ ≃ α × κ :=
    ⟨fun a => (a.1.1, a.2), fun x => (⟨x.1, Finset.notMem_empty _⟩, x.2), fun _ => rfl, fun _ => rfl⟩
  exact (e0.hasProd_iff.2 h1).tprod_eq.symm

theorem dOff_mul (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : dOff D S * ∏ v ∈ S, dLoc D v = dOff D ∅ := by
  have e : ∏' a : {v // v ∈ S} × Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D a.1.1 a.2.1)⁻¹ = ∏ v ∈ S, dLoc D v := by
    rw [tprod_fintype, Fintype.prod_prod_type, ← Finset.prod_coe_sort S]
    exact Finset.prod_congr rfl fun v _ => Finset.prod_coe_sort (Finset.Ioc D.R.t D.R.nV) fun i => (1 - quadTerm D v i)⁻¹
  rw [← e]
  refine tprod_split (fun v (k : Finset.Ioc D.R.t D.R.nV) => (1 - quadTerm D v k.1)⁻¹) (fun p => ?_) S
  obtain ⟨h1, h2, -⟩ := sum_bound p (κ := Finset.Ioc D.R.t D.R.nV) (fun a => |quadTerm D a.1.1 a.2.1|)
    (fun _ => abs_nonneg _) fun a => abs_quadTerm_le _ (by
      have := (Finset.mem_Ioc.1 a.2.2).1
      have := D.R.rank_add_five_le
      omega)
  have h3 : ∀ a : {v // p v} × Finset.Ioc D.R.t D.R.nV, 1 / 2 ≤ 1 - quadTerm D a.1.1 a.2.1 := fun a => by
    have := (abs_le.1 (h1 a)).2
    linarith
  have h4 := multipliable_one_add_of_summable (f := fun a : {v // p v} × Finset.Ioc D.R.t D.R.nV =>
    (1 - quadTerm D a.1.1 a.2.1)⁻¹ - 1) (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => ?_) (h2.mul_left 2))
  · simpa using h4
  · have h5 := h3 a
    have h6 : (1 - quadTerm D a.1.1 a.2.1)⁻¹ - 1 = (1 - quadTerm D a.1.1 a.2.1)⁻¹ * quadTerm D a.1.1 a.2.1 := by
      field_simp
      ring
    rw [h6, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [inv_le_comm₀ (by linarith) two_pos]
    linarith

theorem scalar_real {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) (U : Submodule ℂ Y) (hU : U ≠ ⊥)
    (a : ℝ) (ha : 0 < a) (L : ℂ) (hL : L ≠ 0)
    (h : ∀ y ∈ U, ∀ y', inner ℂ (LinearMap.adjoint th y) (LinearMap.adjoint th y') = a * L * inner ℂ y y') :
    ∃ z : ℝ, 0 < z ∧ L = z ∧ ∀ y ∈ U, th (LinearMap.adjoint th y) = ((a * z : ℝ) : ℂ) • y := by
  have h1 := scalar_of_form th U hU _ h
  have h2 : ‖(a : ℂ) * L‖ = a * ‖L‖ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  rw [h2] at h1
  refine ⟨‖L‖, norm_pos_iff.2 hL, ?_, h1⟩
  obtain ⟨y, hy, h0⟩ := (Submodule.ne_bot_iff _).1 hU
  have h3 := h y hy y
  rw [LinearMap.adjoint_inner_right, h1 y hy, inner_smul_left, Complex.conj_ofReal] at h3
  have h4 := mul_right_cancel₀ (inner_self_ne_zero.2 h0) h3
  push_cast at h4
  exact (mul_left_cancel₀ (by exact_mod_cast ha.ne') h4).symm

theorem integral_tsum_of_factor {ι X : Type} [Fintype ι] {E : ι → Type} [∀ ρ, MeasurableSpace (E ρ)] (m : ∀ ρ, Measure (E ρ))
    [∀ ρ, SigmaFinite (m ρ)] (Z : X → (∀ ρ, E ρ) → ℂ) (k : ∀ ρ, E ρ → ℂ) (δ : ι → ℝ)
    (hδ : ∀ ρ, ∫ b, ‖k ρ b‖ ^ 2 ∂(m ρ) = δ ρ) (a K cst : ℂ) (u : X → (∀ ρ, E ρ) → ℂ)
    (hZ : ∀ x b, Z x b = a * (∏ ρ, k ρ (b ρ)) * u x b)
    (hu : ∀ b, HasSum (fun x => u x b) (K * (cst * ∏ ρ, starRingEnd ℂ (k ρ (b ρ))))) :
    ∫ b, ∑' x, Z x b ∂(Measure.pi m) = a * (∏ ρ, (δ ρ : ℂ)) * K * cst := by
  have e : ∀ b, ∑' x, Z x b = (a * K * cst) * ∏ ρ, ((‖k ρ (b ρ)‖ ^ 2 : ℝ) : ℂ) := fun b => by
    simp only [hZ]
    rw [tsum_mul_left, (hu b).tsum_eq]
    have : ∏ ρ, ((‖k ρ (b ρ)‖ ^ 2 : ℝ) : ℂ) = (∏ ρ, k ρ (b ρ)) * ∏ ρ, starRingEnd ℂ (k ρ (b ρ)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun ρ _ => by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this]; ring
  simp only [e]
  rw [integral_const_mul, integral_fintype_prod_eq_prod (fun ρ b => ((‖k ρ b‖ ^ 2 : ℝ) : ℂ))]
  simp only [integral_complex_ofReal, hδ]
  ring

theorem conj_l2_inner {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓖 : Set X) (F T : X → ℂ) :
    starRingEnd ℂ (l2 μ 𝓖 F T) = ∫ g in 𝓖, star (F g) * T g ∂μ := by
  unfold l2 Lift.pet
  rw [← integral_conj]
  simp only [map_mul, Complex.conj_conj]
  rfl

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

open Datum in

theorem l2_upwardLift {F : Face D A} (hI : InnerProductFormulaC R F) (hFo : FockCoefficientC R F)
    {i t σ s P cμ cη m ω BW f₀ f c io} (hd : IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io)
    {ν : Measure (GA D (Vc D i))} {𝓕 : Set (GA D (Vc D i))} (hν : IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕)
    {μ : Measure (WO (Vc D i) (Wc D i))} {𝓧 : Set (WO (Vc D i) (Wc D i))} (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧)
    {Fr : Frames (Wc D i)} (hFr : IsFrames (Wc D i) Fr) {mR : ∀ ρ, Measure (Upq (Wc D i) ρ)} (hmR : ∀ ρ, Lev.IsMinf (mR ρ))
    {U₁ U₂ : MMap (R.MW i σ)} (h₁ : U₁ ∈ R.Wall i σ) (h₂ : U₂ ∈ R.Wall i σ) {cst : ℂ}
    (hc : IsMultIP (R.MW i σ) (R.νW i) (R.fdW i) U₁ U₂ cst) (K : ℂ)
    (hK : ∀ v₁ v₂ : (R.MW i σ).Vec, HasSum (fun y : FinCos (Wc D i) (levW R i) =>
      l2 μ 𝓧 (ω (1, y.rep) f) f * starRingEnd ℂ (petW R i (rTr (Wc D i) y.rep (U₁ v₁)) (U₂ v₂)))
        (K * starRingEnd ℂ (petW R i (U₁ v₁) (U₂ v₂))))
    (e : ∀ ρ, lowT (R.MW i σ) ρ) (δ : D.what₂.Tau → ℝ)
    (hδ : ∀ ρ, ∫ b, ‖⟪((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
      (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(mR ρ) = δ ρ)
    (w : c.W) (hw : ⟪w, w⟫_ℂ = 1) :
    l2 ν 𝓕 (upLift R i ω (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e) w)) (U₁ fun ρ => e ρ))
        (upLift R i ω (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e) w)) (U₂ fun ρ => e ρ)) =
      ((ν 𝓕).toReal : ℂ) * (Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * (∏ ρ, (δ ρ : ℂ)) * K * cst) := by
  refine (hI i t σ s P cμ cη m ω BW f₀ f c io hd ν 𝓕 hν μ 𝓧 hμ Fr hFr mR hmR U₁ h₁ U₂ h₂ e e _ _).2.2.2.trans (congrArg _ ?_)
  haveI : ∀ ρ, SigmaFinite (mR ρ) := fun ρ => sigmaFinite_haar _ (hmR ρ).1
  let v : (∀ ρ, Upq (Wc D i) ρ) → (R.MW i σ).Vec := fun b ρ =>
    ⟨(R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ (b ρ)) ((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
      rep_mem_sm (R.MW i σ) ρ _ (realMat_mem i hFr ρ (b ρ)) _ (e ρ : (R.MW i σ).sm ρ).2⟩
  refine integral_tsum_of_factor mR _ (fun ρ b => ⟪((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
      (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ) δ hδ _ K cst
    (fun y b => l2 μ 𝓧 (ω (1, y.rep) f) f *
      starRingEnd ℂ (petW R i (rTr (Wc D i) y.rep (U₁ (v b))) (U₂ fun ρ => e ρ))) (fun y b => ?_) fun b => ?_
  · have h1 := hFo i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ y.rep (y.out).2 (fun ρ => realMat (Wc D i) Fr ρ (b ρ))
      (fun ρ => realMat_mem i hFr ρ (b ρ)) e e w w
    have h2 := GlobalTheory.RealEquiv.mult_realElt D _ _ R.θ (R.MW i σ) _ _ U₁ h₁ (fun ρ => realMat (Wc D i) Fr ρ (b ρ))
      (fun ρ => realMat_mem i hFr ρ (b ρ)) (fun ρ => e ρ) (v b) fun _ => rfl
    have h3 : rTr (Wc D i) (y.rep * realElt R.θ (Wc D i) fun ρ => realMat (Wc D i) Fr ρ (b ρ)) (U₁ fun ρ => e ρ) =
        rTr (Wc D i) y.rep (U₁ (v b)) := by
      rw [h2]
      funext g
      exact congrArg (U₁ fun ρ => e ρ) (mul_assoc _ _ _).symm
    rw [hw, mul_one] at h1
    refine (congrArg₂ (· * ·) h1 (congrArg (fun u => starRingEnd ℂ (petW R i u (U₂ fun ρ => e ρ))) h3)).trans ?_
    exact mul_assoc _ _ _
  · have h1 := hK (v b) fun ρ => e ρ
    have h2 : starRingEnd ℂ (petW R i (U₁ (v b)) (U₂ fun ρ => e ρ)) = _ := (conj_l2_inner _ _ _ _).trans (hc _ _).2
    rw [h2] at h1
    simp only [inner_conj_symm]
    exact h1

open Datum in

theorem form_of_data {F : Face D A} (hS : SourceLevelLawC R F) (hI : InnerProductFormulaC R F) (hFo : FockCoefficientC R F)
    {i t σ s P cμ cη m ω BW f₀ f c io} (hd : IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io)
    {ν : Measure (GA D (Vc D i))} {𝓕 : Set (GA D (Vc D i))} (hν : IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕)
    {μ : Measure (WO (Vc D i) (Wc D i))} {𝓧 : Set (WO (Vc D i) (Wc D i))} (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧)
    {Fr : Frames (Wc D i)} (hFr : IsFrames (Wc D i) Fr) {mR : ∀ ρ, Measure (Upq (Wc D i) ρ)} (hmR : ∀ ρ, Lev.IsMinf (mR ρ))
    {I : Type} [Fintype I] {y : I → Bridge.Gf (Vc D i)}
    (hy : Bridge.IsReps (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y)
    (HV : HMod (Bridge.Gf (Vc D i) → c.W))
    (hV : HV.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m))
        (chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)))
      (Bridge.adInner (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y))
    (th : HV.H →ₗ[ℂ] (R.HW i σ).H) (hth : IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th)
    (e : ∀ ρ, lowT (R.MW i σ) ρ) (he : ∀ ρ, ‖((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) (δ : D.what₂.Tau → ℝ)
    (hδ : ∀ ρ, ∫ b, ‖⟪((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
      (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(mR ρ) = δ ρ)
    {N : ℝ} (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM (R.MW i σ) (R.νW i) (R.fdW i) ((R.HW i σ).e x) ((R.HW i σ).e y))
    (y₁ y₂ : (R.HW i σ).H) (K : ℂ)
    (hK : ∀ v₁ v₂ : (R.MW i σ).Vec, HasSum (fun y : FinCos (Wc D i) (levW R i) =>
      l2 μ 𝓧 (ω (1, y.rep) f) f * starRingEnd ℂ (petW R i (rTr (Wc D i) y.rep ((R.HW i σ).e y₁ v₁)) ((R.HW i σ).e y₂ v₂)))
        (K * starRingEnd ℂ (petW R i ((R.HW i σ).e y₁ v₁) ((R.HW i σ).e y₂ v₂)))) :
    inner ℂ (LinearMap.adjoint th y₁) (LinearMap.adjoint th y₂) =
      (N * Module.finrank ℂ c.W * ((ν 𝓕).toReal : ℂ) * Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * (∏ ρ, (δ ρ : ℂ)) * K) *
        inner ℂ y₁ y₂ := by
  have hm : ∀ x, (R.HW i σ).e x ∈ R.Wall i σ := HMod_mem (hd.1.models.HW i σ)
  have hI' := hI i t σ s P cμ cη m ω BW f₀ f c io hd ν 𝓕 hν μ 𝓧 hμ Fr hFr mR hmR
  let φ : c.W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
    pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) BW f ∘ₗ io (PiTensorProduct.tprod ℂ e)
  let b := stdOrthonormalBasis ℂ c.W
  have key := form_eq_sum hd.2.2.2.2.2.1 c hd.2.2.2.2.2.2.2.2.2.1 (R.βV i) (datV i R.Pg (R.Q t) P m) φ
    (fun w => hd.2.2.2.2.2.2.2.2.1 _) (fun u hu w => hd.2.2.2.2.2.2.2.2.2.2.1 u hu _ w)
    (fun κ hκ w => hS i t σ s P cμ cη m ω BW f₀ f c io hd κ hκ _) (R.HW i σ) hW hν hy HV hV (fun ρ => e ρ) he th
    (fun x g => (hth x e g).2) (fun U w h => (hI' _ (hm U) _ (hm U) e e (io (PiTensorProduct.tprod ℂ e) w) 0).1 h) y₁ y₂ b
    fun k => (hI' _ (hm y₁) _ (hm y₂) e e (io (PiTensorProduct.tprod ℂ e) (b k)) (io (PiTensorProduct.tprod ℂ e) (b k))).2.1
  have h2 := fun k => l2_upwardLift R hI hFo hd hν hμ hFr hmR (hm y₁) (hm y₂) (isMultiplicityInner_of_model (R.HW i σ) hW y₁ y₂) K hK e δ hδ (b k)
    (by rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 k]; simp)
  refine key.trans ((congrArg _ (Finset.sum_congr rfl fun k _ => h2 k)).trans ?_)
  rw [hW y₁ y₂, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem inner_HW (h : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x y : (R.HW i σ).H) :
    inner ℂ x y = ((∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ) : ℝ) : ℂ) *
      ipM (R.MW i σ) (R.νW i) (R.fdW i) ((R.HW i σ).e x) ((R.HW i σ).e y) := by
  rw [(h i σ).2.2, ipAt]
  push_cast
  rfl

theorem vol_mul_nrm {i : Fin D.R.m} (hp : (Vc D i).IsPosDef) {t P m} {ν : Measure (GA D (Vc D i))} {𝓕 : Set (GA D (Vc D i))}
    (hν : IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕) (hle : levV R i t P m ≤ GlobalTheory.Mass.Levels.latLev (Vc D i)) {n : ℝ}
    (hn : (((levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) : ℕ) : ℝ) * n = ∏ v ∈ finS R t, (dLoc D v)⁻¹) :
    (ν 𝓕).toReal * n / dOff D (finS R t) =
      GlobalTheory.Mass.unitaryMass D.sp.cm.sig (Vc D i).gram (GlobalTheory.Mass.Levels.latStab (Vc D i)) / dOff D ∅ := by
  have h1 := (dLoc_bound (D := D) (finS R t)).1
  have h2 := (dOff_bound (D := D) (finS R t)).1
  rw [Finset.prod_inv_distrib] at hn
  have h0 : (levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) ≠ 0 := fun h => by
    rw [h, Nat.cast_zero, zero_mul] at hn
    exact (inv_pos.2 h1).ne hn
  rw [GlobalTheory.VolIndex.vol_eq_index_mul_mass D _ _ ν 𝓕 (D.sp.V_sig _) hp hle h0 (isOpen_level _ _ _) hν, ← dOff_mul (finS R t),
    mul_right_comm, hn]
  field_simp

open Datum in

theorem scalar_of_data {F : Face D A} (hS : SourceLevelLawC R F) (hI : InnerProductFormulaC R F) (hFo : FockCoefficientC R F)
    (hZ : FiniteZetaL R F) (hL : LevelIndexNormC R F) (hδ : RealLowestKTypeCoeffSquareIntegrable R) (hp : ∀ i, (Vc D i).IsPosDef) :
    ∃ a : Fin D.R.m → (D.what₂.LL →+* ℂ) → ℝ, (∀ i σ, 0 < a i σ) ∧
    ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io →
    ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))), IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕 →
    ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf (Vc D i)),
      Bridge.IsReps (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y →
    ∀ HV : HMod (Bridge.Gf (Vc D i) → c.W),
      HV.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m))
          (chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)))
        (Bridge.adInner (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y) →
    ∀ th, IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th →
    ∀ ev, typePart R i σ t P ev ≠ ⊥ →
      ∃ (B : GlobalTheory.LFun.Fam D.host.E) (z : ℝ), GlobalTheory.LFun.IsSysParamD D (finS R t) D.R.r ev B ∧
        GlobalTheory.LFun.Converges (GlobalTheory.LFun.above D.host.E (finS R t : Set (HeightOneSpectrum (𝓞 D.host.F))))
          (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val cμ)⁻¹) ((1 + (D.R.t : ℂ)) / 2) ∧ 0 < z ∧
        GlobalTheory.LFun.LSD D (finS R t) B cμ ((1 + (D.R.t : ℂ)) / 2) = (z : ℂ) ∧
        ∀ x ∈ typePart R i σ t P ev, th (LinearMap.adjoint th x) =
          ((a i σ * Module.finrank ℂ c.W * Nat.card P.H * z : ℝ) : ℂ) • x := by
  choose δ hδ0 hδ using hδ
  choose dl hdl0 hdl using GlobalTheory.T.fockNorm_minorProductDeltaAtEmbedding_pos D
  have hN : ∀ i σ, 0 < ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ) := fun i σ =>
    Finset.prod_pos fun ρ _ => by exact_mod_cast one_pos.trans_le (one_le_dimK i σ ρ)
  have hM : ∀ i, 0 < GlobalTheory.Mass.unitaryMass D.sp.cm.sig (Vc D i).gram (GlobalTheory.Mass.Levels.latStab (Vc D i)) := fun i =>
    ((GlobalTheory.Mass.Levels.mass_levels D (Vc D i)).2.2.2.2.2.2 (GlobalTheory.Proof.TotallyDefiniteMass.isTotDef_gram D.sp.cm _ (D.sp.V_sig _) (hp i))).2.2
  have ha : ∀ i σ, 0 < (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ)) * dl i σ * (∏ ρ, δ i σ ρ) *
      (GlobalTheory.Mass.unitaryMass D.sp.cm.sig (Vc D i).gram (GlobalTheory.Mass.Levels.latStab (Vc D i)) / dOff D ∅) := fun i σ =>
    mul_pos (mul_pos (mul_pos (hN i σ) (hdl0 i σ)) (Finset.prod_pos fun ρ _ => hδ0 i σ ρ)) (div_pos (hM i) (dOff_bound _).1)
  refine ⟨_, ha, ?_⟩
  intro i t σ s P cμ cη m ω BW f₀ f c io hd ν 𝓕 hν I _ y hy HV hV th hth ev hev
  refine (GlobalTheory.ThetaAllChar.covolOneExists (Vc D i) (Wc D i)).elim fun μ hμ => hμ.elim fun 𝓧 hμ => ?_
  have hw := (hd.1.models.νW i).1.2
  refine hw.1.elim fun θ hθ => (hw.2 θ hθ).1.elim fun Fr hFr => ((hw.2 θ hθ).2 Fr hFr).1.elim fun mR hmR => ?_
  refine hd.2.2.2.2.2.2.2.2.2.2.2.2.elim fun e he => he.elim fun w he => ?_
  refine (hZ i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ ev hev).elim fun B hB => ?_
  have hL' := hL i t σ s P cμ cη m ω BW f₀ f c io hd
  have hvol := vol_mul_nrm R (hp i) hν hL'.1 (hL'.2 μ 𝓧 hμ)
  haveI : Nontrivial c.W := hd.2.2.2.2.2.2.2.2.2.1.2.2.2.1
  haveI : Finite P.H := inferInstance
  have h1 : (0 : ℝ) < Module.finrank ℂ c.W := by exact_mod_cast Module.finrank_pos
  have h2 : (0 : ℝ) < Nat.card P.H := by exact_mod_cast Nat.card_pos
  refine (scalar_real th _ hev _ (mul_pos (mul_pos (ha i σ) h1) h2) _ hB.2.2.1.ne_zero fun y₁ hy₁ y₂ => ?_).elim
    fun z hz => ⟨B, z, hB.1, hB.2.2.1, hz.1, hz.2.1, hz.2.2⟩
  refine (form_of_data R hS hI hFo hd hν hμ hFr hmR hy HV hV th hth e he.1 (δ i σ)
    (fun ρ => (hδ i σ ρ Fr hFr (mR ρ) (hmR ρ) (e ρ) (he.1 ρ)).2) (inner_HW R hd.1.models.HW i σ) y₁ y₂ _
    (hB.2.2.2 _ hy₁ _ (HMod_mem (hd.1.models.HW i σ) y₂))).trans ?_
  rw [hdl, ← hvol]
  congr 1
  change _ = _ * GlobalTheory.LFun.LSD D (finS R t) B cμ ((1 + (D.R.t : ℂ)) / 2)
  generalize GlobalTheory.LFun.LSD D (finS R t) B cμ ((1 + (D.R.t : ℂ)) / 2) = L
  push_cast
  ring

end GlobalTheory.LiftScalarL

end
