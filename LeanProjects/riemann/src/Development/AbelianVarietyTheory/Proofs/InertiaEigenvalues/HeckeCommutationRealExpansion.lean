import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorBaseChangeForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorsRationalFormsCommuteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentFormsIntermediateFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexHeckeConjugatePlacePeterssonAdjointStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MinpolySeparableOfComplexNormalReadingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorFormsIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalIntertwine
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GoodSS.Heart

theorem aeval_map_of_comm {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (A : Module.End K M) (B : Module.End K N) (h : ∀ x, f (A x) = B (f x)) (p : K[X]) (x : M) :
    f (Polynomial.aeval A p x) = Polynomial.aeval B p (f x) := by
  first
  | exact @_root_.GlobalTheory.AevalIntertwine.aeval_intertwine
  | exact _root_.GlobalTheory.AevalIntertwine.aeval_intertwine
  | (apply _root_.GlobalTheory.AevalIntertwine.aeval_intertwine <;> assumption)
  | (intros; apply _root_.GlobalTheory.AevalIntertwine.aeval_intertwine <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AevalIntertwine.aeval_intertwine <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AevalIntertwine.aeval_intertwine ..)

theorem exists_lift_end {H X : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X]
    (e : H →ₗ[ℂ] X) (he : Function.Injective e) (A : X →ₗ[ℂ] X) (h : ∀ x, ∃ x', e x' = A (e x)) :
    ∃ S : Module.End ℂ H, ∀ x, e (S x) = A (e x) := by
  have hr : ∀ x, (A ∘ₗ e) x ∈ LinearMap.range e := fun x => by
    obtain ⟨x', hx'⟩ := h x
    exact ⟨x', hx'⟩
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ (A ∘ₗ e).codRestrict (LinearMap.range e) hr,
    fun x => ?_⟩
  have h1 := LinearEquiv.ofInjective_apply e (h := he)
    ((LinearEquiv.ofInjective e he).symm ⟨(A ∘ₗ e) x, hr x⟩)
  rw [LinearEquiv.apply_symm_apply] at h1
  exact h1.symm

variable {D : D7} (S : RatDat D.ntw)

theorem inWL_tmul (j : ℕ) (c : ↥D.LL0) (f : FmK S j) :
    inWL S j (c ⊗ₜ[S.Ks] f) = (c : D.what₂.LL) • (show ↥(S.A j).WK from f).1 := rfl

theorem inWL_smul (j : ℕ) (c : ↥D.LL0) (z : ↥D.LL0 ⊗[S.Ks] FmK S j) :
    inWL S j (c • z) = (c : D.what₂.LL) • inWL S j z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    rw [TensorProduct.smul_tmul']
    show ((c • a : ↥D.LL0) : D.what₂.LL) • (_ : S.WL j) = (c : D.what₂.LL) • (((a : ↥D.LL0) : D.what₂.LL) • (_ : S.WL j))
    rw [smul_eq_mul, IntermediateField.coe_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem inWL_opK (j : ℕ) (f : Module.End D.what₂.LL (S.WL j)) (hf : ∀ x ∈ (S.A j).WK, f x ∈ (S.A j).WK)
    (z : ↥D.LL0 ⊗[S.Ks] FmK S j) :
    inWL S j (LinearMap.baseChange ↥D.LL0 (opK S j f hf) z) = f (inWL S j z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, inWL_tmul, inWL_tmul, LinearMap.map_smul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem goodProjector_eq_sum (j : ℕ) (hst : RhoStab S j) (hχ : ChiInLL0 S j) (eC : G0g D.nd → ↥D.LL0)
    (s : Finset (G0g D.nd)) (hs : ∀ g, g ∉ s → eC g = 0) :
    goodProjectorBaseChangeForms S j hst hχ eC = ∑ g ∈ s, (eC g * (chiL S j hχ (S.eG.symm g))⁻¹) •
      LinearMap.baseChange ↥D.LL0 (rhoKG S j hst (S.eG.symm g)) := by
  unfold goodProjectorBaseChangeForms
  refine finsum_eq_sum_of_support_subset _ fun g hg => ?_
  by_contra hgs
  exact hg (by simp only [hs g hgs, zero_mul, zero_smul])

theorem goodProjW_eq_sum (j : ℕ) (eC : G0g D.nd → ↥D.LL0)
    (s : Finset (G0g D.nd)) (hs : ∀ g, g ∉ s → eC g = 0) :
    goodProjW S j eC = ∑ g ∈ s, (((eC g : ↥D.LL0) : D.what₂.LL) *
      ((((S.A j).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹) • (S.A j).ρ (S.eG.symm g) := by
  unfold goodProjW
  refine finsum_eq_sum_of_support_subset _ fun g hg => ?_
  by_contra hgs
  exact hg (by simp only [hs g hgs, IntermediateField.coe_zero, zero_mul, zero_smul])

theorem inForms_goodProjector (j : ℕ) (hst : RhoStab S j) (hχ : ChiInLL0 S j) (eC : G0g D.nd → ↥D.LL0)
    (s : Finset (G0g D.nd)) (hs : ∀ g, g ∉ s → eC g = 0) (z : ↥D.LL0 ⊗[S.Ks] FmK S j) :
    inWL S j (goodProjectorBaseChangeForms S j hst hχ eC z) = goodProjW S j eC (inWL S j z) := by
  rw [goodProjector_eq_sum S j hst hχ eC s hs, goodProjW_eq_sum S j eC s hs, LinearMap.sum_apply, map_sum,
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, inWL_smul, LinearMap.smul_apply]
  have h := inWL_opK S j ((S.A j).ρ (S.eG.symm g)) (fun x hx => hst (S.eG.symm g) x hx) z
  change inWL S j (LinearMap.baseChange ↥D.LL0 (opK S j ((S.A j).ρ (S.eG.symm g)) _) z) = _ at h
  erw [h]
  congr 1

theorem goodProjector_comm (j : ℕ) (hst : RhoStab S j) (hχ : ChiInLL0 S j) (eC : G0g D.nd → ↥D.LL0)
    (s : Finset (G0g D.nd)) (hs : ∀ g, g ∉ s → eC g = 0) (A : Module.End S.Ks (FmK S j))
    (hA : ∀ g, A * rhoKG S j hst g = rhoKG S j hst g * A) :
    LinearMap.baseChange ↥D.LL0 A * goodProjectorBaseChangeForms S j hst hχ eC = goodProjectorBaseChangeForms S j hst hχ eC * LinearMap.baseChange ↥D.LL0 A := by
  have hbm : ∀ f g : Module.End S.Ks (FmK S j),
      LinearMap.baseChange ↥D.LL0 (f * g) = LinearMap.baseChange ↥D.LL0 f * LinearMap.baseChange ↥D.LL0 g :=
    fun f g => LinearMap.baseChange_comp g f
  rw [goodProjector_eq_sum S j hst hχ eC s hs, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← hbm, ← hbm, hA]

end GlobalTheory.GoodSS.Heart

namespace GlobalTheory.GoodSS.Heart

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem hL_separable_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y), CommG D → HkComm D → NExpHeckeRowX Rl cG S Y H (fun j => goodProjW S j D.nexp.eLL0) →
    Rl.Char3 F → Rl.toRealDat.LUnif → Rl.toRealDat.LIntegral →
    (∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i) →
    (∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host))) →
    (∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i) →
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool) k P, HkIdx i k P →
      ∃ q : (↥D.LL0)[X], q.Separable ∧
        ∀ z ∈ LinearMap.range (GlobalTheory.GoodSS.goodProjectorBaseChangeForms S j (Y.rho j h1 h2) (Y.chi j h1 h2) D.nexp.eLL0),
          Polynomial.aeval (LinearMap.baseChange ↥D.LL0
            (GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx))) q z = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ Rl F cG S Y H hG hC hX hR hU hI hS0c hS02 hS0b i hi j h1 h2 b k P hk
  obtain ⟨i0, rfl⟩ : ∃ i0 : Fin D.R.m, j = (i0 : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨hk1, hk2, hPs, hP0⟩ := hk
  obtain ⟨P', hPP', hP's, hP'0, hoffP, hoffP', h2P, h2P'⟩ :=
    GlobalTheory.T.exists_conjugate_splitPlace_off_stableSet D (D.ntw.S0 i) Rl.Sb P (fun P1 P2 h h' => hS0c i P1 P2 h h') (hS02 i) (hS0b i) hPs hP0
  obtain ⟨α, α', R, R', hα, hRd, hα', hRd', hxR, hyR, hadj⟩ :=
    GlobalTheory.T.complexHecke_conjugatePlace_petersson_adjoint Rl F hR i0 k P P' hPs hPP' hoffP hoffP' h2P h2P' hk1 hk2
  have hkP : HkIdx i k P := ⟨hk1, hk2, hPs, hP0⟩
  have hkP' : HkIdx i k P' := ⟨hk1, hk2, hP's, hP'0⟩
  obtain ⟨hPQ, hPg⟩ := GlobalTheory.T.heckeOperatorsRationalForms_commute Rl cG S Y H hG hC i hi ((i0 : ℕ) + 1) h1 h2 b k P k P' hkP hkP'
  obtain ⟨-, hQg⟩ := GlobalTheory.T.heckeOperatorsRationalForms_commute Rl cG S Y H hG hC i hi ((i0 : ℕ) + 1) h1 h2 b k P' k P hkP' hkP

  set s := (D.nexp.eAlg i b).coeff.support with hs
  have hsupp : ∀ g, g ∉ s → D.nexp.eLL0 g = 0 := fun g hg => by
    have h0 : (D.nexp.eAlg i b).coeff g = 0 := Finsupp.notMem_support_iff.1 hg
    have hcoef : (D.nexp.eAlg i b).coeff g = readLL0 S i b (D.nexp.eLL0 g) := by
      rw [D.nexp.eAlg_def]; rfl
    rw [hcoef] at h0
    exact (map_eq_zero_iff _ (readLL0 S i b).injective).1 h0
  set σ0 := Formalism.IndefR.Links.sg0 D A3.A with hσ0
  set hst := Y.rho ((i0 : ℕ) + 1) h1 h2 with hhst
  set hχ := Y.chi ((i0 : ℕ) + 1) h1 h2 with hhχ
  set E := goodProjectorBaseChangeForms S ((i0 : ℕ) + 1) hst hχ D.nexp.eLL0 with hE
  set V := LinearMap.range E with hV
  set Tp := opK S ((i0 : ℕ) + 1) (H.hL ((i0 : ℕ) + 1) k P) (fun x hx => H.hs ((i0 : ℕ) + 1) h1 h2 k P x hx) with hTp
  set Tq := opK S ((i0 : ℕ) + 1) (H.hL ((i0 : ℕ) + 1) k P') (fun x hx => H.hs ((i0 : ℕ) + 1) h1 h2 k P' x hx) with hTq
  set T0 := LinearMap.baseChange ↥D.LL0 Tp with hT0
  set T0' := LinearMap.baseChange ↥D.LL0 Tq with hT0'
  have hTE : T0 * E = E * T0 := goodProjector_comm S _ hst hχ _ s hsupp Tp hPg
  have hTE' : T0' * E = E * T0' := goodProjector_comm S _ hst hχ _ s hsupp Tq hQg
  have hVT : ∀ z ∈ V, T0 z ∈ V := by
    rintro _ ⟨y, rfl⟩
    exact ⟨T0 y, (LinearMap.congr_fun hTE y).symm⟩
  have hVT' : ∀ z ∈ V, T0' z ∈ V := by
    rintro _ ⟨y, rfl⟩
    exact ⟨T0' y, (LinearMap.congr_fun hTE' y).symm⟩
  have hbm : ∀ f g : Module.End S.Ks (FmK S ((i0 : ℕ) + 1)),
      LinearMap.baseChange ↥D.LL0 (f * g) = LinearMap.baseChange ↥D.LL0 f * LinearMap.baseChange ↥D.LL0 g :=
    fun f g => LinearMap.baseChange_comp g f
  have hPQc : T0 * T0' = T0' * T0 := by rw [hT0, hT0', ← hbm, hPQ, hbm]

  have hfix : ∀ z ∈ V, goodProjW S ((i0 : ℕ) + 1) D.nexp.eLL0 (inWL S ((i0 : ℕ) + 1) z) = inWL S ((i0 : ℕ) + 1) z := by
    rintro _ ⟨y, rfl⟩
    rw [inForms_goodProjector S _ hst hχ _ s hsupp y, ← Module.End.mul_apply, GlobalTheory.T.good_projector_forms_idempotent D S ((i0 : ℕ) + 1) i]
  have hT0w : ∀ z, inWL S ((i0 : ℕ) + 1) (T0 z) = H.hL ((i0 : ℕ) + 1) k P (inWL S ((i0 : ℕ) + 1) z) := fun z =>
    inWL_opK S _ _ _ z
  have hT0w' : ∀ z, inWL S ((i0 : ℕ) + 1) (T0' z) = H.hL ((i0 : ℕ) + 1) k P' (inWL S ((i0 : ℕ) + 1) z) := fun z =>
    inWL_opK S _ _ _ z

  set φ : ↥D.LL0 →+* ℂ := σ0.comp (algebraMap ↥D.LL0 D.what₂.LL) with hφ
  let jm : ↥V →ₛₗ[φ] (Rl.HW i0 σ0).H :=
    { toFun := fun z => (Rl.FW i0).j σ0 ((Y.fi i0).e (inWL S ((i0 : ℕ) + 1) z.1))
      map_add' := fun z w => by
        show (Rl.FW i0).j σ0 ((Y.fi i0).e (inWL S ((i0 : ℕ) + 1) (z.1 + w.1))) = _
        rw [map_add, map_add, map_add]
      map_smul' := fun c z => by
        show (Rl.FW i0).j σ0 ((Y.fi i0).e (inWL S ((i0 : ℕ) + 1) (c • z.1))) = _
        rw [inWL_smul, LinearEquiv.map_smul, LinearMap.map_smulₛₗ]
        rfl }
  have hjm : ∀ z : ↥V, jm z = (Rl.FW i0).j σ0 ((Y.fi i0).e (inWL S ((i0 : ℕ) + 1) z.1)) := fun _ => rfl

  have he : Function.Injective (Rl.HW i0 σ0).e := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨y', hy'⟩ := hyR x
    have h0 := hadj 0 x x y' (by rw [hx, map_zero, map_zero]) hy'
    rw [inner_zero_left] at h0
    exact inner_self_eq_zero.1 h0
  obtain ⟨S0, hS0⟩ := exists_lift_end _ he _ hxR
  obtain ⟨S1, hS1⟩ := exists_lift_end _ he _ hyR

  set c : ℂ := (((Rl.C.mu0 i0).val P : ℂˣ) : ℂ)⁻¹ ^ k *
    (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹ with hc
  set c' : ℂ := (((Rl.C.mu0 i0).val P' : ℂˣ) : ℂ)⁻¹ ^ k *
    (((Nat.card (Formalism.L2.DIV.kP P') : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹ with hc'
  have hc'0 : c' ≠ 0 := by
    have hq : ((Nat.card (Formalism.L2.DIV.kP P') : ℕ) : ℂ) ≠ 0 := by
      haveI := Ideal.finiteQuotientOfFreeOfNeBot P'.asIdeal P'.ne_bot
      exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (Units.ne_zero _))) (inv_ne_zero (pow_ne_zero _ hq))
  set T : Module.End ↥D.LL0 ↥V := T0.restrict hVT with hT
  set T' : Module.End ↥D.LL0 ↥V := T0'.restrict hVT' with hT'
  have htie : ∀ z : ↥V, (Rl.HW i0 σ0).e (jm (T z)) = c • Formalism.IndefR.Mult.heckeOn (Rl.MW i0 σ0) R ((Rl.HW i0 σ0).e (jm z)) := by
    intro z
    have h := hX.tie i0 k P hPs hoffP ⟨i, hP0⟩ h2P hk2 α R hα hRd (inWL S ((i0 : ℕ) + 1) z.1) (hfix z.1 z.2)
    rw [hjm, hjm]
    show (Rl.HW i0 σ0).e ((Rl.FW i0).j σ0 ((Y.fi i0).e (inWL S ((i0 : ℕ) + 1) (T0 z.1)))) = _
    rw [hT0w]
    exact h
  have htie' : ∀ z : ↥V, (Rl.HW i0 σ0).e (jm (T' z)) = c' • Formalism.IndefR.Mult.heckeOn (Rl.MW i0 σ0) R' ((Rl.HW i0 σ0).e (jm z)) := by
    intro z
    have h := hX.tie i0 k P' hP's hoffP' ⟨i, hP'0⟩ h2P' hk2 α' R' hα' hRd' (inWL S ((i0 : ℕ) + 1) z.1) (hfix z.1 z.2)
    rw [hjm, hjm]
    show (Rl.HW i0 σ0).e ((Rl.FW i0).j σ0 ((Y.fi i0).e (inWL S ((i0 : ℕ) + 1) (T0' z.1)))) = _
    rw [hT0w']
    exact h
  set SS : Module.End ℂ (Rl.HW i0 σ0).H := c • S0 with hSS
  set SS' : Module.End ℂ (Rl.HW i0 σ0).H := (starRingEnd ℂ c) • S1 with hSS'
  have hSj : ∀ z : ↥V, SS (jm z) = jm (T z) := by
    intro z
    apply he
    rw [htie z, hSS, LinearMap.smul_apply, map_smul, hS0]
  have hS'j : ∀ z : ↥V, SS' (jm z) = (starRingEnd ℂ c * c'⁻¹) • jm (T' z) := by
    intro z
    have h2 : jm (T' z) = c' • S1 (jm z) := he (by rw [htie' z, map_smul, hS1])
    rw [hSS', LinearMap.smul_apply, h2, smul_smul, mul_assoc, inv_mul_cancel₀ hc'0, mul_one]
  have hTT : ∀ z : ↥V, T (T' z) = T' (T z) := fun z => Subtype.ext (LinearMap.congr_fun hPQc z.1)

  obtain ⟨nb, bs, hbs, -, hspan, hbLL, -⟩ := GlobalTheory.T.isKsForm_of_algebraicFormsIso _ _ (Y.fi i0) (hI i0).1
  haveI : IsScalarTower S.Ks ↥D.LL0 D.what₂.LL := IsScalarTower.of_algebraMap_eq fun x => (S.kKs_spec x).symm
  haveI : Module.Finite S.Ks (FmK S ((i0 : ℕ) + 1)) := by
    have h := FiniteDimensional.span_of_finite S.Ks (Set.finite_range bs)
    rw [hspan] at h
    exact h
  haveI : FiniteDimensional ↥D.LL0 ↥V := inferInstance
  have hind : ∀ (n : ℕ) (x : Fin n → ↥V), LinearIndependent ↥D.LL0 x → LinearIndependent ℂ (fun a => jm (x a)) := by
    intro n x hx
    have hx1 : LinearIndependent ↥D.LL0 (fun a => (x a : ↥D.LL0 ⊗[S.Ks] FmK S ((i0 : ℕ) + 1))) :=
      hx.map' V.subtype (Submodule.ker_subtype V)
    have hx2 : LinearIndependent D.what₂.LL (fun a => inWL S ((i0 : ℕ) + 1) (x a).1) :=
      GlobalTheory.T.linearIndependent_forms_intermediate_field S.Ks ↥D.LL0 D.what₂.LL (S.WL ((i0 : ℕ) + 1)) (S.A ((i0 : ℕ) + 1)).WK nb bs hbs hspan hbLL
        (inWL S ((i0 : ℕ) + 1)) (fun _ _ => rfl) n (fun a => (x a).1) hx1
    have hx3 : LinearIndependent D.what₂.LL (fun a => (Y.fi i0).e (inWL S ((i0 : ℕ) + 1) (x a).1)) :=
      hx2.map' (Y.fi i0).e.toLinearMap (LinearEquiv.ker _)
    exact (hU i0 σ0).1 n _ hx3
  have hkeep : ∀ u ∈ Submodule.span ℂ (Set.range jm), SS' u ∈ Submodule.span ℂ (Set.range jm) := by
    intro u hu
    have hle : Submodule.span ℂ (Set.range jm) ≤ (Submodule.span ℂ (Set.range jm)).comap SS' := by
      rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      show SS' (jm z) ∈ Submodule.span ℂ (Set.range jm)
      rw [hS'j]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨T' z, rfl⟩)
    exact hle hu
  have hcomm : ∀ u ∈ Submodule.span ℂ (Set.range jm), SS (SS' u) = SS' (SS u) := by
    intro u hu
    have hle : Submodule.span ℂ (Set.range jm) ≤ LinearMap.eqLocus (SS * SS') (SS' * SS) := by
      rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      show SS (SS' (jm z)) = SS' (SS (jm z))
      rw [hS'j, map_smul, hSj, hSj, hS'j, hTT]
    exact hle hu
  have hadj' : ∀ u ∈ Submodule.span ℂ (Set.range jm), ∀ v ∈ Submodule.span ℂ (Set.range jm),
      inner ℂ (SS u) v = inner ℂ u (SS' v) := by
    intro u _ v _
    rw [hSS, hSS', LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
      hadj u v (S0 u) (S1 v) (hS0 u) (hS1 v)]
  have hsep := GlobalTheory.T.minpoly_separable_of_complex_normal_reading ↥D.LL0 ↥V (Rl.HW i0 σ0).H φ jm T SS SS' hind (fun z => (hSj z).symm) hkeep hadj' hcomm
  refine ⟨minpoly ↥D.LL0 T, hsep, fun z hz => ?_⟩
  have h := aeval_map_of_comm V.subtype T T0 (fun _ => rfl) (minpoly ↥D.LL0 T) ⟨z, hz⟩
  rw [minpoly.aeval, LinearMap.zero_apply, map_zero] at h
  exact h.symm

end GlobalTheory.GoodSS.Heart
