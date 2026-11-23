import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LevelVectorSizeBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalConjChrEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalConjEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurComponentsSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsMultIPOfModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulNormSqLeNormProjApplySqOfSpanningParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodScalarOfIsAdelicScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicScalarBase
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.Survey.LevelVectorSizeBounds

namespace GlobalTheory.LowForm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem op_idem {G H : Type} [Group G] [Fintype G] [AddCommGroup H] [Module ℂ H] (ρ : Representation ℂ G H) {a : G → ℂ}
    (ha : GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents.IsCentralIdem a) (u : H) :
    (∑ g, a g • ρ g : H →ₗ[ℂ] H) ((∑ g, a g • ρ g : H →ₗ[ℂ] H) u) = (∑ g, a g • ρ g : H →ₗ[ℂ] H) u := by
  set E : H →ₗ[ℂ] H := ∑ g, a g • ρ g with hE
  have h1 : E u = ∑ g, ∑ h, (a h * a (h⁻¹ * g)) • ρ g u := by
    simp only [← Finset.sum_smul, ha.2, hE, LinearMap.sum_apply, LinearMap.smul_apply]
  have h2 : E (E u) = ∑ h, ∑ g, (a h * a g) • ρ h (ρ g u) := by
    simp only [hE, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [h2, h1, Finset.sum_comm (f := fun g h => (a h * a (h⁻¹ * g)) • ρ g u)]
  refine Finset.sum_congr rfl fun h _ => Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

theorem adjoint_eq_self {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (E : H →ₗ[ℂ] H)
    (h1 : ∀ u, E (E u) = E u) (h2 : ∀ x, E x = x → ∀ y, ⟪x, E y⟫_ℂ = ⟪x, y⟫_ℂ) : LinearMap.adjoint E = E := by
  refine LinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  rw [LinearMap.adjoint_inner_left, ← h2 _ (h1 x) y, ← inner_conj_symm, ← h2 _ (h1 y) x, inner_conj_symm]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem eC_idem_at (hr : R.grp_record) (σ : D.what₂.LL →+* ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents.IsCentralIdem (RealDat.eC (A := A) σ) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.LiftScalarCompare.eC_idem hr
  unfold RealDat.eC at h1 h2 ⊢
  refine ⟨fun g k => congrArg σ ((sg0 D A).injective (h1 g k)), fun g => ?_⟩
  have := h2 g
  simp only [← map_mul, ← map_sum] at this ⊢
  exact congrArg σ ((sg0 D A).injective this)

theorem projH_idem (h : R.Char F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    projH R i σ (projH R i σ x) = projH R i σ x := op_idem (R.gW i σ) (eC_idem_at h.grp.record σ) x

theorem projH_adjoint (h : R.Char F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    LinearMap.adjoint (projH R i σ) = projH R i σ :=
  adjoint_eq_self _ (projH_idem h i σ) fun _ hx y => GlobalTheory.LiftScalarCompare.adjoint_idem (R.gW i σ)
    (GlobalTheory.gW_norm_eq R h.models.HW h.models.gW h.models.νW i σ) (eC_idem_at h.grp.record σ) hx y

open Classical in
variable (R) in

def blkChar (i : Fin D.R.m) : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ :=
  fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR A.μ0 PP

def conjChar (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ :=
  fun PP => (Units.map (s : ℂ →+* ℂ).toMonoidHom).comp (m PP)

theorem twVal_zero {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    twVal χ 0 P k = ((χ.locK P k : ℂˣ) : ℂ) := by
  unfold twVal
  simp

theorem isConjChars_at (h : R.Char F) (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} (hσ : IsEmbOverK D σ s)
    {μ' η' : (AE D)ˣ →* Circle} (hμ : ChiAt R i σ μ') (hη : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η') :
    IsConjChars R i A.μ0 s μ' η' (conjChar s (blkChar R i)) := by
  obtain ⟨μH, a1, a2⟩ := GlobalTheory.ConjMuChar.exists_galConj_chrEq R F h i σ s hσ μ' hμ
  obtain ⟨ηH, b1, b2⟩ := GlobalTheory.EtaConjChar.exists_galConj_eta R F h σ s hσ η' hη
  obtain ⟨μB, -, c1, -, -, -, c2⟩ := isConjChars_base R h i A.μ0
  refine ⟨μH, ηH, a1, b1, a2, b2, fun PP hP a k u hk hu => Units.ext ?_⟩
  have e1 := a1 PP k
  have e2 := c1 PP k
  rw [twVal_zero, twVal_zero] at e1 e2
  have e3 := c2 PP hP a k u hk hu
  rw [e1]
  exact congrArg s ((congrArg Units.val e3).trans e2)

theorem levFn_conj {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (r : ℕ) (hr : r ≤ n) (t s' : ℕ) (Pg Q : Finset (Pl D.host.E))
    (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x) :
    ((levFn β ⟨r, hr, t, s', Pg, Q, LevelP.triv _ _ _, fun _ => conjChar s m, conjChar s m⟩ x : ℂˣ) : ℂ) =
      s ((levFn β ⟨r, hr, t, s', Pg, Q, LevelP.triv _ _ _, fun _ => m, m⟩ x : ℂˣ) : ℂ) := by
  unfold levFn
  have e : ∀ y, ext1 (LevelP.triv Pg r ℂ).H (LevelP.triv Pg r ℂ).chi y = 1 := fun y => Lev.subgroupCharExtension_one_apply _ _
  simp only [e, one_mul, Units.val_mul, Units.coe_prod, map_mul, map_prod]
  rfl

theorem chrOf_conj (i : Fin D.R.m) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : levJ R i A.μ0) :
    ((chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv (conjChar s m)) k : ℂˣ) : ℂ) =
      s ((chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) k : ℂˣ) : ℂ) :=
  levFn_conj (R.βV i) D.R.r (r_le_V i) D.R.t 1 R.Pg (R.Q A.μ0) s m (Formalism.UG.bc (Lev.swapAE D) k.1.1)

theorem chr_at (h : R.Char F) (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} (hσ : IsEmbOverK D σ s)
    (χ' : levJ R i A.μ0 →* ℂˣ)
    (hχ : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjVal σ (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) ((χ' k : ℂˣ) : ℂ)) :
    chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv (conjChar s (blkChar R i))) = χ' := by
  refine MonoidHom.ext fun k : levJ R i A.μ0 => Units.ext ?_
  refine (hχ k).elim fun y hy => ?_
  have h1 := hy.1
  have h2 := hy.2
  have e1 := congrArg Units.val (DFunLike.congr_fun (chr_base R h i A.μ0) k)
  have e2 := chrOf_conj (R := R) i s (blkChar R i) k
  have e3 : ((χ' k : ℂˣ) : ℂ) = s (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) :=
    h2.symm.trans ((hσ.1 y).trans (congrArg s h1))
  exact e2.trans ((congrArg s e1).trans e3.symm)

theorem isLevelVec_at (h : R.Char F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    {f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ}
    (hf : Datum.IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      R.Pg ∅ (fun _ => 1) f₀ f) :
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q A.μ0)
      m f₀ f := by
  rw [Q_base h.lev]
  unfold Datum.IsThPVecOf at hf
  unfold IsLevelVec
  have hQ : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      Datum.omegaQ ∅ (Wc D i).rank m (-1) y = Datum.omegaQ ∅ (Wc D i).rank (fun _ => 1) (-1) y := by
    intro y
    unfold Datum.omegaQ
    simp
  simp only [omegaG_triv, hQ]
  exact hf

theorem hookPlus_le (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i (lab σ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i id) : hookPlus D i ≤ mainTerm D i σ := by
  have e : mainTerm D i σ = GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i (lab σ) := by
    unfold mainTerm GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum
    simp only [Nat.cast_mul]
    rfl
  rw [e, h]
  unfold hookPlus GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum
  refine Finset.sum_le_sum fun ρ _ => Real.log_le_log (Nat.cast_pos.2 (hookProd_pos _)) (Nat.cast_le.2 ?_)
  exact Nat.le_mul_of_pos_right _ (hookProd_pos _)

theorem eq_of_low_at (hW : R.models_HW) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {v : (R.MW i σ).Vec} (hv : IsExtVec (R.MW i σ) v)
    {x y : (R.HW i σ).H}
    (h : ∀ w : ∀ ρ, lowT (R.MW i σ) ρ, (R.HW i σ).e x (fun ρ => w ρ) = (R.HW i σ).e y fun ρ => w ρ) : x = y := by
  have h0 : (R.HW i σ).e (x - y) v = 0 := by
    rw [LinearMap.map_sub]
    exact sub_eq_zero.2 (h fun ρ => ⟨v ρ, (hv ρ).2.1⟩)
  have h1 := (hW i σ).2.2 (x - y) (x - y)
  rw [ipAt, GlobalTheory.EvalAtUnitVector.ipM_self_eq_zero _ _ _ _ v (fun τ => (hv τ).1) h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

theorem lower_of_parts {X Y ι : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T th : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y)
    (P : ι → Submodule ℂ Y) (S : ι → Prop) (a : ℝ) (h1 : LinearMap.adjoint e = e) (h2 : ∀ y, e (e y) = e y)
    (h3 : (⨆ (k) (_ : S k), P k) = ⊤)
    (h4 : ∀ k, P k ≠ ⊥ → ∃ l : ℝ, 0 < l ∧ (∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) ∧ a ≤ Real.log l)
    (h5 : ∀ x, th x = e (T x)) : ∀ x ∈ (LinearMap.ker th)ᗮ, Real.exp a * ‖x‖ ^ 2 ≤ ‖th x‖ ^ 2 := by
  obtain rfl : th = e ∘ₗ T := LinearMap.ext h5
  refine GlobalTheory.mul_norm_sq_le_norm_proj_apply_sq_of_spanning_parts X Y ι T e P _ (Real.exp_pos a) h1 h2 ?_ fun k => ?_
  · exact top_le_iff.1 (h3.ge.trans (iSup₂_le fun k _ => le_iSup P k))
  · by_cases hk : P k = ⊥
    · refine ⟨_, le_rfl, fun y hy => ?_⟩
      rw [hk, Submodule.mem_bot] at hy
      simp [hy]
    · obtain ⟨l, a1, a2, a3⟩ := h4 k hk
      exact ⟨l, (Real.le_log_iff_exp_le a1).1 a3, a2⟩

open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature in

theorem exists_full_lift (hA : AdelicLiftScalar R F) (h : R.Char F) (i : Fin D.R.m) {b : ℝ} (hb : Sizes D i b)
    (ht : PrimeToHost R A.μ0) {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} (hσ : IsEmbOverK D σ s) {v : (R.MW i σ).Vec}
    (hv : IsExtVec (R.MW i σ) v) {c₀ μ' η' c c₁ H j th} (hd : IsConjDatum R i σ c₀ μ' η' c c₁ H j th) :
    ∃ T : H.H →ₗ[ℂ] (R.HW i σ).H, (∀ x, th x = projH R i σ (T x)) ∧
      ∀ ev, typePart R i σ A.μ0 R.triv ev ≠ ⊥ →
        ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i σ A.μ0 R.triv ev, T (adjLev R.triv T x) = (l : ℂ) • x) ∧
          mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l := by
  have hμ := hd.1
  have hη := hd.2.1
  have hF := hd.2.2.1
  refine hd.2.2.2.elim fun ω a => a.elim fun f₀ a => a.elim fun f a => a.elim fun B a => a.elim fun io a =>
    a.elim fun thP a => ?_
  refine hF.model.elim fun χ' hχ => ?_
  have hH := hχ.2
  rw [← chr_at h i hσ χ' hχ.1] at hH
  have key := hA h i b hb A.μ0 ht σ s hσ R.triv (isLocal_triv R) _ _ _ (isConjChars_at h i hσ hμ hη) ω a.1 B a.2.2.1 f₀ f
    (isLevelVec_at h i σ _ a.2.1) a.2.2.2.1 c hF.coef io a.2.2.2.2.1 (R.νV i A.μ0) (R.fdV i A.μ0) (h.models.νV i A.μ0) _
    (R.B.L i A.μ0).pres.y (R.B.L i A.μ0).pres.reps H hH
  refine key.1.elim fun T hT => ⟨T, fun x => eq_of_low_at h.models.HW hv fun w => ?_, key.2 T hT⟩
  have e1 : (R.HW i σ).e (T x) (fun ρ => w ρ) = thP ((c.ext ∘ₗ H.e).rangeRestrict x) (PiTensorProduct.tprod ℂ w) :=
    funext fun g => (hT x w g).2.trans
      (GlobalTheory.BaseScalar.integrableOn_of_isThetaLift a.2.2.2.2.2.1 x (PiTensorProduct.tprod ℂ w) g).2.symm
  have e2 : (R.HW i σ).e (projH R i σ (T x)) (fun ρ => w ρ) = R.eWf i σ ((R.HW i σ).e (T x) fun ρ => w ρ) :=
    congrArg (fun U : MMap (R.MW i σ) => U fun ρ => w ρ) (e_projH h.models.gW i σ (T x))
  exact (a.2.2.2.2.2.2 x w).trans (e2.trans (congrArg (R.eWf i σ) e1)).symm

theorem parts_scalar (h : R.Char F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) {b : ℝ}
    (hlog : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i (lab σ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i id)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] (T : X →ₗ[ℂ] (R.HW i σ).H)
    (hT : ∀ ev, typePart R i σ A.μ0 R.triv ev ≠ ⊥ →
        ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i σ A.μ0 R.triv ev, T (adjLev R.triv T x) = (l : ℂ) • x) ∧
          mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l) :
    ∀ ev, partH R i σ ev ≠ ⊥ → ∃ l : ℝ, 0 < l ∧ (∀ y ∈ partH R i σ ev, T (LinearMap.adjoint T y) = (l : ℂ) • y) ∧
      GlobalTheory.BigOn.lowB D i b ≤ Real.log l := by
  intro ev hev
  have e := LiftLower.typePart_base h.lev i σ ev
  refine (hT ev (fun h0 => hev (e.symm.trans h0))).elim fun l a => ?_
  refine ⟨l, a.1, fun y hy => ?_, le_trans (sub_le_sub_right (hookPlus_le i σ hlog) _) a.2.2⟩
  have e1 := LinearMap.congr_fun (GlobalTheory.BaseScalar.adjLev_triv R T) y
  have e2 := a.2.1 y (e.ge hy)
  exact (congrArg T e1).symm.trans e2

open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature in

theorem conjLift_lower (hA : AdelicLiftScalar R F) (h : R.Char F) (i : Fin D.R.m) {b : ℝ} (hb : Sizes D i b)
    (ht : PrimeToHost R A.μ0) {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} (hσ : IsEmbOverK D σ s) {v : (R.MW i σ).Vec}
    (hv : IsExtVec (R.MW i σ) v) (hlog : logHookSum i (lab σ) = logHookSum i id) {c₀ μ' η' c c₁ H j th}
    (hd : IsConjDatum R i σ c₀ μ' η' c c₁ H j th) :
    ∀ x ∈ (LinearMap.ker th)ᗮ, Real.exp (GlobalTheory.BigOn.lowB D i b) * ‖x‖ ^ 2 ≤ ‖th x‖ ^ 2 := by
  refine (exists_full_lift hA h i hb ht hσ hv hd).elim fun T hT => ?_
  have p1 := projH_adjoint h i σ
  have p2 := projH_idem h i σ
  have p3 := GlobalTheory.PrincipalDecomp.iSup_partH_eq_top R F h i σ (schurMult_of_models R h.models.HW i σ)
  have p4 := parts_scalar h i σ (b := b) hlog T hT.2
  exact lower_of_parts T th (projH R i σ) (partH R i σ) (IsNormSys R i) _ p1 p2 p3 p4 hT.1

end GlobalTheory.LowForm

end
