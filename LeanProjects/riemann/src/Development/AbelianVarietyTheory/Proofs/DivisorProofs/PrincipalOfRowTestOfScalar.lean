import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemRangeToF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TranslateRepresentations
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DownUpLambdaOperators

noncomputable section

open Module NumberField
open scoped InnerProductSpace Matrix
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult

namespace GlobalTheory.OneFormTest

theorem tw_span_top (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {I : Type} (v : I → E)
    (h : Submodule.span ℂ (Set.range v) = ⊤) : Submodule.span ℂ (Set.range fun i => Tw.mk s (v i)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : Tw.out x ∈ Submodule.span ℂ (Set.range v) := h ▸ Submodule.mem_top
  have key : ∀ y ∈ Submodule.span ℂ (Set.range v),
      Tw.mkL s E y ∈ Submodule.span ℂ (Set.range fun i => Tw.mk s (v i)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  exact key _ hx

theorem tw_map_surjective (s : Bool) {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E']
    [InnerProductSpace ℂ E'] {f : E →ₗ[ℂ] E'} (h : Function.Surjective f) : Function.Surjective (Tw.map s f) := h

theorem model_of_pres {H Γ : Type} [Group H] [Group Γ] {ι : Γ →* H} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup H}
    {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (H → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) (j : S.Forms →ₛₗ[σ] M.H) (hj : ∀ x, M.e (j x) = P.extL x) :
    (∀ x y, ⟪j x, j y⟫_ℂ = σ (S.csum x.1 y.1)) ∧ Function.Injective j ∧ Submodule.span ℂ (Set.range j) = ⊤ := by
  obtain ⟨-, ⟨h1, h2⟩, h3⟩ := GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ P
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · rw [hM.2.2, hj, hj]
    exact h3 x y
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h4 : P.extL x = 0 := by rw [← hj, hx, map_zero]
    rw [← S.basis.sum_repr x, map_sum] at h4
    simp only [map_smulₛₗ] at h4
    have h5 := Fintype.linearIndependent_iff.1 h1 _ h4
    refine S.basis.repr.injective (Finsupp.ext fun i => ?_)
    rw [(map_eq_zero _).1 (h5 i), map_zero, Finsupp.zero_apply]
  · apply Submodule.map_injective_of_injective hM.1
    rw [Submodule.map_top, hM.2.1, Submodule.map_span, ← Set.range_comp, show M.e ∘ j = P.extL from funext hj, h2]

theorem apply_gaOp {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms) {H E : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ G E) (j : S.Forms →ₛₗ[σ] H) (Θ : H →ₗ[ℂ] E) (h : ∀ g x, Θ (j (r g x)) = ρ g (Θ (j x)))
    (Y : Finset (G → K)) (hY : ∀ y, ∑ g, σ ((idemOf Y).coeff g) • ρ g y = y) (x : S.Forms) :
    Θ (j (S.gaOp r (goodAt Y ⊥ 1) x)) = Θ (j x) := by
  rw [goodAt, level_idempotent_bot, mul_one, CSD.gaOp, LinearMap.sum_apply, map_sum, map_sum, ← hY (Θ (j x))]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, map_smulₛₗ, map_smul, h]

theorem surjective_of_scalar {H E : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup E] [Module ℂ E] (f : H →ₗ[ℂ] E)
    (g : E →ₗ[ℂ] H) {I : Type} (p : I → Submodule ℂ E) (hp : ⨆ c, p c = ⊤)
    (h : ∀ c, ∃ l : ℝ, 0 < l ∧ ∀ x ∈ p c, (f ∘ₗ g) x = (l : ℂ) • x) : Function.Surjective f := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hp, iSup_le_iff]
  intro c x hx
  obtain ⟨l, hl, h⟩ := h c
  refine ⟨(l : ℂ)⁻¹ • g x, ?_⟩
  have h1 : f (g x) = (l : ℂ) • x := h x hx
  rw [map_smul, h1, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hl.ne'), one_smul]

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem model_jX (hH : R.models_HX) (hj : R.models_jX) (t : T) :
    (∀ x y : (A.MtildeCSD t).Forms, ⟪R.jX t x, R.jX t y⟫_ℂ = D.what₂.embLL ((A.MtildeCSD t).csum x.1 y.1)) ∧
      Function.Injective (R.jX t) ∧ Submodule.span ℂ (Set.range (R.jX t)) = ⊤ :=
  model_of_pres (S := A.MtildeCSD t) (R.B.R t).pres (R.HX t) (hH t) (R.jX t) (hj t)

theorem formsTie (hH : R.models_HX) (hj : R.models_jX) : FormsTie (F := A.fam) (R.toCx F) where
  inner_eq t x y := ((congrArg (cj (twAt D.what₂.embLL A.v0)) ((model_jX R hH hj t).1 x y)).trans (R.emb0 _).symm :)
  inj t := (model_jX R hH hj t).2.1
  span t := tw_span_top (twAt D.what₂.embLL A.v0) (R.jX t) (model_jX R hH hj t).2.2

theorem sum_gE_eq (hE : R.models_HE) (hg : R.models_gE) (y : R.HE.H) :
    ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gE g y = y := by
  apply hE.1
  have h1 : R.HE.e y ∈ R.EEat R.triv := hE.2.1 ▸ ⟨y, rfl⟩
  have h2 : postOn (R.MY 0) R.e0 (R.HE.e y) = R.HE.e y := sub_eq_zero.1 h1.2
  rw [map_sum]
  refine Eq.trans ?_ h2
  simp only [map_smul, hg]
  ext v h
  simp [RealDat.e0, gaL, postOn, RealDat.eC]
  rfl

theorem isTranslate_jX (hred : R.grp_red_R) (hj : R.models_jX) (t : T) (g : G) (x : (A.MtildeCSD t).Forms) :
    GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.IsTranslate D.sp.X' R.βX (R.datXt t) (R.eG g) ((R.HX t).e (R.jX t x))
      ((R.HX t).e (R.jX t (A.leftGroupActionRight t g x))) := by
  have e1 := hj t x
  have e2 := hj t (A.leftGroupActionRight t g x)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.IsTranslate
  refine ⟨?_, fun κ hκ h => ?_⟩
  · obtain ⟨q, hq⟩ := (R.B.R t).act_tie.red_surj g
    exact ⟨q, (hred t q).symm.trans (congrArg R.eG hq)⟩
  · have h1 : (R.B.R t).act_tie.red κ = g := R.eG.injective ((hred t κ).trans hκ)
    have h2 := ((e2.trans ((R.B.R t).act_tie.act_eq g κ h1 x)).trans
      (congrArg (Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch κ) e1.symm))
    exact congrFun h2 h

theorem th_gaOp (hC : R.Char F) (hG : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.GEquiv R) (t : T) (x : (A.MtildeCSD t).Forms) :
    R.Th t (R.jX t ((A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (goodAt A.X ⊥ 1) x)) = R.Th t (R.jX t x) :=
  apply_gaOp (S := A.MtildeCSD t) (A.leftGroupActionRight t) R.gE (R.jX t) (R.Th t)
    (fun g y => hG.th_of_translate R t (hC.models.HX t).1 g _ _ (isTranslate_jX R hC.grp.red_R hC.models.jX t g y))
    A.X (sum_gE_eq R hC.models.HE hC.models.gE) x

theorem throughGood (hC : R.Char F) (hG : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.GEquiv R) (F' : Face D A) : ThroughGood (F := A.fam) (R.toCx F') :=
  fun t x => th_gaOp R F hC hG t x

def PartsSpan : Prop := ⨆ c, GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.partE R c = ⊤

theorem th_surjective (hB : GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.Concl R) (hS : PartsSpan R) (t : T) : Function.Surjective (R.Th t) :=
  surjective_of_scalar (R.Th t) (LinearMap.adjoint (R.Th t)) (GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.partE R) hS (hB.scalar_pos t)

theorem theta_surjective (hon : ∀ t, Function.Surjective (R.Th t)) (t : T) : Function.Surjective ((R.toCx F).Θ t) :=
  tw_map_surjective (twAt D.what₂.embLL A.v0) (hon t)

theorem principal_of_rowTest {s : ℕ} (hOk : A.fam.Ok s) (hC : R.Char F) (hG : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.GEquiv R)
    (hT : GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestAt R F) (hon : ∀ t, Function.Surjective (R.Th t)) :
    (∀ t, Function.Bijective ((R.toCx (GlobalTheory.OneForm.principalFace F)).iC (GlobalTheory.OneForm.principalFace F).cr false t)) ∧
      (R.toCx (GlobalTheory.OneForm.principalFace F)).RATmu (GlobalTheory.OneForm.principalFace F).cr false :=
  bijective_and_ratMu (F := A.fam) (X := R.toCx (GlobalTheory.OneForm.principalFace F)) hOk
    (formsTie R _ hC.models.HX hC.models.jX) (throughGood R F hC hG _)
    ((GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.rowTest_toCx_iff R _).2 ((GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.rowTest_toCx_iff R F).1 (hT hC))) (theta_surjective R _ hon) _ false
    (GlobalTheory.EquivariantEuclideanComplex.isCoord_base A ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc _)

theorem principal_of_rowTest_of_scalar {s : ℕ} (hOk : A.fam.Ok s) (hC : R.Char F) (hG : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.GEquiv R)
    (hT : GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestAt R F) (hB : GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.Concl R) (hS : PartsSpan R) :
    (∀ t, Function.Bijective ((R.toCx (GlobalTheory.OneForm.principalFace F)).iC (GlobalTheory.OneForm.principalFace F).cr false t)) ∧
      (R.toCx (GlobalTheory.OneForm.principalFace F)).RATmu (GlobalTheory.OneForm.principalFace F).cr false :=
  principal_of_rowTest R F hOk hC hG hT (th_surjective R hB hS)

end Concrete

end GlobalTheory.OneFormTest
