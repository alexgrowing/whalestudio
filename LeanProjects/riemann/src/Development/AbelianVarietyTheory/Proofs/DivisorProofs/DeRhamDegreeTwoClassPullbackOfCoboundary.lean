import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedPre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsBijectiveDegreeOneTwoStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.PullTwo

section Lift

variable {D : Data} (Λ : Lift D)

def j1 (U : AffOp D.X) : Ω[Sec D.s U.unop.1⁄D.R] →+ K1 D.R (Λ.L.obj U).δ where
  toFun ω := Submodule.Quotient.mk ((Λ.semi U).m1 ω)
  map_zero' := by rw [map_zero, Submodule.Quotient.mk_zero]
  map_add' a b := by rw [map_add, Submodule.Quotient.mk_add]

def j2 (U : AffOp D.X) : Om D.R (Sec D.s U.unop.1) 2 →+ K D.R (Λ.L.obj U).δ 2 where
  toFun ω := Submodule.Quotient.mk ((Λ.semi U).mOm 2 ω)
  map_zero' := by rw [map_zero, Submodule.Quotient.mk_zero]
  map_add' a b := by rw [map_add, Submodule.Quotient.mk_add]

theorem compatibleOneFormClass_restriction_natural {U V : AffOp D.X} (a : U ⟶ V) (ω : Ω[Sec D.s U.unop.1⁄D.R]) :
    j1 Λ V (p1 (OAff D.s) a ω) = km1 (SemiHom.of_algHom (Λ.L.map a).φ) (Λ.L.map a).dp (j1 Λ U ω) := by
  show (Submodule.Quotient.mk ((Λ.semi V).m1 ((semiHom_mp (OAff D.s) a).m1 ω)) : K1 D.R (Λ.L.obj V).δ) =
    km1 (SemiHom.of_algHom (Λ.L.map a).φ) (Λ.L.map a).dp (Submodule.Quotient.mk ((Λ.semi U).m1 ω))
  rw [divPowerCompatOneFormMap_mk]
  congr 1
  rw [SemiHom.oneFormMap_comp_oneFormMap (semiHom_mp (OAff D.s) a) (Λ.semi V) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
      (fun _ ↦ rfl),
    SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) (SemiHom.of_algHom (Λ.L.map a).φ) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
      (fun b ↦ (Λ.nat a b).symm)]

theorem compatibleOneFormClass_kaehler_differential (U : AffOp D.X) (b : Sec D.s U.unop.1) :
    j1 Λ U (KaehlerDifferential.D D.R _ b) = kd0 D.R (Λ.L.obj U).δ (Λ.e U b) := by
  show (Submodule.Quotient.mk ((Λ.semi U).m1 (KaehlerDifferential.D D.R _ b)) : K1 D.R (Λ.L.obj U).δ) = _
  rw [SemiHom.m1_D, divPowerCompatFunctionDifferential_apply]
  all_goals rfl

theorem compatibleTwoFormClass_exterior_derivative (U : AffOp D.X) (ω : Ω[Sec D.s U.unop.1⁄D.R]) :
    j2 Λ U (dOne D.R _ ω) = kd1 D.R (Λ.L.obj U).δ (j1 Λ U ω) := by
  show (Submodule.Quotient.mk ((Λ.semi U).mOm 2 (dOne D.R _ ω)) : K D.R (Λ.L.obj U).δ 2) =
    kd1 D.R (Λ.L.obj U).δ (Submodule.Quotient.mk ((Λ.semi U).m1 ω))
  rw [SemiHom.mOm_dOne, divPowerCompatOneFormDerivative_mk]

end Lift

section Pull

variable {D D' : Data} (Λ : Lift D) (Λ' : Lift D') {σ : D.R →+* D'.R} {φ : D'.X ⟶ D.X} {φ₀ : D'.X₀ ⟶ D.X₀}
  (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
  (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
    Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))

include hθ

theorem movedDatum_compatibleOneFormClass (p : (Pair φ)ᵒᵖ) (ω : Ω[Sec D.s p.unop.1.2.1⁄D.R]) :
    ((pairB Λ' φ m).pre θ).a1 p (j1 Λ (Opposite.op p.unop.1.2) ω) =
      j1 Λ' (Opposite.op p.unop.1.1) ((semiHom_secPull hφ p.unop).m1 ω) := by
  exact congrArg Submodule.Quotient.mk
    (((congrArg (morSemi m ((pairFst φ ⋙ Λ'.L).obj p)).m1 (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi (Opposite.op p.unop.1.2)) (SemiHom.of_algHom (θ.app p).φ)
      ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (fun _ ↦ rfl) ω)).trans
      (SemiHom.oneFormMap_comp_oneFormMap ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (morSemi m ((pairFst φ ⋙ Λ'.L).obj p))
        ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1))) (fun b ↦ hθ p b) ω)).trans
      (SemiHom.oneFormMap_comp_oneFormMap (semiHom_secPull hφ p.unop) (Λ'.semi (Opposite.op p.unop.1.1)) ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1)))
        (fun _ ↦ rfl) ω).symm)

theorem movedDatum_compatibleTwoFormClass (p : (Pair φ)ᵒᵖ) (ω : Om D.R (Sec D.s p.unop.1.2.1) 2) :
    ((pairB Λ' φ m).pre θ).a2 p (j2 Λ (Opposite.op p.unop.1.2) ω) =
      j2 Λ' (Opposite.op p.unop.1.1) ((semiHom_secPull hφ p.unop).mOm 2 ω) := by
  exact congrArg Submodule.Quotient.mk
    (((congrArg ((morSemi m ((pairFst φ ⋙ Λ'.L).obj p)).mOm 2) (SemiHom.mOm_mOm (Λ.semi (Opposite.op p.unop.1.2)) (SemiHom.of_algHom (θ.app p).φ)
      ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (fun _ ↦ rfl) ω)).trans
      (SemiHom.mOm_mOm ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (morSemi m ((pairFst φ ⋙ Λ'.L).obj p))
        ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1))) (fun b ↦ hθ p b) ω)).trans
      (SemiHom.mOm_mOm (semiHom_secPull hφ p.unop) (Λ'.semi (Opposite.op p.unop.1.1)) ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1)))
        (fun _ ↦ rfl) ω).symm)

end Pull

section Pairs

variable {D D' : Data} (Λ' : Lift D') (φ : D'.X ⟶ D.X)

abbrev Kp : Cx (Pair φ)ᵒᵖ := (KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)

def i0 (p : (Pair φ)ᵒᵖ) : (OPair φ D'.s).obj p →+ (Kp Λ' φ).M0.obj p :=
  (Λ'.e ((pairFst φ).obj p)).toAddEquiv.toAddMonoidHom

def i1 (p : (Pair φ)ᵒᵖ) : Ω[(OPair φ D'.s).obj p⁄D'.R] →+ (Kp Λ' φ).M1.obj p := j1 Λ' ((pairFst φ).obj p)

def i2 (p : (Pair φ)ᵒᵖ) : Om D'.R ((OPair φ D'.s).obj p) 2 →+ (Kp Λ' φ).M2.obj p := j2 Λ' ((pairFst φ).obj p)

variable {φ}

theorem pairFirstOpenFunctionSections_natural {p q : (Pair φ)ᵒᵖ} (a : p ⟶ q) (x : (OPair φ D'.s).obj p) :
    i0 Λ' φ q (mp (OPair φ D'.s) a x) = (Kp Λ' φ).M0.map a (i0 Λ' φ p x) := Λ'.nat ((pairFst φ).map a) x

theorem pairFirstOpenOneForms_natural {p q : (Pair φ)ᵒᵖ} (a : p ⟶ q) (x : Ω[(OPair φ D'.s).obj p⁄D'.R]) :
    i1 Λ' φ q (p1 (OPair φ D'.s) a x) = (Kp Λ' φ).M1.map a (i1 Λ' φ p x) := compatibleOneFormClass_restriction_natural Λ' ((pairFst φ).map a) x

theorem pairFirstOpenOneForms_kaehler_differential (p : (Pair φ)ᵒᵖ) (x : (OPair φ D'.s).obj p) :
    i1 Λ' φ p (KaehlerDifferential.D D'.R _ x) = (Kp Λ' φ).d0 p (i0 Λ' φ p x) := compatibleOneFormClass_kaehler_differential Λ' _ x

theorem pairFirstOpenTwoForms_exterior_derivative (p : (Pair φ)ᵒᵖ) (x : Ω[(OPair φ D'.s).obj p⁄D'.R]) :
    i2 Λ' φ p (dOne D'.R _ x) = (Kp Λ' φ).d1 p (i1 Λ' φ p x) := compatibleTwoFormClass_exterior_derivative Λ' _ x

def Cor (k : (Kp Λ' φ).T2) (w : Tot2 (OPair φ D'.s)) : Prop :=
  (∀ p q r a b, i0 Λ' φ r (w.1 p q r a b) = k.1 p q r a b) ∧ (∀ p q a, i1 Λ' φ q (w.2.1 p q a) = k.2.1 p q a) ∧
    ∀ p, i2 Λ' φ p (w.2.2 p) = k.2.2 p

theorem Cor.sub {k k' : (Kp Λ' φ).T2} {w w' : Tot2 (OPair φ D'.s)} (h : Cor Λ' k w) (h' : Cor Λ' k' w') :
    Cor Λ' (k - k') (w - w') := by
  unfold Cor at h h' ⊢
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · simp only [Prod.fst_sub, Pi.sub_apply, map_sub, h1, h1']
  · simp only [Prod.snd_sub, Prod.fst_sub, Pi.sub_apply, map_sub, h2, h2']
  · simp only [Prod.snd_sub, Pi.sub_apply, map_sub, h3, h3']

theorem deRhamCochainCorrespondence_degree_one_coboundary {g : (Kp Λ' φ).T1} {c : Tot1 (OPair φ D'.s)} (hf : ∀ p q a, i0 Λ' φ q (c.1 p q a) = g.1 p q a)
    (hω : ∀ p, i1 Λ' φ p (c.2 p) = g.2 p) : Cor Λ' ((Kp Λ' φ).D1 g) (dTot1 _ c) := by
  unfold Cor
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · rw [cechDeRhamTotalDifferentialOne_functionPart, map_add, map_sub, pairFirstOpenFunctionSections_natural, hf, hf, hf]
    all_goals rfl
  · rw [dTot1_a, map_sub, map_sub, hω, pairFirstOpenOneForms_natural, hω, pairFirstOpenOneForms_kaehler_differential, hf]
    all_goals rfl
  · rw [dTot1_η, pairFirstOpenTwoForms_exterior_derivative, hω]
    all_goals rfl

theorem Cor.unique {k : (Kp Λ' φ).T2} {w w' : Tot2 (OPair φ D'.s)} (h : Cor Λ' k w) (h' : Cor Λ' k w') : w = w' := by
  unfold Cor at h h'
  have e0 : ∀ p, Function.Injective (i0 Λ' φ p) := fun p ↦ (Λ'.e _).injective
  have e1 : ∀ p, Function.Injective (i1 Λ' φ p) := fun p ↦ (GlobalTheory.T.liftForms_bijective_degree_one_two D' Λ' _).1.1
  have e2 : ∀ p, Function.Injective (i2 Λ' φ p) := fun p ↦ (GlobalTheory.T.liftForms_bijective_degree_one_two D' Λ' _).2.1
  exact Tot2.ext (fun p q r a b ↦ e0 r ((h.1 p q r a b).trans (h'.1 p q r a b).symm))
    (fun p q a ↦ e1 q ((h.2.1 p q a).trans (h'.2.1 p q a).symm))
    (fun p ↦ e2 p ((h.2.2 p).trans (h'.2.2 p).symm))

theorem cor_res {k' : (KK D'.κ D'.t).T2} {w' : Tot2 (OAff D'.s)}
    (hw' : Λ'.Res2 (((KK D'.κ D'.t).resMap Λ'.L).p2 k') w') :
    Cor Λ' (((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k') (pullTot2 (pairRes φ D'.s) w') := by
  unfold Cor
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · rw [cechDeRhamPullbackTotalDegreeTwo_function_part]
    exact (hw'.1 _ _ _ _ _).symm
  · rw [pullTot2_a]
    exact (congrArg (i1 Λ' φ q) (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff D'.s) (pairFst φ) q _)).trans (hw'.2.1 _ _ _).symm
  · rw [pullTot2_η]
    exact (congrArg (i2 Λ' φ p) (qOm_restrict (OAff D'.s) (pairFst φ) p _)).trans (hw'.2.2 _).symm

theorem cor_pull (Λ : Lift D) {σ : D.R →+* D'.R} {φ₀ : D'.X₀ ⟶ D.X₀}
    (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
    (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
      Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))
    {k : (KK D.κ D.t).T2} {w : Tot2 (OAff D.s)} (hw : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k) w) :
    Cor Λ' (((pairB Λ' φ m).pre θ).p2 k) (pullTot2 (pairPull hφ) w) := by
  unfold Cor
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · rw [cechDeRhamPullbackTotalDegreeTwo_function_part]
    refine (hθ r _).symm.trans ?_
    exact congrArg (fun y ↦ (θ.app r).φ y) (hw.1 _ _ _ _ _).symm
  · rw [pullTot2_a]
    refine (movedDatum_compatibleOneFormClass (Λ := Λ) (Λ' := Λ') (hφ := hφ) (m := m) (θ := θ) (hθ := hθ) q _).symm.trans ?_
    exact congrArg _ (hw.2.1 _ _ _).symm
  · rw [pullTot2_η]
    refine (movedDatum_compatibleTwoFormClass (Λ := Λ) (Λ' := Λ') (hφ := hφ) (m := m) (θ := θ) (hθ := hθ) p _).symm.trans ?_
    exact congrArg _ (hw.2.2 _).symm

theorem exists_deRhamCochainCorrespondence_degree_one (g : (Kp Λ' φ).T1) : ∃ c : Tot1 (OPair φ D'.s), Cor Λ' ((Kp Λ' φ).D1 g) (dTot1 _ c) := by
  obtain ⟨c1, hc1⟩ : ∃ c1 : ∀ (p q : (Pair φ)ᵒᵖ) (_ : p ⟶ q), (OPair φ D'.s).obj q,
      ∀ p q a, i0 Λ' φ q (c1 p q a) = g.1 p q a :=
    ⟨fun p q a ↦ (Λ'.e _).symm (g.1 p q a), fun p q a ↦ (Λ'.e _).apply_symm_apply _⟩
  choose c2 hc2 using fun p ↦ (GlobalTheory.T.liftForms_bijective_degree_one_two D' Λ' ((pairFst φ).obj p)).1.2 (g.2 p)
  exact ⟨(c1, c2), deRhamCochainCorrespondence_degree_one_coboundary Λ' (c := (c1, c2)) hc1 hc2⟩

set_option maxHeartbeats 1000000 in
private theorem isPull2_aux_lemma (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X)
    (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀)
    (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
    (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
      Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))
    (k : (KK D.κ D.t).Z2) (k' : (KK D'.κ D'.t).Z2) (w : cechDeRhamTotalCocyclesTwo (OAff D.s)) (w' : cechDeRhamTotalCocyclesTwo (OAff D'.s))
    (hw : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1) w.1)
    (hw' : Λ'.Res2 (((KK D'.κ D'.t).resMap Λ'.L).p2 k'.1) w'.1)
    (g : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).T1)
    (hg : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D1 g = ((pairB Λ' φ m).pre θ).p2 k.1 -
      ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k'.1) :
    IsPull2 hφ (Hyp2.mk _ w) (Hyp2.mk _ w') := by
  have h1 := cor_pull Λ' Λ hφ m θ hθ hw
  have h2 := cor_res Λ' (φ := φ) hw'
  obtain ⟨c, hc⟩ := exists_deRhamCochainCorrespondence_degree_one Λ' g
  rw [hg] at hc
  have h3 := Cor.unique Λ' hc (Cor.sub Λ' h1 h2)
  unfold IsPull2
  rw [pullHyp2_mk, pullHyp2_mk, Hyp2.mk_eq_mk]
  refine ⟨c, ?_⟩
  rw [coe_pullZZ2, coe_pullZZ2]
  exact h3

end Pairs

theorem isPull2_of_coboundary (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X)
    (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀)
    (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
    (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
      Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))
    (k : (KK D.κ D.t).Z2) (k' : (KK D'.κ D'.t).Z2) (w : cechDeRhamTotalCocyclesTwo (OAff D.s)) (w' : cechDeRhamTotalCocyclesTwo (OAff D'.s))
    (hw : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1) w.1)
    (hw' : Λ'.Res2 (((KK D'.κ D'.t).resMap Λ'.L).p2 k'.1) w'.1)
    (g : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).T1)
    (hg : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D1 g = ((pairB Λ' φ m).pre θ).p2 k.1 -
      ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k'.1) :
    IsPull2 hφ (Hyp2.mk _ w) (Hyp2.mk _ w') := isPull2_aux_lemma D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' g hg

end GlobalTheory.PDForm.PullTwo
