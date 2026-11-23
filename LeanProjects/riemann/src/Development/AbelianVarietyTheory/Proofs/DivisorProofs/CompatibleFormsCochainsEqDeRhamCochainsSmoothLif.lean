import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowerCompatRelFiltrationTwoSidedRelEqBotOfBasStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.LiftRes

variable {D : Data} (Λ : Lift D)

theorem rel_bot (U : AffOp D.X) : rel D.R (Λ.L.obj U).δ = ⊥ :=
  (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base).2 D.R (Λ.L.obj U).B (Λ.L.obj U).J (Λ.L.obj U).δ D.I D.κ (Λ.L.obj U).dp (Λ.gen U).le

theorem smoothLift_compatibleOneForms_mk_injective (U : AffOp D.X) :
    Function.Injective (Submodule.Quotient.mk : Ω[(Λ.L.obj U).B⁄D.R] → K1 D.R (Λ.L.obj U).δ) := by
  intro x y h
  rw [Submodule.Quotient.eq] at h
  have h' : ι1 (x - y) ∈ rel D.R (Λ.L.obj U).δ := h
  rw [rel_bot, Ideal.mem_bot, map_sub, sub_eq_zero] at h'
  exact ExteriorAlgebra.ι_inj _ _ _ |>.1 h'

theorem mk_inj (U : AffOp D.X) (j : ℕ) :
    Function.Injective (Submodule.Quotient.mk : Om D.R (Λ.L.obj U).B j → K D.R (Λ.L.obj U).δ j) := by
  intro x y h
  rw [Submodule.Quotient.eq] at h
  have h' : ((x - y : Om D.R (Λ.L.obj U).B j) : DR D.R (Λ.L.obj U).B) ∈ rel D.R (Λ.L.obj U).δ := h
  rw [rel_bot, Ideal.mem_bot] at h'
  exact sub_eq_zero.1 (Subtype.ext h')

theorem semiInv (U : AffOp D.X) :
    SemiHom (RingHom.id D.R) ((Λ.e U).symm : (Λ.L.obj U).B →+* Sec D.s U.unop.1) :=
  fun r b ↦ map_smul (Λ.e U).symm r b

theorem smoothLift_oneFormsComparison_left_inv (U : AffOp D.X) (ω : Ω[Sec D.s U.unop.1⁄D.R]) : (semiInv Λ U).m1 ((Λ.semi U).m1 ω) = ω :=
  (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) (semiInv Λ U) (SemiHom.of_algHom (AlgHom.id D.R _))
    (fun b ↦ (Λ.e U).symm_apply_apply b) ω).trans (SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) ω)

theorem smoothLift_oneFormsComparison_right_inv (U : AffOp D.X) (ω : Ω[(Λ.L.obj U).B⁄D.R]) : (Λ.semi U).m1 ((semiInv Λ U).m1 ω) = ω :=
  (SemiHom.oneFormMap_comp_oneFormMap (semiInv Λ U) (Λ.semi U) (SemiHom.of_algHom (AlgHom.id D.R _))
    (fun b ↦ (Λ.e U).apply_symm_apply b) ω).trans (SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) ω)

theorem mOm_left (U : AffOp D.X) (j : ℕ) (x : Om D.R (Sec D.s U.unop.1) j) :
    (semiInv Λ U).mOm j ((Λ.semi U).mOm j x) = x :=
  (SemiHom.mOm_mOm (Λ.semi U) (semiInv Λ U) (SemiHom.of_algHom (AlgHom.id D.R _))
    (fun b ↦ (Λ.e U).symm_apply_apply b) x).trans (SemiHom.mOm_id _ (fun _ ↦ rfl) x)

theorem mOm_right (U : AffOp D.X) (j : ℕ) (x : Om D.R (Λ.L.obj U).B j) :
    (Λ.semi U).mOm j ((semiInv Λ U).mOm j x) = x :=
  (SemiHom.mOm_mOm (semiInv Λ U) (Λ.semi U) (SemiHom.of_algHom (AlgHom.id D.R _))
    (fun b ↦ (Λ.e U).apply_symm_apply b) x).trans (SemiHom.mOm_id _ (fun _ ↦ rfl) x)

def f1 (U : AffOp D.X) : Ω[Sec D.s U.unop.1⁄D.R] →+ K1 D.R (Λ.L.obj U).δ :=
  (N1 D.R (Λ.L.obj U).δ).mkQ.toAddMonoidHom.comp (Λ.semi U).m1.toAddMonoidHom

def fm (U : AffOp D.X) (j : ℕ) : Om D.R (Sec D.s U.unop.1) j →+ K D.R (Λ.L.obj U).δ j :=
  (N D.R (Λ.L.obj U).δ j).mkQ.toAddMonoidHom.comp ((Λ.semi U).mOm j).toAddMonoidHom

theorem liftOneFormsToCompatible_apply (U : AffOp D.X) (ω : Ω[Sec D.s U.unop.1⁄D.R]) :
    f1 Λ U ω = Submodule.Quotient.mk ((Λ.semi U).m1 ω) := rfl

theorem fm_apply (U : AffOp D.X) (j : ℕ) (x : Om D.R (Sec D.s U.unop.1) j) :
    fm Λ U j x = Submodule.Quotient.mk ((Λ.semi U).mOm j x) := rfl

theorem liftOneFormsToCompatible_bijective (U : AffOp D.X) : Function.Bijective (f1 Λ U) := by
  refine ⟨fun x y h ↦ ?_, fun z ↦ ?_⟩
  · rw [liftOneFormsToCompatible_apply, liftOneFormsToCompatible_apply] at h
    have := congrArg (semiInv Λ U).m1 (smoothLift_compatibleOneForms_mk_injective Λ U h)
    rwa [smoothLift_oneFormsComparison_left_inv, smoothLift_oneFormsComparison_left_inv] at this
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨(semiInv Λ U).m1 z, congrArg _ (smoothLift_oneFormsComparison_right_inv Λ U z)⟩

theorem fm_bij (U : AffOp D.X) (j : ℕ) : Function.Bijective (fm Λ U j) := by
  refine ⟨fun x y h ↦ ?_, fun z ↦ ?_⟩
  · rw [fm_apply, fm_apply] at h
    have := congrArg ((semiInv Λ U).mOm j) (mk_inj Λ U j h)
    rwa [mOm_left, mOm_left] at this
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨(semiInv Λ U).mOm j z, congrArg _ (mOm_right Λ U j z)⟩

abbrev KL : Cx (AffOp D.X) := (KK D.κ D.t).res Λ.L

theorem map0 {U V : AffOp D.X} (a : U ⟶ V) (b : Sec D.s U.unop.1) :
    (KL Λ).M0.map a (Λ.e U b) = Λ.e V (mp (OAff D.s) a b) := (Λ.nat a b).symm

theorem map1 {U V : AffOp D.X} (a : U ⟶ V) (ω : Ω[Sec D.s U.unop.1⁄D.R]) :
    (KL Λ).M1.map a (f1 Λ U ω) = f1 Λ V (p1 (OAff D.s) a ω) := by
  rw [liftOneFormsToCompatible_apply, liftOneFormsToCompatible_apply]
  change km1 (SemiHom.of_algHom (Λ.L.map a).φ) (Λ.L.map a).dp (Submodule.Quotient.mk _) = Submodule.Quotient.mk _
  rw [divPowerCompatOneFormMap_mk, p1, SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) (SemiHom.of_algHom (Λ.L.map a).φ)
      ((Λ.semi U).comp (SemiHom.of_algHom (Λ.L.map a).φ)) (fun _ ↦ rfl),
    SemiHom.oneFormMap_comp_oneFormMap (semiHom_mp _ a) (Λ.semi V) ((Λ.semi U).comp (SemiHom.of_algHom (Λ.L.map a).φ))
      (fun b ↦ Λ.nat a b)]

theorem map2 {U V : AffOp D.X} (a : U ⟶ V) (x : Om D.R (Sec D.s U.unop.1) 2) :
    (KL Λ).M2.map a (fm Λ U 2 x) = fm Λ V 2 (pOm (OAff D.s) 2 a x) := by
  rw [fm_apply, fm_apply]
  change km (SemiHom.of_algHom (Λ.L.map a).φ) (Λ.L.map a).dp 2 (Submodule.Quotient.mk _) = Submodule.Quotient.mk _
  rw [km_mk, pOm, SemiHom.mOm_mOm (Λ.semi U) (SemiHom.of_algHom (Λ.L.map a).φ)
      ((Λ.semi U).comp (SemiHom.of_algHom (Λ.L.map a).φ)) (fun _ ↦ rfl),
    SemiHom.mOm_mOm (semiHom_mp _ a) (Λ.semi V) ((Λ.semi U).comp (SemiHom.of_algHom (Λ.L.map a).φ))
      (fun b ↦ Λ.nat a b)]

theorem d0e (U : AffOp D.X) (b : Sec D.s U.unop.1) : (KL Λ).d0 U (Λ.e U b) = f1 Λ U (KaehlerDifferential.D D.R _ b) := by
  rw [liftOneFormsToCompatible_apply, SemiHom.m1_D]; rfl

theorem d1e (U : AffOp D.X) (ω : Ω[Sec D.s U.unop.1⁄D.R]) :
    (KL Λ).d1 U (f1 Λ U ω) = fm Λ U 2 (dOne _ _ ω) := by
  rw [liftOneFormsToCompatible_apply, fm_apply, SemiHom.mOm_dOne]; rfl

theorem d2e (U : AffOp D.X) (x : Om D.R (Sec D.s U.unop.1) 2) :
    (KL Λ).d2 U (fm Λ U 2 x) = fm Λ U 3 (dTwo _ _ x) := by
  rw [fm_apply, fm_apply, SemiHom.mOm_dTwo]; rfl

end GlobalTheory.PDForm.LiftRes

namespace GlobalTheory.PDForm.LiftRes

variable {D : Data} (Λ : Lift D)

theorem smoothLift_degreeOneRes_component_eq {k : (KL Λ).T1} {w : Tot1 (OAff D.s)} (h : Λ.Res1 k w) (U : AffOp D.X) :
    k.2 U = f1 Λ U (w.2 U) := h.2 U

theorem smoothLift_degreeTwoRes_oneForm_component_eq {k : (KL Λ).T2} {w : Tot2 (OAff D.s)} (h : Λ.Res2 k w) (U V : AffOp D.X) (a : U ⟶ V) :
    k.2.1 U V a = f1 Λ V (w.2.1 U V a) := h.2.1 U V a

theorem smoothLift_degreeTwoRes_twoForm_component_eq {k : (KL Λ).T2} {w : Tot2 (OAff D.s)} (h : Λ.Res2 k w) (U : AffOp D.X) :
    k.2.2 U = fm Λ U 2 (w.2.2 U) := h.2.2 U

theorem smoothLift_degreeOneRes_of_deRhamCochain (w : Tot1 (OAff D.s)) :
    Λ.Res1 ((fun U V a ↦ Λ.e V (w.1 U V a), fun U ↦ f1 Λ U (w.2 U)) : (KL Λ).T1) w :=
  ⟨fun _ _ _ ↦ rfl, fun _ ↦ rfl⟩

theorem smoothLift_exists_degreeOneRes (k : (KL Λ).T1) : ∃ w, Λ.Res1 k w :=
  ⟨(fun U V a ↦ (Λ.e V).symm (k.1 U V a), fun U ↦ Function.surjInv (liftOneFormsToCompatible_bijective Λ U).2 (k.2 U)),
    fun U V a ↦ ((Λ.e V).apply_symm_apply _).symm, fun U ↦ (Function.surjInv_eq (liftOneFormsToCompatible_bijective Λ U).2 (k.2 U)).symm⟩

theorem smoothLift_degreeOneRes_left_unique {k k' : (KL Λ).T1} {w : Tot1 (OAff D.s)} (h : Λ.Res1 k w) (h' : Λ.Res1 k' w) : k = k' :=
  Prod.ext (by funext U V a; exact (h.1 U V a).trans (h'.1 U V a).symm)
    (funext fun U ↦ (h.2 U).trans (h'.2 U).symm)

theorem smoothLift_degreeOneRes_right_unique {k : (KL Λ).T1} {w w' : Tot1 (OAff D.s)} (h : Λ.Res1 k w) (h' : Λ.Res1 k w') : w = w' :=
  Tot1.ext (fun U V a ↦ (Λ.e V).injective ((h.1 U V a).symm.trans (h'.1 U V a)))
    (fun U ↦ (liftOneFormsToCompatible_bijective Λ U).1 ((smoothLift_degreeOneRes_component_eq Λ h U).symm.trans (smoothLift_degreeOneRes_component_eq Λ h' U)))

theorem smoothLift_degreeTwoRes_of_deRhamCochain (w : Tot2 (OAff D.s)) :
    Λ.Res2 ((fun U V W a b ↦ Λ.e W (w.1 U V W a b), fun U V a ↦ f1 Λ V (w.2.1 U V a),
      fun U ↦ fm Λ U 2 (w.2.2 U)) : (KL Λ).T2) w :=
  ⟨fun _ _ _ _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ ↦ rfl⟩

theorem smoothLift_exists_degreeTwoRes (k : (KL Λ).T2) : ∃ w, Λ.Res2 k w :=
  ⟨(fun U V W a b ↦ (Λ.e W).symm (k.1 U V W a b),
      fun U V a ↦ Function.surjInv (liftOneFormsToCompatible_bijective Λ V).2 (k.2.1 U V a),
      fun U ↦ Function.surjInv (fm_bij Λ U 2).2 (k.2.2 U)),
    fun U V W a b ↦ ((Λ.e W).apply_symm_apply _).symm,
    fun U V a ↦ (Function.surjInv_eq (liftOneFormsToCompatible_bijective Λ V).2 (k.2.1 U V a)).symm,
    fun U ↦ (Function.surjInv_eq (fm_bij Λ U 2).2 (k.2.2 U)).symm⟩

theorem smoothLift_degreeTwoRes_left_unique {k k' : (KL Λ).T2} {w : Tot2 (OAff D.s)} (h : Λ.Res2 k w) (h' : Λ.Res2 k' w) : k = k' :=
  Prod.ext (by funext U V W a b; exact (h.1 U V W a b).trans (h'.1 U V W a b).symm)
    (Prod.ext (by funext U V a; exact (h.2.1 U V a).trans (h'.2.1 U V a).symm)
      (funext fun U ↦ (h.2.2 U).trans (h'.2.2 U).symm))

theorem smoothLift_degreeTwoRes_right_unique {k : (KL Λ).T2} {w w' : Tot2 (OAff D.s)} (h : Λ.Res2 k w) (h' : Λ.Res2 k w') : w = w' :=
  Tot2.ext (fun U V W a b ↦ (Λ.e W).injective ((h.1 U V W a b).symm.trans (h'.1 U V W a b)))
    (fun U V a ↦ (liftOneFormsToCompatible_bijective Λ V).1 ((smoothLift_degreeTwoRes_oneForm_component_eq Λ h U V a).symm.trans (smoothLift_degreeTwoRes_oneForm_component_eq Λ h' U V a)))
    (fun U ↦ (fm_bij Λ U 2).1 ((smoothLift_degreeTwoRes_twoForm_component_eq Λ h U).symm.trans (smoothLift_degreeTwoRes_twoForm_component_eq Λ h' U)))

theorem smoothLift_degreeTwoRes_zero : Λ.Res2 0 0 :=
  ⟨fun _ _ W _ _ ↦ (map_zero (Λ.e W)).symm, fun _ V _ ↦ (map_zero (f1 Λ V)).symm,
    fun U ↦ (map_zero (fm Λ U 2)).symm⟩

theorem smoothLift_degreeOneRes_totalDifferentialZero (g : Tot0 (OAff D.s)) : Λ.Res1 ((KL Λ).D0 fun U ↦ Λ.e U (g U)) (dTot0 _ g) := by
  refine ⟨fun U V a ↦ ?_, fun U ↦ ?_⟩
  · change Λ.e V (g V) - (KL Λ).M0.map a (Λ.e U (g U)) = Λ.e V (g V - mp (OAff D.s) a (g U))
    rw [map0, map_sub]
  · exact d0e Λ U (g U)

theorem smoothLift_degreeTwoRes_totalDifferentialOne {k : (KL Λ).T1} {w : Tot1 (OAff D.s)} (h : Λ.Res1 k w) :
    Λ.Res2 ((KL Λ).D1 k) (dTot1 _ w) := by
  refine ⟨fun U V W a b ↦ ?_, fun U V a ↦ ?_, fun U ↦ ?_⟩
  · change (KL Λ).M0.map b (k.1 U V a) - k.1 U W (a ≫ b) + k.1 V W b =
      Λ.e W (mp (OAff D.s) b (w.1 U V a) - w.1 U W (a ≫ b) + w.1 V W b)
    rw [h.1, h.1, h.1, map0, map_add, map_sub]
  · change k.2 V - (KL Λ).M1.map a (k.2 U) - (KL Λ).d0 V (k.1 U V a) =
      f1 Λ V (w.2 V - p1 (OAff D.s) a (w.2 U) - KaehlerDifferential.D D.R _ (w.1 U V a))
    rw [smoothLift_degreeOneRes_component_eq Λ h, smoothLift_degreeOneRes_component_eq Λ h, h.1, map1, d0e, map_sub, map_sub]
  · change (KL Λ).d1 U (k.2 U) = fm Λ U 2 (dOne _ _ (w.2 U))
    rw [smoothLift_degreeOneRes_component_eq Λ h, d1e]

end GlobalTheory.PDForm.LiftRes

namespace GlobalTheory.PDForm.LiftRes

variable {D : Data} (Λ : Lift D)

theorem part1 : (∀ k, ∃! w, Λ.Res1 k w) ∧ (∀ w, ∃! k, Λ.Res1 k w) ∧ ∀ k w, Λ.Res1 k w →
    (k ∈ ((KK D.κ D.t).res Λ.L).Z1 ↔ w ∈ cechDeRhamTotalCocyclesOne (OAff D.s)) ∧
      ((∃ g, ((KK D.κ D.t).res Λ.L).D0 g = k) ↔ ∃ g, dTot0 (OAff D.s) g = w) := by
  refine ⟨fun k ↦ ?_, fun w ↦ ⟨_, smoothLift_degreeOneRes_of_deRhamCochain Λ w, fun k hk ↦ smoothLift_degreeOneRes_left_unique Λ hk (smoothLift_degreeOneRes_of_deRhamCochain Λ w)⟩, fun k w h ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨w, hw⟩ := smoothLift_exists_degreeOneRes Λ k
    exact ⟨w, hw, fun w' hw' ↦ smoothLift_degreeOneRes_right_unique Λ hw' hw⟩
  · show (KL Λ).D1 k = 0 ↔ dTot1 (OAff D.s) w = 0
    have h2 := smoothLift_degreeTwoRes_totalDifferentialOne Λ h
    constructor
    · intro e
      rw [e] at h2
      exact smoothLift_degreeTwoRes_right_unique Λ h2 (smoothLift_degreeTwoRes_zero Λ)
    · intro e
      rw [e] at h2
      exact smoothLift_degreeTwoRes_left_unique Λ h2 (smoothLift_degreeTwoRes_zero Λ)
  · constructor
    · rintro ⟨g, rfl⟩
      refine ⟨fun U ↦ (Λ.e U).symm (g U), smoothLift_degreeOneRes_right_unique Λ ?_ h⟩
      have := smoothLift_degreeOneRes_totalDifferentialZero Λ (fun U ↦ (Λ.e U).symm (g U))
      simpa only [AlgEquiv.apply_symm_apply] using this
    · rintro ⟨g, rfl⟩
      exact ⟨_, smoothLift_degreeOneRes_left_unique Λ (smoothLift_degreeOneRes_totalDifferentialZero Λ g) h⟩

theorem part2 : (∀ k, ∃! w, Λ.Res2 k w) ∧ (∀ w, ∃! k, Λ.Res2 k w) ∧ ∀ k w, Λ.Res2 k w →
    (k ∈ ((KK D.κ D.t).res Λ.L).Z2 ↔ w ∈ cechDeRhamTotalCocyclesTwo (OAff D.s)) ∧
      ((∃ g, ((KK D.κ D.t).res Λ.L).D1 g = k) ↔ ∃ g, dTot1 (OAff D.s) g = w) := by
  refine ⟨fun k ↦ ?_, fun w ↦ ⟨_, smoothLift_degreeTwoRes_of_deRhamCochain Λ w, fun k hk ↦ smoothLift_degreeTwoRes_left_unique Λ hk (smoothLift_degreeTwoRes_of_deRhamCochain Λ w)⟩, fun k w h ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨w, hw⟩ := smoothLift_exists_degreeTwoRes Λ k
    exact ⟨w, hw, fun w' hw' ↦ smoothLift_degreeTwoRes_right_unique Λ hw' hw⟩
  · rw [mem_cechDeRhamTotalCocyclesTwo_iff]
    have c1 : ∀ (T T' T'' T''' : AffOp D.X) (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''),
        ((KL Λ).M0.map χ (k.1 T T' T'' φ ψ) + k.1 T T'' T''' (φ ≫ ψ) χ =
          k.1 T T' T''' φ (ψ ≫ χ) + k.1 T' T'' T''' ψ χ) ↔
        (mp (OAff D.s) χ (w.1 T T' T'' φ ψ) + w.1 T T'' T''' (φ ≫ ψ) χ =
          w.1 T T' T''' φ (ψ ≫ χ) + w.1 T' T'' T''' ψ χ) := by
      intro T T' T'' T''' φ ψ χ
      rw [h.1, h.1, h.1, h.1, map0, ← map_add, ← map_add, (Λ.e T''').injective.eq_iff]
    have c2 : ∀ (T T' T'' : AffOp D.X) (φ : T ⟶ T') (ψ : T' ⟶ T''),
        (k.2.1 T T'' (φ ≫ ψ) = (KL Λ).M1.map ψ (k.2.1 T T' φ) + k.2.1 T' T'' ψ + (KL Λ).d0 T'' (k.1 T T' T'' φ ψ)) ↔
        (w.2.1 T T'' (φ ≫ ψ) = p1 (OAff D.s) ψ (w.2.1 T T' φ) + w.2.1 T' T'' ψ +
          KaehlerDifferential.D D.R _ (w.1 T T' T'' φ ψ)) := by
      intro T T' T'' φ ψ
      rw [smoothLift_degreeTwoRes_oneForm_component_eq Λ h, smoothLift_degreeTwoRes_oneForm_component_eq Λ h, smoothLift_degreeTwoRes_oneForm_component_eq Λ h, h.1, map1, d0e, ← map_add, ← map_add,
        (liftOneFormsToCompatible_bijective Λ T'').1.eq_iff]
    have c3 : ∀ (T T' : AffOp D.X) (φ : T ⟶ T'),
        (k.2.2 T' = (KL Λ).M2.map φ (k.2.2 T) + (KL Λ).d1 T' (k.2.1 T T' φ)) ↔
        (w.2.2 T' = pOm (OAff D.s) 2 φ (w.2.2 T) + dOne _ _ (w.2.1 T T' φ)) := by
      intro T T' φ
      rw [smoothLift_degreeTwoRes_twoForm_component_eq Λ h, smoothLift_degreeTwoRes_twoForm_component_eq Λ h, smoothLift_degreeTwoRes_oneForm_component_eq Λ h, map2, d1e, ← map_add, (fm_bij Λ T' 2).1.eq_iff]
    have c4 : ∀ T : AffOp D.X, (KL Λ).d2 T (k.2.2 T) = 0 ↔ dTwo _ _ (w.2.2 T) = 0 := by
      intro T
      rw [smoothLift_degreeTwoRes_twoForm_component_eq Λ h, d2e, ← map_zero (fm Λ T 3), (fm_bij Λ T 3).1.eq_iff]
    exact and_congr (forall_congr' fun T ↦ forall_congr' fun T' ↦ forall_congr' fun T'' ↦
        forall_congr' fun T''' ↦ forall_congr' fun φ ↦ forall_congr' fun ψ ↦ forall_congr' fun χ ↦
          c1 T T' T'' T''' φ ψ χ)
      (and_congr (forall_congr' fun T ↦ forall_congr' fun T' ↦ forall_congr' fun T'' ↦
        forall_congr' fun φ ↦ forall_congr' fun ψ ↦ c2 T T' T'' φ ψ)
      (and_congr (forall_congr' fun T ↦ forall_congr' fun T' ↦ forall_congr' fun φ ↦ c3 T T' φ)
        (forall_congr' c4)))
  · constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨v, hv⟩ := smoothLift_exists_degreeOneRes Λ g
      exact ⟨v, smoothLift_degreeTwoRes_right_unique Λ (smoothLift_degreeTwoRes_totalDifferentialOne Λ hv) h⟩
    · rintro ⟨g, rfl⟩
      exact ⟨_, smoothLift_degreeTwoRes_left_unique Λ (smoothLift_degreeTwoRes_totalDifferentialOne Λ (smoothLift_degreeOneRes_of_deRhamCochain Λ g)) h⟩

end GlobalTheory.PDForm.LiftRes

namespace GlobalTheory.PDForm

theorem lift_res_bij : (∀ (D : Data) (Λ : Lift D), (∀ k, ∃! w, Λ.Res1 k w) ∧ (∀ w, ∃! k, Λ.Res1 k w) ∧ ∀ k w, Λ.Res1 k w → (k ∈ ((KK D.κ D.t).res Λ.L).Z1 ↔ w ∈ cechDeRhamTotalCocyclesOne (OAff D.s)) ∧ ((∃ g, ((KK D.κ D.t).res Λ.L).D0 g = k) ↔ ∃ g, dTot0 (OAff D.s) g = w)) ∧ ∀ (D : Data) (Λ : Lift D), (∀ k, ∃! w, Λ.Res2 k w) ∧ (∀ w, ∃! k, Λ.Res2 k w) ∧ ∀ k w, Λ.Res2 k w → (k ∈ ((KK D.κ D.t).res Λ.L).Z2 ↔ w ∈ cechDeRhamTotalCocyclesTwo (OAff D.s)) ∧ ((∃ g, ((KK D.κ D.t).res Λ.L).D1 g = k) ↔ ∃ g, dTot1 (OAff D.s) g = w) :=
  ⟨fun _ Λ ↦ LiftRes.part1 Λ, fun _ Λ ↦ LiftRes.part2 Λ⟩

end GlobalTheory.PDForm
