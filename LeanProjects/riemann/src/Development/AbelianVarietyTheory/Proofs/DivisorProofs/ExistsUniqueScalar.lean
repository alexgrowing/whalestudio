import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.ThetaOne

open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

variable {V₁ : Type} [CommRing V₁] [IsDomain V₁]

abbrev toF (F : Type) [Field F] [Algebra (FractionRing V₁) F] : V₁ →+* F :=
  (algebraMap (FractionRing V₁) F).comp (algebraMap V₁ (FractionRing V₁))

theorem tF_hom (F : Type) [Field F] [Algebra (FractionRing V₁) F] :
    jFK (R := V₁) F ≫ jK V₁ = Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)) := by
  rw [jFK, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem prB_hom' (D : DegPre V₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F] :
    (DegPre.prB D F).left ≫ D.P.A.hom = famBase D F ≫ Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)) := by
  rw [← tF_hom]
  exact (Over.w (DegPre.prB D F)).trans (Over.w (fst (TF (R := V₁) F) D.P.A)).symm

def termF (D : DegPre V₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F] (k : ℕ) (α : D.X) :
    SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k)) →ₛₗ[toF (V₁ := V₁) F] FamTerm D F k α :=
  pullOver D.P.L _ (prB_hom' D F) (famφ_prB D F α)

def pullTo (D : DegPre V₁) {R' : Type} [CommRing R'] (f : V₁ →+* R') :
    SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)) →ₛₗ[f]
      SecOver (fst (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left
        (LB.LinComb D.P.L (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ D.famφB 0 i)
          (DegPre.famε 1)) :=
  pullOver D.P.L _ ((Over.w (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A)).trans
    (Over.w (fst (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A)).symm) (fun _ => rfl)

theorem isPullSecLC_pullTo (D : DegPre V₁) {R' : Type} [CommRing R'] (f : V₁ →+* R')
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) :
    IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left
      θ (pullTo D f θ) := fun _ => rfl

abbrev OneBasisAt (D : DegPre V₁) {R' : Type} [CommRing R'] (f : V₁ →+* R')
    (θ' : LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ D.famφB 0 i)
      (DegPre.famε 1))) : Prop :=
  IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.P.A) _ (fun _ : Fin 1 => θ')

theorem exists_theta [IsLocalRing V₁] (hV : IsCN V₁) (D : DegPre V₁) :
    ∃ θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)),
      ∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
        IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
        OneBasisAt D f θ' := by
  haveI : IsNoetherianRing V₁ := hV.1
  obtain ⟨m, b, hm, hb⟩ := GlobalTheory.twistBaseChange V₁ D 1 le_rfl 0
  obtain rfl : m = 1 := hm.trans (one_pow _)
  refine ⟨b 0, fun R' _ f θ' h => ?_⟩
  exact hb R' f (fun _ => θ') (fun i => by rw [Subsingleton.elim i 0]; exact h)

theorem exists_ne_zero (D : DegPre V₁) {K : Type} [Field K] (f : V₁ →+* K) θ' (h : OneBasisAt D f θ') :
    ∃ j, θ'.f j ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨r, -, hu⟩ := h θ'
  have h1 := hu (fun _ => 1) (fun j => by rw [Fin.sum_univ_one, map_one, map_one, _root_.one_mul])
  have h0 := hu (fun _ => 0) (fun j => by rw [Fin.sum_univ_one, map_zero, map_zero, MulZeroClass.zero_mul, hc j])
  have e10 := congrFun (h1.trans h0.symm) 0
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv e10
  simp at this

theorem basis_BF (D : DegPre V₁) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (hθ : ∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      OneBasisAt D f θ')
    (F : Type) [Field F] [Algebra (FractionRing V₁) F] :
    IsSecBasis (T := TF (R := V₁) F) (A := D.P.A) _
      (fun _ : Fin 1 => (termF D F 1 0 θ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F 0) (DegPre.famε 1)))) := by
  have gen : ∀ (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of V₁)), t = Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)) →
      ∀ (hp : (snd (Over.mk t) D.P.A).left ≫ D.P.A.hom =
          (fst (Over.mk t) D.P.A).left ≫ Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)))
        (φ : Fin 4 → ((Over.mk t ⊗ D.P.A).left ⟶ D.P.A.left))
        (hφ : ∀ i, φ i = (snd (Over.mk t) D.P.A).left ≫ D.famφB 0 i),
      IsSecBasis (T := Over.mk t) (A := D.P.A) _
        (fun _ : Fin 1 => (pullOver D.P.L (DegPre.famε 1) hp hφ θ : LB.Sec (LB.LinComb D.P.L φ (DegPre.famε 1)))) := by
    rintro t rfl hp φ hφ
    obtain rfl : φ = fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)))) D.P.A).left ≫ D.famφB 0 i :=
      funext hφ
    exact hθ F (toF F) _ (isPullSecLC_pullTo D _ θ)
  exact gen _ (tF_hom F) (prB_hom' D F) _ (famφ_prB D F 0)

theorem existsUnique_scalar (D : DegPre V₁) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (hθ : ∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      OneBasisAt D f θ')
    (F : Type) [Field F] [Algebra (FractionRing V₁) F] (th : Fam D F 1) :
    ∃! c : F, famProj D F 1 0 th = c • termF D F 1 0 θ := by
  obtain ⟨r, hr, hu⟩ := basis_BF D θ hθ F (th.s 0)
  let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  refine ⟨e (r 0), SecOps.sec_ext fun j => ?_, fun c hc => ?_⟩
  · refine (hr j).trans ?_
    rw [Fin.sum_univ_one]
    show _ = resTop _ ((famBase D F).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (e (r 0)))) * _
    rw [show (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (e (r 0)) = r 0 from e.symm_apply_apply (r 0)]
    rfl
  · have h2 := hu (fun _ => e.symm c) (fun j => by
      rw [Fin.sum_univ_one]
      exact congrArg (fun s : FamTerm D F 1 0 => LB.Sec.f s j) hc)
    have h3 := congrFun h2 0
    rw [← h3]
    exact (e.apply_symm_apply c).symm

theorem fe_from_zero (hG : GlobalFnsSt) (D : DegPre V₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F]
    (th : Fam D F 1) (mu : D.X) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 1 0 mu) (DegPre.deltaε 1)), u.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F 1 mu 0) ∧
      GeneratorPullback.SecRel D.P.L (DegPre.famφ D F (0 + 1 • mu)) (DegPre.famε 1) (th.s (0 + 1 • mu))
        (DegPre.famφ D F 0) (DegPre.famε 1) (th.s 0) (DegPre.trF D F mu).left
        (DegPre.deltaφ D F 1 0 mu) (DegPre.deltaε 1) u := by
  obtain ⟨u, hu, hc⟩ := (gen_fe (D := D) (F := F) hG 1 mu 0).1
  exact ⟨u, hu, hc, th.fe mu 0 u hu hc⟩

theorem eq_of_term_zero (hG : GlobalFnsSt) (D : DegPre V₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F]
    {th th' : Fam D F 1} (h : th.s 0 = th'.s 0) : th = th' := by
  refine fam_ext fun β => ?_
  have key : ∀ x, x = 0 + 1 • β → ∀ j, (th.s x).f j = (th'.s x).f j := by
    rintro x rfl j
    have hL := D.P.isLB
    obtain ⟨u, hu, hc⟩ := (gen_fe (D := D) (F := F) hG 1 β 0).1
    refine sec_ext_val hL (fun y J hJ => ?_) j
    rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (th.fe β 0 u hu hc) _ _ y J hJ,
      (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (th'.fe β 0 u hu hc) _ _ y J hJ, h]
  exact key β (by rw [zero_add, one_smul])

theorem c_zero (D : DegPre V₁) : D.c 0 = (1 : 𝟙_ _ ⟶ D.P.A) := by
  have h := D.c_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem main [IsLocalRing V₁] (hV : IsCN V₁) (D : DegPre V₁) :
    ∃ θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)),
      (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
        IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
        OneBasisAt D f θ') ∧
      (∀ (K : Type) [Field K] (f : V₁ →+* K), ∃ j, (pullTo D f θ).f j ≠ 0) ∧
      (∀ (F : Type) [Field F] [Algebra (FractionRing V₁) F] (th : Fam D F 1),
        ∃! c : F, famProj D F 1 0 th = c • termF D F 1 0 θ) ∧
      (∀ (F : Type) [Field F] [Algebra (FractionRing V₁) F] (th : Fam D F 1) (mu : D.X),
        ∃ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 1 0 mu) (DegPre.deltaε 1)), u.IsGen ∧
          LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F 1 mu 0) ∧
          GeneratorPullback.SecRel D.P.L (DegPre.famφ D F (0 + 1 • mu)) (DegPre.famε 1) (th.s (0 + 1 • mu))
            (DegPre.famφ D F 0) (DegPre.famε 1) (th.s 0) (DegPre.trF D F mu).left
            (DegPre.deltaφ D F 1 0 mu) (DegPre.deltaε 1) u) ∧
      (∀ (F : Type) [Field F] [Algebra (FractionRing V₁) F] (th th' : Fam D F 1), th.s 0 = th'.s 0 → th = th') := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨θ, hθ⟩ := exists_theta hV D
  exact ⟨θ, hθ, fun K _ f => exists_ne_zero D f _ (hθ K f _ (isPullSecLC_pullTo D f θ)),
    fun F _ _ th => existsUnique_scalar D θ hθ F th, fun F _ _ th mu => fe_from_zero hG D F th mu,
    fun F _ _ _ _ h => eq_of_term_zero hG D F h⟩

end GlobalTheory.Poinc.ThetaOne
