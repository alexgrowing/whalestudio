import Formalism.AdmissibleDesigns.YtRepZero

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBa

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf

section Record

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))

theorem nzsd_R' : NoZeroSMulDivisors (D.nd.O i) Dd.R' := by
  first
  | exact inferInstance
  | (haveI : NoZeroSMulDivisors (D.nd.O i) (FractionRing (D.nd.O i)) :=
        NoZeroSMulDivisors.of_algebraMap_injective (IsFractionRing.injective _ _); exact inferInstance)
  | exact ⟨fun {c x} h => by
      by_cases hc : c = 0
      · exact Or.inl hc
      · refine Or.inr (Subtype.ext (funext fun x' => Matrix.ext fun a b => ?_))
        have h1 := congrFun (congrFun (congrFun (congrArg Subtype.val h) x') a) b
        have h2 : algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c ≠ 0 := fun h0 =>
          hc (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)) (h0.trans (map_zero _).symm))
        simp only [SetLike.val_smul, Pi.smul_apply, Matrix.smul_apply,
          ZeroMemClass.coe_zero, Pi.zero_apply, Matrix.zero_apply] at h1
        rw [Algebra.smul_def] at h1
        exact (mul_eq_zero.mp h1).resolve_left h2⟩

theorem heS {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (a : D.nd.O i) :
    algebraMap ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (selfO i hw a) =
      eS i hw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a) := by
  first
  | rfl
  | (have e1 : ∀ y, eS i hw y = Formalism.MainNotions.N.Br.toLLK (D.nbr i w hw) y := fun _ => rfl
     rw [e1, Formalism.MainNotions.N.Br.toLLK, IsFractionRing.lift_algebraMap]
     rfl)

variable {i dc r Dd}

theorem fd_yt {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (hemb : YtEmbW i dc r Dd hw) :
    FiniteDimensional ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (TrV (eS i hw) (MK (O := D.nd.O i) (YtM i Dd))) := by
  obtain ⟨m, xs, φ, hφ, -⟩ := hemb
  first
  | exact FiniteDimensional.of_injective φ hφ
  | exact Module.Finite.of_injective φ hφ

private theorem continuous_of_injective_linearMap_comp {K V W G : Type*} [Field K] [TopologicalSpace K]
    {_a : AddCommMonoid V} {_m : Module K V} [TopologicalSpace V] [ContinuousAdd V] [IsModuleTopology K V]
    {_aw : AddCommMonoid W} {_mw : Module K W} [TopologicalSpace W] [IsModuleTopology K W]
    [TopologicalSpace G] (φ : V →ₗ[K] W) (hφ : Function.Injective φ) (f : G → V)
    (hf : Continuous fun g => φ (f g)) : Continuous f := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  letI : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  haveI : ContinuousSMul K V := by
    first
    | exact inferInstance
    | exact IsModuleTopology.toContinuousSMul K V
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective φ (LinearMap.ker_eq_bot.mpr hφ)
  have hψc : Continuous ψ := IsModuleTopology.continuous_of_linearMap ψ
  have e1 : f = fun g => ψ (φ (f g)) := funext fun g => (LinearMap.congr_fun hψ (f g)).symm
  rw [e1]
  exact hψc.comp hf

theorem cont_yt {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (hemb : YtEmbW i dc r Dd hw) (hc : MsContW i r hw) (v) : Continuous fun g => ytV i dc Dd hw g v := by
  obtain ⟨m, xs, φ, hφ, heq⟩ := hemb
  have hc' : ∀ x, Continuous (MsW i r hw x) := hc
  refine continuous_of_injective_linearMap_comp φ hφ (fun g => ytV i dc Dd hw g v) ?_
  refine Continuous.congr (f := fun g => fun a => (MsW i r hw (xs a) g).mulVec (φ v a)) ?_
    (fun g => (heq g v).symm)
  refine continuous_pi fun a => ?_
  first
  | exact (hc' (xs a)).matrix_mulVec continuous_const
  | fun_prop

def ytY (hfin : Module.Finite (D.nd.O i) Dd.R') {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (hemb : YtEmbW i dc r Dd hw) (hc : MsContW i r hw) :
    YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
      ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) :=
  haveI := hfin
  haveI := nzsd_R' i Dd
  ytG ℚ_[D.nd.l i] (heS i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) (fd_yt hemb) (cont_yt hemb hc)

theorem ytY_ρ (hfin : Module.Finite (D.nd.O i) Dd.R') {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (hemb : YtEmbW i dc r Dd hw) (hc : MsContW i r hw) :
    (ytY hfin hemb hc).ρ = ytV i dc Dd hw := rfl

theorem msW_eq {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    MsW i r hw x = twistM (TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C (TruncatedSeriesCountingIdentities.CoefExt.self i w hw))⁻¹ := by
  ext g a b
  first
  | exact ((TruncatedSeriesCountingIdentities.CoefExt.self i w hw).inc.comp
      ((algebraMap ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1).comp
        (selfO i hw).toRingHom)).map_mul _ _
  | (simp only [MsW, TruncatedSeriesCountingIdentities.locC, TruncatedSeriesCountingIdentities.chi1C, rTwO, twistM, mapM, Formalism.MainNotions.N.Br.loc, Formalism.MainNotions.N.Br.locChi,
      Formalism.MainNotions.N.Br.locM, Formalism.MainNotions.N.Br.locO, Formalism.MainNotions.N.Br.chiG, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_mk, OneHom.coe_mk, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, MonoidHom.inv_apply,
      Units.coe_map_inv, map_mul]
     rfl)

variable (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

set_option maxHeartbeats 800000 in

theorem ytPsi_rec (hfin : Module.Finite (D.nd.O i) Dd.R') {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (hemb : YtEmbW i dc r Dd hw) (hc : MsContW i r hw)
    [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] (c : Fin (D.R.t + 1))
    (Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1)) :
    PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) (ytY hfin hemb hc) Cd := by
  haveI := hfin
  haveI := nzsd_R' i Dd
  first
  | apply ytG_psi
  | (unfold ytY; apply ytG_psi)

theorem jump_pi (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hc : MsContW i r hw) (x : D.nd.X i) (τ) (a : ℤ)
    (hx : IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x)) τ a) :
    IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw π)) τ a := by
  have hFs := hF w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)
  have hMs : ∀ y, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw y)) := fun y => by
    rw [msW_eq]
    exact (hG2 w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).2 y
  have hfd : FiniteDimensional ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
      ↥(DdR (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x))) :=
    fd_of_crys (Br.PD D.loc D.nbr i w hw) hFs (matG (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (MsW i r hw) hc x) (hMs x)
  have hp := mult_pos (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x)) τ a hx
  have heqm := (hG2 w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).1.2.1 τ x π a
  rw [← msW_eq, ← msW_eq] at heqm
  exact jump_of_mult _ _ τ a (by rw [← heqm]; exact hp.ne')

theorem ytTarget_of (hfin : Module.Finite (D.nd.O i) Dd.R') (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hemb : YtEmbW i dc r Dd hw) (hc : MsContW i r hw)
    [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] (c : Fin (D.R.t + 1)) :
    YtTarget i dc r π Dd hw c := by
  intro Cd
  haveI := hfin
  haveI := nzsd_R' i Dd
  have hMs : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x)) := fun x => by
    rw [msW_eq hw x]
    exact (hG2 w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).2 x
  obtain ⟨m, xs, φ, hφ, heq⟩ := id hemb
  have hcrys : IsCrys (Br.PD D.loc D.nbr i w hw) (ytY hfin hemb hc).ρ ∧
      ∀ τ a, IsJumpV (Br.PD D.loc D.nbr i w hw) (ytY hfin hemb hc).ρ τ a →
        ∃ x, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x)) τ a :=
    ytG_crys (hF := hF w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) (Ms := MsW i r hw) (hMc := hc) (hMs := hMs)
      (xs := xs) (φ := φ) (hφ := hφ) (heq := heq) ..
  refine ⟨ytY hfin hemb hc, ?_, ytPsi_rec hfin hemb hc c Cd⟩
  unfold YtCrys
  refine ⟨hcrys.1, fun τ => ?_⟩
  intro a ha
  obtain ⟨x, hx⟩ := hcrys.2 τ a ha
  exact jump_pi (hF := hF) (hG2 := hG2) (hw := hw) (hc := hc) (x := x) (hx := hx)

end Record

end Formalism.MainNotions.N.K.TBa

end
