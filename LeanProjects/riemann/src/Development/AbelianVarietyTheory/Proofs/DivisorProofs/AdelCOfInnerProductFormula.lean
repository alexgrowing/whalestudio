import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.MassNumeric
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow

variable {D : D7}

section Main

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem inner_HW_lowC {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x y : (R.HW i σ).H) :
    inner ℂ x y = ((∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ) : ℝ) : ℂ) *
      ipM (R.MW i σ) (R.νW i) (R.fdW i) ((R.HW i σ).e x) ((R.HW i σ).e y) := by
  rw [(hR.models.HW i σ).2.2, ipAt]
  push_cast
  rfl

theorem exists_frames_lowC {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) :
    ∃ Fr : Frames (Wc D i), IsFrames (Wc D i) Fr ∧ ∃ mR : ∀ ρ, Measure (Upq (Wc D i) ρ), ∀ ρ, Lev.IsMinf (mR ρ) := by
  obtain ⟨⟨Fr, h1⟩, h2⟩ := (hR.models.νW i).1.2.2 R.θ hR.models.inf
  exact ⟨Fr, h1, (h2 Fr h1).1⟩

variable {R} {F : Face D A} {i : Fin D.R.m} {t : T} {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} {P : LevelP R.Pg D.R.r ℂ}
    {cμ cη : (AE D)ˣ →* Circle} {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ)}
    {BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ} {f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ}
    {c : CoefA (Vc D i)} {io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}
    (hd : IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io)
    {ν : Measure (GA D (Vc D i))} {𝓕 : Set (GA D (Vc D i))} (hν : IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕)

include hd in
open Datum in
theorem exists_covol_lowC : ∃ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))),
    IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 := by
  obtain ⟨p, hp⟩ := hd.2.2.2.2.2.2.2.1.1.2.norm.1
  exact ⟨p.1, p.2, hp⟩

include hd hν in

theorem scalar_bound_lowC (h7 : LevelIndexNormC R F) (h8 : MassLower D) (h9 : FormalDegreeUpperC R F) {b : ℝ} (hb : Sizes D i b)
    {μ : @Measure (Datum.WO (Vc D i) (Wc D i)) (Datum.measMx _ _)} {𝓧 : Set (Datum.WO (Vc D i) (Wc D i))}
    (hμ : Datum.IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧) {Fr : Frames (Wc D i)} (hFr : IsFrames (Wc D i) Fr)
    {mR : ∀ ρ, Measure (Upq (Wc D i) ρ)} (hmR : ∀ ρ, Lev.IsMinf (mR ρ)) (v : ∀ ρ, lowT (R.MW i σ) ρ)
    (hv : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) (x : HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ)
    (hx : ∀ w a, ‖x w a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2 - (1 + (D.R.t : ℝ)) / 2))
    (dim : ℝ) (hdim : 1 ≤ dim) (l : ℝ)
    (hl : l = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ)) * dim * (ν 𝓕).toReal *
      (∏ ρ, ((hookOf (pW D i ρ) (aPlAt D i σ ρ) : ℝ) * (hookOf (qW D i ρ) (aMiAt D i σ ρ) : ℝ))) * Datum.nrm2 μ 𝓧 f /
      dOff D (finS R t) * (∏ ρ, ∫ b, ‖⟪((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(mR ρ)) *
      ‖eulerOff D (finS R t) x‖) :
    0 < l ∧ mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l := by
  obtain ⟨a1, a2⟩ := h7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd
  have a3 := a2 μ 𝓧 hμ
  rw [Finset.prod_inv_distrib] at a3
  have hS := dLoc_bound (finS R t)
  have a4 : (levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) ≠ 0 := fun h => by
    rw [h, Nat.cast_zero, zero_mul] at a3
    exact (inv_pos.2 hS.1).ne a3
  have hp := hd.1.models.vpos i
  have a5 := GlobalTheory.VolIndex.vol_eq_index_mul_mass D (Vc D i) _ ν 𝓕 (D.sp.V_sig _) hp a1 a4 (isOpen_level _ _ _) hν
  obtain ⟨s1, s2, s3, s4, s5⟩ := GlobalTheory.AdelicScalar.SizeBounds.sizes D i b hb
  have a6 := fun ρ => h9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd Fr hFr ρ (mR ρ) (hmR ρ) (v ρ) (hv ρ)
  have r1 := D.R.rank_add_five_le
  have r2 := D.R.m_add_three_le_k
  have r3 := D.R.two_le_m
  rw [hl, a5]
  exact UpperTheory.Mu.numeric_bound D.R.f D.R.nV D.R.r D.what₂.card_Tau (Lp D b) (3 * (D.R.r : ℝ) * b) _ dim _ _ _ _ _ _ _ _
    (fun ρ => (degAt D i σ ρ : ℝ)) (by unfold Ranks.nV Ranks.r; omega) (by unfold Ranks.nV Ranks.r; omega)
    (by unfold Ranks.r; omega) (UpperTheory.Mu.one_le_f D.R) s1 s2
    (by positivity) s4 (NumberField.Units.torsionOrder_pos _) (UpperTheory.Mu.host_torsionOrder_le D.host) (h8 i hp) hdim a3 (eulerOff_lower _ x hx) (dOff_bound _) hS
    (fun ρ => mul_pos (Nat.cast_pos.2 (hookOf_pos _ _)) (Nat.cast_pos.2 (hookOf_pos _ _)))
    (fun ρ => by exact_mod_cast one_le_dimK i σ ρ) (fun ρ => (a6 ρ).2.1) (fun ρ => ⟨Nat.cast_nonneg _, s5 σ ρ⟩)
    fun ρ => (a6 ρ).2.2

include hd hν in

theorem term_eval_lowC (h3 : InnerProductFormulaC R F) (h4 : FockCoefficientC R F)
    {μ : @Measure (Datum.WO (Vc D i) (Wc D i)) (Datum.measMx _ _)} {𝓧 : Set (Datum.WO (Vc D i) (Wc D i))}
    (hμ : Datum.IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧) {Fr : Frames (Wc D i)} (hFr : IsFrames (Wc D i) Fr)
    {mR : ∀ ρ, Measure (Upq (Wc D i) ρ)} (hmR : ∀ ρ, Lev.IsMinf (mR ρ)) (v : ∀ ρ, lowT (R.MW i σ) ρ)
    (U₁ U₂ : (R.HW i σ).H) (w : c.W) (hw : ‖w‖ = 1) (z : ℂ)
    (hZ : ∀ v₁ v₂ : (R.MW i σ).Vec, HasSum (fun y : FinCos (Wc D i) (levW R i) =>
        @l2 _ (Datum.measMx _ _) μ 𝓧 (ω (1, y.rep) f) f *
          starRingEnd ℂ (petW R i (rTr (Wc D i) y.rep ((R.HW i σ).e U₁ v₁)) ((R.HW i σ).e U₂ v₂)))
      (z * starRingEnd ℂ (petW R i ((R.HW i σ).e U₁ v₁) ((R.HW i σ).e U₂ v₂)))) :
    l2 ν 𝓕 (upLift R i ω (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e U₁ fun ρ => v ρ))
        (upLift R i ω (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e U₂ fun ρ => v ρ)) =
      ((ν 𝓕).toReal : ℂ) * (Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * z *
        starRingEnd ℂ (ipM (R.MW i σ) (R.νW i) (R.fdW i) ((R.HW i σ).e U₂) ((R.HW i σ).e U₁)) *
        ((∏ ρ, ∫ b, ‖⟪((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
          (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(mR ρ) : ℝ) : ℂ)) := by
  have m1 := HMod_mem (hd.1.models.HW i σ) U₁
  have a1 := (h3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd ν 𝓕 hν μ 𝓧 hμ Fr hFr mR hmR _ m1 _ (HMod_mem (hd.1.models.HW i σ) U₂) v v
    (io (PiTensorProduct.tprod ℂ v) w) (io (PiTensorProduct.tprod ℂ v) w)).2.2.2
  have a2 := h4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd μ 𝓧 hμ
  have e : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
  refine a1.trans (congrArg _ ?_)
  exact @zeta_eval D (Vc D i) (Wc D i) _ _ _ _ (R.HW i σ) _ (inner_HW_lowC R hd.1 i σ) R.θ _ _ U₁ U₂ m1 (fun ρ => v ρ) (levW R i) _
    (Datum.measMx _ _) μ 𝓧 ω _ f Fr (realMat_mem i hFr) mR hmR _ z (fun x hx g hg => e ▸ a2 x hx g hg v v w w) hZ

end Main

section Final

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
  {F : Face D A} {i : Fin D.R.m} {t : T} {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} {P : LevelP R.Pg D.R.r ℂ}
    {cμ cη : (AE D)ˣ →* Circle} {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ)}
    {BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ} {f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ}
    {c : CoefA (Vc D i)} {io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}
    (hd : IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io)
    {ν : Measure (GA D (Vc D i))} {𝓕 : Set (GA D (Vc D i))} (hν : IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕)
    {I : Type} [Fintype I] {y : I → Bridge.Gf (Vc D i)} (HV : HMod (Bridge.Gf (Vc D i) → c.W))
    (hV : HV.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m))
        (chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)))
      (Bridge.adInner (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y))

include hd hν hV in
theorem integrableOn_isLift_lowC (x : HV.H) (v : ∀ ρ, lowT (R.MW i σ) ρ) (g : GA D (Wc D i)) :
    IntegrableOn (fun h => Datum.thetaKO ω h g (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) (c.ext (HV.e x) h)))) 𝓕 ν := by
  have := integrableOn_lift hd.2.2.2.2.2.1 (D.sp.V_sig _) (hd.1.models.vpos i) c hd.2.2.2.2.2.2.2.2.2.1 _ _ (HMod_mem hV x)
      (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v))) (fun w => by rw [ptL_apply]; exact hd.2.2.2.2.2.2.2.2.1 _) hν g
  simp only [ptL_apply] at this
  convert this using 10

include hd hν hV in

theorem exists_isLift_lowC (h1 : LiftIsCuspC R F) : ∃ th, IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th := by
  refine exists_linear_lift ν 𝓕 (R.HW i σ).e (fun (v : ∀ ρ, lowT (R.MW i σ) ρ) (g : GA D (Wc D i)) U => U (fun ρ => v ρ) g)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) HV.e c.ext
    (fun v g h w => Datum.thetaKO ω h g (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) w))) (fun v g h w w' => ?_)
    (fun v g h a w => ?_) (integrableOn_isLift_lowC hd hν HV hV) fun x => ?_
  · rw [← ptL_apply, map_add, Datum.thetaKO, map_add]
    rfl
  · rw [← ptL_apply, map_smul, thetaKO_smul]
    rfl
  · refine (h1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd ν 𝓕 hν _ (HMod_mem hV x)).elim fun U hU => ?_
    refine (HMod_onto (hd.1.models.HW i σ) hU.1).elim fun u hu => ⟨u, fun v g => ?_⟩
    refine (congrFun (congrFun (congrArg DFunLike.coe hu) _) g).trans ((hU.2 v g).trans ?_)
    unfold Lift.thetaPInt
    rfl

include hd hν hV in
set_option maxHeartbeats 800000 in

theorem form_key_lowC (hy : Bridge.IsReps (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y)
    (h2 : SourceLevelLawC R F) (h3 : InnerProductFormulaC R F)
    (th : HV.H →ₗ[ℂ] (R.HW i σ).H) (hth : IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th) (v : ∀ ρ, lowT (R.MW i σ) ρ)
    (hv : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) (U₁ U₂ : (R.HW i σ).H) {κ : Type} [Fintype κ]
    (b : OrthonormalBasis κ ℂ c.W) {μ : @Measure (Datum.WO (Vc D i) (Wc D i)) (Datum.measMx _ _)}
    {𝓧 : Set (Datum.WO (Vc D i) (Wc D i))} (hμ : Datum.IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧) {Fr : Frames (Wc D i)}
    (hFr : IsFrames (Wc D i) Fr) {mR : ∀ ρ, Measure (Upq (Wc D i) ρ)} (hmR : ∀ ρ, Lev.IsMinf (mR ρ)) :
    inner ℂ (LinearMap.adjoint th U₁) (LinearMap.adjoint th U₂) =
      ((∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ) : ℝ) : ℂ) ^ 2 * ∑ k,
        l2 ν 𝓕 (upLift R i ω (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) (b k))) ((R.HW i σ).e U₁ fun ρ => v ρ))
          (upLift R i ω (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) (b k))) ((R.HW i σ).e U₂ fun ρ => v ρ)) := by
  have hc : c.Is := hd.2.2.2.2.2.2.2.2.2.1
  have hio := hd.2.2.2.2.2.2.2.2.2.2
  have hm := HMod_mem (hd.1.models.HW i σ)
  have hR := fun U₁ U₂ Q₁ Q₂ => h3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd ν 𝓕 hν μ 𝓧 hμ Fr hFr mR hmR _ (hm U₁) _ (hm U₂) v v Q₁ Q₂
  have hφ := ptL_apply R i σ BW f (io (PiTensorProduct.tprod ℂ v))
  have a1 : ∀ w, Datum.IsThetaFunO R.ψ (Vc D i) (Wc D i) (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) w) := fun w => by rw [hφ]; exact hd.2.2.2.2.2.2.2.2.1 _
  have a2 : ∀ u ∈ GinfC (Vc D i), ∀ w, ω (u, 1) (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) w) = ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) (c.ρ u w) := fun u hu w => by rw [hφ, hφ]; exact hio.1 u hu _ w
  have a3 : ∀ κ ∈ Lev.levA (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m)), ∀ w,
      ω (κ, 1) (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) w) = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m) κ)⁻¹ • ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) w :=
    fun κ hκ w => by rw [hφ]; exact h2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd κ hκ _
  have a4 : ∀ x g, (R.HW i σ).e (th x) (fun ρ => v ρ) g = ∫ h in 𝓕, Datum.thetaKO ω h g (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) (c.ext (HV.e x) h)) ∂ν :=
    fun x g => by simp only [hφ]; exact (hth x v g).2
  have a5 : ∀ (U : (R.HW i σ).H) w h, IntegrableOn (fun g => Datum.thetaKO ω h g (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) w) *
      starRingEnd ℂ ((R.HW i σ).e U (fun ρ => v ρ) g)) (R.fdW i) (R.νW i) :=
    fun U w h => by rw [hφ]; exact (hR U U (io (PiTensorProduct.tprod ℂ v) w) 0).1 h
  have a6 : ∀ k, IntegrableOn (fun h =>
      l2 (R.νW i) (R.fdW i) (fun g => Datum.thetaKO ω h g (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) (b k))) ((R.HW i σ).e U₁ fun ρ => v ρ) *
      starRingEnd ℂ (l2 (R.νW i) (R.fdW i) (fun g => Datum.thetaKO ω h g (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) (b k))) ((R.HW i σ).e U₂ fun ρ => v ρ))) 𝓕 ν :=
    fun k => by
      rw [hφ]
      exact (hR U₁ U₂ (io (PiTensorProduct.tprod ℂ v) (b k)) (io (PiTensorProduct.tprod ℂ v) (b k))).2.1
  clear hR
  have key := form_eq_sum hd.2.2.2.2.2.1 c hc (R.βV i) (datV i R.Pg (R.Q t) P m) (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v))) a1 a2 a3 (R.HW i σ) (inner_HW_lowC R hd.1 i σ)
    hν hy HV hV (fun ρ => v ρ) hv th a4 a5 U₁ U₂ b a6
  simp only [hφ] at key
  exact key

end Final

section Scalar

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
  {F : Face D A} {i : Fin D.R.m} {t : T} {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} {P : LevelP R.Pg D.R.r ℂ}
    {cμ cη : (AE D)ˣ →* Circle} {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ)}
    {BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ} {f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ}
    {c : CoefA (Vc D i)} {io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}
    (hd : IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io)
    {ν : Measure (GA D (Vc D i))} {𝓕 : Set (GA D (Vc D i))} (hν : IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕)

include hd hν in

theorem scalar_of_form_key_lowC (h3 : InnerProductFormulaC R F) (h4 : FockCoefficientC R F) (h5 : DeltaNorm D)
    (h6 : FiniteZetaC R F) (h7 : LevelIndexNormC R F) (h8 : MassLower D) (h9 : FormalDegreeUpperC R F) {b : ℝ} (hb : Sizes D i b)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] (th : X →ₗ[ℂ] (R.HW i σ).H)
    (key : ∀ {μ : @Measure (Datum.WO (Vc D i) (Wc D i)) (Datum.measMx _ _)} {𝓧 : Set (Datum.WO (Vc D i) (Wc D i))}
      (_ : Datum.IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧) {Fr : Frames (Wc D i)} (_ : IsFrames (Wc D i) Fr)
      {mR : ∀ ρ, Measure (Upq (Wc D i) ρ)} (_ : ∀ ρ, Lev.IsMinf (mR ρ)) (v : ∀ ρ, lowT (R.MW i σ) ρ) (_ : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) (U₁ U₂ : (R.HW i σ).H)
      {κ : Type} [Fintype κ] (b : OrthonormalBasis κ ℂ c.W), inner ℂ (LinearMap.adjoint th U₁) (LinearMap.adjoint th U₂) =
      ((∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ) : ℝ) : ℂ) ^ 2 * ∑ k,
        l2 ν 𝓕 (upLift R i ω (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) (b k))) ((R.HW i σ).e U₁ fun ρ => v ρ))
          (upLift R i ω (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) (b k))) ((R.HW i σ).e U₂ fun ρ => v ρ)))
    (ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (hev : typePart R i σ t P ev ≠ ⊥) :
    ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i σ t P ev, th (adjLev P th x) = (l : ℂ) • x) ∧
      mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l := by
  have hc : c.Is := hd.2.2.2.2.2.2.2.2.2.1
  obtain ⟨v, -, hv, -⟩ := hd.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨μ, 𝓧, hμ⟩ := exists_covol_lowC hd
  obtain ⟨Fr, hFr, mR, hmR⟩ := exists_frames_lowC R hd.1 i
  obtain ⟨x, hx, hZ⟩ := h6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd μ 𝓧 hμ ev hev
  have hdim : (1 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℂ c.W)) : ℕ) := by
    have := hc.2.2.2.1
    rw [Fintype.card_fin]
    exact_mod_cast Module.finrank_pos
  obtain ⟨b1, b2⟩ := scalar_bound_lowC hd hν h7 h8 h9 hb hμ hFr hmR v hv x hx _ hdim _ rfl
  refine ⟨_, b1, scalar_adjLev P th _ hev _ _ b1 fun U₁ hU₁ U₂ => ?_, b2⟩
  refine form_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ ((h5 i σ).trans ?_) (key hμ hFr hmR v hv U₁ U₂ (stdOrthonormalBasis ℂ c.W))
    (fun k => term_eval_lowC hd hν h3 h4 hμ hFr hmR v U₁ U₂ _ ((stdOrthonormalBasis ℂ c.W).orthonormal.1 k) _
      (hZ _ hU₁ _ (HMod_mem (hd.1.models.HW i σ) U₂))) (eq_of_value (R.HW i σ) (inner_HW_lowC R hd.1 i σ) U₁ U₂)
  push_cast
  rfl

end Scalar

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem adelC_of_innerProductFormula (R : RealDat D A Ks) (F : Face D A) :
    LiftIsCuspC R F → SourceLevelLawC R F → InnerProductFormulaC R F → FockCoefficientC R F → DeltaNorm D →
      FiniteZetaC R F → LevelIndexNormC R F → MassLower D → FormalDegreeUpperC R F → AdelC R F := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 hR i b hb t ht σ s hσ P hP cμ cη m hm ω hω BW hBW f₀ f hf hpt c hc io hio ν 𝓕 hν I _ y hy
    HV hV
  have hd : IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io := ⟨hR, ht, hσ, hP, hm, hω, hBW, hf, hpt, hc, hio⟩
  exact ⟨exists_isLift_lowC hd hν HV hV h1, fun th hth =>
    scalar_of_form_key_lowC hd hν h3 h4 h5 h6 h7 h8 h9 hb th fun {_ _} hμ {_} hFr {_} hmR v hv U₁ U₂ {_} _ b =>
      form_key_lowC hd hν HV hV hy h2 h3 th hth v hv U₁ U₂ b hμ hFr hmR⟩

end GlobalTheory.LowRow
