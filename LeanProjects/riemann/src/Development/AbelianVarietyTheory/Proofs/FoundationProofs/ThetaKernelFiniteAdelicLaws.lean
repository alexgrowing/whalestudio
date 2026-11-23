import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKORatLeftAndEigenRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl.KernLaws

theorem exists_finite_lift {D : D7} (V : HSp D) (q : Bridge.Gf V) : ∃ κ ∈ GfC V, fin V κ = q := by
  obtain ⟨_, g, rfl⟩ := q
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 (finHom V g)
  exact ⟨⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 g.2).2⟩⟩, k1, Subtype.ext k2⟩

theorem fin_mul {D : D7} (V : HSp D) (a b : GA D V) : fin V a * fin V b = fin V (a * b) :=
  (map_mul (finHom V).rangeRestrict a b).symm

theorem ratF_eq {D : D7} (V : HSp D) (γ : GQ V) : Bridge.ratF V γ = fin V γ := rfl

theorem lift_of_mem_J {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {κ : GA D V}
    (hκ : κ ∈ GfC V) (hk : fin V κ ∈ (levEnv V β L).J) :
    IsLevelLift V β L 1 κ ∧ ((((levEnv V β L).χ ⟨_, hk⟩)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  refine ⟨⟨hκ, hk.1, Subgroup.mem_bot.1 hk.2⟩, ?_⟩
  unfold levChi
  rw [← levFn_flag1, Units.val_inv_eq_inv_val]
  rfl

theorem exists_lift_J {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J) : ∃ κ, fin V κ = k ∧
    IsLevelLift V β L 1 κ ∧ ((((levEnv V β L).χ k)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  obtain ⟨k, hk⟩ := k
  obtain ⟨κ, hκ, rfl⟩ := exists_finite_lift V k
  exact ⟨κ, rfl, lift_of_mem_J V β L hκ hk⟩

theorem finE_of_fin {D : D7} (V : HSp D) {κ : GA D V} {x : Bridge.Gf V} (e : fin V κ = x) :
    finE V κ = Formalism.UG.bc (swapAE D) (x : GL _ _) := by
  have : finHom V κ = x.1 := congrArg Subtype.val e
  rw [finE_eq, this]

theorem exists_lift_Q {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).Q) : ∃ κ, fin V κ = k ∧
    IsLevelLift V β L (rTup β L (Formalism.UG.bc (swapAE D) ((k : Bridge.Gf V) : GL _ _))) κ ∧
      ((((levEnv V β L).ch k)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  obtain ⟨κ, hκ, e⟩ := exists_finite_lift V k.1
  have e' := finE_of_fin V e
  refine ⟨κ, e, ⟨hκ, ?_, congrArg (rTup β L) e'⟩, ?_⟩
  · rw [e']
    exact k.2.1
  · have e2 : (levEnv V β L).ch k = levFn β (flagL L) (finE V κ) := (congrArg (levFn β (flagL L)) e').symm
    rw [Units.val_inv_eq_inv_val, e2, levChi]

theorem lift_one {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsLevelLift V β L 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem exists_actL {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (g0 : G0 L.Pg L.r) (hex : ∃ κ, IsLevelLift V β L g0 κ) : ∃ κ, IsLevelLift V β L g0 κ ∧
      ∀ F h, actL V β L g0 F h = (levChi V β (flagL L) κ)⁻¹ * F (h * κ) := by
  refine ⟨hex.choose, hex.choose_spec, fun F h => ?_⟩
  change actG0 V β L g0 F h = _
  unfold actG0
  rw [dif_pos hex]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)

theorem kernA_apply (h : GA D (Vc D i)) (w : (R.cV i).W) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kernA R i t h w v g =
      Datum.thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w))) := rfl

theorem kernA_mul_real (hio : R.thP_ioP) (h : GA D (Vc D i)) {u : GA D (Vc D i)} (hu : u ∈ GinfC (Vc D i)) :
    kernA R i t (h * u) = kernA R i t h := by
  ext w v g
  rw [kernA_apply, kernA_apply]
  unfold Datum.thetaKO
  rw [show ((h * u, g) : GA D (Vc D i) × GA D (Wc D i)) = (h, g) * (u, 1) from Prod.ext rfl (mul_one g).symm,
    map_mul, Module.End.mul_apply, (hio i t).1 u hu, ← Module.End.mul_apply, ← map_mul, mul_inv_rev,
    mul_inv_cancel_left]

theorem kern_fin (hio : R.thP_ioP) (h : GA D (Vc D i)) : kern R i t (fin (Vc D i) h) = kernA R i t h := by
  unfold kern
  have e := (MonoidHom.mem_range.1 (fin (Vc D i) h).2).choose_spec
  generalize (MonoidHom.mem_range.1 (fin (Vc D i) h).2).choose = h' at e
  have hu : h⁻¹ * h' ∈ GinfC (Vc D i) := by
    change finHom (Vc D i) (h⁻¹ * h') = 1
    rw [map_mul, map_inv, e]
    exact inv_mul_cancel _
  rw [← kernA_mul_real R i t hio h hu, mul_inv_cancel_left]

theorem kernA_rat (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (γ : GQ (Vc D i)) (h : GA D (Vc D i)) (w : (R.cV i).W) :
    kernA R i t (γ * h) ((R.cV i).ρ γ w) = kernA R i t h w := by
  funext v g
  rw [kernA_apply, kernA_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ (hω i t) _
    (hpt i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w)))).1 γ γ.2 1 (one_mem _) h g
  rwa [one_mul] at this

theorem kernA_eigen (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i)) {κ' : GA D (Wc D i)} (hκ' : κ' ∈ GfC (Wc D i)) {c : ℂ}
    (e : R.ωP i t (κ, κ') (R.vP i t) = c • R.vP i t) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kernA R i t (h * κ) w v (g * κ') = c * kernA R i t h w v g := by
  rw [kernA_apply, kernA_apply, mul_inv_rev, map_mul, (hc i).1 _ (inv_mem hκ), one_mul]
  exact (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ (hω i t) _ (hpt i t _)).2 κ κ' c
    (GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ _ _ _ _ _ hθ (hω i t) _ _ _ _ _ (hpt i t) κ hκ κ' hκ' c e _) h g

theorem levChi_flag_datWp (κ' : GA D (Wc D i)) : levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κ' = 1 := by
  have h2 : ext1 (flagL (R.datWp i R.triv)).P.H (flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (flagL (R.datWp i R.triv)) (finE (Wc D i) κ')) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2, show (flagL (R.datWp i R.triv)).s = 0 from rfl, Finset.range_zero,
    show (flagL (R.datWp i R.triv)).Q = ∅ from rfl, Finset.prod_empty]
  simp only [Finset.prod_empty, Finset.prod_const_one, mul_one, Units.val_one]

theorem kern_rat (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP) (γ : GQ (Vc D i)) (h : Bridge.Gf (Vc D i))
    (w : (R.cV i).W) : kern R i t (Bridge.ratF (Vc D i) γ * h) ((R.cV i).coef.ρ γ w) = kern R i t h w := by
  obtain ⟨h', -, e⟩ := exists_finite_lift (Vc D i) h
  have e1 : kern R i t (Bridge.ratF (Vc D i) γ * h) = kernA R i t (γ * h') := by
    rw [← e, ratF_eq, fin_mul, kern_fin R i t hio]
  have e2 : kern R i t h = kernA R i t h' := by rw [← e, kern_fin R i t hio]
  rw [e1, e2]
  exact kernA_rat R i t hω hpt γ h' w

theorem kern_eigen (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i)) {κ' : GA D (Wc D i)} (hκ' : κ' ∈ GfC (Wc D i)) {c : ℂ}
    (e : R.ωP i t (κ, κ') (R.vP i t) = c • R.vP i t) (h : Bridge.Gf (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kern R i t (h * fin (Vc D i) κ) w v (g * κ') = c * kern R i t h w v g := by
  obtain ⟨h', -, e0⟩ := exists_finite_lift (Vc D i) h
  have e1 : kern R i t (h * fin (Vc D i) κ) = kernA R i t (h' * κ) := by
    rw [← e0, fin_mul, kern_fin R i t hio]
  have e2 : kern R i t h = kernA R i t h' := by rw [← e0, kern_fin R i t hio]
  rw [e1, e2]
  exact kernA_eigen R i t hθ hc hω hpt hκ hκ' e h' w v g

theorem eq_smul_of_mul_one {X Y : Type} [Monoid Y] (F F' : X → Y → ℂ) (c : ℂ) (h : ∀ v g, F v (g * 1) = c * F' v g) :
    F = c • F' := by
  funext v g
  rw [← mul_one g, h, mul_one]
  rfl

theorem eq_smul_of_mul {Y : Type} [Monoid Y] (B F F' : Y → ℂ) (a c : ℂ) (y : Y) (ha : a = 1) (h1 : ∀ g, B g = a⁻¹ * F (g * y))
    (h : ∀ g, F (g * y) = c * F' g) : B = c • F' := by
  funext g
  rw [h1, ha, inv_one, one_mul, h]
  rfl

theorem kern_level (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    (hD : DatumType R i t) (h : Bridge.Gf (Vc D i)) (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) (w : (R.cV i).W) :
    kern R i t (h * k) w = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k)⁻¹ : ℂˣ) : ℂ) • kern R i t h w := by
  obtain ⟨κ, e1, l1, e2⟩ := exists_lift_J (Vc D i) (R.βV i) (R.datVt i t) k
  rw [e2, ← e1]
  exact eq_smul_of_mul_one _ _ _ (kern_eigen R i t hθ hc hω hpt hio l1.1 (GfC (Wc D i)).one_mem
    (hD 1 κ 1 l1 (lift_one _ (R.βW i) (R.datWp i R.triv))) h w)

theorem kern_act (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    (hD : DatumType R i t) (g0 : G0 R.Pg D.R.r) (q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q)
    (hg : g0 = rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _)))
    (hex : ∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') (h : Bridge.Gf (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 (kern R i t (h * q) w v) =
      ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q)⁻¹ : ℂˣ) : ℂ) • kern R i t h w v := by
  refine (exists_lift_Q (Vc D i) (R.βV i) (R.datVt i t) q).elim fun κ H => ?_
  refine (exists_actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 hex).elim fun κ' H' => ?_
  have l1 : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ := ⟨H.2.1.1, H.2.1.2.1, H.2.1.2.2.trans hg.symm⟩
  have := kern_eigen R i t hθ hc hω hpt hio l1.1 H'.1.1 (hD g0 κ κ' l1 H'.1) h w v
  rw [H.2.2, ← H.1]
  exact eq_smul_of_mul _ _ _ _ _ κ' (levChi_flag_datWp R i κ') (H'.2 _) this

end GlobalTheory.TraceIncl.KernLaws

namespace GlobalTheory.TraceIncl

open KernLaws

theorem kern_laws : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0), R.models_inf → R.models_cV → R.thP_ωP → R.thP_pt_theta → R.thP_ioP → GlobalTheory.TraceIncl.DatumType R i t → (∀ h, GlobalTheory.TraceIncl.kern R i t (fin (Vc D i) h) = GlobalTheory.TraceIncl.kernA R i t h) ∧ (∀ (γ : GQ (Vc D i)) h w, GlobalTheory.TraceIncl.kern R i t (Bridge.ratF (Vc D i) γ * h) ((R.cV i).coef.ρ γ w) = GlobalTheory.TraceIncl.kern R i t h w) ∧ (∀ h (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) w, GlobalTheory.TraceIncl.kern R i t (h * k) w = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k)⁻¹ : ℂˣ) : ℂ) • GlobalTheory.TraceIncl.kern R i t h w) ∧ ∀ (g0 : G0 R.Pg D.R.r) (q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q), g0 = rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _)) → (∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') → ∀ h w v, actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 (GlobalTheory.TraceIncl.kern R i t (h * q) w v) = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q)⁻¹ : ℂˣ) : ℂ) • GlobalTheory.TraceIncl.kern R i t h w v := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i t hθ hc hω hpt hio hD
  exact ⟨kern_fin R i t hio, kern_rat R i t hω hpt hio, kern_level R i t hθ hc hω hpt hio hD,
    kern_act R i t hθ hc hω hpt hio hD⟩

end GlobalTheory.TraceIncl
