import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ProjComm

theorem coeff_conj_of_central {H : Type} [Group H] (z : MonoidAlgebra ℂ H) (hz : ∀ a, z * a = a * z) (g h : H) :
    z.coeff (g * h * g⁻¹) = z.coeff h := by
  have key := congrArg (fun w => w.coeff (g * h)) (hz (MonoidAlgebra.single g 1))
  simp only [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply, mul_one, one_mul,
    inv_mul_cancel_left] at key
  exact key

theorem goodProjector_coeff_classFunction (D : D7) (g h : G0g D.nd) : D.ntypes.e0.coeff (g * h * g⁻¹) = D.ntypes.e0.coeff h := by
  unfold NTypes.e0
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  refine finsum_congr fun a => ?_
  split_ifs
  · exact Finset.prod_congr rfl fun kv _ =>
      coeff_conj_of_central _ (D.ntypes.eSer_central kv.1 _) (g kv) (h kv)
  · rfl

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem isLift_mul {g g' : G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g κ) (hκ' : IsLevelLift V β L g' κ') :
    IsLevelLift V β L (g * g') (κ * κ') := by
  unfold IsLevelLift at hκ hκ' ⊢
  obtain ⟨h1, h2, h3⟩ := hκ
  obtain ⟨h1', h2', h3'⟩ := hκ'
  refine ⟨mul_mem h1 h1', ?_, ?_⟩
  · rw [map_mul]
    exact mul_mem h2 h2'
  · rw [map_mul, Formalism.L2.DIV.rTup_mul h2 h2', h3, h3']

theorem isLift_inv {g : G0 L.Pg L.r} {κ : GA D V} (hκ : IsLevelLift V β L g κ) :
    IsLevelLift V β L g⁻¹ κ⁻¹ := by
  unfold IsLevelLift at hκ ⊢
  obtain ⟨h1, h2, h3⟩ := hκ
  refine ⟨inv_mem h1, ?_, ?_⟩
  · rw [map_inv]
    exact inv_mem h2
  · rw [map_inv, Formalism.L2.DIV.rTup_inv h2, h3]

private theorem actG0_apply_eq_levChi_inv_mul_choose {g : G0 L.Pg L.r} (hex : ∃ κ, IsLevelLift V β L g κ) (F : GA D V → ℂ) (x : GA D V) :
    actG0 V β L g F x = (levChi V β (flagL L) hex.choose)⁻¹ * F (x * hex.choose) := by
  unfold actG0
  rw [dif_pos hex]

private theorem levChi_flagL_mul_of_mem_parLev {κ κ' : GA D V} (hκ : finE V κ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L)
    (hκ' : finE V κ' ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L) :
    levChi V β (flagL L) (κ * κ') = levChi V β (flagL L) κ * levChi V β (flagL L) κ' := by
  unfold levChi
  rw [map_mul, levFn_flag_mul hκ hκ', Units.val_mul]

theorem levelGroupAction_mul_of_lifts {g g' : G0 L.Pg L.r} (hg : ∃ κ, IsLevelLift V β L g κ) (hg' : ∃ κ, IsLevelLift V β L g' κ)
    {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    actG0 V β L g (actG0 V β L g' F) = actG0 V β L (g * g') F := by
  have hex := hg
  obtain ⟨κ', hκ'⟩ := hg'
  funext x
  have hc : IsLevelLift V β L g hex.choose := hex.choose_spec
  have hm : IsLevelLift V β L (g * g') (hex.choose * κ') := isLift_mul hc hκ'
  have hpar : finE V hex.choose ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := by
    unfold IsLevelLift at hc
    exact hc.2.1
  have hpar' : finE V κ' ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := by
    unfold IsLevelLift at hκ'
    exact hκ'.2.1
  rw [actG0_apply_eq_levChi_inv_mul_choose hex, level_action_spec hF ⟨κ', hκ'⟩ κ' hκ' (x * hex.choose),
    level_action_spec hF ⟨_, hm⟩ _ hm x, levChi_flagL_mul_of_mem_parLev hpar hpar', mul_assoc x]
  ring

theorem levelGroupAction_eq_zero_of_no_lift {g : G0 L.Pg L.r} (hg : ¬ ∃ κ, IsLevelLift V β L g κ) (F : GA D V → ℂ) :
    actG0 V β L g F = 0 := by
  unfold actG0
  exact dif_neg hg

theorem actL_conj (g h : G0 L.Pg L.r) {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    actL V β L (g * h * g⁻¹) (actL V β L g F) = actL V β L g (actL V β L h F) := by
  show actG0 V β L (g * h * g⁻¹) (actG0 V β L g F) = actG0 V β L g (actG0 V β L h F)
  by_cases hg : ∃ κ, IsLevelLift V β L g κ
  · obtain ⟨κ, hκ⟩ := hg
    by_cases hh : ∃ κ, IsLevelLift V β L h κ
    · obtain ⟨μ, hμ⟩ := hh
      have hc : ∃ κ, IsLevelLift V β L (g * h * g⁻¹) κ :=
        ⟨κ * μ * κ⁻¹, isLift_mul (isLift_mul hκ hμ) (isLift_inv hκ)⟩
      rw [levelGroupAction_mul_of_lifts hc ⟨κ, hκ⟩ hF, levelGroupAction_mul_of_lifts ⟨κ, hκ⟩ ⟨μ, hμ⟩ hF, inv_mul_cancel_right]
    · have hc : ¬ ∃ κ, IsLevelLift V β L (g * h * g⁻¹) κ := by
        rintro ⟨ν, hν⟩
        apply hh
        have hl := isLift_mul (isLift_mul (isLift_inv hκ) hν) hκ
        rw [show g⁻¹ * (g * h * g⁻¹) * g = h by group] at hl
        exact ⟨_, hl⟩
      rw [levelGroupAction_eq_zero_of_no_lift hc, levelGroupAction_eq_zero_of_no_lift hh]
      exact (map_zero (actL V β L g)).symm
  · rw [levelGroupAction_eq_zero_of_no_lift hg F, levelGroupAction_eq_zero_of_no_lift hg (actG0 V β L h F)]
    exact map_zero (actL V β L (g * h * g⁻¹))

theorem gaL_comm {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)
    (hc : ∀ g h, c (g * h * g⁻¹) = c h) (g : G) {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    gaL V β L eG c (actL V β L (eG g) F) = actL V β L (eG g) (gaL V β L eG c F) := by
  unfold gaL
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun y => ?_).symm
  show c y • actL V β L (eG g) (actL V β L (eG y) F) =
    c (g * y * g⁻¹) • actL V β L (eG (g * y * g⁻¹)) (actL V β L (eG g) F)
  rw [hc, map_mul, map_mul, map_inv, actL_conj _ _ hF]

theorem proj_comm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.grp_record → (∀ g F, HasType (Yc D 0) (R.βY 0) (R.dat0 R.triv) F → R.e0 (actL _ (R.βY 0) (R.dat0 R.triv) (R.eG g) F) = actL _ (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.e0 F)) ∧ ∀ i σ g F, HasType (Wc D i) (R.βW i) (R.datWp i R.triv) F → R.eWf i σ (actL _ (R.βW i) (R.datWp i R.triv) (R.eG g) F) = actL _ (R.βW i) (R.datWp i R.triv) (R.eG g) (R.eWf i σ F) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R _ hrec
  obtain ⟨eR, plg, iso, he, -, -⟩ := hrec
  have hcls : ∀ a b : G, (idemOf A.X).coeff (a * b * a⁻¹) = (idemOf A.X).coeff b := fun a b =>
    D.what₂.embLL.injective (by rw [he, he, map_mul eR, map_mul eR, map_inv eR, goodProjector_coeff_classFunction])
  have hcl : ∀ (σ : D.what₂.LL →+* ℂ) (a b : G),
      RealDat.eC (A := A) σ (a * b * a⁻¹) = RealDat.eC (A := A) σ b := fun σ a b => by
    unfold RealDat.eC
    rw [hcls]
  refine ⟨fun g F hF => ?_, fun i σ g F hF => ?_⟩
  · exact gaL_comm (L := R.dat0 R.triv) R.eG _ (hcl _) g hF
  · exact gaL_comm (L := R.datWp i R.triv) R.eG _ (hcl σ) g hF

end GlobalTheory.ProjComm

end
