import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberPeriodAtTrivialPositionSpec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.TrueRecordEq

open GlobalTheory.Mem.TrueRecord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfF D}

theorem ker_leftE {ψ : AddChar (AF D.host.F) ℂ} (Wf : WeilFun D ψ) (hW : Wf.EqRank) {V W : HSp D} {χ χ' : IdC D}
    (ha : admitted V W χ χ' ∨ AdmE V W χ χ') (Φ : ThS ψ V W) {γ : GA D V} (hγ : γ ∈ GQ V) (g h) :
    Wf.ker V W χ χ' Φ (γ * g) h = Wf.ker V W χ χ' Φ g h := by
  have e : Wf.om V W χ χ' (γ * g, h) = Wf.om V W χ χ' (γ, 1) * Wf.om V W χ χ' (g, h) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  unfold WeilFun.ker
  rw [e, Module.End.mul_apply]
  exact ha.elim (fun ha => Wf.om_aut V W χ χ' ha γ hγ 1 (one_mem _) _)
    fun ha => (hW.weil V W χ χ' ha).aut γ hγ 1 (one_mem _) _

theorem exists_liftE (hL : LiftAut D) (hE : LiftAutEq D) (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (Wf : WeilFun D ψ) (hW : Wf.EqRank) (V W : HSp D) (χ χ' : IdC D) :
    ∃ t : ThS ψ V W →ₗ[ℂ] CuspS θ V →ₗ[ℂ] AFs θ W, (¬ ((admitted V W χ χ' ∨ AdmE V W χ χ') ∧ V.SigOK) → t = 0) ∧
      (admitted V W χ χ' ∨ AdmE V W χ χ' → V.SigOK → ∀ μ 𝓕, IsVolPair D V μ 𝓕 → ∀ Φ F h,
        (t Φ F).1 h = ∫ g in 𝓕, Wf.ker V W χ χ' Φ g h * F.1 g ∂μ) := by
  by_cases h : (admitted V W χ χ' ∨ AdmE V W χ χ') ∧ V.SigOK
  · have k : ∀ (Φ : ThS ψ V W) (F : CuspS θ V),
        (∀ h, IntegrableOn (fun g => Wf.ker V W χ χ' Φ g h * F.1 g) (dom V) (mu V)) ∧
        IsAutFunSm θ W fun h => ∫ g in dom V, Wf.ker V W χ χ' Φ g h * F.1 g ∂(mu V) := fun Φ F =>
      h.1.elim (fun ha => hL θ hθ ψ hψ Wf V W χ χ' ha _ _ (quot_mu V) Φ F.1 (cuspF hθ F))
        fun ha => hE θ hθ ψ hψ V W χ χ' ha _ (hW.weil V W χ χ' ha) _ _ (quot_mu V) Φ F.1 (cuspF hθ F)
    refine ⟨LinearMap.mk₂ ℂ (fun Φ F => ⟨_, Submodule.subset_span (k Φ F).2⟩) ?_ ?_ ?_ ?_, fun h' => absurd h h', ?_⟩
    · intro Φ Φ' F
      ext x
      simp only [Submodule.coe_add, Pi.add_apply]
      rw [← integral_add ((k Φ F).1 x) ((k Φ' F).1 x)]
      simp [WeilFun.ker, add_mul]
    · intro c Φ F
      ext x
      simp only [Submodule.coe_smul, Pi.smul_apply]
      rw [← integral_smul]
      simp [WeilFun.ker, mul_assoc]
    · intro Φ F F'
      ext x
      simp only [Submodule.coe_add, Pi.add_apply]
      rw [← integral_add ((k Φ F).1 x) ((k Φ F').1 x)]
      simp [mul_add]
    · intro c Φ F
      ext x
      simp only [Submodule.coe_smul, Pi.smul_apply]
      rw [← integral_smul]
      simp [mul_left_comm]
    · intro ha hV μ 𝓕 hμ Φ F x
      refine integral_mu hV hμ (fun g => Wf.ker V W χ χ' Φ g x * F.1 g) fun γ hγ g => ?_
      rw [ker_leftE Wf hW ha Φ hγ g x, (cuspF hθ F).1.left γ hγ]
  · exact ⟨0, fun _ => rfl, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩

section Record

variable (hP : PetInt D) (hT : TopInt D) (hB : BesInt D) (hL : LiftAut D) (hE : LiftAutEq D) (hθ : IsInfFam θ)
  {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (Wf : WeilFun D ψ) (hW : Wf.EqRank) (Tw : Tow D) (Rc : RecFun D θ ψ)

abbrev recXE : ThetaX D where
  AF V := AFs θ V
  cusp V := cuspIn θ V
  pet V F G := (Rc.petC V : ℂ) * petForm hP hθ V F (cuspEq θ V G)
  pet_add_left V F F' G := ses_add _ _ _ _ _
  pet_smul_left V c F G := ses_smul _ _ _ _ _
  pet_right V F := ses_right _ _ _ _
  pet_symm V F G := by
    rw [petForm_apply, petForm_apply, star_mul', Complex.star_def, Complex.conj_ofReal, ← integral_conj]
    congr 2
    funext g
    rw [map_mul, mul_comm]
    exact congrArg₂ _ (star_star _).symm rfl
  pet_pos V F hF := by
    have h := GlobalTheory.T.petersson_normSq_pos_automorphicFunction_unitary D V _ _ (quot_mu V) F.1.1 (aut hθ F.1).toIsAutFun
      (fun h => hF (Subtype.ext (Subtype.ext h)))
      (hP θ hθ V _ _ (quot_mu V) _ _ (aut hθ F.1) (cuspF hθ (cuspEq θ V F)))
    rw [Complex.re_ofReal_mul]
    exact mul_pos (mul_pos (Rc.petF_pos V) (Finset.prod_pos fun _ _ => Rc.meas.petR_pos _ _)) h
  actR := actReal hθ
  actR_one V τ := LinearMap.ext fun F => Subtype.ext <| funext fun x => by
    rw [actReal_apply hθ V τ (by simp [Formalism.QuantumDeterminants.UH]), (GlobalTheory.PointAtPlaceHom.atTau_laws D θ hθ V τ).2.1, mul_one]; rfl
  actR_mul V τ g hg h hh := LinearMap.ext fun F => Subtype.ext <| funext fun x => by
    rw [Module.End.mul_apply, actReal_apply hθ V τ hg, actReal_apply hθ V τ hh, actReal_apply hθ V τ (mul_mem_UH hg hh),
      (GlobalTheory.PointAtPlaceHom.atTau_laws D θ hθ V τ).2.2.1 g hg h hh, mul_assoc]
  actR_cusp V τ g hg F hF := by
    rw [actReal, dif_pos hg]; exact trE_cusp hθ V _ _ F hF
  Gf V := GfC V
  actF := actFin hθ
  actF_cusp V g F hF := trE_cusp hθ V g (fun φ h => GlobalTheory.T.smoothAutomorphicForm_rightTranslate_finiteAdelic D θ hθ V φ h g g.2) F hF
  actF_actR V g τ h := by
    unfold actReal
    split_ifs with hh
    · refine LinearMap.ext fun F => Subtype.ext <| funext fun x => ?_
      change F.1 (x * g * atTau θ V τ h) = F.1 (x * atTau θ V τ h * g)
      rw [mul_assoc, mul_assoc, (GlobalTheory.PointAtPlaceHom.atTau_laws D θ hθ V τ).2.2.2.1 h g g.2]
    · rw [mul_one, one_mul]
  Ksph := ksph
  Ksph_mono V S S' h g hg := mem_ksph.2 ((GlobalTheory.T.exists_lattice_stabiliser_subgroup_outside_places D V S).choose_spec.2 S' h (mem_ksph.1 hg))
  typ V P := (TypS θ V P).comap (AFs θ V).subtype
  Chr := chrGrp D
  infTy := expo
  infTy_mul χ χ' τ := expo_eq ((GlobalTheory.T.heckeCharacter_infinityExponent_group_laws D).2.2 _ _ _ _ _ (expo_spec χ τ) (expo_spec χ' τ))
  chrOf μ j := ⟨Rc.chr μ j, mem_chrGrp.2 (Rc.chr_hc μ j)⟩
  chrOf_inf μ j τ := expo_eq (Rc.chr_inf μ j τ)
  etaT := ⟨Rc.eta, mem_chrGrp.2 ⟨Rc.eta_hc, fun τ => ⟨_, Rc.eta_inf τ⟩⟩⟩
  etaT_inf τ := Or.inl (expo_eq (Rc.eta_inf τ))
  etaT_pos τ := expo_eq (Rc.eta_inf τ)
  Sch V W := ThS ψ V W
  fact V W := {Φ | IsPureFun ψ V W Φ.1}
  kfin V W := KfinS ψ θ Rc.dec V W
  th V W χ χ' := (Rc.petC V : ℂ) • (exists_liftE hL hE hθ hψ Wf hW V W χ.1 χ'.1).choose.compl₂ (cuspEq θ V).toLinearMap
  Xs := Tw.Xs
  Xs_rank := Tw.Xs_rank
  Xs_sig t j hj := ⟨(Tw.Xs_sig t j hj).1, fun τ => Or.inl ((Tw.Xs_sig t j hj).2 τ)⟩
  Ys := Tw.Ys
  Ys_rank := Tw.Ys_rank
  Ys_sig t j hj := (Tw.Ys_sig t j hj).1
  iXYs := Tw.iXYs
  iXYs_isom := Tw.iXYs_isom
  iYXm := Tw.iYXm
  iYXm_isom := Tw.iYXm_isom
  YsLow := Tw.YsLow
  YsLow_zero := Tw.YsLow_zero
  Xs_rec := Tw.Xs_rec
  Ys_rec := Tw.Ys_rec
  conjAF V F := ⟨fun g => star (F.1 g), Submodule.subset_span (GlobalTheory.T.isSmoothAutomorphicFunction_star D θ hθ V _ (aut hθ F))⟩
  conjAF_add V F F' := Subtype.ext (funext fun g => star_add _ _)
  conjAF_smul V c F := Subtype.ext (funext fun g => star_mul' _ _)
  conjAF_conjAF V F := Subtype.ext (funext fun g => star_star _)
  conjAF_cusp V F hF := by
    rw [mem_cuspIn hθ] at hF ⊢
    exact (GlobalTheory.T.isCuspFunction_closed_under_operations D V _ _ (aut hθ F).toIsAutFun (aut hθ F).toIsAutFun hF hF).2.2.2
  Pos A B ι := PosT A B ι
  FJd _ _ _ := ℂ
  Bper A B ι p _ φ F := (Rc.petC A : ℂ) * perT hB hθ hψ Rc A B ι p φ (cuspEq θ B F)
  Bper_right A B ι p s φ := ses_right _ _ _ _
  Bper_add_left A B ι p s φ φ' F := ses_add _ _ _ _ _
  Bper_smul_left A B ι p s c φ F := ses_smul _ _ _ _ _
  Bper_odd _ _ _ _ _ _ _ _ _ := rfl
  Btop A B ι φ F := (Rc.petC B : ℂ) * (exists_top hT hθ A B ι).choose φ (cuspEq θ B F)
  Btop_right A B ι φ := ses_right _ _ _ _
  Btop_add_left A B ι φ φ' F := ses_add _ _ _ _ _
  Btop_smul_left A B ι c φ F := ses_smul _ _ _ _ _
  pos1 u := .inr (u, ⟨rfl⟩)
  posSym u := .inl fun _ => bes0 u
  colAF u μ j := (cuspEq θ _).symm.toLinearMap.comp (Rc.col u μ j)
  rowAF μ j := (cuspEq θ _).symm.toLinearMap.comp (Rc.row μ j)
  PhiY := Rc.Phi
  PhiYup μ j := transp (Rc.Phi μ j)
  mY := Rc.mY
  mY_pos := Rc.mY_pos
  adelicDataRowMeasureScale_trivialTuple := Rc.adelicDataRowMeasureScale_trivialTuple
  mY_zero := Rc.mY_zero

abbrev recTE : ThetaTied D (recXE hP hT hB hL hE hθ hψ Wf hW Tw Rc) where
  ev V := (AFs θ V).subtype
  ev_inj V := Subtype.val_injective
  ev_aut V F := (aut hθ F).toIsAutFun
  cusp V F := mem_cuspIn hθ F
  eGf V := MulEquiv.refl _
  actF V g F x := rfl
  actR := ⟨⟨θ, hθ⟩, fun θ' h' V τ g hg => by
    obtain rfl : θ' = θ := (GlobalTheory.Mem.InfFamUnique.existsUnique_infFam D).unique h' hθ
    have h1 := (GlobalTheory.PointAtPlaceHom.atTau_laws D θ' hθ V τ).1 g hg
    refine ⟨h1.exists, fun h hh F x => ?_⟩
    have e : atTau θ' V τ g = h := by
      rw [atTau, dif_pos h1.exists]; exact h1.unique h1.exists.choose_spec hh
    rw [← e]
    exact actReal_apply hθ V τ hg F x⟩
  ksph V S g := mem_ksph
  conj V F x := rfl
  petF := Rc.petF
  petF_pos := Rc.petF_pos
  petR := Rc.meas.petR
  petR_pos := Rc.meas.petR_pos
  petR_def := Rc.meas.petR_def
  petR_minf := Rc.meas.petR_minf
  pet V hV μ 𝓕 hμ F G := congrArg (fun z => (Rc.petC V : ℂ) * z) <|
    integral_mu hV hμ (fun h => star (F.1 h) * G.1.1 h) fun γ hγ g => by
      rw [(aut hθ F).left γ hγ, (aut hθ G.1).left γ hγ]
  btop A B ι hB' hι μ 𝓕 hμ s hs φ F := congrArg (fun z => (Rc.petC B : ℂ) * z) <|
    (exists_top hT hθ A B ι).choose_spec hB' hι μ 𝓕 hμ s hs φ (cuspEq θ B F)
  eChr := (chrGrp D).subtype
  eChr_inj := Subtype.val_injective
  eChr_range := Set.ext fun χ => ⟨fun ⟨x, hx⟩ => hx ▸ mem_chrGrp.1 x.2, fun h => ⟨⟨χ, mem_chrGrp.2 h⟩, rfl⟩⟩
  infTy := expo_spec
  chrOf_res := Rc.chr_res
  etaT_res := Rc.eta_res
  etaT_unr := Rc.eta_unr
  etaT_exp τ := expo_eq (Rc.eta_inf τ)
  xs_pos t j hj := (Tw.Xs_sig t j hj).2
  ys_sig t j hj := (Tw.Ys_sig t j hj).2
  ysLow := Tw.YsLow_witt

abbrev recWE : WeilTied D (recXE hP hT hB hL hE hθ hψ Wf hW Tw Rc) (recTE hP hT hB hL hE hθ hψ Wf hW Tw Rc) where
  ψ := ψ
  ψ_std := hψ
  evS V W := (ThS ψ V W).subtype
  evS_inj V W := Subtype.val_injective
  evS_range V W _ := range_ThS V W
  om V W χ χ' := Wf.om V W χ.1 χ'.1
  om_heis V W χ χ' h h1 h2 := Wf.om_heis V W _ _ (adm χ χ' h h1 h2)
  om_aut V W χ χ' h h1 h2 := Wf.om_aut V W _ _ (adm χ χ' h h1 h2)
  om_cont V W χ χ' h h1 h2 := Wf.om_cont V W _ _ (adm χ χ' h h1 h2)
  om_unit V W χ χ' h h1 h2 := Wf.om_unit V W _ _ (adm χ χ' h h1 h2)
  om_split V W χ χ' h h1 h2 := Wf.om_split V W _ _ (adm χ χ' h h1 h2)
  om_tw :=
    { twW_up := fun V W χ χ' ν h h1 h2 h3 g k x hx => by
        have := Wf.twW V W _ _ ν.1 (adm χ χ' h.ne h1 h2) (mem_chrGrp.1 ν.2) h3 g k x hx
        rw [if_pos h] at this
        exact this
      twV_up := fun V W χ χ' ν h h1 h2 h3 g k x hx => by
        have := Wf.twV V W _ _ ν.1 (adm χ χ' h.ne h1 h2) (mem_chrGrp.1 ν.2) h3 g k x hx
        rw [if_pos h] at this
        exact this
      twW_dn := fun V W χ χ' ν h h1 h2 h3 g k x hx => by
        have := Wf.twW V W _ _ ν.1 (adm χ χ' h.ne' h1 h2) (mem_chrGrp.1 ν.2) h3 g k x hx
        rw [if_neg h.not_gt] at this
        exact this
      twV_dn := fun V W χ χ' ν h h1 h2 h3 g k x hx => by
        have := Wf.twV V W _ _ ν.1 (adm χ χ' h.ne' h1 h2) (mem_chrGrp.1 ν.2) h3 g k x hx
        rw [if_neg h.not_gt] at this
        exact this }
  om_swap V W χ χ' h h1 h2 := Wf.om_swap V W _ _ (adm χ χ' h h1 h2)
  th V W χ χ' h h1 h2 hV μ 𝓕 hμ Φ F x := congrArg (fun z => (Rc.petC V : ℂ) * z) <|
    (exists_liftE hL hE hθ hψ Wf hW V W χ.1 χ'.1).choose_spec.2 (Or.inl (adm χ χ' h h1 h2)) hV μ 𝓕 hμ Φ (cuspEq θ V F) x

def recKE : KfinTied (recWE hP hT hB hL hE hθ hψ Wf hW Tw Rc) where
  cpt := Rc.dec.cpt
  cpt_gram := Rc.dec.cpt_gram
  bas := Rc.dec.bas
  bas_unit := Rc.dec.bas_unit
  bas_orth := Rc.dec.bas_orth
  cpt_bas := Rc.dec.cpt_bas
  kfin := ⟨⟨θ, hθ⟩, fun θ' h' V W _ hV hW' Φ => by
    obtain rfl : θ' = θ := (GlobalTheory.Mem.InfFamUnique.existsUnique_infFam D).unique h' hθ
    exact mem_KfinS hθ hψ Rc.dec hV hW' Φ⟩

theorem besGlobE_inl {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (ho : Odd (B.rank - A.rank)) (hA : A.SigOK)
    (hι : HSpace.IsIsomEmb A B ι) (f : Odd (B.rank - A.rank) → Bes1 A B ι) :
    BesGlob (recTE hP hT hB hL hE hθ hψ Wf hW Tw Rc) ψ (f ho).1 (.inl f : PosT A B ι) :=
  fun _ _ _ hμ _ hs φ F hφ => clause_inl hB hθ hψ Rc ho hA hι f hμ hs φ F hφ

def recBE : BesselTied D (recXE hP hT hB hL hE hθ hψ Wf hW Tw Rc) (recTE hP hT hB hL hE hθ hψ Wf hW Tw Rc)
    (recWE hP hT hB hL hE hθ hψ Wf hW Tw Rc) where
  dat A B ι ho p := (datT A B ι ho p).1
  dat_y A B ι ho p := (datT A B ι ho p).2
  besC _ _ _ _ := 1
  besC_pos _ _ _ _ := one_pos
  besC_one _ _ _ _ := rfl
  bper A B ι ho _ hA hι p hp σ μ 𝓕 hμ ν 𝓝 h1 h2 h3 s hs φ F hφ := by
    rw [one_mul]
    rcases p with f | x
    · exact besGlobE_inl hP hT hB hL hE hθ hψ Wf hW Tw Rc ho hA hι f σ μ 𝓕 hμ s hs φ F hφ ν 𝓝 h1 h2 h3
    · obtain ⟨u, hu⟩ := hp
      exact absurd hu (inr_ne A B ι x _)

theorem realisesE : RealisesE (θ := θ) (recBE hP hT hB hL hE hθ hψ Wf hW Tw Rc) Wf Tw Rc where
  inf := hθ
  forms V := Set.ext fun φ => ⟨fun ⟨x, hx⟩ => hx ▸ aut hθ x, fun h => ⟨⟨φ, Submodule.subset_span h⟩, rfl⟩⟩
  typ V P F := Iff.rfl
  sch V V' := range_ThS V V'
  chr μ j := rfl
  eta := rfl
  col u μ j φ := rfl
  row μ j F := rfl
  phi μ j := rfl
  phiUp μ j hj x := transp_apply hψ (rank_Y_ne (recXE hP hT hB hL hE hθ hψ Wf hW Tw Rc) j hj) (Rc.Phi μ j) x
  mY := rfl
  petF := rfl
  petR := rfl
  xs := rfl
  ys := rfl
  ysLow := rfl
  iXYs t j := HEq.rfl
  iYXm t := HEq.rfl
  om V V' χ χ' p Φ f h := by
    obtain rfl : Φ = f := Subtype.ext h
    rfl
  thOff V V' χ χ' h := by
    change (Rc.petC V : ℂ) • (exists_liftE hL hE hθ hψ Wf hW V V' χ.1 χ'.1).choose.compl₂ (cuspEq θ V).toLinearMap = 0
    rw [(exists_liftE hL hE hθ hψ Wf hW V V' χ.1 χ'.1).choose_spec.1 h]
    ext
    simp
  thEq V V' χ χ' h hV μ 𝓕 hμ Φ F x := congrArg (fun z => (Rc.petC V : ℂ) * z) <|
    (exists_liftE hL hE hθ hψ Wf hW V V' χ.1 χ'.1).choose_spec.2 (Or.inr h) hV μ 𝓕 hμ Φ (cuspEq θ V F) x
  fact V V' Φ := Iff.rfl
  kfin := ⟨recKE hP hT hB hL hE hθ hψ Wf hW Tw Rc, rfl, rfl⟩
  posDat u ho := ⟨rfl, rfl⟩
  pos1Val u σ μ 𝓕 hμ ν 𝓝 hν s hs φ F := memberPeriodAtTrivialPosition_spec hB hθ hψ Rc u hμ hν hs φ F
  besAll A A' ι ho hA hι d hd :=
    ⟨(.inl fun _ => ⟨d, hd⟩ : PosT A A' ι), rfl, besGlobE_inl hP hT hB hL hE hθ hψ Wf hW Tw Rc ho hA hι fun _ => ⟨d, hd⟩⟩
  besOnly A A' ι ho hA hι p := by
    rcases p with f | x
    · exact Or.inl (besGlobE_inl hP hT hB hL hE hθ hψ Wf hW Tw Rc ho hA hι f)
    · exact Or.inr ⟨x.1, inr_eq A A' ι x⟩

end Record

theorem exists_realisedE : ∀ D : D7, PetInt D → TopInt D → BesInt D → LiftAut D → LiftAutEq D → ∀ (θ : InfF D), IsInfFam θ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (Wf : WeilFun D ψ), Wf.EqRank → ∀ (Tw : Tow D) (Rc : RecFun D θ ψ), ∃ (X : ThetaX D) (T : ThetaTied D X) (W : WeilTied D X T) (B : BesselTied D X T W) (h : W.ψ = ψ), RealisesE (θ := θ) B (h ▸ Wf) Tw (h ▸ Rc) := by
  intro D hP hT hB hL hE θ hθ ψ hψ Wf hW Tw Rc
  exact ⟨_, _, _, recBE hP hT hB hL hE hθ hψ Wf hW Tw Rc, rfl, realisesE hP hT hB hL hE hθ hψ Wf hW Tw Rc⟩

end GlobalTheory.Mem.TrueRecordEq

end
