import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalProductsTendstoFrameStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilVacuumEqResidueCharDetSmulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacLaw

theorem redFn_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) (PP : Pl E) (a : Formalism.L2.Herm.intAf F E) (ha : resS F PP a = 1)
    {x y : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))} (hx : x ∈ St β) (hy : y ∈ St β)
    (h : ∀ i j, (a : TensorProduct F E (Formalism.L2.Herm.Af F)) * x.1 i j =
      (a : TensorProduct F E (Formalism.L2.Herm.Af F)) * y.1 i j) :
    redFn β PP x = redFn β PP y := by
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  rw [redFn_frGL, redFn_frGL]
  ext i j
  simp [frGL, intGL, Formalism.UG.bc] at h ⊢
  have hinv : (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))⁻¹ =
      ((β⁻¹ : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) _) :=
    (Matrix.coe_units_inv β).symm
  have hBiB : ((β⁻¹ : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) _) *
      (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) = 1 := Units.inv_mul β
  have back : ∀ Z : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)),
      ((β⁻¹ : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) _) *
        ((a : TensorProduct F E (Formalism.L2.Herm.Af F)) •
          ((β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) * Z *
            (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))⁻¹)) *
        (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) =
      (a : TensorProduct F E (Formalism.L2.Herm.Af F)) • Z := by
    intro Z
    rw [Matrix.mul_smul, Matrix.smul_mul, hinv]
    congr 1
    calc _ = (((β⁻¹ : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) _) *
            (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))) * Z *
          (((β⁻¹ : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) _) *
            (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))) := by
          simp only [Matrix.mul_assoc]
      _ = Z := by rw [hBiB, Matrix.one_mul, Matrix.mul_one]
  have hm : (a : TensorProduct F E (Formalism.L2.Herm.Af F)) •
        ((β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) * (x' : Matrix (Fin n) (Fin n) ↥(Formalism.L2.Herm.intAf F E)).map Subtype.val *
          (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))⁻¹) =
      (a : TensorProduct F E (Formalism.L2.Herm.Af F)) •
        ((β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) * (y' : Matrix (Fin n) (Fin n) ↥(Formalism.L2.Herm.intAf F E)).map Subtype.val *
          (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))⁻¹) := by
    ext k l
    simpa [Matrix.smul_apply] using h k l
  have hxy := congrArg (fun Z => Z i j) ((back _).symm.trans
    ((congrArg (fun W => ((β⁻¹ : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) : Matrix (Fin n) (Fin n) _) * W *
      (β : Matrix (Fin n) (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))) hm).trans (back _)))
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at hxy
  have hs : a * (x' : Matrix (Fin n) (Fin n) ↥(Formalism.L2.Herm.intAf F E)) i j = a * (y' : Matrix (Fin n) (Fin n) ↥(Formalism.L2.Herm.intAf F E)) i j :=
    Subtype.ext (by simpa using hxy)
  have hr := congrArg (resS F PP) hs
  simpa [map_mul, ha] using hr

variable {D : D7}

def detScal (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) (c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (k : GA D V) : ℂˣ :=
  ∏ PP ∈ P, c PP (Matrix.GeneralLinearGroup.det (redFn β PP (finE V k)))

theorem detScal_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    (c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : detScal V β P c 1 = 1 := by
  simp [detScal, redFn, blockDiagonalExtendByOnePrimeField_one]

theorem detScal_mul (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    (c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) {k l : GA D V} (hk : finE V k ∈ St β) (hl : finE V l ∈ St β) :
    detScal V β P c (k * l) = detScal V β P c k * detScal V β P c l := by
  unfold detScal
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun PP _ => ?_
  simp only [map_mul]
  rw [show redFn β PP (finE V k * finE V l) = redFn β PP (finE V k) * redFn β PP (finE V l) from extendMatrixByIdentityAlongIndices_mul _ hk hl]
  simp only [map_mul]

theorem vacScal_eq {S T : HSp D} (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (P : Finset (Pl D.host.E)) (cS cT : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (g : GA D S) (h : GA D T) :
    vacScal βS βT P cS cT g h =
      ((detScal S βS P (fun PP => (cT PP)⁻¹) g : ℂˣ) : ℂ) * ((detScal T βT P cS h : ℂˣ) : ℂ) := by
  simp [vacScal, detScal, Finset.prod_mul_distrib]

theorem law_of_local (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (e : AE D) (P : Finset (Pl D.host.E))
    (c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) {W : Type} (ρ : GA D V →* Module.End ℂ (W → ℂ)) (f : W → ℂ)
    (he : IsIdemSum e P) (hc : ∀ w, Continuous fun k => ρ k f w)
    (hloc : ∀ k ∈ GfC V, finE V k ∈ St β → ∀ v ε, IsPlaceIdem D v ε → SuppPl ε V k →
      ρ k f = ((detScal V β P c k : ℂˣ) : ℂ) • f) :
    ∀ g ∈ GfC V, finE V g ∈ St β → ρ g f = ((detScal V β P c g : ℂˣ) : ℂ) • f := by
  intro g hg hgS
  obtain ⟨γ, hγ, hs⟩ := GlobalTheory.T.exists_local_products_tendsto_frameStabiliser D V β g hg hgS
  obtain ⟨⟨es, hes, rfl⟩, _⟩ := he

  have hfin : ∀ (k : GA D V) (i j : Fin V.rank),
      ((finE V k : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) i j =
        toEAf D (Formalism.L2.Theta.mt V k i j) := by
    intro k i j
    simp [finE, Formalism.UG.bc, finHom, Formalism.L2.Theta.mt, toEAf, swapAE, Formalism.L2.Theta.finPart]

  have hgen : ∀ k ∈ Subgroup.closure
      {k : GA D V | k ∈ GfC V ∧ finE V k ∈ St β ∧ ∃ v ε, IsPlaceIdem D v ε ∧ SuppPl ε V k},
      k ∈ GfC V ∧ finE V k ∈ St β ∧ ρ k f = ((detScal V β P c k : ℂˣ) : ℂ) • f := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem k hk =>
      obtain ⟨hk1, hk2, v, ε, hv, hsupp⟩ := hk
      exact ⟨hk1, hk2, hloc k hk1 hk2 v ε hv hsupp⟩
    | one =>
      refine ⟨(GfC V).one_mem, ?_, ?_⟩
      · rw [map_one]
        exact (St β).one_mem
      · simp [detScal_one]
    | mul k l _ _ hk hl =>
      obtain ⟨hk1, hk2, hk3⟩ := hk
      obtain ⟨hl1, hl2, hl3⟩ := hl
      refine ⟨(GfC V).mul_mem hk1 hl1, ?_, ?_⟩
      · rw [map_mul]
        exact (St β).mul_mem hk2 hl2
      · rw [detScal_mul V β P c hk2 hl2, ρ.map_mul, Module.End.mul_apply, hl3, LinearMap.map_smul, hk3, smul_smul,
          Units.val_mul, mul_comm]
    | inv k _ hk =>
      obtain ⟨hk1, hk2, hk3⟩ := hk
      have hk2' : finE V k⁻¹ ∈ St β := by
        rw [map_inv]
        exact (St β).inv_mem hk2
      refine ⟨(GfC V).inv_mem hk1, hk2', ?_⟩
      have hd : ((detScal V β P c k⁻¹ : ℂˣ) : ℂ) * ((detScal V β P c k : ℂˣ) : ℂ) = 1 := by
        rw [← Units.val_mul, ← detScal_mul V β P c hk2' hk2, inv_mul_cancel, detScal_one, Units.val_one]
      have h1 : f = ((detScal V β P c k : ℂˣ) : ℂ) • ρ k⁻¹ f := by
        calc f = ρ (k⁻¹ * k) f := by rw [inv_mul_cancel, ρ.map_one, Module.End.one_apply]
          _ = _ := by rw [ρ.map_mul, Module.End.mul_apply, hk3, LinearMap.map_smul]
      calc ρ k⁻¹ f = (((detScal V β P c k⁻¹ : ℂˣ) : ℂ) * ((detScal V β P c k : ℂˣ) : ℂ)) • ρ k⁻¹ f := by
            rw [hd, one_smul]
        _ = _ := by rw [mul_smul, ← h1]

  have hev : ∀ᶠ s in Filter.atTop, detScal V β P c (γ s) = detScal V β P c g := by
    have hP : ∀ PP ∈ P, ∀ᶠ s in Filter.atTop, redFn β PP (finE V (γ s)) = redFn β PP (finE V g) := by
      intro PP hPP
      obtain ⟨hsp, _⟩ := hes PP hPP
      obtain ⟨hee, hec, v, ε, hv, hsum⟩ := hsp
      obtain ⟨hint, hres⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hes PP hPP)
      have hfix : es PP * algebraMap (AF D.host.F) (AE D) ε = es PP := by
        rw [← hsum, mul_add, hee, hec, add_zero]
      filter_upwards [Filter.eventually_ge_atTop {v}] with s hsv
      have hvs : v ∈ s := Finset.singleton_subset_iff.mp hsv
      refine redFn_congr β PP ⟨toEAf D (es PP), hint⟩ hres (hgen (γ s) (hs s).1).2.1 hgS ?_
      intro i j
      have hij := (hs s).2 v hvs ε hv i j
      dsimp only
      rw [hfin, hfin, ← map_mul (toEAf D), ← map_mul (toEAf D), ← hfix, mul_assoc, mul_assoc, hij]
    filter_upwards [(Filter.eventually_all_finset P).2 hP] with s hs'
    unfold detScal
    exact Finset.prod_congr rfl fun PP hPP => by rw [hs' PP hPP]

  funext w
  have h1 : Filter.Tendsto (fun s => ρ (γ s) f w) Filter.atTop (nhds (ρ g f w)) :=
    ((hc w).tendsto g).comp hγ
  have h2 : Filter.Tendsto (fun s => ρ (γ s) f w) Filter.atTop
      (nhds ((((detScal V β P c g : ℂˣ) : ℂ) • f) w)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with s hs'
    rw [(hgen (γ s) (hs s).1).2.2, hs']
  exact tendsto_nhds_unique h1 h2

theorem suppPl_one (ε : AF D.host.F) (V : HSp D) : SuppPl ε V 1 := by
  intro i j
  simp [SuppPl, Formalism.L2.Theta.mt]

theorem vac_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (θ : InfFam D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (e : AE D) (P : Finset (Pl D.host.E)) (cS cT : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f : WO S T → ℂ), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → IsIdemSum e P → TameOn χS e P cS → TameOn χT e P cT → (∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → FixesVacAt ψ S T ΛS ΛT om v ε) → IsVacO ψ θ S T sS sT ΛS ΛT f → ∀ g ∈ GfC S, ∀ h ∈ GfC T, finE S g ∈ St βS → finE T h ∈ St βT → om (g, h) f = vacScal βS βT P cS cT g h • f := by
  intro D ψ S T χS χT om θ sS sT ΛS ΛT βS βT e P cS cT f hW hθ hS hT hsS hsT hΛS hΛT hfS hfT he htS htT hfx hvac g hg h hh hgS hhT

  have loc := GlobalTheory.T.weil_vacuum_eq_residueChar_det_smul D ψ S T χS χT om θ sS sT ΛS ΛT βS βT e P cS cT f hW hθ hS hT hsS hsT hΛS hΛT hfS hfT he
    htS htT hfx hvac

  have hcont : ∀ w, Continuous fun p : GA D S × GA D T => om p f w := hW.9 f hvac.2.2
  have hS1 : finE S 1 ∈ St βS := by
    rw [map_one]
    exact (St βS).one_mem
  have hT1 : finE T 1 ∈ St βT := by
    rw [map_one]
    exact (St βT).one_mem

  have lawS : ∀ k ∈ GfC S, finE S k ∈ St βS →
      om (k, 1) f = ((detScal S βS P (fun PP => (cT PP)⁻¹) k : ℂˣ) : ℂ) • f :=
    law_of_local S βS e P (fun PP => (cT PP)⁻¹) (om.comp (MonoidHom.inl (GA D S) (GA D T))) f he
      (fun w => (hcont w).comp (continuous_id.prodMk continuous_const)) (by
        intro k hk hkS v ε hv hsupp
        have hl := loc k hk 1 (GfC T).one_mem hkS hT1 v ε hv hsupp (suppPl_one ε T)
        rw [vacScal_eq, detScal_one, Units.val_one, mul_one] at hl
        exact hl)

  have lawT : ∀ k ∈ GfC T, finE T k ∈ St βT → om (1, k) f = ((detScal T βT P cS k : ℂˣ) : ℂ) • f :=
    law_of_local T βT e P cS (om.comp (MonoidHom.inr (GA D S) (GA D T))) f he
      (fun w => (hcont w).comp (continuous_const.prodMk continuous_id)) (by
        intro k hk hkT v ε hv hsupp
        have hl := loc 1 (GfC S).one_mem k hk hS1 hkT v ε hv (suppPl_one ε S) hsupp
        rw [vacScal_eq, detScal_one, Units.val_one, one_mul] at hl
        exact hl)

  have hsplit : ((g, h) : GA D S × GA D T) = (g, 1) * (1, h) := by
    simp
  rw [hsplit, om.map_mul, Module.End.mul_apply, lawT h hh hhT, LinearMap.map_smul, lawS g hg hgS, smul_smul, vacScal_eq,
    mul_comm]

end GlobalTheory.VacLaw

end
