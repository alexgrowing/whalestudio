import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevChiLift
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitProductRescaleDisjointFinsets
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDatOfTower
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReadsG

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.FamInhab

open GlobalTheory.Fam.Inhab

variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (P : LevelP R.Pg D.R.r ℂ)

theorem cp_iff (t : T) (j : ℕ) (F : SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) : F ∈ CP R P t j ↔ F ∈ R.CC t j ∧
    ∀ (p : P.H) κ, IsLevelLift (Yc D j) (R.βY j) (R.datYt t j R.triv) p.1 κ → ∀ w g,
      (levChi _ (R.βY j) (flagL (R.datYt t j R.triv)) κ)⁻¹ * F w (g * κ) = ((P.chi p : ℂˣ) : ℂ) * F w g :=
  GlobalTheory.ChainOnto.LevelWithP.mem_multT_withP_iff D R.θ (Yc D j) _ (R.MY j) (R.βY j) (R.datYt t j R.triv) P F

theorem cxp_iff (t : T) (F : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) : F ∈ CXP R P t ↔
    F ∈ MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t)) ∧
    ∀ (p : P.H) κ, IsLevelLift D.sp.X' R.βX (R.datXt t) p.1 κ → ∀ w g,
      (levChi _ R.βX (flagL (R.datXt t)) κ)⁻¹ * F w (g * κ) = ((P.chi p : ℂˣ) : ℂ) * F w g :=
  GlobalTheory.ChainOnto.LevelWithP.mem_multT_withP_iff D R.θ D.sp.X' _ R.MX R.βX (R.datXt t) P F

theorem ioY_mem (hCR : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) (t : T) (k : ℕ)
    (hk : k + 1 < D.R.m) (F : R.CC t (k + 1)) (hF : F.1 ∈ CP R P t (k + 1)) : (R.ioY t k F).1 ∈ CP R P t k := by
  have hk' : k < D.R.m := by omega
  refine (cp_iff P t k _).2 ⟨(R.ioY t k F).2, fun p κ hκ w g => ?_⟩
  obtain ⟨κ', hκ'⟩ := GlobalTheory.ChainEquiv.lifts_chain R.toLevCh _ hl t (k + 1) hk p.1
  exact step_eigen (L := R.datYt t k R.triv) (L' := R.datYt t (k + 1) R.triv) (io := R.ioY t k) (It := R.ItY k) hm.inf hCR
    (hc.ωY t k hk) (hc.ptY t k hk) rfl (GlobalTheory.ChainEquiv.meas_chain hm.νY hm.νY' t k hk') (hc.ItY t k hk).ne
    (fun U w => (GlobalTheory.ChainEquiv.multT_value _ _ _ _ _ U.2 w).1) (GlobalTheory.ChainEquiv.meas_chain hm.νY hm.νY' t (k + 1) hk)
    (hc.ioY t k (by omega)) hκ hκ' (GlobalTheory.StepVecLaw.stepVec_lifts R hl hm.inf hc.ωY hc.vY t k hk p.1 κ κ' hκ hκ') F
    (((cp_iff P t (k + 1) _).1 hF).2 p κ' hκ') w g

theorem pred_lt : D.R.m - 1 < D.R.m := by have := D.R.two_le_m; omega

theorem lifts_top (hl : R.toLevCh.Is A.μ0) (t : T) : LiftsExist D.sp.X' R.βX (R.datXt t) := by
  obtain ⟨c, hβ⟩ := hl.βX
  exact GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hβ (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).1 (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).2

theorem ioX_mem (hCR : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) (t : T)
    (F : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (hF : F.1 ∈ CXP R P t) : (R.ioX t F).1 ∈ CP R P t (D.R.m - 1) := by
  refine (cp_iff P t _ _).2 ⟨(R.ioX t F).2, fun p κ hκ w g => ?_⟩
  refine (lifts_top hl t p.1).elim fun κ' hκ' => ?_
  have h1 : (R.νX t).IsHaarMeasure ∧ IsFundamentalDomain (GQ D.sp.X') (R.fdX t) (R.νX t) := ⟨(hm.νX t).1.1, (hm.νX t).2⟩
  have h2 := GlobalTheory.ChainEquiv.range_left R.cX R.prX (R.HX t) _ _ (hm.HX t).2.1
  have h3 := ((cxp_iff P t _).1 hF).2 p κ' hκ'
  have h4 := GlobalTheory.StepLaw.last_step_law R hl hm.inf hc.ωX hc.vX t p.1 κ κ' hκ hκ'
  exact step_eigen (L := R.datYt t (D.R.m - 1) R.triv) (L' := R.datXt t) (io := R.ioX t) (It := R.ItX) hm.inf hCR
    (hc.ωX t) (hc.ptX t) rfl (GlobalTheory.ChainEquiv.meas_chain hm.νY hm.νY' t _ pred_lt) (hc.ItX t).ne h2 h1
    (hc.ioX t) hκ hκ' h4 F h3 w g

include R in
theorem finite_H : Finite P.H := by
  haveI : Finite (G0 R.Pg D.R.r) := Finite.of_equiv G R.eG.toEquiv
  infer_instance

theorem rankY {j : ℕ} (hj : j ≤ D.R.m) : (Yc D j).rank = D.R.r + j * D.R.t := GlobalTheory.Chain.StepVac.rank_Yc hj

theorem sd {V : HSp D} {β Λ N} (h : IsSDFrame V β Λ N) : IsSelfDualC V Λ ∧ IsFrame β Λ :=
  ⟨GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ h, h.elim fun _ hc => hc.1⟩

theorem vec_lev (hl : R.toLevCh.Is A.μ0) (t : T) (k : ℕ) (hk : k < D.R.m) {V : HSp D} {sT : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Lev.EAf D)} {N : ℕ} (hβ : IsSDFrame V β Λ N)
    {χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO (Yc D k) V → ℂ}
    (hf : IsStepVecOf R.ψ R.θ (Yc D k) V (cart (R.MY k)) sT (R.ΛY k) Λ (R.βY k) β (R.datYt t k R.triv) χ (R.Q t) (R.xiR t) f₀ f) :
    ∃ f', IsStepVecOf R.ψ R.θ (Yc D k) V (cart (R.MY k)) sT (R.ΛY k) Λ (R.βY k) β (R.datYt t k P) χ (R.Q t) (R.xiR t) f₀ f' :=
  GlobalTheory.PlaceDatum.stepVecExists D R.ψ R.θ _ _ _ _ _ _ _ _ _ _ _ _ (sd (hl.βY k hk)).1 (sd hβ).1 (sd (hl.βY k hk)).2 (sd hβ).2
    (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).2 (hf.2.imp fun _ h => h.1) f₀ hf.1

def vXT (R : RealDat D A Ks) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : WO (Yc D (j + 1)) D.sp.X' → ℂ :=
  Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) (R.vX t) (idx_top h)

def itXT (R : RealDat D A Ks) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    PolF D D.sp.X'.rank (Yc D (j + 1)).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY (j + 1)) :=
  Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) R.ItX (idx_top h)

theorem top_weil (hc : R.IsChain) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsWeilDatumO R.ψ (Yc D (j + 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1 + 1)).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1 + 1)).2 (omT R t j h) := by
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO R.ψ (Yc D n) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') (R.ωX t) e) := by
    intro n e; subst e; exact hc.ωX t
  rw [show j + 1 + 1 = D.R.m from h]
  exact key _ (idx_top h)

theorem top_vec (hc : R.IsChain) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsStepVecOf R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX) (R.ΛY (j + 1)) R.ΛX (R.βY (j + 1)) R.βX
      (R.datYt t (j + 1) R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) (vacT R j h) (vXT R t j h) := by
  have key : ∀ n (e : D.R.m - 1 = n), IsStepVecOf R.ψ R.θ (Yc D n) D.sp.X' (cart (R.MY n)) (cart R.MX) (R.ΛY n) R.ΛX (R.βY n) R.βX
      (R.datYt t n R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) R.vacX e)
      (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) (R.vX t) e) := by
    intro n e; subst e; exact hc.vX t
  exact key _ (idx_top h)

theorem top_io (hc : R.IsChain) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    Lift.IsIo (R.νX t) (R.fdX t) (thetaKO (omT R t j h)) (pureTensorO R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1)))
      (cart R.MX) (onb (R.MY (j + 1))) (onb R.MX) (vXT R t j h)) (itXT R j h) _ _ (ioXT R t j h) := by
  have key : ∀ n (e : D.R.m - 1 = n), Lift.IsIo (R.νX t) (R.fdX t)
      (thetaKO (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') (R.ωX t) e))
      (pureTensorO R.ψ R.θ (Yc D n) D.sp.X' (cart (R.MY n)) (cart R.MX) (onb (R.MY n)) (onb R.MX)
        (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) (R.vX t) e))
      (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY n)) R.ItX e) _ _
      (Eq.rec (motive := fun n _ => LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n) (R.ioX t) e) := by
    intro n e; subst e; exact hc.ioX t
  exact key _ (idx_top h)

theorem top_mem (hCR : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) (t : T) (j : ℕ)
    (h : j + 2 * 0 + 2 = D.R.m) (F : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (hF : F.1 ∈ CXP R P t) :
    (ioXT R t j h F).1 ∈ CP R P t (j + 1) := by
  have key : ∀ n (e : D.R.m - 1 = n), ((Eq.rec (motive := fun n _ => LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n)
      (R.ioX t) e : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t n) F).1 ∈ CP R P t n := by
    intro n e; subst e; exact ioX_mem P hCR hl hm hc t F hF
  exact key _ (idx_top h)

theorem rank_top {j : ℕ} (h : j + 2 * 0 + 2 = D.R.m) : D.sp.X'.rank = D.R.r + (j + 1 + 1) * D.R.t := by
  rw [show j + 1 + 1 = D.R.m from h]; exact D.sp.X'_rank

def restr {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] {A A' : Submodule ℂ X} {B B' : Submodule ℂ Y}
    (f : A' →ₗ[ℂ] B') (h : A ≤ A') (hm : ∀ x : A', x.1 ∈ A → (f x).1 ∈ B) : A →ₗ[ℂ] B :=
  LinearMap.codRestrict B (B'.subtype ∘ₗ f ∘ₗ Submodule.inclusion h) fun x => hm _ x.2

theorem restr_coe {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] {A A' : Submodule ℂ X}
    {B B' : Submodule ℂ Y} (f : A' →ₗ[ℂ] B') (h : A ≤ A') (hm : ∀ x : A', x.1 ∈ A → (f x).1 ∈ B) (x : A) :
    (restr f h hm x).1 = (f ⟨x.1, h x.2⟩).1 := rfl

theorem exists_core {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (V₀ W₀ : HSp D) {χV χW : (AE D)ˣ →* Circle} {om : Om V W}
    (hom : IsWeilDatumO ψ V W χV χW om) (hV : V.rank % 2 = V₀.rank % 2) (hW : W.rank % 2 = W₀.rank % 2) :
    ∃ om₀, IsWeilDatumO ψ V₀ W₀ χV χW om₀ :=
  GlobalTheory.Unf.Inhab.exists_weil hom.std V₀ W₀ hom.hecS hom.hecT (Formalism.L2.Theta.resEta_parity hom.resS hV)
    (Formalism.L2.Theta.resEta_parity hom.resT hW)

def mkStep {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (V₀ W₀ : HSp D) {χV χW : (AE D)ˣ →* Circle} {om : Om V W}
    (hom : IsWeilDatumO ψ V W χV χW om) (hV : V.rank % 2 = V₀.rank % 2) (hW : W.rank % 2 = W₀.rank % 2) (vW : Vol W) (ρ σ : ℕ) :
    Step ψ V V₀ W W₀ ρ σ :=
  ⟨χV, χW, om, (exists_core V₀ W₀ hom hV hW).choose, hom, (exists_core V₀ W₀ hom hV hW).choose_spec, vW,
    (GlobalTheory.Unf.Inhab.nonempty_volM D W.rank ρ).some, (GlobalTheory.Unf.Inhab.nonempty_volM D σ V₀.rank).some,
    (GlobalTheory.Unf.Inhab.nonempty_volU D ρ).some⟩

theorem cxp_le (hT : Formalism.IndefR.RecTie.TopMultH R) (t : T) : CXP R P t ≤ LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) :=
  fun F hF => (hT t).ge ((cxp_iff P t F).1 hF).1

theorem cp_le (t : T) (j : ℕ) : CP R P t j ≤ R.CC t j := fun F hF => ((cp_iff P t j F).1 hF).1

theorem even_idx {j ρ : ℕ} (h : j + 2 * ρ + 2 = D.R.m) : Even j := by
  obtain ⟨a, ha⟩ := D.R.m_even
  exact ⟨a - ρ - 1, by omega⟩

def rowOf (hCR : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain)
    (hT : Formalism.IndefR.RecTie.TopMultH R) (u : D.what₂.Word) (g : Fam.Geo D) (t : T) : RowCh R P u g t where
  vP j := if h : j + 1 < D.R.m then (vec_lev P hl t j (by omega) (hl.βY (j + 1) h) (hc.vY t j h)).choose else 0
  vT j h := (vec_lev P hl t (j + 1) (by omega) hl.βX (top_vec hc t j h)).choose
  sBF j ρ h := mkStep _ _ (hc.ωY t j (by omega)) (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.bes j ρ h).d) (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.jac j ρ h).d)
    (g.vol (j + 1)) ρ ρ
  sFB j σ h := mkStep _ _ (hc.ωY t (j + 1) (by omega)) (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.jac j (σ + 1) h).d)
    (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.bes (j + 1 + 1) σ (idx_step h)).d) (g.vol (j + 1 + 1)) (σ + 1) σ
  io j := if h : j + 1 < D.R.m then restr (R.ioY t j) (cp_le P t (j + 1)) (ioY_mem P hCR hl hm hc t j h) else 0
  ioT j h := restr (ioXT R t j h) (cxp_le P hT t) (top_mem P hCR hl hm hc t j h)

theorem rowOf_is (hCR : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain)
    (hT : Formalism.IndefR.RecTie.TopMultH R) (u : D.what₂.Word) (g : Fam.Geo D) (t : T) : (rowOf P hCR hl hm hc hT u g t).Is where
  vP j h := by
    have e : (rowOf P hCR hl hm hc hT u g t).vP j = (vec_lev P hl t j (by omega) (hl.βY (j + 1) h) (hc.vY t j h)).choose := dif_pos h
    rw [e]
    exact (vec_lev P hl t j (by omega) (hl.βY (j + 1) h) (hc.vY t j h)).choose_spec
  vT j h := (vec_lev P hl t (j + 1) (by omega) hl.βX (top_vec hc t j h)).choose_spec
  sBF j ρ h := by
    have ho : Odd (j + 1) := (even_idx h).add_one
    refine ⟨rfl, rfl, ?_, ?_⟩
    · show (Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1)).1 = _
      rw [Lift.chrStep, if_pos ho]
    · show (Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1)).2 = _
      rw [Lift.chrStep, if_pos ho]
  sFB j σ h := by
    have ho : ¬ Odd (j + 1 + 1) := Nat.not_odd_iff_even.2 (even_idx h).add_one.add_one
    refine ⟨rfl, rfl, ?_, ?_⟩
    · show (Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1 + 1)).1 = _
      rw [Lift.chrStep, if_neg ho]
    · show (Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1 + 1)).2 = _
      rw [Lift.chrStep, if_neg ho]
  io j h F := by
    have e : (rowOf P hCR hl hm hc hT u g t).io j = restr (R.ioY t j) (cp_le P t (j + 1)) (ioY_mem P hCR hl hm hc t j h) := dif_pos h
    rw [e]
    exact ⟨cp_le P t (j + 1) F.2, restr_coe _ _ _ F⟩
  ioT j h F := ⟨cxp_le P hT t F.2, restr_coe (ioXT R t j h) (cxp_le P hT t) (top_mem P hCR hl hm hc t j h) F⟩

theorem rowOf_same (hCR : GlobalTheory.Published.CuspRapidDecay) (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain)
    (hT : Formalism.IndefR.RecTie.TopMultH R) (u : D.what₂.Word) (g : Fam.Geo D) (t t' : T) :
    (rowOf P hCR hl hm hc hT u g t).Same (rowOf P hCR hl hm hc hT u g t') :=
  ⟨fun _ _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ _ => ⟨rfl, rfl, rfl⟩⟩

structure LiftLaws {c : Comm D} (t : Tup c) : Prop where
  sBF : ∀ j ρ h, (t.sBF j ρ h).om = t.om j ∧ (t.sBF j ρ h).vW = c.vol (j + 1)
  sFB : ∀ j σ h, (t.sFB j σ h).om = t.om (j + 1) ∧ (t.sFB j σ h).vW = c.vol (j + 1 + 1)
  pt : ∀ j, j + 1 < D.R.m → ∀ P, IsThetaFunO c.ψ _ _ (t.pt j P)
  ptT : ∀ j h P, IsThetaFunO c.ψ _ _ (t.ptT j h P)
  CC : ∀ j, j < D.R.m → ∃ J χ, t.CC j ≤ MultT c.θ (c.M j) J χ
  CT : ∃ J χ, t.CT ≤ MultT c.θ c.MT J χ
  io : ∀ j, j + 1 < D.R.m → ∀ (G : t.CC (j + 1)) P v,
    liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (G.1 v) (t.pt j P) = t.cI j • (t.io j G).1 (c.It j P v)
  ioT : ∀ j h (F : t.CT) P v,
    liftS (t.omT j h) c.volT.μ c.volT.𝓕 (F.1 v) (t.ptT j h P) = t.cI (j + 1) • (t.ioT j h F).1 (c.ItT j h P v)
  cI : ∀ j, j < D.R.m → t.cI j ≠ 0

def volSmul {V : HSp D} {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (h : ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓕 ν)
    {c : ENNReal} (hc : c ≠ 0 ∧ c ≠ ⊤) : Vol V :=
  ⟨c • ν, 𝓕, by haveI := h.1; exact Measure.IsHaarMeasure.smul ν hc.1 hc.2, h.2.mono Measure.smul_absolutelyContinuous⟩

section Read

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {At : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C At Pm} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (K : ClassesAtPrimes M bad)

variable {K}

def valG {K : ClsPTied u} (V : ValPTied u K) : ValuationAtPrimes K.toG fun _ => False :=
  ⟨V.sg, V.eW, V.ptC, V.ipP, V.rat, fun _ h => h.elim⟩

end Read

section Real

open GlobalTheory.MiS

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word)

def colBase (ψ : (D.chTw u D.what₂.mu0).cls D.R.m → (D.chTw u D.what₂.mu0).Y D.R.m → ℂ) :
    (D.mem u).C.cls D.R.m → (D.mem u).C.Y D.R.m → ℂ :=
  Eq.rec (motive := fun C _ => C.cls D.R.m → C.Y D.R.m → ℂ) ψ (D.memberColumns_twistedChain_base u)

variable {W}

theorem topMult : Formalism.IndefR.RecTie.TopMultH (pk W) :=
  (GlobalTheory.DefiniteMult.topMult_and_extV_injective D _ _ _ _ _ (pk W) _ W.Q.charW.base).1

def colOne (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (om : ∀ j, Om (D.sp.X j) (D.sp.X (j + 1))) : ColCh u C where
  kom := om
  Ch _ := Unit
  dd _ _ _ := Finsupp.single 0 1
  e _ _ := Finsupp.single 1 1
  eT _ _ _ := Finsupp.single 1 1
  Ram _ := Set.univ
  S _ := id
  rd _ _ _ _ := 0
  cV _ := 1
  cK _ := 1
  cP := 1

end Real

end GlobalTheory.Fam.FamInhab

end
