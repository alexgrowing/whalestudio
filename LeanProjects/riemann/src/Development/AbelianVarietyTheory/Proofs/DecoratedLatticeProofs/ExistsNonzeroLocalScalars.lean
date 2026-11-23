import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmPureTensorOComb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataChainStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataTopStepStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumCombinationsDifferByScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.GVecAt

section Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem theta_comb (hψ : IsStdChar D ψ (-1)) {c : WO S T →₀ ℂ} (hc : IsFinComb c) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T c f) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun u hu => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (hc u hu))

theorem comb_smul (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  funext w
  simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem comb_zero (c : WO S T →₀ ℂ) : comb ψ S T c 0 = 0 := by
  have := comb_smul (ψ := ψ) c 0 0
  rwa [zero_smul, zero_smul] at this

theorem comb_pureTensorO (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS sT BS BT) {e : WO S T →₀ ℂ} (he : IsFinComb e)
    {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀) (P) :
    comb ψ S T e (pureTensorO ψ θ S T sS sT BS BT f₀ P) = pureTensorO ψ θ S T sS sT BS BT (comb ψ S T e f₀) P := by
  let q := e.support.equivFin
  have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hψ hθ sS sT BS BT f₀ hf₀ e.support.card
    (fun i => e (q.symm i).1) (fun i => (q.symm i).1) (fun i => he _ (q.symm i).2) P).1
  have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ e.support, e u • g u = ∑ i, e (q.symm i).1 • g (q.symm i).1 := by
    intro g
    rw [← Finset.sum_coe_sort e.support]
    exact (Equiv.sum_comp q.symm (fun u : e.support => e u.1 • g u.1)).symm
  simp only [comb]
  rw [h1, h1]
  exact key

theorem fock {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hθ : IsInfFam θ) (hW : IsWeilDatumO ψ S T χS χT om) (sS sT BS BT)
    {d o e : WO S T →₀ ℂ} {g : WO S T → ℂ} {s : ℂ} (hd : IsFinComb d) (ho : IsFinComb o) (he : IsFinComb e)
    (hg : IsThetaFunO ψ S T g) {b : GA D S} (hb : b ∈ GfC S) {b' : GA D T} (hb' : b' ∈ GfC T)
    (h : om (b, b') (comb ψ S T d g) = s • comb ψ S T e (comb ψ S T o (om (b, b') g))) (P) {a : GA D S} (ha : a ∈ GinfC S)
    {a' : GA D T} (ha' : a' ∈ GinfC T) :
    om (a * b, a' * b') (comb ψ S T d (pureTensorO ψ θ S T sS sT BS BT g P)) =
      s • comb ψ S T e (comb ψ S T o (om (a * b, a' * b') (pureTensorO ψ θ S T sS sT BS BT g P))) := by
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hfin : ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) ∧
      om (b, b') (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (om (b, b') f) P := fun f hf =>
    GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT b b'
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.one_mul]) f hf P
  have hbg := hW.om_pres (b, b') g hg
  have e1 : ((a * b, a' * b') : GA D S × GA D T) = (a, a') * (b, b') := rfl
  have t1 : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT (om (b, b') g) P) := (hfin _ hbg).1
  have t2 : IsThetaFunO ψ S T (comb ψ S T o (pureTensorO ψ θ S T sS sT BS BT (om (b, b') g) P)) := theta_comb hψ ho t1
  rw [e1, map_mul, Module.End.mul_apply, Module.End.mul_apply, comb_pureTensorO hψ hθ sS sT BS BT hd hg,
    (hfin _ (theta_comb hψ hd hg)).2, h, GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, (hfin g hg).2,
    ← comb_pureTensorO hψ hθ sS sT BS BT he (theta_comb hψ ho hbg), ← comb_pureTensorO hψ hθ sS sT BS BT ho hbg,
    GlobalTheory.FrComb.om_comb hW ha ha' he t2, GlobalTheory.FrComb.om_comb hW ha ha' ho t1]

theorem pureTensorO_zero (sS sT BS BT) (P) : pureTensorO ψ θ S T sS sT BS BT (0 : WO S T → ℂ) P = 0 := by
  have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ S T sS sT BS BT 0 0 P
  rwa [zero_smul, zero_smul] at this

theorem vac_mono {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} (P : GlobalTheory.FinPl.Pl D → Prop) {f : WO S T → ℂ}
    (h : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) f) : GlobalTheory.FinPl.Vac ψ S T LS LT P f := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True :=
    AddSubgroup.closure_mono fun w ⟨α, hα, _, hw⟩ => ⟨α, hα, fun _ h => absurd trivial h, hw⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

end Gen

end GlobalTheory.GVecAt

namespace GlobalTheory.GVecAt

theorem datum_mid : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, IsDG W j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (o' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb f.c.ψ _ _ o' ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j))) ∧ (((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j)) ≠ 0 → comb f.c.ψ _ _ o' ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, IsDG W j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) d → (pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((pk W).vac j)) = κ • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o' ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j))) := GlobalTheory.T.descent_data_chain_step
theorem datum_top : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∀ d₀, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (M' : GlobalTheory.FinPl.Lat D.sp.X') (o' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ), IsSelfDualC (Yc D (j + 1)) M ∧ IsSelfDualC D.sp.X' M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.gP) (comb f.c.ψ _ _ o' (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h))) ∧ ((omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h)) ≠ 0 → comb f.c.ψ _ _ o' (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) d → omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (pk W) j h)) = κ • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ o' (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h))) := GlobalTheory.T.descent_data_top_step
theorem scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)) (o o' : WO S T →₀ ℂ) (g₀ : WO S T → ℂ), IsStdChar D ψ (-1) → IsSelfDualC S M → IsSelfDualC T M' → IsSelfDualC S N → IsSelfDualC T N' → GlobalTheory.FinPl.CombAt (· ∈ Q) o → GlobalTheory.FinPl.CombAt (· ∈ Q) o' → GlobalTheory.FinPl.Vac ψ S T M M' (· ∈ Q) g₀ → GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ Q) (comb ψ S T o g₀) → GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ Q) (comb ψ S T o' g₀) → comb ψ S T o' g₀ ≠ 0 → ∃ c : ℂ, comb ψ S T o g₀ = c • comb ψ S T o' g₀ := GlobalTheory.T.latticeVacuumCombinations_differ_by_scalar

section Fam

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

theorem weil_top (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : ∃ χS χT, IsWeilDatumO (pk W).ψ (Yc D (j + 1)) D.sp.X' χS χT
    (omT (pk W) W.P.A3.A.μ0 j h) := by
  have hω := W.Q.charW.base.chain.ωX W.P.A3.A.μ0
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (pk W).ψ (Yc D n) D.sp.X'
      (Lift.chrStep ((pk W).toLevCh.mu W.P.A3.A.μ0) (pk W).eta D.R.m).1
      (Lift.chrStep ((pk W).toLevCh.mu W.P.A3.A.μ0) (pk W).eta D.R.m).2
      (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((pk W).ωX W.P.A3.A.μ0) e) := by
    intro n e
    subst e
    exact hω
  exact ⟨_, _, key _ (GlobalTheory.Fam.idx_top h)⟩

end Fam

theorem main : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∃ s : ℕ → ℂ, (∀ j, s j ≠ 0) ∧ GVec f v s := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR
  have fin : ∀ {S T : HSp D} (P : GlobalTheory.FinPl.Pl D → Prop) (e : WO S T →₀ ℂ), IsStdChar D (pk W).ψ (-1) →
      GlobalTheory.FinPl.CombAt P e → IsFinComb e := fun P e hψ he =>
    ((GlobalTheory.DisjComb.main D (pk W).ψ hψ _ _ P (fun _ => False) (fun _ _ h => h)).2.1 e he).1
  have mid : ∀ j, j + 1 < D.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ d, IsDG W j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1))
      ((pk W).vac j) d → ∀ P, ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, (pk W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1))
        (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1)))
          (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P)) = c • comb f.c.ψ _ _ (v.eG j) (v.Ψ j P a a') := by
    intro j hj
    by_cases hex : ∃ d₀, IsDG W j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) d₀
    swap
    · exact ⟨1, one_ne_zero, fun d hd => absurd ⟨d, hd⟩ hex⟩
    obtain ⟨d₀, hd₀⟩ := hex
    obtain ⟨M, M', o', hM, hM', ho', hg0, ho'v, ho'nz, κ, hκ, hdat⟩ := datum_mid D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT
      n G pl hGP hGR j hj d₀ hd₀
    obtain ⟨o, ho, hΨ⟩ := hVT.Ψ j hj
    have hstd : IsStdChar D (pk W).ψ (-1) := hd₀.2.1.1
    have hinf : IsInfFam (pk W).θ := hd₀.2.1.2.inf
    have hvth : IsThetaFunO (pk W).ψ _ _ ((pk W).vac j) := hd₀.2.1.2.theta
    have hWe := W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj
    have hb : f.g.b j ∈ GfC _ := hVT.b j ▸ hv.b j
    have hb' : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
    have hΨ1 : v.Ψ j 1 1 1 = comb f.c.ψ _ _ o ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j)) := by
      rw [hΨ, GlobalTheory.FiniteFock.pureTensorO_one, one_mul, one_mul]
    have hov := vac_mono (· ∈ v.gP) (hΨ1 ▸ hv.Ψ j hj 1 1 (one_mem _) 1 (one_mem _))
    have honz : comb f.c.ψ _ _ o ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j)) ≠ 0 := by
      intro h0
      obtain ⟨P, hP⟩ := hVT.nz.1 j hj
      apply hP
      rw [hΨ, one_mul, one_mul]
      have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D (pk W).ψ (pk W).θ _ _ _ _ _ hWe hinf (cart ((pk W).MY j)) (cart ((pk W).MY j)) (onb ((pk W).MY j)) (onb ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY (j + 1))) (onb ((pk W).MY (j + 1))) (f.g.b j) (f.g.b (j + 1))
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.one_mul]) _ hvth P
      rw [hfin.2, comb_pureTensorO hstd hinf _ _ _ _ (fin _ o hstd ho) (hWe.om_pres _ _ hvth), h0, pureTensorO_zero]
    have hg0nz : (pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j) ≠ 0 := fun h0 =>
      honz (by rw [h0]; exact comb_zero _)
    obtain ⟨c, hc⟩ := scalar D f.c.ψ _ _ M (v.N j) M' (v.N (j + 1)) v.gP o o' _ hstd hM hM' (hv.sd j (by omega))
      (hv.sd (j + 1) hj) ho ho' hg0 hov ho'v (ho'nz hg0nz)
    have hc0 : c ≠ 0 := fun h0 => honz (by rw [hc, h0, zero_smul])
    refine ⟨κ / c, div_ne_zero hκ hc0, fun d hd P a ha a' ha' => ?_⟩
    have hbase : (pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((pk W).vac j)) =
        (κ / c) • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j))) := by
      rw [hdat d hd, hc, comb_smul, smul_smul, div_mul_cancel₀ _ hc0]
    rw [hΨ P a a']
    exact fock hinf hWe _ _ _ _ (fin _ d hstd hd.1) (fin _ o hstd ho) (fin _ _ hstd (hv.atG j).1) hvth hb hb' hbase P ha ha'
  have top : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ c : ℂ, c ≠ 0 ∧ ∀ d, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) d →
      ∀ P, omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D (j + 1)) D.sp.X'
        (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P)) =
        c • comb f.c.ψ _ _ (v.eGT j h) (v.ΨT j h P) := by
    intro j h
    by_cases hex : ∃ d₀, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) d₀
    swap
    · exact ⟨1, one_ne_zero, fun d hd => absurd ⟨d, hd⟩ hex⟩
    obtain ⟨d₀, hd₀⟩ := hex
    obtain ⟨M, M', o', hM, hM', ho', hg0, ho'v, ho'nz, κ, hκ, hdat⟩ := datum_top D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT
      n G pl hGP hGR j h d₀ hd₀
    obtain ⟨o, ho, hΨ⟩ := hVT.ΨT j h
    have hstd : IsStdChar D (pk W).ψ (-1) := hd₀.2.1.1
    have hinf : IsInfFam (pk W).θ := hd₀.2.1.2.inf
    have hvth : IsThetaFunO (pk W).ψ _ _ (vacT (pk W) j h) := hd₀.2.1.2.theta
    obtain ⟨χS, χT, hWe⟩ := weil_top W j h
    have hb : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
    have hb' : f.g.bT ∈ GfC _ := hVT.bT.1 ▸ hv.bT
    have hΨ1 : v.ΨT j h 1 = comb f.c.ψ _ _ o (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h)) := by
      rw [hΨ, GlobalTheory.FiniteFock.pureTensorO_one]
    have hov := vac_mono (· ∈ v.gP) (hΨ1 ▸ hv.ΨT j h 1)
    have honz : comb f.c.ψ _ _ o (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h)) ≠ 0 := by
      intro h0
      obtain ⟨P, hP⟩ := hVT.nz.2 j h
      apply hP
      rw [hΨ]
      have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D (pk W).ψ (pk W).θ _ _ _ _ _ hWe hinf (cart ((pk W).MY (j + 1))) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY (j + 1))) (onb ((pk W).MY (j + 1))) (cart (pk W).MX) (cart (pk W).MX) (onb (pk W).MX) (onb (pk W).MX) (f.g.b (j + 1)) f.g.bT
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.one_mul]) _ hvth P
      rw [hfin.2, comb_pureTensorO hstd hinf _ _ _ _ (fin _ o hstd ho) (hWe.om_pres _ _ hvth), h0, pureTensorO_zero]
    have hg0nz : omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h) ≠ 0 := fun h0 =>
      honz (by rw [h0]; exact comb_zero _)
    obtain ⟨c, hc⟩ := scalar D f.c.ψ _ _ M (v.N (j + 1)) M' v.NT v.gP o o' _ hstd hM hM' (hv.sd (j + 1) (by omega))
      hv.sdT ho ho' hg0 hov ho'v (ho'nz hg0nz)
    have hc0 : c ≠ 0 := fun h0 => honz (by rw [hc, h0, zero_smul])
    refine ⟨κ / c, div_ne_zero hκ hc0, fun d hd P => ?_⟩
    have hbase : omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (pk W) j h)) =
        (κ / c) • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ o (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h))) := by
      rw [hdat d hd, hc, comb_smul, smul_smul, div_mul_cancel₀ _ hc0]
    rw [hΨ P]
    have := fock hinf hWe (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (fin _ d hstd hd.1) (fin _ o hstd ho) (fin _ _ hstd ((hv.atG j).2.2 h)) hvth hb hb' hbase P
      (one_mem (GinfC _)) (one_mem (GinfC _))
    simpa only [one_mul] using this
  choose cm hcm using mid
  choose ct hct using top
  let s : ℕ → ℂ := fun i => if hi : i + 1 < D.R.m then cm i hi else
    match i with
    | 0 => 1
    | k + 1 => if hk : k + 2 * 0 + 2 = D.R.m then ct k hk else 1
  refine ⟨s, fun i => ?_, fun j hj d hd P a ha a' ha' => ?_, fun j h d hd P => ?_⟩
  · show (if hi : i + 1 < D.R.m then cm i hi else
      (match i with
      | 0 => 1
      | k + 1 => if hk : k + 2 * 0 + 2 = D.R.m then ct k hk else 1)) ≠ 0
    split_ifs with hi
    · exact (hcm i hi).1
    · split
      · exact one_ne_zero
      · split_ifs with hk
        · exact (hct _ hk).1
        · exact one_ne_zero
  · have hs : s j = cm j hj := dif_pos hj
    rw [hs]
    exact (hcm j hj).2 d hd P a ha a' ha'
  · have hs : s (j + 1) = ct j h := by
      show (if hi : j + 1 + 1 < D.R.m then cm (j + 1) hi else if hk : j + 2 * 0 + 2 = D.R.m then ct j hk else 1) = ct j h
      rw [dif_neg (by omega), dif_pos h]
    rw [hs]
    exact (hct j h).2 d hd P

end GlobalTheory.GVecAt
