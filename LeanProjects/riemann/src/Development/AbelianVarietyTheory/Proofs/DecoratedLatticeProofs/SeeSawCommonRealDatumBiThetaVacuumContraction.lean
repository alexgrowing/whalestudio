import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumIsTwoVariableThetaFunction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VReal

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem biTheta_add {A S A' : HSp D} {f g : WO A S → WO S A' → ℂ} (hf : IsBiTheta ψ A S A' f)
    (hg : IsBiTheta ψ A S A' g) : IsBiTheta ψ A S A' (f + g) := by
  refine ⟨hf.cont.add hg.cont, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · intro n L L' hL hL' hLf hL'f u v
    exact (hf.smooth n L L' hL hL' hLf hL'f u v).add (hg.smooth n L L' hL hL' hLf hL'f u v)
  · simp only [Pi.add_apply]; rw [hf.quasiL, hg.quasiL]; ring
  · simp only [Pi.add_apply]; rw [hf.quasiR, hg.quasiR]; ring
  · obtain ⟨U, hU, hUf⟩ := hf.levL
    obtain ⟨V, hV, hVf⟩ := hg.levL
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩
    funext u
    have h1 := congrFun (hUf a ha.1 ha' v) u
    have h2 := congrFun (hVf a ha.2 ha' v) u
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  · obtain ⟨U, hU, hUf⟩ := hf.levR
    obtain ⟨V, hV, hVf⟩ := hg.levR
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩
    funext v
    have h1 := congrFun (hUf a ha.1 ha' u) v
    have h2 := congrFun (hVf a ha.2 ha' u) v
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]

theorem biTheta_zero {A S A' : HSp D} : IsBiTheta ψ A S A' 0 := by
  refine ⟨?_, fun n L L' _ _ _ _ u v => ?_, fun γ u v => by simp, fun γ u v => by simp, ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ v => ?_⟩,
    ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ u => ?_⟩⟩
  · simp only [Pi.zero_apply]; exact continuous_const
  · simp only [Pi.zero_apply]; exact contDiff_const
  · funext x; simp [heisO]
  · funext x; simp [heisO]

theorem biTheta_app (hψ : IsStdChar D ψ (-1)) {A S A' : HSp D} (o : BiOp A S A')
    (ho : ∀ i, IsFinComb (o.u i) ∧ IsFinComb (o.u' i)) {C : WO A S → WO S A' → ℂ} (hC : IsBiTheta ψ A S A' C) :
    IsBiTheta ψ A S A' (o.app ψ C) := by
  unfold BiOp.app
  exact Finset.sum_induction _ (IsBiTheta ψ A S A') (fun f g hf hg => biTheta_add hf hg) biTheta_zero
    fun i _ => GlobalTheory.FrComb.biTheta_combL hψ (GlobalTheory.FrComb.biTheta_combR hψ hC (ho i).2) (ho i).1

theorem heisO_add {S T : HSp D} (w : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T w (f + g) = heisO ψ S T w f + heisO ψ S T w g := by
  funext x; simp only [heisO, Pi.add_apply, mul_add]

theorem heisO_zero {S T : HSp D} (w : WO S T) : heisO ψ S T w 0 = 0 := by
  funext x; simp [heisO]

theorem latVac_add {S T : HSp D} {Λ : AddSubgroup (WO S T)} {f g : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) Λ f)
    (hg : IsLatVac (heisO ψ S T) Λ g) : IsLatVac (heisO ψ S T) Λ (f + g) :=
  ⟨fun u hu => by rw [heisO_add, hf.1 u hu, hg.1 u hu],
    fun e he u hu hh => by rw [heisO_add, hf.2 e he u hu hh, hg.2 e he u hu hh]⟩

theorem latVac_zero {S T : HSp D} {Λ : AddSubgroup (WO S T)} : IsLatVac (heisO ψ S T) Λ 0 :=
  ⟨fun u _ => heisO_zero _, fun _ _ u _ _ => heisO_zero u⟩

theorem latVac_sum {S T : HSp D} {Λ : AddSubgroup (WO S T)} {ι : Type} (s : Finset ι) (F : ι → WO S T → ℂ)
    (h : ∀ i ∈ s, IsLatVac (heisO ψ S T) Λ (F i)) : IsLatVac (heisO ψ S T) Λ (∑ i ∈ s, F i) :=
  Finset.sum_induction _ _ (fun _ _ hf hg => latVac_add hf hg) latVac_zero h

def combEnd (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : Module.End ℂ (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext u; simp only [GlobalTheory.FrComb.comb_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext u
    simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

theorem vac_of_true {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {f : WO S T → ℂ}
    (h : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT P f := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun v hv => absurd trivial hv, rest⟩
  unfold Vac IsLatVac at h ⊢
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem vac_union (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (P : Pl D → Prop) (LS : Lat S) (LT : Lat T) (f : WO S T → ℂ)
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (h1 : Vac ψ S T LS LT P f) (h2 : Vac ψ S T LS LT (fun p => ¬ P p) f) :
    Vac ψ S T LS LT (fun _ => True) f := by
  have H := (GlobalTheory.DisjComb.main D ψ hψ S T P (fun p => ¬ P p) (fun p hp hq => hq hp)).2.2.2.2 LS LT f hS hT
  have e : (fun p => P p ∨ ¬ P p) = fun _ => True := funext fun p => propext ⟨fun _ => trivial, fun _ => em _⟩
  have h3 := H.2 ⟨h1, h2⟩
  rwa [e] at h3

theorem real_of (hψ : IsStdChar D ψ (-1)) (P : Pl D → Prop)
    (hcomb : ∀ (S T : HSp D) (e : WO S T →₀ ℂ), CombAt P e → IsFinComb e ∧
      ∀ LS LT f, Vac ψ S T LS LT (fun p => ¬ P p) f → Vac ψ S T LS LT (fun p => ¬ P p) (comb ψ S T e f))
    {A S A' : HSp D} {LA : Lat A} {LS : Lat S} {LA' : Lat A'} (hA : IsSelfDualC A LA) (hS : IsSelfDualC S LS)
    (hA' : IsSelfDualC A' LA') (o : BiOp A S A') (ho : ∀ i, CombAt P (o.u i) ∧ CombAt P (o.u' i))
    {C : WO A S → WO S A' → ℂ} (hC : IsBiTheta ψ A S A' C) (hoff : BiVacAt ψ LA LS LA' (fun p => ¬ P p) C)
    (hon : BiVacAt ψ LA LS LA' P (o.app ψ C)) :
    IsBiTheta ψ A S A' (o.app ψ C) ∧ IsBiVac ψ A S A' LA LS LA' (o.app ψ C) ∧ IsBiSmooth (o.app ψ C) := by
  have hfin : ∀ i, IsFinComb (o.u i) ∧ IsFinComb (o.u' i) :=
    fun i => ⟨(hcomb _ _ _ (ho i).1).1, (hcomb _ _ _ (ho i).2).1⟩
  have hB := biTheta_app hψ o hfin hC
  have hoffApp : BiVacAt ψ LA LS LA' (fun p => ¬ P p) (o.app ψ C) := by
    refine ⟨fun v => ⟨GlobalTheory.FrComb.slice_left hB v, ?_⟩, fun u => ⟨GlobalTheory.FrComb.slice_right hB u, ?_⟩⟩
    · have e : (fun u => o.app ψ C u v) = ∑ i, fun u => biComb ψ A S A' (o.u i) (o.u' i) C u v := by
        funext u; simp only [BiOp.app, Finset.sum_apply]
      rw [e]
      refine latVac_sum _ _ fun i _ => ?_
      have hR := GlobalTheory.FrComb.biTheta_combR hψ hC (hfin i).2
      have hg : Vac ψ A S LA LS (fun p => ¬ P p) (fun u' => comb ψ S A' (o.u' i) (C u') v) :=
        ⟨GlobalTheory.FrComb.slice_left hR v, GlobalTheory.FrComb.latVac_opR (fun v => (hoff.1 v).2) (combEnd ψ S A' (o.u' i)) v⟩
      exact ((hcomb _ _ _ (ho i).1).2 LA LS _ hg).2
    · have e : o.app ψ C u = ∑ i, fun v => biComb ψ A S A' (o.u i) (o.u' i) C u v := by
        funext v; simp only [BiOp.app, Finset.sum_apply]
      rw [e]
      refine latVac_sum _ _ fun i _ => ?_
      exact GlobalTheory.FrComb.latVac_opL (K := fun u' => comb ψ S A' (o.u' i) (C u'))
        (fun u' => ((hcomb _ _ _ (ho i).2).2 LS LA' _ (hoff.2 u')).2) (combEnd ψ A S (o.u i)) u
  have hT : BiVacAt ψ LA LS LA' (fun _ => True) (o.app ψ C) :=
    ⟨fun v => vac_union hψ _ _ P _ _ _ hA hS (hon.1 v) (hoffApp.1 v),
      fun u => vac_union hψ _ _ P _ _ _ hS hA' (hon.2 u) (hoffApp.2 u)⟩
  exact ⟨hB, ⟨hB.cont, fun v => hT.1 v, fun u => hT.2 u⟩, hB.smooth⟩

theorem v_real : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VacLaw (t := t) v → TLaw v w → FlatLaw D → (∀ j σ h Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → IsBiTheta c.ψ _ _ _ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) ∧ c.IsReal j ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂))) ∧ ∀ j h Ψ₁ Ψ₂, WeilOK (t := t) v → Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) Ψ₂ → IsBiTheta c.ψ _ _ _ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) ∧ c.IsReal j ((v.op j).app c.ψ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
  intro D c v t w hc hv ht hV hT hF
  have hψ := hc.std
  have hfl := GlobalTheory.Unf.FlatTheta.flat_isThetaFun D hF c.ψ
  have hcomb : ∀ (S T : HSp D) (e : WO S T →₀ ℂ), CombAt (· ∈ v.tP) e → IsFinComb e ∧
      ∀ LS LT f, Vac c.ψ S T LS LT (fun p => ¬ p ∈ v.tP) f → Vac c.ψ S T LS LT (fun p => ¬ p ∈ v.tP) (comb c.ψ S T e f) :=
    fun S T e he => (GlobalTheory.DisjComb.main D c.ψ hψ S T (· ∈ v.tP) (fun p => ¬ p ∈ v.tP) (fun p hp hq => hq hp)).2.1 e he
  refine ⟨fun j σ h Ψ₁ Ψ₂ h1 h2 => ?_, fun j h Ψ₁ Ψ₂ hW h1 h2 => ?_⟩
  · have hC : IsBiTheta c.ψ _ _ _ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂) :=
      (GlobalTheory.ContrComb.contr_comb_main D c.ψ hψ (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1))
        (c.vL j σ h) (flatBF (t.sBF j (σ + 1) h) Ψ₁) (flatFB (t.sFB j σ h) Ψ₂)
        (hfl.1 (σ + 1) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (t.sBF j (σ + 1) h) Ψ₁ h1.1)
        (hfl.2 σ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sFB j σ h) Ψ₂ h2.1)).1
    have R := real_of hψ (· ∈ v.tP) hcomb (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd (v.op j) (hv.atT j).2 hC (hV.1 j σ h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2))
      (hT.1 j σ h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2)).1
    exact ⟨hC, R.2.1, R.2.2⟩
  · have hC : IsBiTheta c.ψ _ _ _ (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂) :=
      GlobalTheory.LastBiTheta.isBiTheta_lastBi D c.ψ hψ _ _ _ _ _ _ _ (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) (hW.tau j h).2 (flatBF (t.sBF j 0 h) Ψ₁) (fun w => Ψ₂ ((c.jac j 0 h).d.ext0 c.T w))
        (hfl.1 0 (c.B j 0 h) (c.J j 0 h) (t.sBF j 0 h) Ψ₁ h1.1) ((GlobalTheory.WeilSrc.Zero.theta_iff (c.jac j 0 h).d Ψ₂).2 h2.1)
    have R := real_of hψ (· ∈ v.tP) hcomb (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd (v.op j) (hv.atT j).2 hC (hV.2 j h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2))
      (hT.2 j h Ψ₁ Ψ₂ (vac_of_true h1) (vac_of_true h2)).1
    exact ⟨hC, R.2.1, R.2.2⟩

end GlobalTheory.VReal

end
