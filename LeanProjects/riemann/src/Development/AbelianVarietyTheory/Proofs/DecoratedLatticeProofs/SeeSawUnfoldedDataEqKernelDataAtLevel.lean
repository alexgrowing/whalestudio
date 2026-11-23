import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacuaStatement
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSawRhs

variable {D : D7}

theorem latO_mono (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : latO S T LS LT P ≤ latO S T LS LT P' := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun v hv' => hv v (fun hp => hv' (h v hp)), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono S T _ _ h hu),
    fun e he u hu hh => hf.2.2 e he u (latO_mono S T _ _ h hu) hh⟩

theorem idAt_mono {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : idAt D P ≤ idAt D P' := by
  intro x hx
  simp only [idAt, Ideal.mem_inf, Submodule.mem_iInf] at hx ⊢
  exact ⟨hx.1, fun w => hx.2 ⟨w.1, fun hw => w.2 (h _ hw)⟩⟩

theorem combAt_mono {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) {S T : HSp D} {c : WO S T →₀ ℂ}
    (hc : CombAt P c) : CombAt P' c := fun u hu i j => idAt_mono h (hc u hu i j)

theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ x ∈ c.support, c x * (ψ (symplOH S T w x) * f (w + x)) := by
  simp [comb, heisO, Finset.sum_apply]

theorem comb_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  funext w
  simp only [comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem biComb_smul (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' c c' (a • C) = a • biComb ψ A S A' c c' C := by
  funext u v
  simp only [biComb, Pi.smul_apply, smul_eq_mul, comb_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem comb_comm2 (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (e : WO A S →₀ ℂ) (d' : WO S A' →₀ ℂ)
    (G : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    comb ψ S A' d' (fun v' => comb ψ A S e (fun u'' => G u'' v') u) v =
      comb ψ A S e (fun u'' => comb ψ S A' d' (G u'') v) u := by
  simp only [comb_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem biComb_biComb (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (d e : WO A S →₀ ℂ) (d' e' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    biComb ψ A S A' d d' (biComb ψ A S A' e e' C) u v =
      comb ψ A S d (comb ψ A S e (fun u'' => comb ψ S A' d' (comb ψ S A' e' (C u'')) v)) u := by
  simp only [biComb]
  congr 1
  funext u'
  exact comb_comm2 ψ A S A' e d' (fun u'' v' => comb ψ S A' e' (C u'') v') u' v

theorem biLift_smul {A S A' : HSp D} (oma : Om A S) (omb : Om S A') (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S A' → ℂ) : biLift oma omb vA vS φ (a • C) = a • biLift oma omb vA vS φ C := by
  funext h₂
  have h1 : ∀ h₀ h₁ v, oma (h₀, h₁) (fun u => a * C u v) 0 = a * oma (h₀, h₁) (fun u => C u v) 0 := by
    intro h₀ h₁ v
    rw [show (fun u => a * C u v) = a • (fun u => C u v) from rfl, map_smul]
    rfl
  have h2 : ∀ h₀ h₁, omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) 0 =
      a * omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0 := by
    intro h₀ h₁
    have e : (fun v => oma (h₀, h₁) (fun u => a * C u v) 0) = a • (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
      funext fun v => h1 h₀ h₁ v
    rw [e, map_smul]
    rfl
  simp only [biLift, Pi.smul_apply, smul_eq_mul, h2]
  simp_rw [show ∀ x y : ℂ, x * (a * y) = a * (x * y) from fun x y => mul_left_comm x a y, integral_const_mul]

theorem theta_comb_left {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} (Y : WO A S → WO S A' → ℂ)
    (hY : ∀ v, IsThetaFunO ψ A S (fun u => Y u v)) (c : WO S A' →₀ ℂ) (v : WO S A') :
    IsThetaFunO ψ A S (fun u => comb ψ S A' c (Y u) v) := by
  classical
  have key : ∀ s : Finset (WO S A'),
      IsThetaFunO ψ A S (fun u => ∑ x ∈ s, c x * (ψ (symplOH S A' v x) * Y u (v + x))) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.sum_empty]
      exact Formalism.IndefR.Fock.CCR.theta_zero ψ A S
    · intro x s hx ih
      have := Formalism.IndefR.Fock.CCR.theta_add_smul ih (hY (v + x)) (c x * ψ (symplOH S A' v x))
      convert this using 1
      funext u
      simp only [Finset.sum_insert hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  simpa only [comb_apply] using key c.support

end GlobalTheory.SeeSawRhs

namespace GlobalTheory.SeeSawRhs

theorem unfolded_eq_kernel_data : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → GValue (t := t) v → TLaw v w → FlatLaw D → BiAct D → ∀ j σ h Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ β, (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂)))) = (v.cG j * w.cT j) • t.two j (fun α => v.Sad j (φ α)) ((v.op j).app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) β := by
  intro D c v t w hc hv _ hF hG hT _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ β
  have hj : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega
  have top : ∀ (P : Pl D → Prop) p, P p → True := fun _ _ _ => trivial
  simp only [Comm.bl]
  rw [hG.1 j σ h Ψ₁ Ψ₂ (vac_mono (top _) h₁) (vac_mono (top _) h₂)]
  obtain ⟨hBV, hTL⟩ := hT.1 j σ h Ψ₁ Ψ₂ (vac_mono (top _) h₁) (vac_mono (top _) h₂)
  simp only [Comm.bl] at hTL
  set X₀ := c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂ with hX₀
  set Y := (v.op j).app c.ψ X₀ with hY
  have hQG : ∀ p, p ∈ w.Q → ¬ p ∈ v.gP := fun p hp => Finset.disjoint_left.mp hF.disjG hp
  have hoff : ∀ p, (p ∈ w.Q ∨ p ∈ v.gP) → p ∉ v.tP := by
    rintro p (hp | hp)
    · exact Finset.disjoint_left.mp hF.disjT hp
    · exact Finset.disjoint_left.mp hv.disj hp
  have prod := fun (S T : HSp D) => (GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D c.ψ hc.std S T (· ∈ w.Q) (· ∈ v.gP) hQG).2.2.2.1
  unfold Tup.two
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  obtain ⟨d₁, hd₁, ed₁⟩ := prod _ _ (w.dQ j α γ) (v.dG j)
    (combAt_mono (fun p hp => Or.inl hp) ((hF.atQ j).2.2 α γ)) (combAt_mono (fun p hp => Or.inr hp) (hv.atG j).2.1)
  obtain ⟨d₂, hd₂, ed₂⟩ := prod _ _ (w.dQ (j + 1) γ β) (v.dG (j + 1))
    (combAt_mono (fun p hp => Or.inl hp) ((hF.atQ (j + 1)).2.2 γ β))
    (combAt_mono (fun p hp => Or.inr hp) (hv.atG (j + 1)).2.1)
  have e1 : biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) X₀) =
      biComb c.ψ _ _ _ d₁ d₂ X₀ := by
    funext u v'
    rw [biComb_biComb]
    simp only [biComb, ed₁, ed₂]
  have e2 : biComb c.ψ _ _ _ d₁ d₂ (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) Y) =
      biComb c.ψ _ _ _ (t.dd j α γ) (t.dd (j + 1) γ β) Y := by
    funext u v'
    rw [biComb_biComb, ed₁]
    have hF' : (fun u'' => comb c.ψ _ _ d₂ (comb c.ψ _ _ (v.dT (j + 1)) (Y u'')) v') =
        fun u'' => comb c.ψ _ _ (t.dd (j + 1) γ β) (Y u'') v' := by
      funext u''
      rw [ed₂, ← hF.dd (j + 1) hj1 γ β _ (hBV.2 u'').1]
    rw [hF', ← hF.dd j hj α γ _ (theta_comb_left Y (fun v'' => (hBV.1 v'').1) _ v')]
    rfl
  rw [biComb_smul, biLift_smul, e1, hTL d₁ d₂ (combAt_mono hoff hd₁) (combAt_mono hoff hd₂) (φ α) (hφ α), e2,
    smul_smul]

end GlobalTheory.SeeSawRhs
