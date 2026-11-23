import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLocallyConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientTendstoZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientIdeleScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCharacterAnnihilatorCompactStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF.ShiftSupp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open scoped Classical in

theorem locPart_inv (B : Base F E) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hM : M.IsGood B.ψ) {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {ei ev}
    (hL : IsLocPart M M₁ e ei ev) (v : Pl F) (T : Fn F n d → Fn F n d)
    (hT : ∀ Φ ∈ schA F (Fin n × Fin d), e (T Φ) = e Φ) {φ φ₁ : (Fin n × Fin d → Fv F v) → ℂ}
    (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) (hφ₁ : φ₁ ∈ SB (Fin n × Fin d → Fv F v))
    (hA : Acts (evFin F v) T φ φ₁) : ev v φ₁ = ev v φ := by
  obtain ⟨hei, hev, hloc⟩ := hL
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  obtain ⟨y, hy⟩ : ∃ y, ei f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)

  let pt : (Fin n₁ × Fin d₁ → Fv F v) → (Fin n₁ × Fin d₁ → AF F) := fun t i =>
    GlobalTheory.HeisSchA.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) 0 + GlobalTheory.LatVac.liftV v (t i)
  have hI : ∀ t, (fun i => evI F (pt t i)) = y := fun t => funext fun i => by
    change InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i) + 0) = y i
    rw [add_zero, RingEquiv.apply_symm_apply]
  have h0 : ∀ w a, evFin F w (GlobalTheory.HeisSchA.mk a 0) = 0 := fun w a => map_zero (evalV F w)
  have hv : ∀ t, (fun i => evFin F v (pt t i)) = t := fun t => funext fun i => by
    simp only [pt, map_add, h0, GlobalTheory.LatVac.evFin_liftV, zero_add]
  have hw : ∀ t w, w ≠ v → (fun i => evFin F w (pt t i)) = 0 := fun t w hw => funext fun i => by
    simp only [pt, map_add, h0, zero_add]
    exact evalV_singleFin_ne hw _
  have hupd : ∀ χ : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ, (∀ w, χ w ∈ SB _) → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∀ w, Function.update χ v φ w ∈ SB _ := by
    intro χ hχ φ hφ w
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact hφ
    · rw [Function.update_of_ne hw]
      exact hχ w
  have hcof : ∀ χ : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ, (∀ᶠ w in cofinite, χ w = M.vac w) →
      ∀ φ, ∀ᶠ w in cofinite, Function.update χ v φ w = M.vac w := by
    intro χ hχ φ
    filter_upwards [hχ, Filter.eventually_cofinite_ne v] with w h1 hw
    rw [Function.update_of_ne hw, h1]
  have hstd : ∀ χ : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ, (∀ᶠ w in cofinite, χ w = M.vac w) →
      ∀ᶠ w in cofinite, χ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    intro χ hχ
    filter_upwards [hχ, hM.std] with w h1 h2
    rw [h1, h2]

  have hfin : {w | M₁.vac w 0 ≠ 1}.Finite := by
    by_contra hinf
    obtain ⟨r, -, hr⟩ := GlobalTheory.PureFactor.exists_rest_factor v f M.vac hM.std
    have h1 := congrFun (hloc f _ (hupd M.vac (fun w => (hM.vac w).1) 0 (zero_mem _))
      (hcof M.vac (Eventually.of_forall fun _ => rfl) 0)) (pt 0)
    have hz : tens (evFin F v) (0 : (Fin n × Fin d → Fv F v) → ℂ) r = 0 := funext fun x => zero_mul _
    rw [← hr, hz, map_zero, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hI, finprod_of_infinite_mulSupport, mul_one] at h1
    · exact hy h1.symm
    · refine Set.Infinite.mono ?_ (Set.Infinite.diff hinf (Set.finite_singleton v))
      rintro w ⟨h2, h3⟩
      have h3' : w ≠ v := h3
      rw [Function.mem_mulSupport, Function.update_of_ne h3', (hev w).1, hw 0 w h3']
      exact h2

  have hex : ∀ w, ∃ χ ∈ SB (Fin n × Fin d → Fv F w), ev w χ 0 = 1 ∧ (M₁.vac w 0 = 1 → χ = M.vac w) := by
    intro w
    by_cases h : M₁.vac w 0 = 1
    · exact ⟨M.vac w, (hM.vac w).1, by rw [(hev w).1, h], fun _ => rfl⟩
    · have hm := GlobalTheory.StdVacuum.indicator_mem_SB (κ := Fin n₁ × Fin d₁) w
      rw [← (hev w).2] at hm
      obtain ⟨χ, hχ, hχe⟩ := hm
      refine ⟨χ, hχ, ?_, fun h' => absurd h' h⟩
      rw [hχe, Set.indicator_of_mem (by intro i; exact zero_mem _)]
      rfl
  choose χ hχ hχ1 hχv using hex
  have hχc : ∀ᶠ w in cofinite, χ w = M.vac w :=
    (show ∀ᶠ w in cofinite, M₁.vac w 0 = 1 from hfin).mono fun w h => hχv w h
  obtain ⟨r, hr0, hr⟩ := GlobalTheory.PureFactor.exists_rest_factor v f χ (hstd χ hχc)
  have hRest : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ r := fun φ hφ =>
    ⟨hr0, by
      rw [hr φ]
      exact GlobalTheory.TensUniq.pure_mem_schA f _ (hupd χ hχ φ hφ) (hstd _ (hcof χ hχc φ))⟩
  have key : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ t, e (tens (evFin F v) φ r) (pt t) = ei f y * ev v φ t := by
    intro φ hφ t
    rw [hr, hloc f _ (hupd χ hχ φ hφ) (hcof χ hχc φ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hI, finprod_eq_single _ v]
    · rw [Function.update_self, hv]
    · intro w h
      rw [Function.update_of_ne h, hw t w h, hχ1]
  funext t
  refine mul_left_cancel₀ hy ?_
  rw [← key φ₁ hφ₁, ← key φ hφ, ← hA r (hRest φ hφ), hT _ (hRest φ hφ).2]

open scoped GlobalTheory.VacAny in
open GlobalTheory.VanishLoc GlobalTheory.LatVac in

theorem ev_shift_eq_zero_off_compact : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om', IsTriple B G X om om' → ∀ (v : Pl F), ∀ ψ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
    ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ ∀ l ∈ idelesAt E (evFin F v),
      ((GlobalTheory.Doubling.unitFin F E v l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∉ C →
        ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) ψ) = 0 := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' hC e' hE ei ev hL X om om' hT v φ hφ
  have hψ : Continuous B.ψ := hT.base.std.1
  have hψv : Continuous (psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hψ v
  have hne : psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v
  set U : Set (Fv F v ⊗[F] E) := {t | schr (psiAt B.ψ v) (locCo G.M'.co v (uAt H H' v t)) φ = φ} with hUdef
  have hU : U ∈ nhds 0 := (GlobalTheory.T.local_coefficient_tendsto_zero G.M' H H' v).eventually (GlobalTheory.T.schrodinger_locally_constant v (psiAt B.ψ v) hψv φ hφ)
  refine ⟨_, GlobalTheory.T.trace_character_annihilator_compact v (psiAt B.ψ v) hψv hne U hU, fun l _ hl => ?_⟩
  simp only [Set.mem_setOf_eq, not_forall] at hl
  obtain ⟨t, ht, hne1⟩ := hl
  have ht' : schr (psiAt B.ψ v) (locCo G.M'.co v (uAt H H' v t)) φ = φ := ht
  rw [(locOp_rho G.M'.co hψ v (shiftB σ H H' l) hφ).2]
  have hS : schr (psiAt B.ψ v) (locCo G.M'.co v (shiftB σ H H' l)) φ ∈ SB _ :=
    GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ v _ φ hφ
  have h1 := locPart_inv B hT.geo.hM' hL v _ (hE.inv _ (uAt_mem_isoB H H' v t)) hS
    (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ v _ _ hS) (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v _ (at_uAt H H' v t) _)
  rw [schr_comm, ht', map_smul, GlobalTheory.T.local_coefficient_idele_scaling B G G₁ H H' hC X om om' hT v t l] at h1
  have h2 : (psiAt B.ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * compFin F E v l.1)) - 1) •
      ev v (schr (psiAt B.ψ v) (locCo G.M'.co v (shiftB σ H H' l)) φ) = 0 := by
    rw [sub_smul, h1, one_smul, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne1)

end GlobalTheory.ThK.LemF.ShiftSupp

end
