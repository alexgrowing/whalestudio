import Development.WeilBound.CoreStatements.LocalThetaKernels.LocpairAlg
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictAd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.BoxFunMemSB

noncomputable section

namespace PositivityTheory.ThKH.Locpair

open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK PositivityTheory.ThKH.Locrep
open MeasureTheory
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right tensAt tensAt_tmul compFin_tensAt tensAt_mul_right)

theorem exists_ext {G V : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (T : G → Module.End ℂ V)
    (pres : ∀ g, ∀ φ ∈ S, T g φ ∈ S) (one : ∀ φ ∈ S, T 1 φ = φ) (mul : ∀ g g', ∀ φ ∈ S, T (g * g') φ = T g (T g' φ)) :
    ∃ ρ : G →* Module.End ℂ V, ∀ g, ∀ φ ∈ S, ρ g φ = T g φ := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_extend (LinearMap.id : S →ₗ[ℂ] S)
  let P : Module.End ℂ V := S.subtype ∘ₗ π
  have h1 : ∀ φ ∈ S, P φ = φ := fun φ hφ => congrArg Subtype.val (LinearMap.congr_fun hπ ⟨φ, hφ⟩)
  have h2 : ∀ x, P x ∈ S := fun x => (π x).2
  refine ⟨{ toFun := fun g => T g * P + (1 - P), map_one' := ?_, map_mul' := fun g g' => ?_ }, fun g φ hφ => ?_⟩
  · ext x; simp [one _ (h2 x)]
  · ext x
    simp [mul _ _ _ (h2 x), h1 _ (h2 x), h1 _ (pres _ _ (h2 x))]
  · simp [h1 φ hφ]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem modu_eq (u : (AF F)ˣ) : ((distribHaarChar (AF F) u : NNReal) : ℝ) = GroundTheory.Global.IdeleGroup.ideleModule F u := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := inferInstance
  have : (GroundTheory.Global.adeleMeasure F).Regular := by
    obtain ⟨K⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (AdeleRing (𝓞 F) F)))
    exact Measure.regular_of_isAddLeftInvariant K.isCompact K.interior_nonempty K.isCompact.measure_lt_top.ne
  have h0 := (GroundTheory.Global.IdeleGroup.ideleModule F u).2
  have key : distribHaarChar (AdeleRing (𝓞 F) F) u = NNReal.mk _ h0.le := by
    refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := GroundTheory.Global.adeleMeasure F)
      (s := GroundTheory.Global.fundamentalSet F) ?_ ?_ ?_
    · rw [GroundTheory.Global.adeleMeasure_fundamentalSet]; exact one_ne_zero
    · rw [GroundTheory.Global.adeleMeasure_fundamentalSet]; exact ENNReal.one_ne_top
    · rw [← ENNReal.ofReal_eq_coe_nnreal h0.le]
      exact GroundTheory.Global.adeleMeasure_smul (K := F) u (GroundTheory.Global.fundamentalSet F)
  exact congrArg NNReal.toReal key

theorem modu_single [LocallyCompactSpace (Fv F v)] (u : (AF F)ˣ) (x : (Fv F v)ˣ)
    (h : (u : AF F) = 1 - atPlace v 1 + atPlace v x) :
    ((distribHaarChar (AF F) u : NNReal) : ℝ) = (distribHaarChar (Fv F v) x : NNReal) := by
  rw [modu_eq, GroundTheory.Global.IdeleGroup.ideleModule_apply]
  have h1 : ∀ w, (u : AF F).1 w = 1 := fun w => by
    rw [h]
    change (1 : Ainf F) w - (0 : Ainf F) w + (0 : Ainf F) w = 1
    rw [sub_add_cancel]
    rfl
  have h2 : ∀ w, (u : AF F).2 w =
      1 - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleFin v 1) + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleFin v x) :=
    fun w => by rw [h]; rfl
  have h3 : GroundTheory.Global.IdeleGroup.infiniteModule u = 1 := Finset.prod_eq_one fun w _ => by
    change ‖(u : AF F).1 w‖ ^ _ = 1
    rw [h1, norm_one, one_pow]
  have h4 : GroundTheory.Global.IdeleGroup.finiteModule u = ‖(x : Fv F v)‖ := by
    change ∏ᶠ w, ‖(u : AF F).2 w‖ = _
    rw [finprod_eq_single _ v fun w hw => by rw [h2, evalV_singleFin_ne hw, evalV_singleFin_ne hw, sub_add_cancel, norm_one],
      h2, evalV_singleFin_self, evalV_singleFin_self, sub_self, zero_add]
  rw [h3, h4, one_mul]
  have := GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v (x : Fv F v) x.ne_zero
  rw [Units.mk0_val] at this
  exact (congrArg NNReal.toReal this).symm

section Fun

variable {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

theorem std_ne (h : IsStd ψ) (v : Pl F) : ψ ≠ 1 := fun e => GlobalTheory.PsiNontriv.psiV_ne_one ψ h v (by rw [e]; rfl)

theorem acts_schr (ψ : AddChar (AF F) ℂ) {w : (κ → AF F) × (κ → AF F)} (hw : At (evFin F v) w) (φ : (κ → Fv F v) → ℂ) :
    Acts (evFin F v) (schr ψ w) φ (schr (GlobalTheory.VacAny.psiV ψ v) (locW v w) φ) := fun r hr =>
  GlobalTheory.SchrLoc.schr_tens_of_at ψ v w (fun i a ha => congrFun (congrArg Prod.fst (hw a ha)) i)
    (fun i a ha => congrFun (congrArg Prod.snd (hw a ha)) i) φ r hr.1

omit [Fintype κ] in
theorem tens_inj {r : (κ → AF F) → ℂ} (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) {x₀ : κ → AF F} (h₁ : r x₀ = 1)
    {φ φ' : (κ → Fv F v) → ℂ} (h : tens (evFin F v) φ r = tens (evFin F v) φ' r) : φ = φ' := by
  funext y
  have := congrFun h (putA v x₀ y)
  change φ (evA κ v (putA v x₀ y)) * r (putA v x₀ y) = φ' (evA κ v (putA v x₀ y)) * r (putA v x₀ y) at this
  rwa [ev_put (evA_inA v), inv_putA v hr, h₁, mul_one, mul_one] at this

variable (v) in

def IsLocOm {G : Type} [Monoid G] (om : G →* Module.End ℂ ((κ → AF F) → ℂ))
    (omv : G →* Module.End ℂ ((κ → Fv F v) → ℂ)) : Prop :=
  ∀ g, ∀ φ ∈ SB _, omv g φ ∈ SB _ ∧ Acts (evFin F v) (om g) φ (omv g φ)

theorem exists_locOm (hψ : IsStd ψ) {G : Type} [Monoid G] (om : G →* Module.End ℂ ((κ → AF F) → ℂ))
    (hp : ∀ g, ∀ Φ ∈ schA F κ, om g Φ ∈ schA F κ)
    (ha : ∀ g, ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ om g ∈ (adeleClass F).adm κ)
    (hc : ∀ g, ∀ w : (κ → AF F) × (κ → AF F), atPlace v (1 : Fv F v) • w = 0 →
      ∀ Φ ∈ schA F κ, om g (schr ψ w Φ) = schr ψ w (om g Φ)) : ∃ omv, IsLocOm v om omv := by
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base κ v
  let T : G → Module.End ℂ ((κ → Fv F v) → ℂ) := fun g => res v x₀ ∘ₗ om g ∘ₗ tensL v r₀
  have hT : ∀ g φ, T g φ = res v x₀ (om g (tens (evFin F v) φ r₀)) := fun _ _ => rfl
  have pres : ∀ g, ∀ φ ∈ SB _, T g φ ∈ SB _ := fun g φ hφ => res_mem v x₀ (hp g _ (h₀ φ hφ).2)
  have acts : ∀ g, ∀ φ ∈ SB _, Acts (evFin F v) (om g) φ (T g φ) := fun g φ hφ =>
    acts_res v hψ.1 (std_ne hψ v) hψ.2.1 (hp g) (ha g) (fun w h1 h2 => hc g w (by
      rw [← in_locW, locW, h1, h2, map_zero]; rfl)) h₁ hφ (h₀ φ hφ)
  obtain ⟨ρ, hρ⟩ := exists_ext (SB _) T pres
    (fun φ hφ => (eq_of_acts v h₁ (h₀ φ hφ) (T := om 1) fun r _ => by rw [map_one]; rfl).symm)
    (fun g g' φ hφ => by rw [hT, hT g, ← acts g' φ hφ r₀ (h₀ φ hφ), map_mul]; rfl)
  exact ⟨ρ, fun g φ hφ => by rw [hρ g φ hφ]; exact ⟨pres g φ hφ, acts g φ hφ⟩⟩

omit [Fintype κ] in
theorem putA_zero (x : κ → AF F) : putA v x 0 = (1 - atPlace v (1 : Fv F v)) • x := by
  funext i
  rw [putA_apply, Pi.zero_apply, map_zero, add_zero, Pi.smul_apply, smul_eq_mul, sub_mul, one_mul]

theorem arg_eq (a : κ → Fv F v) (w : (κ → AF F) × (κ → AF F)) :
    inA κ v a ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2 - putA v w.1 0 ⬝ᵥ putA v w.2 0) =
      atPlace v (a ⬝ᵥ (locW v w).2 + ⅟(2 : Fv F v) * ((locW v w).1 ⬝ᵥ (locW v w).2)) := by
  refine extF v ?_ ?_
  · rw [evFin_atPlace, map_add, map_mul, map_sub, ev_dot, ev_dot, ev_dot, evA_inA, ev_put (evA_inA v),
      GlobalTheory.VacAny.evFin_invOf_two, zero_dotProduct, sub_zero]
    rfl
  · have e : ∀ i, awF v (inA κ v a i) = 0 := fun i => awF_at v _
    simp [awF_at, putA_zero, dotProduct, e]

theorem exists_form (Λ : Set ((κ → AF F) × (κ → AF F))) (hΛ : ∀ w ∈ Λ, (1 - atPlace v (1 : Fv F v)) • w ∈ Λ)
    {L : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hL : L ∈ (adeleClass F).adm κ)
    (hi : ∀ w ∈ Λ, ∀ Φ ∈ schA F κ, L (schr ψ w Φ) = L Φ) (h0 : ∃ Φ ∈ schA F κ, L Φ ≠ 0)
    (lv : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (hv : ∀ w ∈ Λ, ∀ φ ∈ SB _, lv (schr (GlobalTheory.VacAny.psiV ψ v) (locW v w) φ) = lv φ) :
    ∃ l ∈ (adeleClass F).adm κ, (∀ w ∈ Λ, ∀ Φ ∈ schA F κ, l (schr ψ w Φ) = l Φ) ∧
      ∃ (r : (κ → AF F) → ℂ) (c : ℂ), c ≠ 0 ∧ (∀ φ ∈ SB _, Rest (evFin F v) φ r) ∧
        ∀ φ, l (tens (evFin F v) φ r) = c * lv φ := by
  obtain ⟨φ₀, hφ₀, y₀, Ψ, hΨ, hne⟩ : ∃ φ₀ ∈ SB (κ → Fv F v), ∃ y₀, ∃ Ψ ∈ schA F κ, L (PA v φ₀ y₀ Ψ) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨Φ, hΦ, hn⟩ := h0
    exact hn (schA_le v (LinearMap.ker L) h hΦ)
  let sl : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ := LinearMap.pi fun y => L ∘ₗ PA v φ₀ y
  have hsl : ∀ φ₁ y₁ Φ, sl (PA v φ₁ y₁ Φ) = L (PA v φ₀ y₁ Φ) • φ₁ := fun φ₁ y₁ Φ => by
    funext y
    change L (PA v φ₀ y (PA v φ₁ y₁ Φ)) = _
    rw [Pm_Pm (evA_inA v), map_smul, smul_eq_mul, mul_comm]
    rfl
  have hm : ∀ Φ ∈ schA F κ, sl Φ ∈ SB _ := fun Φ hΦ => schA_le v ((SB _).comap sl) (fun φ hφ y Ψ _ => by
    rw [Submodule.mem_comap, hsl]; exact Submodule.smul_mem _ _ hφ) hΦ
  refine ⟨lv ∘ₗ sl, admissible_of_integral_conj_le v _ fun φ hφ y => ?_, fun w hw Φ hΦ => ?_, fun x => Ψ (putA v x y₀), L (PA v φ₀ y₀ Ψ), hne,
    fun φ hφ => ⟨fun x z hz => by simp only [putA_add v hz], PA_mem v hφ y₀ hΨ⟩, fun φ => ?_⟩
  · rw [show (lv ∘ₗ sl) ∘ₗ PA v φ y = lv φ • (L ∘ₗ PA v φ₀ y) from LinearMap.ext fun Φ => by
      simp only [LinearMap.comp_apply, hsl, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]]
    intro g hg
    obtain ⟨T, hT⟩ := PA_adm v hφ₀ y hL g hg
    exact ⟨lv φ • T, fun f => congrArg (lv φ • ·) (hT f)⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hv w hw _ (hm Φ hΦ)]
    congr 1
    funext a
    change L (PA v φ₀ a (schr ψ w Φ)) = _
    have e : (putA v w.1 0, putA v w.2 0) = (1 - atPlace v (1 : Fv F v)) • w := by rw [putA_zero, putA_zero]; rfl
    rw [PA_schr, map_smul, arg_eq, e, hi _ (hΛ w hw) _ (PA_mem v hφ₀ _ hΦ)]
    rfl
  · change lv (sl (PA v φ y₀ Ψ)) = _
    rw [hsl, map_smul, smul_eq_mul]

end Fun

end PositivityTheory.ThKH.Locpair
