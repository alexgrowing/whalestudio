import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.EvFinIdemSelf
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.ArchSlice
import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PureSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF
open scoped Classical

def evIH (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

section Op
variable {κ : Type} [Fintype κ]

theorem opF_eq {v : Pl F} {S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {φ φ₁ : (κ → Fv F v) → ℂ} (h0 : φ ∈ SB _) (h1 : φ₁ ∈ SB _)
    (h : Acts (evFin F v) S φ φ₁) : opF v S φ = φ₁ := by
  have ex : ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) S φ φ₁ := ⟨φ₁, h1, h⟩
  rw [opF, dif_pos ex]
  exact GlobalTheory.TensUniq.eq_of_tens_eq v φ _ _ h0 fun r hr => (ex.choose_spec.2 r hr).symm.trans (h r hr)

theorem opI_eq (hU : ArchUniq) {S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ} (h : Acts (evI F) S f f₁) : opI S f = f₁ := by
  have ex : ∃ f₁ : SInf F κ, Acts (evI F) S f f₁ := ⟨f₁, h⟩
  rw [opI, dif_pos ex]
  exact (hU F κ f _ _).1 S ex.choose_spec h

theorem acts_comp {R : Type} [Zero R] {ev : AF F → R} {S S' : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {φ φ₁ φ₂ : (κ → R) → ℂ}
    (hS : ∀ Φ ∈ schA F κ, S Φ ∈ schA F κ) (h : Acts ev S φ φ₁) (h' : Acts ev S' φ₁ φ₂) : Acts ev (fun Φ => S' (S Φ)) φ φ₂ := fun r hr => by
  show S' (S _) = _
  rw [h r hr]
  exact h' r ⟨hr.1, h r hr ▸ hS _ hr.2⟩

theorem pure_real {S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ} (h : Acts (evI F) S f f₁) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ SB _) (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    S (pure f φ) = pure f₁ φ := by
  refine h (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  refine finprod_congr fun v => congrArg _ (funext fun i => ?_)
  have := congrFun (hz (idem F v) (evI_idem v)) i
  have h2 := congrArg (evFin F v) this
  rw [Pi.smul_apply, smul_eq_mul, map_mul, evFin_idem_self, one_mul, Pi.zero_apply, map_zero] at h2
  rw [Pi.add_apply, map_add, h2, add_zero]

theorem proj_adm (x : κ → AF F) : (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := fun g _ =>
  ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => by
    show f _ * g _ = g _ * f _
    ring⟩

theorem pure_zero (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) (v : Pl F) (h : φ v = 0) : pure f φ = 0 := by
  funext x
  show f _ * ∏ᶠ u, _ = 0
  rw [finprod_eq_zero _ v (by rw [h]; rfl) (GlobalTheory.PureFactor.mulSupport_finite φ hstd x), mul_zero]

theorem acts_rho_fin {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} (co : Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (v : Pl F) (w : W) (φ : (κ → Fv F v) → ℂ) :
    Acts (evFin F v) (co.rho ψ (idem F v • w)) φ (schr (PositivityTheory.KCo.psiV ψ v) (PositivityTheory.KCo.locW v (co.e w)) φ) := by
  have h := GlobalTheory.VacBridge.rho_acts_locCo co ψ v _ (at_idem v w) φ
  have e : GlobalTheory.LatVac.locCo co v (idem F v • w) = PositivityTheory.KCo.locW v (co.e w) := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show evFin F v ((co.e (idem F v • w)).1 i) = evFin F v ((co.e w).1 i)
      rw [map_smul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, map_mul, evFin_idem_self, one_mul]
    · show evFin F v ((co.e (idem F v • w)).2 i) = evFin F v ((co.e w).2 i)
      rw [map_smul, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, evFin_idem_self, one_mul]
  rw [e] at h
  convert h using 1
  funext x
  simp only [schr, invOf_eq_inv]
  rfl

theorem acts_rho_inf {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} (co : Darboux B κ) {ψ : AddChar (AF F) ℂ}
    (hψ : IsStd ψ) (w : W) {f g : SInf F κ} (hg : PositivityTheory.Mix.IsTr (co.e w) f g) : Acts (evI F) (co.rho ψ (realAd F 1 • w)) f g := by
  intro r hr
  funext x
  have hat : ∀ y : κ → AF F, At (evI F) (realAd F 1 • y) := fun y => at_real y
  have hev : ∀ a : AF F, evI F (realAd F 1 * a) = evI F a := fun a => by rw [evI_mul, evI_real, one_mul]
  show ψ (x ⬝ᵥ (co.e (realAd F 1 • w)).2 + ⅟(2 : AF F) * ((co.e (realAd F 1 • w)).1 ⬝ᵥ (co.e (realAd F 1 • w)).2)) *
    (f (fun i => evI F ((x + (co.e (realAd F 1 • w)).1) i)) * r (x + (co.e (realAd F 1 • w)).1)) = g _ * r x
  rw [map_smul, Prod.smul_fst, Prod.smul_snd, hr.1 x _ (hat _), hg, ← mul_assoc]
  congr 1
  have e : x ⬝ᵥ (realAd F 1 • (co.e w).2) + ⅟(2 : AF F) * ((realAd F 1 • (co.e w).1) ⬝ᵥ (realAd F 1 • (co.e w).2)) =
      realAd F 1 • (x ⬝ᵥ (co.e w).2 + ⅟(2 : AF F) * ((co.e w).1 ⬝ᵥ (co.e w).2)) := by
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
    linear_combination (⅟(2 : AF F) * ((co.e w).1 ⬝ᵥ (co.e w).2)) * (real_mul_self (F := F))
  rw [e, hψ.2.2 _ (at_real _), smul_eq_mul, hev]
  congr 1
  · congr 2
    have h2 : evI F (⅟(2 : AF F)) = algebraMap ℝ _ (1 / 2 : ℝ) := by
      have h3 : evI F (⅟(2 : AF F)) * 2 = 1 := by
        have := congrArg (evI F) (invOf_mul_self (2 : AF F))
        rw [evI_mul, evI_one] at this
        rw [← this]; congr 1
        exact (map_ofNat (evIH F) 2).symm
      have h4 : algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2 : ℝ) * 2 = 1 := by
        rw [← map_ofNat (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2, ← map_mul]; norm_num
      calc _ = evI F (⅟(2 : AF F)) * (algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2 : ℝ) * 2) := by rw [h4, mul_one]
        _ = algebraMap ℝ _ (1 / 2 : ℝ) * (evI F (⅟(2 : AF F)) * 2) := by ring
        _ = _ := by rw [h3, mul_one]
    have hd : ∀ a b : κ → AF F, evI F (a ⬝ᵥ b) = (fun i => evI F (a i)) ⬝ᵥ fun i => evI F (b i) := fun a b => by
      show evIH F _ = _
      simp only [dotProduct, map_sum, map_mul]; rfl
    rw [evI_add, evI_mul, h2, map_add, ← Algebra.smul_def, map_smul, hd, hd]
    simp only [PositivityTheory.Mix.beta, smul_eq_mul]
    push_cast
    rw [one_div, inv_mul_eq_div]
    rfl
  · congr 1
    funext i
    rw [Pi.add_apply, evI_add, Pi.smul_apply, smul_eq_mul, hev]
    rfl

end Op

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem om_pres {B : Base F E} {M : Model σ X W} {χX χW om r s r' s'} (hP : IsPair B M χX χW om r s r' s') (g : UA σ X.J) :
    ∀ Φ ∈ schA F _, om (g, 1) Φ ∈ schA F _ := by
  obtain ⟨d', -, h, -⟩ := hP.weil.2.1
  exact h.pres g

theorem om_pure (hA : ActsEx) (hV : VacFixX) {B : Base F E} {M : Model σ X W} {χX χW om r s r' s'} (hP : IsPair B M χX χW om r s r' s')
    {K : Subgroup (UA σ X.J)} (hK : IsStab B K) (T : Finset (Pl F)) (u1 : UnrOff χX (T : Set (Pl F))) (u2 : UnrOff χW (T : Set (Pl F)))
    (f f₁ : SInf F _) (φ) (hSB : ∀ v, φ v ∈ SB _) (hT : ∀ v ∉ T, φ v = M.vac v) {k} (hk : k ∈ K)
    (h1 : Acts (evI F) (om (partU real_mul_self k, 1)) f f₁) :
    ∃ φ₁ : ∀ v : Pl F, Fl F v n d, (∀ v, φ₁ v ∈ SB _ ∧ Acts (evFin F v) (om (partU (idem_mul_self v) k, 1)) (φ v) (φ₁ v)) ∧
      (∀ v ∉ T, φ₁ v = M.vac v) ∧ om (k, 1) (pure f φ) = pure f₁ φ₁ := by
  have one : ∀ v, (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := fun v u _ => by
    show u • (mat (1 : UA σ W.J) - 1) = 0
    rw [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, smul_zero]
  have ex := fun v => (hA F E σ B n d X W M χX χW om r s r' s' hP v).1 _ (partU_idem_mem v k) 1 (one v) (φ v) (hSB v)
  choose φ₁ h₁ hu using ex
  have hvac : ∀ v ∉ T, φ₁ v = M.vac v := fun v hv => by
    refine (hu v _ ⟨(hP.good.vac v).1, ?_⟩).symm
    rw [hT v hv]
    exact hV F E σ B n d X W M χX χW om r s r' s' hP K hK v
      (fun w hw => ⟨u1 w fun h => hv (hw ▸ h), u2 w fun h => hv (hw ▸ h)⟩) _ (partU_mem_kAt hK hk v)
  have std : ∀ ξ : ∀ v : Pl F, Fl F v n d, (∀ v ∉ T, ξ v = M.vac v) →
      ∀ᶠ v in cofinite, ξ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun ξ h => by
    filter_upwards [hP.good.std, T.eventually_cofinite_notMem] with v a b using (h v b).trans a
  refine ⟨φ₁, h₁, hvac, ?_⟩
  have step : ∀ S : Finset (Pl F), om (partU (aS_mul_self S) k, 1) (pure f φ) = pure f₁ fun v => if v ∈ S then φ₁ v else φ v := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : partU (aS_mul_self ∅) k = partU real_mul_self k := mat_inj (by rw [mat_partU, mat_partU, aS, Finset.sum_empty, add_zero])
      rw [this, pure_real h1 φ hSB (std φ hT)]
      simp
    | insert v S hv ih =>
      have e : partU (aS_mul_self (insert v S)) k = partU (idem_mul_self v) k * partU (aS_mul_self S) k := by
        rw [← partU_add (idem_mul_self v) (aS_mul_self S) (idem_mul_aS hv) (aS_insert hv ▸ aS_mul_self (insert v S))]
        exact mat_inj (by rw [mat_partU, mat_partU, aS_insert hv])
      have e2 : ((partU (idem_mul_self v) k * partU (aS_mul_self S) k, 1) : UA σ X.J × UA σ W.J) =
          (partU (idem_mul_self v) k, 1) * (partU (aS_mul_self S) k, 1) := by simp
      rw [e, e2, map_mul, Module.End.mul_apply, ih]
      have := (pureAct F _ v (om (partU (idem_mul_self v) k, 1)) f₁ (fun v => if v ∈ S then φ₁ v else φ v)
        (fun u => by split_ifs; exacts [(h₁ u).1, hSB u])
        (std _ fun u hu => by split_ifs; exacts [hvac u hu, hT u hu])).2.2 (φ₁ v) (by
          simp only [if_neg hv]; exact (h₁ v).2)
      rw [this]
      congr 1
      funext u
      rcases eq_or_ne u v with rfl | h
      · simp
      · rw [Function.update_of_ne h]; simp [h]
  funext x
  have c := (hP.weil.2.2 _ (proj_adm x) _ (GlobalTheory.TensUniq.pure_mem_schA f φ hSB (std φ hT))).continuousAt (x := (k, 1))
  have t := c.tendsto.comp ((tendsto_partU k).prodMk_nhds tendsto_const_nhds)
  refine tendsto_nhds_unique t (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop T] with S hS
  show _ = om (partU (aS_mul_self S) k, 1) (pure f φ) x
  rw [step]
  congr 2
  funext v
  split_ifs with h
  · rfl
  · rw [hvac v fun h' => h (hS h'), hT v fun h' => h (hS h')]

def VacShift : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) e u ei ev, Cfg B M M₁ H H' e u → IsEvLoc M M₁ e ei ev →
    ∀ v : Pl F, ∀ l, ev v (opF v (M.co.rho B.ψ (idem F v • u l)) (M.vac v)) = if idem F v • u l ∈ latAtV X W v then M₁.vac v else 0

theorem part_shift {B : Base F E} {n₁ d₁ : ℕ} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H H' e u}
    (h : Cfg B M M₁ H H' e u) {a : AF F} (ha : a * a = a) {l l' : (AE F E)ˣ} (hl : IsPart a l l') : a • u l' = a • u l := by
  have e0 : a * (1 - a) = 0 := by rw [mul_sub, mul_one, ha, sub_self]
  have e1 : a • (l' : AE F E) = a • (l : AE F E) := by rw [hl, smul_add, smul_smul, smul_smul, ha, e0, zero_smul, add_zero]
  rcases h.ev with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · rw [shiftA, shiftA, ← smul_assoc, ← smul_assoc, e1]
  · rw [shiftB, shiftB, ← smul_assoc, ← smul_assoc, ← map_smul, ← map_smul, e1]

theorem pureFac_of (hA : ActsEx) (hO : ArchOp) (hU : ArchUniq) (hV : VacFixX) (hS : VacShift) (hPS : PositivityTheory.Mix.PureSt) : PureFac := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev hC hE K hK χX χW om r s r' s' hP T u1 u2 f φ hSB hT k hk l ki kf li lf
    hki hkf hli hlf
  obtain rfl := hki.eq real_mul_self
  have hkf' : ∀ v, kf v = partU (idem_mul_self v) k := fun v => (hkf v).eq _
  have one : (1 : UA σ W.J) ∈ UAt σ W (evI F) := fun u _ => by
    show u • (mat (1 : UA σ W.J) - 1) = 0
    rw [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, smul_zero]
  obtain ⟨Ti, hTi, -⟩ := hO F E σ B n d X W M χX χW om r s r' s' hP _ (partU_real_mem k) 1 one
  obtain ⟨φ₁, h₁, hvac, eq⟩ := om_pure hA hV hP hK T u1 u2 f (Ti f) φ hSB hT hk (hTi.2 f)
  have std : ∀ᶠ v in cofinite, φ₁ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hP.good.std, T.eventually_cofinite_notMem] with v a b using (hvac v b).trans a
  obtain ⟨⟨g, hg⟩, hp⟩ := hPS F B.ψ hC.base.std _ (M.co.e (u l)) (Ti f)
  obtain ⟨std2, eq2⟩ := hp φ₁ std
  set φ₂ : ∀ v : Pl F, Fl F v n d := fun v => schr (PositivityTheory.KCo.psiV B.ψ v) (PositivityTheory.KCo.locW v (M.co.e (u l))) (φ₁ v) with hφ₂
  have a2 : ∀ v, Acts (evFin F v) (M.co.rho B.ψ (idem F v • u l)) (φ₁ v) (φ₂ v) := fun v => acts_rho_fin M.co B.ψ v (u l) (φ₁ v)
  have sb2 : ∀ v, φ₂ v ∈ SB _ := fun v => by
    obtain ⟨ξ, hξ, -⟩ := (hA F E σ B n d X W M χX χW om r s r' s' hP v).2.1 _ (at_idem v (u l)) (φ₁ v) (h₁ v).1
    rw [GlobalTheory.TensUniq.eq_of_tens_eq v (φ₁ v) (φ₂ v) ξ (h₁ v).1 fun r hr => (a2 v r hr).symm.trans (hξ.2 r hr)]
    exact hξ.1
  have ev2 : ∀ᶠ v in cofinite, φ₂ v = M.vac v := by
    filter_upwards [hP.good.std, std2] with v a b using b.trans a.symm
  have e3 : e (M.co.rho B.ψ (u l) (om (k, 1) (pure f φ))) = pure (ei g) fun v => ev v (φ₂ v) := by
    rw [eq, ← hE.pure g φ₂ sb2 ev2]
    exact congrArg e (eq2 g hg)
  have off : ∀ v ∉ T, ev v (φ₂ v) = if idem F v • u l ∈ latAtV X W v then M₁.vac v else 0 := fun v hv => by
    rw [← hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev hC hE v l,
      opF_eq (hP.good.vac v).1 (sb2 v) (hvac v hv ▸ a2 v)]
  rw [e3]
  split_ifs with hall
  · rw [one_smul, part_shift hC real_mul_self hli,
      opI_eq hU (acts_comp (om_pres hP _) (hTi.2 f) (acts_rho_inf M.co hC.base.std (u l) hg))]
    congr 1
    funext v
    split_ifs with hv
    · rw [part_shift hC (idem_mul_self v) (hlf v), hkf' v, opF_eq (hSB v) (sb2 v) (acts_comp (om_pres hP _) (h₁ v).2 (a2 v))]
    · rw [off v hv, if_pos (hall v hv)]
  · push Not at hall
    obtain ⟨v, hv, hn⟩ := hall
    rw [zero_smul]
    refine pure_zero _ _ ?_ v (by rw [off v hv, if_neg hn])
    filter_upwards [ev2, hC.good₁.std] with t a b
    rw [a, (hE.vac t).1, b]

end PositivityTheory.ThKG.Loc.Cone

end
