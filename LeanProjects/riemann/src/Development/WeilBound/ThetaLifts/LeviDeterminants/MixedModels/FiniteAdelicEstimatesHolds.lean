import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PureSt
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.CompFinLiftE
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictAd
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictMod
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PsiUnrOfNotLe

noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.KCo
  GlobalTheory.LatVac

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {v : Pl F}

def liftW (v : Pl F) (y : (κ → Fv F v) × (κ → Fv F v)) : (κ → AF F) × (κ → AF F) :=
  (fun i => liftV v (y.1 i), fun i => liftV v (y.2 i))

omit [Fintype κ] in
theorem locW_smul (a : AF F) (z : (κ → AF F) × (κ → AF F)) : locW v (a • z) = evFin F v a • locW v z :=
  Prod.ext (funext fun _ => map_mul _ _ _) (funext fun _ => map_mul _ _ _)

omit [Fintype κ] in
theorem locW_add (z z' : (κ → AF F) × (κ → AF F)) : locW v (z + z') = locW v z + locW v z' :=
  Prod.ext (funext fun _ => map_add _ _ _) (funext fun _ => map_add _ _ _)

omit [Fintype κ] in
theorem locW_liftW (y : (κ → Fv F v) × (κ → Fv F v)) : locW v (liftW v y) = y :=
  Prod.ext (funext fun _ => evFin_liftV _ _) (funext fun _ => evFin_liftV _ _)

omit [Fintype κ] in
theorem liftW_locW (z : (κ → AF F) × (κ → AF F)) : liftW v (locW v z) = liftV v 1 • z :=
  Prod.ext (funext fun _ => (GlobalTheory.LatVacArith.liftV_one_mul _ _).symm) (funext fun _ => (GlobalTheory.LatVacArith.liftV_one_mul _ _).symm)

def locT (v : Pl F) (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) :
    ((κ → Fv F v) × (κ → Fv F v)) →ₗ[Fv F v] ((κ → Fv F v) × (κ → Fv F v)) where
  toFun y := locW v (T (liftW v y))
  map_add' y y' := by
    rw [← locW_add, ← map_add]
    congr 2
    exact Prod.ext (funext fun _ => map_add _ _ _) (funext fun _ => map_add _ _ _)
  map_smul' c y := by
    have e : liftW v (c • y) = liftV v c • liftW v y := by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
        exact ((mul_liftV _ _).trans (by rw [evFin_liftV]; rfl)).symm
    rw [e, map_smul, locW_smul, evFin_liftV]
    rfl

omit [Fintype κ] in
theorem locT_locW (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) (z) : locT v T (locW v z) = locW v (T z) := by
  change locW v (T (liftW v (locW v z))) = _
  rw [liftW_locW, map_smul, locW_smul, evFin_liftV, one_smul]

def locE (v : Pl F) (S : ((κ → AF F) × (κ → AF F)) ≃ₗ[AF F] ((κ → AF F) × (κ → AF F))) :
    ((κ → Fv F v) × (κ → Fv F v)) ≃ₗ[Fv F v] ((κ → Fv F v) × (κ → Fv F v)) :=
  { locT v S.toLinearMap with
    invFun := locT v S.symm.toLinearMap
    left_inv := fun y => by
      change locT v _ (locW v _) = _
      rw [locT_locW, LinearEquiv.coe_coe, LinearEquiv.coe_coe, S.symm_apply_apply, locW_liftW]
    right_inv := fun y => by
      change locT v _ (locW v _) = _
      rw [locT_locW, LinearEquiv.coe_coe, LinearEquiv.coe_coe, S.apply_symm_apply, locW_liftW] }

def intW (v : Pl F) : Submodule (v.adicCompletionIntegers F) ((κ → Fv F v) × (κ → Fv F v)) where
  carrier := {y | (∀ i, y.1 i ∈ v.adicCompletionIntegers F) ∧ ∀ i, y.2 i ∈ v.adicCompletionIntegers F}
  add_mem' ha hb := ⟨fun i => add_mem (ha.1 i) (hb.1 i), fun i => add_mem (ha.2 i) (hb.2 i)⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  smul_mem' c _ h := ⟨fun i => mul_mem c.2 (h.1 i), fun i => mul_mem c.2 (h.2 i)⟩

theorem locW_int (z : (κ → AF F) × (κ → AF F)) : ∀ᶠ v in cofinite, locW v z ∈ intW v :=
  (eventually_all.2 fun i => (z.1 i).2.2).and (eventually_all.2 fun i => (z.2 i).2.2)

theorem locT_int (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) :
    ∀ᶠ v in cofinite, ∀ y ∈ intW v, locT v T y ∈ intW v := by
  classical
  filter_upwards [eventually_all.2 fun i => locW_int (T (Pi.single i 1, 0)), eventually_all.2 fun i => locW_int (T (0, Pi.single i 1))]
    with v h1 h2 y hy
  have e : liftW v y = ∑ i, liftV v (y.1 i) • ((Pi.single i 1, 0) : (κ → AF F) × (κ → AF F)) +
      ∑ i, liftV v (y.2 i) • ((0, Pi.single i 1) : (κ → AF F) × (κ → AF F)) := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      simp [liftW, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hs : ∀ (c : κ → Fv F v) (z : κ → (κ → AF F) × (κ → AF F)), (∀ i, c i ∈ v.adicCompletionIntegers F) →
      (∀ i, locW v (T (z i)) ∈ intW v) → locW v (T (∑ i, liftV v (c i) • z i)) ∈ intW v := fun c z hc hz => by
    rw [map_sum]
    refine Finset.sum_induction _ (fun t => locW v t ∈ intW v) (fun a b ha hb => locW_add a b ▸ add_mem ha hb) ?_ fun i _ => ?_
    · have z0 : evFin F v 0 ∈ v.adicCompletionIntegers F := by rw [map_zero]; exact zero_mem _
      exact ⟨fun _ => z0, fun _ => z0⟩
    · rw [map_smul, locW_smul, evFin_liftV]
      exact ⟨fun j => mul_mem (hc i) ((hz i).1 j), fun j => mul_mem (hc i) ((hz i).2 j)⟩
  change locW v (T (liftW v y)) ∈ _
  rw [e, map_add, locW_add]
  exact add_mem (hs _ _ hy.1 h1) (hs _ _ hy.2 h2)

theorem schr_std {ψ : AddChar (AF F) ℂ} (hψ : PsiUnr ψ v) (h2 : (2 : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F) {y} (hy : y ∈ intW (κ := κ) v) :
    schr (psiV ψ v) y (Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  funext x
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have h : psiV ψ v (x ⬝ᵥ y.2 + ⅟(2 : Fv F v) * (y.1 ⬝ᵥ y.2)) = 1 := by
      have := (hψ _).2 (show x ⬝ᵥ y.2 + ⅟(2 : Fv F v) * (y.1 ⬝ᵥ y.2) ∈ v.adicCompletionIntegers F from
        add_mem (sum_mem fun i _ => mul_mem (hx i) (hy.2 i))
          (mul_mem (by rwa [invOf_eq_inv]) (sum_mem fun i _ => mul_mem (hy.1 i) (hy.2 i)))) 1 (one_mem _)
      rwa [mul_one] at this
    rw [schr, h, one_mul, Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx),
      Set.indicator_of_mem (show x + y.1 ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        fun i => add_mem (hx i) (hy.1 i))]
    rfl
  · rw [schr, Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx),
      Set.indicator_of_notMem (show x + y.1 ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun h => hx fun i => by
        simpa using sub_mem (h i) (hy.1 i)), mul_zero]

theorem eq_std {ψ : AddChar (AF F) ℂ} (hψ : PsiUnr ψ v) {Φ : (κ → Fv F v) → ℂ} (h : ∀ y ∈ intW v, schr (psiV ψ v) y Φ = Φ) :
    Φ = Φ 0 • Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  classical
  funext x
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have := congrFun (h (x, 0) ⟨hx, fun _ => zero_mem _⟩) 0
    rw [Pi.smul_apply, Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
    simpa [schr] using this
  · rw [Pi.smul_apply, Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx), smul_zero]
    obtain ⟨i, hi⟩ := not_forall.1 hx
    obtain ⟨y, hy, hne⟩ : ∃ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x i * y) ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hi ((hψ _).1 hc)
    have := congrFun (h (0, Pi.single i y) ⟨fun _ => zero_mem _, fun j => by
      by_cases e : j = i
      · subst e; simpa using hy
      · simp [Pi.single_eq_of_ne e]⟩) x
    simp only [schr, dotProduct_single, zero_dotProduct, mul_zero, add_zero, Pi.zero_apply, zero_mul] at this
    exact (mul_left_eq_self₀.1 this).resolve_left hne

theorem finite_adelic_estimates_holds : FinSt := by
  intro F _ _ ψ hψ κ _ S hS
  classical
  have hsy : ∀ (v : Pl F) y y', ((locE v S).symm y).1 ⬝ᵥ ((locE v S).symm y').2 - ((locE v S).symm y').1 ⬝ᵥ ((locE v S).symm y).2 =
      y.1 ⬝ᵥ y'.2 - y'.1 ⬝ᵥ y.2 := fun v y y' => by
    have := congrArg (evFin F v) (hS (S.symm (liftW v y)) (S.symm (liftW v y')))
    rw [S.apply_symm_apply, S.apply_symm_apply] at this
    simp only [dotProduct, map_sub, map_sum, map_mul, liftW, evFin_liftV] at this
    exact this.symm
  choose ι hb hi using fun v : Pl F => Mod.model ((adjoint_statement.psi F ψ hψ).2 v).1 ((adjoint_statement.psi F ψ hψ).2 v).2 (locE v S).symm (hsy v)
  let s : ∀ v : Pl F, (κ → Fv F v) → ℂ := fun v => Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let c : Pl F → ℂ := fun v => if ι v (s v) 0 = 0 then 1 else (ι v (s v) 0)⁻¹
  have hc : ∀ v, c v ≠ 0 := fun v => by
    simp only [c]
    split_ifs with e
    exacts [one_ne_zero, inv_ne_zero e]
  refine ⟨fun v => c v • ι v, fun v => ⟨fun φ hφ => Submodule.smul_mem _ _ ((hb v).1 hφ), fun φ hφ φ' hφ' e =>
    (hb v).2.1 hφ hφ' (smul_right_injective _ (hc v) e), fun Φ hΦ => ?_⟩, fun v w φ hφ => ?_, ?_⟩
  · obtain ⟨φ, hφ, e⟩ := (hb v).2.2 (Submodule.smul_mem _ (c v)⁻¹ hΦ)
    exact ⟨φ, hφ, by rw [LinearMap.smul_apply, e, smul_inv_smul₀ (hc v)]⟩
  · have e : locW v w = (locE v S).symm (locW v (S w)) := by
      change _ = locT v _ _
      rw [locT_locW, LinearEquiv.coe_coe, S.symm_apply_apply]
    rw [LinearMap.smul_apply, LinearMap.smul_apply, e, hi v _ φ hφ]
    funext x
    simp [schr, mul_left_comm]
  · have hd : ∀ᶠ v : Pl F in cofinite, ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal :=
      (Ideal.finite_factors differentIdeal_ne_bot).subset fun v hv => Ideal.dvd_iff_le.2 (not_not.1 hv)
    have h2 : ∀ᶠ v : Pl F in cofinite, evFin F v (algebraMap F (AF F) 2⁻¹) ∈ v.adicCompletionIntegers F :=
      (algebraMap F (AF F) 2⁻¹).2.2
    filter_upwards [hd, h2, locT_int S.symm.toLinearMap] with v e1 e2 e3
    have hu : PsiUnr ψ v := psiUnr_of_not_le hψ v e1
    have e2' : (2 : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F := by
      rwa [AlgHom.commutes, map_inv₀, map_ofNat] at e2
    have h := eq_std hu (Φ := ι v (s v)) fun y hy => by
      rw [← hi v y _ (std_mem_SB v)]
      exact congrArg (ι v) (schr_std hu e2' (e3 y hy))
    have h0 : ι v (s v) 0 ≠ 0 := fun e => by
      rw [e, zero_smul] at h
      have := congrFun ((hb v).2.1 (std_mem_SB v) (zero_mem (SB _)) (h.trans (map_zero _).symm)) 0
      rw [Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        fun i => zero_mem _)] at this
      exact one_ne_zero this
    change c v • ι v (s v) = _
    rw [show c v = (ι v (s v) 0)⁻¹ from if_neg h0, inv_smul_eq_iff₀ h0]
    exact h

end PositivityTheory.Mix
