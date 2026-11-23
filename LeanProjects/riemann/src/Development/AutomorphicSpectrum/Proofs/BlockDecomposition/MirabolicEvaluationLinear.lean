import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair.EvLin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem continuous_uM (n : ℕ) : Continuous (uM (k := k) n) :=
  (continuous_unipIn n).comp continuous_ofAdd

theorem uM_add (n : ℕ) (x y : Fin n → k) : uM n (x + y) = uM n x * uM n y := by
  simp only [uM, ofAdd_add, map_mul]

theorem uM_zero (n : ℕ) : uM (k := k) n 0 = 1 := by
  simp only [uM, ofAdd_zero, map_one]

theorem continuous_coef (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hT : IsSmooth T)
    (v : V) (v' : V') : Continuous (coef T B v v') := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  refine ⟨(fun y => uM n (y - x)) ⁻¹' {g | T g v = v}, (hT v).preimage
    ((continuous_uM n).comp (continuous_id.sub continuous_const)), ?_, fun y hy => ?_⟩
  · simp [uM_zero]
  · have hy' : T (uM n (y - x)) v = v := hy
    have h : uM n y = uM n x * uM n (y - x) := by
      rw [← uM_add, add_sub_cancel]
    simp only [coef, h, map_mul, Module.End.mul_apply, hy']

theorem continuous_wt (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) : Continuous (wt ψ n) :=
  continuous_subtype_val.comp (hψ.comp (continuous_apply _).neg)

variable [MeasurableSpace k] [BorelSpace k]

theorem integrableOn_box (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle)
    (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hψ : Continuous ψ) (hT : IsSmooth T) (v : V) (v' : V') (t : kˣ) :
    IntegrableOn (fun x => wt ψ n x * coef T B v v' x) (box (n + 1) t : Set (Fin (n + 1) → k))
      (piHaar ν (n + 1)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : IsFiniteMeasureOnCompacts (piHaar ν (n + 1)) := by
    unfold piHaar
    infer_instance
  exact ((continuous_wt ψ hψ n).mul (continuous_coef T B hT v v')).continuousOn.integrableOn_compact
    (isCompact_box _ t)

theorem coef_add_left (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v₁ v₂ : V) (v' : V')
    (x : Fin n → k) : coef T B (v₁ + v₂) v' x = coef T B v₁ v' x + coef T B v₂ v' x := by
  simp [coef]

theorem coef_smul_left (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (z : ℂ) (v : V) (v' : V')
    (x : Fin n → k) : coef T B (z • v) v' x = z * coef T B v v' x := by
  simp [coef]

theorem coef_add_right (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v : V) (v₁ v₂ : V')
    (x : Fin n → k) : coef T B v (v₁ + v₂) x = coef T B v v₁ x + coef T B v v₂ x := by
  simp [coef]

theorem coef_smul_right (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (z : ℂ) (v : V) (v' : V')
    (x : Fin n → k) : coef T B v (z • v') x = z * coef T B v v' x := by
  simp [coef]

theorem exists_common_threshold {P Q : kˣ → Prop}
    (hP : ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → P t)
    (hQ : ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → Q t) :
    ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → P t ∧ Q t := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
  · exact ⟨b, fun t ht => ⟨ha t (h.trans ht), hb t ht⟩⟩
  · exact ⟨a, fun t ht => ⟨ha t ht, hb t (h.trans ht)⟩⟩

theorem evVal_bilinear (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle)
    (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hψ : Continuous ψ) (hT : IsSmooth T) :
    (∀ (v₁ v₂ : V) (v' : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v₁ v' A₁ → EvVal ν ψ T B v₂ v' A₂ →
      EvVal ν ψ T B (v₁ + v₂) v' (A₁ + A₂)) ∧
    (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (z • v) v' (z * A)) ∧
    (∀ (v : V) (v₁ v₂ : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v v₁ A₁ → EvVal ν ψ T B v v₂ A₂ →
      EvVal ν ψ T B v (v₁ + v₂) (A₁ + A₂)) ∧
    (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B v (z • v') (z * A)) := by
  refine ⟨fun v₁ v₂ v' A₁ A₂ h₁ h₂ => ?_, fun z v v' A h => ?_, fun v v₁ v₂ A₁ A₂ h₁ h₂ => ?_,
    fun z v v' A h => ?_⟩
  · obtain ⟨t₀, ht₀⟩ := exists_common_threshold h₁ h₂
    refine ⟨t₀, fun t ht => ?_⟩
    obtain ⟨e₁, e₂⟩ := ht₀ t ht
    rw [← e₁, ← e₂]
    simp only [JJ, coef_add_left, mul_add]
    exact integral_add (integrableOn_box ν ψ T B hψ hT v₁ v' t) (integrableOn_box ν ψ T B hψ hT v₂ v' t)
  · obtain ⟨t₀, ht₀⟩ := h
    refine ⟨t₀, fun t ht => ?_⟩
    rw [← ht₀ t ht]
    simp only [JJ, coef_smul_left, mul_left_comm _ z]
    exact integral_const_mul z _
  · obtain ⟨t₀, ht₀⟩ := exists_common_threshold h₁ h₂
    refine ⟨t₀, fun t ht => ?_⟩
    obtain ⟨e₁, e₂⟩ := ht₀ t ht
    rw [← e₁, ← e₂]
    simp only [JJ, coef_add_right, mul_add]
    exact integral_add (integrableOn_box ν ψ T B hψ hT v v₁ t) (integrableOn_box ν ψ T B hψ hT v v₂ t)
  · obtain ⟨t₀, ht₀⟩ := h
    refine ⟨t₀, fun t ht => ?_⟩
    rw [← ht₀ t ht]
    simp only [JJ, coef_smul_right, mul_left_comm _ z]
    exact integral_const_mul z _

theorem evVal_additive_homogeneous : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), Continuous ψ → IsSmooth T → (∀ (v₁ v₂ : V) (v' : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v₁ v' A₁ → EvVal ν ψ T B v₂ v' A₂ → EvVal ν ψ T B (v₁ + v₂) v' (A₁ + A₂)) ∧ (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (z • v) v' (z * A)) ∧ (∀ (v : V) (v₁ v₂ : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v v₁ A₁ → EvVal ν ψ T B v v₂ A₂ → EvVal ν ψ T B v (v₁ + v₂) (A₁ + A₂)) ∧ (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B v (z • v') (z * A)) := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T B hψ hT
  exact evVal_bilinear ν ψ T B hψ hT

end GlobalTheory.CompanionTheory.MirPair.EvLin

end
