import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictDef
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocallyConstantSplitOm
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.IntegrablePair
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.CyclicAndLine
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsInvariantForm
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DualNumberGraphFiltrationIsotropicOfSkew

noncomputable section

open Matrix GlobalTheory.WeilM MeasureTheory Filter Topology ValuativeRel

namespace PositivityTheory.KCo

namespace Mod

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ μ : Type} [Fintype κ] [Fintype μ] {ψ : AddChar k ℂ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem schr_schr (w w' : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : k) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add,
    ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc, add_dotProduct, dotProduct_add]
  congr 2
  have h2 : ⅟(2 : k) * 2 = 1 := invOf_mul_self _
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem schr_zero (φ : (κ → k) → ℂ) : schr ψ 0 φ = φ := by
  funext x
  simp [schr]

theorem schr_mem (hc : Continuous ψ) (w : (κ → k) × (κ → k)) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    schr ψ w φ ∈ SB (κ → k) := by
  have := nonarch_field k
  have hlc := isLocallyConstant_addChar ψ hc
  have h1 : IsLocallyConstant fun x : κ → k => ψ (x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2)) :=
    hlc.comp_continuous ((continuous_id.dotProduct continuous_const).add continuous_const)
  exact ⟨h1.mul (hφ.1.comp_continuous (continuous_id.add continuous_const)),
    (hφ.2.comp_homeomorph (Homeomorph.addRight w.1)).mul_left⟩

omit [Invertible (2 : k)] in
theorem norm_le_one (hc : Continuous ψ) (x : k) : ‖ψ x‖ ≤ 1 := by
  obtain ⟨ψ₀, h₀⟩ := (GlobalTheory.CompanionTheory.VacLoc.GoodInh.exists_goodChar k).1
  obtain ⟨M, hM⟩ := h₀.compact.exists_bound_of_continuousOn (f := fun y : k => ψ (x * y))
    (hc.comp (continuous_const.mul continuous_id)).continuousOn
  by_contra h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (not_le.1 h)
  have := hM (n : k) (natCast_mem _ n)
  rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow] at this
  exact absurd hn (not_lt.2 this)

omit [Invertible (2 : k)] in
theorem norm_one (hc : Continuous ψ) (x : k) : ‖ψ x‖ = 1 := by
  have h1 := norm_le_one hc x
  have h2 := norm_le_one hc (-x)
  have h3 : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel]; simp
  nlinarith [norm_nonneg (ψ x), norm_nonneg (ψ (-x))]

theorem cyc (hc : Continuous ψ) (h1 : ψ ≠ 1) {φ₀ : (κ → k) → ℂ} (h₀ : φ₀ ∈ SB (κ → k)) (hne : φ₀ ≠ 0)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w, l (schr ψ w φ₀) = 0) : ∀ φ ∈ SB (κ → k), l φ = 0 := by
  have := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨u, hu⟩ := (GlobalTheory.CompanionTheory.VacLoc.GoodInh.exists_goodChar k).2 ψ hc (norm_one hc) h1
  let d : Darboux (R := k) (W := (κ → k) × (κ → k)) (fun w w' => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) κ :=
    ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩
  let : MeasurableSpace (κ → k) := borel _
  have : BorelSpace (κ → k) := ⟨rfl⟩
  obtain ⟨S, hS⟩ := GlobalTheory.CompanionTheory.SchrSys.exists_isModel ψ _ u d Measure.addHaar hu inferInstance
  have hcyc := (GlobalTheory.CompanionTheory.VacLoc.ModelLine.cyclic_and_line ψ _ u d _ S ⊥ (fun _ => 1) ⟨φ₀, h₀⟩ ⟨φ₀, h₀⟩ hu hS).1
    (fun h => hne (congrArg Subtype.val h))
  intro φ hφ
  have hle : Submodule.span ℂ (Set.range fun x => S.rho x ⟨φ₀, h₀⟩) ≤ LinearMap.ker (l ∘ₗ (SB (κ → k)).subtype) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    show l _ = 0
    rw [Submodule.subtype_apply, hS.1]
    exact hl w
  have hm : (⟨φ, hφ⟩ : SB (κ → k)) ∈ Submodule.span ℂ (Set.range fun x => S.rho x ⟨φ₀, h₀⟩) := by
    rw [show Submodule.span ℂ (Set.range fun x => S.rho x ⟨φ₀, h₀⟩) = ⊤ from hcyc]
    trivial
  exact hle hm

theorem small (hc : Continuous ψ) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), schr ψ w φ = φ := by
  have := nonarch_field k
  have hlc := isLocallyConstant_addChar ψ hc
  have h1 := eventually_comp_eq (p₀ := (0 : (κ → k) × (κ → k))) (fun p v => v + p.1) (fun p v => v - p.1)
    (by fun_prop) (by fun_prop) (by simp) (by simp) (by simp) hφ
  have hq : Continuous fun q : ((κ → k) × (κ → k)) × (κ → k) => q.2 ⬝ᵥ q.1.2 + ⅟(2 : k) * (q.1.1 ⬝ᵥ q.1.2) :=
    (continuous_snd.dotProduct continuous_fst.snd).add
      (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd))
  have h2 : ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), ∀ v ∈ tsupport φ, ψ (v ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2)) = 1 := by
    refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun v _ => ?_
    filter_upwards [(hlc.comp_continuous hq).eventually_eq (0, v)] with q h
    simpa using h
  filter_upwards [h1, h2] with w a b
  funext v
  rw [schr, a v]
  by_cases hv : v ∈ tsupport φ
  · rw [b v hv, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hv, mul_zero]

theorem model (hc : Continuous ψ) (h1 : ψ ≠ 1) (e : ((μ → k) × (μ → k)) ≃ₗ[k] ((κ → k) × (κ → k)))
    (he : ∀ w w', (e w).1 ⬝ᵥ (e w').2 - (e w').1 ⬝ᵥ (e w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) :
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] ((μ → k) → ℂ), Set.BijOn ι (SB (κ → k) : Set _) (SB (μ → k) : Set _) ∧
      ∀ w, ∀ φ ∈ SB (κ → k), ι (schr ψ (e w) φ) = schr ψ w (ι φ) := by
  classical
  obtain ⟨l, ⟨φ₀, hφ₀, hl₀⟩, hl⟩ := GlobalTheory.CompanionTheory.LagFun.exists_invariant_form k κ ψ hc h1
    (LinearMap.range (e.toLinearMap ∘ₗ LinearMap.inr k _ _)) (by
      rintro _ ⟨z, rfl⟩ _ ⟨z', rfl⟩
      have := he (0, z) (0, z')
      simpa [sub_eq_zero] using this)
  have hl' : ∀ z, ∀ φ ∈ SB (κ → k), l (schr ψ (e (0, z)) φ) = l φ := fun z => hl _ ⟨z, rfl⟩
  let ι : ((κ → k) → ℂ) →ₗ[ℂ] ((μ → k) → ℂ) :=
    { toFun := fun φ y => l (schr ψ (e (y, 0)) φ)
      map_add' := fun φ φ' => funext fun y => by
        rw [Pi.add_apply, ← map_add]
        congr 1
        funext x
        simp [schr, mul_add]
      map_smul' := fun c φ => funext fun y => by
        rw [RingHom.id_apply, Pi.smul_apply, ← map_smul]
        congr 1
        funext x
        simp [schr, mul_left_comm] }
  have hι : ∀ φ y, ι φ y = l (schr ψ (e (y, 0)) φ) := fun _ _ => rfl
  have h0 : ∀ φ, ι φ 0 = l φ := fun φ => by rw [hι, show ((0 : μ → k), (0 : μ → k)) = 0 from rfl, map_zero, schr_zero]
  have hint : ∀ w, ∀ φ ∈ SB (κ → k), ι (schr ψ (e w) φ) = schr ψ w (ι φ) := fun w φ hφ => funext fun y => by
    have a := hl' w.2 _ (schr_mem hc (e (y + w.1, 0)) hφ)
    rw [schr_schr, he, ← map_add, map_smul] at a
    rw [hι, schr_schr, he, ← map_add, map_smul, schr, hι, ← a,
      show ((y, 0) + w : (μ → k) × (μ → k)) = (0, w.2) + (y + w.1, 0) from Prod.ext (by simp) (by simp),
      smul_eq_mul, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    have h2 : ⅟(2 : k) * 2 = 1 := invOf_mul_self _
    simp only [dotProduct_zero, add_dotProduct]
    linear_combination (y ⬝ᵥ w.2) * h2
  have c1 : Continuous fun y : μ → k => e (y, 0) := (e.toLinearMap ∘ₗ LinearMap.inl k _ _).continuous_on_pi
  have c2 : Continuous fun y : μ → k => e (0, y) := (e.toLinearMap ∘ₗ LinearMap.inr k _ _).continuous_on_pi
  have hmaps : ∀ φ ∈ SB (κ → k), ι φ ∈ SB (μ → k) := fun φ hφ => by
    have s1 : ∀ᶠ y in 𝓝 (0 : μ → k), schr ψ (e (y, 0)) φ = φ :=
      (c1.tendsto' 0 0 (map_zero e)).eventually (small hc hφ)
    have s2 : ∀ᶠ y in 𝓝 (0 : μ → k), schr ψ (e (0, y)) φ = φ :=
      (c2.tendsto' 0 0 (map_zero e)).eventually (small hc hφ)
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun y₀ => ?_, ?_⟩
    · have : Tendsto (fun y => y - y₀) (𝓝 y₀) (𝓝 0) := Continuous.tendsto' (by fun_prop) _ _ (sub_self _)
      filter_upwards [this.eventually s1] with y hy
      have := congrFun (hint (y - y₀, 0) φ hφ) y₀
      rw [hy] at this
      simpa [schr] using this.symm
    · obtain ⟨u, hu⟩ := (GlobalTheory.CompanionTheory.VacLoc.GoodInh.exists_goodChar k).2 ψ hc (norm_one hc) h1
      have s3 : ∀ i : μ, ∃ v : kˣ, ∀ o ∈ 𝒪[k], schr ψ (e (0, Pi.single i ((v : k) * o))) φ = φ := fun i =>
        hu.basis _ (((continuous_single (A := fun _ : μ => k) i).tendsto' 0 0 (Pi.single_zero i)).eventually s2)
      choose v hv using s3
      refine HasCompactSupport.intro (K := Set.pi Set.univ fun i => (fun o => (u : k) * ((v i)⁻¹ : kˣ) * o) '' (𝒪[k] : Set k))
        (isCompact_univ_pi fun i => hu.compact.image (by fun_prop)) fun y hy => by_contra fun hne => hy fun i _ => ?_
      refine ⟨_, (hu.ann (y i * v i)).1 fun o ho => ?_, ?_⟩
      · have := congrFun (hint (0, Pi.single i ((v i : k) * o)) φ hφ) y
        rw [hv i o ho] at this
        simp only [schr, Pi.zero_apply, zero_mul, mul_zero, add_zero, dotProduct_single] at this
        rw [mul_assoc]
        exact mul_right_cancel₀ hne (this.symm.trans (one_mul _).symm)
      · simp only [Units.val_inv_eq_inv_val]
        field_simp
  refine ⟨ι, ⟨hmaps, fun φ hφ φ' hφ' h => ?_, fun Φ hΦ => ?_⟩, hint⟩
  · by_contra hne
    have hd := (SB (κ → k)).sub_mem hφ hφ'
    refine hl₀ (cyc hc h1 hd (sub_ne_zero.2 hne) l (fun w => ?_) _ hφ₀)
    obtain ⟨w, rfl⟩ := e.surjective w
    rw [← h0, hint w _ hd, map_sub, h, sub_self]
    simp [schr]
  · by_contra hn
    have hn' : Φ ∉ (SB (κ → k)).map ι := hn
    obtain ⟨m, hm, hb⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn' inferInstance
    refine hm (cyc hc h1 (hmaps _ hφ₀) (fun h => hl₀ (by rw [← h0, h]; rfl)) m (fun w => ?_) _ hΦ)
    rw [← hint w _ hφ₀, ← Submodule.mem_bot ℂ, ← hb]
    exact ⟨_, ⟨_, schr_mem hc _ hφ₀, rfl⟩, rfl⟩

end Mod

theorem cyclicity : Cyc := fun _ _ _ _ _ _ _ _ _ hc h1 _ h₀ hne l hl => Mod.cyc hc h1 h₀ hne l hl

theorem model_existence : ModelEx := fun _ _ _ _ _ _ _ _ _ _ _ hc h1 e he => Mod.model hc h1 e he

end PositivityTheory.KCo
