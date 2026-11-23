import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.FinSep

theorem exists_open_normalised {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (C : Subgroup G) (hC : IsCompact (C : Set G)) (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W ≤ U ∧ ∀ c ∈ C, ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
  let W : Subgroup G :=
    { carrier := {u | ∀ c ∈ C, c * u * c⁻¹ ∈ U}
      one_mem' := fun c _ => by simp [U.one_mem]
      mul_mem' := fun {a b} ha hb c hc => by
        have := U.mul_mem (ha c hc) (hb c hc)
        simpa [mul_assoc] using this
      inv_mem' := fun {a} ha c hc => by
        have := U.inv_mem (ha c hc)
        simpa [mul_assoc] using this }
  have hO : IsOpen ((fun q : G × G => q.1 * q.2 * q.1⁻¹) ⁻¹' (U : Set G)) :=
    hU.preimage (by fun_prop)
  obtain ⟨u, v, -, hv, hCu, h1v, huv⟩ := generalized_tube_lemma hC (isCompact_singleton (x := (1 : G))) hO
    (fun q hq => by
      obtain ⟨-, hq2⟩ := hq
      simp only [Set.mem_singleton_iff] at hq2
      simp [Set.mem_preimage, hq2, U.one_mem])
  refine ⟨W, W.isOpen_of_mem_nhds (g := 1) ?_, fun w hw => by simpa using hw 1 C.one_mem, ?_⟩
  · refine Filter.mem_of_superset (hv.mem_nhds (h1v rfl)) fun w hw c hc => ?_
    exact huv (Set.mk_mem_prod (hCu hc) hw)
  · intro c hc w hw d hd
    have := hw (d * c) (C.mul_mem hd hc)
    simpa [mul_assoc] using this

theorem exists_finDim_separating : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ Kc : Subgroup (GAd σ J), IsCompact (Kc : Set (GAd σ J)) → ∀ x ∈ Kc, ∀ y ∈ Kc, projFin σ J x ≠ projFin σ J y →
      ∃ V : Submodule ℂ (GAd σ J → ℂ), FiniteDimensional ℂ V ∧
        (∀ w ∈ V, Continuous w ∧ GlobalTheory.UAut.IsSm σ J w ∧
          (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ u ∈ U, u ∈ finPts σ J → ∀ g, w (g * u) = w g) ∧
          ∀ k ∈ Kc, (fun g => w (k * g)) ∈ V ∧ (fun g => w (g * k)) ∈ V) ∧ ∃ f ∈ V, f x ≠ f y := by
  intro F E _ _ _ _ _ σ _ n J _ Kc hKc x hx y hy hxy
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin σ J
  classical
  let C : Subgroup (GFin σ J) := Kc.map (projFin σ J)
  have hC : IsCompact (C : Set (GFin σ J)) := by
    rw [Subgroup.coe_map]; exact hKc.image (continuous_projFin σ J)
  have hpC : ∀ k ∈ Kc, projFin σ J k ∈ C := fun k hk => Subgroup.mem_map_of_mem _ hk
  have ha : (projFin σ J x)⁻¹ * projFin σ J y ≠ 1 := fun h => hxy (inv_mul_eq_one.1 h)
  obtain ⟨U₀, hU₀⟩ := NonarchimedeanGroup.is_nonarchimedean
    ({(projFin σ J x)⁻¹ * projFin σ J y}ᶜ : Set (GFin σ J))
    (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.2 (Ne.symm ha)))
  obtain ⟨W, hWo, hWU, hWn⟩ := exists_open_normalised C hC U₀.toSubgroup U₀.isOpen
  let e : GFin σ J → GAd σ J → ℂ := fun c g => if c⁻¹ * projFin σ J g ∈ W then 1 else 0
  let S : Set (GAd σ J → ℂ) := e '' (C : Set (GFin σ J))
  let U : Subgroup (GAd σ J) := W.comap (projFin σ J)
  have hUo : IsOpen (U : Set (GAd σ J)) := hWo.preimage (continuous_projFin σ J)

  have hfin : S.Finite := by
    obtain ⟨t, htC, hcov⟩ := hC.elim_nhds_subcover (fun c => {z | c⁻¹ * z ∈ W})
      (fun c _ => (hWo.preimage (continuous_const_mul c⁻¹)).mem_nhds (by simp [W.one_mem]))
    refine ((t.finite_toSet.image e).subset ?_)
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨d, hd, hcd⟩ := Set.mem_iUnion₂.1 (hcov hc)
    refine ⟨d, hd, funext fun g => ?_⟩
    have hcd' : d⁻¹ * c ∈ W := hcd
    have key : d⁻¹ * projFin σ J g ∈ W ↔ c⁻¹ * projFin σ J g ∈ W := by
      constructor
      · intro h
        have := W.mul_mem (W.inv_mem hcd') h
        simpa [mul_assoc] using this
      · intro h
        have := W.mul_mem hcd' h
        simpa [mul_assoc] using this
    simp only [e, key]

  have hinv : ∀ w ∈ Submodule.span ℂ S, ∀ u ∈ U, ∀ g, w (g * u) = w g := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨c, -, rfl⟩ := hw
      intro u hu g
      have hu' : projFin σ J u ∈ W := hu
      have key : c⁻¹ * projFin σ J (g * u) ∈ W ↔ c⁻¹ * projFin σ J g ∈ W := by
        rw [map_mul, ← mul_assoc]
        exact ⟨fun h => by simpa using W.mul_mem h (W.inv_mem hu'), fun h => W.mul_mem h hu'⟩
      simp only [e, key]
    | zero => intro u _ g; rfl
    | add a b _ _ ha hb => intro u hu g; simp [ha u hu g, hb u hu g]
    | smul r a _ ha => intro u hu g; simp [ha u hu g]
  have hcont : ∀ w : GAd σ J → ℂ, (∀ u ∈ U, ∀ g, w (g * u) = w g) → Continuous w := fun w hw =>
    continuous_iff_continuousAt.2 fun g => by
      have hn : (fun h => g⁻¹ * h) ⁻¹' (U : Set (GAd σ J)) ∈ 𝓝 g :=
        (hUo.preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp [U.one_mem])
      have hev : ∀ᶠ h in 𝓝 g, w g = w h := by
        filter_upwards [hn] with h hh
        have := hw _ hh g
        rw [mul_inv_cancel_left] at this
        exact this.symm
      exact continuousAt_const.congr hev
  have hsm : ∀ w : GAd σ J → ℂ, (∀ u ∈ U, ∀ g, w (g * u) = w g) → GlobalTheory.UAut.IsSm σ J w := by
    intro w hw k γ hγ g
    have hmem : ∀ t : Fin k → ℝ, (List.ofFn fun i => γ i (t i)).prod ∈ U := fun t =>
      U.list_prod_mem fun a ha => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
        obtain ⟨w', τ, Z, -, hZ⟩ := hγ i
        obtain ⟨z, hz, -⟩ := hZ (t i)
        show projFin σ J (γ i (t i)) ∈ W
        rw [hz, projFin_embArch]
        exact W.one_mem
    have : (fun t : Fin k → ℝ => w (g * (List.ofFn fun i => γ i (t i)).prod)) = fun _ => w g :=
      funext fun t => hw _ (hmem t) g
    rw [this]
    exact contDiff_const

  have hleft : ∀ k ∈ Kc, Submodule.span ℂ S ≤
      (Submodule.span ℂ S).comap (LinearMap.funLeft ℂ ℂ (fun g : GAd σ J => k * g)) := by
    intro k hk
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    refine Submodule.subset_span ⟨(projFin σ J k)⁻¹ * c, C.mul_mem (C.inv_mem (hpC k hk)) hc, funext fun g => ?_⟩
    simp [e, LinearMap.funLeft_apply, mul_assoc]
  have hright : ∀ k ∈ Kc, Submodule.span ℂ S ≤
      (Submodule.span ℂ S).comap (LinearMap.funLeft ℂ ℂ (fun g : GAd σ J => g * k)) := by
    intro k hk
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    have hk' := hpC k hk
    refine Submodule.subset_span ⟨c * (projFin σ J k)⁻¹, C.mul_mem hc (C.inv_mem hk'), funext fun g => ?_⟩
    have key : (c * (projFin σ J k)⁻¹)⁻¹ * projFin σ J g ∈ W ↔ c⁻¹ * projFin σ J (g * k) ∈ W := by
      rw [mul_inv_rev, inv_inv, map_mul]
      constructor
      · intro h
        have := hWn _ (C.inv_mem hk') _ h
        simpa [mul_assoc] using this
      · intro h
        have := hWn _ hk' _ h
        simpa [mul_assoc] using this
    simp only [e, LinearMap.funLeft_apply, Function.comp_apply, key]
  refine ⟨Submodule.span ℂ S, FiniteDimensional.span_of_finite ℂ hfin, fun w hw =>
    ⟨hcont w (hinv w hw), hsm w (hinv w hw), ⟨U, hUo, fun u hu _ g => hinv w hw u hu g⟩,
      fun k hk => ⟨hleft k hk hw, hright k hk hw⟩⟩, e (projFin σ J x),
    Submodule.subset_span ⟨_, hpC x hx, rfl⟩, ?_⟩
  have h1 : (projFin σ J x)⁻¹ * projFin σ J x ∈ W := by simp [W.one_mem]
  have h2 : (projFin σ J x)⁻¹ * projFin σ J y ∉ W := fun h => hU₀ (hWU h) rfl
  simp only [e, h1, h2, if_true, if_false]
  exact one_ne_zero

end GlobalTheory.FinSep
