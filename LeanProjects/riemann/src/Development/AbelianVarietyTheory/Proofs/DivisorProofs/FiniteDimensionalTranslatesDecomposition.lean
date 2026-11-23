import Mathlib

namespace GlobalTheory

theorem translates_span_finiteDimensional_of_double_coset :
    ∀ (A : Type) [CommGroup A] (Fn : A → ℂ) (Γ U S : Set A) (C : Finset A),
      (∀ γ ∈ Γ, ∀ t, Fn (γ * t) = Fn t) → (∀ u ∈ U, ∀ t, Fn (t * u) = Fn t) →
      (∀ t, ∃ γ ∈ Γ, ∃ c ∈ C, ∃ a ∈ S, ∃ u ∈ U, t = γ * c * a * u) →
      (∀ b : A, FiniteDimensional ℂ
        (Submodule.span ℂ (Set.range fun a : S => fun a' : S => Fn (b * a' * a)))) →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun s : A => fun t => Fn (t * s))) := by
  intro A _ Fn Γ U S C hΓ hU hdec hfin
  set T := Submodule.span ℂ (Set.range fun s : A => fun t => Fn (t * s)) with hT

  have hinv : ∀ g ∈ T, (∀ γ ∈ Γ, ∀ t, g (γ * t) = g t) ∧ (∀ u ∈ U, ∀ t, g (t * u) = g t) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      refine ⟨fun γ hγ t => ?_, fun u hu t => ?_⟩
      · show Fn (γ * t * s) = Fn (t * s)
        rw [mul_assoc]; exact hΓ γ hγ _
      · show Fn (t * u * s) = Fn (t * s)
        rw [mul_right_comm]; exact hU u hu _
    | zero => exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    | add x y _ _ hx hy =>
      exact ⟨fun γ hγ t => by simp [hx.1 γ hγ t, hy.1 γ hγ t],
        fun u hu t => by simp [hx.2 u hu t, hy.2 u hu t]⟩
    | smul r x _ hx =>
      exact ⟨fun γ hγ t => by simp [hx.1 γ hγ t], fun u hu t => by simp [hx.2 u hu t]⟩

  let L : (A → ℂ) →ₗ[ℂ] (C → S → ℂ) :=
    { toFun := fun g c a => g (c.1 * a.1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : ∀ g ∈ T, ∀ h ∈ T, L g = L h → g = h := by
    intro g hg h hh hgh
    funext t
    obtain ⟨γ, hγ, c, hc, a, ha, u, hu, rfl⟩ := hdec t
    have rd : ∀ f ∈ T, f (γ * c * a * u) = f (c * a) := fun f hf => by
      rw [(hinv f hf).2 u hu, mul_assoc, (hinv f hf).1 γ hγ]
    rw [rd g hg, rd h hh]
    exact congrFun (congrFun hgh ⟨c, hc⟩) ⟨a, ha⟩

  let W : Submodule ℂ (S → ℂ) := ⨆ p : C × C,
    Submodule.span ℂ (Set.range fun a : S => fun a' : S => Fn (p.1.1 * p.2.1 * a' * a))
  haveI : ∀ p : C × C, FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun a : S => fun a' : S => Fn (p.1.1 * p.2.1 * a' * a))) :=
    fun p => hfin _
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_iSup _
  let Φ : (C → W) →ₗ[ℂ] (C → S → ℂ) := LinearMap.pi fun c => W.subtype ∘ₗ LinearMap.proj c
  have hle : T ≤ (LinearMap.range Φ).comap L := by
    rw [hT, Submodule.span_le]
    rintro x ⟨s, rfl⟩
    have hW : ∀ c : C, (fun a' : S => Fn (c.1 * a'.1 * s)) ∈ W := by
      intro c
      obtain ⟨γ0, hγ0, c0, hc0, a0, ha0, u0, hu0, rfl⟩ := hdec s
      have key : ∀ t, Fn (γ0 * t * u0) = Fn t := fun t => by rw [hU u0 hu0, hΓ γ0 hγ0]
      have e : (fun a' : S => Fn (c.1 * a'.1 * (γ0 * c0 * a0 * u0)))
          = fun a' : S => Fn ((c.1 * c0) * a'.1 * a0) := by
        funext a'
        rw [← key (c.1 * c0 * a'.1 * a0)]
        congr 1
        ac_rfl
      rw [e]
      exact Submodule.mem_iSup_of_mem (c, ⟨c0, hc0⟩)
        (Submodule.subset_span ⟨⟨a0, ha0⟩, rfl⟩)
    exact ⟨fun c => ⟨_, hW c⟩, rfl⟩

  let f : T →ₗ[ℂ] LinearMap.range Φ :=
    LinearMap.codRestrict _ (L ∘ₗ T.subtype) (fun x => hle x.2)
  exact Module.Finite.of_injective f
    (fun x y hxy => Subtype.ext (hinj x.1 x.2 y.1 y.2 (congrArg Subtype.val hxy)))

end GlobalTheory
