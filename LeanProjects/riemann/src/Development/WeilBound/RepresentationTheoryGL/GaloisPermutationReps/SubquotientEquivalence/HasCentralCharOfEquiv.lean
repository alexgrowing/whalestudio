import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

namespace CentralCharacterTransfer

theorem equiv_apply {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (g : G) (v : V) :
    φ (ρ g v) = σ g (φ v) :=
  Representation.IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g v

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {H : Subgroup G} {v : V} : v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  change (∀ h : H, ρ h v = ((1 : H →* ℂˣ) h : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · intro hv h hh
    exact hv ⟨h, hh⟩
  · intro hv h
    exact hv h h.2

theorem map_fixed {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (H : Subgroup G) :
    (fixed ρ H).map φ.toLinearEquiv.toLinearMap = fixed σ H := by
  ext w
  simp only [Submodule.mem_map, mem_fixed_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩ h hh
    change σ h (φ v) = φ v
    rw [← equiv_apply, hv h hh]
  · intro hw
    have e2 : φ (φ.toLinearEquiv.symm w) = w := φ.toLinearEquiv.apply_symm_apply w
    refine ⟨φ.toLinearEquiv.symm w, fun h hh => ?_, e2⟩
    apply φ.toLinearEquiv.injective
    change φ _ = φ _
    rw [equiv_apply, e2, hw h hh]

theorem hasCentralChar_of_equiv {k V W : Type} [Field k] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} (φ : π.Equiv σ)
    {ω : kˣ →* ℂˣ} (h : HasCentralChar π ω) : HasCentralChar σ ω := by
  intro z w
  have e2 : φ (φ.toLinearEquiv.symm w) = w := φ.toLinearEquiv.apply_symm_apply w
  rw [← e2, ← equiv_apply, h z]
  exact φ.toLinearEquiv.map_smul _ _

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem transfer {W W' V V' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}
    {τ : Representation ℂ (GL (Fin n) 𝓀[k]) W} {τ' : Representation ℂ (GL (Fin n) 𝓀[k]) W'}
    {π : Representation ℂ (GL (Fin n) k) V} {π' : Representation ℂ (GL (Fin n) k) V'}
    {j : W →ₗ[ℂ] V} {j' : W' →ₗ[ℂ] V'} (hj : IsTypeMap τ π j) (hj' : IsTypeMap τ' π' j')
    (hf : fixed π (KOne k (Fin n)) = LinearMap.range j) (hf' : fixed π' (KOne k (Fin n)) = LinearMap.range j')
    (φ : π.Equiv π') : ∃ e : W ≃ₗ[ℂ] W', ∀ g v, e (τ g v) = τ' g (e v) := by
  have hm := map_fixed φ (KOne k (Fin n))
  rw [hf, hf'] at hm
  let e : W ≃ₗ[ℂ] W' := (LinearEquiv.ofInjective j hj.1).trans
    ((φ.toLinearEquiv.submoduleMap (LinearMap.range j)).trans
      ((LinearEquiv.ofEq _ _ hm).trans (LinearEquiv.ofInjective j' hj'.1).symm))
  have key : ∀ w, j' (e w) = φ (j w) := by
    intro w
    have h1 := congrArg Subtype.val ((LinearEquiv.ofInjective j' hj'.1).apply_symm_apply
      ((LinearEquiv.ofEq _ _ hm) ((φ.toLinearEquiv.submoduleMap _) ((LinearEquiv.ofInjective j hj.1) w))))
    rw [LinearEquiv.ofInjective_apply] at h1
    exact h1
  refine ⟨e, fun g v => ?_⟩
  obtain ⟨g', rfl⟩ := GlobalTheory.LocGL.redK_surjective g
  apply hj'.1
  rw [key, hj.2, hj'.2, key]
  exact equiv_apply φ _ _

end CentralCharacterTransfer

open CentralCharacterTransfer in
theorem st8a : St4 → St5 → St6 → St7 → St8a := by
  classical
  intro h4 h5 h6 h7 k _ _ _ _ n hn ϖ hϖ c
  obtain ⟨τ, hτ, hinj⟩ := h7 𝓀[k] n hn
  have hdata : ∀ P ∈ Lab 𝓀[k] n, ∃ (π : IrrRep (GL (Fin n) k)) (ω : kˣ →* ℂˣ) (j : (τ P).V →ₗ[ℂ] π.V),
      HasCentralChar π.ρ ω ∧ ω ϖ = c ∧ IsTypeMap (τ P).ρ π.ρ j :=
    fun P hP => h4 k (τ P).V n hn (τ P).ρ (hτ P hP).1 ϖ hϖ c
  choose π ω j hω hc hj using hdata
  have hirr : (1 : Representation ℂ (GL (Fin n) k) ℂ).IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun s => ?_ }
    · exact bot_ne_top (α := Submodule ℂ ℂ) (congrArg Subrepresentation.toSubmodule h)
    · rcases Ideal.eq_bot_or_top s.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  let d : IrrRep (GL (Fin n) k) := ⟨ℂ, 1, fun v => by simp, hirr⟩
  let F : 𝓀[k][X] → IrrGL k := fun P =>
    if hP : P ∈ Lab 𝓀[k] n then ⟨n, Quotient.mk _ (π P hP)⟩ else ⟨n, Quotient.mk _ d⟩
  have hF : ∀ P (hP : P ∈ Lab 𝓀[k] n), F P = ⟨n, Quotient.mk _ (π P hP)⟩ := by
    intro P hP
    simp only [F, dif_pos hP]
  have hfix : ∀ P (hP : P ∈ Lab 𝓀[k] n),
      fixed (π P hP).ρ (KOne k (Fin n)) = LinearMap.range (j P hP) := by
    intro P hP
    haveI := GlobalTheory.SmGL.nontrivial_of_irreducible (hτ P hP).1
    exact h6 k (τ P).V n (τ P).ρ (hτ P hP).2 (π P hP) (ω P hP) (hω P hP) (j P hP) (hj P hP)
  refine ⟨F, fun P hP => ?_, fun P hP P' hP' hPP => ?_⟩
  · haveI := GlobalTheory.SmGL.nontrivial_of_irreducible (hτ P hP).1
    rw [hF P hP]
    obtain ⟨ψ⟩ : Nonempty ((π P hP).ρ.Equiv
        (IrrCl.rep (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))).ρ) :=
      Quotient.exact (Quotient.out_eq (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))).symm
    set π₀ := IrrCl.rep (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))
    let j₀ : (τ P).V →ₗ[ℂ] π₀.V := ψ.toLinearEquiv.toLinearMap ∘ₗ j P hP
    have hj₀ : IsTypeMap (τ P).ρ π₀.ρ j₀ := by
      refine ⟨ψ.toLinearEquiv.injective.comp (hj P hP).1, fun g v => ?_⟩
      change ψ (j P hP _) = π₀.ρ g (ψ (j P hP v))
      rw [(hj P hP).2, equiv_apply]
    have hcc := hasCentralChar_of_equiv ψ (hω P hP)
    refine ⟨rfl, ⟨hn, h5 k (τ P).V n (τ P).ρ (hτ P hP).2 π₀ j₀ hj₀⟩, ?_, ω P hP, hcc, hc P hP⟩
    change fixed π₀.ρ (KOne k (Fin n)) ≠ ⊥
    rw [h6 k (τ P).V n (τ P).ρ (hτ P hP).2 π₀ (ω P hP) hcc j₀ hj₀]
    obtain ⟨w, hw⟩ := exists_ne (0 : (τ P).V)
    intro hb
    apply hw
    apply hj₀.1
    rw [map_zero]
    have hm : j₀ w ∈ LinearMap.range j₀ := LinearMap.mem_range_self j₀ w
    rw [hb] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  · rw [hF P hP, hF P' hP'] at hPP
    have hq := eq_of_heq (Sigma.mk.inj_iff.1 hPP).2
    obtain ⟨φ⟩ : Nonempty ((π P hP).ρ.Equiv (π P' hP').ρ) := Quotient.exact hq
    obtain ⟨e, he⟩ := transfer (hj P hP) (hj P' hP') (hfix P hP) (hfix P' hP') φ
    exact hinj P hP P' hP' ⟨e, he⟩

end PositivityTheory.Rg.DzCount

end
