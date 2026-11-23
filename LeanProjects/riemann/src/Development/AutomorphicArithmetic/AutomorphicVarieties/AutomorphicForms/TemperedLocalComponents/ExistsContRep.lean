import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PCuspFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
open NumberField GlobalTheory.CuspRep UpperTheory.V

open Matrix in

private theorem exists_contRep {K I : Type} [Group K] [TopologicalSpace K] {d : ℕ} (ξ : K →* Matrix (Fin d) (Fin d) ℂ)
    (ev : I → Module.Dual ℂ (Fin d → ℂ)) (hc : ∀ i v, Continuous fun k => ev i (ξ k *ᵥ v))
    (hs : ∀ k v, (∀ i, ev i v = 0) → ∀ i, ev i (ξ k *ᵥ v) = 0) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W) (ρ : Representation ℂ K W),
      GlobalTheory.Published.AutFin.IsContRep ρ ∧ ∀ i v, (fun k => ev i (ξ k *ᵥ v)) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  let N : Submodule ℂ (Fin d → ℂ) := ⨅ i, LinearMap.ker (ev i)
  have hN : ∀ v, v ∈ N ↔ ∀ i, ev i v = 0 := fun v => by simp [N, Submodule.mem_iInf]
  let σ : Representation ℂ K (Fin d → ℂ) := (Matrix.toLinAlgEquiv' : _ ≃ₐ[ℂ] _).toMonoidHom.comp ξ
  have hσ : ∀ k v, σ k v = ξ k *ᵥ v := fun k v => Matrix.toLinAlgEquiv'_apply _ _
  have hle : ∀ k, N ≤ N.comap (σ k) := fun k v hv => (hN _).2 (hσ k v ▸ hs k v ((hN v).1 hv))
  have hq : ∀ k v, σ.quotient N hle k (N.mkQ v) = N.mkQ (ξ k *ᵥ v) := fun k v => by rw [← hσ]; rfl
  refine ⟨(Fin d → ℂ) ⧸ N, inferInstance, inferInstance, inferInstance, σ.quotient N hle, fun ℓ w => ?_, fun i v => ?_⟩
  · obtain ⟨v, rfl⟩ := N.mkQ_surjective w
    simp only [hq]
    have hl : ℓ ∘ₗ N.mkQ ∈ Submodule.span ℂ (Set.range ev) :=
      FiniteDimensional.mem_span_of_iInf_ker_le_ker fun x hx => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, (Submodule.Quotient.mk_eq_zero N).2 hx |> fun h => show N.mkQ x = 0 from h,
          map_zero]
    change Continuous fun k => (ℓ ∘ₗ N.mkQ) (ξ k *ᵥ v)
    generalize ℓ ∘ₗ N.mkQ = m at hl
    induction hl using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hc i v
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  · refine Submodule.subset_span ⟨N.liftQ (ev i) (iInf_le _ i), N.mkQ v, funext fun k => ?_⟩
    rw [hq]
    rfl

open Matrix in
theorem UpperTheory.V.Af.admissibleReal :
    UpperTheory.V.Published.AdmissibleReal := by
  intro F _ _ _ a π U hU d ξ
  obtain ⟨c, hc⟩ := TR.Cen.exists_cap_scalar π
  let I : Type := {f : (Fin d → ℂ) →ₗ[ℂ] π.V // ∀ k v, f (ξ k *ᵥ v) = π.op (.cpt k) (f v)} × GA F a
  let ev : I → Module.Dual ℂ (Fin d → ℂ) := fun i =>
    (LinearMap.proj i.2).comp ((TR.Sm F a).subtype.comp (π.V.subtype.comp i.1.1))
  have hev : ∀ (i : I) k v, ev i (ξ k *ᵥ v) = (TR.cptRep F a k (i.1.1 v).1).1 i.2 := fun i k v =>
    congrArg (fun x : π.V => x.1.1 i.2) (i.1.2 k v)
  obtain ⟨W, _, _, _, ρ, hρ, hco⟩ := exists_contRep ξ ev
    (fun i v => by simp only [hev]; exact TR.Cen.continuous_cptRep _ _)
    (fun k v h i => by rw [hev]; exact h (i.1, i.2 * TR.infGL F a (Unitary.toUnits k)))
  have hfin := UpperTheory.V.Af.cuspFormsFiniteReal F a U hU W ρ hρ c
  set S := Submodule.span ℂ {φ : TR.Sm F a | TR.IsCuspForm φ ∧ (∀ k ∈ U, TR.finRep F a k φ = φ) ∧
    (∀ g : GA F a, (fun k : TR.Kinf F a => (TR.cptRep F a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
    ∀ v u, TR.cap v u φ = c v u • φ}
  refine ⟨S.comap π.V.subtype, FiniteDimensional.of_injective
    ((π.V.subtype ∘ₗ (S.comap π.V.subtype).subtype).codRestrict S fun x => x.2) (fun x y e => ?_), ?_⟩
  · exact Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
  · rintro f hf hfix _ ⟨v, rfl⟩
    refine Submodule.subset_span ⟨π.cusp _ (f v).2, fun k hk => congrArg Subtype.val (hfix k hk v), fun g => ?_,
      fun w u => hc w u _ (f v).2⟩
    have h := hco (⟨f, hf⟩, g) v
    simp only [hev] at h
    exact h
