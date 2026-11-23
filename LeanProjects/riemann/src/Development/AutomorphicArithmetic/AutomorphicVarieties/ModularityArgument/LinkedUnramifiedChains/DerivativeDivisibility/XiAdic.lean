import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LinkedUnlOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

noncomputable section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open IsLocalRing Formalism.ConjugateSelfDual UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.Pr

namespace UpperTheory.V.J

private def xiExt {l : ℕ} [Fact l.Prime] {k k' : Type} [Field k] [Field k'] {Φ : Fr.Frame l k} {n : ℕ}
    {K : Type} [CommRing K] (f : k →+* k') (ρ : Fr.NRep Φ n K) : Fr.NRep (Φ.ext f) n K where
  r := ρ.r
  ψ := ρ.ψ
  pol := ρ.pol
  diag := ρ.diag
  ord := ρ.ord

private theorem xi_adic {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] {u : Γ → R} (h : AdicCont (maximalIdeal R) u) :
    AdicCont (maximalIdeal S) fun g => φ (u g) := by
  unfold AdicCont at h ⊢
  intro N
  have h1 : Ideal.map φ (maximalIdeal R) ≤ maximalIdeal S :=
    Ideal.map_le_iff_le_comap.mpr (fun a ha => Ideal.mem_comap.mpr (map_nonunit φ a ha))
  have hle : maximalIdeal R ^ N ≤ Ideal.comap φ (maximalIdeal S ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono h1 N
  have hc := (h N).comp (Ideal.quotientMap (maximalIdeal S ^ N) φ hle)
  convert hc using 1
  funext g
  simp only [Function.comp_apply, Ideal.quotientMap_mk]

private theorem xi_key {O A O₁ : Type} [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A]
    [CommRing O₁] [IsLocalRing O₁] [IsNoetherianRing O₁] [IsAdicComplete (maximalIdeal O₁) O₁]
    [Algebra O A] [IsLocalHom (algebraMap O A)] (j : A →+* O₁) [IsLocalHom j]
    (f : ResidueField O →+* ResidueField O₁)
    (hf : ∀ a, f (residue O a) = residue O₁ (j (algebraMap O A a))) (x : A) (u : ResidueField O)
    (h : residue A x = ResidueField.map (algebraMap O A) u) : res O₁ O₁ (j x) = f u := by
  obtain ⟨a, rfl⟩ := residue_surjective u
  have h1 : x - algebraMap O A a ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, map_sub, h, ResidueField.map_residue, sub_self]
  have h2 : j x - j (algebraMap O A a) ∈ maximalIdeal O₁ := by
    rw [← map_sub]
    exact map_nonunit j _ h1
  have h3 : residue O₁ (j x) = residue O₁ (j (algebraMap O A a)) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact h2
  rw [hf, ← h3]
  simp only [res]
  simp
  rw [RingEquiv.symm_apply_eq]
  rfl

private theorem xi_lift {l : ℕ} [Fact l.Prime] {O A O₁ : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [IsLocalRing A] [CommRing O₁] [IsLocalRing O₁] [IsNoetherianRing O₁]
    [IsAdicComplete (maximalIdeal O₁) O₁] [Algebra O A] [IsLocalHom (algebraMap O A)] (j : A →+* O₁)
    [IsLocalHom j] (f : ResidueField O →+* ResidueField O₁)
    (hf : ∀ a, f (residue O a) = residue O₁ (j (algebraMap O A a)))
    {Φ : Fr.Frame l (ResidueField O)} {n : ℕ} (ρ : Fr.NRep Φ n A) (h : IsLiftA O ρ) :
    Fr.IsLift O₁ ((xiExt f ρ).map j) := by
  obtain ⟨hc, hb, hd⟩ := h
  refine ⟨⟨fun i k => ?_, fun v i => ?_⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i k hik => ?_⟩
  · exact xi_adic j (hc.1 i k)
  · exact xi_adic j (hc.2 v i)
  · change res O₁ O₁ (j (ρ.r g i i)) = _
    rw [xi_key j f hf (ρ.r g i i) _ (hb.1 g i)]
    simp [Fr.Frame.ext, map_pow]
    rfl
  · change res O₁ O₁ (j ((ρ.ψ v i g : Aˣ) : A)) = _
    rw [xi_key j f hf _ _ (hb.2 v i g)]
    simp [Fr.Frame.ext, map_pow]
    rfl
  · change res O₁ O₁ (j (ρ.r g i k)) = 0
    rw [xi_key j f hf (ρ.r g i k) 0 (by rw [map_zero]; exact hd g i k hik), map_zero]

private theorem xi_loc {l : ℕ} [Fact l.Prime] (c c₁ : Coef l) (A : Subalgebra c.O (PadicAlgCl l))
    (hA : ∀ x ∈ A, x ∈ c₁.O) : ∃ j : A →+* c₁.O, (∀ x, (j x).1 = x.1) ∧ IsLocalHom j := by
  let j : A →+* c₁.O :=
    { toFun := fun x => ⟨x.1, hA x.1 x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨j, fun x => rfl, ?_⟩
  have hfin := c₁.fin
  have hint : (algebraMap ℤ_[l] c₁.O).IsIntegral :=
    algebraMap_isIntegral_iff.mpr (Algebra.IsIntegral.of_finite ℤ_[l] c₁.O)
  have hcomp : j.comp ((algebraMap c.O A).comp (algebraMap ℤ_[l] c.O)) = algebraMap ℤ_[l] c₁.O :=
    RingHom.ext fun x => Subtype.ext rfl
  have hj : j.IsIntegral := RingHom.IsIntegral.tower_top _ j (hcomp ▸ hint)
  refine hj.isLocalHom (fun x y h => ?_)
  have h' := congrArg (fun z : c₁.O => (z : PadicAlgCl l)) h
  exact Subtype.ext h'

theorem xiEx :
    UpperTheory.V.J.XiEx := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f R A _ _ _ hA ρ hρ
  obtain ⟨j, hj, _⟩ := xi_loc c c₁ A hA
  have hf : ∀ a, f (residue c.O a) = residue c₁.O (j (algebraMap c.O A a)) := fun a =>
    R.hf a _ (hj (algebraMap c.O A a)).symm
  obtain ⟨ξ, hξ, -⟩ := R.S.univ c₁.O _ (xi_lift j f hf ρ hρ)
  refine ⟨ξ, fun g a b => ?_, fun v i g => ?_⟩
  · exact (congrArg (fun t : Fr.NRep _ _ c₁.O => (t.r g a b).1) hξ).trans (hj _)
  · exact (congrArg (fun t : Fr.NRep _ _ c₁.O => ((t.ψ v i g : c₁.Oˣ) : c₁.O).1) hξ).trans (hj _)

end UpperTheory.V.J

end
