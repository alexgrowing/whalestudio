import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Descend

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [DiscreteTopology M]

private theorem coc_one {ρ : Representation R Γ M} {c : Γ → M} (hc : c ∈ Z1 ρ) : c 1 = 0 := by
  have h := hc.2 1 1
  simpa using h

private def killSub (ρ : Representation R Γ M) {c : Γ → M} (hc : c ∈ Z1 ρ) : Subgroup Γ where
  carrier := {g | ρ g = 1 ∧ c g = 0}
  one_mem' := ⟨map_one ρ, coc_one hc⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [map_mul, ha, hb, one_mul], by rw [hc.2, ha', hb', map_zero, add_zero]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ρ a⁻¹ = 1 := by
      have : ρ (a * a⁻¹) = 1 := by rw [mul_inv_cancel, map_one]
      rwa [map_mul, ha, one_mul] at this
    refine ⟨h1, ?_⟩
    have h := hc.2 a a⁻¹
    rw [mul_inv_cancel, coc_one hc, ha', ha] at h
    simpa using h.symm

private theorem killSub_normal (ρ : Representation R Γ M) {c : Γ → M} (hc : c ∈ Z1 ρ) : (killSub ρ hc).Normal where
  conj_mem := by
    rintro g ⟨hg, hg'⟩ h
    refine ⟨by rw [map_mul, map_mul, hg, mul_one, ← map_mul, mul_inv_cancel, map_one], ?_⟩
    have e := hc.2 h h⁻¹
    rw [mul_inv_cancel, coc_one hc] at e
    rw [hc.2, hc.2, hg', map_zero, add_zero, map_mul, hg, mul_one]
    exact e.symm

private theorem killSub_closed (ρ : Representation R Γ M) (hρ : ContAction ρ) {c : Γ → M} (hc : c ∈ Z1 ρ) :
    IsClosed (killSub ρ hc : Set Γ) := by
  have e : (killSub ρ hc : Set Γ) = (⋂ m : M, {g | ρ g m = m}) ∩ {g | c g = 0} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact and_congr_left' LinearMap.ext_iff
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun m => isClosed_eq ?_ continuous_const) (isClosed_eq hc.1 continuous_const)
  exact Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) hρ (continuous_id.prodMk continuous_const)

private theorem module_finite_z1_padicInt [Finite M] (ρ : Representation R Γ M) [Finite (H1 ρ)] : Finite (Z1 ρ) := by
  haveI : Finite (B1 ρ) := (Set.finite_range (d0 ρ)).to_subtype
  haveI : Finite ((B1 ρ).comap (Z1 ρ).subtype) :=
    Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 ρ)) fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : B1 ρ => z.1) h))
  haveI : Finite ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup := this
  haveI : Finite (Z1 ρ ⧸ ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup) := ‹Finite (H1 ρ)›
  exact Finite.of_addSubgroup_quotient ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup

end

theorem UpperTheory.V.Ws.Gys.zunrFin :
    GlobalFiniteness → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation (ZMod (l ^ 1)) (G F Ω) M) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ContAction ρ → UnrOut ρ S → (Zunr ρ S).Finite := by
  intro hGF F Ω _ _ _ _ _ l _ M _ _ _ _ _ ρ S hS hρ hU
  obtain ⟨ρS, hcomp, hρS⟩ := UpperTheory.V.Ws.Gys.descend F Ω _ M ρ S hρ hU
  obtain ⟨-, f1, -⟩ := hGF F Ω l 1 M S ρS one_pos hS hρS
  haveI := f1
  haveI := module_finite_z1_padicInt ρS
  refine (Set.finite_range fun c : Z1 ρS => c.1 ∘ toGS Ω (S : Set (HeightOneSpectrum (𝓞 F)))).subset ?_
  rintro c ⟨hc, hI⟩
  haveI := killSub_normal ρ hc
  have hle : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ killSub ρ hc := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => ?_) (killSub_closed ρ hρ hc)
    simp only [Set.mem_iUnion] at hg
    obtain ⟨v, hv, A, hA, hg⟩ := hg
    exact ⟨hU v hv A hA g hg, hI v hv A hA g hg⟩
  let cS : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M := Quotient.lift c fun a b hab => by
    have h := (hle (QuotientGroup.leftRel_apply.1 hab)).2
    have e := hc.2 a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h, map_zero, add_zero] at e
    exact e.symm
  refine ⟨⟨cS, hc.1.quotient_lift _, fun x y => ?_⟩, rfl⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have e := hc.2 a b
  rw [← hcomp] at e
  exact e
