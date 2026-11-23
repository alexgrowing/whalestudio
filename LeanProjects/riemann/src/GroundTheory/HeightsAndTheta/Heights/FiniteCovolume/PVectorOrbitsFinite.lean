import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineIndex
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCongruenceUnitsFiniteIndex

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

theorem exists_finset_of_finite_image {α β : Type*} (s : Set α) (f : α → β) (hf : (f '' s).Finite)
    (P : α → α → Prop) (hP : ∀ x ∈ s, ∀ y ∈ s, f x = f y → P y x) :
    ∃ S : Finset α, (S : Set α) ⊆ s ∧ ∀ x ∈ s, ∃ y ∈ S, P y x := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨∅, by simp, fun x _ => isEmptyElim x⟩
  choose! g hg1 hg2 using fun b (hb : b ∈ f '' s) => hb
  refine ⟨hf.toFinset.image g, ?_, fun x hx => ?_⟩
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    exact hg1 b (hf.mem_toFinset.1 hb)
  · have hb : f x ∈ f '' s := ⟨x, hx, rfl⟩
    exact ⟨g (f x), Finset.mem_image_of_mem _ (hf.mem_toFinset.2 hb),
      hP x hx _ (hg1 _ hb) (hg2 _ hb).symm⟩

section Vectors

variable {E : Type*} [Field E] [NumberField E] {W : Type*} [AddCommGroup W] [Module E W]

omit [NumberField E] in
theorem mem_ringMultiples {x y : W} : y ∈ ringMultiples E x ↔ ∃ a : 𝓞 E, (a : E) • x = y := by
  simp [ringMultiples]

theorem exists_unit_of_ringMultiples_eq {x b : W} (hb : b ≠ 0)
    (hxb : ringMultiples E x = ringMultiples E b) : ∃ ε : (𝓞 E)ˣ, x = ((ε : 𝓞 E) : E) • b := by
  have hx : x ∈ ringMultiples E b := hxb ▸ mem_ringMultiples.2 ⟨1, by simp⟩
  have hbx : b ∈ ringMultiples E x := hxb ▸ mem_ringMultiples.2 ⟨1, by simp⟩
  obtain ⟨a, ha⟩ := mem_ringMultiples.1 hx
  obtain ⟨c, hc⟩ := mem_ringMultiples.1 hbx
  have h1 : ((c : E) * (a : E)) • b = (1 : E) • b := by rw [mul_smul, ha, hc, one_smul]
  have hca : c * a = 1 := RingOfIntegers.ext (by simpa using smul_left_injective E hb h1)
  exact ⟨⟨a, c, by rw [mul_comm]; exact hca, hca⟩, ha.symm⟩

end Vectors

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in
theorem unitary_smul_smul {h : HermitianForm F E W} (γ : h.unitaryGroup) (c : E) (w : W) :
    γ • (c • w) = c • (γ • w) := by
  simp only [Subgroup.smul_def, LinearEquiv.smul_def, map_smul]

theorem line_vectorOrbits (h : HermitianForm F E W) (h₂ : IsotropicScaling.Statement h)
    (h₃ : BoundedIndexSubgroupsFinite.Statement W) (h₅ : LineIndexNeZero.Statement E W)
    {D : ℕ} {La : AddSubgroup W} {VV : Set W} (hLa : IsDIntegral h D La) (hsub : VV ⊆ La)
    (hiso : ∀ x ∈ VV, x ≠ 0 ∧ h.toSesq x x = 0) {C : ℕ} (hC : ∀ x ∈ VV, lineIndex E La x ≤ C)
    {v₀ : W} (hv₀ : v₀ ∈ VV) :
    ∃ S : Finset W, (S : Set W) ⊆ VV ∧ ∀ x ∈ VV, x ∈ Submodule.span E {v₀} →
      ∃ y ∈ S, ∃ γ ∈ latticeStab h La, γ • y = x := by
  classical
  obtain ⟨N, hN, hγ⟩ := h₂ La v₀ hLa.isLattice hLa.integral (hsub hv₀) (hiso v₀ hv₀).1
    (hiso v₀ hv₀).2
  have hUfin : Finite ((𝓞 E)ˣ ⧸ congruenceUnits E N) := by
    have : (congruenceUnits E N).FiniteIndex := ⟨CongruenceUnitsFiniteIndex.proof E N hN⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  let L : Set W := {x ∈ VV | x ∈ Submodule.span E {v₀}}
  have hspan : ∀ x ∈ L, Submodule.span E {x} = Submodule.span E {v₀} := by
    rintro x ⟨hx, hxs⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxs
    have hc : c ≠ 0 := by
      rintro rfl
      exact (hiso _ hx).1 (zero_smul E v₀)
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc) v₀
  have hT : ∀ x ∈ L, ringMultiples E x ∈ {H : AddSubgroup W |
      H ≤ La ⊓ (Submodule.span E {v₀}).toAddSubgroup ∧
      H.relIndex (La ⊓ (Submodule.span E {v₀}).toAddSubgroup) ≠ 0 ∧
      H.relIndex (La ⊓ (Submodule.span E {v₀}).toAddSubgroup) ≤ C} := by
    intro x hxL
    have h1 := h₅ La x hLa.isLattice (hsub hxL.1) (hiso x hxL.1).1
    have h2 := hC x hxL.1
    unfold lineIndex at h1 h2
    rw [hspan x hxL] at h1 h2
    refine ⟨fun y hy => ?_, h1, h2⟩
    obtain ⟨a, rfl⟩ := mem_ringMultiples.1 hy
    exact ⟨hLa.isLattice.smul_mem a x (hsub hxL.1), Submodule.smul_mem _ _ hxL.2⟩
  have hTfin := h₃ (La ⊓ (Submodule.span E {v₀}).toAddSubgroup) La hLa.isLattice.fg inf_le_left C
  choose! b hbL hb using fun H (hH : H ∈ (fun x => ringMultiples E x) '' L) => hH
  have hunit : ∀ x ∈ L, ∃ ε : (𝓞 E)ˣ, x = ((ε : 𝓞 E) : E) • b (ringMultiples E x) := by
    intro x hx
    have hH : ringMultiples E x ∈ (fun x => ringMultiples E x) '' L := ⟨x, hx, rfl⟩
    exact exists_unit_of_ringMultiples_eq (hiso _ (hbL _ hH).1).1 (hb _ hH).symm
  choose! ε hε using hunit
  let f : W → AddSubgroup W × ((𝓞 E)ˣ ⧸ congruenceUnits E N) :=
    fun x => (ringMultiples E x, QuotientGroup.mk (ε x))
  have hfin : (f '' L).Finite :=
    (hTfin.prod Set.finite_univ).subset (by rintro _ ⟨x, hx, rfl⟩; exact ⟨hT x hx, trivial⟩)
  have hP : ∀ x ∈ L, ∀ y ∈ L, f x = f y → ∃ γ ∈ latticeStab h La, γ • y = x := by
    intro x hx y hy hxy
    simp only [f, Prod.mk.injEq] at hxy
    obtain ⟨hR, hQ⟩ := hxy
    rw [QuotientGroup.eq] at hQ
    have hδ : (ε y)⁻¹ * ε x ∈ congruenceUnits E N := by
      have := inv_mem hQ
      rwa [mul_inv_rev, inv_inv] at this
    obtain ⟨γ, hγS, hγv⟩ := hγ _ hδ
    refine ⟨γ, hγS, ?_⟩
    have hx' := hε x hx
    have hy' := hε y hy
    rw [hR] at hx'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy.2
    have key : (((ε y)⁻¹ * ε x : (𝓞 E)ˣ) : 𝓞 E) * ((ε y : 𝓞 E)) = (ε x : 𝓞 E) := by
      rw [← Units.val_mul, mul_comm, mul_inv_cancel_left]
    have keyE : ((((ε y)⁻¹ * ε x : (𝓞 E)ˣ) : 𝓞 E) : E) * ((ε y : 𝓞 E) : E) = ((ε x : 𝓞 E) : E) := by
      rw [← key]
      rfl
    rw [← hc, unitary_smul_smul, hγv, smul_smul, mul_comm, ← smul_smul, hc,
      congrArg (fun t => ((((ε y)⁻¹ * ε x : (𝓞 E)ˣ) : 𝓞 E) : E) • t) hy', smul_smul, keyE, ← hx']
  obtain ⟨S, hS, hcov⟩ := exists_finset_of_finite_image L f hfin
    (fun y x => ∃ γ ∈ latticeStab h La, γ • y = x) hP
  exact ⟨S, hS.trans fun x hx => hx.1, fun x hx hxs => hcov x ⟨hx, hxs⟩⟩

theorem VectorOrbitsFinite.proof (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : LinePairOrbitsFinite.Statement h) (h₂ : IsotropicScaling.Statement h)
    (h₃ : BoundedIndexSubgroupsFinite.Statement W) (h₅ : LineIndexNeZero.Statement E W) :
    VectorOrbitsFinite.Statement h := by
  classical
  intro D La VV hLa hsub hiso hst ⟨C, hC⟩
  obtain ⟨Sp, hSp, hcov⟩ := h₁ D
  have hline : ∀ x ∈ VV, ∃ p ∈ Sp, ∃ g : h.unitaryGroup, g • p.1 = La ∧
      p.2.map ((g : W ≃ₗ[E] W) : W →ₗ[E] W) = Submodule.span E {x} := by
    intro x hx
    refine hcov La _ hLa ⟨finrank_span_singleton (hiso x hx).1, fun a ha c hc => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hc
    rw [h.toSesq.map_smulₛₗ a x, LinearMap.smul_apply, map_smul, (hiso x hx).2, smul_zero,
      smul_zero]
  choose! pf hpf gf hgf using hline
  have hfin : (pf '' VV).Finite := hSp.subset (by rintro _ ⟨x, hx, rfl⟩; exact hpf x hx)
  choose! rr hrr1 hrr2 using fun p (hp : p ∈ pf '' VV) => hp
  have hlines : ∀ p ∈ pf '' VV, ∃ S : Finset W, (S : Set W) ⊆ VV ∧ ∀ x ∈ VV,
      x ∈ Submodule.span E {rr p} → ∃ y ∈ S, ∃ γ ∈ latticeStab h La, γ • y = x :=
    fun p hp => line_vectorOrbits h h₂ h₃ h₅ hLa hsub hiso hC (hrr1 p hp)
  choose! Sl hSl1 hSl2 using hlines
  refine ⟨hfin.toFinset.biUnion Sl, ?_, fun x hx => ?_⟩
  · intro y hy
    obtain ⟨p, hp, hyp⟩ := Finset.mem_biUnion.1 hy
    exact hSl1 p (hfin.mem_toFinset.1 hp) hyp
  have hp : pf x ∈ pf '' VV := ⟨x, hx, rfl⟩
  set r := rr (pf x) with hr
  have hr1 : r ∈ VV := hrr1 _ hp
  have hr2 : pf r = pf x := hrr2 _ hp
  set γ₀ := gf r * (gf x)⁻¹ with hγ₀def
  have hγ₀ : γ₀ ∈ latticeStab h La := by
    refine MulAction.mem_stabilizer_iff.2 ?_
    rw [hγ₀def, mul_smul, inv_smul_eq_iff.2 (hgf x hx).1.symm, ← hr2]
    exact (hgf r hr1).1
  have hxm : x ∈ (pf x).2.map ((gf x : W ≃ₗ[E] W) : W →ₗ[E] W) := by
    rw [(hgf x hx).2]
    exact Submodule.mem_span_singleton_self x
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.1 hxm
  have hzx' : gf x • z = x := hzx
  have hγ₀x : γ₀ • x ∈ Submodule.span E {r} := by
    rw [hγ₀def, mul_smul, inv_smul_eq_iff.2 hzx'.symm, ← (hgf r hr1).2, hr2]
    exact Submodule.mem_map_of_mem hz
  obtain ⟨y, hy, γ, hγ, hγy⟩ := hSl2 _ hp _ (hst γ₀ hγ₀ x hx) hγ₀x
  refine ⟨y, Finset.mem_biUnion.2 ⟨pf x, hfin.mem_toFinset.2 hp, hy⟩, γ₀⁻¹ * γ,
    mul_mem (inv_mem hγ₀) hγ, ?_⟩
  rw [mul_smul, hγy, inv_smul_smul]

end Spaces

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
