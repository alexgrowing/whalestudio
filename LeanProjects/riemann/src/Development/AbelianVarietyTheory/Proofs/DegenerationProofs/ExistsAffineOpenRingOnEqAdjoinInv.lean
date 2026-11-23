import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRingHomOfMulPowMem

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

section

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_of_mul_pow_mem_of_inv_mem {S : Subalgebra o Ω} {d x : Ω} (hd : d ≠ 0) (hi : d⁻¹ ∈ S) {n : ℕ}
    (h : x * d ^ n ∈ S) : x ∈ S := by
  have := S.mul_mem h (S.pow_mem hi n)
  rwa [_root_.mul_assoc, ← mul_pow, mul_inv_cancel₀ hd, one_pow, _root_.mul_one] at this

theorem exists_mul_eq_of_eq_div {R : Subalgebra o Ω} (h : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (x : Ω) :
    ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h x
  by_cases h0 : b = 0
  · exact ⟨0, R.zero_mem, 1, R.one_mem, one_ne_zero, by simp [h0]⟩
  · exact ⟨a, ha, b, hb, h0, div_mul_cancel₀ a h0⟩

theorem exists_adjoin_inv_eq (R B : Subalgebra o Ω) (A : Set Ω) (hR : R.FG) (hB : B.FG)
    (hRf : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a)
    (hBf : ∀ x : Ω, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) (hA : A.Finite) :
    ∃ a ∈ R, ∃ c ∈ B, a ≠ 0 ∧ c ≠ 0 ∧
      Algebra.adjoin o (insert c⁻¹ (B : Set Ω)) = Algebra.adjoin o (insert a⁻¹ (R : Set Ω)) ∧
      A ⊆ Algebra.adjoin o (insert a⁻¹ (R : Set Ω)) := by
  obtain ⟨d, hdR, hd0, hd⟩ := exists_mul_pow_mem_of_fg (B ⊔ Algebra.adjoin o A) R
    (hB.sup (Subalgebra.fg_def.2 ⟨_, hA, rfl⟩)) hRf
  obtain ⟨c, hcB, hc0, hc⟩ := exists_mul_pow_mem_of_fg (R ⊔ Algebra.adjoin o {d⁻¹}) B
    (hR.sup (Subalgebra.fg_def.2 ⟨_, Set.finite_singleton _, rfl⟩)) hBf
  obtain ⟨m, hm⟩ := hd c (le_sup_left (a := B) hcB)
  have ha0 : d * (c * d ^ m) ≠ 0 := mul_ne_zero hd0 (mul_ne_zero hc0 (pow_ne_zero _ hd0))
  set S := Algebra.adjoin o (insert (d * (c * d ^ m))⁻¹ (R : Set Ω)) with hS
  set S' := Algebra.adjoin o (insert c⁻¹ (B : Set Ω)) with hS'
  have hRS : ∀ x ∈ R, x ∈ S := fun x hx => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
  have haS : (d * (c * d ^ m))⁻¹ ∈ S := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hdS : d⁻¹ ∈ S := by
    have := S.mul_mem haS (hRS _ hm)
    convert this using 1
    field_simp
  have hcS : c⁻¹ ∈ S := by
    have := S.mul_mem haS (hRS _ (R.mul_mem hdR (R.pow_mem hdR m)))
    convert this using 1
    field_simp
  have h1 : ∀ x ∈ B ⊔ Algebra.adjoin o A, x ∈ S := fun x hx => by
    obtain ⟨n, hn⟩ := hd x hx
    exact mem_of_mul_pow_mem_of_inv_mem hd0 hdS (hRS _ hn)
  have hcS' : c⁻¹ ∈ S' := Algebra.subset_adjoin (Set.mem_insert _ _)
  have h2 : ∀ x ∈ R ⊔ Algebra.adjoin o {d⁻¹}, x ∈ S' := fun x hx => by
    obtain ⟨n, hn⟩ := hc x hx
    exact mem_of_mul_pow_mem_of_inv_mem hc0 hcS' (Algebra.subset_adjoin (Set.mem_insert_of_mem _ hn))
  have hdS' : d⁻¹ ∈ S' := h2 _ (le_sup_right (a := R) (Algebra.subset_adjoin (Set.mem_singleton _)))
  refine ⟨_, R.mul_mem hdR hm, c, hcB, ha0, hc0, le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_),
    fun x hx => h1 x (le_sup_right (a := B) (Algebra.subset_adjoin hx))⟩
  · rintro x (rfl | hx)
    · exact hcS
    · exact h1 x (le_sup_left (a := B) hx)
  · rintro x (rfl | hx)
    · have := S'.mul_mem hdS' (S'.mul_mem hcS' (S'.pow_mem hdS' m))
      rwa [inv_pow, ← mul_inv, ← mul_inv] at this
    · exact h2 x (le_sup_left (a := R) hx)

namespace RatModel

variable {M : RatModel o Ω}

theorem fg_ringOn {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) :
    (M.ringOn V).FG := by
  have := M.lft
  have h1 : (M.s.appLE ⊤ V le_top).hom.FiniteType := M.s.finiteType_appLE (isAffineOpen_top _) hV _
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective
  have h3 : (M.sectionsEquiv V hne).toRingHom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (M.sectionsEquiv V hne).surjective
  have h4 := h3.comp (h1.comp h2)
  have e : (M.sectionsEquiv V hne).toRingHom.comp ((M.s.appLE ⊤ V le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom) = algebraMap o (M.ringOn V) :=
    RingHom.ext fun a => Subtype.ext ((coe_sectionsEquiv V hne _).trans (M.valF_constFn hne a))
  rw [e, RingHom.finiteType_algebraMap] at h4
  exact (Subalgebra.fg_iff_finiteType _).2 h4

theorem nonempty_basicOpen {V : M.Z.Opens} (hne : (V : Set M.Z).Nonempty) {g : Γ(M.Z, V)}
    (hg : valF M.pt V g ≠ 0) : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  apply hg
  rw [(basicOpen_eq_bot_iff g).1 (SetLike.coe_injective h), ← M.res_apply V hne, map_zero]

theorem ringOn_basicOpen {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) {g : Γ(M.Z, V)}
    (hg0 : valF M.pt V g ≠ 0) :
    M.ringOn (M.Z.basicOpen g) = Algebra.adjoin o (insert (valF M.pt V g)⁻¹ (M.ringOn V : Set Ω)) := by
  have hg := nonempty_basicOpen hne hg0
  refine le_antisymm (fun x hx => ?_) (Algebra.adjoin_le ?_)
  · obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hg).1 hx
    have := hV.isLocalization_basicOpen g
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g f
    have h1 := congrArg (M.res _ hg) ha
    have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
      fun t => M.res_resG (M.Z.basicOpen_le g) hg t
    rw [map_mul, map_pow, h2, h2, res_apply, res_apply, res_apply] at h1
    refine mem_of_mul_pow_mem_of_inv_mem hg0 (Algebra.subset_adjoin (Set.mem_insert _ _)) (n := n) ?_
    rw [h1]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ((mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩))
  · rintro x (rfl | hx)
    · exact mem_ringOn.2 fun z hz =>
        ((isUnit_O_iff _).1 ((isUnit_valF_iff (M.Z.basicOpen_le g hz) g).2 hz)).2
    · exact ringOn_anti (M.Z.basicOpen_le g) hx

end RatModel

end

theorem exists_affineOpen_ringOn_eq_adjoin_inv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (R : Subalgebra o Ω) (A : Set Ω), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) → A.Finite → ∀ W : M.Z.Opens, (W : Set M.Z).Nonempty → ∃ (U₀ : M.Z.Opens) (a : Ω), U₀ ≤ W ∧ (U₀ : Set M.Z).Nonempty ∧ IsAffineOpen U₀ ∧ a ∈ R ∧ a ≠ 0 ∧ M.ringOn U₀ = Algebra.adjoin o (insert a⁻¹ (R : Set Ω)) ∧ A ⊆ M.ringOn U₀ := by
  intro o Ω _ _ _ M R A hR hRf hA W ⟨w, hw⟩
  obtain ⟨V, hV, hwV, hVW⟩ := exists_isAffineOpen_mem_and_subset (U := W) hw
  have hne : (V : Set M.Z).Nonempty := ⟨w, hwV⟩
  obtain ⟨a, ha, c, hc, ha0, hc0, he, hAS⟩ := exists_adjoin_inv_eq R (M.ringOn V) A hR
    (RatModel.fg_ringOn hV hne) (exists_mul_eq_of_eq_div hRf) (exists_mul_eq_of_eq_div fun x => by
      obtain ⟨a, b, -, h⟩ := RatModel.exists_eq_div hV hne x
      exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩, _,
        (RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩, h⟩) hA
  obtain ⟨g, rfl⟩ := (RatModel.mem_ringOn_iff_exists hne).1 hc
  have h := (RatModel.ringOn_basicOpen hV hne hc0).trans he
  exact ⟨M.Z.basicOpen g, a, (M.Z.basicOpen_le g).trans hVW, RatModel.nonempty_basicOpen hne hc0,
    hV.basicOpen g, ha, ha0, h, h ▸ hAS⟩

end GlobalTheory.ZH
