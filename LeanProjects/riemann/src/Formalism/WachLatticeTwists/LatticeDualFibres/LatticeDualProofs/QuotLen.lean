import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import Formalism.WachLatticeTwists.TorsionLengthCounts.RowCol
import Formalism.WachLatticeTwists.TorsionLengthCounts.SubmoduleLengthBoundStatement
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthEqKerAddRange

universe u

open Formalism.NG (KO annih)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

open Module

section

variable {O : Type u} [CommRing O]

theorem mem_mulSub {a : O} {M : Type u} [AddCommGroup M] [Module O M] (x : M) :
    x ∈ mulSub a M ↔ ∃ m, a • m = x := by
  simp only [mulSub, LinearMap.mem_range, LinearMap.lsmul_apply]

theorem length_quot_le_of_surj {a : O} {M M' : Type u} [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] (f : M →ₗ[O] M') (hf : Function.Surjective f) :
    Module.length O (M' ⧸ mulSub a M') ≤ Module.length O (M ⧸ mulSub a M) := by
  have hle : mulSub a M ≤ (mulSub a M').comap f := by
    intro x hx
    obtain ⟨m, rfl⟩ := (mem_mulSub x).1 hx
    exact (mem_mulSub _).2 ⟨f m, by rw [map_smul]⟩
  refine Module.length_le_of_surjective (Submodule.mapQ _ _ f hle) ?_
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem length_quot_le_add (a : O) {M : Type u} [AddCommGroup M] [Module O M]
    (Q : Submodule O M) :
    Module.length O (M ⧸ mulSub a M) ≤
      Module.length O (Q ⧸ mulSub a Q) + Module.length O ((M ⧸ Q) ⧸ mulSub a (M ⧸ Q)) := by
  have hle : mulSub a M ≤ (mulSub a (M ⧸ Q)).comap Q.mkQ := by
    intro x hx
    obtain ⟨m, rfl⟩ := (mem_mulSub x).1 hx
    exact (mem_mulSub _).2 ⟨Q.mkQ m, by rw [map_smul]⟩
  have hle' : mulSub a Q ≤ (mulSub a M).comap Q.subtype := by
    intro x hx
    obtain ⟨m, rfl⟩ := (mem_mulSub x).1 hx
    exact (mem_mulSub _).2 ⟨Q.subtype m, by rw [map_smul]⟩
  let f := Submodule.mapQ (mulSub a M) (mulSub a (M ⧸ Q)) Q.mkQ hle
  let g := Submodule.mapQ (mulSub a Q) (mulSub a M) Q.subtype hle'
  have hker : LinearMap.ker f ≤ LinearMap.range g := by
    intro x hx
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ x
    have h1 : (Submodule.Quotient.mk (Q.mkQ m) : (M ⧸ Q) ⧸ mulSub a (M ⧸ Q)) = 0 := hx
    obtain ⟨w, hw⟩ := (mem_mulSub _).1 ((Submodule.Quotient.mk_eq_zero _).1 h1)
    obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective _ w
    have h2 : m - a • m' ∈ Q := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
      rw [sub_eq_zero]
      exact hw.symm
    refine ⟨Submodule.Quotient.mk ⟨m - a • m', h2⟩, ?_⟩
    show (Submodule.Quotient.mk (m - a • m') : M ⧸ mulSub a M) = Submodule.Quotient.mk m
    rw [Submodule.Quotient.eq]
    refine (mem_mulSub _).2 ⟨-m', ?_⟩
    rw [smul_neg]; abel
  calc Module.length O (M ⧸ mulSub a M)
      = Module.length O (LinearMap.ker f) + Module.length O (LinearMap.range f) :=
        Formalism.NG.IdempotentNormalFormsRhoFacts.length_eq_ker_add_range f
    _ ≤ Module.length O (Q ⧸ mulSub a Q) + Module.length O ((M ⧸ Q) ⧸ mulSub a (M ⧸ Q)) := by
        refine add_le_add ?_ ?_
        · exact (Formalism.NG.IdempotentNormalFormsRhoFacts.length_mono hker).trans
            (Module.length_le_of_surjective g.rangeRestrict g.surjective_rangeRestrict)
        · exact Module.length_le_of_injective (LinearMap.range f).subtype
            (Submodule.injective_subtype _)

theorem length_coker_eq_ker (a : O) {M : Type u} [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) :
    Module.length O (M ⧸ mulSub a M) = Module.length O (LinearMap.ker (LinearMap.lsmul O M a)) := by
  have h1 := Formalism.NG.IdempotentNormalFormsRhoFacts.length_eq_ker_add_range (LinearMap.lsmul O M a)
  have h2 : Module.length O M = Module.length O (mulSub a M) + Module.length O (M ⧸ mulSub a M) :=
    Module.length_eq_add_of_exact (mulSub a M).subtype (mulSub a M).mkQ
      (mulSub a M).injective_subtype (mulSub a M).mkQ_surjective
      (LinearMap.exact_subtype_mkQ _)
  have hr : Module.length O (mulSub a M) ≠ ⊤ := by
    intro h
    rw [h, top_add] at h2
    exact hM h2
  have h3 : Module.length O (M ⧸ mulSub a M) + Module.length O (mulSub a M) =
      Module.length O (LinearMap.ker (LinearMap.lsmul O M a)) + Module.length O (mulSub a M) := by
    rw [add_comm, ← h2, h1]; rfl
  exact ENat.add_left_injective_of_ne_top hr h3

end

section DVR

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem KO_torsion (z : KO O) : ∃ c : O, c ≠ 0 ∧ c • z = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors O) x
  refine ⟨s, nonZeroDivisors.coe_ne_zero s, ?_⟩
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
  refine ⟨r, ?_⟩
  rw [Algebra.smul_def, mul_comm]
  exact hrs.symm

theorem pi_torsion {d : ℕ} (w : Fin d → KO O) : ∃ c : O, c ≠ 0 ∧ c • w = 0 := by
  choose c hc hc' using fun z : KO O => KO_torsion z
  refine ⟨∏ i, c (w i), Finset.prod_ne_zero_iff.2 fun i _ => hc _, ?_⟩
  funext i
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun i => c (w i)) (Finset.mem_univ i)
  rw [Pi.smul_apply, Pi.zero_apply, hr, mul_comm, mul_smul, hc', smul_zero]

theorem span_killed {N : Type u} [AddCommGroup N] [Module O N]
    (ht : ∀ x : N, ∃ c : O, c ≠ 0 ∧ c • x = 0) (t : Finset N) :
    ∃ c : O, c ≠ 0 ∧ ∀ n ∈ Submodule.span O (t : Set N), c • n = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert x t _ ih =>
    obtain ⟨c, hc, h⟩ := ih
    obtain ⟨c', hc', h'⟩ := ht x
    refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
    intro n hn
    rw [Finset.coe_insert, Submodule.mem_span_insert] at hn
    obtain ⟨r, z, hz, rfl⟩ := hn
    rw [smul_add, mul_smul, smul_comm c' r x, h', smul_zero, smul_zero, zero_add, mul_comm,
      mul_smul, h z hz, smul_zero]

theorem length_quot_of_KO {Q N : Type u} [AddCommGroup Q] [Module O Q] [Module.Finite O Q]
    [AddCommGroup N] [Module O N] {d : ℕ} (ι : N →ₗ[O] (Fin d → KO O)) (hι : Function.Injective ι)
    (δ : N →ₗ[O] Q) (hδ : Function.Surjective δ) (ℓ e : ℕ) :
    Module.length O (Q ⧸ mulSub ((ℓ : O) ^ e) Q) ≤ (d : ℕ∞) * ((e : ℕ∞) * eO O ℓ) := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule O Q).FG)
  let f : Q → N := Function.surjInv hδ
  have hf : ∀ x, δ (f x) = x := Function.surjInv_eq hδ
  let t : Finset N := s.image f
  let N₂ : Submodule O N := Submodule.span O (t : Set N)
  have ht : ∀ x : N, ∃ c : O, c ≠ 0 ∧ c • x = 0 := by
    intro x
    obtain ⟨c, hc, h⟩ := pi_torsion (ι x)
    refine ⟨c, hc, hι ?_⟩
    rw [map_smul, h, map_zero]
  obtain ⟨c, hc, hkill⟩ := span_killed ht t
  have hfg : N₂.FG := ⟨t, rfl⟩
  have : Module.Finite O N₂ := Module.Finite.iff_fg.2 hfg

  have hfin : Module.length O N₂ ≠ ⊤ := by
    obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin' O N₂
    have h1 := Formalism.RepresentationBoundsCohomology.RowCol.length_le_of_killed c g hg (by
      intro x
      exact Subtype.ext (hkill x x.2))
    rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, Fintype.card_fin] at h1
    have h2 : IsDiscreteValuationRing.addVal O c ≠ ⊤ :=
      fun h' => hc (IsDiscreteValuationRing.addVal_eq_top_iff.1 h')
    intro h
    rw [h, top_le_iff] at h1
    lift IsDiscreteValuationRing.addVal O c to ℕ using h2 with v
    exact ENat.natCast_ne_top (k * v) (by exact_mod_cast h1)

  let δ₂ : N₂ →ₗ[O] Q := δ ∘ₗ N₂.subtype
  have hδ₂ : Function.Surjective δ₂ := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype, eq_top_iff, ← hs,
      Submodule.span_le]
    intro x hx
    exact ⟨f x, Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx)), hf x⟩
  refine (length_quot_le_of_surj δ₂ hδ₂).trans ?_
  rw [length_coker_eq_ker _ hfin]

  let κ := LinearMap.ker (LinearMap.lsmul O N₂ ((ℓ : O) ^ e))
  let j : κ →ₗ[O] (Fin d → KO O) := ι ∘ₗ N₂.subtype ∘ₗ κ.subtype
  have hj : Function.Injective j :=
    hι.comp (N₂.injective_subtype.comp κ.injective_subtype)
  have h0 := Formalism.RepresentationBoundsCohomology.submoduleLengthBound_statement O (Fin d) (LinearMap.range j) ℓ e (by
    rintro _ ⟨x, rfl⟩
    rw [← map_smul]
    have : ((ℓ : O) ^ e) • x = 0 := Subtype.ext x.2
    rw [this, map_zero])
  rw [Fintype.card_fin] at h0
  exact (Module.length_le_of_injective j.rangeRestrict (by
    intro x y hxy
    exact hj (congrArg Subtype.val hxy))).trans h0

end DVR

theorem locQuotLen : StatLocQuotLen.{u} := by
  intro O M _ _ _ _ _ _ d N δ hδ ℓ e
  let Q := Submodule.torsion O M
  have hA := length_quot_le_add ((ℓ : O) ^ e) Q

  have hT0 : finrank O Q = 0 := by
    rw [Module.finrank_eq_zero_iff]
    intro x
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (x : M)).mp x.2
    refine ⟨a, nonZeroDivisors.coe_ne_zero a, ?_⟩
    apply Subtype.ext
    rw [Submodule.coe_smul, Submodule.coe_zero]
    exact ha
  have hrank : finrank O (M ⧸ Q) = finrank O M := by
    have h := Submodule.finrank_quotient_add_finrank Q
    rw [hT0, add_zero] at h
    exact h
  have hB := Formalism.RepresentationBoundsCohomology.rowColength O (M ⧸ Q) (mulSub ((ℓ : O) ^ e) (M ⧸ Q)) ℓ e
    (fun m => (mem_mulSub _).2 ⟨m, rfl⟩)
  have htors : Module.length O (Submodule.torsion O (M ⧸ Q)) = 0 := by
    rw [Submodule.QuotientTorsion.torsion_eq_bot]
    exact Module.length_eq_zero
  rw [htors, add_zero, hrank] at hB

  let N' : Submodule O N := Q.comap δ
  let δ' : N' →ₗ[O] Q := δ.restrict (fun x hx => hx)
  have hδ' : Function.Surjective δ' := by
    intro x
    obtain ⟨n, hn⟩ := hδ x.2
    exact ⟨⟨n, by show δ n ∈ Q; rw [hn]; exact x.2⟩, Subtype.ext hn⟩
  have hC := length_quot_of_KO (N.subtype ∘ₗ N'.subtype)
    (N.injective_subtype.comp N'.injective_subtype) δ' hδ' ℓ e
  refine hA.trans ((add_le_add hC hB).trans (le_of_eq ?_))
  rw [eO, Nat.cast_add, add_mul, add_comm]

end Formalism.RepresentationBoundsCohomology.LOC
