import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualLatticeModPrime
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace DualLatticeModPrimeAlt

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

abbrev locAt (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors

theorem exists_smul_mem (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (L : Submodule (𝓞 K) (Fin i → K)) {x : Fin i → K}
    (hx : x ∈ Submodule.span (locAt 𝔭) (L : Set (Fin i → K))) :
    ∃ s ∈ 𝔭.primeCompl, s • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, 𝔭.primeCompl.one_mem, by rwa [one_smul]⟩
  | zero => exact ⟨1, 𝔭.primeCompl.one_mem, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s₁, hs₁, hx⟩ := hx
    obtain ⟨s₂, hs₂, hy⟩ := hy
    refine ⟨s₁ * s₂, 𝔭.primeCompl.mul_mem hs₁ hs₂, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem _ hx
    · rw [mul_smul]
      exact L.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl a
    refine ⟨q * s, 𝔭.primeCompl.mul_mem q.2 hs, ?_⟩
    have hq : (q : 𝓞 K) • (IsLocalization.mk' (locAt 𝔭) p q) = algebraMap (𝓞 K) (locAt 𝔭) p := by
      rw [Algebra.smul_def, mul_comm, IsLocalization.mk'_spec]
    have e : (q * s) • (IsLocalization.mk' (locAt 𝔭) p q • x) = p • (s • x) := by
      rw [mul_comm, mul_smul, ← smul_assoc (q : 𝓞 K), hq, algebraMap_smul, smul_comm]
    rw [e]
    exact L.smul_mem _ hx

theorem span_dual_eq_top (F : HermLattice K i) :
    Submodule.span K (DualLatticeIndexAlt.dual F.lattice : Set (Fin i → K)) = ⊤ := by
  obtain ⟨e, he0, hle⟩ := DualLatticeIndexAlt.exists_le_box F.lattice F.fg
  have heK : algebraMap (𝓞 K) K e ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr he0
  have hbox : DualLatticeIndexAlt.box (i := i) (algebraMap (𝓞 K) K e) ≤ DualLatticeIndexAlt.dual F.lattice := by
    have := DualLatticeIndexAlt.dual_anti hle
    rwa [DualLatticeIndexAlt.dual_box (inv_ne_zero heK), inv_inv] at this
  rw [eq_top_iff, ← (Pi.basisFun K (Fin i)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hj : (Pi.single j (algebraMap (𝓞 K) K e) : Fin i → K) ∈ DualLatticeIndexAlt.dual F.lattice := by
    refine hbox (DualLatticeIndexAlt.mem_box.mpr fun l => ?_)
    by_cases hl : l = j
    · subst hl
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hl]⟩
  have e1 : Pi.basisFun K (Fin i) j = (algebraMap (𝓞 K) K e)⁻¹ • (Pi.single j (algebraMap (𝓞 K) K e) : Fin i → K) := by
    ext l
    by_cases hl : l = j
    · subst hl
      simp [heK]
    · simp [Pi.basisFun_apply, hl]
  rw [SetLike.mem_coe, e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hj)

theorem dual_le_span (F : HermLattice K i) :
    ∃ u : Fin i → Fin i → K, DualLatticeIndexAlt.dual F.lattice ≤ Submodule.span (𝓞 K) (Set.range u) := by
  obtain ⟨e, he0, hle⟩ := DualLatticeIndexAlt.exists_box_le F.lattice F.span_eq
  have heK : algebraMap (𝓞 K) K e ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr he0
  refine ⟨fun j => Pi.single j (algebraMap (𝓞 K) K e)⁻¹, fun x hx => ?_⟩
  have hx' := DualLatticeIndexAlt.dual_anti hle hx
  rw [DualLatticeIndexAlt.dual_box heK, DualLatticeIndexAlt.mem_box] at hx'
  choose a ha using hx'
  have e1 : x = ∑ j, a j • (Pi.single j (algebraMap (𝓞 K) K e)⁻¹ : Fin i → K) := by
    ext l
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact (ha l).symm
  rw [e1]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end DualLatticeModPrimeAlt

open DualLatticeModPrimeAlt in

theorem DualLatticeModPrime.proof : DualLatticeModPrime.Statement := by
  intro K _ _ i F 𝔭 h𝔭
  classical
  have hbot : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField K)
  have : IsDiscreteValuationRing (locAt 𝔭) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hbot (locAt 𝔭)
  set D := DualLatticeIndexAlt.dual F.lattice
  set DA := Submodule.span (locAt 𝔭) (D : Set (Fin i → K))
  obtain ⟨u, hu⟩ := dual_le_span F
  have hDA : DA ≤ Submodule.span (locAt 𝔭) (Set.range u) :=
    Submodule.span_le.mpr fun x hx =>
      Submodule.span_le_restrictScalars (𝓞 K) (locAt 𝔭) _ (hu hx)
  have := isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range u)) (R := locAt 𝔭)
  have : Module.Finite (locAt 𝔭) DA := Module.Finite.iff_fg.mpr (isNoetherian_submodule.mp this DA hDA)
  have : Module.IsTorsionFree (locAt 𝔭) DA := inferInstance
  let b := Module.Free.chooseBasis (locAt 𝔭) DA
  have hspan : Submodule.span K (Set.range fun j => (b j : Fin i → K)) = ⊤ := by
    rw [eq_top_iff, ← span_dual_eq_top F, Submodule.span_le]
    intro d hd
    have e0 : d = ∑ j, ((b.repr ⟨d, Submodule.subset_span hd⟩ j • b j : DA) : Fin i → K) := by
      rw [← Submodule.coe_sum, b.sum_repr]
    rw [e0, SetLike.mem_coe]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Submodule.coe_smul]
    exact Submodule.span_le_restrictScalars (locAt 𝔭) K _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hcard : Fintype.card (Fin i) ≤ Fintype.card (Module.Free.ChooseBasisIndex (locAt 𝔭) DA) := by
    have := finrank_range_le_card (R := K) fun j => (b j : Fin i → K)
    rw [Set.finrank, hspan, finrank_top, Module.finrank_fin_fun] at this
    simpa using this
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
  let ρ : locAt 𝔭 →+* 𝓞 K ⧸ 𝔭 := IsLocalization.lift (M := 𝔭.primeCompl) (g := Ideal.Quotient.mk 𝔭)
    fun s => by
      obtain ⟨c, hc⟩ := Ideal.Quotient.exists_inv (I := 𝔭) (a := Ideal.Quotient.mk 𝔭 s)
        fun h => s.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
      exact ⟨⟨_, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩
  have hρ : ∀ a, ρ (algebraMap (𝓞 K) (locAt 𝔭) a) = Ideal.Quotient.mk 𝔭 a := fun a =>
    IsLocalization.lift_eq _ _
  have incl : ∀ φ : dualLattice F, (φ : Fin i → K) ∈ DA := fun φ => Submodule.subset_span φ.2
  let ι : dualLattice F →+ DA := AddMonoidHom.mk' (fun φ => ⟨φ, incl φ⟩) fun _ _ => rfl
  let τ : DA →+ (Fin i → 𝓞 K ⧸ 𝔭) := AddMonoidHom.mk' (fun x l => ρ (b.repr x (g l)))
    fun x y => by funext l; simp [map_add]
  have hsmul : ∀ (μ : 𝓞 K) (x : DA), ((algebraMap (𝓞 K) (locAt 𝔭) μ • x : DA) : Fin i → K) =
      algebraMap (𝓞 K) K μ • (x : Fin i → K) := fun μ x => by
    rw [Submodule.coe_smul, algebraMap_smul, algebraMap_smul]
  refine ⟨τ.comp ι, ?_, ?_⟩
  · intro v
    let w : Module.Free.ChooseBasisIndex (locAt 𝔭) DA → 𝓞 K ⧸ 𝔭 := Function.extend g v 0
    choose a ha using fun j => Ideal.Quotient.mk_surjective (I := 𝔭) (w j)
    let x : DA := ∑ j, algebraMap (𝓞 K) (locAt 𝔭) (a j) • b j
    have hx : ∀ j, b.repr x j = algebraMap (𝓞 K) (locAt 𝔭) (a j) := by
      intro j
      simp only [x, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem 𝔭 D x.2
    have hs0 : Ideal.Quotient.mk 𝔭 s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    obtain ⟨c, hc⟩ := Ideal.Quotient.exists_inv hs0
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (I := 𝔭) c
    refine ⟨⟨t • s • (x : Fin i → K), D.smul_mem t hsx⟩, ?_⟩
    have e1 : ι ⟨t • s • (x : Fin i → K), D.smul_mem t hsx⟩ = algebraMap (𝓞 K) (locAt 𝔭) (t * s) • x := by
      apply Subtype.ext
      rw [hsmul, algebraMap_smul, mul_smul]
      rfl
    funext l
    have key : ∀ y : DA, τ y l = ρ (b.repr y (g l)) := fun _ => rfl
    rw [AddMonoidHom.comp_apply, e1, key, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hρ, hx, hρ,
      map_mul, ht, mul_comm c, hc, one_mul, ha]
    exact g.injective.extend_apply _ _ _
  · intro μ φ ψ h
    have e1 : ι ψ = algebraMap (𝓞 K) (locAt 𝔭) μ • ι φ := by
      apply Subtype.ext
      rw [hsmul]
      exact h
    funext l
    have key : ∀ x : DA, τ x l = ρ (b.repr x (g l)) := fun _ => rfl
    rw [Pi.smul_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, e1, key, key, map_smul,
      Finsupp.smul_apply, smul_eq_mul, map_mul, hρ, smul_eq_mul]

end

end GroundTheory.Heights₂.Heights
