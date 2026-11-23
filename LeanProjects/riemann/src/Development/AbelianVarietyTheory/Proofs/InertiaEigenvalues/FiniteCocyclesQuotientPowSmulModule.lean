import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1H2Local
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

theorem finite_of_finite_quotient_submodule {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    (S : Submodule R N) [Finite (N ⧸ S)] [Finite S] : Finite N := by
  classical
  let s := Function.surjInv (Submodule.Quotient.mk_surjective S)
  have hs : ∀ x : N, x - s (Submodule.Quotient.mk x) ∈ S := fun x =>
    (Submodule.Quotient.eq S).1 (Function.surjInv_eq (Submodule.Quotient.mk_surjective S) _).symm
  refine Finite.of_injective (fun x : N => ((Submodule.Quotient.mk x : N ⧸ S), (⟨_, hs x⟩ : S))) ?_
  intro x y h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2
  simpa using h2

theorem finite_cocycles_of_finite_h1 {R : Type*} [CommRing R] {H : Type*} [Group H] [TopologicalSpace H]
    {Q : Type*} [AddCommGroup Q] [Module R Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q]
    [ContinuousConstSMul R Q] [Finite Q] (σ : Representation R H Q) [Finite (H1 σ)] :
    Finite (Z1 σ) := by
  haveI : Finite ((B1 σ).comap (Z1 σ).subtype) := by
    haveI : Finite (B1 σ) := by
      haveI : Finite (Set.range (d0 σ)) := Set.finite_range _
      exact Finite.of_injective (fun x : B1 σ => (⟨x.1, x.2⟩ : Set.range (d0 σ)))
        (fun x y h => Subtype.ext (congrArg Subtype.val h))
    exact Finite.of_injective (fun x : (B1 σ).comap (Z1 σ).subtype => (⟨x.1.1, x.2⟩ : B1 σ))
      (fun x y h => by
        apply Subtype.ext; apply Subtype.ext
        have := congrArg Subtype.val h
        simpa using this)
  exact finite_of_finite_quotient_submodule ((B1 σ).comap (Z1 σ).subtype)

end GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.LocDualInt

def toZModRep {R H Q : Type*} [CommRing R] [Group H] [AddCommGroup Q] [Module R Q] (m : ℕ)
    [Module (ZMod m) Q] (τ : Representation R H Q) : Representation (ZMod m) H Q where
  toFun h := (τ h).toAddMonoidHom.toZModLinearMap m
  map_one' := LinearMap.ext fun x => by simp
  map_mul' g h := LinearMap.ext fun x => by simp [Module.End.mul_apply]

@[simp] theorem toZModRep_apply {R H Q : Type*} [CommRing R] [Group H] [AddCommGroup Q]
    [Module R Q] (m : ℕ) [Module (ZMod m) Q] (τ : Representation R H Q) (h : H) (x : Q) :
    toZModRep m τ h x = τ h x := rfl

section Transport

variable {R G H Q : Type*} [CommRing R] [Group G] [TopologicalSpace G] [Group H]
  [TopologicalSpace H] [AddCommGroup Q] [Module R Q] [TopologicalSpace Q]
  [IsTopologicalAddGroup Q] [ContinuousConstSMul R Q] (m : ℕ) [Module (ZMod m) Q]
  [ContinuousConstSMul (ZMod m) Q]

theorem contAction_toZModRep (τ : Representation R H Q) (hτ : ContAction τ) :
    ContAction (toZModRep m τ) := hτ

theorem cocycles_subset_image_toZModRestriction (i : G ≃ₜ* H) (τ : Representation R G Q) :
    (Z1 τ : Set (G → Q)) ⊆
      (fun f : H → Q => f ∘ i) '' (Z1 (toZModRep m (τ.comp i.symm.toMonoidHom)) : Set (H → Q)) := by
  intro f hf
  refine ⟨f ∘ i.symm, ⟨hf.1.comp i.symm.continuous, fun g h => ?_⟩, ?_⟩
  · show f (i.symm (g * h)) = f (i.symm g) + τ (i.symm g) (f (i.symm h))
    rw [map_mul, hf.2]
  · funext x
    simp

end Transport

end GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.LocDualInt

theorem finite_cocycles_quotient_pow_smul_module : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [CompactSpace M], FiniteDimensional ℚ_[p] K → (p : O) ∈ IsLocalRing.maximalIdeal O → ∀ (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (ρ : Representation O G M), ContAction ρ → ∀ ϖ : O, Irreducible ϖ → (∀ n : ℕ, IsOpen ((powSub (M := M) ϖ n : Submodule O M) : Set M)) → ∀ n : ℕ, (Z1 (quotRep ρ ϖ n) : Set (G → M ⧸ powSub (M := M) ϖ n)).Finite := by
  intro hT p _ K O _ _ _ G _ _ M _ _ _ _ _ _ hK hp i ρ hρ ϖ hϖ hopen n
  have hmk := Submodule.isOpenQuotientMap_mkQ (powSub (M := M) ϖ n)
  haveI hdisc : DiscreteTopology (M ⧸ powSub (M := M) ϖ n) := by
    rw [discreteTopology_iff_isOpen_singleton_zero, ← hmk.isQuotientMap.isOpen_preimage]
    convert hopen n using 1
    ext x
    simp [Submodule.Quotient.mk_eq_zero]
  haveI : CompactSpace (M ⧸ powSub (M := M) ϖ n) :=
    ⟨by simpa [hmk.surjective.range_eq] using isCompact_univ.image hmk.continuous⟩
  haveI : Finite (M ⧸ powSub (M := M) ϖ n) := finite_of_compact_of_discrete
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (M ⧸ powSub (M := M) ϖ 0) := by
      refine ⟨fun a b => ?_⟩
      induction a using Submodule.Quotient.induction_on with | _ x => ?_
      induction b using Submodule.Quotient.induction_on with | _ y => ?_
      rw [Submodule.Quotient.eq]
      exact mem_powSub.2 ⟨x - y, by simp⟩
    exact Set.Subsingleton.finite fun f _ g _ => Subsingleton.elim f g
  obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton'.1 (hϖ.maximalIdeal_eq ▸ hp))
  have kill : ∀ x : M ⧸ powSub (M := M) ϖ n, (p ^ n) • x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with | _ y => ?_
    rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    push_cast
    rw [← ha, mul_pow, mul_comm, mul_smul]
    exact smul_mem_powSub ϖ n _
  letI : Module (ZMod (p ^ n)) (M ⧸ powSub (M := M) ϖ n) := AddCommGroup.zmodModule kill
  haveI : ContinuousConstSMul (ZMod (p ^ n)) (M ⧸ powSub (M := M) ϖ n) :=
    ⟨fun _ => continuous_of_discreteTopology⟩
  have hcont : ContAction ((quotRep ρ ϖ n).comp i.symm.toMonoidHom) := by
    refine continuous_prod_of_discrete_right.2 fun q => ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    show Continuous fun g => quotRep ρ ϖ n (i.symm g) (Submodule.Quotient.mk x)
    simp only [quotRep_mk]
    exact hmk.continuous.comp (hρ.comp (i.symm.continuous.prodMk continuous_const))
  haveI := (GlobalTheory.finite_H1_H2_of_localTateDuality hT p K hK n (M ⧸ powSub (M := M) ϖ n)
    (toZModRep (p ^ n) ((quotRep ρ ϖ n).comp i.symm.toMonoidHom)) hn
    (contAction_toZModRep _ _ hcont)).1
  haveI := finite_cocycles_of_finite_h1 (toZModRep (p ^ n) ((quotRep ρ ϖ n).comp i.symm.toMonoidHom))
  exact ((Set.toFinite _).image _).subset (cocycles_subset_image_toZModRestriction (p ^ n) i (quotRep ρ ϖ n))

end GlobalTheory.LocDualInt
