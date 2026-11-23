import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.RepScalar
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcSumEqOfMk
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SphComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem integers_isLocalRing : IsLocalRing 𝒪[k] := (inferInstance : IsDiscreteValuationRing 𝒪[k]).toIsLocalRing
attribute [local instance] integers_isLocalRing

private theorem valuation_unif_eq_uniformizer : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  have h0 : x ≠ 0 := by
    rintro rfl
    exact uniformizer_pos.ne (by simpa using hx)
  exact Classical.epsilon_spec (p := fun x : kˣ => valuation k (x : k) = uniformizer k) ⟨Units.mk0 x h0, hx⟩

private theorem mem_maximal_pow_iff_valuation (c : ℕ) (x : 𝒪[k]) :
    x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c ↔ valuation k (x : k) ≤ uniformizer k ^ c := by
  have hI := Valuation.integer.integers (valuation k)
  let p : 𝒪[k] := ⟨unif k, (valuation_unif_eq_uniformizer.trans_lt uniformizer_lt_one).le⟩
  have hp : valuation k (algebraMap 𝒪[k] k p) = uniformizer k := valuation_unif_eq_uniformizer
  have e : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {p} := by
    ext y
    rw [← IsLocalRing.residue_eq_zero_iff, GlobalTheory.StepData.residue_eq_zero_iff_lt, Ideal.mem_span_singleton,
      hI.dvd_iff_le, hp, le_uniformizer_iff]
    rfl
  rw [e, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hI.dvd_iff_le, map_pow, map_pow, hp]
  rfl

private theorem mem_Kc_iff' {c : ℕ} {g : GL (Fin n) k} :
    g ∈ Kc k n c ↔ g ∈ KO k (Fin n) ∧ ∀ i j, valuation k ((g.val - 1) i j) ≤ uniformizer k ^ c := by
  have key : ∀ u : GL (Fin n) 𝒪[k],
      u ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))).ker ↔
      ∀ i j, valuation k (((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u).val - 1) i j) ≤ uniformizer k ^ c := by
    intro u
    rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
    refine forall₂_congr fun i j => ?_
    have e : ((1 : GL (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ c)).val) i j =
        Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := by
      simp only [Units.val_one, Matrix.one_apply]; split_ifs <;> simp
    rw [e]
    refine (Ideal.Quotient.eq.trans (mem_maximal_pow_iff_valuation c _)).trans (iff_of_eq ?_)
    congr 2
    simp only [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> simp <;> rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, rfl⟩, (key u).1 hu⟩
  · rintro ⟨⟨u, rfl⟩, hu⟩
    exact ⟨u, (key u).2 hu, rfl⟩

private theorem congruence_subgroup_isOpen (c : ℕ) : IsOpen (Kc k n c : Set (GL (Fin n) k)) := by
  have e : (Kc k n c : Set (GL (Fin n) k)) = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin n) k => (g.val - 1) i j) ⁻¹' {x | valuation k x ≤ uniformizer k ^ c} := by
    ext g; simp only [SetLike.mem_coe, mem_Kc_iff', Set.mem_iInter, Set.mem_inter_iff]; rfl
  rw [e]
  refine GlobalTheory.SplitFlip.isOpen_KO.inter <|
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.preimage ?_ ?_
  · have := Units.continuous_val (M := Matrix (Fin n) (Fin n) k)
    fun_prop
  · have h0 : (valuation k).restrict ((unif k : k) ^ c) ≠ 0 := by simp
    simpa only [Valuation.restrict_le_iff, map_pow (valuation k), valuation_unif_eq_uniformizer] using Valuation.isOpen_closedBall h0

end SlopeTestRemainingChoices

private theorem eigenspace_one_eq_fixed {H M : Type} [Group H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M)
    (K : Subgroup H) : GlobalTheory.PRep.eig ρ K 1 = fixd ρ K := by
  ext v
  constructor
  · intro hv u hu
    have h := hv ⟨u, hu⟩
    simpa using h
  · intro hv u
    have h := hv u u.2
    simpa using h

theorem UpperTheory.V.Hi.partUR2Abs :
    ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GLw n w) M) (Z : Submodule ℂ M) (τ : SmIrr (GLw n w)), IsoSum ρ Z τ →
    (∀ K : Subgroup (GLw n w), IsCompact (K : Set (GLw n w)) → Z ⊓ fixd ρ K ≠ ⊥ → fixd τ.ρ K ≠ ⊥) ∧
    (∀ (j : ℕ) (a : ℂ), (∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v) → ∀ z ∈ Z ⊓ fixd ρ (KO (w.adicCompletion L) (Fin n)), sphOp ρ j z = a • z) ∧
    (∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (ρ' : Representation ℂ (GLw n w) M') (f : M →+ M'), (∀ g v, f (ρ g v) = ρ' g (f v)) → ∀ (j : ℕ) v, f (sphOp ρ j v) = sphOp ρ' j (f v)) ∧
    ∀ c : ℕ, IsCompact (Kc (w.adicCompletion L) n c : Set (GLw n w)) := by
  intro L _ _ n w M _ _ ρ Z τ hZ
  have hnat : ∀ (N N' : Type) [AddCommGroup N] [Module ℂ N] [AddCommGroup N'] [Module ℂ N']
      (σ : Representation ℂ (GLw n w) N) (σ' : Representation ℂ (GLw n w) N') (f : N →+ N'),
      (∀ g v, f (σ g v) = σ' g (f v)) → ∀ (j : ℕ) v, f (sphOp σ j v) = sphOp σ' j (f v) := by
    intro N N' _ _ _ _ σ σ' f hf j v
    exact (dcSum ℂ _ N σ _ _ _ ((sphComm _ n ℂ N σ).1 _)).2.2.2 ℂ N' σ' f hf v
  have key := fun (K : Subgroup (GLw n w)) (hK : IsCompact (K : Set (GLw n w))) =>
    UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.repScalar ρ τ.ρ τ.smooth Z hZ K 1 hK (by simp)
  simp only [eigenspace_one_eq_fixed] at key
  refine ⟨fun K hK => (key K hK).1, fun j a ha => ?_, fun M' _ _ ρ' => hnat M M' ρ ρ', fun c => ?_⟩
  · refine (key _ GlobalTheory.SplitFlip.isCompact_KO).2 (sphOp ρ j) (sphOp τ.ρ j) a (fun f v _ => ?_) ha
    exact (hnat _ _ τ.ρ ρ f.1.toAddMonoidHom f.2.1 j v).symm
  · exact GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (congruence_subgroup_isOpen c))
      fun g hg => (mem_Kc_iff'.1 hg).1
