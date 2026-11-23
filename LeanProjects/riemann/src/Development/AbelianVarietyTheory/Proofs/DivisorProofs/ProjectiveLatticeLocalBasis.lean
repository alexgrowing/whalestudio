import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)

namespace GlobalTheory.LocFreeSub

theorem exists_basis_near_prime : ∀ (R : Type) [CommRing R] [IsDomain R] (h : ℕ) (P : Submodule R (Fin h → R)), Module.Finite R P → Module.Projective R P → ∀ c : R, c ≠ 0 → (∀ x : Fin h → R, c • x ∈ P) → ∀ q : Ideal R, q.IsPrime → ∃ g ∉ q, ∃ b : Fin h → Fin h → R, (∀ l, b l ∈ P) ∧ (Matrix.of fun a l => b l a).det ≠ 0 ∧ ∀ u ∈ P, ∃ n : ℕ, g ^ n • u ∈ Submodule.span R (Set.range b) := by
  intro R _ _ h P hfin hproj c hc hcP q hq
  classical
  haveI : Module.FinitePresentation R P := Module.finitePresentation_of_projective _ _
  haveI : Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl P) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl P) (Localization.AtPrime q)
  have hr0 : r ≠ 0 := fun h0 => hr (h0 ▸ q.zero_mem)
  have hle : Submonoid.powers r ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hr0
  let L := Localization (Submonoid.powers r)
  let f := LocalizedModule.mkLinearMap (Submonoid.powers r) P
  have hinj : Function.Injective (algebraMap R L) := IsLocalization.injective L hle
  haveI : Nontrivial L := hinj.nontrivial
  haveI : Module.Finite L (LocalizedModule (Submonoid.powers r) P) :=
    Module.Finite.of_isLocalizedModule (Submonoid.powers r) f
  let ι := Module.Free.ChooseBasisIndex L (LocalizedModule (Submonoid.powers r) P)
  let β := Module.Free.chooseBasis L (LocalizedModule (Submonoid.powers r) P)
  have hlift : ∀ i, ∃ (m : P) (s : Submonoid.powers r), β i = LocalizedModule.mk m s := fun i =>
    LocalizedModule.induction_on (fun m s => ⟨m, s, rfl⟩) (β i)
  choose p s hps using hlift
  let w : ι → Lˣ := fun i => (IsLocalization.map_units L (s i)).unit
  let β' := β.unitsSMul w
  have hβ' : ∀ i, β' i = f (p i) := by
    intro i
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, IsUnit.unit_spec, algebraMap_smul, hps i,
      LocalizedModule.smul'_mk, LocalizedModule.mkLinearMap_apply]
    exact LocalizedModule.mk_cancel (s i) (p i)
  haveI : Finite ι := Module.Finite.finite_basis β
  letI : Fintype ι := Fintype.ofFinite ι
  have hpR : LinearIndependent R p := by
    have hL := β'.linearIndependent
    rw [linearIndependent_iff'] at hL ⊢
    intro t g hg i hi
    have h0 := hL t (fun i => algebraMap R L (g i)) (by
      have h1 := congrArg f hg
      rw [map_sum, map_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, algebraMap_smul, hβ' j]) i hi
    exact hinj (by rw [map_zero]; exact h0)
  let b₀ : ι → Fin h → R := fun i => (p i : Fin h → R)
  have hb₀ : LinearIndependent R b₀ := hpR.map' P.subtype P.ker_subtype
  have hspan : ∀ u ∈ P, ∃ n : ℕ, r ^ n • u ∈ Submodule.span R (Set.range b₀) := by
    intro u hu
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers r)
      (Finset.univ : Finset ι) (fun i => β'.repr (f ⟨u, hu⟩) i)
    choose z hz using fun i => hd i (Finset.mem_univ i)
    have h1 : f ((d : R) • (⟨u, hu⟩ : P)) = f (∑ i, z i • p i) := by
      rw [map_smul, map_sum]
      conv_lhs => rw [← β'.sum_repr (f ⟨u, hu⟩)]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← smul_assoc, ← hz i, algebraMap_smul, hβ' i]
    obtain ⟨e, he⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers r) h1
    obtain ⟨k, hk⟩ := (e * d).2
    refine ⟨k, ?_⟩
    have hk' : r ^ k = (e : R) * (d : R) := hk
    have he' : (e : R) • (d : R) • u = (e : R) • ∑ i, z i • b₀ i := by
      have h2 := congrArg P.subtype he
      rw [Submonoid.smul_def, Submonoid.smul_def, map_smul, map_smul, map_smul, map_sum] at h2
      simpa only [map_smul, Submodule.subtype_apply] using h2
    rw [hk', mul_smul, he']
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hcard : Fintype.card ι = h := by
    apply le_antisymm
    · simpa using hb₀.fintype_card_le_finrank
    · choose n hn using fun a : Fin h => hspan (c • Pi.basisFun R (Fin h) a) (hcP _)
      have hd0 : r ^ (∑ a, n a) * c ≠ 0 := mul_ne_zero (pow_ne_zero _ hr0) hc
      have hmem : ∀ a : Fin h, (r ^ (∑ a, n a) * c) • Pi.basisFun R (Fin h) a ∈
          Submodule.span R (Set.range b₀) := by
        intro a
        obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le
          (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a))
        rw [hm, add_comm, pow_add, mul_assoc, mul_smul, mul_smul]
        exact Submodule.smul_mem _ _ (hn a)
      have hli : LinearIndependent R
          (fun a : Fin h => (r ^ (∑ a, n a) * c) • Pi.basisFun R (Fin h) a) :=
        (Pi.basisFun R (Fin h)).linearIndependent.map'
          ((r ^ (∑ a, n a) * c) • (LinearMap.id : (Fin h → R) →ₗ[R] (Fin h → R)))
          (LinearMap.ker_eq_bot.mpr (smul_right_injective (Fin h → R) hd0))
      have hli' : LinearIndependent R
          (fun a : Fin h => (⟨_, hmem a⟩ : Submodule.span R (Set.range b₀))) :=
        LinearIndependent.of_comp (Submodule.span R (Set.range b₀)).subtype hli
      haveI : Module.Finite R (Submodule.span R (Set.range b₀)) :=
        Module.Finite.span_of_finite R (Set.finite_range b₀)
      have h3 := hli'.fintype_card_le_finrank
      rwa [finrank_span_eq_card hb₀, Fintype.card_fin] at h3
  let e : ι ≃ Fin h := Fintype.equivFinOfCardEq hcard
  have hb : LinearIndependent R (b₀ ∘ e.symm) := hb₀.comp e.symm e.symm.injective
  refine ⟨r, hr, b₀ ∘ e.symm, fun l => (p (e.symm l)).2, ?_, ?_⟩
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine hv0 (funext (Fintype.linearIndependent_iff.mp hb v ?_))
    funext a
    have h4 := congrFun hv a
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h4
  · intro u hu
    rw [e.symm.surjective.range_comp]
    exact hspan u hu

end GlobalTheory.LocFreeSub
