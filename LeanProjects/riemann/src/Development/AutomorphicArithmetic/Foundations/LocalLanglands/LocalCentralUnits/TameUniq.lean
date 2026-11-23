import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.EquivariantPartsOfFiniteType
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.PairingFactorsThroughPeriods
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.MemOfTameGeneratorFrobenius
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsUnitRho

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open PositivityTheory.Rg.DzCount

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Fields

variable {g n : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]

private theorem pow_period (hn : 0 < n) (hr : Module.finrank (ZMod g) K = n) (z : Kˣ) :
    z ^ g ^ n = z := by
  have h1 : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hr ▸ hn)
  have h2 : Finite K := Module.finite_of_finite (ZMod g)
  have h3 : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod g) (V := K), ZMod.card, hr]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, ← hc, FiniteField.pow_card]

private theorem prod_shift {M : Type*} [CommMonoid M] {n : ℕ} (hn : 0 < n) (f : ℕ → M)
    (hf : ∀ i, f (i + n) = f i) (j : ℕ) :
    ∏ i ∈ Finset.range n, f (i + j) = ∏ i ∈ Finset.range n, f i := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← ih, Finset.prod_range_succ (fun i => f (i + (j + 1))),
      Finset.prod_range_succ' (fun i => f (i + j))]
    have e1 : f (m + (j + 1)) = f (0 + j) := by
      have := hf j
      rw [show j + (m + 1) = m + (j + 1) by omega] at this
      simpa using this
    rw [e1]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    omega

private theorem orbit_of_sums (hn : 0 < n) (θ θ' : Kˣ →* ℂˣ)
    (h : ∀ z : Kˣ, ∑ i ∈ Finset.range n, ((θ (z ^ g ^ i) : ℂˣ) : ℂ) =
      ∑ i ∈ Finset.range n, ((θ' (z ^ g ^ i) : ℂˣ) : ℂ)) :
    ∃ j < n, θ' = θ ^ g ^ j := by
  classical
  let v : (Kˣ →* ℂˣ) → (Kˣ → ℂ) := fun χ x => ((χ x : ℂˣ) : ℂ)
  have hv : LinearIndependent ℂ v := by
    have hinj : Function.Injective (fun χ : Kˣ →* ℂˣ => (Units.coeHom ℂ).comp χ) := by
      intro χ χ' e
      ext x
      exact congrArg (fun f : Kˣ →* ℂ => f x) e
    have h0 := (linearIndependent_monoidHom Kˣ ℂ).comp _ hinj
    exact h0
  by_contra hne
  push_neg at hne
  let l1 : (Kˣ →* ℂˣ) →₀ ℂ := ∑ i ∈ Finset.range n, Finsupp.single (θ ^ g ^ i) 1
  let l2 : (Kˣ →* ℂˣ) →₀ ℂ := ∑ i ∈ Finset.range n, Finsupp.single (θ' ^ g ^ i) 1
  have hl : Finsupp.linearCombination ℂ v l1 = Finsupp.linearCombination ℂ v l2 := by
    simp only [l1, l2, map_sum, Finsupp.linearCombination_single, one_smul]
    funext z
    simp only [Finset.sum_apply, v, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    have := h z
    simpa only [map_pow, Units.val_pow_eq_pow_val] using this
  have he : l1 = l2 := hv.finsuppLinearCombination_injective hl
  have h1 : l1 θ' = 0 := by
    simp only [l1, Finsupp.finset_sum_apply, Finsupp.single_apply]
    exact Finset.sum_eq_zero fun i hi => if_neg fun e => hne i (Finset.mem_range.mp hi) e.symm
  have h2 : l2 θ' ≠ 0 := by
    simp only [l2, Finsupp.finset_sum_apply, Finsupp.single_apply]
    rw [Finset.sum_boole]
    have : (Finset.filter (fun i => θ' ^ g ^ i = θ') (Finset.range n)).card ≠ 0 := by
      refine Finset.card_ne_zero.mpr ⟨0, ?_⟩
      simp [hn]
    exact_mod_cast this
  exact h2 (he ▸ h1)

end Fields

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

open TameWeilRepresentationIrreducibility in

private theorem pair_of_gen (φ : Weil h) (hφ : deg φ = -1) : ∃ t₀ : Ine (F := E) A,
    (∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)), (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1) →
      a.ρ (ineIncl h t₀) * a.ρ φ = a.ρ φ * a.ρ (ineIncl h t₀) ^ normV w ∧
        (a.ρ.IsIrreducible → IrrPair (a.ρ (ineIncl h t₀)) (a.ρ φ))) ∧
    ∀ (n m : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h (Fin m → ℂ)),
      (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1) →
      (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → b.ρ σ = 1) → a.ρ.IsIrreducible → b.ρ.IsIrreducible →
      ∀ e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ), (∀ v, e (a.ρ (ineIncl h t₀) v) = b.ρ (ineIncl h t₀) (e v)) →
        (∀ v, e (a.ρ φ v) = b.ρ φ (e v)) → a.Iso b := by
  obtain ⟨γ0, hγ⟩ := GlobalTheory.MemTame.exists_tameGenAt E Ω w A h
  have e0 : ineIncl h (⟨γ0, hγ.1⟩ : Ine (F := E) A) = (⟨γ0, Ine_le_Weil h hγ.1⟩ : Weil h) :=
    Subtype.ext rfl
  refine ⟨⟨γ0, hγ.1⟩, ?_, ?_⟩
  · rw [e0]
    intro n a ha
    have hT : a.Tame := fun σ hσ => ha σ (wild_inertia_isWild hσ)
    refine ⟨?_, fun hirr => ?_⟩
    · have hF : deg φ⁻¹ = 1 := by simp [hφ]
      have h1 := hT.conj_eq_pow (γ := ⟨γ0, Ine_le_Weil h hγ.1⟩) (φ := φ⁻¹) hγ.1 hF
      rw [← h1, ← map_mul, ← map_mul]
      congr 1
      group
    · have := irreducible_nontrivial hirr
      refine ⟨inferInstance, fun U hM hG => ?_⟩
      have hinj : ∀ σ, Function.Injective (a.ρ σ) := fun σ =>
        (Representation.apply_bijective a.ρ σ).1
      have hall : ∀ σ, σ ∈ weilStabiliserSubgroup a.ρ U :=
        mem_of_tame_generator_frobenius a.ρ a.smooth (fun σ hσ => ha σ (wild_inertia_isWild hσ)) hγ hφ (weilStabiliserSubgroup a.ρ U)
          (fun σ hσ => mem_weil_stabiliser_iff.mpr fun v => by rw [hσ, Module.End.one_apply])
          (mem_weil_stabiliser_iff.mpr fun v => ⟨hM v, fun hv => mem_of_injective_maps_into (hinj _) hM hv⟩)
          (mem_weil_stabiliser_iff.mpr fun v => ⟨hG v, fun hv => mem_of_injective_maps_into (hinj _) hG hv⟩)
      exact irreducible_stable_bot_or_top hirr U (fun σ v hv => (mem_weil_stabiliser_iff.mp (hall σ) v).mp hv)
  · rw [e0]
    intro n m a b ha hb hirra hirrb e hγe hφe
    have hNa := irreducible_monodromy_zero a hirra
    have hNb := irreducible_monodromy_zero b hirrb
    let f : Weil h →* Module.End ℂ (Fin n → ℂ) × Module.End ℂ (Fin m → ℂ) := MonoidHom.prod a.ρ b.ρ
    have hf : IsSmooth f := IsSmooth.of_le₂ a.smooth b.smooth (fun σ h1 h2 => Prod.ext h1 h2)
    have hall : ∀ σ, σ ∈ weilIntertwiningSubgroup a.ρ b.ρ e :=
      mem_of_tame_generator_frobenius f hf
        (fun σ hσ => Prod.ext (ha σ (wild_inertia_isWild hσ)) (hb σ (wild_inertia_isWild hσ)))
        hγ hφ (weilIntertwiningSubgroup a.ρ b.ρ e)
        (fun σ hσ => mem_weil_intertwining_iff.mpr fun v => by
          have h1 : a.ρ σ = 1 := congrArg Prod.fst hσ
          have h2 : b.ρ σ = 1 := congrArg Prod.snd hσ
          rw [h1, h2, Module.End.one_apply, Module.End.one_apply])
        (mem_weil_intertwining_iff.mpr hγe) (mem_weil_intertwining_iff.mpr hφe)
    show ∃ e' : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ), (∀ σ v, e' (a.ρ σ v) = b.ρ σ (e' v)) ∧ ∀ v, e' (a.N v) = b.N (e' v)
    exact ⟨e, fun σ v => mem_weil_intertwining_iff.mp (hall σ) v, fun v => by rw [hNa, hNb]; simp⟩

private theorem charpoly_of_inFor {g n m : ℕ} {K : Type} [Field K] {R : Ine (F := E) A →* Kˣ}
    {θ : Kˣ →* ℂˣ} (a : WDRep h (Fin m → ℂ)) (hV : InFor g n R θ (WD.mk a)) (t : Ine (F := E) A) :
    (a.ρ (ineIncl h t)).charpoly = ∏ j ∈ Finset.range n, (X - C ((θ (R t ^ g ^ j) : ℂˣ) : ℂ)) := by
  have := hV t
  rwa [WD.inePol_of_mem_Ine _ t.2, WD.charPol_mk] at this

private theorem eigenvalue_iff {g n m : ℕ} {K : Type} [Field K] {R : Ine (F := E) A →* Kˣ}
    {θ : Kˣ →* ℂˣ} (a : WDRep h (Fin m → ℂ)) (hV : InFor g n R θ (WD.mk a)) (t : Ine (F := E) A)
    (z : ℂ) : Module.End.HasEigenvalue (a.ρ (ineIncl h t)) z ↔
      ∃ i < n, z = ((θ (R t ^ g ^ i) : ℂˣ) : ℂ) := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, charpoly_of_inFor a hV t, IsRoot.def,
    eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

end UpperTheory.Zero.LLC

open UpperTheory.Zero.LLC in
theorem UpperTheory.Zero.LLC.tameUniq :
    UpperTheory.Zero.LLC.TameUniq := by
  intro E Ω _ _ _ _ _ A w h g _ n K _ _ R hR θ hθ V hV
  have hn := hR.pos
  have hr := hR.rank
  refine ⟨fun j => ?_, fun θ' hθ' => ?_, fun V' hi hi' ht ht' hV' hdet => ?_⟩
  · intro t
    rw [hV t]
    have hf : ∀ i, (X - C ((θ (R t ^ g ^ (i + n)) : ℂˣ) : ℂ) : ℂ[X]) =
        X - C ((θ (R t ^ g ^ i) : ℂˣ) : ℂ) := by
      intro i
      have e : R t ^ g ^ (i + n) = R t ^ g ^ i := by
        rw [add_comm, pow_add, mul_comm, pow_mul, pow_period hn hr]
      rw [e]
    rw [← prod_shift hn (fun i => (X - C ((θ (R t ^ g ^ i) : ℂˣ) : ℂ) : ℂ[X])) hf j]
    refine Finset.prod_congr rfl fun i _ => ?_
    have e : (θ ^ g ^ j) (R t ^ g ^ i) = θ (R t ^ g ^ (i + j)) := by
      rw [MonoidHom.pow_apply, ← map_pow, ← pow_mul, pow_add]
    rw [e]
  · refine orbit_of_sums hn θ θ' fun z => ?_
    obtain ⟨t, rfl⟩ := hR.surj z
    have e := congrArg Polynomial.nextCoeff ((hV t).symm.trans (hθ' t))
    rw [prod_X_sub_C_nextCoeff, prod_X_sub_C_nextCoeff] at e
    exact neg_injective e
  · obtain ⟨φ, hφ⟩ : ∃ φ : Weil h, deg φ = -1 := ⟨(frob h)⁻¹, by simp [deg_frob]⟩
    obtain ⟨t₀, h1, h2⟩ := pair_of_gen φ hφ
    obtain ⟨m, a, rfl, hai, hat⟩ := PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.exists_good hi ht
    obtain ⟨m', a', rfl, hai', hat'⟩ := PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.exists_good hi' ht'
    have hdim : ∀ {m : ℕ} (b : WDRep h (Fin m → ℂ)), InFor g n R θ (WD.mk b) →
        Module.finrank ℂ (Fin m → ℂ) = n := by
      intro m b hb
      have e := congrArg Polynomial.natDegree (charpoly_of_inFor b hb t₀)
      rwa [LinearMap.charpoly_natDegree, natDegree_finset_prod_X_sub_C_eq_card, Finset.card_range] at e
    have hm := hdim a hV
    have hm' := hdim a' hV'
    obtain ⟨hc, hirr⟩ := h1 m a hat
    obtain ⟨hc', -⟩ := h1 m' a' hat'
    rw [hR.normV_eq] at hc hc'
    obtain ⟨z, hz1, hz2⟩ := st1a (Fin m → ℂ) g (a.ρ (ineIncl h t₀)) (a.ρ φ)
      (PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.isUnit_rho a _) (PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.isUnit_rho a _) hc
      (hirr hai)
    rw [hm] at hz2
    obtain ⟨i, hin, hzi⟩ := (eigenvalue_iff a hV t₀ z).mp hz1
    have hz3 : Module.End.HasEigenvalue (a'.ρ (ineIncl h t₀)) (z ^ g ^ (n - i)) := by
      refine (eigenvalue_iff a' hV' t₀ _).mpr ⟨0, hn, ?_⟩
      rw [hzi, ← Units.val_pow_eq_pow_val, ← map_pow, ← pow_mul, ← pow_add,
        Nat.add_sub_of_le hin.le, pow_period hn hr]
      simp
    have hd : LinearMap.det (a.ρ φ) = LinearMap.det (a'.ρ φ) := by
      rw [← PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.eig_prod, ← PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.eig_prod]
      exact hdet φ
    obtain ⟨e, he1, he2⟩ := st1b (Fin m → ℂ) (Fin m' → ℂ) g n (n - i) _ (a.ρ φ) _ (a'.ρ φ) z hn hm hm'
      (PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.isUnit_rho a _) (PositivityTheory.Rg.DzCount.DepthZeroEigenvalues.isUnit_rho a' _) hc hc' hz2 hz1 hz3 hd
    exact (WD.mk_eq_mk.mpr (h2 m m' a a' hat hat' hai hai' e he1 he2)).symm

end
