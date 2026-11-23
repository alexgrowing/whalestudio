import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalDegrees
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract
  FiniteSubfield IsDedekindDomain

open scoped GroundTheory.LocalField.Abstract Pointwise GroundTheory.Global.SemiLocal

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace CyclotomicLayer

theorem degreeMod_eq_one_of_mem_fixingSubgroup (q : Nat.Primes) (a : ℕ) {σ : Gal(ℚ̄/ℚ)}
    (hσ : σ ∈ (rootsOfUnityField ((q : ℕ) ^ (a + unitsLevel (q : ℕ)))).fixingSubgroup) :
    degreeMod (primePowPNat (q : ℕ) a) σ = 1 := by
  have hq : Fact (q : ℕ).Prime := ⟨q.2⟩
  have : NeZero ((q : ℕ) ^ (a + unitsLevel (q : ℕ))) := ⟨pow_ne_zero _ q.2.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ ((q : ℕ) ^ (a + unitsLevel (q : ℕ)))
  have hζmem : ζ ∈ rootsOfUnityField ((q : ℕ) ^ (a + unitsLevel (q : ℕ))) :=
    subset_adjoin ℚ _ hζ.pow_eq_one
  have h1 := modCharacter_eq_one hζ ((mem_fixingSubgroup_iff _ _).1 hσ ζ hζmem)
  have h2 : redUnits (q : ℕ) (a + unitsLevel (q : ℕ))
      (Units.map (toPadicInt (q : ℕ)).toMonoidHom (character σ)) = 1 := by
    apply Units.ext
    rw [redUnits_character, h1]
  apply Multiplicative.toAdd.injective
  rw [toAdd_degreeMod, toAdd_one, ← toZModPow_toPadicInt, toPadicInt_degree, degreeComponent_apply,
    toZModPow_padicUnitsLog, h2, map_one, toAdd_one]
  rfl

theorem zhatLayerField_le_rootsOfUnityField (q : Nat.Primes) (a : ℕ) :
    zhatLayerField (primePowPNat (q : ℕ) a) ≤ rootsOfUnityField ((q : ℕ) ^ (a + unitsLevel (q : ℕ))) := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  intro x hx
  rw [zhatLayerField, mem_fixedField_iff] at hx
  rw [← InfiniteGalois.fixedField_fixingSubgroup (rootsOfUnityField _), mem_fixedField_iff]
  intro σ hσ
  exact hx σ (MonoidHom.mem_ker.2 (degreeMod_eq_one_of_mem_fixingSubgroup q a hσ))

theorem exists_pow_dvd_finrank_cyclotomicLayer (K : FiniteSubfield)
    (S : Finset (HeightOneSpectrum (𝓞 K.1))) {m : ℕ} (hm : m ≠ 0) :
    ∃ r : ℕ+, (∃ N : ℕ, (r : ℕ) = m ^ (N + 1)) ∧ ∀ v ∈ S,
      ∀ w : SemiLocal.PlacesOver (cyclotomicLayer K r).1 v,
        m ∣ Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion (cyclotomicLayer K r).1) := by
  choose n hn using fun (v : HeightOneSpectrum (𝓞 K.1)) (q : Nat.Primes) =>
    exists_mem_stabilizer_toZModPow_degreeComponent_ne_zero (K := K) v q
  let N : ℕ := S.sup fun v =>
    m.primeFactors.attach.sup fun q => n v ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ+, (r : ℕ) = m ^ (N + 1) :=
    ⟨⟨m ^ (N + 1), pow_pos (Nat.pos_of_ne_zero hm) _⟩, rfl⟩
  refine ⟨r, ⟨N, hr⟩, fun v hv w => ?_⟩
  rw [SemiLocal.finrank_eq_ramificationIdx_mul_inertiaDeg _ v w.1, ← card_decompositionGroup v w.1]
  refine dvd_trans ?_ (Subgroup.card_map_dvd _ (layerDegree K _))
  refine dvd_natCard_of_forall_pow_dvd_orderOf _ hm fun q hq hqm => ?_
  obtain ⟨P, hP, hPw⟩ := exists_prime_comap_eq (cyclotomicLayer K _) w.1
  have hPv : P.comap (ringOfIntegersIncl K.1) = v.asIdeal := comap_eq_of_liesOver w.1 hPw
  obtain ⟨σ, hσP, hσK, hσ⟩ := hn v ⟨q, hq⟩ P hP hPv
  refine ⟨degreeMod _ σ, Subgroup.mem_map.2 ⟨restrictHom (E := cyclotomicLayer K _) ⟨σ, hσK⟩, ?_,
    layerDegree_restrictHom K _ _⟩, ?_⟩
  · rw [← hPw]
    exact restrictHom_mem_stabilizer K _ P ⟨σ, hσK⟩ hσP
  · have hnN : n v ⟨q, hq⟩ ≤ N := by
      have hqmem : q ∈ m.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqm, hm⟩
      refine le_trans ?_ (Finset.le_sup (f := fun v =>
        m.primeFactors.attach.sup fun q => n v ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩) hv)
      exact Finset.le_sup (f := fun q : m.primeFactors => n v ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩)
        (Finset.mem_attach _ ⟨q, hqmem⟩)
    have he : 1 ≤ m.factorization q := (hq.dvd_iff_one_le_factorization hm).1 hqm
    have hqr : q ^ (N + m.factorization q) ∣ m ^ (N + 1) := by
      calc q ^ (N + m.factorization q) ∣ q ^ (m.factorization q * (N + 1)) :=
            Nat.pow_dvd_pow q (by nlinarith)
        _ = (q ^ m.factorization q) ^ (N + 1) := pow_mul _ _ _
        _ ∣ m ^ (N + 1) := pow_dvd_pow_of_dvd (Nat.ordProj_dvd m q) _
    exact pow_dvd_orderOf_degreeMod r ⟨q, hq⟩ (hr ▸ hqr) (by omega) hσ

end CyclotomicLayer

end

end GroundTheory.ProfCoh
