import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol
import GroundTheory.LocalFields.ExplicitQp
import GroundTheory.LocalFields.LocalArtinTransport

namespace GroundTheory.Global

open IsDedekindDomain NumberField

noncomputable section

namespace RationalSymbol

abbrev prime (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ := Rat.HeightOneSpectrum.primesEquiv v

instance (v : HeightOneSpectrum (𝓞 ℚ)) : Fact (prime v).Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev padicRingEquiv : v.adicCompletion ℚ ≃+* ℚ_[prime v] :=
  RingEquivClass.toRingEquiv (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)

theorem continuous_padicRingEquiv : Continuous (padicRingEquiv v) :=
  map_continuous (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)

theorem continuous_padicRingEquiv_symm : Continuous (padicRingEquiv v).symm :=
  HomeomorphClass.inv_continuous (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)

def closureEquiv :
    AlgebraicClosure (v.adicCompletion ℚ) ≃+* AlgebraicClosure ℚ_[prime v] :=
  IsAlgClosure.equivOfEquiv _ _ (padicRingEquiv v)

theorem closureEquiv_algebraMap (x : v.adicCompletion ℚ) :
    closureEquiv v (algebraMap _ (AlgebraicClosure (v.adicCompletion ℚ)) x) =
      algebraMap ℚ_[prime v] (AlgebraicClosure ℚ_[prime v]) (padicRingEquiv v x) :=
  IsAlgClosure.equivOfEquiv_algebraMap _ _ _ x

theorem mem_maximalAbelianExtension_of_pow_eq_one {y : AlgebraicClosure (v.adicCompletion ℚ)}
    {n : ℕ} (hn : 0 < n) (hy : y ^ n = 1) :
    y ∈ LocalField.maximalAbelianExtension (v.adicCompletion ℚ)
      (AlgebraicClosure (v.adicCompletion ℚ)) := by
  rw [← LocalField.mem_maximalAbelianExtension_transport_iff (padicRingEquiv v) (closureEquiv v)
    (closureEquiv_algebraMap v), LocalField.Padic.maximalAbelianExtension_eq_adjoin_rootsOfUnity]
  exact IntermediateField.subset_adjoin _ _ ⟨n, hn, by rw [← map_pow, hy, map_one]⟩

theorem closureEquiv_apply_of_localReciprocityLimit (x : (v.adicCompletion ℚ)ˣ)
    {τ : AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ)}
    (hτ : (τ : TopologicalAbelianization (AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ))) =
        LocalField.localReciprocityLimit (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ)) x)
    {τ' : AlgebraicClosure ℚ_[prime v] ≃ₐ[ℚ_[prime v]] AlgebraicClosure ℚ_[prime v]}
    (hτ' : (τ' : TopologicalAbelianization (AlgebraicClosure ℚ_[prime v] ≃ₐ[ℚ_[prime v]]
      AlgebraicClosure ℚ_[prime v])) =
        LocalField.localReciprocityLimit ℚ_[prime v] (AlgebraicClosure ℚ_[prime v])
          (Units.map (padicRingEquiv v).toRingHom.toMonoidHom x))
    {y : AlgebraicClosure (v.adicCompletion ℚ)}
    (hy : y ∈ LocalField.maximalAbelianExtension (v.adicCompletion ℚ)
      (AlgebraicClosure (v.adicCompletion ℚ))) :
    closureEquiv v (τ y) = τ' (closureEquiv v y) := by
  have h := LocalField.transport_localArtinMap_apply_of_continuous (padicRingEquiv v)
    (continuous_padicRingEquiv v) (continuous_padicRingEquiv_symm v) (closureEquiv v)
    (closureEquiv_algebraMap v) x hy
  rw [LocalField.localArtinMap_apply, LocalField.localArtinMap_apply, ← hτ, ← hτ',
    LocalField.topologicalAbelianizationEquiv_mk_apply,
    LocalField.topologicalAbelianizationEquiv_mk_apply] at h
  exact h

theorem pos_of_coprime {m : ℕ} (hm : m.Coprime (prime v)) : 0 < m :=
  Nat.pos_of_ne_zero fun h ↦ by
    subst h
    exact (Fact.out : (prime v).Prime).one_lt.ne' ((Nat.coprime_zero_left _).1 hm)

theorem apply_of_pow_eq_one_of_prime_pow (x : (v.adicCompletion ℚ)ˣ) (u : ℤ_[prime v]ˣ) (r : ℤ)
    (hx : padicRingEquiv v x = ((u : ℤ_[prime v]) : ℚ_[prime v]) * (prime v : ℚ_[prime v]) ^ r)
    {τ : AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ)}
    (hτ : (τ : TopologicalAbelianization (AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ))) =
        LocalField.localReciprocityLimit (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ)) x)
    {n : ℕ} {y : AlgebraicClosure (v.adicCompletion ℚ)} (hy : y ^ (prime v ^ n) = 1) :
    τ y = y ^ (PadicInt.toZModPow n ((u⁻¹ : ℤ_[prime v]ˣ) : ℤ_[prime v])).val := by
  obtain ⟨τ', hτ'⟩ := QuotientGroup.mk_surjective (LocalField.localReciprocityLimit ℚ_[prime v]
    (AlgebraicClosure ℚ_[prime v]) (Units.map (padicRingEquiv v).toRingHom.toMonoidHom x))
  have hmem := mem_maximalAbelianExtension_of_pow_eq_one v
    (pow_pos (Fact.out : (prime v).Prime).pos n) hy
  apply (closureEquiv v).injective
  rw [closureEquiv_apply_of_localReciprocityLimit v x hτ hτ' hmem, map_pow]
  exact LocalField.Padic.apply_of_pow_eq_one_of_prime_pow (prime v) _ u r
    (by rw [Units.coe_map]; exact hx) hτ' (by rw [← map_pow, hy, map_one])

theorem apply_of_pow_eq_one_of_coprime (x : (v.adicCompletion ℚ)ˣ) (u : ℤ_[prime v]ˣ) (r : ℕ)
    (hx : padicRingEquiv v x = ((u : ℤ_[prime v]) : ℚ_[prime v]) * (prime v : ℚ_[prime v]) ^ r)
    {τ : AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ)}
    (hτ : (τ : TopologicalAbelianization (AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ))) =
        LocalField.localReciprocityLimit (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ)) x)
    {m : ℕ} (hm : m.Coprime (prime v)) {y : AlgebraicClosure (v.adicCompletion ℚ)} (hy : y ^ m = 1) :
    τ y = y ^ (prime v ^ r) := by
  obtain ⟨τ', hτ'⟩ := QuotientGroup.mk_surjective (LocalField.localReciprocityLimit ℚ_[prime v]
    (AlgebraicClosure ℚ_[prime v]) (Units.map (padicRingEquiv v).toRingHom.toMonoidHom x))
  have hmem := mem_maximalAbelianExtension_of_pow_eq_one v (pos_of_coprime v hm) hy
  apply (closureEquiv v).injective
  rw [closureEquiv_apply_of_localReciprocityLimit v x hτ hτ' hmem, map_pow]
  exact LocalField.Padic.apply_of_pow_eq_one_of_coprime_of_nat (prime v) _ u r
    (by rw [Units.coe_map]; exact hx) hτ' hm (by rw [← map_pow, hy, map_one])

section Symbol

open SemiLocal

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)]

theorem residueEmbedding_localSymbol_apply (w : PlacesOver L v) (x : (v.adicCompletion ℚ)ˣ)
    {τ : AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ)}
    (hτ : (τ : TopologicalAbelianization (AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ))) =
        LocalField.localReciprocityLimit (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ)) x)
    (l : L) :
    residueEmbedding (v.adicCompletion ℚ) (w.1.adicCompletion L)
        (algebraMap L (w.1.adicCompletion L) (localSymbol L v x l)) =
      τ (residueEmbedding (v.adicCompletion ℚ) (w.1.adicCompletion L)
        (algebraMap L (w.1.adicCompletion L) l)) := by
  rw [algebraMap_localSymbol_apply L v w x l]
  exact normResidueSymbol_spec _ hτ _

theorem localSymbol_apply_of_pow_eq_one_of_prime_pow (x : (v.adicCompletion ℚ)ˣ) (u : ℤ_[prime v]ˣ)
    (r : ℤ)
    (hx : padicRingEquiv v x = ((u : ℤ_[prime v]) : ℚ_[prime v]) * (prime v : ℚ_[prime v]) ^ r)
    {n : ℕ} {ζ : L} (hζ : ζ ^ (prime v ^ n) = 1) :
    localSymbol L v x ζ = ζ ^ (PadicInt.toZModPow n ((u⁻¹ : ℤ_[prime v]ˣ) : ℤ_[prime v])).val := by
  obtain ⟨w⟩ := nonempty_placesOver L v
  obtain ⟨τ, hτ⟩ := exists_mk_eq_localReciprocityLimit (k := v.adicCompletion ℚ) x
  set i := residueEmbedding (v.adicCompletion ℚ) (w.1.adicCompletion L)
  have hj : Function.Injective fun l : L ↦ i (algebraMap L (w.1.adicCompletion L) l) :=
    i.toRingHom.injective.comp (algebraMap L (w.1.adicCompletion L)).injective
  apply hj
  simp only
  rw [residueEmbedding_localSymbol_apply v L w x hτ, map_pow, map_pow]
  exact apply_of_pow_eq_one_of_prime_pow v x u r hx hτ
    (by rw [← map_pow, ← map_pow, hζ, map_one, map_one])

theorem localSymbol_apply_of_pow_eq_one_of_coprime (x : (v.adicCompletion ℚ)ˣ) (u : ℤ_[prime v]ˣ)
    (r : ℕ)
    (hx : padicRingEquiv v x = ((u : ℤ_[prime v]) : ℚ_[prime v]) * (prime v : ℚ_[prime v]) ^ r)
    {m : ℕ} (hm : m.Coprime (prime v)) {ζ : L} (hζ : ζ ^ m = 1) :
    localSymbol L v x ζ = ζ ^ (prime v ^ r) := by
  obtain ⟨w⟩ := nonempty_placesOver L v
  obtain ⟨τ, hτ⟩ := exists_mk_eq_localReciprocityLimit (k := v.adicCompletion ℚ) x
  set i := residueEmbedding (v.adicCompletion ℚ) (w.1.adicCompletion L)
  have hj : Function.Injective fun l : L ↦ i (algebraMap L (w.1.adicCompletion L) l) :=
    i.toRingHom.injective.comp (algebraMap L (w.1.adicCompletion L)).injective
  apply hj
  simp only
  rw [residueEmbedding_localSymbol_apply v L w x hτ, map_pow, map_pow]
  exact apply_of_pow_eq_one_of_coprime v x u r hx hτ hm
    (by rw [← map_pow, ← map_pow, hζ, map_one, map_one])

end Symbol

end RationalSymbol

end

end GroundTheory.Global
