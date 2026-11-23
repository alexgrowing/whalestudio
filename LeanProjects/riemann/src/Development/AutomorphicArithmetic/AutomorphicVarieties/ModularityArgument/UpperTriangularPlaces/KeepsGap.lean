import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelFRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UnlGap
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.UnlRes

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
open UpperTheory.V.Af.Bc
open scoped Pointwise

private theorem conj_into {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (w : HeightOneSpectrum (𝓞 K)) {A B : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F)))
    (hB : IsPlaceOver B w) :
    ∃ g : G F Ω, (∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) A) ∧
      ∀ s ∈ Ine (F := K) B, g * res F Ω K s * g⁻¹ ∈ Ine (F := F) A := by
  have hB' : IsPlaceOver B (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω]
    exact hB (algebraMap (𝓞 F) (𝓞 K) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hB' hA
  have hmem : ∀ x, x ∈ B ↔ g x ∈ g • B := fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hval : ∀ y, (g • B).valuation (g y) < 1 ↔ B.valuation y < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hmem, ← hmem, map_eq_zero_iff _ g.injective]
  have hdec : ∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) (g • B) := fun s hs => by
    have h1 : res F Ω K s • B = B := hs
    show (g * res F Ω K s * g⁻¹) • g • B = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  refine ⟨g, hdec, fun s hs => ⟨hdec s hs.1, fun x hx => ?_⟩⟩
  obtain ⟨y, rfl⟩ := g.surjective x
  have e : (g * res F Ω K s * g⁻¹) (g y) = g (s y) := by
    show g (s (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e, ← map_sub, hval]
  exact hs.2 y ((B.valuation_le_one_iff _).2 ((hmem y).2 (((g • B).valuation_le_one_iff _).1 hx)))

private theorem flag_at_place {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    (w : HeightOneSpectrum (𝓞 K)) {A B : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F)))
    (hB : IsPlaceOver B w) {κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ} (hκ : FlagAt M m r A κ) :
    ∃ κ' : Fin n → ↥(Dec (F := K) B) →* (Qbar l)ˣ, FlagAt M m (r.comp (res F Ω K)) B κ' := by
  obtain ⟨χ, hχ, ⟨P, hP⟩, hI⟩ := hκ
  obtain ⟨g, hD, hIn⟩ := conj_into w hA hB
  let d : ↥(Dec (F := K) B) →* ↥(Dec (F := F) A) :=
    (((MulAut.conj g).toMonoidHom.comp (res F Ω K)).comp (Dec (F := K) B).subtype).codRestrict _
      fun s => hD s s.2
  have hd : ∀ s, (d s : G F Ω) = g * res F Ω K s * g⁻¹ := fun _ => rfl
  have hcyc : ∀ (ψ : G F Ω →* (Qbar l)ˣ) (s : G K Ω), ψ (g * res F Ω K s * g⁻¹) = ψ (res F Ω K s) := fun ψ s => by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have hrep : ∀ s : G K Ω, P * r g * r (res F Ω K s) * (P * r g)⁻¹ = P * r (g * res F Ω K s * g⁻¹) * P⁻¹ := fun s => by
    rw [map_mul, map_mul, map_inv]
    group
  refine ⟨fun i => (κ i).comp d, fun i => (χ i).comp (res F Ω K), fun i s hs => hχ i _ hs, ⟨P * r g, fun s => ?_⟩,
    fun i s hs => ?_⟩
  · rw [MonoidHom.comp_apply, hrep]
    exact hP (d s)
  · have h := hI i (d s) (hIn s hs)
    rw [hd, hcyc, hcyc] at h
    exact h

end

theorem UpperTheory.V.Z.Keep.keepsGap :
    ∀ (F L Ω : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsAlgClosure F Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), 1 ≤ M → (∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∃ κ, Af.FlagAt M m r A κ) → (∀ i j, m i ≠ m j + 1) → Z.Win.Keeps r L := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ l _ n M m r hM hflag hgap w hw _ B hB
  have hlow : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal := by
    change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal
    rwa [map_natCast]
  obtain ⟨A, hA, κ, hκ⟩ := hflag _ hlow
  obtain ⟨κ', hκ'⟩ := flag_at_place w hA hB hκ
  have hfl : IsFlagOn _ _ κ' := hκ'.choose_spec.2.1
  exact ⟨κ', hfl, Lev.unlGap L Ω l n M hM m _ w hw B hB _ hκ' hgap⟩
