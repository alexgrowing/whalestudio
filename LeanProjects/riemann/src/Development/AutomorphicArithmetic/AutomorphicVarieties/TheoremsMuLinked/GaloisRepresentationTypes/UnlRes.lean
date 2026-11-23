import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.AutP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelFRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UnlGap

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
open UpperTheory.V.Af.Bc
open scoped Pointwise

private theorem move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F))) :
    ∃ (B : ValuationSubring Ω) (g : G F Ω), IsPlaceOver B w ∧
      (∀ s ∈ Dec (F := F) A, g⁻¹ * s * g ∈ Dec (F := F) B) ∧
      (∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) A) ∧
      ∀ s ∈ Ine (F := K) B, g * res F Ω K s * g⁻¹ ∈ Ine (F := F) A := by
  obtain ⟨B, hB⟩ := (exists_isPlaceOver Ω w : ∃ B : ValuationSubring Ω, IsPlaceOver B w)
  have hB' : IsPlaceOver B (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω]
    exact hB (algebraMap (𝓞 F) (𝓞 K) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hB' hA
  have hm : ∀ x, x ∈ B ↔ g x ∈ g • B := fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hv : ∀ y, (g • B).valuation (g y) < 1 ↔ B.valuation y < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hm, ← hm, map_eq_zero_iff _ g.injective]
  have hD : ∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) (g • B) := fun s hs => by
    have h1 : res F Ω K s • B = B := hs
    show (g * res F Ω K s * g⁻¹) • g • B = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  have hD' : ∀ s ∈ Dec (F := F) (g • B), g⁻¹ * s * g ∈ Dec (F := F) B := fun s hs => by
    have h1 : s • g • B = g • B := hs
    show (g⁻¹ * s * g) • B = B
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  refine ⟨B, g, hB, hD', hD, fun s hs => ⟨hD s hs.1, fun x hx => ?_⟩⟩
  obtain ⟨y, rfl⟩ := g.surjective x
  have e : (g * res F Ω K s * g⁻¹) (g y) = g (s y) := by
    show g (s (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e, ← map_sub, hv]
  exact hs.2 y ((B.valuation_le_one_iff _).2 ((hm y).2 (((g • B).valuation_le_one_iff _).1 hx)))

private theorem nat_mem_under {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (l : ℕ)
    (w : HeightOneSpectrum (𝓞 L)) : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

private theorem char_conj {Γ C : Type} [Group Γ] [CommGroup C] (χ : Γ →* C) (g s : Γ) : χ (g * s * g⁻¹) = χ s := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

private theorem rep_conj {Γ C : Type} [Group Γ] [Group C] (r : Γ →* C) (P : C) (g s : Γ) :
    P * r g * r s * (P * r g)⁻¹ = P * r (g * s * g⁻¹) * P⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  group

private theorem flag_move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F)))
    {κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ} (hκ : FlagAt M m r A κ) :
    ∃ (B : ValuationSubring Ω) (d : ↥(Dec (F := K) B) →* ↥(Dec (F := F) A)), IsPlaceOver B w ∧
      FlagAt M m (r.comp (res F Ω K)) B (fun i => (κ i).comp d) ∧
      (∀ s, cycBar F Ω l (d s) = cycBar K Ω l s) ∧
      (Dec (F := F) B ≤ (res F Ω K).range → Function.Surjective d) := by
  obtain ⟨χ, hχ, ⟨P, hP⟩, hκ⟩ := hκ
  obtain ⟨B, g, hB, hD', hD, hI⟩ := move w hA
  let d : ↥(Dec (F := K) B) →* ↥(Dec (F := F) A) :=
    (((MulAut.conj g).toMonoidHom.comp (res F Ω K)).comp (Dec (F := K) B).subtype).codRestrict _
      fun s => hD s s.2
  have hd : ∀ s, (d s : G F Ω) = g * res F Ω K s * g⁻¹ := fun _ => rfl
  refine ⟨B, d, hB, ⟨fun i => (χ i).comp (res F Ω K), fun i s hs => hχ i _ hs,
    ⟨P * r g, fun s => ?_⟩, fun i s hs => ?_⟩, fun s => ?_, fun H s => ?_⟩
  · rw [MonoidHom.comp_apply, rep_conj]
    exact hP (d s)
  · have h := hκ i (d s) (hI s hs)
    rw [hd, char_conj, char_conj] at h
    exact h
  · rw [hd, char_conj]
    rfl
  · obtain ⟨t, ht⟩ := H (hD' s s.2)
    have htD : t ∈ Dec (F := K) B := by
      have h1 : res F Ω K t • B = B := by
        rw [ht]
        exact hD' s s.2
      exact h1
    refine ⟨⟨t, htD⟩, Subtype.ext ?_⟩
    rw [hd]
    show g * res F Ω K t * g⁻¹ = s
    rw [ht]
    group

end

theorem UpperTheory.V.Th.unlRes :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)), 1 ≤ M → ((∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω).range) → Unl l M m r → Unl l M m (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) ∧ ((∀ i j, m i ≠ m j + 1) → Af.Level l M m r → Unl l M m (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) := by
  intro K Ω _ _ _ _ _ _ _ l _ n M m r hM
  refine ⟨fun hdec H w hw => ?_, fun hm H w hw => ?_⟩
  · obtain ⟨A, hA, κ, hκ, hu⟩ := H (w.under (𝓞 ℚ)) ((nat_mem_under l w).2 hw)
    obtain ⟨B, d, hB, hF, hc, hs⟩ := flag_move w hA hκ
    have hv : B.valuation (l : Ω) < 1 := by
      simpa using (hB _).2 hw
    refine ⟨B, hB, _, hF, fun i j e => hu i j (MonoidHom.ext fun s => ?_)⟩
    obtain ⟨t, rfl⟩ := hs (hdec B hv) s
    have h1 := DFunLike.congr_fun e t
    change κ i (d t) = κ j (d t) * cycBar K Ω l t at h1
    change κ i (d t) = κ j (d t) * cycBar ℚ Ω l (d t)
    rw [hc, h1]
  · obtain ⟨A, hA, κ, hκ⟩ := (Lev.LevelF.of_level H).above (w.under (𝓞 ℚ)) ((nat_mem_under l w).2 hw)
    obtain ⟨B, d, hB, hF, -, -⟩ := flag_move w hA hκ
    exact ⟨B, hB, _, hF, Lev.unlGap K Ω l n M hM m _ w hw B hB _ hF hm⟩
