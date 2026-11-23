import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemFixedOfCharacterSumProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RankFixedInfCharacterEigenspace
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsLevelOneAddCharLiftingResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CardUnipotentUpperEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnipotentUpperMapSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsInjectiveGenericUnipotentCharacters
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IndexNeZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.LevelTorusLeTorus

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi

namespace UpperTheory.V.Z.Desc.V0

private theorem locO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : IsLocalRing 𝒪[k] :=
  (inferInstance : IsDiscreteValuationRing 𝒪[k]).toIsLocalRing
attribute [local instance] locO

section SlopeTestRemainingChoices

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

private def iA : unipB 𝒪[k] (Fin n) →* GL (Fin n) k :=
  (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)).comp (unipB 𝒪[k] (Fin n)).subtype

private theorem pA_mem (a : unipB 𝒪[k] (Fin n)) :
    GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k]) (a : GL (Fin n) 𝒪[k]) ∈ unipB 𝓀[k] (Fin n) := by
  obtain ⟨h1, h2⟩ := (mem_unipB _).1 a.2
  refine (mem_unipB _).2 ⟨fun i j h => ?_, fun i => ?_⟩
  · change IsLocalRing.residue 𝒪[k] _ = 0
    rw [h1 i j h, map_zero]
  · change IsLocalRing.residue 𝒪[k] _ = 1
    rw [h2 i, map_one]

private def pA : unipB 𝒪[k] (Fin n) →* unipB 𝓀[k] (Fin n) :=
  ((GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k])).comp (unipB 𝒪[k] (Fin n)).subtype).codRestrict _
    (pA_mem k n)

private theorem pA_surj : Function.Surjective (pA k n) := fun x => by
  obtain ⟨y, hy, e⟩ := UpperTheory.unipotent_upper_map_surjective (IsLocalRing.residue 𝒪[k]) IsLocalRing.residue_surjective n x.1 x.2
  exact ⟨⟨y, hy⟩, Subtype.ext e⟩

private theorem map_inj : Function.Injective (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)) := fun A B h =>
  Units.ext (Matrix.ext fun i j => Subtype.ext (congrArg (fun g : GL (Fin n) k => g.val i j) h))

private theorem red_iff (y : GL (Fin n) 𝒪[k]) :
    GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ 1)) y = 1 ↔
      GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k]) y = 1 := by
  rw [Units.ext_iff, Units.ext_iff, ← Matrix.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  have e1 : ((1 : GL (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ 1)).val) i j =
      Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := by
    simp only [Units.val_one, Matrix.one_apply]; split_ifs <;> simp
  have e2 : ((1 : GL (Fin n) 𝓀[k]).val) i j = IsLocalRing.residue 𝒪[k] ((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := by
    simp only [Units.val_one, Matrix.one_apply]; split_ifs <;> simp
  rw [e1, e2]
  change Ideal.Quotient.mk _ (y.val i j) = _ ↔ Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k]) (y.val i j) = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.eq, Ideal.Quotient.eq, pow_one]

private theorem pA_ker (a : unipB 𝒪[k] (Fin n)) : pA k n a = 1 ↔ iA k n a ∈ Kc k n 1 := by
  constructor
  · intro h
    exact ⟨a.1, (red_iff k n a.1).2 (congrArg Subtype.val h), rfl⟩
  · rintro ⟨y, hy, e⟩
    obtain rfl : y = a.1 := map_inj k n e
    exact Subtype.ext ((red_iff k n a.1).1 hy)

private theorem iA_mem (a : unipB 𝒪[k] (Fin n)) : iA k n a ∈ unipB k (Fin n) ∧ iA k n a ∈ KO k (Fin n) := by
  obtain ⟨h1, h2⟩ := (mem_unipB _).1 a.2
  refine ⟨(mem_unipB _).2 ⟨fun i j h => ?_, fun i => ?_⟩, ⟨a.1, rfl⟩⟩
  · change ((a.1.val i j : 𝒪[k]) : k) = 0
    rw [h1 i j h]; rfl
  · change ((a.1.val i i : 𝒪[k]) : k) = 1
    rw [h2 i]; rfl

private theorem iA_onto {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n) ∧ u ∈ KO k (Fin n)) : ∃ a, iA k n a = u := by
  obtain ⟨h, hk⟩ := hu
  obtain ⟨y, rfl⟩ := hk
  obtain ⟨h1, h2⟩ := (mem_unipB _).1 h
  exact ⟨⟨y, (mem_unipB _).2 ⟨fun i j hij => Subtype.ext (h1 i j hij), fun i => Subtype.ext (h2 i)⟩⟩, rfl⟩

end SlopeTestRemainingChoices

theorem eOp : EOp := by
  intro k _ _ _ _ n
  classical
  obtain ⟨ψ, φ, hψ, hφ, hres⟩ := UpperTheory.exists_level_one_addChar_lifting_residue k
  letI : Fintype 𝓀[k] := Fintype.ofFinite _
  obtain ⟨χ, hχi, hχv, c, hc⟩ := UpperTheory.exists_injective_generic_unipotent_characters 𝓀[k] n φ hφ
  haveI : Finite (Matrix (Fin n) (Fin n) 𝓀[k]) := inferInstanceAs (Finite (Fin n → Fin n → _))
  haveI : Finite (GL (Fin n) 𝓀[k]) := Finite.of_injective _ Units.val_injective
  letI : Fintype (unipB 𝓀[k] (Fin n)) := Fintype.ofFinite _
  obtain ⟨j, hj⟩ := UpperTheory.card_unipotent_upper_eq_pow 𝓀[k] n
  have hcard : Fintype.card (unipB 𝓀[k] (Fin n)) = Nat.card 𝓀[k] ^ j := by
    rw [← Nat.card_eq_fintype_card, hj]
  let s : unipB 𝓀[k] (Fin n) → unipB 𝒪[k] (Fin n) := Function.surjInv (pA_surj k n)
  have hs : ∀ x, pA k n (s x) = x := Function.surjInv_eq (pA_surj k n)
  have hn : ∀ a, ∀ u ∈ Kc k n 1, (iA k n a)⁻¹ * u * iA k n a ∈ Kc k n 1 := fun a u hu => by
    simpa using UpperTheory.V.Z.Sym.Sig.Kc_conj (inv_mem (iA_mem k n a).2) hu
  have hrs : Function.Surjective (IsLocalRing.residue 𝒪[k]) := IsLocalRing.residue_surjective
  let l : 𝓀[k] → 𝒪[k] := Function.surjInv hrs
  have hl : ∀ x, IsLocalRing.residue 𝒪[k] (l x) = x := Function.surjInv_eq hrs
  let lift : ({p : Fin n × Fin n // (p.2 : ℕ) = p.1 + 1} → 𝓀[k]ˣ) → Fin n → k := fun f i =>
    if h : (i : ℕ) + 1 < n then ((l (f ⟨(i, ⟨(i : ℕ) + 1, h⟩), rfl⟩ : 𝓀[k]) : 𝒪[k]) : k) else 1
  have hlp : ∀ f (p : {p : Fin n × Fin n // (p.2 : ℕ) = p.1 + 1}), lift f p.1.1 = ((l (f p : 𝓀[k]) : 𝒪[k]) : k) := by
    rintro f ⟨⟨i, i'⟩, hp⟩
    have h : (i : ℕ) + 1 < n := by have := i'.2; simp only at hp; omega
    have e : (⟨(i, ⟨(i : ℕ) + 1, h⟩), rfl⟩ : {p : Fin n × Fin n // (p.2 : ℕ) = p.1 + 1}) = ⟨(i, i'), hp⟩ :=
      Subtype.ext (Prod.ext rfl (Fin.ext hp.symm))
    simp only [lift, dif_pos h, e]
  have hinj : Function.Injective lift := fun f g h => by
    funext p
    refine Units.ext ?_
    have h1 : l (f p : 𝓀[k]) = l (g p : 𝓀[k]) := Subtype.ext (by
      rw [← hlp, ← hlp, h])
    rw [← hl (f p : 𝓀[k]), ← hl (g p : 𝓀[k]), h1]
  have hunit : ∀ x : 𝓀[k]ˣ, valuation k ((l (x : 𝓀[k]) : 𝒪[k]) : k) = 1 := fun x => by
    have h1 : IsUnit (l (x : 𝓀[k])) := by
      rw [← isUnit_map_iff (IsLocalRing.residue 𝒪[k]), hl]
      exact x.isUnit
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers (valuation k))).1 h1
  have key : ∀ f (y : unipB 𝒪[k] (Fin n)), ((χ f (pA k n y) : ℂˣ) : ℂ) = chr ψ (lift f) (iA k n y) := fun f y => by
    rw [hχv, chr, Finset.sum_subtype (p := fun p : Fin n × Fin n => (p.2 : ℕ) = p.1 + 1) _ (by simp)]
    have e : ∑ p : {p : Fin n × Fin n // (p.2 : ℕ) = p.1 + 1},
        lift f p.1.1 * (iA k n y : Matrix (Fin n) (Fin n) k) p.1.1 p.1.2 =
        ((∑ p : {p : Fin n × Fin n // (p.2 : ℕ) = p.1 + 1},
          l (f p : 𝓀[k]) * (y.1.val p.1.1 p.1.2) : 𝒪[k]) : k) := by
      rw [AddSubmonoidClass.coe_finset_sum]
      exact Finset.sum_congr rfl fun p _ => by rw [hlp]; rfl
    rw [e, hres, map_sum (IsLocalRing.residue 𝒪[k])]
    congr 2
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, hl]
    rfl
  refine ⟨ψ, ∑ x, Finsupp.single (iA k n (s x)) (c x), j,
    Finset.univ.map ⟨lift, hinj⟩, hψ, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hg)
    have : g = iA k n (s x) := by
      have := Finsupp.support_single_subset hx
      simpa using this
    exact this ▸ (iA_mem k n _).2
  · intro g hg u hu
    simpa using UpperTheory.V.Z.Sym.Sig.Kc_conj (inv_mem hg) hu
  · intro R W _ _ _ ρ v hv
    rw [← hcard]
    exact UpperTheory.mem_fixed_of_character_sum_projection (Kc k n 1) (iA k n) (pA k n) s hs (pA_ker k n) hn χ hχi c hc R W ρ v hv
  · exact ⟨_, Finset.mem_map_of_mem _ (Finset.mem_univ fun _ => 1)⟩
  · intro t ht i
    obtain ⟨f, -, rfl⟩ := Finset.mem_map.1 ht
    change valuation k (lift f i) = 1
    by_cases h : (i : ℕ) + 1 < n
    · simp only [lift, dif_pos h]
      exact hunit _
    · simp only [lift, dif_neg h, map_one]
  · intro W _ _ τ
    rw [← hcard, UpperTheory.rank_fixed_inf_character_eigenspace (Kc k n 1) (iA k n) (pA k n) s hs (pA_ker k n) hn χ hχi c hc W τ, Finset.sum_map]
    refine Finset.sum_congr rfl fun f _ => ?_
    have e : (⨅ y : unipB 𝒪[k] (Fin n), Module.End.eigenspace (τ (iA k n y)) ((χ f (pA k n y) : ℂˣ) : ℂ)) =
        ⨅ (u : GL (Fin n) k) (_ : u ∈ unipB k (Fin n) ∧ u ∈ KO k (Fin n)),
          Module.End.eigenspace (τ u) (chr ψ (lift f) u) := by
      refine le_antisymm (le_iInf₂ fun u hu => ?_) (le_iInf fun y => ?_)
      · obtain ⟨y, rfl⟩ := iA_onto k n hu
        exact (iInf_le _ y).trans_eq (by rw [key])
      · exact (iInf₂_le (iA k n y) (iA_mem k n y)).trans_eq (by rw [key])
    change _ = Module.rank ℂ ↥(isoPart τ ψ (lift f))
    rw [e, isoPart]

end UpperTheory.V.Z.Desc.V0
