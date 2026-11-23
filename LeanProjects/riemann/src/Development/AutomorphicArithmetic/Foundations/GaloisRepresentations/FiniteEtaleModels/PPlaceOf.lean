import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private lemma map_eq_zero_of_mem_max {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero O] {k : Type} [Field k] [CharP k p] (β : O →+* k) {x : O}
    (hx : x ∈ IsLocalRing.maximalIdeal O) : β x = 0 := by
  have hprime : (RingHom.ker β).IsPrime := RingHom.ker_isPrime β
  have hp : ((p : ℕ) : O) ∈ RingHom.ker β := by
    rw [RingHom.mem_ker, map_natCast]
    exact CharP.cast_eq_zero k p
  have hne : RingHom.ker β ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)
  have hmax : (RingHom.ker β).IsMaximal := IsPrime.to_maximal_ideal hne
  have heq : RingHom.ker β = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
  rw [← heq] at hx
  exact hx

private lemma exists_map_ker {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F]
    (J : Ideal (𝓞 F)) (hJ : J.IsMaximal) (hp : (p : 𝓞 F) ∈ J) (hne : J ≠ ⊥)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] :
    ∃ φ : 𝓞 F →+* k, RingHom.ker φ = J := by
  classical
  letI : Field (𝓞 F ⧸ J) := Ideal.Quotient.field J
  have hpr : p.Prime := Fact.out
  haveI : CharP (𝓞 F ⧸ J) p := by
    rw [CharP.charP_iff_prime_eq_zero hpr]
    rw [← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
    exact hp
  haveI : Finite (𝓞 F ⧸ J) := Ideal.finiteQuotientOfFreeOfNeBot J hne
  letI : Algebra (ZMod p) (𝓞 F ⧸ J) := ZMod.algebra _ p
  letI : Algebra (ZMod p) k := ZMod.algebra _ p
  haveI : Module.Finite (ZMod p) (𝓞 F ⧸ J) := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ZMod p) (𝓞 F ⧸ J) := Algebra.IsAlgebraic.of_finite _ _
  let ψ : (𝓞 F ⧸ J) →ₐ[ZMod p] k := IsAlgClosed.lift
  refine ⟨(ψ : (𝓞 F ⧸ J) →+* k).comp (Ideal.Quotient.mk J), ?_⟩
  rw [RingHom.ker_comp_of_injective _ (ψ : (𝓞 F ⧸ J) →+* k).injective, Ideal.mk_ker]

theorem UpperTheory.Gal.FiniteEtaleModels.placeOf_holds :
    PlaceOf := by
  intro p _ D O _ _ _ _ b r w hw hpO ha hUw htw 𝔞 h𝔞w
  have hpr : p.Prime := Fact.out
  have i0 : Fin D.a := ⟨0, by omega⟩
  have hρ : ∀ (k : Type) [Field k] [CharP k p] (β : O →+* k), β b.ρ = (r : k) := by
    intro k _ _ β
    have hm : b.t i0 (D.ω - (r : 𝓞 D.F)) ∈ IsLocalRing.maximalIdeal O :=
      htw i0 _ (hUw (sub_mem_uIdeal D r))
    have h0 := map_eq_zero_of_mem_max (p := p) β hm
    rw [map_sub, map_intCast, map_sub, map_intCast, b.t_ω, sub_eq_zero] at h0
    exact h0
  constructor
  · intro h
    obtain ⟨hne, hall⟩ := h
    have hrad : uIdeal D r ≤ 𝔞.radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf ?_
      rintro P ⟨hP𝔞, hPprime⟩
      have hPne : P ≠ ⊥ := by
        rintro rfl
        exact hne (le_bot_iff.mp hP𝔞)
      have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal hPprime hPne
      obtain ⟨_, hpP, _, hφ⟩ := hall P hPmax hP𝔞
      haveI : CharP (IsLocalRing.ResidueField O) p := by
        rw [CharP.charP_iff_prime_eq_zero hpr, ← map_natCast (IsLocalRing.residue O)]
        exact (IsLocalRing.residue_eq_zero_iff _).mpr hpO
      haveI : CharP (AlgebraicClosure (IsLocalRing.ResidueField O)) p := by
        rw [CharP.charP_iff_prime_eq_zero hpr,
          ← map_natCast (algebraMap (IsLocalRing.ResidueField O) (AlgebraicClosure _)),
          CharP.cast_eq_zero, map_zero]
      obtain ⟨φ, hker⟩ :=
        exists_map_ker (p := p) P hPmax hpP hPne (AlgebraicClosure (IsLocalRing.ResidueField O))
      let β : O →+* AlgebraicClosure (IsLocalRing.ResidueField O) :=
        (algebraMap _ _).comp (IsLocalRing.residue O)
      have h1 := hφ (AlgebraicClosure (IsLocalRing.ResidueField O)) β φ hker
      rw [hρ _ β] at h1
      have hsub : D.ω - (r : 𝓞 D.F) ∈ P := by
        rw [← hker, RingHom.mem_ker, map_sub, map_intCast, h1, sub_self]
      unfold uIdeal
      rw [Ideal.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hpP
      · exact hsub
    exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  · rintro ⟨e, he⟩
    have hpe : ((p : ℕ) : 𝓞 D.F) ^ e ∈ uIdeal D r ^ e := Ideal.pow_mem_pow (p_mem_uIdeal D r) e
    refine ⟨?_, ?_⟩
    · intro h
      rw [h] at he
      have h0 := he hpe
      rw [Ideal.mem_bot] at h0
      have h00 : ((p : ℕ) : 𝓞 D.F) = 0 := eq_zero_of_pow_eq_zero h0
      exact hpr.ne_zero (by exact_mod_cast h00)
    · intro w' hw' h𝔞w'
      haveI := hw'.isPrime
      have hUw' : uIdeal D r ≤ w' := Ideal.IsPrime.le_of_pow_le (he.trans h𝔞w')
      have hne : w' ≠ w := by
        rintro rfl
        exact hw'.ne_top (top_le_iff.mp (h𝔞w ▸ sup_le h𝔞w' le_rfl))
      refine ⟨hw', hUw' (p_mem_uIdeal D r), ?_, ?_⟩
      · intro i
        by_contra hspan
        obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hspan
        have hMeq : M = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hM
        have hKtop : RingHom.ker ((IsLocalRing.residue O).comp (b.t i)) ≠ ⊤ := RingHom.ker_ne_top _
        have hwK : w ≤ RingHom.ker ((IsLocalRing.residue O).comp (b.t i)) := by
          intro x hx
          rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
          exact htw i x hx
        have hw'K : w' ≤ RingHom.ker ((IsLocalRing.residue O).comp (b.t i)) := by
          intro x hx
          rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, ← hMeq]
          exact hle (Ideal.subset_span ⟨x, hx, rfl⟩)
        exact hne ((hw'.eq_of_le hKtop hw'K).trans (hw.eq_of_le hKtop hwK).symm)
      · intro k _ _ β φ hφ
        rw [hρ k β]
        have h2 : φ (D.ω - (r : 𝓞 D.F)) = 0 := by
          rw [← RingHom.mem_ker, hφ]
          exact hUw' (sub_mem_uIdeal D r)
        rw [map_sub, map_intCast, sub_eq_zero] at h2
        exact h2
