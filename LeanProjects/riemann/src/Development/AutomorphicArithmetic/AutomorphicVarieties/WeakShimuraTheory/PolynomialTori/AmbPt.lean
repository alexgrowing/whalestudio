import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ClosedOfSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.DimOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.PsFinEv
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.FinExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AlLoc

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Po.ambPt :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (B : Type) [CommRing B] [Algebra c.O B] [IsCO c.O B], ¬ Module.Finite c.O B →
      ∃ (𝔞 : Amb l) (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (f : A →+* 𝔞.V) (s : Finset 𝔞.K)
        (y : B →+* 𝔞.V), CharP 𝔞.K l ∧ 𝔞.IsDvr f ∧ y.comp (algebraMap c.O B) = 𝔞.a c ∧ (∀ b ∈ maximalIdeal B, y b ∈ maximalIdeal 𝔞.V) ∧
        (∃ b ∈ maximalIdeal B, y b ≠ 0) ∧ (∀ a ∈ maximalIdeal c.O, 𝔞.a c a = 0) ∧
        ∀ b, (y b : 𝔞.K) ∈ Subfield.closure (Set.range (𝔞.toK.comp f) ∪ s) := by
  intro l _ c B _ _ _ hB
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (dvrFacts l c.O).2.2.2.1
  obtain ⟨P, t, n, hP, hmP, ht, htP, hn⟩ := Po.dimOne c.O B hB
  haveI : IsDomain (B ⧸ P) := Ideal.Quotient.isDomain P
  haveI : IsCO c.O (B ⧸ P) := co_quot c.O B _ (Ideal.Quotient.mkₐ c.O P) (Ideal.Quotient.mkₐ_surjective c.O P)
  have hq : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hm : (maximalIdeal B).map (Ideal.Quotient.mk P) = maximalIdeal (B ⧸ P) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hq
  have h0 : ∀ a ∈ maximalIdeal c.O, algebraMap c.O (B ⧸ P) a = 0 := fun a ha =>
    (Ideal.Quotient.eq_zero_iff_mem (a := algebraMap c.O B a)).2 (hmP (Ideal.mem_map_of_mem _ ha))
  have hn' : maximalIdeal (B ⧸ P) ^ n ≤ Ideal.span {Ideal.Quotient.mk P t} := by
    rw [← hm, ← Ideal.map_pow]
    refine (Ideal.map_mono hn).trans ?_
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
  obtain ⟨φ, hφi, hφf, hφX, hφC⟩ := Po.psFin c.O (B ⧸ P) h0 (Ideal.Quotient.mk P t)
    (hm ▸ Ideal.mem_map_of_mem _ ht) (fun h => htP (Ideal.Quotient.eq_zero_iff_mem.1 h)) n hn'
  obtain ⟨hfin, hch⟩ := Po.fin_res c
  haveI : IsAdicComplete (maximalIdeal (PowerSeries (ResidueField c.O))) (PowerSeries (ResidueField c.O)) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  haveI : Finite (ResidueField (PowerSeries (ResidueField c.O))) :=
    Finite.of_equiv _ (PowerSeries.residueFieldOfPowerSeries (k := ResidueField c.O)).symm.toEquiv
  haveI : CharP (PowerSeries (ResidueField c.O)) l :=
    charP_of_injective_ringHom (PowerSeries.C_injective (R := ResidueField c.O)) l
  obtain ⟨𝔞, f, hK, hf, hfa⟩ := ambL c (PowerSeries (ResidueField c.O)) (PowerSeries.C.comp (residue c.O))
  obtain ⟨y, s, hy, hs⟩ := Po.finExt 𝔞.K 𝔞.V _ _ φ f hφi hφf hf.inj
  have hyφ : ∀ x, y (φ x) = f x := fun x => RingHom.congr_fun hy x
  have hya : ∀ a, y (algebraMap c.O (B ⧸ P) a) = 𝔞.a c a := fun a => by
    rw [← hφC, hyφ, ← hfa]
    rfl
  have hX : f PowerSeries.X ∈ maximalIdeal 𝔞.V := by
    haveI := hf.loc
    refine map_nonunit f _ ?_
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _
  refine ⟨𝔞, _, inferInstance, inferInstance, inferInstance, f, s, y.comp (Ideal.Quotient.mk P), hK, hf,
    RingHom.ext hya, fun b hb => ?_, ⟨t, ht, ?_⟩, fun a ha => ?_, fun b => hs _⟩
  · have hb' : Ideal.Quotient.mk P b ∈ maximalIdeal (B ⧸ P) := hm ▸ Ideal.mem_map_of_mem _ hb
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (hn' (Ideal.pow_mem_pow hb' n))
    refine (maximalIdeal.isMaximal 𝔞.V).isPrime.mem_of_pow_mem n ?_
    rw [RingHom.comp_apply, ← map_pow, ← hu, map_mul, ← hφX, hyφ]
    exact Ideal.mul_mem_left _ _ hX
  · rw [RingHom.comp_apply, ← hφX, hyφ]
    exact fun h => PowerSeries.X_ne_zero (hf.inj (h.trans (map_zero f).symm))
  · rw [← hya, h0 a ha, map_zero]
