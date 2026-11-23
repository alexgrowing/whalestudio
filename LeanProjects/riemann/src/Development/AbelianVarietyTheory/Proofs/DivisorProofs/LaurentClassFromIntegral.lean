import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsCohomologyBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalRingOfIsIntegralOfHenselian
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.LiftWitness

theorem laurentMap_coeff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : LaurentPolynomial A) (n : ℤ) :
    (laurentMap f p).coeff n = f (p.coeff n) := by
  simp [laurentMap]

theorem spMap_id (L : Type) [CommRing L] : spMap (RingHom.id L) = 𝟙 _ := by
  simp [spMap]

theorem laurentProd_bijective (B C : Type) [CommRing B] [CommRing C] : Function.Bijective
    ((laurentMap (RingHom.fst B C)).prod (laurentMap (RingHom.snd B C))) := by
  constructor
  · intro p p' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [RingHom.prod_apply] at h1 h2
    apply AddMonoidAlgebra.coeff_injective
    ext n
    · simpa [laurentMap_coeff] using congrArg (fun r => r.coeff n) h1
    · simpa [laurentMap_coeff] using congrArg (fun r => r.coeff n) h2
  · rintro ⟨f, g⟩
    refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.zipWith Prod.mk rfl f.coeff g.coeff), ?_⟩
    simp only [RingHom.prod_apply, Prod.mk.injEq]
    constructor <;> (apply AddMonoidAlgebra.coeff_injective; ext n; simp [laurentMap_coeff])

open GlobalTheory.EtC.GmPhiNat in

theorem eq_zero_of_pull_laurent_fst_snd (q : ℕ) (B C : Type) [CommRing B] [CommRing C] (n i : ℤ)
    (z : Ht q (sp (LaurentPolynomial (B × C))) n i)
    (h1 : pull _ (spMap (laurentMap (RingHom.fst B C))) _ n z = 0)
    (h2 : pull _ (spMap (laurentMap (RingHom.snd B C))) _ n z = 0) : z = 0 := by
  let e := (laurentMap (RingHom.fst B C)).prod (laurentMap (RingHom.snd B C))
  let E := RingEquiv.ofBijective e (laurentProd_bijective B C)
  have hinv : E.symm.toRingHom.comp e = RingHom.id _ :=
    RingHom.ext fun x => E.symm_apply_apply x
  have hw : pull _ (spMap e) _ n z = 0 := by
    apply (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q (LaurentPolynomial B) (LaurentPolynomial C) n i).1
    simp only [← pull_spMap_comp, map_zero, e, RingHom.fst_comp_prod, RingHom.snd_comp_prod]
    exact Prod.ext h1 h2
  have := pull_spMap_comp q e E.symm.toRingHom n i z
  rw [hinv, spMap_id, pull_id, hw, map_zero] at this
  exact this

theorem surj_prod (q : ℕ) [NeZero q] (B C : Type) [CommRing B] [CommRing C] (hq : IsUnit (q : B × C)) (i : ℤ)
    (hB : Function.Surjective (gmPhi q B i)) (hC : Function.Surjective (gmPhi q C i)) :
    Function.Surjective (gmPhi q (B × C) i) := by
  intro y
  obtain ⟨b, hb⟩ := hB (pull _ (spMap (laurentMap (RingHom.fst B C))) _ 1 y)
  obtain ⟨c, hc⟩ := hC (pull _ (spMap (laurentMap (RingHom.snd B C))) _ 1 y)
  obtain ⟨a, ha⟩ := (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q B C 0 (i - 1)).2 (b, c)
  simp only [Prod.mk.injEq] at ha
  refine ⟨a, (sub_eq_zero.mp ?_).symm⟩
  apply eq_zero_of_pull_laurent_fst_snd q B C 1 i
  · rw [map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q _ hq, ha.1, hb, sub_self]
  · rw [map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q _ hq, ha.2, hc, sub_self]

theorem exists_factor (q : ℕ) [NeZero q] (A : Type) [CommRing A] [HenselianLocalRing A] (hq : IsUnit (q : A)) (i : ℤ)
    (p : Ideal A) [p.IsPrime] :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Algebra.IsIntegral A B ∧
      (∀ a, algebraMap A B a = 0 → a ∈ p) ∧ Function.Surjective (gmPhi q B i) := by
  let D := A ⧸ p
  let Ω := AlgebraicClosure (FractionRing D)
  let T := integralClosure D Ω
  letI : Algebra A T := ((algebraMap D T).comp (Ideal.Quotient.mk p)).toAlgebra
  have hint : Algebra.IsIntegral A T := by
    have h1 : (Ideal.Quotient.mk p).IsIntegral := RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 : (algebraMap D T).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := D) x
    exact ⟨fun x => RingHom.IsIntegral.trans _ _ h1 h2 x⟩
  have hloc : IsLocalRing T := GlobalTheory.IntClLocal.isLocalRing_of_isIntegral_of_henselian A T
  have hqT : IsUnit (q : T) := by simpa using hq.map (algebraMap A T)
  refine ⟨T, inferInstance, inferInstance, hint, fun a ha => ?_,
    (GlobalTheory.T.units_cohomology_bijective q T (GlobalTheory.aic_integralClosure_algebraicClosure D) hqT i).2⟩
  have hinjΩ : Function.Injective (algebraMap D Ω) := by
    rw [IsScalarTower.algebraMap_eq D (FractionRing D) Ω]
    exact (algebraMap (FractionRing D) Ω).injective.comp (IsFractionRing.injective D (FractionRing D))
  have hinj : Function.Injective (algebraMap D T) := by
    intro x y h
    exact hinjΩ (congrArg Subtype.val h)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply hinj
  rw [map_zero]
  exact ha

theorem exists_witness (q : ℕ) [NeZero q] (A : Type) [CommRing A] [HenselianLocalRing A] (hq : IsUnit (q : A)) (i : ℤ)
    (S : Finset (Ideal A)) (hS : ∀ p ∈ S, p.IsPrime) (hne : S.Nonempty) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Algebra.IsIntegral A B ∧
      (∀ a, algebraMap A B a = 0 → ∀ p ∈ S, a ∈ p) ∧ Function.Surjective (gmPhi q B i) := by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton p =>
    have := hS p (Finset.mem_singleton_self p)
    obtain ⟨B, _, _, hint, hker, hsurj⟩ := exists_factor q A hq i p
    exact ⟨B, inferInstance, inferInstance, hint, fun a ha r hr => by
      rw [Finset.mem_singleton] at hr; subst hr; exact hker a ha, hsurj⟩
  | cons p S hp hSne ih =>
    have := hS p (Finset.mem_cons_self p S)
    obtain ⟨B, _, _, hintB, hkerB, hsurjB⟩ := ih fun r hr => hS r (Finset.mem_cons_of_mem hr)
    obtain ⟨C, _, _, hintC, hkerC, hsurjC⟩ := exists_factor q A hq i p
    have hqBC : IsUnit (q : B × C) := by simpa using hq.map (algebraMap A (B × C))
    refine ⟨B × C, inferInstance, inferInstance, inferInstance, fun a ha r hr => ?_,
      surj_prod q B C hqBC i hsurjB hsurjC⟩
    rw [Prod.algebraMap_apply, Prod.mk_eq_zero] at ha
    rcases Finset.mem_cons.1 hr with rfl | hr
    · exact hkerC a ha.2
    · exact hkerB a ha.1 r hr

theorem lift_witness : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ (i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) 1 i), ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'),
      Algebra.IsIntegral A A' ∧ RingHom.ker (algebraMap A A') ≤ nilradical A ∧
      ∃ a' : Ht q (sp A') 0 (i - 1), pull _ (spMap (laurentMap (algebraMap A A'))) _ 1 x = gmPhi q A' i a' := by
  intro q _ A _ _ hSH hq i x
  obtain ⟨hH, -⟩ := hSH
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  have hne : hfin.toFinset.Nonempty := by
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := IsLocalRing.maximalIdeal A) bot_le
    exact ⟨p, hfin.mem_toFinset.2 hp⟩
  obtain ⟨B, _, _, hint, hker, hsurj⟩ := exists_witness q A hq i hfin.toFinset
    (fun p hp => (hfin.mem_toFinset.1 hp).1.1) hne
  obtain ⟨a', ha'⟩ := hsurj (pull _ (spMap (laurentMap (algebraMap A B))) _ 1 x)
  refine ⟨B, inferInstance, inferInstance, hint, fun a ha => ?_, a', ha'.symm⟩
  rw [RingHom.mem_ker] at ha
  have : a ∈ (⊥ : Ideal A).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.2 fun p hp => hker a ha p (hfin.mem_toFinset.2 hp)
  exact this
end GlobalTheory.EtC.LiftWitness
