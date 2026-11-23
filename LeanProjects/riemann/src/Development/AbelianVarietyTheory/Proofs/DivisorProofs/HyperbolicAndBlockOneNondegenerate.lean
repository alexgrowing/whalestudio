import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassKummerClassAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductGradedCommRingAxiomsHoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentAbsIntClosedLocalDomaiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroStrictlyHenselianEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfKummerClassOfUnitEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgClosedResidueFieldOfAic
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.GmAicDeg1

theorem cast_eq_zero_iff {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i) :
    x.cast hn hi = 0 ↔ x = 0 := by
  subst hn; subst hi; exact Iff.rfl

theorem cast_nsmul {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (k : ℕ) (x : Ht q E n i) :
    (k • x).cast hn hi = k • x.cast hn hi := by
  subst hn; subst hi; rfl

theorem inv_sp (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) : Inv q (sp A) := fun U ⟨x⟩ => by
  have h := (hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).map
    (show U ⟶ Spec (CommRingCat.of A) from x).appTop.hom
  simpa only [map_natCast] using h

theorem dvd_of_T_eq_pow {T : Type} [CommRing T] [IsDomain T] (q n : ℕ) (w : LaurentPolynomial T)
    (hw : (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial T) = w ^ q) : q ∣ n := by
  obtain ⟨k, f, hf⟩ := LaurentPolynomial.exists_T_pow w
  have h : Polynomial.toLaurent (f ^ q) = Polynomial.toLaurent (Polynomial.X ^ (n + k * q) : Polynomial T) := by
    rw [map_pow, hf, mul_pow, ← hw, Polynomial.toLaurent_X_pow, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
    congr 1
    push_cast
    ring
  have h2 := congrArg Polynomial.natDegree (Polynomial.toLaurent_injective h)
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_pow] at h2
  have h3 : q ∣ n + k * q := ⟨f.natDegree, h2.symm⟩
  exact (Nat.dvd_add_left (dvd_mul_left q k)).mp h3

theorem kum_pow (q : ℕ) [NeZero q] {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) (u : (Γ(X, ⊤))ˣ) (m : ℕ) :
    kum q (u ^ m) = m • kum q u := by
  have hadd : ∀ u v : (Γ(X, ⊤))ˣ, IsUnit (q : Γ(X, ⊤)) → kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0 :=
    fun u v h => (GlobalTheory.T.chernClass_kummerClass_additive q).2 u v h
  have h1 : kum q (1 : (Γ(X, ⊤))ˣ) = 0 := by
    have h := (hadd 1 1 hX).1
    rw [mul_one] at h
    simpa using h
  induction m with
  | zero => rw [pow_zero, zero_smul, h1]
  | succ m ih => rw [pow_succ, (hadd _ _ hX).1, ih, succ_nsmul]

theorem laurentVar_val (T : Type) [CommRing T] :
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial T))).hom.hom ((laurentVar T : Γ(Spec (CommRingCat.of (LaurentPolynomial T)), ⊤))) =
      LaurentPolynomial.T 1 := by
  simp [laurentVar, laurentVarUnit]

end GlobalTheory.EtC.GmAicDeg1

namespace GlobalTheory.EtC.GmAicDeg1

theorem eq_zero_of_cup_kum (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (hT : AIC T)
    (hq : IsUnit (q : T)) (b : Ht q (sp T) 0 0)
    (hb : cup q (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 b) (kum q (laurentVar T)) = 0) :
    b = 0 := by
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh q T (GlobalTheory.GenusTwoPureComparison.Cmp.sh_of_aic hT) hq 0
  have hrep : ∀ x : Ht q (sp T) 0 0, x = (e x).val • e.symm 1 := fun x => by
    apply e.injective
    rw [map_nsmul, AddEquiv.apply_symm_apply, nsmul_one, ZMod.natCast_zmod_val]
  have hqL : IsUnit (q : LaurentPolynomial T) := by simpa using hq.map (LaurentPolynomial.C : T →+* LaurentPolynomial T)
  have hqΓ := GmPhiNat.isUnit_gamma q T hq
  have hκ : ∀ (m : ℕ) (x : Ht q (sp T) 0 0),
      cup q (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 (m • x)) (kum q (laurentVar T)) =
        m • cup q (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 x) (kum q (laurentVar T)) := by
    intro m x
    rw [map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply]
  have hone : pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q 0) 0 (one q (sp T)) =
      one q (sp (LaurentPolynomial T)) := (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).2.1 _ (inv_sp q T hq)
  have hunit := (GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold q (sp (LaurentPolynomial T))).1 (inv_sp q _ hqL) (kum q (laurentVar T))
  have h1 := hκ (e (one q (sp T))).val (e.symm 1)
  rw [← hrep, hone, hunit] at h1
  have h2 := hκ (e b).val (e.symm 1)
  rw [← hrep, hb] at h2
  have h3 : (e b).val • (kum q (laurentVar T)).cast (by ring) (by ring) = (0 : Ht q (sp (LaurentPolynomial T)) (0 + 1) (0 + 1)) := by
    rw [h1, smul_smul, mul_comm, ← smul_smul, ← h2, smul_zero]
  rw [← cast_nsmul, cast_eq_zero_iff] at h3
  have h5 : kum q (laurentVar T ^ (e b).val) = 0 := by rw [kum_pow q hqΓ, h3]
  obtain ⟨v, hv⟩ := GlobalTheory.T.eq_pow_of_kummerClassOfUnit_eq_zero q (LaurentPolynomial T) hqL _ h5
  have h6 := congrArg (fun u : (Γ(Spec (CommRingCat.of (LaurentPolynomial T)), ⊤))ˣ =>
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial T))).hom.hom (u : Γ(Spec (CommRingCat.of (LaurentPolynomial T)), ⊤))) hv
  simp only [Units.val_pow_eq_pow_val, map_pow] at h6
  rw [laurentVar_val, LaurentPolynomial.T_pow, mul_one] at h6
  have h7 := dvd_of_T_eq_pow q (e b).val _ h6
  have h8 : (e b).val = 0 := Nat.eq_zero_of_dvd_of_lt h7 (ZMod.val_lt _)
  rw [ZMod.val_eq_zero] at h8
  exact e.map_eq_zero_iff.1 h8

theorem main : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  intro q _ T _ _ _ hT hq i
  have hinj : Function.Injective (gmPhi q T i) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    simp only [gmPhi, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at ha
    rw [cast_eq_zero_iff] at ha
    obtain ⟨z, hz⟩ : ∃ z : T, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 := by
      obtain ⟨a, ha⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
        (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
      exact ⟨a, by rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]; exact ha⟩
    let ζ : Prim q Γ(Spec (CommRingCat.of T), ⊤) := Prim.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ⟨z, hq, hz⟩
    let τ := Untwist.twistEquiv ζ (inv_sp q T hq) 0 (i - 1) 0
    have hτ : τ a = 0 := by
      apply eq_zero_of_cup_kum q T hT hq
      show cup q (pull _ _ _ 0 ((cup q (rootClass (0 - (i - 1)) ζ) a).cast (zero_add 0) (by ring))) (kum q (laurentVar T)) = 0
      rw [GmPhiNat.pull_cast, Untwist.cup_cast_left, cast_eq_zero_iff, (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).1,
        (GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold q _).2.1, cast_eq_zero_iff, ha, map_zero]
    exact τ.map_eq_zero_iff.1 hτ
  obtain ⟨e0⟩ := GlobalTheory.T.nonempty_ht_zero_addEquiv_zmod_of_sh q T (GlobalTheory.GenusTwoPureComparison.Cmp.sh_of_aic hT) hq (i - 1)
  obtain ⟨e1⟩ := (GlobalTheory.T.tateTwistCohomology_laurent_absIntClosedLocalDomain q T hT hq 1 i).2
  haveI : Finite (Ht q (sp (LaurentPolynomial T)) 1 i) := Finite.of_equiv _ e1.symm.toEquiv
  exact hinj.bijective_of_nat_card_le (by rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv])

end GlobalTheory.EtC.GmAicDeg1

theorem GlobalTheory.EtC.gmPhi_bijective_of_aic : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T],
    AIC T → IsUnit (q : T) → ∀ i : ℤ, Function.Bijective (gmPhi q T i) :=
  GlobalTheory.EtC.GmAicDeg1.main
