import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace GlobalTheory.CompanionTheory.EllCRT

private theorem monic_of_mem_normalizedFactors' {K : Type} [Field K] {P q : K[X]}
    (hq : q ∈ UniqueFactorizationMonoid.normalizedFactors P) : q.Monic := by
  have hq0 : q ≠ 0 := (UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq).ne_zero
  rw [← UniqueFactorizationMonoid.normalize_normalized_factor q hq]
  exact Polynomial.monic_normalize hq0

private theorem span_sup_span_eq_unit_ideal_of_ne_normalizedFactors {K : Type} [Field K] {P p q : K[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors P)
    (hq : q ∈ UniqueFactorizationMonoid.normalizedFactors P) (hpq : p ≠ q) :
    Ideal.span {p} ⊔ Ideal.span {q} = ⊤ := by
  have hpi : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hqi : Irreducible q := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
  have hcop : IsCoprime p q := by
    rw [Irreducible.coprime_iff_not_dvd hpi]
    intro hd
    exact hpq (Polynomial.eq_of_monic_of_associated (monic_of_mem_normalizedFactors' hp)
      (monic_of_mem_normalizedFactors' hq) (hpi.associated_of_dvd hqi hd))
  exact (Ideal.sup_eq_top_iff_isCoprime p q).mpr hcop

theorem exists_congr_monic_factors {K : Type} [Field K] {P : K[X]} (hP : P ≠ 0) (t : K[X] → K[X]) :
    ∃ m : K[X], ∀ f : K[X], f.Monic → Irreducible f → f ∣ P → f ∣ m - t f := by
  classical
  let S : Finset K[X] := (UniqueFactorizationMonoid.normalizedFactors P).toFinset
  have hcop : Pairwise (Function.onFun IsCoprime (fun i : S => Ideal.span {(i : K[X])})) := by
    intro i j hij
    show IsCoprime (Ideal.span {(i : K[X])}) (Ideal.span {(j : K[X])})
    exact Ideal.isCoprime_iff_sup_eq.mpr (span_sup_span_eq_unit_ideal_of_ne_normalizedFactors (Multiset.mem_toFinset.mp i.2)
      (Multiset.mem_toFinset.mp j.2) (fun h => hij (Subtype.ext h)))
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal hcop (fun i : S => t i)
  refine ⟨r, fun f hfm hfi hfP => ?_⟩
  obtain ⟨q, hq, hfq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hP hfi hfP
  have hfeq : f = q := Polynomial.eq_of_monic_of_associated hfm (monic_of_mem_normalizedFactors' hq) hfq
  subst hfeq
  have h := hr ⟨f, Multiset.mem_toFinset.mpr hq⟩
  exact Ideal.mem_span_singleton.mp h

private theorem adjoinRoot_exists_mk_eq {R : Type} [CommRing R] {f : R[X]} (x : AdjoinRoot f) :
    ∃ p : R[X], AdjoinRoot.mk f p = x :=
  AdjoinRoot.mk_surjective x

private theorem adjoinRoot_mk_eq_of_selfRecip_val_eq {E : Type} [Field E] [NumberField E] [IsCMField E]
    (g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q) {r r' : ℕ} (Q : SelfRecip E r)
    (Q' : SelfRecip E r') (hQ : Q'.1 = Q.1) (l : E[X])
    (hl : (AdjoinRoot.mk Q'.1 l : Fld Q') = g r' Q') :
    (AdjoinRoot.mk Q.1 l : Fld Q) = g r Q := by
  have h1 : Q'.1.natDegree = r' := Q'.2.2.2.1
  have h2 : Q.1.natDegree = r := Q.2.2.2.1
  rw [hQ] at h1
  have hrr : r' = r := h1.symm.trans h2
  subst hrr
  obtain rfl : Q' = Q := Subtype.ext hQ
  exact hl

private theorem exists_polynomial_lift_adjoinRoot_selfRecip {E : Type} [Field E] [NumberField E] [IsCMField E]
    (g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q) :
    ∃ t : E[X] → E[X], ∀ (r : ℕ) (Q : SelfRecip E r),
      (AdjoinRoot.mk Q.1 (t Q.1) : Fld Q) = g r Q := by
  classical
  refine ⟨fun f => if h : ∃ Q' : SelfRecip E f.natDegree, Q'.1 = f then
      (adjoinRoot_exists_mk_eq (f := h.choose.1) (g f.natDegree h.choose)).choose else 0, ?_⟩
  intro r Q
  have hex : ∃ Q' : SelfRecip E Q.1.natDegree, Q'.1 = Q.1 :=
    ⟨⟨Q.1, by rw [Q.2.2.2.1]; exact Q.2⟩, rfl⟩
  dsimp only
  rw [dif_pos hex]
  exact adjoinRoot_mk_eq_of_selfRecip_val_eq g Q hex.choose hex.choose_spec _
    (adjoinRoot_exists_mk_eq (f := hex.choose.1) (g Q.1.natDegree hex.choose)).choose_spec

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E),
    γ₀.val.charpoly ∈ Ell E n → ∀ g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q, ∃ m : E[X],
      ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly →
        (AdjoinRoot.mk Q.1 m : Fld Q) = g r Q := by
  intro E _ _ _ n γ₀ _ g
  obtain ⟨t, ht⟩ := exists_polynomial_lift_adjoinRoot_selfRecip g
  obtain ⟨m, hm⟩ := exists_congr_monic_factors (Matrix.charpoly_monic γ₀.val).ne_zero t
  refine ⟨m, fun r Q hQ => ?_⟩
  rw [← ht r Q]
  exact AdjoinRoot.mk_eq_mk.mpr (hm Q.1 Q.2.1 Q.2.2.1 hQ)

end GlobalTheory.CompanionTheory.EllCRT
