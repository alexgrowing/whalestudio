import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEmbeddingOfHomogeneousKerEqStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ResidueGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DescendToThetaConstantFieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KerConeMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjectAtMinimalPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneousStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.GenericObject

theorem isThetaPt_unit_mul {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (v v' : I → Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)) (hc : IsUnit c) (hv : ∀ i, v' i = c * v i)
    (h : Out.IsThetaPt P k x v) : Out.IsThetaPt P k x v' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hp, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  have hc1 : IsUnit (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom c) := hc.map V.ι.appTop.hom
  obtain ⟨c', hc'⟩ := hc1
  refine ⟨V, hp, th, s1, α, τ, U, s2, w, c' * u, a1, a2, a3, a4, a5, a6, a7, fun i => ?_⟩
  have e1 : (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom (v' i)) =
      (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom c) * (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom (v i)) := by
    rw [hv i]
    exact map_mul V.ι.appTop.hom c (v i)
  have e2 : (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom (v i)) = u * w i := a8 i
  rw [← hc', e2, ← _root_.mul_assoc] at e1
  exact e1

theorem hasTh_unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s) {R : Type} [CommRing R] (x : Sp R ⟶ S) (v v' : Ix g (N' ^ 2) → R) (c : R) (hc : IsUnit c)
    (hv : ∀ a, v' a = c * v a) (h : t.HasTh x v) : t.HasTh x v' := by
  refine isThetaPt_unit_mul _ _ _ _ _ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) (hc.map _) (fun a => ?_) h
  rw [hv a]
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c (v a)

theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) : Countable o := by
  obtain ⟨m, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have : Countable (MvPolynomial (Fin m) ℤ) :=
    (MvPolynomial.basisMonomials (Fin m) ℤ).repr.injective.countable
  exact hf.countable

theorem exists_generic_object : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (Y : MMPre n (n ^ j) (thIdeal em C)) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), IsOpenImmersion x → x ≫ Y.s = spMap β → SecCoord Y.de Y.th x v → ∀ q ∈ minimalPrimes R, ∃ (K : Type) (_ : Field K) (y : R →+* K) (e : K →+* ℂ) (t : TObj g ((n ^ j) ^ 2) J b (spMap y ≫ spMap β)) (tc : TObj g ((n ^ j) ^ 2) J b (spMap em)), RingHom.ker y = q ∧ e.comp (y.comp β) = em ∧ C tc ∧ TMap tc t (spMap e) ∧ t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => y (v a)) := by
  intro L1 L2 g J _ Mat κ n w w' hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.descend_to_thetaConstant_field L1 L2 g J Mat κ n w w' hn hodd
  refine ⟨max j₀ 1, fun j hj o _ b em C d har hC Y R _ β x v hx hxs hv q hq => ?_⟩
  have hj0 : j ≥ j₀ := le_trans (le_max_left _ _) hj
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    obtain ⟨m, hm⟩ := hodd
    omega
  have hN3 : 3 ≤ n ^ j := le_trans hn3 (Nat.le_self_pow (by omega) n)
  have hNodd : Odd (n ^ j) := hodd.pow
  haveI hqp : q.IsPrime := hq.1.1
  let K := FractionRing (R ⧸ q)
  let y : R →+* K := (algebraMap (R ⧸ q) K).comp (Ideal.Quotient.mk q)
  have hy0 : ∀ r, y r = 0 ↔ r ∈ q := fun r => by
    simp only [y, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ q) K), Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker y = q := Ideal.ext fun r => by rw [RingHom.mem_ker, hy0]
  have hfrac : ∀ k : K, ∃ r r' : R, y r' ≠ 0 ∧ k * y r' = y r := by
    intro k
    obtain ⟨a, a', ha', rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ q) k
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective a'
    have h0 : algebraMap (R ⧸ q) K (Ideal.Quotient.mk q r') ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := K) ha'
    exact ⟨r, r', h0, div_mul_cancel₀ _ h0⟩
  obtain ⟨c₀, hc₀⟩ := (Y.loc R β x v hxs hv).2 q hqp 0
  set a₀ := (0 : Ix g ((n ^ j) ^ 2)) + (n ^ j / n) • c₀ with ha₀
  have hva : y (v a₀) ≠ 0 := fun h => hc₀ ((hy0 _).1 h)
  obtain ⟨hcl, hmin⟩ := GlobalTheory.CoordChart.residue_generic o g n (n ^ j) (thIdeal em C) Y R β x v K y a₀ (by omega) hx hxs hv hfrac hva
  have hmin' := hmin (by rw [hker]; exact hq)
  obtain ⟨-, hhom, -⟩ := GlobalTheory.T.thetaPointsVanishingIdeal_radical_homogeneous o g (n ^ j) J b em C har.2.2
  have hu : (fun a => y (v a) / y (v a₀)) a₀ = 1 := div_self hva
  have hP := GlobalTheory.ker_cone_mem_minimalPrimes o _ K (thIdeal em C) (y.comp β) (fun a => y (v a) / y (v a₀)) a₀ hhom hu hmin'
  obtain ⟨tc, wv, htc, hth, hkw⟩ := GlobalTheory.ZM.exists_object_at_minimalPrime o g (n ^ j) J b em C Mat κ w w' d L1 L2 hN3 hNodd
    (countable_of_finiteType o har.2.1) hC _ hP
  obtain ⟨e, c, hc, he, hec⟩ := GlobalTheory.T.exists_complex_embedding_scaling_of_ker_eval_eq o K _ (y.comp β) em (fun a => y (v a) / y (v a₀)) wv a₀
    (div_ne_zero hva hva) (by simpa only [div_self hva, div_one] using hcl) hkw.symm
  have heva : e (y (v a₀)) ≠ 0 := (map_ne_zero e).2 hva
  have hth' : tc.HasTh (𝟙 _) (fun a => e (y (v a))) := by
    refine hasTh_unit_mul tc _ wv _ (e (y (v a₀)) * c) (IsUnit.mk0 _ (mul_ne_zero heva hc)) (fun a => ?_) hth
    have := hec a
    simp only [map_div₀] at this
    rw [_root_.mul_assoc, ← this]
    field_simp
  have hs : spMap em = spMap e ≫ spMap (y.comp β) := by
    rw [← he]
    exact Spec.map_comp (CommRingCat.ofHom (y.comp β)) (CommRingCat.ofHom e)
  have hs' : spMap (y.comp β) = spMap y ≫ spMap β :=
    Spec.map_comp (CommRingCat.ofHom β) (CommRingCat.ofHom y)
  have key := hj₀ j hj0 o b K ℂ (y.comp β) e (spMap em) tc (fun a => y (v a)) hs (hC.shape tc htc).1 (hC.shape tc htc).2 hth'
  rw [hs'] at key
  obtain ⟨t, h1, h2, h3, h4⟩ := key
  exact ⟨K, inferInstance, y, e, t, tc, hker, he, htc, h1, h2, h3, h4⟩

end GlobalTheory.GenericObject
end
