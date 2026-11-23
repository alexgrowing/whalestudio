import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmicDerivationLocalizationAtPrimeSpanOfRiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendLocalizationAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdDerivationOfMemSpanProdParamsStatement
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory

theorem derivation_prod_eq_zero_of_forall {F R : Type} [CommRing F] [CommRing R] [Algebra F R]
    (D : Derivation F R R) {ι : Type} (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, D (f i) = 0) :
    D (∏ i ∈ s, f i) = 0 :=
  Finset.prod_induction f (fun y => D y = 0)
    (fun a b ha hb => by rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero])
    (Derivation.map_one_eq_zero D) h

theorem logDet_local_eq_unit_mul_prod :
    ∀ (F A R : Type) [Field F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [IsNoetherianRing A] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] [Algebra.FiniteType F A] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n m : ℕ) (x : Fin n → A) (e : Fin m ↪ Fin n) (J : Finset (Fin m)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun j => algebraMap A R (x (e j))) → (∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i))) → ∀ (I : Ideal A), I.map (algebraMap A R) = Ideal.span {algebraMap A R (∏ j ∈ J, x (e j))} → ∀ (b : Fin n → Derivation ℤ A A), (∀ j c, b j (algebraMap F A c) = 0) → (∀ j, ∀ f ∈ I, b j f ∈ I) → (∀ D : Derivation ℤ A A, (∀ c, D (algebraMap F A c) = 0) → (∀ f ∈ I, D f ∈ I) → ∃ c : Fin n → A, D = ∑ j, c j • b j) → ∃ u : Rˣ, algebraMap A R (GlobalTheory.LogPole.logDet b x) = u * algebraMap A R (∏ j ∈ J, x (e j)) := by
  intro F A R _ _ _ _ _ _ _ _ _ _ _ _ P _ _ n m x e J hrsp hbs I hI b _hbF hbI hspan
  obtain ⟨bs, hbs⟩ := hbs
  set φ := algebraMap A R with hφ
  set r : Fin m → R := fun j => φ (x (e j)) with hr
  set g : R := ∏ j ∈ J, r j with hg
  have hφg : φ (∏ j ∈ J, x (e j)) = g := by rw [map_prod]
  have hIg : I.map φ = Ideal.span {g} := by rw [hI, hφg]

  let dd : Fin n → Derivation F R R := fun i => (bs.coord i).compDer (KaehlerDifferential.D F R)
  have hδ : ∀ i l, dd i (φ (x l)) = if l = i then 1 else 0 := by
    intro i l
    show bs.coord i (KaehlerDifferential.D F R (φ (x l))) = _
    rw [← hbs l, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  let hm : Fin n → R := fun l => if l ∈ J.map e then φ (x l) else 1
  let E : Fin n → Derivation F R R := fun i => hm i • dd i
  have hEapp : ∀ i y, E i y = hm i * dd i y := fun i y => rfl

  have hEg : ∀ i, E i g ∈ Ideal.span {g} := by
    intro i
    rw [hEapp]
    by_cases hi : i ∈ J.map e
    · obtain ⟨j0, hj0, rfl⟩ := Finset.mem_map.mp hi
      have hsplit : g = r j0 * ∏ j ∈ J.erase j0, r j := (Finset.mul_prod_erase J r hj0).symm
      have hrest : dd (e j0) (∏ j ∈ J.erase j0, r j) = 0 := by
        refine derivation_prod_eq_zero_of_forall _ _ _ fun j hj => ?_
        have hne : e j ≠ e j0 := fun h => (Finset.ne_of_mem_erase hj) (e.injective h)
        show dd (e j0) (φ (x (e j))) = 0
        rw [hδ, if_neg hne]
      have hone : dd (e j0) (r j0) = 1 := by
        show dd (e j0) (φ (x (e j0))) = 1
        rw [hδ, if_pos rfl]
      have hmv : hm (e j0) = r j0 := if_pos hi
      have : hm (e j0) * dd (e j0) g = g := by
        conv_lhs => rw [hsplit]
        rw [Derivation.leibniz, hrest, hone, hmv, smul_zero, zero_add, smul_eq_mul, mul_one, ← hsplit]
      rw [this]
      exact Ideal.mem_span_singleton_self g
    · have : dd i g = 0 := by
        refine derivation_prod_eq_zero_of_forall _ _ _ fun j hj => ?_
        have hne : e j ≠ i := fun h => hi (Finset.mem_map.mpr ⟨j, hj, h⟩)
        show dd i (φ (x (e j))) = 0
        rw [hδ, if_neg hne]
      rw [this, mul_zero]
      exact Ideal.zero_mem _
  have hE : ∀ i, ∀ f ∈ I.map φ, E i f ∈ I.map φ := by
    intro i f hf
    rw [hIg] at hf ⊢
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hEg i))
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g))
  choose N hN using fun i => GlobalTheory.T.logarithmicDerivation_localizationAtPrime_span_of_ring F A R P I n b hspan (E i) (hE i)

  choose D' hD' using fun k =>
    GlobalTheory.T.exists_derivation_extend_localization_atPrime ℤ A R P ((Algebra.linearMap A R).compDer (b k))
  have hD'a : ∀ k a, D' k (φ a) = φ (b k a) := fun k a => hD' k a
  have hD'I : ∀ k, ∀ f ∈ I.map φ, D' k f ∈ I.map φ := by
    intro k f hf
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      rw [hD'a]
      exact Ideal.mem_map_of_mem _ (hbI k a ha)
    | zero => rw [map_zero]; exact Ideal.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Ideal.add_mem _ hy hz
    | smul c y hy hy' =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy') (Ideal.mul_mem_right _ _ hy)
  have hdiv : ∀ l k, ∃ c, φ (b k (x l)) = hm l * c := by
    intro l k
    by_cases hl : l ∈ J.map e
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hl
      have hgk : D' k g ∈ Ideal.span {g} := by
        rw [← hIg]; exact hD'I k g (by rw [hIg]; exact Ideal.mem_span_singleton_self g)
      have := GlobalTheory.T.dvd_derivation_of_mem_span_prod_params' R m r hrsp J (D' k) hgk j hj
      obtain ⟨c, hc⟩ := this
      refine ⟨c, ?_⟩
      have hmv : hm (e j) = r j := if_pos hl
      rw [hmv, ← hc]
      exact (hD'a k (x (e j))).symm
    · refine ⟨φ (b k (x l)), ?_⟩
      have hmv : hm l = 1 := if_neg hl
      rw [hmv, one_mul]
  choose M hM using hdiv

  let Bm : Matrix (Fin n) (Fin n) R := Matrix.of fun l k => φ (b k (x l))
  have hBdet : φ (logDet b x) = Bm.det := by
    rw [logDet, RingHom.map_det]
    congr 1
  have h1 : Bm = Matrix.diagonal hm * Matrix.of M := by
    ext l k
    simp [Bm, Matrix.diagonal_mul, hM]
  have h2 : Matrix.diagonal hm = Bm * (Matrix.of N).transpose := by
    ext l i
    rw [Matrix.mul_apply]
    have hsum : ∑ k, Bm l k * (Matrix.of N).transpose k i = ∑ k, N i k * φ (b k (x l)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [Bm, mul_comm]
    rw [hsum, ← hN i (x l), hEapp, hδ, Matrix.diagonal_apply]
    by_cases hli : l = i
    · subst hli; simp
    · simp [hli]
  have hdetD : (Matrix.diagonal hm).det = g := by
    rw [Matrix.det_diagonal]
    have : ∏ l, hm l = ∏ l ∈ J.map e, φ (x l) := by
      rw [← Finset.prod_filter]
      congr 1
      ext l; simp
    rw [this, Finset.prod_map]
  haveI : IsDomain R := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hprime : ∀ j, Prime (r j) := ReciprocityTheory.AnForm.R.prime_of_regular_params r hrsp.1 hrsp.2
  have hg0 : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (hprime j).ne_zero
  have hMN : (Matrix.of M).det * (Matrix.of N).transpose.det = 1 := by
    have h3 : Matrix.diagonal hm = Matrix.diagonal hm * (Matrix.of M * (Matrix.of N).transpose) := by
      conv_lhs => rw [h2, h1]
      rw [Matrix.mul_assoc]
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_mul, Matrix.det_mul, hdetD] at h4
    exact (mul_left_cancel₀ hg0 (h4.symm.trans (mul_one g).symm))
  refine ⟨Units.mkOfMulEqOne _ _ hMN, ?_⟩
  rw [Units.val_mkOfMulEqOne, hφg, hBdet, h1, Matrix.det_mul, hdetD, mul_comm]

end GlobalTheory
