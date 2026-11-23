import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjectAtMinimalPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem eval₂_mul_eq_zero_of_complex {o K₀ K σ : Type} [CommRing o] [Field K₀] [CommRing K] (β : o →+* K₀)
    (i : K₀ →+* K) (j : K₀ →+* ℂ) (v : σ → K₀) (F : MvPolynomial σ o)
    (h : ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval₂ (j.comp β) (fun a => c * j (v a)) F = 0) (u : K) :
    MvPolynomial.eval₂ (i.comp β) (fun a => u * i (v a)) F = 0 := by
  let P : Polynomial K₀ :=
    MvPolynomial.eval₂ (Polynomial.C.comp β) (fun a => Polynomial.X * Polynomial.C (v a)) F
  have key : ∀ {E : Type} [CommRing E] (k : K₀ →+* E) (c : E),
      Polynomial.eval₂RingHom k c P = MvPolynomial.eval₂ (k.comp β) (fun a => c * k (v a)) F := by
    intro E _ k c
    simp only [P]
    rw [MvPolynomial.hom_eval₂]
    congr 1
    · ext r
      simp
    · funext a
      rw [map_mul]
      simp
  have hP : P.map j = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun c hc => ?_)
    change (P.map j).eval c = 0
    rw [Polynomial.eval_map]
    exact (key j c).trans (h c hc)
  rw [Polynomial.map_eq_zero] at hP
  rw [← key, hP, map_zero]

theorem TObj.exists_hasTh_field (hL : Out.Laws) (hL2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (hN : Odd N') :
    ∃ v : Ix g (N' ^ 2) → K, t.HasTh (𝟙 _) v := by
  obtain ⟨R, _, x, v, hx, ⟨p, hp⟩, hth⟩ := GlobalTheory.ThetaLocal.exists_hasTh hL hL2 o g N' J b _ s t hN
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have hr : Set.range (𝟙 (Sp K) : Sp K ⟶ Sp K) ⊆ Set.range x := by
    rintro q -
    exact ⟨p, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift x (𝟙 _) hr)
  have e : spMap φ.hom ≫ x = 𝟙 _ := by
    rw [← IsOpenImmersion.lift_fac x (𝟙 _) hr, ← hφ]
    rfl
  exact ⟨_, e ▸ GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ s t R K φ.hom x v hth⟩

theorem eval₂_eq_zero_of_fromC (hL : Out.Laws) (hL2 : Out.Laws2) {o : Type} [CommRing o] {g n N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {em : o →+* ℂ} {C : TObj g (N' ^ 2) J b (spMap em) → Prop} {S : Scheme.{0}}
    {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} (h2 : 2 ≤ n) (hn : n ∣ N') (hN : Odd N') {K : Type} [Field K]
    {y : Sp K ⟶ S} (hy : FromC em C t y) (β : o →+* K) (hβ : y ≫ s = spMap β) {w : Ix g (N' ^ 2) → K}
    (hw : t.HasTh y w) {F : MvPolynomial (Ix g (N' ^ 2)) o} (hF : F ∈ thIdeal em C) :
    MvPolynomial.eval₂ β w F = 0 := by
  obtain ⟨K₀, _, β₀, i, j, t₀, tx, tc, hem, hs, m1, m2, m3, hC⟩ := hy
  have hβi : β = i.comp β₀ := by
    have e : Spec.map (CommRingCat.ofHom β) = Spec.map (CommRingCat.ofHom β₀ ≫ CommRingCat.ofHom i) := by
      rw [Spec.map_comp]
      exact hβ.symm.trans hs
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have a1 : tx.HasTh (𝟙 _) w :=
    (GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ t _ _ tx y K (𝟙 _) w m1).2 (by rwa [Category.id_comp])
  have a2 : t₀.HasTh (spMap i) w := by
    have := (GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tx (spMap i) K (𝟙 _) w m2).1 a1
    rwa [Category.id_comp] at this
  obtain ⟨v₀, hv₀⟩ := t₀.exists_hasTh_field hL hL2 hN
  have a3 : t₀.HasTh (spMap i) (fun a => i (v₀ a)) := by
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ K i (𝟙 _) v₀ hv₀
    rwa [Category.comp_id] at this
  have hspan : Ideal.span (Set.range fun a => i (v₀ a)) = ⊤ := by
    obtain ⟨a, ha⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b _ _ t₀ n K (spMap i) _ ⊥ h2 hn a3 Ideal.isPrime_bot 0
    rw [Ideal.mem_bot] at ha
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit ha)
  obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ t₀ K (spMap i) _ w a3 a2 hspan
  have a4 : tc.HasTh (𝟙 _) (fun a => j (v₀ a)) := by
    refine (GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tc (spMap j) ℂ (𝟙 _) _ m3).2 ?_
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ ℂ j (𝟙 _) v₀ hv₀
    rw [Category.comp_id] at this
    rwa [Category.id_comp]
  rw [hβi, funext hu]
  refine eval₂_mul_eq_zero_of_complex β₀ i j v₀ F (fun c hc => ?_) u
  have hle : thIdeal em C ≤ RingHom.ker (MvPolynomial.eval₂Hom em (fun a => c * j (v₀ a))) :=
    iInf_le_of_le tc (iInf_le_of_le _ (iInf_le_of_le ⟨hC, a4.unit_mul c hc.isUnit⟩ le_rfl))
  rw [hem]
  exact hle hF

theorem inMM_of_dense_fromSet :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), 2 ≤ n → n ∣ N' → Odd N' → IsReduced S → Dense (fromSet em C t) → IsOpenImmersion x → x ≫ s = spMap β → t.HasTh x v → InMM n N' (thIdeal em C) β v := by
  intro hL hL2 o _ g n N' J b em C S s t R _ β x v h2 hn hN hS hd hx hβ hth
  refine ⟨fun F hF => ?_, fun q hq => GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b S s t n R x v q h2 hn hth hq⟩
  have hR : IsReduced (Sp R) := isReduced_of_isOpenImmersion x
  have hR' : _root_.IsReduced R := (affine_isReduced_iff (CommRingCat.of R)).1 hR
  refine IsNilpotent.eq_zero ((PrimeSpectrum.basicOpen_eq_bot_iff _).1 ?_)
  by_contra hne
  have hd' : Dense (x ⁻¹' fromSet em C t) := hd.preimage x.isOpenEmbedding.isOpenMap
  obtain ⟨q, hq, K, _, y, ⟨p, hp⟩, hy⟩ := hd'.inter_open_nonempty
    (PrimeSpectrum.basicOpen (MvPolynomial.eval₂ β v F) : Set (PrimeSpectrum R))
    (PrimeSpectrum.basicOpen _).isOpen ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne)
  have hr : Set.range y ⊆ Set.range x := by
    rintro _ ⟨p', rfl⟩
    exact ⟨q, by rw [← hp, Subsingleton.elim (α := PrimeSpectrum K) p p']⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift x y hr)
  have e : spMap φ.hom ≫ x = y := by
    rw [← IsOpenImmersion.lift_fac x y hr, ← hφ]
    rfl
  have hq' : PrimeSpectrum.comap φ.hom p = q := by
    apply x.isOpenEmbedding.injective
    rw [← hp, ← e]
    rfl
  have hw : t.HasTh y (fun a => φ.hom (v a)) := e ▸ GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R K φ.hom x v hth
  have hs : y ≫ s = spMap (φ.hom.comp β) := by
    rw [← e, Category.assoc, hβ, ← Spec.map_comp]
    rfl
  have h0 := eval₂_eq_zero_of_fromC hL hL2 h2 hn hN hy _ hs hw hF
  rw [← MvPolynomial.hom_eval₂] at h0
  apply hq
  rw [← hq']
  change φ.hom _ ∈ PrimeSpectrum.asIdeal p
  rw [h0]
  exact Ideal.zero_mem _

end GlobalTheory.ZM
