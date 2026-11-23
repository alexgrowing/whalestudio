import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
open IsDedekindDomain

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GalSup

section Prime

variable {K : Type} [Field K] [NumberField K]

abbrev primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s).symm la

theorem count_equiv {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [DecidableEq (Associates (Ideal R))] [∀ p : Associates (Ideal R), Decidable (Irreducible p)]
    [DecidableEq (Associates (Ideal S))] [∀ p : Associates (Ideal S), Decidable (Irreducible p)]
    (e : R ≃+* S) (p : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    (Associates.mk (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal).count (Associates.mk (I.comap e.symm)).factors =
      (Associates.mk p.asIdeal).count (Associates.mk I).factors := by
  have hI' : I.comap e.symm ≠ ⊥ := by
    rw [← Ideal.map_comap_of_equiv]
    exact fun h => hI ((Ideal.map_eq_bot_iff_of_injective e.injective).1 h)
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI') (HeightOneSpectrum.associates_irreducible _),
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI) (HeightOneSpectrum.associates_irreducible _),
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le]
  have : (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal = p.asIdeal.map (e : R →+* S) := by
    rw [Ideal.map_comap_of_equiv]; rfl
  rw [this, ← Ideal.map_pow, Ideal.map_comap_of_equiv]
  exact Ideal.comap_le_comap_iff_of_surjective e.symm e.symm.surjective _ _

theorem intValuation_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    (primeBack s la).intValuation a = la.intValuation (RingOfIntegers.mapRingEquiv s a) := by
  classical
  by_cases ha : a = 0
  · subst ha; simp
  have ha' : RingOfIntegers.mapRingEquiv s a ≠ 0 := by simpa using ha
  rw [HeightOneSpectrum.intValuation_if_neg _ ha, HeightOneSpectrum.intValuation_if_neg _ ha']
  have hc : (Ideal.span {RingOfIntegers.mapRingEquiv s a}).comap (RingOfIntegers.mapRingEquiv s).symm.symm =
      Ideal.span {a} := by
    rw [← Ideal.map_comap_of_equiv, Ideal.map_span, Set.image_singleton]
    simp
  have := count_equiv (RingOfIntegers.mapRingEquiv s).symm la
    (I := Ideal.span {RingOfIntegers.mapRingEquiv s a}) (by simpa using ha')
  rw [hc] at this
  rw [this]

theorem valuation_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (x : K) :
    (primeBack s la).valuation K x = la.valuation K (s x) := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hs : ∀ z : 𝓞 K, s (algebraMap (𝓞 K) K z) = algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv s z) :=
    fun _ => rfl
  rw [map_div₀, map_div₀, map_div₀, hs, hs, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_primeBack, intValuation_primeBack]

theorem vLa_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (x : K) :
    vLa (primeBack s la) x = vLa la (s x) := by
  simp only [vLa, valuation_primeBack]

end Prime
end GlobalTheory.GalSup

namespace GlobalTheory.GalSup

section Pts

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

def changeEmbedding {L : Type} [CommRing L] (ι₀ ι₁ : c'.F →+* L) (κ : c.F →+* L)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) (h₁ : ∀ a, ι₁ (incF c c' hle a) = κ a)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' L) : letI := ι₁.toAlgebra; FrPt Xo c' L :=
  letI : Algebra c.F L := κ.toAlgebra
  let y₀ : FrPt Xo c L := (letI : Algebra c'.F L := ι₀.toAlgebra; y.res hle h₀)
  letI : Algebra c'.F L := ι₁.toAlgebra
  y₀.ext hle h₁

theorem evR_rulBC {L : Type} [CommRing L] (ι₀ : c'.F →+* L) (κ : c.F →+* L)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' L) :
    (letI := ι₀.toAlgebra; evR Xo c' (rulBC hle f) y) =
      (letI : Algebra c.F L := κ.toAlgebra; letI := ι₀.toAlgebra; evR Xo c f (y.res hle h₀)) := by
  letI : Algebra c.F L := κ.toAlgebra
  letI := ι₀.toAlgebra
  exact ((rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2 L h₀ y

theorem integral_reread {T : CDVR} (ι₀ ι₁ : c'.F →+* T.Fr) (κ : c.F →+* T.Fr)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) (h₁ : ∀ a, ι₁ (incF c c' hle a) = κ a)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' T.Fr) (hy : Integral T ι₀ y) :
    Integral T ι₁ (changeEmbedding hle ι₀ ι₁ κ h₀ h₁ y) := by
  have key : ∀ (τ : E →+* ℂ) (b : 𝓞 E), ι₁ (embK c' τ b) = ι₀ (embK c' τ b) := fun τ b => by
    rw [← embK_incF hle τ b, h₀, h₁]
  have eig : ∀ (G : SAB H (Sp T.V)) τ (w : epsOver T.V T.V ⟶ G.G),
      IsEigV c' ι₁ G τ w ↔ IsEigV c' ι₀ G τ w := fun G τ w => by
    unfold IsEigV
    simp only [key]
  obtain ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, rest⟩ := hy
  exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (eig G τ _).2 (h2 τ i),
    fun τ w ht he => h3 τ w ht ((eig G τ w).1 he), h4⟩, rest⟩

end Pts
end GlobalTheory.GalSup

namespace GlobalTheory.GalSup

open ReciprocityTheory.ChartRestriction.G

theorem evI_sum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) {m : ℕ}
    (b : Fin m → c.F) (g : Fin m → Rul Xo c) :
    evI y (∑ i, b i • g i) = ∑ i, io (b i) * evI y (g i) := by
  have h := map_sum (AddMonoidHom.mk' (evI y) (evI_add y)) (fun i => b i • g i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at h
  rw [h]
  simp only [evI_smul]

theorem intAt_galois : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : c'.F ≃+* c'.F), (∀ x : c.F, s (incF c c' hle x) = incF c c' hle x) → ∀ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ sec Xo c a n) → IntAt Xo c' (∑ i, as i • rulBC hle (fs i)) → IntAt Xo c' (∑ i, s (as i) • rulBC hle (fs i)) := by
  intro E _ _ _ H Dw l Xo c c' hle a n s hs m as fs hfs hint la v hv
  obtain ⟨⟨q, T, ι, e, ho, y, hy, eta, heta, hq⟩, rfl⟩ := hv
  subst hq
  show 0 ≤ nval T.V e (evI y _)
  let κ : c.F →+* T.Fr := ι.comp (incF c c' hle)
  let ι₁ : c'.F →+* T.Fr := ι.comp (s : c'.F →+* c'.F)
  have h₀ : ∀ x, ι (incF c c' hle x) = κ x := fun _ => rfl
  have h₁ : ∀ x, ι₁ (incF c c' hle x) = κ x := fun x => by
    show ι (s (incF c c' hle x)) = ι (incF c c' hle x)
    rw [hs x]
  let y₁ : IntFr Xo c' T ι₁ := ⟨changeEmbedding hle ι ι₁ κ h₀ h₁ y.1,
    (letI := ι₁.toAlgebra; GlobalTheory.FlagTan.fromTest_of_isLocalRing _), integral_reread hle ι ι₁ κ h₀ h₁ y.1 y.2.2⟩
  have ho₁ : OverLa (primeBack s la) T.V ι₁ e := ⟨ho.1, fun x => by
    rw [vLa_primeBack]; exact ho.2 (s x)⟩
  have key : 0 ≤ nval T.V e (evI y₁ (∑ i, as i • rulBC hle (fs i))) :=
    hint (primeBack s la) _ ⟨PtV.mk (primeBack s la) ho₁ y₁ hy () trivial, rfl⟩
  have e1 : evI y (∑ i, s (as i) • rulBC hle (fs i)) = evI y₁ (∑ i, as i • rulBC hle (fs i)) := by
    rw [evI_sum, evI_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    unfold evI
    rw [evR_rulBC hle ι κ h₀ (hfs i), evR_rulBC hle ι₁ κ h₁ (hfs i)]
    rfl
  rw [e1]
  exact key

end GlobalTheory.GalSup
