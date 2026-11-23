import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.HermitianLattices.StatementLat
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocDict

section Lin
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem baer_fractionRing : Module.Baer R K := by
  intro I g
  by_cases hI : I = ⊥
  · subst hI
    refine ⟨0, fun x hx => ?_⟩
    have h0 : x = 0 := by simpa using hx
    subst h0
    have : (⟨0, hx⟩ : (⊥ : Ideal R)) = 0 := rfl
    rw [this, map_zero, map_zero]
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have ha' : algebraMap R K a ≠ 0 := by
      simpa using ha0
    refine ⟨LinearMap.toSpanSingleton R K (g ⟨a, ha⟩ / algebraMap R K a), fun x hx => ?_⟩
    have h1 : a • g ⟨x, hx⟩ = x • g ⟨a, ha⟩ := by
      rw [← map_smul, ← map_smul]
      congr 1
      ext
      simp [mul_comm]
    rw [Algebra.smul_def, Algebra.smul_def] at h1
    rw [LinearMap.toSpanSingleton_apply, Algebra.smul_def]
    field_simp
    rw [← h1]

variable {V : Type} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem exists_functional (L : Submodule R V) (φ : L →ₗ[R] K) :
    ∃ Φ : V →ₗ[K] K, ∀ y : L, Φ (y : V) = φ y := by
  obtain ⟨h, hh⟩ := (baer_fractionRing (R := R) (K := K)).extension_property L.subtype
    L.injective_subtype φ
  exact ⟨LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors R) K h, fun y => congr($hh y)⟩

theorem exists_dual [IsDedekindDomain R] (L : Submodule R V) (hL : L.FG) :
    ∃ (m : ℕ) (b : Fin m → V) (Φ : Fin m → V →ₗ[K] K), (∀ i, b i ∈ L) ∧
      (∀ i, ∀ y ∈ L, ∃ o : R, Φ i y = algebraMap R K o) ∧ ∀ y ∈ L, y = ∑ i, Φ i y • b i := by
  haveI : Module.Finite R L := Module.Finite.iff_fg.2 hL
  have htors : Submodule.torsion R L = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨a, ha⟩, hy⟩
    have hy' : a • y = 0 := hy
    have ha0 : algebraMap R K a ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero ha
    have h2 : a • (y : V) = 0 := congrArg Subtype.val hy'
    rw [← algebraMap_smul K a (y : V)] at h2
    have h3 : (y : V) = 0 := (smul_eq_zero.1 h2).resolve_left ha0
    exact Subtype.ext h3
  haveI : Module.Flat R L := flat_iff_torsion_eq_bot.2 htors
  haveI : Module.FinitePresentation R L := Module.finitePresentation_of_finite R L
  haveI : Module.Projective R L := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin' R L
  obtain ⟨t, ht⟩ := Module.projective_lifting_property g LinearMap.id hg
  choose Φ hΦ using fun i : Fin m =>
    exists_functional (K := K) L ((Algebra.linearMap R K) ∘ₗ (LinearMap.proj i) ∘ₗ t)
  refine ⟨m, fun i => (g fun j => if i = j then 1 else 0 : L), Φ, fun i => Subtype.property _,
    fun i y hy => ⟨t ⟨y, hy⟩ i, hΦ i ⟨y, hy⟩⟩, fun y hy => ?_⟩
  have h1 : g (t ⟨y, hy⟩) = ⟨y, hy⟩ := congr($ht ⟨y, hy⟩)
  have h2 := LinearMap.pi_apply_eq_sum_univ g (t ⟨y, hy⟩)
  rw [h1] at h2
  have h3 := congrArg Subtype.val h2
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
  refine h3.trans (Finset.sum_congr rfl fun i _ => ?_)
  have h4 := hΦ i ⟨y, hy⟩
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, Algebra.linearMap_apply] at h4
  change _ = Φ i y • _
  rw [h4, algebraMap_smul]

end Lin

section Places
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} (A : Places F E sig) {n : ℕ} (p : HeightOneSpectrum (𝓞 F))

theorem exists_bc_map {m : ℕ} (f : (Fin n → E) →ₗ[E] (Fin m → E)) :
    ∃ g : (Fin n → (A.loc p).Ep) →ₗ[(A.loc p).Ep] (Fin m → (A.loc p).Ep),
      ∀ x, g (A.bc p x) = A.bc p (f x) := by
  refine ⟨Matrix.toLin' ((LinearMap.toMatrix' f).map (A.loc p).ιE), fun x => ?_⟩
  funext i
  rw [Matrix.toLin'_apply]
  simp only [Places.bc]
  rw [← LinearMap.toMatrix'_mulVec f x, RingHom.map_mulVec]
  rfl

theorem lat_transfer (Λ : Submodule (𝓞 E) (Fin n → E)) {m : ℕ}
    (f : (Fin n → E) →ₗ[E] (Fin m → E)) (N : Submodule (A.L p).O (Fin m → (A.loc p).Ep))
    (h : ∀ y ∈ Λ, A.bc p (f y) ∈ N) {x : Fin n → E} (hx : A.bc p x ∈ A.lat p Λ) :
    A.bc p (f x) ∈ N := by
  obtain ⟨g, hg⟩ := exists_bc_map A p f
  have hle : A.lat p Λ ≤ N.comap (g.restrictScalars (A.L p).O) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    change g (A.bc p y) ∈ N
    rw [hg]
    exact h y hy
  have h2 : g (A.bc p x) ∈ N := hle hx
  rwa [hg] at h2

theorem exists_den (c : E) (hc : (A.loc p).ιE c ∈ (A.L p).O) :
    ∃ s : 𝓞 F, s ∉ p.asIdeal ∧ ∃ o : 𝓞 E, algebraMap (𝓞 F) E s * c = algebraMap (𝓞 E) E o := by
  obtain ⟨t, k, ht, hk⟩ := PlacesInt.exists_trace_norm A c
  obtain ⟨h1, h2⟩ := (PlacesInt.mem_O_iff A p c t k ht hk).1 hc
  obtain ⟨a, d, had⟩ := p.exists_primeCompl_mul_eq_of_integer t h1
  obtain ⟨b, e, hbe⟩ := p.exists_primeCompl_mul_eq_of_integer k h2
  have e1 : algebraMap (𝓞 F) E a = algebraMap F E t * algebraMap (𝓞 F) E d := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, ← had, map_mul,
      ← IsScalarTower.algebraMap_apply]
  have e2 : algebraMap (𝓞 F) E b = algebraMap F E k * algebraMap (𝓞 F) E e := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, ← hbe, map_mul,
      ← IsScalarTower.algebraMap_apply]
  have hi : IsIntegral (𝓞 F) (algebraMap (𝓞 F) E ((d : 𝓞 F) * e) * c) :=
    PlacesInt.isIntegral_of_quad _ (algebraMap (𝓞 F) E ((d : 𝓞 F) * e) * sig c)
      (a * e) ((d : 𝓞 F) ^ 2 * e * b)
      (by simp only [map_mul, e1, ht]; ring)
      (by simp only [map_mul, map_pow, e2, hk]; ring)
  exact ⟨(d : 𝓞 F) * e, fun h => (p.isPrime.mem_or_mem h).elim d.2 e.2,
    ⟨_, isIntegral_trans (R := ℤ) _ hi⟩, rfl⟩

theorem exists_smul_mem (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Λ.FG) (x : Fin n → E)
    (hx : A.bc p x ∈ A.lat p Λ) :
    ∃ s : 𝓞 F, s ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) s • x ∈ Λ := by
  obtain ⟨m, b, Φ, hb, hΦ, hy⟩ := exists_dual (K := E) Λ hΛ
  let Pr : (Fin n → E) →ₗ[E] (Fin n → E) := LinearMap.id - ∑ i, (Φ i).smulRight (b i)
  have hPr : ∀ y, Pr y = y - ∑ i, Φ i y • b i := fun y => by
    simp [Pr, LinearMap.sum_apply]
  have hx0 : Pr x = 0 := by
    have h1 := lat_transfer A p Λ Pr ⊥ (fun y hy' => by
      have : Pr y = 0 := by rw [hPr, ← hy y hy', sub_self]
      have h0 : A.bc p (0 : Fin n → E) = 0 := by
        funext i
        exact map_zero (A.loc p).ιE
      rw [this, h0]
      exact Submodule.zero_mem _) hx
    have h2 : A.bc p (Pr x) = 0 := h1
    haveI := PlacesInt.nontrivial_Ep (A.loc p)
    funext i
    exact (A.loc p).ιE.injective (by simpa [Places.bc] using congrFun h2 i)
  have hxs : x = ∑ i, Φ i x • b i := by
    rw [hPr, sub_eq_zero] at hx0
    exact hx0
  let N : Submodule (A.L p).O (Fin m → (A.loc p).Ep) :=
    Submodule.pi Set.univ fun _ => (LinearMap.range (Algebra.linearMap (A.L p).O (A.loc p).Ep))
  have hC := lat_transfer A p Λ (LinearMap.pi Φ) N (fun y hy' i _ => by
    obtain ⟨o, ho⟩ := hΦ i y hy'
    have hoO : (A.loc p).ιE (algebraMap (𝓞 E) E o) ∈ (A.L p).O :=
      (PlacesInt.integers_local A).1 _ |>.2 ⟨o, rfl⟩ p
    exact ⟨⟨_, hoO⟩, by simp [Places.bc, ho]; rfl⟩) hx
  have hC' : ∀ i, (A.loc p).ιE (Φ i x) ∈ (A.L p).O := fun i => by
    obtain ⟨o, ho⟩ := hC i (Set.mem_univ _)
    have : (A.loc p).ιE (Φ i x) = o := ho.symm
    rw [this]
    exact o.2
  choose s hs o ho using fun i => exists_den A p (Φ i x) (hC' i)
  refine ⟨∏ i, s i, fun h => ?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := p.isPrime)).1 h
    exact hs i hi
  · rw [hxs, Finset.smul_sum]
    refine Λ.sum_mem fun i _ => ?_
    have e : (algebraMap (𝓞 F) (𝓞 E) (∏ j, s j)) • (Φ i x • b i)
        = (algebraMap (𝓞 F) (𝓞 E) (∏ j ∈ Finset.univ.erase i, s j) * o i) • b i := by
      rw [← algebraMap_smul E (algebraMap (𝓞 F) (𝓞 E) (∏ j, s j)), smul_smul,
        ← algebraMap_smul E (_ * o i)]
      congr 1
      rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i), map_mul, map_mul, map_mul,
        ← ho i, ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E (s i)]
      ring
    rw [e]
    exact Λ.smul_mem _ (hb i)

include A in

theorem exists_base_smul_mem (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal →
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ) :
    ∃ a : 𝓞 F, a ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) a • x ∈ Λ := by
  let I : Ideal (𝓞 E) := Λ.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
  have hI : ∀ s, s ∈ I ↔ s • x ∈ Λ := fun s => by simp [I]
  let q : Ideal (𝓞 E) := Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p.asIdeal
  haveI := p.isMaximal
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) = ⊥ := (RingHom.injective_iff_ker_eq_bot _).1 hinj
  obtain ⟨Q0, hQ0m, hQ0⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) p.asIdeal
    (by rw [hker]; exact bot_le)
  have hq : q ≠ ⊤ := fun h => hQ0m.ne_top (top_le_iff.1 (h ▸ Ideal.map_le_iff_le_comap.2 hQ0.ge))
  have hsup : I ⊔ q = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_le_maximal _ hne
    have hqQ : q ≤ Q := le_sup_right.trans hQ
    have hp' : p.asIdeal ≤ Q.comap (algebraMap (𝓞 F) (𝓞 E)) := Ideal.map_le_iff_le_comap.1 hqQ
    have hc : Q.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal :=
      (p.isMaximal.eq_of_le (Ideal.comap_ne_top _ hQm.ne_top) hp').symm
    have hbot : Q ≠ ⊥ := by
      rintro rfl
      apply p.ne_bot
      rw [eq_bot_iff, ← hc]
      intro z hz
      have : algebraMap (𝓞 F) (𝓞 E) z = 0 := hz
      exact (map_eq_zero_iff _ hinj).1 this
    obtain ⟨s, hs, hsx⟩ := h ⟨Q, hQm.isPrime, hbot⟩ hc
    exact hs (hQ (Ideal.mem_sup_left ((hI s).2 hsx)))
  have h1 : (1 : 𝓞 E) ∈ I ⊔ q := by rw [hsup]; trivial
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (sig : E →+* E)
  have hσc : ∀ z : 𝓞 E, ((σ z : 𝓞 E) : E) = sig z := fun _ => rfl
  have hσq : ∀ z ∈ q, σ z ∈ q := by
    have : q ≤ q.comap σ := Ideal.map_le_iff_le_comap.2 fun a ha => by
      have e : σ (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
        apply RingOfIntegers.ext
        rw [hσc]
        change sig (algebraMap (𝓞 E) E _) = algebraMap (𝓞 E) E _
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E,
          AlgHom.commutes]
      change σ _ ∈ q
      rw [e]
      exact Ideal.mem_map_of_mem _ ha
    exact fun z hz => this hz
  obtain ⟨-, k, -, hk⟩ := PlacesInt.exists_trace_norm A (s : E)
  have hint : IsIntegral ℤ k := by
    have : IsIntegral ℤ (algebraMap F E k) := by
      rw [hk]
      exact (s * σ s).isIntegral_coe
    exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 this
  let a : 𝓞 F := ⟨k, hint⟩
  have ha : algebraMap (𝓞 F) (𝓞 E) a = s * σ s := by
    apply RingOfIntegers.ext
    change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    exact hk
  refine ⟨a, fun hap => ?_, ?_⟩
  · have h2 : s * σ s ∈ q := ha ▸ Ideal.mem_map_of_mem _ hap
    have hs' : s = 1 - t := eq_sub_of_add_eq hst
    have hσs : σ s = 1 - σ t := by rw [hs', map_sub, map_one]
    have e : (1 : 𝓞 E) = s * σ s + t + σ t - t * σ t := by
      rw [hσs, hs']
      ring
    have h3 : (1 : 𝓞 E) ∈ q := by
      rw [e]
      exact q.sub_mem (q.add_mem (q.add_mem h2 ht) (hσq _ ht)) (q.mul_mem_right _ ht)
    exact hq ((Ideal.eq_top_iff_one _).2 h3)
  · rw [ha]
    exact (hI _).1 (I.mul_mem_right _ hs)

theorem bc_mem_of_smul_mem (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) (a : 𝓞 F)
    (ha : a ∉ p.asIdeal) (h : algebraMap (𝓞 F) (𝓞 E) a • x ∈ Λ) : A.bc p x ∈ A.lat p Λ := by
  have hv : p.valuation F (algebraMap (𝓞 F) F a) = 1 :=
    le_antisymm (p.valuation_le_one a)
      (not_lt.1 fun hlt => ha ((p.valuation_lt_one_iff_mem (K := F) a).1 hlt))
  have hinv : p.valuation F (algebraMap (𝓞 F) F a)⁻¹ ≤ 1 := by rw [map_inv₀, hv, inv_one]
  have hO := (PlacesInt.mem_int_iff (A.loc p) _).2 hinv
  have ha0 : algebraMap (𝓞 F) F a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  let w : (A.L p).O := ⟨algebraMap (A.loc p).Fp (A.loc p).Ep
      ((A.loc p).ιF (algebraMap (𝓞 F) F a)⁻¹), ((A.L p).O_def _).2 (by
    have : IsIntegral 𝒪[(A.loc p).Fp] (algebraMap 𝒪[(A.loc p).Fp] (A.loc p).Ep ⟨_, hO⟩) :=
      isIntegral_algebraMap
    exact this)⟩
  have e : A.bc p x = w • A.bc p (algebraMap (𝓞 F) (𝓞 E) a • x) := by
    funext i
    have h1 : (A.loc p).ιE (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)) =
        algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF (algebraMap (𝓞 F) F a)) := by
      rw [← (A.loc p).compat, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply (𝓞 F) F E]
    change (A.loc p).ιE (x i) = algebraMap (A.loc p).Fp (A.loc p).Ep
      ((A.loc p).ιF (algebraMap (𝓞 F) F a)⁻¹) *
        (A.loc p).ιE (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) * x i)
    rw [map_mul, h1, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ ha0, map_one, map_one,
      one_mul]
  rw [e]
  exact Submodule.smul_mem _ w (Submodule.subset_span ⟨_, h, rfl⟩)

end Places

theorem mem_lat_iff_mem_locP : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Λ.FG → ∀ (p : HeightOneSpectrum (𝓞 F)) (x : Fin n → E), (A.bc p x ∈ A.lat p Λ ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal → x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) := by
  intro F E _ _ _ _ _ sig A n Λ hΛ p x
  constructor
  · intro hx P hP
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem A p Λ hΛ x hx
    haveI := P.isPrime
    refine ⟨algebraMap (𝓞 F) (𝓞 E) s, fun h => hs ?_, hsx⟩
    rw [← hP]
    exact h
  · intro h
    obtain ⟨a, ha, hax⟩ := exists_base_smul_mem A p Λ x fun P hP => by
      haveI := P.isPrime
      obtain ⟨s, hs, hsx⟩ := h P hP
      exact ⟨s, hs, hsx⟩
    exact bc_mem_of_smul_mem A p Λ x a ha hax

end GlobalTheory.HL.LocDict
