import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodUnramUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemHcompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodulaStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminanStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeBadPrimesIffGramDetStatement

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped ENNReal Classical

namespace GlobalTheory.Mass.MaxGenus

section Abstract

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def extForm (h : V →ₗ⋆[K] V →ₗ[K] K) (π : K) : (V × K) →ₗ⋆[K] (V × K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun z w => h z.1 w.1 + star z.2 * π * w.2)
    (fun a b w => by simp; ring)
    (fun c a w => by simp [LinearMap.map_smulₛₗ, starRingEnd_apply]; ring)
    (fun a b w => by simp; ring)
    (fun c a w => by simp; ring)

theorem extForm_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (π : K) (z w : V × K) :
    extForm h π z w = h z.1 w.1 + star z.2 * π * w.2 := rfl

theorem extForm_symm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {π : K} (hπ : star π = π) :
    (extForm h π).IsSymm := by
  refine ⟨fun z w => ?_⟩
  rw [extForm_apply, extForm_apply, starRingEnd_apply, star_add, LocWitt.symm' hs]
  simp only [star_mul', star_star, hπ]
  ring

theorem extForm_nondeg {h : V →ₗ⋆[K] V →ₗ[K] K} (hn : h.Nondegenerate) {π : K} (h0 : π ≠ 0) :
    (extForm h π).Nondegenerate := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have a : z.1 = 0 := hn.1 _ fun y => by simpa [extForm_apply] using hz (y, 0)
    have b : z.2 = 0 := by simpa [extForm_apply, h0] using hz (0, 1)
    exact Prod.ext a b
  · have a : z.1 = 0 := hn.2 _ fun y => by simpa [extForm_apply] using hz (y, 0)
    have b : z.2 = 0 := by simpa [extForm_apply, h0] using hz (0, 1)
    exact Prod.ext a b

theorem abs_unimod {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {Λ : AddSubgroup V} {A : Subring K}
    (hA : ∀ a ∈ A, star a ∈ A) (hΛ : ∀ a ∈ A, ∀ v ∈ Λ, a • v ∈ Λ) (hi : ∀ v ∈ Λ, ∀ w ∈ Λ, h v w ∈ A)
    {π c : K} {x : V} (πA : π ∈ A) (π0 : π ≠ 0) (πs : star π = π) (hx : x ∈ Λ) (a0 : h x x ≠ 0)
    (cA : c ∈ A) (c0 : c ≠ 0) (cN : (star c * c)⁻¹ ∈ A) (πa : π / h x x ∈ A)
    (hm : ∀ m ∈ Λ, h m x / π ∈ A) (hG : (star c * c * h x x + π) / π ^ 2 ∈ A)
    (hd : ∀ y, (∀ m ∈ Λ, h m y ∈ A) → ∃ r ∈ A, y - (r * (h x x)⁻¹) • x ∈ Λ) (z : V × K) :
    (∀ w : V × K, (π * w.2 ∈ A ∧ w.1 - (w.2 * c) • x ∈ Λ) → extForm h π w z ∈ A) ↔
      (π * z.2 ∈ A ∧ z.1 - (z.2 * c) • x ∈ Λ) := by
  have sc0 : star c ≠ 0 := star_ne_zero.2 c0
  obtain ⟨v, t⟩ := z
  constructor
  · intro H
    obtain ⟨r, rA, hr⟩ := hd v fun m hm => by
      simpa [extForm_apply] using H (m, 0) ⟨by simpa using A.zero_mem, by simpa using hm⟩
    have E := H ((π⁻¹ * c) • x, π⁻¹) ⟨by simpa [π0] using A.one_mem, by simpa using Λ.zero_mem⟩
    have F := hA _ (hm _ hr)
    rw [star_div₀, LocWitt.symm' hs, πs] at F
    simp only [extForm_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply,
      star_mul', star_inv₀, πs, smul_eq_mul] at E
    simp only [map_sub, map_smul, smul_eq_mul] at F
    have T : π * t ∈ A := by
      have := A.sub_mem (A.mul_mem πA E) (A.mul_mem (hA _ cA) (A.add_mem rA (A.mul_mem πA F)))
      convert this using 1
      field_simp
      ring
    refine ⟨T, ?_⟩
    have S := A.mul_mem (A.mul_mem (A.mul_mem πa cA) cN)
      (A.sub_mem (A.sub_mem E (A.mul_mem (hA _ cA) F)) (A.mul_mem T hG))
    have := Λ.add_mem hr (hΛ _ S x hx)
    convert this using 1
    rw [sub_add, ← sub_smul]
    congr 2
    field_simp
    ring
  · rintro ⟨T, hv⟩ ⟨v', t'⟩ ⟨T', hv'⟩
    have F := hA _ (hm _ hv)
    have T'' := hA _ T'
    rw [star_div₀, LocWitt.symm' hs, πs] at F
    rw [star_mul', πs] at T''
    have := A.add_mem (A.add_mem (hi _ hv' _ hv) (A.mul_mem (A.mul_mem T cA) (hm _ hv')))
      (A.add_mem (A.mul_mem (A.mul_mem T'' (hA _ cA)) F) (A.mul_mem (A.mul_mem T'' T) hG))
    convert this using 1
    simp only [extForm_apply, map_sub, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      LinearMap.sub_apply, starRingEnd_apply, star_mul', smul_eq_mul, RingHom.id_apply]
    field_simp
    ring

theorem restrict [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {π : K} (π0 : π ≠ 0)
    {G : (V × K) ≃ₗ[K] (V × K)} (hG : G ∈ isom (extForm h π)) (hy : G (0, 1) = (0, 1)) :
    ∃ g ∈ isom h, ∀ v, G (v, 0) = (g v, 0) := by
  have h2 : ∀ v, (G (v, 0)).2 = 0 := fun v => by
    have := hG (0, 1) (v, 0)
    rw [hy] at this
    simpa [extForm_apply, π0] using this
  let f : V →ₗ[K] V := LinearMap.fst K V K ∘ₗ (G : V × K →ₗ[K] V × K) ∘ₗ LinearMap.inl K V K
  have hf : ∀ v, G (v, 0) = (f v, 0) := fun v => Prod.ext rfl (h2 v)
  have inj : Function.Injective f := fun a b e => by
    have : G (a, 0) = G (b, 0) := by rw [hf, hf, e]
    exact congrArg Prod.fst (G.injective this)
  refine ⟨LinearEquiv.ofInjectiveEndo f inj, fun a b => ?_, hf⟩
  have := hG (a, 0) (b, 0)
  rw [hf, hf] at this
  simpa [extForm_apply] using this

theorem norm_onto {k : Type} [Field k] [Finite k] (σ : k →+* k) (hσ : ∀ a, σ (σ a) = a)
    {θ : k} (hθ : θ - σ θ ≠ 0) {u : k} (hu : σ u = u) : ∃ c, σ c * c = u := by
  let F := RingHom.eqLocusField σ (RingHom.id k)
  have mF : ∀ a, a ∈ F ↔ σ a = a := fun a => Iff.rfl
  obtain ⟨a, b, e⟩ := unimodUnramUnique_ff (k := F) ⟨θ + σ θ, (mF _).2 (by rw [map_add, hσ, add_comm])⟩
    ⟨θ * σ θ, (mF _).2 (by rw [map_mul, hσ, mul_comm])⟩ ⟨u, hu⟩ (fun e => by
      have := congrArg F.subtype e
      simp only [map_sub, map_pow, map_mul, map_ofNat, map_zero, Subfield.coe_subtype] at this
      exact pow_ne_zero 2 hθ (by linear_combination this))
  have := congrArg F.subtype e
  simp only [map_add, map_pow, map_mul, Subfield.coe_subtype] at this
  refine ⟨a + b * θ, ?_⟩
  rw [map_add, map_mul, (mF a).1 a.2, (mF b).1 b.2]
  linear_combination this

end Abstract

section Local

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem hstar (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
  LocWitt.star_int r

theorem mem_loc {W : Type} [AddCommGroup W] [Module (𝓞 K) W] {p : HeightOneSpectrum (𝓞 K)}
    (hc : conjIdeal (K := K) p.asIdeal = p.asIdeal) (L : Submodule (𝓞 K) W) (v : W) :
    v ∈ loc (K := K) p.asIdeal L ↔ ∃ s, s ∉ p.asIdeal ∧ s • v ∈ L :=
  exists_congr fun s => and_congr_left' (LocWitt.mem_hcompl p.isMaximal hc s)

theorem val_one {p : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∉ p.asIdeal) :
    p.valuation K (algebraMap (𝓞 K) K s) = 1 :=
  le_antisymm (p.valuation_le_one s) (not_lt.1 fun a => hs ((p.valuation_lt_one_iff_mem s).1 a))

theorem mem_locR {p : HeightOneSpectrum (𝓞 K)} (hc : conjIdeal (K := K) p.asIdeal = p.asIdeal)
    (a : K) : a ∈ locR (K := K) p.asIdeal ↔ p.valuation K a ≤ 1 := by
  rw [locR, mem_loc hc]
  constructor
  · rintro ⟨s, hs, hr⟩
    obtain ⟨r, e⟩ := Submodule.mem_one.1 hr
    have : p.valuation K (algebraMap (𝓞 K) K r) ≤ 1 := p.valuation_le_one r
    rwa [e, Algebra.smul_def, map_mul, val_one hs, one_mul] at this
  · intro ha
    obtain ⟨n, d, e⟩ := p.exists_primeCompl_mul_eq_of_integer a ha
    exact ⟨d, d.2, Submodule.mem_one.2 ⟨n, by rw [Algebra.smul_def, mul_comm, e]⟩⟩

theorem star_notMem {p : HeightOneSpectrum (𝓞 K)} (hc : conjIdeal (K := K) p.asIdeal = p.asIdeal)
    {s t : 𝓞 K} (e : algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s)) (hs : s ∉ p.asIdeal) :
    t ∉ p.asIdeal := fun a => hs (by
  rw [← hc]
  exact Ideal.subset_span ⟨t, a, by rw [e, star_star]⟩)

theorem star_le {p : HeightOneSpectrum (𝓞 K)} (hc : conjIdeal (K := K) p.asIdeal = p.asIdeal)
    (a : K) (ha : p.valuation K a ≤ 1) : p.valuation K (star a) ≤ 1 := by
  obtain ⟨n, d, e⟩ := p.exists_primeCompl_mul_eq_of_integer a ha
  obtain ⟨n', en⟩ := hstar n
  obtain ⟨d', ed⟩ := hstar (d : 𝓞 K)
  have : p.valuation K (algebraMap (𝓞 K) K n') ≤ 1 := p.valuation_le_one n'
  rwa [en, ← e, star_mul', ← ed, map_mul, val_one (star_notMem hc ed d.2), mul_one] at this

theorem smul_mem_loc {p : HeightOneSpectrum (𝓞 K)} (hc : conjIdeal (K := K) p.asIdeal = p.asIdeal)
    (L : Submodule (𝓞 K) V) (a : K) (ha : p.valuation K a ≤ 1) (v : V)
    (hv : v ∈ loc (K := K) p.asIdeal L) : a • v ∈ loc (K := K) p.asIdeal L := by
  obtain ⟨n, d, e⟩ := p.exists_primeCompl_mul_eq_of_integer a ha
  obtain ⟨s, hs, e'⟩ := (mem_loc hc L v).1 hv
  refine (mem_loc hc L _).2 ⟨d * s, fun b => (p.isPrime.mem_or_mem b).elim d.2 hs, ?_⟩
  have : ((d : 𝓞 K) * s) • a • v = n • s • v := by
    rw [← algebraMap_smul K ((d : 𝓞 K) * s), ← algebraMap_smul K n, ← algebraMap_smul K s, smul_smul,
      smul_smul, ← e, map_mul]
    congr 1; ring
  rw [this]
  exact L.smul_mem n e'

theorem val_unif {p : HeightOneSpectrum (𝓞 K)} {a : 𝓞 K} (h1 : a ∈ p.asIdeal) (h2 : a ∉ p.asIdeal ^ 2) :
    p.valuation K (algebraMap (𝓞 K) K a) = WithZero.exp (-1 : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  have a1 := (p.intValuation_le_pow_iff_mem a 1).2 (by simpa using h1)
  have a2 := mt (p.intValuation_le_pow_iff_mem a 2).1 h2
  have a0 : p.intValuation a ≠ 0 := fun e => a2 (by rw [e]; exact zero_le)
  rw [← WithZero.exp_log a0, WithZero.exp_le_exp] at a1 a2
  rw [← WithZero.exp_log a0, WithZero.exp_inj]
  omega

theorem le_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases a0 : x = 0
  · rw [a0]; exact zero_le
  rw [← WithZero.exp_log a0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [← WithZero.exp_log a0, WithZero.exp_le_exp]
  omega

theorem exists_norm (hK : IsCMUnram K) {p : HeightOneSpectrum (𝓞 K)}
    (hc : conjIdeal (K := K) p.asIdeal = p.asIdeal) {u : K} (hu : p.valuation K u ≤ 1)
    (us : star u = u) : ∃ c : K, p.valuation K c ≤ 1 ∧ p.valuation K (star c * c - u) < 1 := by
  have inj : Function.Injective (algebraMap (𝓞 K) K) := RingOfIntegers.coe_injective
  let σ := locBasic_sigma inj hstar
  have hσ : ∀ r, algebraMap (𝓞 K) K (σ r) = star (algebraMap (𝓞 K) K r) := locBasic_sigma_spec inj hstar
  have hle : p.asIdeal ≤ p.asIdeal.comap σ := by
    rw [← locBasic_conj_eq inj hstar, hc]
  have := p.isMaximal
  letI : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ p.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ p.ne_bot
  let τ := Ideal.quotientMap p.asIdeal σ hle
  have hτ : ∀ r, τ (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (σ r) := fun r => rfl
  have σσ : ∀ r, σ (σ r) = r := fun r => inj (by rw [hσ, hσ, star_star])
  obtain ⟨θ, t, et, hθ⟩ := hK.2.2 _ p.isMaximal
  obtain ⟨n, d, e⟩ := p.exists_primeCompl_mul_eq_of_integer u hu
  have fix : σ (n * σ d) = n * σ d := inj (by
    rw [hσ, map_mul, hσ, ← e, star_mul', star_mul', star_star, us]; ring)
  obtain ⟨c, ec⟩ := norm_onto τ (fun a => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [hτ, hτ, σσ]) (θ := Ideal.Quotient.mk _ θ) (u := Ideal.Quotient.mk _ (n * σ d))
    (by
      rw [hτ, ← map_sub, Ne, Ideal.Quotient.eq_zero_iff_mem, show σ θ = t from inj (by rw [hσ, et])]
      exact hθ) (by rw [hτ, fix])
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [hτ, ← map_mul, Ideal.Quotient.eq] at ec
  have d1 := val_one (K := K) d.2
  have d2 := val_one (K := K) (star_notMem hc (hσ d) d.2)
  have d0 : algebraMap (𝓞 K) K d ≠ 0 := fun z => by simp [z] at d1
  have d0' : star (algebraMap (𝓞 K) K d) ≠ 0 := star_ne_zero.2 d0
  refine ⟨algebraMap (𝓞 K) K c / algebraMap (𝓞 K) K d, ?_, ?_⟩
  · rw [map_div₀, d1, div_one]; exact p.valuation_le_one c
  · have : star (algebraMap (𝓞 K) K c / algebraMap (𝓞 K) K d) * (algebraMap (𝓞 K) K c / algebraMap (𝓞 K) K d) - u
        = algebraMap (𝓞 K) K (σ c * c - n * σ d) / (algebraMap (𝓞 K) K (σ d) * algebraMap (𝓞 K) K d) := by
      rw [map_sub, map_mul, map_mul, hσ, hσ, ← e, star_div₀]
      field_simp
    rw [this, map_div₀, map_mul, d1, d2, mul_one, div_one]
    exact (p.valuation_lt_one_iff_mem _).2 ec

theorem loc_int {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {M : Submodule (𝓞 K) V} (hM : IsIntLat h M)
    {P : Ideal (𝓞 K)} (hP : P.IsPrime) :
    dualAt h P (loc (K := K) P M) = loc (K := K) P (dual h M) ∧
      loc (K := K) P M ≤ loc (K := K) P (dual h M) := by
  have a := ((locDual (𝓞 K) K V h hs hstar M hM.1.fg).1 P hP)
  exact ⟨a.2.trans a.1.symm, locBasic_locS_mono _ (((dualBasic (𝓞 K) K V h hs hstar).2.2.2.1 M).1 hM.2)⟩

theorem exists_ext [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} (hK : IsCMUnram K) (hs : h.IsSymm)
    (hn : h.Nondegenerate) {M : Submodule (𝓞 K) V} (hM : IsMaxLat h M) {p : HeightOneSpectrum (𝓞 K)}
    (hb : p.asIdeal ∈ badP h M) {π : K} (πs : star π = π)
    (πv : p.valuation K π = WithZero.exp (-1 : ℤ)) :
    ∃ L : Submodule (𝓞 K) (V × K), Submodule.IsLattice K L ∧ IsUnimodularAt (extForm h π) p.asIdeal L ∧
      (0, 1) ∈ loc (K := K) p.asIdeal L ∧
      (∃ w ∈ loc (K := K) p.asIdeal L, extForm h π w (0, 1) = 1) ∧
      ∀ v, (v, 0) ∈ loc (K := K) p.asIdeal L ↔ v ∈ loc (K := K) p.asIdeal M := by
  obtain ⟨hc, -, -, x, xM, ⟨a, ea, a1, a2⟩, hd⟩ := (GlobalTheory.T.maximalHermitianLattice_local_structure_discriminant K V h hK hs hn M hM).2.2.2 _ hb
  have av : p.valuation K (h x x) = WithZero.exp (-1 : ℤ) := ea ▸ val_unif a1 a2
  have a0 : h x x ≠ 0 := fun z => WithZero.exp_ne_zero (by rw [← av, z, map_zero])
  have π0 : π ≠ 0 := fun z => WithZero.exp_ne_zero (by rw [← πv, z, map_zero])
  have e0 : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  obtain ⟨l1, l2⟩ := loc_int hs hM.1 p.isPrime
  have xL : x ∈ loc (K := K) p.asIdeal M := locBasic_le_locS _ _ xM
  have md : ∀ y, y ∈ loc (K := K) p.asIdeal (dual h M) ↔
      ∀ m ∈ loc (K := K) p.asIdeal M, p.valuation K (h m y) ≤ 1 := fun y => by
    rw [← l1, locDual_mem_dualAt]
    simp only [mem_locR hc]
  have uv : p.valuation K (-π / h x x) = 1 := by
    rw [map_div₀, Valuation.map_neg, πv, av, div_self e0]
  obtain ⟨c, cA, cN⟩ := exists_norm hK hc uv.le (by rw [star_div₀, star_neg, πs, LocWitt.symm' hs])
  have Nv : p.valuation K (star c * c) = 1 := by
    rw [← uv]
    exact Valuation.map_eq_of_sub_lt _ (uv ▸ cN)
  have c0 : c ≠ 0 := fun z => by simp [z] at Nv
  have hm : ∀ m ∈ loc (K := K) p.asIdeal M, p.valuation K (h m x / π) ≤ 1 := by
    obtain ⟨y, y1, y2⟩ : ∃ y ∈ loc (K := K) p.asIdeal (dual h M), y ∉ loc (K := K) p.asIdeal M := by
      by_contra! hh
      exact hb.2 (l1.trans (le_antisymm hh l2))
    obtain ⟨r, rA, hr⟩ := hd y y1
    rw [mem_locR hc] at rA
    have r1 : p.valuation K r = 1 := by
      refine le_antisymm rA (not_lt.1 fun lt => y2 ?_)
      have := smul_mem_loc hc M (r * (h x x)⁻¹) (by
        rw [map_mul, map_inv₀, av, mul_inv_le_iff₀ (zero_lt_iff.2 e0), one_mul]
        exact le_of_lt_one lt) x xL
      simpa using Submodule.add_mem _ hr this
    intro m hm
    have b := (p.valuation K).map_sub_le ((md y).1 y1 m hm) ((md _).1 (l2 hr) m hm)
    have : h m y - h m (y - (r * (h x x)⁻¹) • x) = r * (h m x / h x x) := by
      simp only [map_sub, map_smul, smul_eq_mul]; ring
    rw [this, map_mul, r1, one_mul, map_div₀, av] at b
    rwa [map_div₀, πv]
  have hG : p.valuation K ((star c * c * h x x + π) / π ^ 2) ≤ 1 := by
    have : (star c * c * h x x + π) / π ^ 2 = (star c * c - -π / h x x) * h x x / (π * π) := by
      field_simp; ring
    rw [this, map_div₀, map_mul, map_mul, av, πv, mul_div_mul_right _ _ e0,
      div_le_one₀ (zero_lt_iff.2 e0)]
    exact le_of_lt_one cN
  have πA : p.valuation K π ≤ 1 := by
    rw [πv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have key := abs_unimod (h := h) hs (Λ := (loc (K := K) p.asIdeal M).toAddSubgroup)
    (A := (p.valuation K).integer) (star_le hc) (smul_mem_loc hc M)
    (fun v hv w hw => (md w).1 (l2 hw) v hv) (π := π) (c := c) (x := x) πA π0 πs xL a0 cA c0
    (by change p.valuation K _ ≤ 1; rw [map_inv₀, Nv, inv_one])
    (by change p.valuation K _ ≤ 1; rw [map_div₀, πv, av, div_self e0]) hm hG
    (fun y hy => by
      obtain ⟨r, rA, hr⟩ := hd y ((md y).2 hy)
      exact ⟨r, (mem_locR hc r).1 rA, hr⟩)
  let w : V × K := ((π⁻¹ * c) • x, π⁻¹)
  let L : Submodule (𝓞 K) (V × K) := M.map (LinearMap.inl (𝓞 K) V K) ⊔ Submodule.span (𝓞 K) {w}
  have dec : ∀ z : V × K, z = (z.1 - (z.2 * c) • x, 0) + (π * z.2) • w := fun z => by
    refine Prod.ext ?_ ?_
    · simp only [w, Prod.fst_add, Prod.smul_fst, smul_smul]
      rw [show π * z.2 * (π⁻¹ * c) = z.2 * c by field_simp]; simp
    · simp only [w, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; field_simp; simp
  have mL : ∀ z : V × K, z ∈ L ↔ π * z.2 ∈ (1 : Submodule (𝓞 K) K) ∧ z.1 - (z.2 * c) • x ∈ M := by
    intro z
    constructor
    · intro hz
      obtain ⟨_, ⟨m, hm, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hb
      rw [← algebraMap_smul K r w]
      refine ⟨Submodule.mem_one.2 ⟨r, ?_⟩, ?_⟩
      · simp only [w, Prod.snd_add, Prod.smul_snd, smul_eq_mul, LinearMap.inl_apply]; field_simp; simp
      · simpa [w, smul_smul, mul_assoc] using hm
    · rintro ⟨h1, h2⟩
      obtain ⟨r, er⟩ := Submodule.mem_one.1 h1
      rw [dec z, ← er, algebraMap_smul]
      exact Submodule.add_mem_sup ⟨_, h2, rfl⟩ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w))
  have mL' : ∀ z : V × K, z ∈ loc (K := K) p.asIdeal L ↔
      p.valuation K (π * z.2) ≤ 1 ∧ z.1 - (z.2 * c) • x ∈ loc (K := K) p.asIdeal M := by
    intro z
    have e1 : ∀ s : 𝓞 K, π * (s • z).2 = s • (π * z.2) := fun s => by simp
    have e2 : ∀ s : 𝓞 K, (s • z).1 - ((s • z).2 * c) • x = s • (z.1 - (z.2 * c) • x) := fun s => by
      simp [smul_sub]
    rw [← mem_locR hc, locR, mem_loc hc, mem_loc hc, mem_loc hc]
    simp only [mL, e1, e2]
    constructor
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨⟨s, hs, h1⟩, s, hs, h2⟩
    · rintro ⟨⟨s, hs, h1⟩, s', hs', h2⟩
      refine ⟨s * s', fun b => (p.isPrime.mem_or_mem b).elim hs hs', ?_, ?_⟩
      · rw [mul_comm s, mul_smul]; exact Submodule.smul_mem _ _ h1
      · rw [mul_smul]; exact Submodule.smul_mem _ _ h2
  refine ⟨L, ⟨(hM.1.1.fg.map _).sup (Submodule.fg_span_singleton w), ?_⟩, ?_, ?_, ⟨w, ?_, ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro z _
    rw [dec z]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))))
    have : z.1 - (z.2 * c) • x ∈ Submodule.span K (M : Set V) := by
      rw [hM.1.1.span_eq_top]; trivial
    have := Submodule.mem_map_of_mem (f := LinearMap.inl K V K) this
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨m, hm, rfl⟩
    exact Submodule.mem_sup_left ⟨m, hm, rfl⟩
  · ext z
    rw [locDual_mem_dualAt]
    simp only [mL', mem_locR hc]
    exact key z
  · rw [mL']
    refine ⟨by simpa using πA, ?_⟩
    simpa using smul_mem_loc hc M c cA x xL
  · exact locBasic_le_locS _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
  · simp [extForm_apply, w, πs, π0]
  · intro v
    rw [mL']; simp

theorem mem_iff_of_gmap {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {g : W ≃ₗ[K] W} {A B : Submodule (𝓞 K) W} :
    gmap g A = B ↔ ∀ v, g v ∈ B ↔ v ∈ A := by
  constructor
  · rintro rfl v
    simp [gmap]
  · intro hh
    ext v
    simp only [gmap, Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hh w).2 hw
    · intro hv
      exact ⟨g.symm v, (hh _).1 (by simpa using hv), by simp⟩

theorem sameGenus [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} (hK : IsCMUnram K) (hs : h.IsSymm)
    (hn : h.Nondegenerate) {M N : Submodule (𝓞 K) V} (hM : IsMaxLat h M) (hN : IsMaxLat h N) :
    SameGenus h M N := by
  intro P hP
  have par : P ∈ badP h M ↔ P ∈ badP h N :=
    (GlobalTheory.T.maximalHermitianLattice_badPrimes_iff_gramDet K V h hK hs hn M hM _ (Module.finBasis K V) P hP).trans
      (GlobalTheory.T.maximalHermitianLattice_badPrimes_iff_gramDet K V h hK hs hn N hN _ (Module.finBasis K V) P hP).symm
  by_cases hb : P ∈ badP h M
  swap
  · exact GlobalTheory.T.exists_isometry_of_unimodular_lattices_at_place K V h hK hs hn M N hM.1.1 hN.1.1 P hP (by_contra fun a => hb ⟨hP, a⟩)
      (by_contra fun a => hb (par.2 ⟨hP, a⟩))
  let p : HeightOneSpectrum (𝓞 K) := ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP
    (RingOfIntegers.not_isField K)⟩
  obtain ⟨hc, -, -, x, -, ⟨a, ea, a1, a2⟩, -⟩ := (GlobalTheory.T.maximalHermitianLattice_local_structure_discriminant K V h hK hs hn M hM).2.2.2 _ hb
  have πv : p.valuation K (h x x) = WithZero.exp (-1 : ℤ) := ea ▸ val_unif (p := p) a1 a2
  have π0 : h x x ≠ 0 := fun z => WithZero.exp_ne_zero (by rw [← πv, z, map_zero])
  have πs := LocWitt.symm' hs x x
  obtain ⟨L, L1, L2, L3, ⟨w, L4, L5⟩, L6⟩ := exists_ext hK hs hn hM (p := p) hb πs πv
  obtain ⟨L', N1, N2, N3, N4, N6⟩ := exists_ext hK hs hn hN (p := p) (par.1 hb) πs πv
  have s' := extForm_symm hs πs
  have n' := extForm_nondeg hn π0
  obtain ⟨g, g1, g2⟩ := GlobalTheory.T.exists_isometry_of_unimodular_lattices_at_place K (V × K) _ hK s' n' L L' L1 N1 P hP L2 N2
  rw [mem_iff_of_gmap] at g2
  obtain ⟨k, k1, k2, k3⟩ := LocWitt.main K (V × K) _ hK s' n' L' N1 P hP hc N2 (g (0, 1))
    ((g2 _).2 L3) (0, 1) N3 (g1 _ _) ⟨g w, (g2 _).2 L4, (g1 _ _).trans L5⟩ N4
  rw [mem_iff_of_gmap] at k2
  obtain ⟨f, f1, f2⟩ := restrict π0 ((isom _).mul_mem k1 g1) k3
  refine ⟨f, f1, mem_iff_of_gmap.2 fun v => ?_⟩
  exact ((N6 _).symm.trans (by rw [← f2]; exact (k2 _).trans (g2 _))).trans (L6 v)

end Local

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ M N : Submodule (𝓞 K) V, IsMaxLat h M → (N ∈ genus h M ↔ IsMaxLat h N) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hpd M N hM
  have hn : h.Nondegenerate := by
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have : ∀ x, h x x = 0 → x = 0 := fun x e => by
      by_contra a
      have := hpd τ x a
      simp [e] at this
    exact ⟨fun x hx => this x (hx x), fun x hx => this x (hx x)⟩
  refine ⟨fun hN => ?_, fun hN => ⟨hN.1.1, sameGenus hK hs hn hM hN⟩⟩
  have dM := (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hn M hM.1).2.2.2.1
  obtain ⟨N1, N2⟩ := dM N hN
  obtain ⟨N', m', le⟩ := (GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V h hK hs hn).1 N N1
  have N3 := (dM N' ⟨m'.1.1, sameGenus hK hs hn hM m'⟩).2
  have dN := GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hn N N1
  have e := (dN.2.2.1 N' m'.1 le).2
  rw [N3, ← N2] at e
  have i1 : idxN N' N = 1 := by
    have := mul_left_cancel₀ dN.1 ((mul_one _).trans e)
    exact (Nat.pow_eq_one.1 this.symm).resolve_right (by norm_num)
  have : N' ≤ N := fun x hx => AddSubgroup.relIndex_eq_one.1 i1 hx
  rw [le_antisymm le this]
  exact m'

end GlobalTheory.Mass.MaxGenus
