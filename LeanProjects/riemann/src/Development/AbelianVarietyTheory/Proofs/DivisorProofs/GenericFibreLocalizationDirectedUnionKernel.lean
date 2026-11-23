import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
open IsLocalRing Polynomial

namespace GlobalTheory

theorem genFib_colim_ker : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T) (hA : Monotone 𝒜), (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra T E] (Q : Ideal E) [Q.IsPrime]
      (Ek : ι → Type) [∀ k, CommRing (Ek k)] [∀ k, Algebra (𝒜 k) (Ek k)]
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k (a : 𝒜 k), e k (algebraMap (𝒜 k) (Ek k) a) = algebraMap T E a) →
      (∀ k l (hkl : k ≤ l) (a : 𝒜 k), h k l hkl (algebraMap (𝒜 k) (Ek k) a) =
          algebraMap (𝒜 l) (Ek l) (Subring.inclusion (hA hkl) a)) →
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) →
      (∀ k, Function.Injective (e k)) →
      (∀ x : E, ∃ k y, e k y = x) →
    ∀ (g : ∀ k, GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
      (∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y))) →
    ∀ (f : ∀ k l, k ≤ l → GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib (𝒜 l) (Localization.AtPrime (Q.comap (e l)))),
      (∀ k l (hkl : k ≤ l) (y : Ek k), f k l hkl (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime (Q.comap (e l)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 l) (Localization.AtPrime (Q.comap (e l))))
          (algebraMap (Ek l) (Localization.AtPrime (Q.comap (e l))) (h k l hkl y))) →
    ∀ k (x : GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))), g k x = 0 →
      ∃ l, ∃ hkl : k ≤ l, f k l hkl x = 0 := by
  intro T _ _ ι _ _ 𝒜 hA hcov E _ _ Q _ Ek _ _ e h he hh heh hinj hsurj g hg f hf k x hx
  classical

  set L := Localization.AtPrime (Q.comap (e k)) with hL
  obtain ⟨⟨z, a'⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid L (nonZeroDivisors (𝒜 k))) x
  obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Q.comap (e k)).primeCompl z
  dsimp only at hx ⊢
  set G := GlobalTheory.LocAcyc.GenFib (𝒜 k) L
  set X := IsLocalization.mk' G (IsLocalization.mk' L y s) a' with hX
  set v : G := algebraMap L G (a' : L) * algebraMap L G (algebraMap (Ek k) L (s : Ek k)) with hv
  have hvu : IsUnit v := by
    refine (IsLocalization.map_units G a').mul ?_
    exact (IsLocalization.map_units L s).map _
  have hXv : X * v = algebraMap L G (algebraMap (Ek k) L y) := by
    rw [hv, ← mul_assoc, hX, IsLocalization.mk'_spec, ← map_mul, IsLocalization.mk'_spec]

  have hgy : g k (algebraMap L G (algebraMap (Ek k) L y)) = 0 := by
    rw [← hXv, map_mul, hx, zero_mul]
  rw [hg] at hgy

  obtain ⟨⟨m0, hm0⟩, hm0y⟩ := (IsLocalization.map_eq_zero_iff
    (Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)) _ _).1 hgy
  obtain ⟨t, ht, rfl⟩ := Submonoid.mem_map.1 hm0
  simp only at hm0y
  rw [IsScalarTower.algebraMap_apply T E (Localization.AtPrime Q), ← map_mul] at hm0y
  obtain ⟨⟨u, hu⟩, huy⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl _ _).1 hm0y
  simp only at huy
  obtain ⟨m, u', rfl⟩ := hsurj u
  obtain ⟨m', htm'⟩ := hcov t
  obtain ⟨l1, hkl1, hml1⟩ := directed_of (· ≤ ·) k m
  obtain ⟨l, hl1, hm'l⟩ := directed_of (· ≤ ·) l1 m'
  have hkl : k ≤ l := hkl1.trans hl1
  have hml : m ≤ l := hml1.trans hl1
  let c : 𝒜 l := ⟨t, hA hm'l htm'⟩
  have hc0 : c ∈ nonZeroDivisors (𝒜 l) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    have : (t : T) = 0 := congrArg Subtype.val h0
    exact nonZeroDivisors.ne_zero ht this
  have hprod : h m l hml u' * (algebraMap (𝒜 l) (Ek l) c * h k l hkl y) = 0 := by
    apply hinj l
    rw [map_mul, map_mul, heh, heh, he, map_zero]
    simpa [mul_assoc] using huy
  have hu'' : h m l hml u' ∈ (Q.comap (e l)).primeCompl := by
    change e l (h m l hml u') ∉ Q
    rw [heh]; exact hu
  set Ll := Localization.AtPrime (Q.comap (e l))
  have h1 : algebraMap (Ek l) Ll (algebraMap (𝒜 l) (Ek l) c * h k l hkl y) = 0 := by
    have := congrArg (algebraMap (Ek l) Ll) hprod
    rw [map_mul, map_zero] at this
    exact ((IsLocalization.map_units Ll ⟨_, hu''⟩).mul_right_eq_zero).1 this
  have h2 : algebraMap Ll (GlobalTheory.LocAcyc.GenFib (𝒜 l) Ll) (algebraMap (Ek l) Ll (h k l hkl y)) = 0 := by
    have hcm : algebraMap (𝒜 l) Ll c ∈ Algebra.algebraMapSubmonoid Ll (nonZeroDivisors (𝒜 l)) :=
      Submonoid.mem_map.2 ⟨c, hc0, rfl⟩
    have := congrArg (algebraMap Ll (GlobalTheory.LocAcyc.GenFib (𝒜 l) Ll)) h1
    rw [map_mul, map_zero, ← IsScalarTower.algebraMap_apply, map_mul] at this
    exact ((IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib (𝒜 l) Ll) ⟨_, hcm⟩).mul_right_eq_zero).1 this
  refine ⟨l, hkl, ?_⟩
  have hfy : f k l hkl (algebraMap L G (algebraMap (Ek k) L y)) = 0 := by
    rw [hf]; exact h2
  have := congrArg (f k l hkl) hXv
  rw [map_mul, hfy] at this
  exact ((hvu.map (f k l hkl)).mul_left_eq_zero).1 this

end GlobalTheory
