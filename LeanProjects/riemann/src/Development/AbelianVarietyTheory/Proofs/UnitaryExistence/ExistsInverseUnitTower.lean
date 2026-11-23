import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TateIsoExistsLiftOfTwoData
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCompatibleNormTowerProfiniteStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_inverse_unit_tower (ν : ℕ → ℤ) (h1 : ∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ))
    (h2 : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) :
    ∃ κ : ℕ → ℤ, (∀ n : ℕ, 0 < n → (n : ℤ) ∣ κ n * ν n - 1) ∧ (∀ n : ℕ, 0 < n → IsCoprime (κ n) (n : ℤ)) ∧
      ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ κ (n * m) - κ n := by
  have h : ∀ n : ℕ, ∃ x : ℤ, 0 < n → (n : ℤ) ∣ x * ν n - 1 := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨x, y, hxy⟩ := h1 n hn
      exact ⟨x, fun _ => ⟨-y, by linear_combination hxy⟩⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose κ hκ using h
  refine ⟨κ, hκ, fun n hn => ?_, fun n m hn hm => ?_⟩
  · obtain ⟨c, hc⟩ := hκ n hn
    exact ⟨ν n, -c, by linear_combination hc⟩
  · obtain ⟨c, hc⟩ := hκ n hn
    obtain ⟨c', hc'⟩ := hκ (n * m) (Nat.mul_pos hn hm)
    obtain ⟨d, hd⟩ := h2 n m hn hm
    push_cast at hc'
    refine ⟨κ n * m * c' - κ (n * m) * c - κ (n * m) * κ n * d, ?_⟩
    linear_combination κ n * hc' - κ (n * m) * hc - κ (n * m) * κ n * hd

theorem level_smul_mem_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H)
    {V : Type} [AddCommGroup V] [Module (𝓞 E) V] {s : 𝓞 E} (hs : s ∈ l.Mb) {a : V}
    (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) V)) : ∃ e, s • a = l.M • e := by
  have h : s • a ∈ Ideal.span {(l.M : 𝓞 E)} • (⊤ : Submodule (𝓞 E) V) := by
    rw [← l.prod, mul_smul]
    exact Submodule.smul_mem_smul hs ha
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨e, -, he⟩ := h
  exact ⟨e, by rw [← he, Nat.cast_smul_eq_nsmul]⟩

theorem familyUnif_lattice_genus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → ∃ f : ℕ → D.La →ₗ[𝓞 E] (U.Di i).La, (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ (U.Di i).EF (f n a) (f n a') - D.EF a a') ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, f l.M a = U.t i a + l.M • e := by
  intro E _ _ _ H D l Xo σ g ty U i P hP
  obtain ⟨f, ν, h1, h2, h3, h4, h5, h6, -⟩ := familyUnif_lattice_similar E H D l Xo σ g ty U i P hP
  obtain ⟨κ, hκ1, hκ2, hκ3⟩ := exists_inverse_unit_tower ν h3 h4
  obtain ⟨s, hs1, hs2, hs3⟩ := GlobalTheory.T.exists_compatible_norm_tower_profinite E H l κ hκ2 hκ3
  have hinv : ∀ n : ℕ, 0 < n → ∃ r c : 𝓞 E, r * s n = 1 + n * c := by
    intro n hn
    obtain ⟨c, hc⟩ := hs1 n hn
    obtain ⟨d, hd⟩ := hκ1 n hn
    have hd' : (κ n : 𝓞 E) * (ν n : 𝓞 E) - 1 = (n : 𝓞 E) * (d : 𝓞 E) := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hd
    exact ⟨(ν n : 𝓞 E) * H.bar (s n), (ν n : 𝓞 E) * c + d, by linear_combination (ν n : 𝓞 E) * hc + hd'⟩
  refine ⟨fun n => s n • f n, fun n m hn hm a => ?_, fun n hn => ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩,
    fun n hn a a' => ?_, fun a ha => ?_⟩
  · obtain ⟨e, he⟩ := h1 n m hn hm a
    obtain ⟨c, hc⟩ := hs2 n m hn hm
    have hc' : s (n * m) = s n + n * c := by linear_combination hc
    refine ⟨c • f n a + s (n * m) • e, ?_⟩
    simp only [LinearMap.smul_apply]
    rw [he, hc', ← Nat.cast_smul_eq_nsmul (𝓞 E), ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    module
  · rintro ⟨e, he⟩
    obtain ⟨r, c, hrc⟩ := hinv n hn
    rw [← (h2 n hn).1 a]
    refine ⟨r • e - c • f n a, ?_⟩
    rw [LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul (𝓞 E)] at he
    have h : (r * s n) • f n a = r • (n : 𝓞 E) • e := by rw [mul_smul, he]
    rw [hrc] at h
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    linear_combination (norm := module) h
  · rintro ⟨e, rfl⟩
    exact ⟨(s n • f n) e, by rw [map_nsmul]⟩
  · obtain ⟨a, e, he⟩ := (h2 n hn).2 a'
    obtain ⟨r, c, hrc⟩ := hinv n hn
    refine ⟨r • a, e - c • f n a, ?_⟩
    rw [LinearMap.smul_apply, map_smul, smul_smul, mul_comm, hrc, he, ← Nat.cast_smul_eq_nsmul (𝓞 E),
      ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    module
  · obtain ⟨c, hc⟩ := hs1 n hn
    obtain ⟨d, hd⟩ := hκ1 n hn
    obtain ⟨k, hk⟩ := h5 n hn (s n • a) (s n • a')
    have hc' : H.bar (s n) * s n = (κ n : 𝓞 E) + (n : 𝓞 E) * c := by linear_combination hc
    have e1 : D.EF (s n • a) (s n • a') = κ n * D.EF a a' + n * D.EF a (c • a') := by
      rw [D.adj, smul_smul, hc', add_smul, mul_smul, Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul, map_add,
        map_nsmul, map_zsmul, smul_eq_mul, nsmul_eq_mul]
    simp only [LinearMap.smul_apply, ← map_smul]
    rw [e1] at hk
    refine ⟨k + d * D.EF a a' + ν n * D.EF a (c • a'), ?_⟩
    linear_combination hk + D.EF a a' * hd
  · obtain ⟨e, he⟩ := h6 a ha
    obtain ⟨e', he'⟩ := level_smul_mem_half l hs3 ha
    refine ⟨e + f l.M e', ?_⟩
    have h : s l.M • a = a + l.M • e' := by rw [← he', sub_smul, one_smul, add_sub_cancel]
    rw [LinearMap.smul_apply, ← map_smul, h, map_add, map_nsmul, he, smul_add, add_assoc]

end GlobalTheory
