import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.GenLatCmp

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_range_iff (x : E) : x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem mem_std (v : Fin n → E) : v ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, IsIntegral ℤ (v i) := by
  simp only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun i => mem_range_iff (v i)

theorem std_eq : Formalism.L2.Pj.stdLat E n = stdL E n := by
  apply le_antisymm
  · intro v hv
    rw [mem_std] at hv
    have : v = ∑ i, (⟨v i, hv i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_std]
    intro j
    by_cases h : j = i
    · subst h; simpa using isIntegral_one
    · simpa [Pi.single_apply, h] using isIntegral_zero

theorem span_smul_le (k : ℕ) (A B : Lt E n) :
    Ideal.span {(k : 𝓞 E)} • A ≤ B ↔ ∀ v ∈ A, (k : E) • v ∈ B := by
  have e : ∀ v : Fin n → E, (k : 𝓞 E) • v = (k : E) • v := fun v => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [Submodule.ideal_span_singleton_smul]
  constructor
  · intro h v hv
    rw [← e]
    exact h (Submodule.smul_mem_pointwise_smul v _ A hv)
  · intro h x hx
    obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [e]; exact h v hv

theorem natCast_smul_mem (k : ℕ) {A : Lt E n} {v : Fin n → E} (hv : v ∈ A) : (k : E) • v ∈ A := by
  rw [Nat.cast_smul_eq_nsmul]; exact A.toAddSubgroup.nsmul_mem hv k

theorem fg_of_smul_le {Λ : Lt E n} {s : ℕ} (hs : 0 < s) (h : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n) :
    Λ.FG := by
  have h0 : (stdL E n).FG := Submodule.fg_span (Set.finite_range _)
  have h1 := h0.map ((LinearMap.lsmul E (Fin n → E) (s : E)⁻¹).restrictScalars (𝓞 E))
  refine h1.of_le fun v hv => ⟨(s : E) • v, h v hv, ?_⟩
  have : (s : E) ≠ 0 := by exact_mod_cast hs.ne'
  simp [smul_smul, this]

variable [IsCMField E]

theorem herm_one_eq (x y : Fin n → E) :
    herm 1 x y = cc (∑ j, IsCMField.complexConj E (x j) * y j) := by
  simp [herm, cc, Matrix.one_apply]

theorem unimod_iff (Λ : Lt E n) : (⟨Λ⟩ : GenLat E n).Unimod ↔
    ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y) := by
  refine forall_congr' fun x => iff_congr Iff.rfl (forall₂_congr fun y _ => ?_)
  rw [mem_range_iff, herm_one_eq]
  refine ⟨Base.isIntegral_cc, fun h => ?_⟩
  simpa [cc] using Base.isIntegral_cc h

theorem smul_mem_std {Λ : Lt E n} (hU : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) {s : ℕ}
    (h : ∀ v ∈ stdL E n, (s : E) • v ∈ Λ) : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n := by
  intro v hv
  rw [← std_eq, mem_std]
  intro i
  have := (hU v).1 hv _ (h (Pi.single i 1) (Submodule.subset_span ⟨i, rfl⟩))
  convert this using 1
  simp [herm, cc, Matrix.one_apply, Pi.single_apply, mul_comm, apply_ite (IsCMField.complexConj E)]

theorem genLat_vset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Λ : Lt E n), (∀ bad M : ℕ, 0 < bad → Odd M → Λ ∈ Vset E n (2 * bad * M) → (⟨Λ⟩ : GenLat E n).Unimod ∧ (⟨Λ⟩ : GenLat E n).TrivAt bad ∧ (⟨Λ⟩ : GenLat E n).TrivAt M ∧ ∃ N, NOK Λ N M) ∧ (∀ M N : ℕ, 0 < M → (⟨Λ⟩ : GenLat E n).Unimod → (⟨Λ⟩ : GenLat E n).TrivAt M → NOK Λ N M → Λ ∈ Vset E n M) ∧ (∀ M M' : ℕ, M ∣ M' → Λ ∈ Vset E n M' → Λ ∈ Vset E n M) ∧ stdLat E n = stdL E n := by
  intro E _ _ _ n Λ
  refine ⟨?_, ?_, ?_, std_eq⟩
  · rintro bad M - hM ⟨-, hU, s, -, hs, h1, h2⟩
    have t : ∀ m, s.Coprime m → (⟨Λ⟩ : GenLat E n).TrivAt m := fun m hm =>
      ⟨s, hm, by rw [std_eq, span_smul_le]; exact h1, by rw [std_eq, span_smul_le]; exact h2⟩
    refine ⟨(unimod_iff Λ).2 hU, t _ hs.coprime_mul_right_right.coprime_mul_left_right,
      t _ hs.coprime_mul_left_right, s * M, ?_, Dvd.intro_left _ rfl, ?_⟩
    · exact (Nat.coprime_two_right.1 hs.coprime_mul_right_right.coprime_mul_right_right).mul hM
    · rw [span_smul_le]
      intro v hv
      refine ⟨?_, natCast_smul_mem _ hv⟩
      rw [std_eq] at hv
      rw [mul_comm, Nat.cast_mul, mul_smul]
      exact natCast_smul_mem M (h2 v hv)
  · rintro M N - hU ⟨k, hk, h1, h2⟩ ⟨hN, -, h3⟩
    rw [unimod_iff] at hU
    rw [std_eq, span_smul_le] at h1 h2 h3
    have h4 : ∀ v ∈ stdL E n, (N : E) • v ∈ Λ := fun v hv => (h3 v hv).1
    have h5 := smul_mem_std hU h4
    refine ⟨fg_of_smul_le hN.pos h5, hU, ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.coprime_zero_left] at hk
      exact ⟨N, hN.pos, hk ▸ Nat.coprime_one_right N, h5, h4⟩
    · exact ⟨k, hk0, hk, h1, h2⟩
  · rintro M M' hM ⟨a, b, s, hs, hc, h⟩
    exact ⟨a, b, s, hs, hc.coprime_dvd_right hM, h⟩

end GlobalTheory.Dict.GenLatCmp
