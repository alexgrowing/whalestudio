import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.HermitianLattices.StatementLat
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLatIffMemLocP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationAdditiveQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntCastIsUnitCompletionAlmostAllPlaces
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocCongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

theorem approx_int (A : Places F E sig) (g : ℕ) (hg : 0 < g) (p : HeightOneSpectrum (𝓞 F))
    (z : (A.loc p).Ep) (hz : z ∈ (A.L p).O) :
    ∃ x : 𝓞 E, ∃ o ∈ (A.L p).O, z - (A.loc p).ιE (x : E) = (A.loc p).ιE (g : E) * o := by
  have hgF : ((g : ℤ) : F) ≠ 0 := by exact_mod_cast hg.ne'
  let c : ∀ q, ((A.loc q).Fp)ˣ := fun q => Units.mk0 ((g : ℤ) : (A.loc q).Fp) (by
    rw [← map_intCast (A.loc q).ιF]; exact (map_ne_zero _).2 hgF)
  have hc := PlacesInt.intCast_isUnit_almost_all A (g : ℤ) (by exact_mod_cast hg.ne')
  have hcE : ∀ q, algebraMap (A.loc q).Fp (A.loc q).Ep (c q) = (A.loc q).ιE (g : E) := by
    intro q
    change algebraMap (A.loc q).Fp (A.loc q).Ep ((g : ℤ) : (A.loc q).Fp) = _
    rw [map_intCast, map_natCast, Int.cast_natCast]
  have hgO : ∀ q, (A.loc q).ιE (g : E) ∈ (A.L q).O := fun q => by
    rw [map_natCast]; exact natCast_mem (A.L q).O g
  let y : ∀ q, (A.loc q).Ep := Pi.single (M := fun q => (A.loc q).Ep) p z
  have hy : {q | y q ∉ (A.L q).O}.Finite := by
    refine (Set.finite_singleton p).subset fun q hq => ?_
    by_contra hne
    apply hq
    change Pi.single (M := fun q => (A.loc q).Ep) p z q ∈ (A.L q).O
    rw [Pi.single_eq_of_ne hne]
    exact zero_mem _
  obtain ⟨-, hE, -⟩ := StrongApprox.strong_approx_additive A c hc
  obtain ⟨x, hx⟩ := hE y hy
  have hint : ∀ q, (A.loc q).ιE x ∈ (A.L q).O := by
    intro q
    obtain ⟨o, ho, he⟩ := hx q
    have hyq : y q ∈ (A.L q).O := by
      by_cases h : q = p
      · subst h
        change Pi.single (M := fun q => (A.loc q).Ep) q z q ∈ (A.L q).O
        rw [Pi.single_eq_same]; exact hz
      · change Pi.single (M := fun q => (A.loc q).Ep) p z q ∈ (A.L q).O
        rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have e : (A.loc q).ιE x = y q + algebraMap (A.loc q).Fp (A.loc q).Ep (c q) * o := by
      rw [← he]; ring
    rw [e, hcE]
    exact add_mem hyq (mul_mem (hgO q) ho)
  obtain ⟨xo, hxo⟩ := ((PlacesInt.integers_local A).1 x).1 hint
  obtain ⟨o, ho, he⟩ := hx p
  refine ⟨xo, -o, neg_mem ho, ?_⟩
  have hyp : y p = z := by
    change Pi.single (M := fun q => (A.loc q).Ep) p z p = z
    exact Pi.single_eq_same _ _
  rw [hyp, hcE] at he
  rw [hxo]
  linear_combination -he

section
variable (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ}

theorem bc_sub (u v : Fin N → E) : A.bc p (u - v) = A.bc p u - A.bc p v := by
  funext i; simp [Places.bc]

theorem bc_smul (t : E) (u : Fin N → E) : A.bc p (t • u) = (A.loc p).ιE t • A.bc p u := by
  funext i; simp [Places.bc]

theorem bc_sum {ι : Type} (s : Finset ι) (f : ι → Fin N → E) :
    A.bc p (∑ i ∈ s, f i) = ∑ i ∈ s, A.bc p (f i) := by
  funext j; simp [Places.bc, Finset.sum_apply, map_sum]

theorem lat_smul (Λ : Submodule (𝓞 E) (Fin N → E)) (t : 𝓞 E) (v : Fin N → (A.loc p).Ep)
    (hv : v ∈ A.lat p Λ) : (A.loc p).ιE (t : E) • v ∈ A.lat p (Ideal.span {t} • Λ) := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, hu, rfl⟩ := hw
    have e : (A.loc p).ιE (t : E) • A.bc p u = A.bc p (t • u) := by
      funext i
      change (A.loc p).ιE (t : E) * (A.loc p).ιE (u i) = (A.loc p).ιE (t • u i)
      rw [Algebra.smul_def, map_mul]
    rw [e]
    exact Submodule.subset_span ⟨_, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) hu, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o a _ ha =>
    have e : (A.loc p).ιE (t : E) • (o • a) = o • ((A.loc p).ιE (t : E) • a) := by
      change (A.loc p).ιE (t : E) • ((o : (A.loc p).Ep) • a) = (o : (A.loc p).Ep) • ((A.loc p).ιE (t : E) • a)
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ o ha

end

theorem loc_cong_approx : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : GlobalTheory.HL.Places F E sig) (N r : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)), Λ.FG → ∀ (g : ℕ), 0 < g → ∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (y x : Fin (r + 1) → Fin N → E) (ξp : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep), (∀ a b, ξp a b ∈ (A.L p).O) → (∀ a b, b < a → ξp a b = 0) → (∀ a, ξp a a = 1) → (∀ a, A.bc p (y a) ∈ A.lat p Λ) → (∀ b, A.bc p (x b) - ∑ a, ξp a b • A.bc p (y a) ∈ A.lat p (Ideal.span {(g : 𝓞 E)} • Λ)) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal → ∀ b, x b - ∑ a, ((ξ a b : 𝓞 E) : E) • y a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ)) := by
  intro F E _ _ _ _ _ sig A N r Λ hΛ g hg p y x ξp hO hlow hdiag hy hx
  choose ξ0 o ho hξ0 using fun a b => approx_int A g hg p (ξp a b) (hO a b)
  let ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) :=
    fun a b => if b < a then 0 else if a = b then 1 else ξ0 a b
  have hd : ∀ a b, ∃ o ∈ (A.L p).O,
      ξp a b - (A.loc p).ιE ((ξ a b : 𝓞 E) : E) = (A.loc p).ιE (g : E) * o := by
    intro a b
    by_cases h1 : b < a
    · refine ⟨0, zero_mem _, ?_⟩
      simp [ξ, h1, hlow a b h1]
    · by_cases h2 : a = b
      · subst h2
        refine ⟨0, zero_mem _, ?_⟩
        simp [ξ, hdiag]
      · refine ⟨o a b, ho a b, ?_⟩
        simp only [ξ, h1, h2, if_false]
        exact hξ0 a b
  have hFG : (Ideal.span {(g : 𝓞 E)} • Λ).FG := Submodule.FG.smul (Submodule.fg_span_singleton _) hΛ
  have hmem : ∀ b, A.bc p (x b - ∑ a, ((ξ a b : 𝓞 E) : E) • y a) ∈
      A.lat p (Ideal.span {(g : 𝓞 E)} • Λ) := by
    intro b
    rw [bc_sub, bc_sum]
    simp only [bc_smul]
    have e : A.bc p (x b) - ∑ a, (A.loc p).ιE ((ξ a b : 𝓞 E) : E) • A.bc p (y a) =
        (A.bc p (x b) - ∑ a, ξp a b • A.bc p (y a)) +
          ∑ a, (ξp a b - (A.loc p).ιE ((ξ a b : 𝓞 E) : E)) • A.bc p (y a) := by
      simp only [sub_smul, Finset.sum_sub_distrib]; abel
    rw [e]
    refine add_mem (hx b) (Submodule.sum_mem _ fun a _ => ?_)
    obtain ⟨o', ho', he⟩ := hd a b
    rw [he, mul_smul]
    have h1 : (⟨o', ho'⟩ : (A.L p).O) • A.bc p (y a) ∈ A.lat p Λ := Submodule.smul_mem _ _ (hy a)
    have h2 := lat_smul A p Λ (g : 𝓞 E) _ h1
    have e2 : (((g : 𝓞 E) : E)) = (g : E) := by simp
    rw [e2] at h2
    exact h2
  refine ⟨ξ, fun a b h => by simp [ξ, h], fun a => by simp [ξ], fun P hP b => ?_⟩
  exact (LocDict.mem_lat_iff_mem_locP A N _ hFG p _).1 (hmem b) P hP

end GlobalTheory.HL.LocCongApprox
