import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfForallXiPowDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_isEps_for_inj (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, h⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  refine ⟨ε, ?_, ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro hh
    have := h 1
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    exact congrArg Subtype.val hh

theorem eq_zero_of_mem_span_pow_away {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (r ξ : A)
    [IsLocalization.Away r B] (hs : ∀ n : ℕ, ∀ a : A, ξ ^ n ∣ r * a → ξ ^ n ∣ a)
    (hh : ∀ a : A, (∀ n : ℕ, ξ ^ n ∣ a) → a = 0) (x : B)
    (hx : ∀ n : ℕ, x ∈ Ideal.span {algebraMap A B ξ} ^ n) : x = 0 := by
  have hs' : ∀ n m : ℕ, ∀ a : A, ξ ^ n ∣ r ^ m * a → ξ ^ n ∣ a := by
    intro n m
    induction m with
    | zero => intro a ha; simpa using ha
    | succ m ih =>
      intro a ha
      apply ih
      apply hs
      rwa [← mul_assoc, ← pow_succ']
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) x
  have ha : a = 0 := by
    apply hh
    intro n
    have h1 : algebraMap A B a ∈ Ideal.map (algebraMap A B) (Ideal.span {ξ ^ n}) := by
      rw [Ideal.map_span, Set.image_singleton, map_pow, ← Ideal.span_singleton_pow,
        ← IsLocalization.mk'_spec B a s]
      exact Ideal.mul_mem_right _ _ (hx n)
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers r)] at h1
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ := h1
    exact hs' n m a (Ideal.mem_span_singleton.1 hm)
  simp [ha]

theorem algebraMap_AinfP_BdRp_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  obtain ⟨e, he⟩ := exists_isEps_for_inj l
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_mem_span_pow_away (l : Per.Ainf l) (xi e)
    (fun n a h => XiHaus.xi_sat he n a h) (GlobalTheory.MemLoc.eq_zero_of_forall_xi_pow_dvd l e he) x fun n => ?_
  rw [← GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he, ← Ideal.Quotient.eq_zero_iff_mem]
  have h1 : Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) = Ideal.Quotient.mk _ x :=
    GlobalTheory.RingIface.ev_alg l n x
  rw [← h1, hx, map_zero]

end GlobalTheory.MemLoc
