import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactFirstTermBundle
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LinearIndependentMapVec
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsSplitInjectiveAndExists
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactEigenSubDegreeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenspaceFrobeniusTwistStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualEigenSubDegreeTransposeStatement

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.ConjEq

theorem eq_zero_of_scale {S : Type} [Finite S] (h : S → ℤ) (p : ℕ) (hp : 2 ≤ p)
    (H : ∀ s, ∃ u, h u = p * h s) (s : S) : h s = 0 := by
  haveI : Nonempty S := ⟨s⟩
  obtain ⟨m, hm⟩ := Finite.exists_max (fun s => |h s|)
  obtain ⟨u, hu⟩ := H m
  have h1 : |h u| = p * |h m| := by
    rw [hu, abs_mul, Nat.abs_cast]
  have h2 : |h u| ≤ |h m| := hm u
  have h3 : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have h4 : |h m| = 0 := by
    have h5 : 0 ≤ |h m| := abs_nonneg _
    nlinarith
  have h6 : |h s| ≤ 0 := h4 ▸ hm s
  exact abs_eq_zero.1 (le_antisymm h6 (abs_nonneg _))

variable {K : Type} [Field K]

theorem eig_star {O V : Type} [CommRing O] [StarRing O] [AddCommGroup V] [Module K V]
    (ρ : O → V →ₗ[K] V) (χ χ' : O → K) (h : ∀ a, χ' a = χ (star a)) :
    eig (fun a => ρ (star a)) χ = eig ρ χ' := by
  ext x
  simp only [eig, Submodule.mem_iInf]
  constructor
  · intro H a
    have := H (star a)
    rwa [star_star, ← h] at this
  · intro H a
    have := H (star a)
    rwa [h, star_star] at this

section Data

variable (C : ACurve K) {p : ℕ} {O : Type} [CommRing O] [StarRing O] {d : ℕ}
  (D : ConjData C p O d)

theorem lie_hom (a : O) : IsHom C D.lie D.lie (Matrix.toLin' (D.ρ a)) := by
  intro i x hx
  obtain ⟨y, hy, rfl⟩ := (D.hodge.2.2.2.2 i x).1 hx
  refine (D.hodge.2.2.2.2 i _).2 ⟨D.ρH a y, D.ρH_hom a i y hy, ?_⟩
  simpa using D.ρH_fst a y

theorem dual_bun : IsBun C (dotDual C D.lie) :=
  (deg_shortExact K C _ _ _ _ _ _ _ _ D.H_bun D.hodge).1

variable {k S : Type} [Field k] [Algebra k K] [Fintype S] (χ : S → (O →+* k))

theorem hodge_eq (hχ : IsSplit χ) (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (s t : S)
    (hst : ∀ a, χ t a = χ s (star a)) :
    subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ s a))) =
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) -
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a))) := by
  classical
  have h1 := GlobalTheory.T.short_exact_eigen_sub_degree K C _ _ _ (dotDual C D.lie) D.H D.lie (LinearMap.inr K _ _)
    (LinearMap.fst K _ _) O k S χ hχ hk (fun a => Matrix.toLin' (D.ρ (star a)).transpose) D.ρH
    (fun a => Matrix.toLin' (D.ρ a)) D.H_bun D.ρH_hom D.hodge
    (fun a x => by simpa using (D.ρH_inr a x).symm) (fun a y => by simpa using D.ρH_fst a y) s
  have h2 := eig_star (K := K) (fun a => Matrix.toLin' (D.ρ a).transpose)
    (fun a => algebraMap k K (χ s a)) (fun a => algebraMap k K (χ t a))
    (fun a => by rw [hst])
  have h3 := GlobalTheory.T.dual_eigen_sub_degree_transpose K C d D.lie O k S χ hχ hk D.ρ D.lie_bun (lie_hom C D) t
  rw [h1, h2, h3]
  ring

theorem conj_eq [Fact p.Prime] [CharP K p] (hχ : IsSplit χ)
    (hk : ∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) (s t u : S)
    (hst : ∀ a, χ t a = χ s (star a)) (hu : ∀ a, χ u a = χ s a ^ p) :
    subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ u a))) =
      p * (subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) -
      subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a)))) := by
  classical
  have h1 := GlobalTheory.T.short_exact_eigen_sub_degree K C _ _ _ (frobLat C p D.lie) D.H (frobLat C p (dotDual C D.lie))
    D.α D.β O k S χ hχ hk (fun a => Matrix.toLin' ((D.ρ a).map (· ^ p))) D.ρH
    (fun a => Matrix.toLin' ((D.ρ (star a)).transpose.map (· ^ p))) D.H_bun D.ρH_hom D.conj
    (fun a x => by simpa using D.α_act a x) (fun a y => by simpa using D.β_act a y) u
  have hc : (fun a => algebraMap k K (χ u a)) = fun a => algebraMap k K (χ s a) ^ p := by
    funext a
    rw [hu, map_pow]
  have h2 := GlobalTheory.T.eigenspace_frobenius_twist K p d O (fun a => D.ρ a) (fun a => algebraMap k K (χ s a))
  have h3 := GlobalTheory.T.eigenspace_frobenius_twist K p d O (fun a => (D.ρ (star a)).transpose)
    (fun a => algebraMap k K (χ s a))
  have h4 := eig_star (K := K) (fun a => Matrix.toLin' (D.ρ a).transpose)
    (fun a => algebraMap k K (χ s a)) (fun a => algebraMap k K (χ t a))
    (fun a => by rw [hst])
  have h5 := GlobalTheory.T.dual_eigen_sub_degree_transpose K C d D.lie O k S χ hχ hk D.ρ D.lie_bun (lie_hom C D) t
  rw [h1, hc, h2, h3, SubFrob.subDeg_frob K C p d _ _ D.lie_bun,
    SubFrob.subDeg_frob K C p d _ _ (dual_bun C D), h4, h5]
  ring

end Data

theorem subDeg_eig_conj : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ s t : S, (∀ a, χ t a = χ s (star a)) → subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) = subDeg C D.lie (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ t a))) := by
  intro K _ C p _ _ O k S _ _ _ _ _ χ d D hχ hk s t hst
  have hp : p.Prime := Fact.out
  haveI : CharP k p := (algebraMap k K).charP (algebraMap k K).injective p
  haveI : ExpChar k p := ExpChar.prime hp
  have hall := (isSplit_injective_and_exists O k S χ hχ).2
  have hconj : ∀ s, ∃ t, ∀ a, χ t a = χ s (star a) := fun s => by
    obtain ⟨t, ht⟩ := hall ((χ s).comp (starRingEnd O))
    exact ⟨t, fun a => by rw [ht]; rfl⟩
  have hfrob : ∀ s, ∃ u, ∀ a, χ u a = χ s a ^ p := fun s => by
    obtain ⟨u, hu⟩ := hall ((frobenius k p).comp (χ s))
    exact ⟨u, fun a => by rw [hu]; rfl⟩
  have hzero := eq_zero_of_scale
    (fun s => subDeg C D.H (eig (fun a => D.ρH a) (fun a => algebraMap k K (χ s a))))
    p hp.two_le (fun s => by
      obtain ⟨t, ht⟩ := hconj s
      obtain ⟨u, hu⟩ := hfrob s
      refine ⟨u, ?_⟩
      rw [conj_eq C D χ hχ hk s t u ht hu, hodge_eq C D χ hχ hk s t ht]) s
  have h := hodge_eq C D χ hχ hk s t hst
  rw [hzero] at h
  exact sub_eq_zero.1 h.symm

end GlobalTheory.CompanionTheory.Ar.Crv.ConjEq
