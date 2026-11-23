import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoCover

theorem X_mem_of_finite {K : Type} [Field K] {n m : ℕ}
    (I P : Ideal (MvPolynomial (Fin n) K)) [hPp : P.IsPrime] (hIP : I ≤ P)
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (y : Fin m → MvPolynomial (Fin n) K) (hy : ∀ k, y k ∈ P)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I))
    (j : Fin n) : (MvPolynomial.X j : MvPolynomial (Fin n) K) ∈ P := by
  classical
  by_contra hj
  let φ : (MvPolynomial (Fin n) K ⧸ I) →+* (MvPolynomial (Fin n) K ⧸ P) := Ideal.Quotient.factor hIP
  have hφ : ∀ g, φ (Ideal.Quotient.mk I g) = Ideal.Quotient.mk P g := fun g => rfl
  let Q : Ideal (MvPolynomial (Fin n) K ⧸ I) := RingHom.ker φ
  haveI : Q.IsPrime := RingHom.ker_isPrime φ
  haveI : Algebra.IsIntegral (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I) := Algebra.IsIntegral.of_finite _ _
  have hc0 : ∀ r ∈ Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)),
      ∃ c : K, φ r = Ideal.Quotient.mk P (MvPolynomial.C c) := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨0, by rw [hφ, map_zero, map_zero]; exact Ideal.Quotient.eq_zero_iff_mem.2 (hy k)⟩
    | algebraMap c => exact ⟨c, rfl⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c + d, by rw [map_add, hc, hd, map_add, map_add]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c * d, by rw [map_mul, hc, hd, map_mul, map_mul]⟩
  have h1 : (1 : MvPolynomial (Fin n) K ⧸ P) ≠ 0 := by
    intro h
    have : (1 : MvPolynomial (Fin n) K) ∈ P := Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_one]; exact h)
    exact hPp.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hmax : (Q.comap (algebraMap (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I))).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h => h1 ?_, fun J x hle hx hxJ => ?_⟩
    · have : φ 1 = 0 := by simpa [Q, RingHom.mem_ker, Ideal.mem_comap] using h
      simpa using this
    · obtain ⟨c, hc⟩ := hc0 x.1 x.2
      have hc' : c ≠ 0 := by
        rintro rfl
        apply hx
        rw [Ideal.mem_comap]
        change φ x.1 = 0
        rw [hc, map_zero, map_zero]
      have hm : x * algebraMap K _ c⁻¹ - 1 ∈ J := by
        apply hle
        rw [Ideal.mem_comap]
        change φ (x.1 * algebraMap K _ c⁻¹ - 1) = 0
        rw [map_sub, map_mul, hc, map_one]
        change _ * Ideal.Quotient.mk P (MvPolynomial.C c⁻¹) - 1 = 0
        rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc', map_one, map_one, sub_self]
      have := J.sub_mem (J.mul_mem_right (algebraMap K _ c⁻¹) hxJ) hm
      simpa using this
  have hQ : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
    (R := Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k))) Q hmax
  have hjQ : Ideal.Quotient.mk I (MvPolynomial.X j) ∉ Q := fun h =>
    hj (Ideal.Quotient.eq_zero_iff_mem.1 ((hφ _).symm.trans (RingHom.mem_ker.1 h)))
  obtain ⟨a, b, hb, hab⟩ := hQ.exists_inv hjQ
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h2 : Ideal.Quotient.mk P (g * MvPolynomial.X j - 1) = 0 := by
    have := congrArg φ hab
    rw [map_add, map_mul, hφ, hφ, show φ b = 0 from hb, add_zero, map_one] at this
    rw [map_sub, map_mul, this, map_one, sub_self]
  have h3 : MvPolynomial.homogeneousComponent 0 (g * MvPolynomial.X j - 1) ∈ P := by
    rw [← MvPolynomial.decomposition.decompose'_apply]
    exact hP 0 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
  have h4 : MvPolynomial.coeff 0 (g * MvPolynomial.X j - 1) = -1 := by
    have : MvPolynomial.constantCoeff (g * MvPolynomial.X j - 1) = -1 := by simp
    rwa [MvPolynomial.constantCoeff_eq] at this
  rw [MvPolynomial.homogeneousComponent_zero, h4, map_neg, map_one] at h3
  exact hPp.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.neg_mem h3))

theorem mem_of_evV_eq_zero {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (p : X)
    (j : Fin (N + 1)) (hj : i p ∈ Proj.basicOpen (grK K N) (MvPolynomial.X j))
    {d : ℕ} {f : MvPolynomial (Fin (N + 1)) K} (hf : f ∈ grK K N (d • 1))
    (h : evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf) = 0) :
    f ∈ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
  by_contra hfP
  have hf' : f * MvPolynomial.X j ∈ grK K N (d + 1) := by
    have := SetLike.mul_mem_graded hf (xv_mem K N j)
    simpa using this
  have e : HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf =
      HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf' := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk]
    exact Localization.mk_eq_mk_iff.2 (Localization.r_of_eq (by
      change MvPolynomial.X j ^ (d + 1) * f = MvPolynomial.X j ^ d * (f * MvPolynomial.X j)
      ring))
  have hb := GroundTheory.Arith.SchemeCoh.ProjHom.basicOpen_awayToSection_isLocalizationElem (grK K N)
    (xv_mem K N j) one_pos hf' (Nat.succ_pos d)
  have hx : i p ∈ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf')) := by
    erw [hb]
    refine ⟨hj, fun hm => ?_⟩
    exact ((i p : ProjectiveSpectrum (grK K N)).isPrime.mem_or_mem hm).elim hfP hj
  have hp : p ∈ i ⁻¹ᵁ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf')) := hx
  rw [Scheme.preimage_basicOpen, ← e] at hp
  have h0 : i.app _ (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf)) = 0 := by
    rw [Scheme.Hom.app_eq_appLE]
    exact h
  rw [h0, Scheme.basicOpen_zero] at hp
  exact hp

theorem iSup_preimage_eq_top : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ {m e : ℕ}, 0 < e → ∀ (y : Fin m → MvPolynomial (Fin (N + 1)) K), (∀ k, (y k).IsHomogeneous e) → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ⨆ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = ⊤ := by
  intro K _ X N i m e _ y _ hfin
  rw [_root_.eq_top_iff]
  intro p _
  by_contra hcon
  obtain ⟨j, hj⟩ : ∃ j, i p ∈ Proj.basicOpen (grK K N) (MvPolynomial.X j) := by
    have : i p ∈ (⨆ j : Fin (N + 1), Proj.basicOpen (grK K N) (MvPolynomial.X j)) := by
      erw [GroundTheory.Arith.SchemeCoh.ProjSpace.iSup_basicOpen_X]
      trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  have hy : ∀ k, y k ∈ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
    intro k
    by_contra hk
    apply hcon
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨k, hk⟩
  have hle : homIdeal i ≤ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
    rw [homIdeal, Ideal.span_le]
    rintro f ⟨d, hf, hv⟩
    exact mem_of_evV_eq_zero i p j hj hf (hv j)
  haveI : (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal.IsPrime :=
    (i p : ProjectiveSpectrum (grK K N)).isPrime
  exact hj (X_mem_of_finite _ _ hle
    (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).isHomogeneous y hy hfin j)

end GlobalTheory.CompanionTheory.GeoCover
