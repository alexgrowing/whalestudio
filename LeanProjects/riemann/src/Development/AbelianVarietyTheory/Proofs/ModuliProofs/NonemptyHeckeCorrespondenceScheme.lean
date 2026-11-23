import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetEtaleLevelStructureExistsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientDescendsEtaleSurjectiveCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoQuotientsSameKernelReducedBaseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeomPtRangeEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversalReducedBasesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObjectStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientExistsListedKernelsSmoothBaseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem corr_kerSet_unique {S : Scheme.{0}} {G G' : Over S} [GrpObj G'] {ψ : G ⟶ G'} {K K' : Set G.left}
    (h : KerSet ψ K) (h' : KerSet ψ K') : K = K' := by
  ext g
  obtain ⟨k, _, _, z₀, hz⟩ := exists_geomPt_range_eq G.left g
  let z : Over.mk (z₀ ≫ G.hom) ⟶ G := Over.homMk z₀ rfl
  have h1 := h k _ z
  have h2 := h' k _ z
  have hzl : z.left = z₀ := rfl
  rw [hzl, hz, Set.singleton_subset_iff] at h1 h2
  exact h1.symm.trans h2

theorem corr_heckeSet_kill {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {S : Scheme.{0}} (t : SAB H S) {P : Ideal (𝓞 E)} {p i : ℕ} {K : Set t.G.left} (hpP : (p : 𝓞 E) ∈ P)
    (hK : HeckeSet D t P p i K) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ t.G)
    (hz : Set.range z.left ⊆ K) : z ^ p ^ 2 = 1 := by
  have hnat : ∀ {T : Over S} (x : T ⟶ t.G) (n : ℕ), x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
    intro T x n
    induction n with
    | zero =>
      have h := t.act.add 0 0
      rw [add_zero] at h
      have h0 : t.act.act 0 = 1 := by simpa using h
      rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]
  obtain ⟨C, hC, hH⟩ := hK k x
  have hzC := hH.2.2.1 ((hC z).2 hz)
  have hbar : (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
    rwa [map_natCast] at this
  have h := hzC ((p ^ 2 : ℕ) : 𝓞 E) (by
    rw [Nat.cast_pow, pow_two]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hbar)
  rwa [hnat] at h

theorem corr_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), 1 ≤ D.p + D.q → admitted l 𝔓 p → Nonempty (Corr Xo 𝔓 p i) := by
  intro E _ _ _ H D l Xo P p i hr hA
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_heckeKernelScheme_universal_reduced_bases E H D l Xo P p i hA
  have := Z.et₁
  have := Xo.smooth
  have hXs : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have hs : Smooth (Z.π₁ ≫ Xo.s) := inferInstance
  have hred : IsReduced Z.Hk :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hs).1
  obtain ⟨S', π, o', m, τ, hf, he, hsu, hL⟩ :=
    GlobalTheory.T.hecke_set_etale_level_structure_exists E H D l P p i Z.Hk _ Z.o₁ Z.K hA hZ Z.hecke
  have hH' := ((GlobalTheory.heckeSets_pull E H D P p i _ _ _ _ _ m.toSABMap Z.o₁.proper).2 Z.K).1 Z.hecke
  have hq' := GlobalTheory.T.heckeQuotient_exists_listed_kernels_smooth_base E H D l Xo P p i _ S' _ o' τ _ hr hA inferInstance hL hH'
  obtain ⟨o₂, ψ, hi, hk⟩ := GlobalTheory.T.heckeQuotient_descends_etale_surjective_cover E H D l Xo P p i Z.Hk S' _ π Z.o₁ o' m Z.K hA Z.hecke he hsu
    inferInstance hq'
  obtain ⟨π₂, ⟨hb, ⟨m₂⟩⟩, -⟩ := Xo.rep _ _ hred o₂
  refine ⟨{ toKerScheme := Z, π₂ := π₂, base₂ := hb, o₂ := o₂, m₂ := m₂, ψ := ψ, isog := hi, ker := hk, univ := ?_ }⟩
  intro S s hS o o' ψ' ⟨hi', K', hk', hH⟩
  have := o'.proper
  have het := (etSet_of_kerSet S _ _ ψ' K' inferInstance hi'.1.2.1 hi'.1.2.2.1 hk').1
  obtain ⟨h, ⟨hh, n₁, hn₁⟩, hu⟩ := Z.rep S s hS o K' het hH
  refine ⟨h, ⟨hh, ?_⟩, ?_⟩
  · obtain ⟨o₃, ⟨n₃⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ s h rfl rfl
      (by rw [hh]; simp [spMap]) o₂
    obtain ⟨⟨ψ₃, hψ₃, -⟩, hall⟩ := GlobalTheory.T.exists_isogeny_pullback_heckeModuliObject E H D l p _ _ _ _ h Z.o₁ o₂ o o₃ n₁ n₃ ψ
    obtain ⟨hi₃, hk₃⟩ := hall ψ₃ hψ₃
    have hk₃' := hk₃ Z.K hi.1.1 hk
    rw [← hn₁] at hk₃'
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_iso_quotients_same_kernel_reduced_base E H D l p S s o o' o₃ ψ' ψ₃ K' hA.2.2.1 hA.2.2.2.2 hi' (hi₃ hi) hk' hk₃'
      (corr_heckeSet_kill o.t hA.2.2.2.1 hH)
    have hc := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o₂ o₃ o').2 h (𝟙 S) n₃).1 m
    have hc' : ∀ g : S ⟶ Z.Hk, g = h → (∃ m'' : ObjMap o' o₂ g, m''.toSABMap.φ = m.toSABMap.φ ≫ n₃.toSABMap.φ) →
        ∃ m'' : ObjMap o' o₂ h, m''.toSABMap.φ = m.toSABMap.φ ≫ n₃.toSABMap.φ := by
      rintro g rfl hg
      exact hg
    obtain ⟨n₂, hn₂⟩ := hc' _ (Category.id_comp h) hc
    exact ⟨n₁, n₂, by rw [hn₂, ← Category.assoc, hm, hψ₃]⟩
  · rintro h' ⟨hh', n₁', n₂', e⟩
    have hk₃ := ((GlobalTheory.T.exists_isogeny_pullback_heckeModuliObject E H D l p _ _ _ _ h' Z.o₁ o₂ o o' n₁' n₂' ψ).2 ψ' e).2 Z.K hi.1.1 hk
    exact hu h' ⟨hh', n₁', corr_kerSet_unique hk' hk₃⟩

end GlobalTheory.HkFam
