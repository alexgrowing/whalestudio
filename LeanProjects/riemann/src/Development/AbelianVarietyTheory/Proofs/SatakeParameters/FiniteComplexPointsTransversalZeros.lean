import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TransvZeros

theorem mem_minimalPrimes_of_le_sup_sq {A : Type} [CommRing A] {I m : Ideal A} [hm : m.IsMaximal]
    (hfg : m.FG) (hI : I ≤ m) (hsq : m ≤ I ⊔ m ^ 2) : m ∈ I.minimalPrimes := by
  refine ⟨⟨hm.isPrime, hI⟩, fun P hP hPm => ?_⟩
  obtain ⟨hPp, hIP⟩ := hP
  let π := Ideal.Quotient.mk I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hcm : (m.map π).comap π = m := by
    rw [Ideal.comap_map_of_surjective' π hπ, Ideal.mk_ker, sup_eq_left.2 hI]
  have hcP : (P.map π).comap π = P := by
    rw [Ideal.comap_map_of_surjective' π hπ, Ideal.mk_ker, sup_eq_left.2 hIP]
  have hidem : IsIdempotentElem (m.map π) := by
    refine le_antisymm Ideal.mul_le_left ?_
    have h1 : m.map π ≤ (I ⊔ m ^ 2).map π := Ideal.map_mono hsq
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow, pow_two] at h1
    exact h1
  obtain ⟨e, he, hme⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (hfg.map π)).1 hidem
  have hPq : (P.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ
    (by rw [Ideal.mk_ker]; exact hIP)
  have hem : e ∈ m.map π := hme ▸ Ideal.mem_span_singleton_self e
  have hne : 1 - e ∉ P.map π := by
    intro h
    have h' : 1 - e ∈ m.map π := Ideal.map_mono hPm h
    have h1 : (1 : A ⧸ I) ∈ m.map π := by simpa using Ideal.add_mem _ h' hem
    have h2 : (1 : A) ∈ m := by
      rw [← hcm, Ideal.mem_comap, map_one]; exact h1
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  have heP : e ∈ P.map π := by
    have h0 : e * (1 - e) ∈ P.map π := by
      rw [mul_sub, mul_one, he.eq, sub_self]; exact Ideal.zero_mem _
    exact (hPq.mem_or_mem h0).resolve_right hne
  have hle : m.map π ≤ P.map π := by
    rw [hme, Ideal.span_le, Set.singleton_subset_iff]; exact heP
  rw [← hcm, ← hcP]
  exact Ideal.comap_mono hle

theorem eq_of_evHom_eq {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} (hU : IsAffineOpen U)
    {y z : CxPts p (RingHom.id ℂ)} (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U)
    (hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U) (e : CxPts.evHom hy = CxPts.evHom hz) : y = z := by
  have e₁ : y.1.appLE U ⊤ hy = z.1.appLE U ⊤ hz := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]
    exact CommRingCat.hom_ext e
  have a := IsAffineOpen.SpecMap_appLE_fromSpec y.1 hU (isAffineOpen_top (Sp ℂ)) hy
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec z.1 hU (isAffineOpen_top (Sp ℂ)) hz
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact Subtype.ext ((cancel_epi _).1 a).symm

theorem evHom_algX {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} {y : CxPts p (RingHom.id ℂ)}
    (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U) (c : ℂ) : CxPts.evHom hy (algX p U c) = c :=
  (CxPts.ev_eq hy _).symm.trans (CxPts.ev_algX hy c)

theorem eq_of_ker_eq {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} (hU : IsAffineOpen U)
    {y z : CxPts p (RingHom.id ℂ)} (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U)
    (hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U)
    (e : RingHom.ker (CxPts.evHom hy) = RingHom.ker (CxPts.evHom hz)) : y = z := by
  refine eq_of_evHom_eq hU hy hz (RingHom.ext fun f => ?_)
  have h1 : f - algX p U (CxPts.evHom hy f) ∈ RingHom.ker (CxPts.evHom hy) := by
    rw [RingHom.mem_ker, map_sub, evHom_algX, sub_self]
  rw [e, RingHom.mem_ker, map_sub, evHom_algX, sub_eq_zero] at h1
  exact h1.symm

theorem finite_transv_zeros : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ (k : ℕ) (φ : Fin k → Γ(X, U)), {z : CxPts p (RingHom.id ℂ) | ∃ hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U,
      (∀ j, CxPts.evHom hz (φ j) = 0) ∧
        RingHom.ker (CxPts.evHom hz) ≤ Ideal.span (Set.range φ) ⊔ RingHom.ker (CxPts.evHom hz) ^ 2}.Finite := by
  intro X p _ U hU k φ
  have h1 := LocallyOfFiniteType.finiteType_of_affine_subset p (isAffineOpen_top (Sp ℂ)) hU (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  have hft : (algX p U).FiniteType := h1.comp h2
  letI : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, U) := hft
  haveI : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing ℂ _
  classical
  let F : CxPts p (RingHom.id ℂ) → Ideal Γ(X, U) := fun z =>
    if hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U then RingHom.ker (CxPts.evHom hz) else ⊥
  refine Set.Finite.of_finite_image (f := F)
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ (Ideal.span (Set.range φ))).subset ?_) ?_
  · rintro _ ⟨z, ⟨hz, hv, hsq⟩, rfl⟩
    simp only [F, dif_pos hz]
    haveI : (RingHom.ker (CxPts.evHom hz)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ fun c => ⟨algX p U c, evHom_algX hz c⟩
    refine mem_minimalPrimes_of_le_sup_sq (IsNoetherian.noetherian _) ?_ hsq
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hv j
  · rintro y ⟨hy, -⟩ z ⟨hz, -⟩ e
    simp only [F, dif_pos hy, dif_pos hz] at e
    exact eq_of_ker_eq hU hy hz e

end GlobalTheory.TransvZeros
