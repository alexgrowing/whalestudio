import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericResidueLinearIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodStalks

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem interNumRed_eq_one_of_eq_singleton {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    [Algebra K Γ(X, ⊤)] (hp : IsProjOver (strHom K X)) (Z : Closeds X) {w : X}
    (hZ : (Z : Set X) = {w}) (P : Fin 0 → LB X) : interNumRed K Z P = 1 := by
  letI := algebraΓAlong K (redι Z)
  have hk := appTop_algebraMap_along K (redι Z)
  have hX : IsProper (strHom K X) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have hrange : Set.range (redι Z) = {w} := (range_redι Z).trans hZ

  have hsub : Subsingleton (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    refine ⟨fun a b => (redι Z).isEmbedding.injective ?_⟩
    have ha : redι Z a = w := by
      have : redι Z a ∈ Set.range (redι Z) := ⟨a, rfl⟩
      rwa [hrange] at this
    have hb : redι Z b = w := by
      have : redι Z b ∈ Set.range (redι Z) := ⟨b, rfl⟩
      rwa [hrange] at this
    rw [ha, hb]
  have hne : Nonempty (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    have : w ∈ Set.range (redι Z) := by rw [hrange]; rfl
    obtain ⟨a, -⟩ := this
    exact ⟨a⟩
  obtain ⟨p⟩ := hne
  have hAff : IsAffine (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := ⊤) trivial
    have hUt : U = ⊤ := top_le_iff.1 fun q _ => (Subsingleton.elim q p) ▸ hpU
    subst hUt
    haveI : IsAffine (⊤ : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Opens).toScheme := hU
    exact IsAffine.of_isIso (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.topIso.inv
  haveI : Nonempty (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := ⟨p⟩
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    isIntegral_red (hZ ▸ isIrreducible_singleton)
  have hpr : IsProper (strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    rw [← comp_strHom hk]
    infer_instance
  haveI : IsFinite (strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : Module.Finite K Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := by
    have hf := IsFinite.finite_app (strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ⊤
      (isAffineOpen_top _)
    have hi : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom.Finite :=
      RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
    have hc := hf.comp hi
    have e : algebraMap K Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) =
        ((strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme).app ⊤).hom.comp
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom :=
      RingHom.ext (algebraMap_eq_strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)
    rw [← RingHom.finite_algebraMap, e]
    exact hc
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
    (K := Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤))
  have e1 : interNumRed K Z P =
      chi K (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    change interNumOn K (redι Z) P = _
    exact (interNumOn_eq_interNum_pull hk isEmptyElim).trans (interNum_of_isEmpty K _ _)
  rw [e1, chi_structureModule_of_isAffine]
  have e2 := (LinearEquiv.ofBijective (Algebra.linearMap K
    Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤)) hbij).finrank_eq
  rw [← e2]
  simp

theorem chi_eq_ncard_support : ∀ {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [Algebra K Γ(X, ⊤)], IsProjOver (strHom K X) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (0 : ℕ) → (∀ x : X, Module.length (X.presheaf.stalk x) (F.presheaf.stalk x :) ≤ 1) → chi K F = ((support F).ncard : ℤ) ∧ ∀ x ∈ support F, IsClosed ({x} : Set X) := by
  intro K _ _ X _ hp F _ hd hlen
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  have hdim0 : ∀ w ∈ support F,
      topologicalKrullDim (closure ({w} : Set X)) = ((0 : ℕ) : WithBot ℕ∞) := by
    intro w hw
    have hle := (GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.dim_closure_le_suppDim hw).trans hd
    have hne : topologicalKrullDim (closure ({w} : Set X)) ≠ ⊥ := by
      rw [Ne, topologicalKrullDim_eq_bot_iff]
      exact not_isEmpty_of_nonempty (α := (closure ({w} : Set X) : Set X))
        (h := ⟨⟨w, subset_closure rfl⟩⟩)
    obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hne
    rw [← ha] at hle ⊢
    have : a ≤ 0 := by exact_mod_cast hle
    have : a = 0 := le_antisymm this bot_le
    subst this
    rfl
  have hcl : ∀ x ∈ support F, IsClosed ({x} : Set X) := by
    intro x hx
    refine isClosed_of_closure_subset fun y hy => ?_
    have hys : y ∈ support F :=
      (isClosed_support F).closure_subset_iff.2 (Set.singleton_subset_iff.2 hx) hy
    exact (GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.eq_of_mem_closure hd (hdim0 y hys) x hx hy).symm
  have hfin : (support F).Finite := by
    obtain ⟨S, hSf, hSc, hSi, hS⟩ :=
      NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_support F)
    rw [hS]
    refine hSf.sUnion fun t ht => ?_
    have hg := (hSi t ht).isGenericPoint_genericPoint_closure
    have hgt : (hSi t ht).genericPoint ∈ t := by
      have := hg.mem
      rwa [(hSc t ht).closure_eq] at this
    have hgs : (hSi t ht).genericPoint ∈ support F := by
      rw [hS]
      exact ⟨t, ht, hgt⟩
    have e : t = {(hSi t ht).genericPoint} := by
      have := hg.def
      rw [(hSc t ht).closure_eq, (hcl _ hgs).closure_eq] at this
      exact this.symm
    rw [e]
    exact Set.finite_singleton _
  refine ⟨?_, hcl⟩
  have hP : ∀ i : Fin 0, ((finZeroElim : Fin 0 → LB X) i).IsLB := isEmptyElim
  have h := GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.interNum_eq_sum_length_mul_interNumRed K X hp (Fin 0)
    finZeroElim hP F (by simpa using hd) hfin.toFinset (fun w hw _ => hfin.mem_toFinset.2 hw)
  rw [interNum_of_isEmpty] at h
  rw [h, Set.ncard_eq_toFinset_card _ hfin, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hws : w ∈ support F := hfin.mem_toFinset.1 hw
  have hlen1 : Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) = 1 := by
    refine le_antisymm (hlen w) (ENat.one_le_iff_ne_zero.2 fun h0 => ?_)
    have := Module.length_eq_zero_iff.1 h0
    exact (mem_support_iff.1 hws).exists_pair_ne.elim fun a ⟨b, hab⟩ => hab (Subsingleton.elim a b)
  rw [hlen1, interNumRed_eq_one_of_eq_singleton hp _ (w := w) (hcl w hws).closure_eq]
  simp

end GlobalTheory.CompanionTheory.KoszulCount
