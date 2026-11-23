import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.LocalCoord

theorem appLE_resG {X Y : Scheme.{0}} (x : Y ⟶ X) {U U' : X.Opens} (hU : U' ≤ U) {V : Y.Opens} (h : V ≤ x ⁻¹ᵁ U')
    (a : Γ(X, U)) : (x.appLE U' V h).hom (resG X hU a) = (x.appLE U V (h.trans (x.preimage_mono hU))).hom a := by
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem resG_appLE {X Y : Scheme.{0}} (x : Y ⟶ X) {U : X.Opens} {V V' : Y.Opens} (h : V ≤ x ⁻¹ᵁ U) (hV : V' ≤ V)
    (a : Γ(X, U)) : resG Y hV ((x.appLE U V h).hom a) = (x.appLE U V' (hV.trans h)).hom a := by
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private theorem res_val_lemma {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    ((res h a : Γ(X, V)ˣ) : Γ(X, V)) = resG X h (a : Γ(X, U)) := by
  rfl

private theorem res_pullU_val_eq_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {W : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ W)
    (u : Γ(X, W)ˣ) : ((res h (pullU f W u) : Γ(Y, V)ˣ) : Γ(Y, V)) = (f.appLE W V h).hom (u : Γ(X, W)) := by
  rfl

private theorem pull_U_le_preimage_U {X Y : Scheme.{0}} (M : LB X) (f : Y ⟶ X) (j : PUnit → M.ι) (k : PUnit) :
    (M.pull f).U j ≤ f ⁻¹ᵁ M.U (j k) := by
  intro y hy
  have hy' : y ∈ ⋂ k, f ⁻¹' (M.U (j k) : Set X) := hy
  exact Set.mem_iInter.1 hy' k

private theorem resG_app_eq_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {W : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ W)
    (u : Γ(X, W)) : resG Y h ((f.app W).hom u) = (f.appLE W V h).hom u := by
  rfl

private theorem pullU_val_eq_app {X Y : Scheme.{0}} (f : Y ⟶ X) (W : X.Opens) (u : Γ(X, W)ˣ) :
    ((pullU f W u : Γ(Y, f ⁻¹ᵁ W)ˣ) : Γ(Y, f ⁻¹ᵁ W)) = (f.app W).hom (u : Γ(X, W)) := by
  rfl

private theorem pull_g_lemma_6 {X Y : Scheme.{0}} (M : LB X) (f : Y ⟶ X) (j j' : PUnit → M.ι)
    (h : (M.pull f).U j ⊓ (M.pull f).U j' ≤ f ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    (((M.pull f).g j j' : Γ(Y, (M.pull f).U j ⊓ (M.pull f).U j')ˣ) : Γ(Y, (M.pull f).U j ⊓ (M.pull f).U j')) =
      (f.appLE _ _ h).hom (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(X, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) := by
  unfold LB.pull LB.LinComb
  simp only [Fintype.prod_unique, zpow_one]
  rfl

private theorem resG_eq_presheaf_map {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    resG X h a = (X.presheaf.map (homOfLE h).op).hom a := by
  rfl

theorem exists_secCoord_of_chart {X : Scheme.{0}} (M : LB X) (hM : M.IsLB) {I : Type} (th : I → M.Sec)
    {R : Type} [CommRing R] (x : Sp R ⟶ X) (j₀ : M.ι) (h₀ : ⊤ ≤ x ⁻¹ᵁ M.U j₀) : ∃ v, SecCoord M th x v := by
  have hV : ∀ j : PUnit → M.ι, (M.pull x).U j ≤ x ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U j₀) := by
    intro j y hy
    exact ⟨pull_U_le_preimage_U M x j PUnit.unit hy, h₀ trivial⟩
  let τ : (M.pull x).Gen := ⟨fun j => res (hV j) (pullU x _ (M.g (j PUnit.unit) j₀))⟩
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((x.appLE (M.U j₀) ⊤ h₀).hom ((th i).f j₀)), τ, ?_, ?_⟩
  · intro j j'
    apply Units.ext
    have hc := congrArg Units.val (hM.cocycle (j PUnit.unit) (j' PUnit.unit) j₀)
    simp only [Units.val_mul, res_val_lemma] at hc
    have hT : (M.pull x).U j ⊓ (M.pull x).U j' ≤ x ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit) ⊓ M.U j₀) := by
      intro y hy
      exact ⟨⟨pull_U_le_preimage_U M x j _ hy.1, pull_U_le_preimage_U M x j' _ hy.2⟩, h₀ trivial⟩
    have hc' := congrArg (x.appLE _ _ hT).hom hc
    rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at hc'
    have hjj : (M.pull x).U j ⊓ (M.pull x).U j' ≤ x ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) := by
      intro y hy
      exact ⟨pull_U_le_preimage_U M x j _ hy.1, pull_U_le_preimage_U M x j' _ hy.2⟩
    simp only [τ, Units.val_mul, res_val_lemma, pullU_val_eq_app, resG_app_eq_appLE, resG_appLE, pull_g_lemma_6 M x j j' hjj]
    exact hc'.symm
  · intro i j h
    have hf := (th i).compat (j PUnit.unit) j₀
    simp only [τ, res_pullU_val_eq_appLE]
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply, resG_appLE,
      ← appLE_resG x (inf_le_left : M.U (j PUnit.unit) ⊓ M.U j₀ ≤ _) (hV j), resG_eq_presheaf_map, hf, map_mul,
      ← resG_eq_presheaf_map, appLE_resG, mul_comm]

theorem exists_chart {X : Scheme.{0}} (M : LB X) (hM : M.IsLB) (p : X) : ∃ j, p ∈ M.U j := by
  have hp : p ∈ (⨆ i, M.U i) := by
    rw [hM.cover]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.1 hp

theorem secCoord_local : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), ∃ v, SecCoord M th x v) ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (p : Sp R), ∃ f : R, f ∉ p.asIdeal ∧ ∃ v, SecCoord M th (spMap (algebraMap R (Localization.Away f)) ≫ x) v) ∧ ∀ p : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : I → R), IsOpenImmersion x ∧ p ∈ Set.range x ∧ SecCoord M th x v := by
  intro X M I th hM
  refine ⟨?_, ?_, ?_⟩
  · intro R _ _ x
    obtain ⟨j₀, hj⟩ := exists_chart M hM (x (IsLocalRing.closedPoint R))
    refine exists_secCoord_of_chart M hM th x j₀ ?_
    intro y _
    exact (IsLocalRing.specializes_closedPoint (R := R) y).mem_open (x ⁻¹ᵁ M.U j₀).isOpen hj
  · intro R _ x p
    obtain ⟨j₀, hj⟩ := exists_chart M hM (x p)
    obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := (p : PrimeSpectrum R)) hj
        (x ⁻¹ᵁ M.U j₀).isOpen
    refine ⟨f, hpf, exists_secCoord_of_chart M hM th _ j₀ ?_⟩
    intro y _
    have hy : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) (show PrimeSpectrum (Localization.Away f) from y) ∈
        ((PrimeSpectrum.basicOpen (f : R) : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) (f : R)]
      exact ⟨_, rfl⟩
    exact hsub hy
  · intro p
    obtain ⟨j₀, hj⟩ := exists_chart M hM p
    obtain ⟨V, hV, hpV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hj
    have hV' : IsAffineOpen V := hV
    obtain ⟨v, hv⟩ := exists_secCoord_of_chart M hM th (R := Γ(X, V)) hV'.fromSpec j₀ (by
      intro y _
      apply hVU
      have h1 : hV'.fromSpec y ∈ Set.range hV'.fromSpec := ⟨y, rfl⟩
      rw [hV'.range_fromSpec] at h1
      exact h1)
    refine ⟨Γ(X, V), inferInstance, hV'.fromSpec, v, inferInstance, ?_, hv⟩
    rw [hV'.range_fromSpec]
    exact hpV

end GlobalTheory.ZM.LocalCoord
end
