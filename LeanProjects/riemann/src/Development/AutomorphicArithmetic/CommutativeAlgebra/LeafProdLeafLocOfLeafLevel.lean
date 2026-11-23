import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing
import Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectivityOfDisjointOpenCover
import Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectivityOfCechDisjointCover
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

private theorem conn_mono {R : Type} [CommRing R] {F : Shv R} {c m : ℤ} (h : m ≤ c) {E E' : Spc} {f : E ⟶ E'}
    (hf : Conn R F c f) : Conn R F m f := fun n =>
  ⟨fun hn => (hf n).1 (by omega), fun hn => (hf n).2 (by omega)⟩

private theorem conn_nonpos (a9 : A9) {R : Type} [CommRing R] (F : Shv R) {m : ℤ} (h : m ≤ 0) {E E' : Spc} (f : E ⟶ E') :
    Conn R F m f := by
  intro n
  have hs := (a9 R F).1
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · haveI := hs E n (by omega)
    haveI := hs E' n (by omega)
    exact ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ y⟩⟩
  · haveI := hs E' n (by omega)
    exact fun x y _ => Subsingleton.elim x y

private theorem conn_iso {R : Type} [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E') [IsIso f] :
    Conn R F c f := by
  have hb : ∀ n, Function.Bijective (pull R f F n) := fun n =>
    Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
      fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id],
      fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩
  exact fun n => ⟨fun _ => hb n, fun _ => (hb n).1⟩

private theorem conn_congr {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {X : Scheme.{0}} {U U' : X.Opens} (e : U = U')
    (h : Conn R F c (sch.map U.ι)) : Conn R F c (sch.map U'.ι) := e ▸ h

private theorem conn_top {R : Type} [CommRing R] (F : Shv R) (c : ℤ) {X : Scheme.{0}} {U : X.Opens} (e : U = ⊤) :
    Conn R F c (sch.map U.ι) := by
  subst e
  haveI : IsIso (⊤ : X.Opens).ι := by
    first
      | infer_instance
      | (rw [← Scheme.topIso_hom]; infer_instance)
      | exact isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  exact conn_iso F c _

private theorem exists_good {R : Type} [CommRing R] {F : Shv R} {c : ℤ} {X : Scheme.{0}} {U : X.Opens}
    (H : ∀ x : X, x ∉ U → ∀ W : X.Opens, x ∈ W → ∃ (Y : Scheme.{0}) (j : Y ⟶ X) (_ : IsOpenImmersion j),
      x ∈ Set.range j ∧ Set.range j ⊆ (W : Set X) ∧ Conn R F c (sch.map (j ⁻¹ᵁ U).ι))
    {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) :
    ∃ (O : Scheme.{0}) (o : O ⟶ Y) (_ : IsOpenImmersion o), y ∈ Set.range o ∧
      Conn R F c (sch.map ((o ≫ j) ⁻¹ᵁ U).ι) := by
  by_cases hy : j y ∈ U
  · refine ⟨_, (j ⁻¹ᵁ U).ι, inferInstance, ?_, conn_top F c ?_⟩
    · rw [Scheme.Opens.range_ι]
      exact hy
    · rw [Scheme.Hom.comp_preimage]
      exact Scheme.Opens.ι_preimage_self _
  · obtain ⟨Y', j', hj', hx, hsub, hC⟩ := H (j y) hy j.opensRange ⟨y, rfl⟩
    have hle : Set.range j' ⊆ Set.range j := hsub
    have hfac : IsOpenImmersion.lift j j' hle ≫ j = j' := IsOpenImmersion.lift_fac j j' hle
    haveI : IsOpenImmersion (IsOpenImmersion.lift j j' hle ≫ j) := by rw [hfac]; exact hj'
    refine ⟨Y', IsOpenImmersion.lift j j' hle, IsOpenImmersion.of_comp _ j, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := hx
      refine ⟨z, j.isOpenEmbedding.injective ?_⟩
      rw [← hz, ← Scheme.Hom.comp_apply, hfac]
    · rw [hfac]
      exact hC

theorem UpperTheory.leafProd_leafLoc_of_leafLevel :
    LeafLevel → LeafProd → LeafLoc := by
  intro hLev hProd a1 a2 a9 R _ F c X U H
  have main : ∀ k : ℕ, ∀ {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j],
      Conn R F (min c k) (sch.map (j ⁻¹ᵁ U).ι) := by
    intro k
    induction k with
    | zero =>
      intro Y j _
      exact conn_nonpos a9 F (by simp) _
    | succ k ih =>
      intro Y j _
      have hmc : min c ((k + 1 : ℕ) : ℤ) ≤ c := min_le_left _ _
      have hm1 : min c ((k + 1 : ℕ) : ℤ) - 1 ≤ min c (k : ℤ) := by omega
      choose O o ho hyo hc using fun y : Y => exists_good H j y
      haveI := ho
      have hcomp : ∀ a, Sigma.ι O a ≫ Sigma.desc o = o a := fun a => Sigma.ι_desc _ _
      haveI hsurj : Surjective (Sigma.desc o) := ⟨fun y => by
        obtain ⟨z, hz⟩ := hyo y
        refine ⟨Sigma.ι O y z, ?_⟩
        rw [← Scheme.Hom.comp_apply, hcomp, hz]⟩
      have hdisj : ∀ a b, a ≠ b → Disjoint (Set.range (Sigma.ι O a)) (Set.range (Sigma.ι O b)) := fun a b hab => by
        have := disjoint_opensRange_sigmaι O a b hab
        rw [Set.disjoint_left]
        intro x hxa hxb
        exact (disjoint_iff_inf_le.1 this : _) ⟨hxa, hxb⟩
      have hcov : ∀ y : (∐ O : Scheme.{0}), ∃ a, y ∈ Set.range (Sigma.ι O a) := fun y => by
        obtain ⟨a, z, hz⟩ := (sigmaOpenCover O).exists_eq y
        exact ⟨a, z, hz⟩
      refine UpperTheory.connectivity_of_cech_disjoint_cover hLev a1 a2 R F _ (Sigma.desc o)
        ⟨Y, O, Sigma.ι O, inferInstance, hdisj, hcov, fun a => by rw [hcomp]; exact ho a⟩ (j ⁻¹ᵁ U) ?_ ?_
      · refine UpperTheory.connectivity_of_disjoint_open_cover hProd a1 R F _ O (Sigma.ι O) hdisj hcov _ fun a => ?_
        refine conn_congr ?_ (conn_mono hmc (hc a))
        rw [Scheme.Hom.comp_preimage, ← hcomp a, Scheme.Hom.comp_preimage]
      · rintro Z g ⟨ι', O', j', hoi, hdis', hcov', hcp⟩
        haveI := hoi
        refine UpperTheory.connectivity_of_disjoint_open_cover hProd a1 R F _ O' j' hdis' hcov' _ fun a => ?_
        haveI := hcp a
        refine conn_congr ?_ (conn_mono hm1 (ih ((j' a ≫ g) ≫ j)))
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  have hfin := main c.toNat (𝟙 X)
  have hmin : min c (c.toNat : ℤ) = c := min_eq_left (Int.self_le_toNat c)
  rw [hmin] at hfin
  exact conn_congr (Scheme.Hom.id_preimage U) hfin

end
