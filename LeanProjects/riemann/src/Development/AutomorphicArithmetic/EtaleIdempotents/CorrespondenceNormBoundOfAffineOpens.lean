import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrystallineComparison
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFactsAlt
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSecChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatchVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSnBasic
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.crystallineComparison

private lemma spec_chart {B : Type} [CommRing B] {X : Scheme.{0}} (w : Spec (CommRingCat.of B) ⟶ X) {V : X.Opens}
    (hV : IsAffineOpen V) (hw : ⊤ ≤ w ⁻¹ᵁ V) :
    w = Spec.map (w.appLE V ⊤ hw ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom) ≫ hV.fromSpec := by
  rw [Spec.map_comp, Category.assoc, hV.SpecMap_appLE_fromSpec w (isAffineOpen_top _) hw,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

private lemma unit_away (l : ℕ) (B : Type) [CommRing B] :
    IsUnit (l : Γ(Spec (CommRingCat.of (Localization.Away (l : B))), ⊤)) := by
  have h : IsUnit (l : Localization.Away (l : B)) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : B)) (l : B)
  simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (l : B)))).inv.hom

private lemma chart_norm {l Q n : ℕ} {Y : Scheme.{0}} (T : Fin (n + 1) → Corr l Y) {U V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : ∀ j, (T j).p ⁻¹ᵁ U ≤ (T j).r ⁻¹ᵁ V) (π : Γ(Y, ⊤))
    (hn : NormOn l Q n π T U V h) (B : Type) [CommRing B] (hl : (l : B) ∈ nonZeroDivisors B)
    (y : Spec (CommRingCat.of B) ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ U)
    (z : ∀ j, Fin (T j).d → (Spec (CommRingCat.of B) ⟶ (T j).Z)) (hzy : ∀ j i, z j i ≫ (T j).p = y)
    (hs : ∀ j, SplitOn (T j).p (awayPt l B ≫ y) fun i => awayPt l B ≫ z j i)
    (B' : Type) [CommRing B'] (ψ : B →+* B')
    (hψ : ψ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (y.appTop.hom π)) = 0) :
    ∃ α : ∀ j, Fin (T j).d → (Γ(Y, V) →+* B),
      (∀ j i, z j i ≫ (T j).r = ptOf hV B (α j i)) ∧
      ∀ (ι : Type) [Fintype ι] (x : ι → Γ(Y, V)),
        SameNorm (pts (wEv Q) fun j i k => ψ (α j i (x k)) ^ Q ^ (n - j))
          (pts (wOd Q) fun j i k => ψ (α j i (x k)) ^ Q ^ (n - j)) := by
  have hz : ∀ j i, ⊤ ≤ z j i ⁻¹ᵁ ((T j).p ⁻¹ᵁ U) := fun j i => by
    rw [← Scheme.Hom.comp_preimage, hzy]
    exact hy
  letI := fun j => (T j).alg U
  letI : Algebra Γ(Y, U) B := ((y.appLE U ⊤ hy ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom).toAlgebra
  have H := fun j => splitRules.2 l Y (T j) U hU B y hy (z j) (hz j) (hzy j) (hs j)
  choose ζ hζ hζe using H
  have hres : ψ (algebraMap Γ(Y, U) B (Y.presheaf.map (homOfLE le_top).op π)) = 0 := by
    have e : Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ y.appLE U ⊤ hy = y.appTop := by
      rw [Scheme.Hom.map_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    have e' : algebraMap Γ(Y, U) B (Y.presheaf.map (homOfLE le_top).op π) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (y.appTop.hom π) := by
      rw [← e]
      rfl
    rw [e', hψ]
  refine ⟨fun j i => (ζ j i).toRingHom.comp ((T j).r.appLE V _ (h j)).hom, fun j i => ?_, fun ι _ x => ?_⟩
  · haveI := (T j).fin
    have hS : IsAffineOpen ((T j).p ⁻¹ᵁ U) := hU.preimage (T j).p
    have e1 := spec_chart (z j i) hS (hz j i)
    have e2 : (z j i).appLE ((T j).p ⁻¹ᵁ U) ⊤ (hz j i) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
        CommRingCat.ofHom (ζ j i).toRingHom := by
      ext a
      exact (hζe j i a).symm
    rw [e2] at e1
    have e3 := (ptChart_of Y V hV B).2.2 (T j).Z (T j).r _ hS (h j) B (RingHom.id B) (ζ j i).toRingHom
    have e4 : Spec.map (CommRingCat.ofHom (RingHom.id B)) = 𝟙 _ := by
      rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [e4, Category.id_comp, RingHom.id_comp] at e3
    rw [e1]
    exact (Category.assoc _ _ _).trans e3
  · exact hn B hl (fun j => Fin (T j).d) ζ hζ B' ψ hres ι x

theorem UpperTheory.correspondence_norm_bound_of_affine_opens :
    ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of O)) (ϖ : O) (Q n : ℕ)
        (T : Fin (n + 1) → Corr l Y) (κ : O →+* OC l) (D : WDat l T)
        (A : Test l) (y : (PX (D.π ≫ q) κ).obj A.obj) {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
        (h : ∀ j, (T j).p ⁻¹ᵁ U ≤ (T j).r ⁻¹ᵁ V), ⊤ ≤ (y.1 ≫ D.π) ⁻¹ᵁ U →
        NormOn l Q n (fn q ϖ) T U V h → ∀ (ψ : A.obj.U →+* Qb A.obj), ψ (A.obj.oC (κ ϖ)) = 0 →
        ∃ α : ∀ j, Fin (T j).d → (Γ(Y, V) →+* A.obj.U),
          (∀ j i, y.1 ≫ D.s j i ≫ (T j).r = ptOf hV A.obj.U (α j i)) ∧
          ∀ (ι : Type) [Fintype ι] (x : ι → Γ(Y, V)),
            SameNorm (pts (wEv Q) fun j i k => ψ (α j i (x k)) ^ Q ^ (n - j))
              (pts (wOd Q) fun j i k => ψ (α j i (x k)) ^ Q ^ (n - j)) := by
  intro l _ O _ Y q ϖ Q n T κ D A y U V hU hV h hy hn ψ hψ
  have hl : (l : A.obj.U) ∈ nonZeroDivisors A.obj.U := (testFacts l A.obj A.property).1
  have hyq : (y.1 ≫ D.π) ≫ q = Spec.map (CommRingCat.ofHom (A.obj.oC.comp κ)) := by
    rw [Category.assoc]
    exact y.2
  have hval : (Scheme.ΓSpecIso (CommRingCat.of A.obj.U)).hom.hom ((y.1 ≫ D.π).appTop.hom (fn q ϖ)) =
      A.obj.oC (κ ϖ) := by
    have e : (y.1 ≫ D.π).appTop.hom (fn q ϖ) =
        ((y.1 ≫ D.π) ≫ q).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ) := by
      rw [Scheme.Hom.comp_appTop]
      rfl
    rw [e, hyq]
    have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (A.obj.oC.comp κ))
    have e3 := congr($(e2).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ))
    refine e3.trans ?_
    simp
  obtain ⟨α, h1, h2⟩ := chart_norm T hU hV h (fn q ϖ) hn A.obj.U hl (y.1 ≫ D.π) hy
    (fun j i => y.1 ≫ D.s j i) (fun j i => by rw [Category.assoc, D.hs])
    (fun j => by
      have := D.gen _ (awayPt l A.obj.U ≫ y.1) (unit_away l A.obj.U) j
      simpa only [Category.assoc] using this)
    (Qb A.obj) ψ (by rw [hval]; exact hψ)
  exact ⟨α, h1, h2⟩
