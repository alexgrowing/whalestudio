import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratesAlong

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjSpace

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

theorem mem_ideal_of_locally (I : W.IdealSheafData) (A : W.affineOpens) (b : Γ(W, A.1))
    (h : ∀ y ∈ A.1, ∃ (B : W.affineOpens) (e : B.1 ≤ A.1), y ∈ B.1 ∧ resG W e b ∈ I.ideal B) :
    b ∈ I.ideal A := by
  have hk : ∀ B : W.affineOpens, I.ideal B = RingHom.ker (I.subschemeι.app B.1).hom := fun B => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [hk, RingHom.mem_ker]
  refine ext_germ fun z hz => ?_
  obtain ⟨B, e, hzB, this⟩ := h _ hz
  rw [hk, RingHom.mem_ker, app_resG] at this
  rw [← germ_resG (I.subschemeι.preimage_mono e) z hzB, this, map_zero, map_zero]

theorem appLE_mem_ideal_comap (J : X.IdealSheafData) (g : W ⟶ X) (V : X.affineOpens) (A : W.affineOpens)
    (h : A.1 ≤ g ⁻¹ᵁ V.1) {a : Γ(X, V.1)} (ha : a ∈ J.ideal V) :
    (g.appLE V.1 A.1 h).hom a ∈ (J.comap g).ideal A :=
  (comap_le_iff J g _).1 le_rfl V a ha A h

theorem exists_affine_pair (g : W ⟶ X) (U : X.Opens) (A : W.Opens) (y : W) (hy : y ∈ A) (hU : g y ∈ U) :
    ∃ (V : X.affineOpens) (B : W.affineOpens), V.1 ≤ U ∧ B.1 ≤ A ∧ B.1 ≤ g ⁻¹ᵁ V.1 ∧ y ∈ B.1 := by
  obtain ⟨_, ⟨V, hV', rfl⟩, hyV, hV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hU U.isOpen
  obtain ⟨_, ⟨B, hB', rfl⟩, hyB, hB⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ A ⊓ g ⁻¹ᵁ V from ⟨hy, hyV⟩) (A ⊓ g ⁻¹ᵁ V).isOpen
  exact ⟨⟨V, hV'⟩, ⟨B, hB'⟩, hV, fun x hx => (hB hx).1, fun x hx => (hB hx).2, hyB⟩

theorem Generates.ideal_comap_top_le [IsAffine W] {J : X.IdealSheafData} {σ : Fin (m + 1) → L.Sec}
    (hJ : Generates J σ) (g : W ⟶ X) (k : L.ι) (h : ⊤ ≤ g ⁻¹ᵁ L.U k) :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top W⟩ ≤
      Ideal.span (Set.range fun j => (g.appLE (L.U k) ⊤ h).hom ((σ j).f k)) := by
  set K : Ideal Γ(W, ⊤) := Ideal.span (Set.range fun j => (g.appLE (L.U k) ⊤ h).hom ((σ j).f k)) with hK
  have key : J.comap g ≤ Scheme.IdealSheafData.ofIdealTop K := by
    refine (comap_le_iff _ _ _).2 fun U a ha A hA => mem_ideal_of_locally _ _ _ fun y hy => ?_
    obtain ⟨V, B, hV, hB, hBV, hyB⟩ := exists_affine_pair g (U.1 ⊓ L.U k) A.1 y hy ⟨hA hy, h trivial⟩
    refine ⟨B, hB, hyB, ?_⟩
    have h1 : resG X (hV.trans inf_le_left) a ∈ J.ideal V :=
      J.ideal_le_comap_ideal (U := V) (V := U) (hV.trans inf_le_left) ha
    rw [hJ.2 k V (hV.trans inf_le_right)] at h1
    have h2 : resG W hB (resG W hA ((g.app U.1).hom a)) =
        (g.appLE V.1 B.1 hBV).hom (resG X (hV.trans inf_le_left) a) := by
      rw [appLE_resG, resG_resG]
      rfl
    rw [h2]
    rw [← Ideal.mem_comap]
    refine Ideal.span_le.2 ?_ h1
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, appLE_resG, ← resG_appLE g h le_top]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)
  refine (key _).trans ?_
  simp

theorem Generates.generatesAlong_comap {J : X.IdealSheafData} {σ : Fin (m + 1) → L.Sec}
    (hJ : Generates J σ) (g : W ⟶ X) : GeneratesAlong (J.comap g) σ g := by
  refine ⟨by rw [← Scheme.Hom.preimage_iSup, hJ.1, Scheme.Hom.preimage_top], fun k A h => le_antisymm ?_ ?_⟩
  · intro s hs
    have : IsAffine A.1.toScheme := A.2
    have hA : ⊤ ≤ A.1.ι ⁻¹ᵁ A.1 := A.1.ι_preimage_self.ge
    have h1 := appLE_mem_ideal_comap (J.comap g) A.1.ι A ⟨⊤, isAffineOpen_top _⟩ hA hs
    rw [← Scheme.IdealSheafData.comap_comp] at h1
    have h2 := hJ.ideal_comap_top_le (A.1.ι ≫ g) k (hA.trans (A.1.ι.preimage_mono h)) h1
    have hb : Function.Bijective (A.1.ι.appLE A.1 ⊤ hA).hom := ConcreteCategory.bijective_of_isIso _
    rw [← Ideal.comap_map_of_bijective _ hb (I := Ideal.span _), Ideal.mem_comap, Ideal.map_span,
      ← Set.range_comp]
    convert h2 using 3
    funext j
    exact appLE_appLE _ _ h hA _
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    refine mem_ideal_of_locally _ _ _ fun y hy => ?_
    obtain ⟨V, B, hV, hB, hBV, hyB⟩ := exists_affine_pair g (L.U k) A.1 y hy (h hy)
    refine ⟨B, hB, hyB, ?_⟩
    have h1 : resG X hV ((σ j).f k) ∈ J.ideal V := by
      rw [hJ.2 k V hV]
      exact Ideal.subset_span ⟨j, rfl⟩
    have h2 := appLE_mem_ideal_comap J g V B hBV h1
    rw [appLE_resG] at h2
    rwa [resG_appLE]

theorem generatesAlong_comap_of_generates (X W : Scheme.{0}) (J : X.IdealSheafData) (L : LB X) (m : ℕ)
    (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (hJ : Generates J σ) : GeneratesAlong (J.comap g) σ g :=
  hJ.generatesAlong_comap g

end GlobalTheory.ProjBlowup
