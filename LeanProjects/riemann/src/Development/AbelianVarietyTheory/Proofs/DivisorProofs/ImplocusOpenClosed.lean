import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section
namespace GlobalTheory.LevCover

theorem implocus_open_closed : ∀ (Y : Scheme.{0}) (Z : Over Y) (P Q : ∀ T : Over Y, (T ⟶ Z) → Prop), IsFinite Z.hom → Etale Z.hom → GlobalTheory.LevCover.ClopenCond Z P → GlobalTheory.LevCover.ClopenCond Z Q → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ z : T ⟶ Z, P T z → Q T z) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔ ∀ z : Over.mk x ⟶ Z, P _ z → Q _ z := by
  intro Y Z P Q hfin het hP hQ
  obtain ⟨U, hUc, HU⟩ := hP
  obtain ⟨V, hVc, HV⟩ := hQ
  let B : Set Z.left := (U : Set Z.left) \ V
  have hBo : IsOpen B := U.isOpen.sdiff hVc
  have hBc : IsClosed B := hUc.sdiff V.isOpen
  have c1 : ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ (Z.hom.base '' B)ᶜ ↔
      ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ z : T ⟶ Z, P T z → Q T z := by
    intro Tb t
    constructor
    · intro hW T σ hσ z hPz
      rw [HU] at hPz
      rw [HV]
      rintro _ ⟨w, rfl⟩
      by_contra hv
      have hb : z.left.base w ∈ B := ⟨hPz ⟨w, rfl⟩, hv⟩
      apply hW ⟨σ.base w, rfl⟩
      refine ⟨_, hb, ?_⟩
      rw [← Scheme.Hom.comp_apply, Over.w z, ← hσ, Scheme.Hom.comp_apply]
    · intro H
      rintro _ ⟨τ, rfl⟩ ⟨u, hu, hτ⟩
      obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback τ u hτ.symm
      let O : (pullback t Z.hom).Opens := (pullback.snd t Z.hom) ⁻¹ᵁ ⟨B, hBo⟩
      let T : Over Y := Over.mk (O.ι ≫ pullback.fst t Z.hom ≫ t)
      let z : T ⟶ Z := Over.homMk (O.ι ≫ pullback.snd t Z.hom) (by simp [T, pullback.condition])
      have hmem : ∀ w, O.ι.base w ∈ (O : Set _) := fun w => by
        rw [← Scheme.Opens.range_ι O]; exact ⟨w, rfl⟩
      have hPz : P T z := by
        rw [HU]
        rintro _ ⟨w, rfl⟩
        exact (hmem w).1
      have hQz := H T (O.ι ≫ pullback.fst t Z.hom) (Category.assoc _ _ _) z hPz
      rw [HV] at hQz
      have hpO : p ∈ Set.range O.ι.base := by
        rw [Scheme.Opens.range_ι O]
        show (pullback.snd t Z.hom).base p ∈ B
        rw [hp2]; exact hu
      obtain ⟨w, hw⟩ := hpO
      apply hu.2
      have := hQz ⟨w, rfl⟩
      simpa [z, Scheme.Hom.comp_apply, hw, hp2] using this
  refine ⟨(Z.hom.base '' B)ᶜ, (Z.hom.isClosedMap _ hBc).isOpen_compl,
    (Z.hom.isOpenMap _ hBo).isClosed_compl, c1, ?_⟩
  intro k _ _ x
  constructor
  · intro hW z hPz
    exact (c1 (Sp k) x).1 hW (Over.mk x) (𝟙 _) (Category.id_comp _) z hPz
  · intro H
    rintro _ ⟨s, rfl⟩ ⟨u, hu, hs⟩
    let Bo : Z.left.Opens := ⟨B, hBo⟩
    haveI : IsClosedImmersion Bo.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hBc)
    have huB : u ∈ Set.range Bo.ι.base := by rw [Scheme.Opens.range_ι]; exact hu
    obtain ⟨v, hv⟩ := huB
    obtain ⟨w, hw⟩ := GlobalTheory.LevCover.exists_lift_geom (Bo.ι ≫ Z.hom) x (by
      rintro _ ⟨s', rfl⟩
      refine ⟨v, ?_⟩
      rw [Subsingleton.elim s' s, Scheme.Hom.comp_apply, hv, hs])
    let z : Over.mk x ⟶ Z := Over.homMk (w ≫ Bo.ι) (by simpa using hw)
    have hPz : P _ z := by
      rw [HU]
      rintro _ ⟨y, rfl⟩
      have : (Bo.ι.base (w.base y)) ∈ (Bo : Set Z.left) := by
        rw [← Scheme.Opens.range_ι Bo]; exact ⟨_, rfl⟩
      exact this.1
    have hQz := H z hPz
    rw [HV] at hQz
    let y0 : Sp k := (⊥ : PrimeSpectrum k)
    have h1 : (Bo.ι.base (w.base y0)) ∈ (Bo : Set Z.left) := by
      rw [← Scheme.Opens.range_ι Bo]; exact ⟨_, rfl⟩
    exact h1.2 (hQz ⟨y0, rfl⟩)

end GlobalTheory.LevCover
