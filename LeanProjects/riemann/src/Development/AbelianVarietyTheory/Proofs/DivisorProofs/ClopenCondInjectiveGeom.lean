import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem clopenCond_injective_geom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), (∀ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = 1 → y ∈ wSub D w0 r) := by
  intro p _ D R _ b N w0 r hw S _ s o K κ hKf hKe hκ hrep Z et hZf hZe hadd hlin hvan
  have hkill : ∀ y, ∀ c ∈ w0 ^ r, et y ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro y c hc
    rw [← hlin]
    exact hvan _ (Submodule.subset_span ⟨c, hc, y, rfl⟩)
  have h0 : et 0 = 1 := hvan 0 (Submodule.zero_mem _)
  have hE : ∀ y, GlobalTheory.LevCover.ClopenCond Z fun _ h => h ≫ et y = 1 := by
    intro y
    obtain ⟨u, hu, -⟩ := hrep Z (et y) (hkill y)
    obtain ⟨u0, hu0, -⟩ := hrep Z (et 0) (hkill 0)
    refine (GlobalTheory.LevCover.clopenCond_eq u u0).congr fun T' h => ⟨fun H => ?_, fun H => ?_⟩
    · have hk : ∀ c ∈ w0 ^ r, (h ≫ et y) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => by
        rw [Category.assoc, hkill y c hc, MonObj.comp_one]
      refine (hrep T' (h ≫ et y) hk).unique ?_ ?_
      · rw [Category.assoc, hu]
      · rw [Category.assoc, hu0, h0, MonObj.comp_one, H]
    · rw [← hu, ← Category.assoc, H, Category.assoc, hu0, h0, MonObj.comp_one]
  have hP : ∀ y, GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k]
      (x : Sp k ⟶ T'.left),
      (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = 1 → y ∈ wSub D w0 r := by
    intro y
    by_cases hy : y ∈ wSub D w0 r
    · exact ⟨⊤, isClosed_univ, fun T' h => ⟨fun _ => by simp, fun _ _ _ _ _ _ => hy⟩⟩
    · obtain ⟨U, hU, H⟩ := hE y
      refine ⟨⟨(U : Set Z.left)ᶜ, hU.isOpen_compl⟩, U.isOpen.isClosed_compl, fun T' h =>
        ⟨fun P => ?_, fun hsub k _ _ x hx => ?_⟩⟩
      · rintro _ ⟨t, rfl⟩ ht
        obtain ⟨k, _, _, a, ha⟩ := FinEt.exists_algClosed_point T'.left t
        apply hy
        refine P k a ?_
        rw [← Category.assoc]
        refine (H _ _).2 ?_
        rintro _ ⟨q, rfl⟩
        have haq : a q = t := (ha ▸ Set.mem_range_self q : a q ∈ ({t} : Set T'.left))
        simp only [Over.comp_left, Over.homMk_left, Scheme.Hom.comp_apply, haq]
        exact ht
      · rw [← Category.assoc] at hx
        have hr := (H _ _).1 hx
        obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
        exact (hsub ⟨x q, rfl⟩ (hr ⟨q, by simp⟩)).elim
  haveI := D.freeLa
  haveI := D.finLa
  have hpos : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos r
  obtain ⟨κ', _, q, hq⟩ := GlobalTheory.LevCover.exists_finite_mod D.La hpos
  have hpr : ∀ c : D.La, (p ^ r) • c ∈ wSub D w0 r := by
    intro c
    refine Submodule.subset_span ⟨(p : 𝓞 D.F) ^ r, Ideal.pow_mem_pow hw.2.1 r, c, ?_⟩
    rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  refine (GlobalTheory.LevCover.ClopenCond.forall_of_finite q hP ?_).congr fun T' h => ?_
  · intro i j hij T' h Pi k _ _ x hx
    obtain ⟨c, rfl⟩ := hq i j hij
    have he : et (i + p ^ r • c) = et i := by rw [hadd, hvan _ (hpr c), _root_.mul_one]
    rw [he] at hx
    exact (wSub D w0 r).add_mem (Pi k x hx) (hpr c)
  · exact ⟨fun H y k _ _ x => H k x y, fun H k _ _ x y => H y k x⟩

end GlobalTheory.UPel.HT.EtLev
