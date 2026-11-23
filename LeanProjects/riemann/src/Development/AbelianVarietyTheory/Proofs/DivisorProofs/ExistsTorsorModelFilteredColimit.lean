import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodTorsorModelOfFilteredColimitStatement

open IsLocalRing Polynomial CategoryTheory Limits

namespace GlobalTheory.TorsorColimElem

theorem exists_torsor_model_of_elements : ∀ (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Type) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j),
    (∀ i (h : i ≤ i), f i i h = RingHom.id (R i)) →
    (∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk)) →
    ∀ (B : Type) [CommRing B] (g : ∀ i, R i →+* B),
    (∀ i j (h : i ≤ j), (g j).comp (f i j h) = g i) →
    (∀ b : B, ∃ i x, g i x = b) →
    (∀ i x, g i x = 0 → ∃ j, ∃ h : i ≤ j, f i j h x = 0) →
    ∀ (q : ℕ), 0 < q →
    ∀ (D : Type) [CommRing D] [Algebra B D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ i, letI : Algebra (R i) B := (g i).toAlgebra
      ∃ (Di : Type) (_ : CommRing Di) (_ : Algebra (R i) Di)
        (acti : Multiplicative (ZMod q) →* (Di ≃ₐ[R i] Di)),
        GlobalTheory.KeyOriginCut.IsZTorsor (R i) Di q acti ∧ Nonempty (TensorProduct (R i) B Di ≃ₐ[B] D) := by
  intro ι _ _ _ R _ f hid hcomp B _ g hcompat hsurj hinj q hq D _ _ act hT
  let F : ι ⥤ CommRingCat.{0} :=
    { obj := fun i => CommRingCat.of (R i)
      map := fun {i j} h => CommRingCat.ofHom (f i j h.le)
      map_id := fun i => by
        ext x
        simp [hid]
      map_comp := fun {i j k} a b => by
        ext x
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
          Function.comp_apply]
        exact (RingHom.congr_fun (hcomp i j k a.le b.le) x).symm }
  let c : Cocone F :=
    { pt := CommRingCat.of B
      ι := { app := fun i => CommRingCat.ofHom (g i)
             naturality := fun i j h => by
               ext x
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
                 CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, F]
               exact RingHom.congr_fun (hcompat i j h.le) x } }
  have hc : IsColimit c := by
    haveI : ReflectsColimit F (forget CommRingCat) :=
      reflectsColimit_of_reflectsIsomorphisms F (forget CommRingCat)
    apply isColimitOfReflects (forget CommRingCat)
    apply Types.FilteredColimit.isColimitOf
    · intro x
      obtain ⟨i, y, hy⟩ := hsurj x
      exact ⟨i, y, hy.symm⟩
    · intro i j x y hxy
      have hxy' : g i x = g j y := hxy
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
      have h0 : g k (f i k hik x - f j k hjk y) = 0 := by
        have e1 : g k (f i k hik x) = g i x := by rw [← hcompat i k hik]; rfl
        have e2 : g k (f j k hjk y) = g j y := by rw [← hcompat j k hjk]; rfl
        rw [map_sub, e1, e2, hxy', sub_self]
      obtain ⟨l, hkl, hl⟩ := hinj k _ h0
      refine ⟨l, homOfLE (hik.trans hkl), homOfLE (hjk.trans hkl), ?_⟩
      change f i l _ x = f j l _ y
      rw [map_sub, sub_eq_zero] at hl
      rw [← hcomp i k l hik hkl, ← hcomp j k l hjk hkl]
      exact hl
  have hT' : GlobalTheory.LocAcyc.IsZModTorsor B D q act := hT
  obtain ⟨j, Dj, i1, i2, actj, hTj, ⟨e⟩⟩ :=
    @GlobalTheory.T.exists_zmodTorsor_model_of_filtered_colimit ι _ _ F c hc q hq D _ ‹Algebra B D› act hT'
  exact ⟨j, Dj, i1, i2, actj, hTj, ⟨e⟩⟩

end GlobalTheory.TorsorColimElem
