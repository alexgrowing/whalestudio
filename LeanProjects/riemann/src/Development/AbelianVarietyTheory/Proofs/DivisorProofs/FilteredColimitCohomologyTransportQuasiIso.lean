import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem hom_d_apply {C D : AbCx} (φ : C ⟶ D) (i j : ℤ) (x : C.X i) :
    φ.f j (C.d i j x) = D.d i j (φ.f i x) := by
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, HomologicalComplex.Hom.comm]

theorem nat_f_apply {N M : CommRingCat.{0} ⥤ AbCx} (ε : N ⟶ M) {A B : CommRingCat.{0}} (g : A ⟶ B) (n : ℤ)
    (x : (N.obj A).X n) : (ε.app B).f n ((N.map g).f n x) = (M.map g).f n ((ε.app A).f n x) := by
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f, ε.naturality]

end GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contH_transport_quasiIso : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M), (∀ A, SurjH (ε.app A) ∧ InjH (ε.app A)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  intro N M ε hε hN J _ _ D c hc n
  obtain ⟨hN1, hN2⟩ := hN J D c hc n
  have nat : ∀ (j : J) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      (ε.app c.pt).f m ((N.map (c.ι.app j)).f m x) = (M.map (c.ι.app j)).f m ((ε.app (D.obj j)).f m x) :=
    fun j m x => nat_f_apply ε (B := c.pt) (c.ι.app j) m x
  have dN : ∀ (j : J) (m m' : ℤ) (x : ((N).obj (D.obj j)).X m),
      (N.map (c.ι.app j)).f m' (((N).obj (D.obj j)).d m m' x) = ((N).obj c.pt).d m m' ((N.map (c.ι.app j)).f m x) :=
    fun j m m' x => hom_d_apply (D := (N).obj c.pt) (N.map (c.ι.app j)) m m' x
  have dM : ∀ (j : J) (m m' : ℤ) (x : ((M).obj (D.obj j)).X m),
      (M.map (c.ι.app j)).f m' (((M).obj (D.obj j)).d m m' x) = ((M).obj c.pt).d m m' ((M.map (c.ι.app j)).f m x) :=
    fun j m m' x => hom_d_apply (D := (M).obj c.pt) (M.map (c.ι.app j)) m m' x
  refine ⟨fun z hz => ?_, fun j w hw ⟨y, hy⟩ => ?_⟩
  · obtain ⟨c', y1, hc', h1⟩ := (hε c.pt).1 n z hz
    obtain ⟨j, w, y2, hw, h2⟩ := hN1 c' hc'
    refine ⟨j, (ε.app (D.obj j)).f n w, y1 + (ε.app c.pt).f (n - 1) y2, ?_, ?_⟩
    · rw [← hom_d_apply, hw, map_zero]
    · rw [← nat, h2, map_add, h1, map_add, hom_d_apply]
      abel
  · obtain ⟨c1, y1, hc1, h1⟩ := (hε (D.obj j)).1 n w hw
    have hcz : ((N).obj c.pt).d n (n + 1) ((N.map (c.ι.app j)).f n c1) = 0 := by
      rw [← dN, hc1, map_zero]
    obtain ⟨b, hb⟩ := (hε c.pt).2 n _ hcz ⟨y + (show ((M).obj c.pt).X (n - 1) from (M.map (c.ι.app j)).f (n - 1) y1), by
      rw [nat, h1, map_add, hy, map_add, dM]⟩
    obtain ⟨k, f, y2, h2⟩ := hN2 j c1 hc1 ⟨b, hb.symm⟩
    refine ⟨k, f, (ε.app (D.obj k)).f (n - 1) y2 - (M.map (D.map f)).f (n - 1) y1, ?_⟩
    have e1 : w = (ε.app (D.obj j)).f n c1 - ((M).obj (D.obj j)).d (n - 1) n y1 := by
      rw [h1]; abel
    rw [e1, map_sub, map_sub, ← nat_f_apply, h2, hom_d_apply, hom_d_apply]

end GlobalTheory.EtC
