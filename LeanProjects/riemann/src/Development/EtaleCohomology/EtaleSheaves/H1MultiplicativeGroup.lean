import Development.EtaleCohomology.EtaleSheaves.LeafKumCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.H1MultiplicativeGroup

structure Cov (A : Type) [CommRing A] where

  B : Type
  [cr : CommRing B]
  [alg : Algebra A B]
  [et : Algebra.Etale A B]
  [ff : Module.FaithfullyFlat A B]

attribute [instance] Cov.cr Cov.alg Cov.et Cov.ff

def kerH (A : Type) [CommRing A] (U : Cov A) : AddSubgroup (H ℤ (sp A) Gm 1) :=
  (pull ℤ (spMap (algebraMap A U.B)) Gm 1).ker

def kerP (A : Type) [CommRing A] (U : Cov A) : AddSubgroup (Additive (CommRing.Pic A)) :=
  (CommRing.Pic.mapAlgebra A U.B).toAdditive.ker

def LeafKill : Prop := Hyps → ∀ (A : Type) [CommRing A] (x : H ℤ (sp A) Gm 1), ∃ U : Cov A, x ∈ kerH A U

def LeafTriv : Prop := ∀ (A : Type) [CommRing A] (c : Additive (CommRing.Pic A)), ∃ U : Cov A, c ∈ kerP A U

def LeafRefine : Prop := ∀ (A : Type) [CommRing A] (U V : Cov A), ∃ W : Cov A,
  Nonempty (U.B →ₐ[A] W.B) ∧ Nonempty (V.B →ₐ[A] W.B)

def LeafDesc : Prop := Hyps → ∀ (A : Type) [CommRing A], ∃ e : ∀ U : Cov A, kerH A U ≃+ kerP A U,
  ∀ (U V : Cov A) (_g : U.B →ₐ[A] V.B) (x : H ℤ (sp A) Gm 1) (hU : x ∈ kerH A U) (hV : x ∈ kerH A V),
    (e U ⟨x, hU⟩ : Additive (CommRing.Pic A)) = e V ⟨x, hV⟩

theorem kerH_mono (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) : kerH A U ≤ kerH A V := by
  intro x hx
  simp only [kerH, AddMonoidHom.mem_ker] at hx ⊢
  have h : spMap (algebraMap A V.B) = spMap (g : U.B →+* V.B) ≫ spMap (algebraMap A U.B) := by
    simp only [spMap]
    rw [← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]
  rw [h, pull_comp, hx, map_zero]

theorem goal_of (hK : LeafKill) (hT : LeafTriv) (hR : LeafRefine) (hD : LeafDesc) : LateralTheory.E.LeafKumCut.EtaleFirstCohomologyMultiplicativeGroupPicard := by
  intro hH A _
  obtain ⟨e, he⟩ := hD hH A
  choose U hU using hK hH A
  have key : ∀ (x : H ℤ (sp A) Gm 1) (V : Cov A) (hV : x ∈ kerH A V),
      (e V ⟨x, hV⟩ : Additive (CommRing.Pic A)) = e (U x) ⟨x, hU x⟩ := by
    intro x V hV
    obtain ⟨W, ⟨g1⟩, ⟨g2⟩⟩ := hR A V (U x)
    rw [he V W g1 x hV (kerH_mono A V W g1 hV), he (U x) W g2 x (hU x) (kerH_mono A (U x) W g2 (hU x))]
  let f : H ℤ (sp A) Gm 1 →+ Additive (CommRing.Pic A) :=
    { toFun := fun x => e (U x) ⟨x, hU x⟩
      map_zero' := by
        have h0 : (⟨0, hU 0⟩ : kerH A (U 0)) = 0 := rfl
        rw [h0, map_zero]
        rfl
      map_add' := fun x y => by
        show (e (U (x + y)) ⟨x + y, hU _⟩ : Additive (CommRing.Pic A)) = e (U x) ⟨x, hU x⟩ + e (U y) ⟨y, hU y⟩
        obtain ⟨W, ⟨g1⟩, ⟨g2⟩⟩ := hR A (U x) (U y)
        have hx := kerH_mono A _ W g1 (hU x)
        have hy := kerH_mono A _ W g2 (hU y)
        rw [← key x W hx, ← key y W hy, ← key (x + y) W (add_mem hx hy), ← AddSubgroup.coe_add, ← map_add]
        rfl }
  refine ⟨AddEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro x y h
    obtain ⟨W, ⟨g1⟩, ⟨g2⟩⟩ := hR A (U x) (U y)
    have hx := kerH_mono A _ W g1 (hU x)
    have hy := kerH_mono A _ W g2 (hU y)
    have h' : e W ⟨x, hx⟩ = e W ⟨y, hy⟩ := Subtype.ext (by rw [key x W hx, key y W hy]; exact h)
    exact congrArg Subtype.val ((e W).injective h')
  · intro c
    obtain ⟨V, hV⟩ := hT A c
    obtain ⟨⟨x, hx⟩, hxe⟩ := (e V).surjective ⟨c, hV⟩
    refine ⟨x, ?_⟩
    show (e (U x) ⟨x, hU x⟩ : Additive (CommRing.Pic A)) = c
    rw [← key x V hx, hxe]

end LateralTheory.E.H1MultiplicativeGroup
