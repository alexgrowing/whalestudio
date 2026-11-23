import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem epi_spMap_field (Ω L : Type) [Field Ω] [Field L] (iL : Ω →+* L) : Epi (spMap iL) := by
  letI : Algebra Ω L := iL.toAlgebra
  have hf : Flat (spMap iL) := by
    rw [show spMap iL = Spec.map (CommRingCat.ofHom iL) from rfl]
    rw [Flat.SpecMap_iff]
    exact (RingHom.flat_algebraMap_iff).2 inferInstance
  have hs : Surjective (spMap iL) := ⟨fun z =>
    ⟨(default : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem splitTors_of_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    (Y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (x : Sp R ⟶ Y.X)
    (y : Sp (FractionRing R) ⟶ Xo.XF c), spMap (algebraMap R (FractionRing R)) ≫ x = y ≫ Y.j →
    ∀ N : ℕ, N ∣ l.A → GlobalTheory.LineNorm.SplitTors Y.t x N := by
  intro E _ _ _ H Dw l Xo c O _ β Y R _ _ x y hxy N hN Ω _ io w hw
  let L := AlgebraicClosure Ω
  let iL : Ω →+* L := algebraMap Ω L
  let xL : Sp L ⟶ Xo.XF c := spMap (iL.comp io) ≫ y
  obtain ⟨β', hβ⟩ : ∃ β' : KA l →+* L,
      xL ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β' :=
    ⟨(Spec.preimage (xL ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)).hom,
      (Spec.map_preimage _).symm⟩
  obtain ⟨-, I, -, hA, -⟩ := Y.oF.geom L xL β' hβ
  have hNpos : 0 < N := Nat.pos_of_dvd_of_pos hN l.A_pos
  obtain ⟨m, hm⟩ := hN
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; have := l.A_pos; omega
    · exact h
  have hU : xL ≫ Y.j = spMap iL ≫ spMap (io.comp (algebraMap R (FractionRing R))) ≫ x := by
    show (spMap (iL.comp io) ≫ y) ≫ Y.j = _
    rw [Category.assoc, ← hxy, ← spMap_comp' io iL, ← spMap_comp' (algebraMap R _) io]
    simp only [Category.assoc]
  let U : Over.mk (xL ≫ Y.j) ⟶ Over.mk (spMap (io.comp (algebraMap R (FractionRing R))) ≫ x) :=
    Over.homMk (spMap iL) hU.symm
  let wL : Over.mk (xL ≫ Y.j) ⟶ Y.t.G := ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom U w
  have hwL : wL ^ N = 1 := by
    show ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom U w ^ N = 1
    rw [← map_pow, hw, map_one]
  have h := Y.m.cart
  let P := pushHom h (Over.mk xL)
  let v : Over.mk xL ⟶ Y.oF.t.G :=
    Over.homMk (h.1.lift wL.left xL (Over.w wL)) (h.1.lift_snd _ _ _)
  have hvφ : v.left ≫ Y.m.φ = wL.left := h.1.lift_fst _ _ _
  have hPinj : Function.Injective P := by
    intro p q hpq
    have e : p.left ≫ Y.m.φ = q.left ≫ Y.m.φ := congrArg (fun V => V.left) hpq
    apply Over.OverMorphism.ext
    exact h.1.hom_ext e ((Over.w p).trans (Over.w q).symm)
  have hPv : P v = wL := Over.OverMorphism.ext hvφ
  have hvN : v ^ N = 1 := hPinj (by rw [map_pow, hPv, map_one]; exact hwL)
  obtain ⟨a, ha⟩ := (I.onto N hNpos v).1 hvN
  have hve : v = ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (SemiCartesianMonoidalCategory.toUnit (Over.mk xL)) (Y.oF.etaA a ^ m) := by
    rw [map_pow]
    show v = (SemiCartesianMonoidalCategory.toUnit (Over.mk xL) ≫ Y.oF.etaA a) ^ m
    rw [hA a, hm, I.tower N m hNpos hmpos a, ha]
  have e1 : v.left = xL ≫ (Y.oF.etaA a ^ m).left := by
    have e0 : (SemiCartesianMonoidalCategory.toUnit (Over.mk xL)).left = xL := by
      simpa using Over.w (SemiCartesianMonoidalCategory.toUnit (Over.mk xL))
    rw [hve]
    show (SemiCartesianMonoidalCategory.toUnit (Over.mk xL) ≫ (Y.oF.etaA a ^ m)).left = _
    rw [Over.comp_left, e0]
  refine ⟨y ≫ (Y.oF.etaA a ^ m).left ≫ Y.m.φ, ?_⟩
  haveI := epi_spMap_field Ω L iL
  rw [← cancel_epi (spMap iL)]
  have e2 : wL.left = spMap iL ≫ w.left := rfl
  rw [← e2, ← hvφ, e1]
  show _ = ((spMap (iL.comp io) ≫ y) ≫ _) ≫ _
  rw [← spMap_comp' io iL]
  simp only [Category.assoc]

end GlobalTheory.HTLine
