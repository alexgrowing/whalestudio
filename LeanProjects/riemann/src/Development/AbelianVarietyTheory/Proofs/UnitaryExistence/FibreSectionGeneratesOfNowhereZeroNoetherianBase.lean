import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.FrameGenerator

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem scal_eq_constFn {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (i : (PPx x).ι) :
    scal x a i = constFn (fst (Over.mk x) Xo.univ.t.G).left _ a := rfl

theorem scal_one' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x (1 : S) i = 1 := by
  rw [scal_eq_constFn]
  exact (congrArg _ (map_one _)).trans (map_one _)

theorem isPullback_gx {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) :
    IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left Xo.univ.t.G.hom x :=
  (IsPullback.of_hasPullback _ _).flip

theorem secGen_of_secNZ (hS : Out.SecBaseChangeSt) {T : Type} [CommRing T] (x : Sp T ⟶ Xo.X)
    (θ : LB.Sec (PPx x)) (h : SecNZ x θ) : SecGen x θ := by
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  intro s
  have hw : LBIso (PPx x) (Xo.univ.t.PP.L.pull (snd (Over.mk x) Xo.univ.t.G).left) :=
    exists_iso_linComb Xo.univ.t.PP.isLB _ _ fun _ _ _ => by simp
  refine SectionBaseChange.generates hS (Obj.toPolAV Xo.univ) (isPullback_gx x)
    (DVR.linComb_isLB _ Xo.univ.t.PP.isLB _ _) hw θ (fun y => ?_) s
  obtain ⟨q, i, hq, hi⟩ := h y
  exact ⟨q, hq, TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩⟩

theorem secNZ_of_secBC {R T : Type} [CommRing R] [CommRing T] {ψ : R →+* T} {j : Sp R ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    {θ : LB.Sec (PPx j)} {θ' : LB.Sec (PPx x')} (h : SecNZ j θ) (hx : x' = spMap ψ ≫ j)
    (hb : SecBC ψ 1 j x' θ θ') : SecNZ x' θ' := by
  obtain ⟨pm, h₁, h₂, h₃⟩ := hb
  have sq : IsPullback pm (fst (Over.mk x') Xo.univ.t.G).left (fst (Over.mk j) Xo.univ.t.G).left (spMap ψ) :=
    IsPullback.of_right (by rw [h₁, ← hx]; exact isPullback_gx x') h₂ (isPullback_gx j)
  intro p
  obtain ⟨q, i, hq, hi⟩ := h (spMap ψ p)
  obtain ⟨q', rfl, e₂⟩ := Scheme.exists_preimage_of_isPullback sq q p hq
  have le : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx j).U i := fun y hy => Set.mem_iInter.2 fun k => by
    have : (snd (Over.mk x') Xo.univ.t.G).left y ∈ Xo.univ.t.PP.L.U (i k) := Set.mem_iInter.1 hy k
    rw [← h₁] at this; exact this
  have mem : q' ∈ (PPx x').U i := Set.mem_iInter.2 fun k => by
    have : (snd (Over.mk j) Xo.univ.t.G).left (pm q') ∈ Xo.univ.t.PP.L.U (i k) :=
      Set.mem_iInter.1 ((Gx j).basicOpen_le _ hi) k
    show (snd (Over.mk x') Xo.univ.t.G).left q' ∈ Xo.univ.t.PP.L.U (i k)
    rw [← h₁]; exact this
  refine ⟨q', i, e₂, ?_⟩
  rw [← h₃ i le, scal_one', _root_.one_mul, Scheme.basicOpen_appLE]
  exact ⟨mem, hi⟩

theorem secGen_of_secNZ_baseChange : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (R : Type) [CommRing R] [IsNoetherianRing R] (j : Sp R ⟶ Xo.X) (θ : LB.Sec (PPx j)), SecNZ j θ → ∀ (T : Type) [CommRing T] (ψ : R →+* T) (x' : Sp T ⟶ Xo.X) (θ' : LB.Sec (PPx x')), x' = spMap ψ ≫ j → SecBC ψ 1 j x' θ θ' → SecGen x' θ' :=
  fun hS _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ _ x' θ' hx hb => secGen_of_secNZ hS x' θ' (secNZ_of_secBC h hx hb)

end GlobalTheory.FrameGenerator
