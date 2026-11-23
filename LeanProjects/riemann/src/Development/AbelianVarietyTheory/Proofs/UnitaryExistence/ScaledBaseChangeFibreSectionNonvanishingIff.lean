import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem exists_mem_basicOpen_iff_of_isPullback {P X Y Z : Scheme.{0}} {pm : P ⟶ X} {g' : P ⟶ Y} {g : X ⟶ Z}
    {f : Y ⟶ Z} (hP : IsPullback pm g' g f) {J : Type} (U : J → X.Opens) (U' : J → P.Opens)
    (hU : ∀ i, U' i = pm ⁻¹ᵁ U i) (s : ∀ i, Γ(X, U i)) (s' : ∀ i, Γ(P, U' i))
    (hs : ∀ i, (pm.appLE _ _ (hU i).le).hom (s i) = s' i) (p' : Y) :
    (∃ (q : P) (i : J), g' q = p' ∧ q ∈ P.basicOpen (s' i)) ↔
      ∃ (q : X) (i : J), g q = f p' ∧ q ∈ X.basicOpen (s i) := by
  have key : ∀ (i : J) (q : P), q ∈ P.basicOpen (s' i) ↔ pm q ∈ X.basicOpen (s i) := by
    intro i q
    have e := Scheme.basicOpen_appLE pm (U' i) (U i) (hU i).le (s i)
    have e' : P.basicOpen (s' i) = U' i ⊓ pm ⁻¹ᵁ (X.basicOpen (s i)) := by
      rw [← hs i]; exact e
    rw [e']
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rw [hU i]
    exact X.basicOpen_le (s i) h
  constructor
  · rintro ⟨q, i, rfl, hq⟩
    refine ⟨pm q, i, ?_, (key i q).1 hq⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hP.w]
  · rintro ⟨q, i, hq, hq'⟩
    obtain ⟨z, rfl, hz⟩ := Scheme.exists_preimage_of_isPullback hP q p' hq
    exact ⟨z, i, hz, (key i z).2 hq'⟩

theorem secBC_nonvanishing_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s s', SecBC φ 1 x x' s s' → ∀ p' : Sp T, (∃ (q : Gx x') (i : (PPx x').ι), Formalism.L2.PjFree.gxSnd x' q = p' ∧ q ∈ (Gx x').basicOpen (s'.f i)) ↔ ∃ (q : Gx x) (i : (PPx x).ι), Formalism.L2.PjFree.gxSnd x q = spMap φ p' ∧ q ∈ (Gx x).basicOpen (s.f i) := by
  intro E _ _ _ H Dw l Xo S T _ _ φ x x' hx s s' hbc p'
  obtain ⟨pm, h1, h2, h3⟩ := hbc
  have hA : IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left
      Xo.univ.t.G.hom x := (IsPullback.of_hasPullback x Xo.univ.t.G.hom).flip
  have hB : IsPullback (snd (Over.mk x') Xo.univ.t.G).left (fst (Over.mk x') Xo.univ.t.G).left
      Xo.univ.t.G.hom x' := (IsPullback.of_hasPullback x' Xo.univ.t.G.hom).flip
  have hP : IsPullback pm (fst (Over.mk x') Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left (spMap φ) := by
    refine IsPullback.of_right ?_ h2 hA
    rw [h1]
    exact hx ▸ hB
  have hU : ∀ i : Fin 1 → Xo.univ.t.PP.L.ι, (PPx x').U i = pm ⁻¹ᵁ (PPx x).U i := by
    intro i
    ext y
    change y ∈ ⋂ k : Fin 1, (snd (Over.mk x') Xo.univ.t.G).left ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) ↔
      pm y ∈ ⋂ k : Fin 1, (snd (Over.mk x) Xo.univ.t.G).left ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
    rw [← h1]
    simp only [Set.mem_iInter, Set.mem_preimage, Scheme.Hom.comp_apply]
  have h1' : ∀ i, scal x 1 i = 1 := fun i => by
    simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]
  refine exists_mem_basicOpen_iff_of_isPullback hP (PPx x).U (PPx x').U hU s.f s'.f (fun i => ?_) p'
  have := h3 i (hU i).le
  rwa [h1' i, _root_.one_mul] at this

end GlobalTheory.Frames
