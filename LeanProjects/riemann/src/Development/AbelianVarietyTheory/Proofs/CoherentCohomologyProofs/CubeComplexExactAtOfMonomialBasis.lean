import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory

variable {ι : Type} (R : Type) [CommRing R]

def Cube.above (w : Finset ι) : Cube.{0} ι R :=
  Cube.mk (fun s => ModuleCat.of R (PLift (w ⊆ s) →₀ R))
    (fun h => Finsupp.lmapDomain R R fun x => ⟨x.down.trans h⟩)
    (fun _ _ => Finsupp.mapDomain_id)
    (fun _ _ _ => Finsupp.mapDomain_comp.symm)

theorem cubeComplex_above_exactAt [LinearOrder ι] [Fintype ι] (w : Finset ι) {p : ℕ}
    (hp : p ≠ Fintype.card ι) : (cubeComplex (Cube.above R w)).ExactAt p := by
  by_cases hw : w = Finset.univ
  · subst hw
    have : Subsingleton (Cube.Term (Cube.above R (Finset.univ : Finset ι)) p) := by
      refine ⟨fun x y => funext fun s => ?_⟩
      refine Finsupp.ext fun a => absurd ?_ hp
      rw [← s.2, Finset.univ_subset_iff.1 a.down, Finset.card_univ]
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ShortComplex.isZero_homology_of_isZero_X₂ _
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Cube.Term _ p)))
  · obtain ⟨i, hi⟩ : ∃ i, i ∉ w := by
      by_contra! h
      exact hw (Finset.eq_univ_iff_forall.2 h)
    refine cubeComplex_exactAt_of_bijective _ i (fun s _ => ?_) p
    refine ⟨Finsupp.mapDomain_injective fun _ _ _ => Subsingleton.elim _ _,
      Finsupp.mapDomain_surjective fun x => ⟨⟨?_⟩, Subsingleton.elim _ _⟩⟩
    exact (Finset.subset_insert_iff_of_notMem hi).1 x.down

variable {R}

def monomialCoord {κ : Type} (T : κ → Finset ι) {s : Finset ι} {M : Type} [AddCommGroup M]
    [Module R M] (b : Module.Basis {a : κ // T a ⊆ s} R M) :
    M ≃ₗ[R] ⨁ a, (PLift (T a ⊆ s) →₀ R) :=
  b.repr ≪≫ₗ Finsupp.domLCongr (Equiv.sigmaPLiftEquivSubtype fun a => T a ⊆ s).symm ≪≫ₗ
    sigmaFinsuppLequivDFinsupp R

theorem monomialCoord_basis {κ : Type} [DecidableEq κ] (T : κ → Finset ι) {s : Finset ι} {M : Type}
    [AddCommGroup M] [Module R M] (b : Module.Basis {a : κ // T a ⊆ s} R M)
    (a : {a : κ // T a ⊆ s}) :
    monomialCoord T b (b a) =
      DirectSum.lof R κ (fun a => PLift (T a ⊆ s) →₀ R) a.1 (Finsupp.single ⟨a.2⟩ 1) := by
  simp only [monomialCoord, LinearEquiv.trans_apply, Module.Basis.repr_self, Finsupp.domLCongr_single]
  exact sigmaFinsuppEquivDFinsupp_single _ _

theorem cubeComplex_exactAt_of_monomialBasis (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (κ : Type) (T : κ → Finset ι) (A : Cube.{0} ι R)
    (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s))
    (hb : ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}),
      Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩)
    (p : ℕ) (hp : p ≠ Fintype.card ι) : (cubeComplex A).ExactAt p := by
  classical
  let e : A ≅ Cube.directSum fun a => Cube.above R (T a) :=
    Cube.isoMk (fun s => monomialCoord T (b s)) fun {s t} h x => by
      have : (monomialCoord T (b t)).toLinearMap ∘ₗ Cube.res A h =
          (DirectSum.lmap fun a => Finsupp.lmapDomain R R
            fun x : PLift (T a ⊆ s) => (⟨x.down.trans h⟩ : PLift (T a ⊆ t))) ∘ₗ
            (monomialCoord T (b s)).toLinearMap := by
        refine (b s).ext fun a => ?_
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hb, monomialCoord_basis,
          DirectSum.lmap_lof, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      exact congr($this x)
  exact (exactAt_iff_of_quasiIsoAt ((cubeFunctor ι R).mapIso e).hom p).2
    ((cubeComplex_directSum_exactAt_iff _ p).2 fun a => cubeComplex_above_exactAt R (T a) hp)

end GlobalTheory
