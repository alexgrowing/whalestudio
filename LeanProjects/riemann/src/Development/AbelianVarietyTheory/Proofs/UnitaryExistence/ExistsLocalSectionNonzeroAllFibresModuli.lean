import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.PushLoc

open LBGerm PushInv ReciprocityTheory.ChartRestriction.G.Out

theorem exists_sec_lpow {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (T : Over S) {V : S.Opens}
    (hV : ∀ y, T.hom y ∈ V) {θ : ∀ i, Γ(A.left, A.hom ⁻¹ᵁ V ⊓ L.U i)} (hθ : θ ∈ secOn L (A.hom ⁻¹ᵁ V))
    (hne : ∀ y ∈ V, ∃ (g : A.left) (i : L.ι), A.hom g = y ∧ g ∈ A.left.basicOpen (θ i)) :
    ∃ s : LB.Sec (LPow A L (1 : ℕ) T), ∀ p : T.left, ∃ (q : (T ⊗ A).left) (i : (LPow A L (1 : ℕ) T).ι),
      (fst T A).left q = p ∧ q ∈ (T ⊗ A).left.basicOpen (s.f i) := by
  have hz : ∀ z, A.hom ((snd T A).left z) ∈ V := fun z => by
    rw [← Scheme.Hom.comp_apply, w_snd, Scheme.Hom.comp_apply]; exact hV _
  have le : ∀ j : Fin 1 → L.ι, (LPow A L (1 : ℕ) T).U j ≤ (snd T A).left ⁻¹ᵁ (A.hom ⁻¹ᵁ V ⊓ L.U (j 0)) :=
    fun j z h => ⟨hz z, (mem_chart A L T _ z j).1 h⟩
  have v : ∀ (j : Fin 1 → L.ι) z, z ∈ (LPow A L (1 : ℕ) T).U j →
      gs (𝟙 _) z _ (((snd T A).left.appLE _ _ (le j)).hom (θ (j 0))) =
        ((snd T A).left.stalkMap z).hom (gs (𝟙 _) _ _ (θ (j 0))) := fun j z h => by
    rw [gs_appLE _ _ _ (le j) (𝟙 _) z h, Category.id_comp]
    exact gs_stalkMap _ z (A.hom ⁻¹ᵁ V ⊓ L.U (j 0)) (le j h) _
  refine ⟨secOfGerm (fun j => ((snd T A).left.appLE _ _ (le j)).hom (θ (j 0)))
    fun z i j hi hj => by
      rw [v i z hi, v j z hj, gm_lpow A L T (𝟙 _) z i j hi hj, Category.id_comp,
        gs_secOn hθ _ (i 0) (j 0) (hz z) (le i hi).2 (le j hj).2, map_mul,
        ← gm_comp _ (𝟙 _) z (L.U (i 0) ⊓ L.U (j 0)) ⟨(le i hi).2, (le j hj).2⟩, Category.comp_id], fun p => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := hne (T.hom p) (hV p)
  obtain ⟨q, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback T.hom A.hom) p g hg.symm
  obtain rfl : (snd T A).left q = g := h₂
  refine ⟨q, fun _ => i, h₁, ?_⟩
  show q ∈ (T ⊗ A).left.basicOpen (((snd T A).left.appLE _ _ (le fun _ => i)).hom (θ i))
  rw [Scheme.basicOpen_appLE]
  exact ⟨(mem_chart A L T _ q _).2 (A.left.basicOpen_le _ hi).2, hi⟩

theorem exists_secNZ : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (z : Xo.X), ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (j : Sp R ⟶ Xo.X) (θ : LB.Sec (PPx j)), IsOpenImmersion j ∧ z ∈ Set.range j ∧ SecNZ j θ := by
  intro hS E _ _ _ H D l Xo z
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  obtain ⟨V, hV, θ, hθ, -, hne⟩ := pushInvertible hS Xo.X (Obj.toPolAV Xo.univ) z
  obtain ⟨B, j, hj, hp, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := Xo.X) (x := z) (U := V) hV
  have hN : IsLocallyNoetherian (Spec B) := isLocallyNoetherian_of_isOpenImmersion j
  obtain ⟨s, hs⟩ := exists_sec_lpow Xo.univ.t.G Xo.univ.t.PP.L (Over.mk j) (V := V) (fun y => hsub ⟨y, rfl⟩) hθ hne
  exact ⟨B, inferInstance, (isLocallyNoetherian_Spec (R := B)).1 hN, j, s, hj, hp, hs⟩

end GlobalTheory.PushLoc
