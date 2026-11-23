import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianModelFiniteExtCompleteDVR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrSplitExt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSemiAbelianModelAfterExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTraitThetaConstantsTwoLevelsIntegralStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegCmp

theorem prim_comp_of_isIntegral : ∀ {V W K : Type} [CommRing V] [CommRing W] [Field K] (f : V →+* W) (j : W →+* K), f.IsIntegral → ∀ {J : Type} (c : J → K), Prim j c → Prim (j.comp f) c := by
  intro V W K _ _ _ f j hf J c hc
  letI := f.toAlgebra
  letI := j.toAlgebra
  letI : Algebra V K := (j.comp f).toAlgebra
  haveI : IsScalarTower V W K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral V W := ⟨hf⟩
  have key : ∀ x : K, j.IsIntegralElem x → (j.comp f).IsIntegralElem x := fun x hx =>
    (isIntegral_trans (R := V) (A := W) x hx : IsIntegral V x)
  exact ⟨fun a => key _ (hc.1 a), let ⟨a, h0, h1⟩ := hc.2; ⟨a, h0, key _ h1⟩⟩

theorem exists_ext_fractionRing : ∀ (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (f : V →+* W) (fK : FractionRing V →+* FractionRing W), f.IsIntegral → (∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K), ∃ io' : FractionRing W →+* K, io'.comp fK = io := by
  intro V W _ _ _ _ f fK hf hfK K _ _ io
  letI := fK.toAlgebra
  letI := io.toAlgebra
  have hint : ∀ w : W, IsIntegral (FractionRing V) (algebraMap W (FractionRing W) w) := by
    intro w
    obtain ⟨p, hp, hpe⟩ := hf w
    refine ⟨p.map (algebraMap V (FractionRing V)), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap (FractionRing V) (FractionRing W)).comp (algebraMap V (FractionRing V)) =
        (algebraMap W (FractionRing W)).comp f := by
      ext a; exact hfK a
    rw [this, ← Polynomial.hom_eval₂, hpe, map_zero]
  have hmem : ∀ w : W, algebraMap W (FractionRing W) w ∈ algebraicClosure (FractionRing V) (FractionRing W) :=
    fun w => mem_algebraicClosure_iff.2 (hint w).isAlgebraic
  haveI : Algebra.IsAlgebraic (FractionRing V) (FractionRing W) := by
    constructor
    intro z
    rw [← mem_algebraicClosure_iff]
    obtain ⟨⟨w, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors W) z
    simp only [IsFractionRing.mk'_eq_div]
    exact div_mem (hmem w) (hmem s)
  refine ⟨(IsAlgClosed.lift : FractionRing W →ₐ[FractionRing V] K).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : FractionRing W →ₐ[FractionRing V] K).commutes x

theorem theta_two_levels_prim : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (y : Sp (FractionRing V) ⟶ S) (P : PolAV (Sp (FractionRing V))) (α : P.A.left ⟶ G.left), IsGrpPullback P.A G y α → LBIso P.L (L.pull α) → (letI := P.isAb.comm; HypS P.A P.L) → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : V) → Odd m' → 3 ≤ m' → IsUnit (m' : V) → HasTh₂ G L ρ m m' (spMap io ≫ y) d d' → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d' b / a) := by

  intro S G _ _ L ρ hL hρ V _ _ _ hV y P α hα hLα hS K _ _ io m m' N N' d d' hm hm3 hmu hm' hm3' hmu' hth
  letI := P.isAb.comm
  obtain ⟨ρP, hρP⟩ := P.rigid
  have h1 : HasTh₂ P.A P.L ρP m m' (spMap io) d d' :=
    (ThMove.hasTh₂_move S G L ρ hL hρ _ P.A P.L ρP y α P.isLB hρP hα hLα m m' N N' K (spMap io) d d').2 hth
  obtain ⟨W, _, _, _, _, f, fK, hWc, hfi, hfinj, hfK, A, β, hβ, hLβ, G', _, _, gen, hG', hgen, E, hE⟩ := GlobalTheory.T.exists_split_semiAbelian_model_after_extension V hV P
  letI := A.isAb.comm
  have hSA : HypS A.A A.L :=
    SymBaseChange.hypS_baseChange _ _ P.A A.A (spMap fK) β P.L A.L P.isLB A.isLB hβ hLβ hS
  obtain ⟨D, U, -⟩ := GlobalTheory.ZH.thmU_and_uTors.1 W hWc A G' hG' ⟨E, hE⟩ hSA gen hgen
  obtain ⟨io', hio'⟩ := exists_ext_fractionRing V W f fK hfi hfK K io
  obtain ⟨ρA, hρA⟩ := A.rigid
  have hx : spMap io' ≫ spMap fK = spMap io := by
    rw [← hio']; simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h2 : HasTh₂ A.A A.L ρA m m' (spMap io') d d' := by
    refine (ThMove.hasTh₂_move _ P.A P.L ρP P.isLB hρP _ A.A A.L ρA (spMap fK) β A.isLB hρA hβ hLβ
      m m' N N' K (spMap io') d d').2 ?_
    rw [hx]; exact h1
  have hmuW : IsUnit (m : W) := by simpa using hmu.map f
  have hmuW' : IsUnit (m' : W) := by simpa using hmu'.map f
  obtain ⟨a, ha, hp, hp'⟩ := GlobalTheory.T.uniformised_trait_theta_constants_two_levels_integral W hWc D A G' hG' U ρA hρA K io' m m' N N' d d' hm hm3 hmuW hm' hm3' hmuW' h2
  have hcomp : (io'.comp (algebraMap W (FractionRing W))).comp f = io.comp (algebraMap V (FractionRing V)) := by
    ext x; simp [← hfK, ← hio']
  refine ⟨a, ha, ?_, ?_⟩
  · rw [← hcomp]; exact prim_comp_of_isIntegral f _ hfi _ hp
  · rw [← hcomp]; exact prim_comp_of_isIntegral f _ hfi _ hp'

end GlobalTheory.SiegCmp

end
