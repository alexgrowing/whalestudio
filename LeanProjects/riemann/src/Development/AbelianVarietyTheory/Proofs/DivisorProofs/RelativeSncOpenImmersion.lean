import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenPullOpenImmersionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem relSnc_pull_of_isOpenImmersion : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R) (e : Y ⟶ X) [IsOpenImmersion e] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), RelSnc f d L σ → RelSnc (e ≫ f) d (fun i => (L i).pull e) (fun i => Cartier.secPull (σ i) e) := by
  intro R _ X Y f e _ d s L σ h
  refine ⟨fun i => LB.isLB_pull (h.isLB i) e, fun y => ?_⟩
  obtain ⟨C, hC⟩ := h.chart (e y)
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := y) (u := (e ⁻¹ᵁ C.U : Y.Opens)) hC
      (e ⁻¹ᵁ C.U).isOpen
  have hle : W ≤ e ⁻¹ᵁ C.U := hWV
  have hap : ∀ a : Γ(X, C.U), (e.appLE C.U W hle).hom a = resG Y hle ((e.app C.U).hom a) :=
    fun _ => rfl
  refine ⟨{ U := W
            affine := hW
            t := fun a => (e.appLE C.U W hle).hom (C.t a)
            etale := GlobalTheory.T.isEtaleCoordinatesOnOpen_pull_openImmersion R X Y f e C.U W hle d C.t C.affine hW C.etale
            c := fun i _ => C.c i
            le := fun i => (hle.trans (e.preimage_mono (C.le i))).trans
              (Cartier.pull_U (L i) e (fun _ => C.c i)).ge
            e := C.e
            inj := C.inj
            u := fun i => Units.map (e.appLE C.U W hle).hom.toMonoidHom (C.u i)
            eq := fun i => ?_ }, hyW⟩
  have h1 := congrArg (e.appLE C.U W hle).hom (C.eq i)
  rw [map_mul, hap, Cartier.app_resG, Cartier.resG_resG] at h1
  refine (Cartier.resG_resG _ _ _).trans (h1.trans ?_)
  congr 1
  cases C.e i with
  | none => exact map_one _
  | some a => rfl

end GlobalTheory.LogPair
