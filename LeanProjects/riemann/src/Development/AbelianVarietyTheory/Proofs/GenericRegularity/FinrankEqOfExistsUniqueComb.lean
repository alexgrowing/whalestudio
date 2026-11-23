import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCombAtIffCoordinateCombination
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinates

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open scoped CategoryTheory.Obj

namespace GlobalTheory.Reg

theorem finrank_eq_of_existsUnique_comb {L V : Type} [Field L] [AddCommGroup V] [Module L V] (N : Submodule L V)
    {m : ℕ} (cv : Fin m → V) (hcv : ∀ i, cv i ∈ N) (h : ∀ v ∈ N, ∃! a : Fin m → L, ∑ i, a i • cv i = v) :
    Module.finrank L N = m := by
  have hli : LinearIndependent L cv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := (h 0 N.zero_mem).unique hg (y₂ := 0) (by simp)
    rw [this]; rfl
  have hN : N = Submodule.span L (Set.range cv) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨a, rfl, -⟩ := h v hv
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hcv i
  rw [hN, finrank_span_eq_card hli, Fintype.card_fin]

theorem finrank_chart_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (x : Sp L ⟶ Xo.X) (Λ : M.Lift f x) (τ : E →+* ℂ) (N : Submodule L (Fin M.n → L)), (∀ cv, cv ∈ N ↔ M.Eig f τ cv) → Module.finrank L N = Dw.mult τ := by
  intro E _ _ _ H Dw l Xo c O _ β Y M L _ _ f x Λ τ N hN
  classical
  have hx0 : x ≫ Xo.s = sOf c L := by
    rw [← Λ.xF_fst, Category.assoc, pullback.condition, ← Category.assoc, Λ.xF_snd]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hs : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom := by
    have := Xo.univ.t.semi.smooth
    show Smooth (pullback.snd Xo.univ.t.G.hom x)
    infer_instance
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  obtain ⟨d, hd, hdW⟩ : ∃ d : Fin (Dw.mult τ) → Fin n → L,
      LinearIndependent L d ∧ ∀ i, d i ∈ gfpEig (c := c) hx τ := by
    obtain ⟨B⟩ : Nonempty (Module.Basis (Fin (Dw.mult τ)) L (gfpEig (c := c) hx τ)) :=
      ⟨Module.finBasisOfFinrankEq L _ (gfp_finrank hx0 hx τ)⟩
    exact ⟨(gfpEig (c := c) hx τ).subtype ∘ B,
      B.linearIndependent.map' (gfpEig (c := c) hx τ).subtype (Submodule.ker_subtype _), fun i => by simp⟩
  obtain ⟨hex, htan, hco⟩ := GlobalTheory.Reg.vec_bijective E H Dw l Xo c O β Y M L f x Λ
  have hcomb := GlobalTheory.Reg.VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M L f x Λ
  have heig := GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c O β Y M L f x Λ τ
  choose cv hcv using fun i => (hco _ (gfp_tan hx (d i))).exists
  refine finrank_eq_of_existsUnique_comb N cv
    (fun i => (hN _).2 ((heig _ _ (hcv i)).1 ((gfp_eig_iff hx τ _).2 (hdW i)))) fun v hv => ?_
  obtain ⟨w, hw⟩ := (hex v).exists
  have hwt := htan v w hw
  have hb := gfp_basis hx0 hx τ d hd hdW w hwt ((heig v w hw).2 ((hN v).1 hv))
  refine (existsUnique_congr fun a => ?_).1 hb
  rw [hcomb _ cv _ a w hcv]
  exact ⟨fun h => (hco w hwt).unique h hw, fun h => h ▸ hw⟩

end GlobalTheory.Reg
