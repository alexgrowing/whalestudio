import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem secIsMul_gs {R : Type} [CommRing R] {Y Z : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of R)} {L : LB Y} {a : R}
    {σ τ : LB.Sec L} (h : SecIsMul p a σ τ) (q : Z ⟶ Y) (z : Z) (j : L.ι) (hz : q z ∈ L.U j) :
    gs q z (L.U j) (σ.f j) = cst (q ≫ p) z a * gs q z (L.U j) (τ.f j) := by
  rw [h j, gs_mul q z _ hz]
  congr 1
  exact gs_constFn p (L.U j) q z hz a

private theorem gs_eq_cst_mul_gs_of_secIsMul {R : Type} [CommRing R] {Y Z : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of R)}
    {L : LB Y} {a : R} {σ τ : LB.Sec L} (h : SecIsMul p a σ τ) (q : Z ⟶ Y) (z : Z) (j : L.ι) :
    gs q z (L.U j) (σ.f j) = cst (q ≫ p) z a * gs q z (L.U j) (τ.f j) := by
  by_cases hz : q z ∈ L.U j
  · exact secIsMul_gs h q z j hz
  · simp only [gs, dif_neg hz, mul_zero]

theorem expandsAt_secIsMul : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (a : R) (σ σ' : H0 U.LG.L k) (f f' : ∀ α : D.toPre.X, D.toPre.SecB k α), SecIsMul G.hom a σ' σ → (∀ α, SecIsMul D.toPre.P.A.hom a (f' α) (f α)) → U.ExpandsAt e k σ f → U.ExpandsAt e k σ' f' := by
  intro R _ _ I D A G _ _ U e k a σ σ' f f' hσ hf hE
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f hE
  have hsf : ∀ α (y : (thickObj R I e G).left) J, sval (f' α) (pGl U e) y J =
      cst (pGl U e ≫ D.toPre.P.A.hom) y a * sval (f α) (pGl U e) y J := by
    intro α y J
    unfold sval
    exact gs_eq_cst_mul_gs_of_secIsMul (hf α) _ _ _
  have hsσ : ∀ (y : (thickObj R I e G).left) jL, sv U k σ' (fGl I G e) y jL =
      cst (fGl I G e ≫ G.hom) y a * sv U k σ (fGl I G e) y jL := by
    intro y jL
    unfold sv
    exact gs_eq_cst_mul_gs_of_secIsMul hσ _ _ _
  have hmap : fGl I G e ≫ G.hom = pGl U e ≫ D.toPre.P.A.hom := by
    simp only [fGl, pGl, Over.w]
  refine expandsAt_of_val U e k σ' f' S ?_
  intro y J hJ
  obtain ⟨h0, h1⟩ := hS _ (𝟙 _) y J hJ
  simp only [Category.id_comp] at h0 h1
  refine ⟨fun α hα => ?_, fun jL hmem => ?_⟩
  · rw [hsf, h0 α hα, mul_zero]
  · have h1' := h1 jL hmem
    rw [hsσ, hmap]
    have hsum : ∑ α ∈ S, sval (f' α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val =
        cst (pGl U e ≫ D.toPre.P.A.hom) y a *
          ∑ α ∈ S, sval (f α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [hsf, _root_.mul_assoc]
    rw [hsum, ← h1']
    ring

end GlobalTheory
