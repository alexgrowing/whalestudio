import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem gs_res_global_scal_eq_cst {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    (q : Z ⟶ Y) (z : Z) (V : Y.Opens) (hz : q z ∈ V) (c : R) :
    gs q z V (resTop V (scal p c)) = cst (q ≫ p) z c := by
  unfold resTop
  rw [gs_res q z le_top hz]
  unfold scal cst
  exact gs_pull q p z ⊤ trivial _

theorem gs_of_eq_sum_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    (q : Z ⟶ Y) (z : Z) (V : Y.Opens) (hz : q z ∈ V) {n : ℕ} (c : Fin n → R) {a : Γ(Y, V)} {b : Fin n → Γ(Y, V)}
    (h : a = ∑ i, resTop V (scal p (c i)) * b i) :
    gs q z V a = ∑ i, cst (q ≫ p) z (c i) * gs q z V (b i) := by
  subst h
  rw [gs_fsum q z V hz]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul q z V hz, gs_res_global_scal_eq_cst p q z V hz]

theorem expandsAt_iff_stalks {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) :
    U.ExpandsAt e k σ f ↔ ∃ S : Finset D.toPre.X, ∀ (y : (thickObj R I e G).left) (J), Good D.toPre.P.L y J →
      (∀ α ∉ S, sval (f α) (pGl U e) y J = 0) ∧ ∀ jL, (fGl I G e) y ∈ U.LG.L.U jL →
        (wv U e (𝟙 _) y (J (pGl U e)) jL ^ k).val * sv U k σ (fGl I G e) y jL =
          ∑ α ∈ S, sval (f α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := expandsAt_val U e k σ f h
    refine ⟨S, fun y J hJ => ?_⟩
    have hy := hS _ (𝟙 _) y J hJ
    simp only [Category.id_comp] at hy
    exact hy
  · rintro ⟨S, hS⟩
    exact expandsAt_of_val U e k σ f S hS

theorem expandsAt_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k e n : ℕ) (c : Fin n → R) (σ : Fin n → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f : Fin n → ∀ α, D.toPre.SecB k α) (σ₀ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ : ∀ α, D.toPre.SecB k α), (∀ i, U.ExpandsAt e k (σ i) (f i)) → (∀ j, σ₀.f j = ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j) → (∀ α j, (f₀ α).f j = ∑ i, resTop _ (scal D.toPre.P.A.hom (c i)) * (f i α).f j) → U.ExpandsAt e k σ₀ f₀ := by
  intro R _ _ I D A G _ _ U k e n c σ f σ₀ f₀ hE hσ hf
  classical
  have hE' := fun i => (expandsAt_iff_stalks U e k (σ i) (f i)).1 (hE i)
  choose S hS using hE'
  refine (expandsAt_iff_stalks U e k σ₀ f₀).2 ⟨Finset.univ.biUnion S, fun y J hJ => ?_⟩
  have hc : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom := (Over.w _).trans (Over.w _).symm
  have key₀ : ∀ α, sval (f₀ α) (pGl U e) y J =
      ∑ i, cst (pGl U e ≫ D.toPre.P.A.hom) y (c i) * sval (f i α) (pGl U e) y J := fun α =>
    gs_of_eq_sum_scal D.toPre.P.A.hom (pGl U e) y _ (Good.mem hJ _ _) c (hf α _)
  refine ⟨fun α hα => ?_, fun jL hjL => ?_⟩
  · rw [key₀ α]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hS i y J hJ).1 α (fun h => hα (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, h⟩)), mul_zero]
  · have hmem : fGl I G e y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL) :=
      Set.mem_iInter.2 fun _ => hjL
    have keyσ : sv U k σ₀ (fGl I G e) y jL =
        ∑ i, cst (fGl I G e ≫ G.hom) y (c i) * sv U k (σ i) (fGl I G e) y jL :=
      gs_of_eq_sum_scal G.hom (fGl I G e) y _ hmem c (hσ _)
    have hR : ∑ α ∈ Finset.univ.biUnion S, sval (f₀ α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val =
        ∑ i, ∑ α ∈ Finset.univ.biUnion S,
          cst (fGl I G e ≫ G.hom) y (c i) * sval (f i α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [key₀ α, Finset.sum_mul, hc]
    rw [hR, keyσ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, (hS i y J hJ).2 jL hjL,
      Finset.sum_subset (Finset.subset_biUnion_of_mem S (Finset.mem_univ i))
        (fun α _ hα => by rw [(hS i y J hJ).1 α hα, zero_mul]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [_root_.mul_assoc]

end GlobalTheory
