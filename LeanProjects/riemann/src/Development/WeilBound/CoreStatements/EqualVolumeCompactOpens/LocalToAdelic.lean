import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Assembly
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.ExistsDualBasis
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.CptLact

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates

open IsDedekindDomain
open scoped TensorProduct

theorem mem_hat_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (hΛ : IsLat Λ) (y : Fin r → Adf (maximalRealSubfield E) E) :
    y ∈ hatLat (maximalRealSubfield E) Λ.toAddSubgroup ↔
      ∀ v, (fun i => GroundTheory.Heights₂.Heights.StrongApprox.compAt E v (y i)) ∈ GlobalTheory.SelfDualGenus.locLattice v Λ := by
  constructor
  · intro hy v
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, x, hx, rfl⟩ := hy
      have := (GlobalTheory.SelfDualGenus.locLattice v Λ).smul_mem ⟨b v, hb v⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)
      convert this using 1
      funext i
      show b v ⊗ₜ x i = b v • ((1 : v.adicCompletion (maximalRealSubfield E)) ⊗ₜ[maximalRealSubfield E] x i)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | zero => simp only [Pi.zero_apply, map_zero]; exact (GlobalTheory.SelfDualGenus.locLattice v Λ).zero_mem
    | add x y _ _ hx hy => simp only [Pi.add_apply, map_add]; exact (GlobalTheory.SelfDualGenus.locLattice v Λ).add_mem hx hy
    | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact (GlobalTheory.SelfDualGenus.locLattice v Λ).neg_mem hx
  · intro h
    obtain ⟨k, z, l, hz, hl, e⟩ := exists_dualBasis (F := maximalRealSubfield E) hΛ
    rw [eq_sum_coordR e y]
    refine AddSubgroup.sum_mem _ fun j _ => tmul_mem_hat (fun v => ?_) (hz j)
    have h1 := map_coordR (l j) (GroundTheory.Heights₂.Heights.StrongApprox.evalAt (maximalRealSubfield E) v) y
    show GroundTheory.Heights₂.Heights.StrongApprox.evalAt (maximalRealSubfield E) v _ ∈ _
    rw [h1]
    have key : ∀ w ∈ GlobalTheory.SelfDualGenus.locLattice v Λ,
        coordR (l j) (v.adicCompletion (maximalRealSubfield E)) w ∈ v.adicCompletionIntegers _ := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨x, hx, rfl⟩ := hw
        obtain ⟨o, ho⟩ := hl j x hx
        have : coordR (l j) (v.adicCompletion (maximalRealSubfield E)) (fun i => GlobalTheory.SelfDualGenus.locEmb v (x i)) =
            l j x • 1 := coordR_tmul _ 1 x
        rw [this, ho, ← Algebra.algebraMap_eq_smul_one]
        exact HeightOneSpectrum.coe_algebraMap_mem _ _ v o
      | zero => rw [coordR_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [coordR_add]; exact add_mem hx hy
      | smul a x _ hx =>
        have : ∀ (a : v.adicCompletion (maximalRealSubfield E)) x,
            coordR (l j) (v.adicCompletion (maximalRealSubfield E)) (a • x) = a * coordR (l j) _ x := by
          intro a x
          induction x using pi_induction with
          | h0 => simp [coordR_zero]
          | h1 b x =>
            have : (a • fun i => b ⊗ₜ[maximalRealSubfield E] x i) = fun i => (a * b) ⊗ₜ[maximalRealSubfield E] x i := rfl
            rw [this, coordR_tmul, coordR_tmul, mul_smul_comm]
          | h2 x y hx hy => rw [smul_add, coordR_add, coordR_add, hx, hy, mul_add]
        have e2 := this a x
        exact (show coordR (l j) _ (a • x) = _ from e2) ▸ mul_mem a.2 hx
    exact key _ (h v)

open GroundTheory.Heights₂.Heights.StrongApprox in
theorem localToAdelic : LocalToAdelic := by
  intro E _ _ _ r G L L' hL hL' ⟨γ, hγ, hfin⟩
  classical
  obtain ⟨hsep, hv⟩ := PlaceMaps.full (maximalRealSubfield E) E (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E)
  have hsepM : ∀ A B : Matrix (Fin r) (Fin r) (Adf (maximalRealSubfield E) E),
      (∀ v, A.map (compAt E v) = B.map (compAt E v)) → A = B := fun A B h =>
    Matrix.ext fun i j => hsep _ _ fun v => congrFun (congrFun (h v) i) j
  have glue : ∀ M : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      Matrix (Fin r) (Fin r) (GlobalTheory.SelfDualGenus.LocAlg v), (∀ v, γ v = 1 → M v = 1) →
      ∃ A : Matrix (Fin r) (Fin r) (Adf (maximalRealSubfield E) E), ∀ v, A.map (compAt E v) = M v := by
    intro M hM
    refine ⟨1 + ∑ w ∈ hfin.toFinset, (M w - 1).map (singleV E w), fun v => Matrix.ext fun i j => ?_⟩
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, map_add, map_sum]
    rw [Finset.sum_eq_single v (fun w _ hw => (hv w).2.1 v hw.symm _) (fun h => by
      rw [hM v (by simpa using h)]; simp), (hv v).1, Matrix.one_apply, apply_ite (compAt E v), map_one, map_zero,
      Matrix.sub_apply, Matrix.one_apply]
    ring
  obtain ⟨A, hA⟩ := glue (fun v => γ v) fun v h => by rw [h, Units.val_one]
  obtain ⟨B, hB⟩ := glue (fun v => ((γ v)⁻¹ : GL (Fin r) _)) fun v h => by rw [h, inv_one, Units.val_one]
  have h1 : ∀ v, (1 : Matrix (Fin r) (Fin r) (Adf (maximalRealSubfield E) E)).map (compAt E v) = 1 := fun v =>
    Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨A, B, hsepM _ _ fun v => by rw [Matrix.map_mul, hA, hB, Units.mul_inv, h1],
    hsepM _ _ fun v => by rw [Matrix.map_mul, hA, hB, Units.inv_mul, h1]⟩, hsepM _ _ fun v => ?_, fun x => ?_⟩
  · have e1 : (G.map (inclAd (maximalRealSubfield E) E)).map (compAt E v) = G.map (GlobalTheory.SelfDualGenus.locEmb v) :=
      Matrix.ext fun i j => (hv v).2.2.2.2.2.2.2.1 _
    have e2 : (A.map (sigAd (IsCMField.complexConj E))).map (compAt E v) =
        (A.map (compAt E v)).map (GlobalTheory.SelfDualGenus.locConj v) :=
      Matrix.ext fun i j => (hv v).2.2.2.2.2.2.1 _
    show (Aᵀ * _ * A.map _).map _ = _
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2, Matrix.transpose_map, hA]
    exact (hγ v).1.symm
  · rw [mem_hat_iff hL, mem_hat_iff hL']
    refine forall_congr' fun v => ((hγ v).2 _).trans ?_
    rw [← hA]
    have : (A.map (compAt E v)) *ᵥ (fun i => compAt E v (x i)) = fun i => compAt E v ((A *ᵥ x) i) :=
      funext fun i => (RingHom.map_mulVec (compAt E v) A x i).symm
    rw [this]

end PositivityTheory.EqVol
