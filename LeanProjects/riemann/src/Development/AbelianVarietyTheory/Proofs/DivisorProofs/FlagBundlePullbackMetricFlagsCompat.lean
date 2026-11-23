import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleMetricSetupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSmoothRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernRenameBlockPerm

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPullSquare

theorem prod_Ioi_eq_rootDiscr {ι : Type} [Fintype ι] (r : ι → ℕ) :
    (∏ a, ∏ i : Fin (r a), ∏ i' ∈ Finset.Ioi i,
      (MvPolynomial.X (⟨a, i'⟩ : Σ a, Fin (r a)) - MvPolynomial.X ⟨a, i⟩) : MvPolynomial (Σ a, Fin (r a)) ℝ) =
      GlobalTheory.GoodMetric.rootDiscr r := by
  unfold GlobalTheory.GoodMetric.rootDiscr
  refine Finset.prod_congr rfl fun a _ => ?_
  exact Finset.prod_comm' (fun j i => by simp [and_comm])

theorem isHomogeneous_rootDiscr {ι : Type} [Fintype ι] (r : ι → ℕ) :
    (GlobalTheory.GoodMetric.rootDiscr r).IsHomogeneous (∑ a, r a * (r a - 1) / 2) := by
  have h : (GlobalTheory.GoodMetric.rootDiscr r).IsHomogeneous (∑ a, ∑ j : Fin (r a), ∑ _i ∈ Finset.Iio j, 1) := by
    unfold GlobalTheory.GoodMetric.rootDiscr
    refine IsHomogeneous.prod _ _ _ fun a _ => ?_
    refine IsHomogeneous.prod _ _ _ fun j _ => ?_
    refine IsHomogeneous.prod _ _ _ fun i _ => ?_
    exact (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
  convert h using 1
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun j => j) (r a), Finset.sum_range_id]

theorem antisymm_rootDiscr {ι : Type} [Fintype ι] (r : ι → ℕ) :
    GlobalTheory.GoodMetric.antisymm (GlobalTheory.GoodMetric.rootDiscr r) =
      (∏ a, ((r a).factorial : ℝ)) • GlobalTheory.GoodMetric.rootDiscr r := by
  unfold GlobalTheory.GoodMetric.antisymm
  have key (w : ∀ a, Equiv.Perm (Fin (r a))) :
      ((∏ a, Equiv.Perm.sign (w a) : ℤˣ) : ℤ) •
        rename (fun x : GlobalTheory.GoodMetric.Root r => (⟨x.1, w x.1 x.2⟩ : GlobalTheory.GoodMetric.Root r)) (GlobalTheory.GoodMetric.rootDiscr r) =
        GlobalTheory.GoodMetric.rootDiscr r := by
    have e := GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr ι r w
    have e' : (fun x : GlobalTheory.GoodMetric.Root r => (⟨x.1, w x.1 x.2⟩ : GlobalTheory.GoodMetric.Root r)) = Equiv.sigmaCongrRight w := by
      funext x
      rcases x with ⟨a, i⟩
      rfl
    rw [e', e, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  rw [Finset.sum_congr rfl fun w _ => key w, Finset.sum_const, Finset.card_univ, Fintype.card_pi,
    ← Nat.cast_smul_eq_nsmul ℝ]
  simp [Fintype.card_perm]

theorem powerSum_pull_vandermonde : Hypotheses2 → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (D : ℕ), IsRegSurf q → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (m : ∀ a, Vert.Flag (E a) (r a)) (s : (Σ a, Fin (r a)) → ℝ), (∀ z, (VMetric.grLB (m z.1) z.2 (H z.1)).IsSelfInter (s z)) → ∀ Ψ : MvPolynomial ((Σ a, Fin (r a)) ⊕ (Σ a, Fin (r a))) ℝ →ₗ[ℝ] ℝ, IsArFun (Sum.elim (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) (fun z : Σ a, Fin (r a) => (VMetric.grLB (m z.1) z.2 (H z.1)).pull π w)) D Ψ → Ψ (rename Sum.inr (∑ z : Σ a, Fin (r a), MvPolynomial.X z ^ 2) * rename Sum.inl (∏ a, ∏ i : Fin (r a), ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (⟨a, i'⟩ : Σ a, Fin (r a)) - MvPolynomial.X ⟨a, i⟩))) = (∏ a, ((r a).factorial : ℝ)) * ∑ z, s z := by
  intro HP k _ B Y _ _ q p D hq hp π w ι _ E r h H fl hfl m s hs Ψ hΨ
  have hq' := hq.toIsArithVar
  have hE : ∀ a, GlobalTheory.VB.IsVB (E a) (r a) := fun a => (h a).isVB
  have hD : D - 1 = ∑ a, r a * (r a - 1) / 2 := by
    have := GlobalTheory.T.flag_bundle_smooth_relative_dimension B Y π ι E r fl hE hfl
    have := hq'.isLocallyNoetherian
    have h₁ := (GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_of_smooth_surjective B Y π (∑ a, r a * (r a - 1) / 2) 1
      (GlobalTheory.FlagSurj.isFlagBundle_surjective B Y π ι E r fl hE hfl) hq'.dim_eq).symm.trans hp.dim_eq
    have h₂ : 1 + (∑ a, r a * (r a - 1) / 2) + 1 = D + 1 := by exact_mod_cast h₁
    omega
  obtain ⟨Φ, hΦ⟩ := ((HP.p4.arExists k B q 1 hq').2 (Σ a, Fin (r a))
    fun z : Σ a, Fin (r a) => VMetric.grLB (m z.1) z.2 (H z.1)).1
  have hP : (∑ z : Σ a, Fin (r a), MvPolynomial.X z ^ 2 : MvPolynomial (Σ a, Fin (r a)) ℝ).IsHomogeneous (1 + 1) :=
    IsHomogeneous.sum _ _ _ fun z _ => isHomogeneous_X_pow z 2
  have key := GlobalTheory.T.flag_bundle_metric_setup HP k B Y q p 1 D hq' hq.regular hp π w ι E r h H fl hfl (Σ a, Fin (r a))
    (fun z : Σ a, Fin (r a) => VMetric.grLB (m z.1) z.2 (H z.1)) Φ Ψ hΦ hΨ _ _ _ hP
    (hD ▸ isHomogeneous_rootDiscr r) (antisymm_rootDiscr r)
  rw [prod_Ioi_eq_rootDiscr, mul_comm, key, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun z _ =>
    HermLB.IsSelfInter.unique hq' (((HP.p4.arIso k B q 1 hq').2 _ _ Φ hΦ).1 z) (hs z)

end GlobalTheory.FlagPullSquare
