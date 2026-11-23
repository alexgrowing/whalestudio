import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationOfOrthogonalPerfectPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationsOrthogonalLineBundlePairingProdu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamLocallyFreeHodgeDegenerates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqOfRankAtStalk
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLagr

open GlobalTheory GlobalTheory.CatCoh GlobalTheory.PDiv GlobalTheory.PtExt in

theorem mem_fil_of_orth_of_ker (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (g : ℕ) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom) (P : LB (A ⊗ B).left) (hLB : P.IsLB)
    (hz : GlobalTheory.AbLaw.Triv (AbDual.ev P (𝟙 A) (1 : A ⟶ B))) (e : ℕ) (he : IsUnit (e : R))
    (hker : ∀ v : epsR R ⟶ B, GlobalTheory.AbLaw.Triv (AbDual.ev P (fst A (epsR R)) (snd A (epsR R) ≫ v)) → v ^ e = 1)
    (φ : HdR A →ₗ[R] HdR B →ₗ[R] R) (hφ : AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ) (y : HdR B)
    (hy : ∀ x ∈ Fil A, φ x y = 0) : y ∈ Fil B := by
  have hHDR := GlobalTheory.AbCoh.abelianHodgeDeRham
  obtain ⟨-, hHodge, -⟩ := GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange hHDR
  obtain ⟨v, hv⟩ := ((hHodge R B g hB hgB).1.1 y).exists
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_isChartChoiceForPoints_of_nontrivial R A B P hLB
  have horth := GlobalTheory.T.hodgeFiltrations_orthogonal_lineBundlePairing_product hHDR R A B g hA hB hgA hgB P hLB φ hφ
  obtain ⟨k, hk⟩ := GlobalTheory.T.cohomologous_neg_torsor_cocycle_of_orthogonal hHDR R A B g hA hB hgA hgB P hLB φ hφ horth y v hv 0
    (fun h hh ↦ by rw [hy h hh, map_zero]) 0 (by simp) j hj
  have hk' : IsCob (chartsA P) (tanCoc P j v) k := by
    intro D _ _ D' _ _ ψ x hx
    have e := hk D D' ψ x hx
    simp only [Fn1.add, Fn1.neg, fv, neg_neg] at e
    rw [show ev (0 : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (trivMap ψ x) = 0 from rfl, zero_add] at e
    exact e
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_pointwiseLineBundleGenerator_of_trivial_pullback R (A ⊗ B) A P hLB (AbDual.inl A B) hz
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_dualNumberGenerator_of_torsorCoboundary R A B P hLB v hv.1 j hj s hs k hk'
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_pointwiseGenerator_of_dualNumberLineBundleGenerator R A B P hLB v hv.1 T hT
  have htriv := GlobalTheory.T.cechLineBundle_pull_trivial_of_pointwiseGenerator R (A ⊗ B) (A ⊗ epsR R) P hLB _ t ht
  have hv1 : v ^ e = 1 := hker v htriv
  have hpow : ∀ n : ℕ, IsLieImage (n • y) (v ^ n) := by
    intro n
    induction n with
    | zero => rw [zero_smul, pow_zero]; exact isLieImage_one_iff.2 (Submodule.zero_mem _)
    | succ n ih => rw [succ_nsmul, pow_succ]; exact ih.add hv
  have h1 : (e : R) • y ∈ Fil B := by
    rw [Nat.cast_smul_eq_nsmul]
    have := hpow e
    rw [hv1] at this
    exact isLieImage_one_iff.1 this
  obtain ⟨u, hu⟩ := he
  have hyu : y = ((u⁻¹ : Rˣ) : R) • ((e : R) • y) := by
    rw [smul_smul, ← hu, Units.inv_mul, one_smul]
  rw [hyu]
  exact Submodule.smul_mem _ _ h1

theorem fil_lagrangian : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C₀ : Type) [CommRing C₀] (s : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s)
    (φ' : HdR o₀.A →ₗ[C₀] HdR o₀.A →ₗ[C₀] C₀), (∃ g : ℕ, SmoothOfRelativeDimension g o₀.A.hom) →
    GlobalTheory.AbDual.IsCorrForm (dp0 C₀) (𝟙 _) o₀.A o₀.A o₀.P φ' →
    (∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, φ' x y = 0) ∧ ∀ x, (∀ y ∈ Fil o₀.A, φ' x y = 0) → x ∈ Fil o₀.A := by
  intro p _ D R _ b N C₀ _ s o₀ φ' ⟨g, hg⟩ hφ
  refine ⟨GlobalTheory.PtExt.HodgeOrth.fil_orthogonal GlobalTheory.AbCoh.abelianHodgeDeRham C₀ o₀.A o₀.A g o₀.ab o₀.ab hg hg o₀.P
    o₀.isLB φ' hφ, fun x hx ↦ ?_⟩
  rcases subsingleton_or_nontrivial C₀ with hC | hC
  · haveI : Subsingleton (HdR o₀.A) := Module.subsingleton C₀ _
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _
  obtain ⟨e, hep, hker⟩ := o₀.kerP
  have heu : IsUnit (e : C₀) := by
    have := (b.unit e hep).map (Spec.preimage s).hom
    rwa [map_natCast] at this
  have hs : (AbDual.swap o₀.P).IsLB := pull_isLB o₀.isLB _
  refine mem_fil_of_orth_of_ker C₀ o₀.A o₀.A g o₀.ab o₀.ab hg hg (AbDual.swap o₀.P) hs ?_ e heu ?_ (-φ'.flip)
    (GlobalTheory.SymmPoincare.isCorrForm_swap hφ) x ?_
  · rw [AbDual.triv_ev_iff hs, AbDual.evc_swap o₀.isLB, ← AbDual.triv_ev_iff o₀.isLB]
    exact o₀.rig₁
  · intro v hv
    rw [AbDual.triv_ev_iff hs, AbDual.evc_swap o₀.isLB, ← AbDual.triv_ev_iff o₀.isLB] at hv
    exact hker _ v hv
  · intro y hy
    simp [hx y hy]

end GlobalTheory.HTLagr
