import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCochainPullbackBaseChangeCocycleCoboundaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeSpecAlgebraProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPointwiseCoboundaryOfPullbackBaseChangeIsIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangePullSumMulPointValueEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsAdditiveLiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCohomologousOfDeRhamSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToH1StructureSurjectiveAbelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtAlgCompRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEq
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.SurjD

theorem exists_fin_sum_tmul {R D M : Type*} [CommRing R] [CommRing D] [Algebra R D] [AddCommGroup M]
    [Module R M] (z : D ⊗[R] M) : ∃ (n : ℕ) (d : Fin n → D) (m : Fin n → M), z = ∑ i, d i ⊗ₜ m i := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset z
  refine ⟨S.card, fun i ↦ (S.equivFin.symm i).1.1, fun i ↦ (S.equivFin.symm i).1.2, ?_⟩
  rw [hS, ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp S.equivFin.symm (fun p : S ↦ p.1.1 ⊗ₜ p.1.2)).symm

theorem cohom_of_cob {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens}
    {u a b c : Fn1 X} (h : Cohom W u a) (k : Fn0 X) (hk : IsCob W c k)
    (ha : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt X D), a D D' φ x = c D D' φ x + b D D' φ x) : Cohom W u b := by
  obtain ⟨k₀, hk₀⟩ := h
  refine ⟨fun D _ _ x ↦ k₀ D x + k D x, ?_⟩
  intro D _ _ D' _ _ φ x hx
  have h1 := hk₀ D D' φ x hx
  have h2 := hk D D' φ x hx
  have h3 := ha D D' φ x
  simp only [Fn1.add, Fn1.neg] at h1 ⊢
  rw [map_add]
  linear_combination h1 + h2 + h3

end GlobalTheory.PtExt.SurjD

open GlobalTheory.PtExt.SurjD in

theorem GlobalTheory.PtExt.cohom_sumMul_fv_of_abelian : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ (D : Type) [CommRing D] [Algebra R D] (u : Fn1 (SpAlg R D ⊗ B)), IsCoc (whole _) u → ∃ (n : ℕ) (d : Fin n → D) (β : Fin n → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))), Cohom (whole _) u (sumMul d fun i ↦ fv (β i)) := by
  intro H R _ B _ g hB hg D _ _ u hu
  obtain ⟨B', _, π, q, hpb, hB', hg', hq, hfst, hsnd⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_spec_algebra_prod R D B g hB hg
  have w : q ≫ (SpAlg R D ⊗ B).hom = B'.hom ≫ spMap (algebraMap R D) := by
    rw [← Over.w (fst (SpAlg R D) B), ← Category.assoc, hfst]
    rfl
  have hu' := (GlobalTheory.T.pointCochainPullbackBaseChange_cocycle_coboundary_whole R D (algebraMap R D) _ B' q w u).1 hu
  have hsurj := GlobalTheory.PtExt.toH1O_surjective_of_abelian H D B' g hB' hg'
  obtain ⟨f', hf'⟩ := GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective D B' hsurj (bcPull w u) hu'
  obtain ⟨hFree, -, hBC⟩ := GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange H
  have hbc := (hBC R B g hB hg D B' π hpb).1
  have hall : prim (dp0 D) (𝟙 _) B' = ⊤ := (hFree D B' g hB' hg').1
  have hmem : H1.mk _ f' ∈ prim (dp0 D) (𝟙 _) B' := by rw [hall]; exact Submodule.mem_top
  obtain ⟨z, hz⟩ := hbc.2 ⟨H1.mk _ f', hmem⟩
  obtain ⟨n, d, m, rfl⟩ := exists_fin_sum_tmul z
  choose β hβ using fun i ↦ H1.mk_surjective _ (m i).1
  refine ⟨n, d, β, ?_⟩
  let mB := (GlobalTheory.Published.AbelianDeRham.bcMor hpb).isMor
  let S : Z1 (O (dp0 D) (B'.hom ≫ 𝟙 _)) := ∑ i, d i • mB.coef.pullbackOneCocycle (β i)
  have hcl : H1.mk _ f' = H1.mk _ S := by
    have e := congrArg Subtype.val hz
    simp only [map_sum, liftSemi_tmul] at e
    rw [← e]
    simp only [S, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, GrpMor.coe_pull]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hβ i]
    rfl
  obtain ⟨g₀, hg₀⟩ := H1.mk_eq_mk.1 hcl
  obtain ⟨hadd, -, hcob⟩ := GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear D B'
  obtain ⟨k, hk⟩ := hcob g₀
  have hsplit : f' = ⟨d0 _ g₀, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g₀⟩ + S := Subtype.ext (by simp [hg₀])
  have hC : Cohom (whole B') (bcPull w u) (fv S) := by
    refine cohom_of_cob hf' k hk ?_
    rw [hsplit, hadd]
    intros
    rfl
  have hsum := GlobalTheory.T.baseChangePull_sum_mul_pointValue_eq R D B B' q w π hfst hsnd mB (Fin n) d β
  obtain ⟨k', hk'⟩ : ∃ k, IsCob (whole B') (bcPull w (u.add (sumMul d fun i ↦ fv (β i)).neg)) k := by
    obtain ⟨k', hk'⟩ := hC
    refine ⟨k', ?_⟩
    have e : bcPull w (u.add (sumMul d fun i ↦ fv (β i)).neg) = (bcPull w u).add (fv S).neg := by
      rw [← hsum]; rfl
    rw [e]; exact hk'
  have hsm : IsCoc (whole _) (sumMul d fun i ↦ fv (β i)) :=
    (GlobalTheory.PtExt.SumMulFacts.main R D B (Fin n) d _).1 fun i ↦ (fv_isCoc_and_ev_eq R B (β i)).1
  have hdiff : IsCoc (whole _) (u.add (sumMul d fun i ↦ fv (β i)).neg) := by
    intro E _ _ E' _ _ E'' _ _ φ ψ x hx
    have h1 := hu E E' E'' φ ψ x hx
    have h2 := hsm E E' E'' φ ψ x hx
    simp only [Fn1.add, Fn1.neg, map_add, map_neg]
    linear_combination h1 - h2
  exact GlobalTheory.T.isPointwiseCoboundary_of_pullbackBaseChange_isIso R D (algebraMap R D) _ B' q w hq _ hdiff ⟨k', hk'⟩
