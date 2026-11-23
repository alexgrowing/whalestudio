import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareOfSymmetricTensorRelationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommAlgFunctorCohomologyCupAnticommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyH1AxesPrimitiveRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyStructureSheafIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyTrivialBundleAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KunnethCupTensorInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.WedgeSq

theorem exists_fin_sum_tmul {K V W : Type} [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (t : V ⊗[K] W) : ∃ (n : ℕ) (x : Fin n → V) (y : Fin n → W), t = ∑ i, x i ⊗ₜ[K] y i := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a b => exact ⟨1, fun _ ↦ a, fun _ ↦ b, by simp⟩
  | add s t hs ht =>
    obtain ⟨n, x, y, rfl⟩ := hs
    obtain ⟨m, x', y', rfl⟩ := ht
    exact ⟨n + m, Fin.append x x', Fin.append y y', by simp [Fin.sum_univ_add]⟩

theorem exists_fin_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [QuasiCompact s] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).1 isCompact_univ
  have := hS.fintype
  let q := (Fintype.equivFin S).symm
  refine ⟨_, fun i ↦ (q i).1.1, fun i ↦ (q i).1.2, ?_⟩
  rw [e]
  apply le_antisymm
  · exact iSup_le fun i ↦ le_iSup₂_of_le (q i).1 (q i).2 le_rfl
  · refine iSup₂_le fun U hU ↦ ?_
    obtain ⟨i, hi⟩ := q.surjective ⟨U, hU⟩
    exact le_iSup_of_le i (by simp only [hi]; exact le_rfl)

variable {K : Type} [Field K]

theorem overPullbackStructureSheaf_cohomology_cup {Y A : Over (Sp K)} (f : Y ⟶ A) (a b : HO1 A.hom) :
    structureSheafH2Pullback f (cup (OAff A.hom) a b) = cup (OAff Y.hom) (pO1 f a) (pO1 f b) :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.1 K K A.left Y.left A.hom Y.hom (RingHom.id K) f.left (ovw f)).1 a b

variable (A : Over (Sp K)) [GrpObj A]

abbrev mixed : HO1 A.hom →ₗ[K] HO1 A.hom →ₗ[K] HO2 (A ⊗ A).hom :=
  (cup (OAff (A ⊗ A).hom)).compl₁₂ (pO1 (fst A A)) (pO1 (snd A A))

theorem defect_eq (hp : StructureSheafH1Primitive A) (t : HO1 A.hom ⊗[K] HO1 A.hom) :
    structureSheafH2Pullback μ[A] (TensorProduct.lift (cup (OAff A.hom)) t) - structureSheafH2Pullback (fst A A) (TensorProduct.lift (cup (OAff A.hom)) t)
      - structureSheafH2Pullback (snd A A) (TensorProduct.lift (cup (OAff A.hom)) t)
      = TensorProduct.lift (mixed A) (t - TensorProduct.comm K _ _ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.lift.tmul, TensorProduct.comm_tmul, map_sub, overPullbackStructureSheaf_cohomology_cup, hp a, hp b, map_add,
      LinearMap.add_apply, LinearMap.compl₁₂_apply]
    rw [GlobalTheory.T.commAlgFunctorCohomologyCup_anticomm K _ (OAff (A ⊗ A).hom) (pO1 (snd A A) a) (pO1 (fst A A) b)]
    abel
  | add s t hs ht =>
    have e : s + t - TensorProduct.comm K _ _ (s + t)
        = (s - TensorProduct.comm K _ _ s) + (t - TensorProduct.comm K _ _ t) := by
      rw [map_add]; abel
    rw [e, map_add (TensorProduct.lift (mixed A)), ← hs, ← ht]
    simp only [map_add]
    abel

theorem mixed_injective [IsSeparated A.hom] [QuasiCompact A.hom] (u : HO1 A.hom ⊗[K] HO1 A.hom)
    (hu : TensorProduct.lift (mixed A) u = 0) : u = 0 := by
  obtain ⟨n, x, y, rfl⟩ := exists_fin_sum_tmul u
  refine GlobalTheory.T.kunneth_cup_tensor_injective K A A inferInstance inferInstance inferInstance inferInstance n x y ?_
  simpa [map_sum] using hu

theorem symm_of_prim [IsSeparated A.hom] [QuasiCompact A.hom] (hp : StructureSheafH1Primitive A) (t : HO1 A.hom ⊗[K] HO1 A.hom)
    (ht : structureSheafH2Pullback μ[A] (TensorProduct.lift (cup (OAff A.hom)) t)
      = structureSheafH2Pullback (fst A A) (TensorProduct.lift (cup (OAff A.hom)) t)
        + structureSheafH2Pullback (snd A A) (TensorProduct.lift (cup (OAff A.hom)) t)) :
    TensorProduct.comm K _ _ t = t := by
  have h0 := defect_eq A hp t
  rw [ht, add_sub_cancel_left, sub_self] at h0
  exact (sub_eq_zero.1 (mixed_injective A _ h0.symm)).symm

end GlobalTheory.AbCoh.WedgeSq

open GlobalTheory.AbCoh.WedgeSq in

theorem GlobalTheory.AbCoh.wedgeO_noPrimO2 : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    GlobalTheory.AbCoh.WedgeO (OAff A.hom) ∧ GlobalTheory.AbCoh.NoPrimitiveStructureSheafH2 A := by
  intro K _ _ A _ g hab hsm
  haveI : IsProper A.hom := hab.proper
  haveI hsep : IsSeparated A.hom := inferInstance
  haveI hqc : QuasiCompact A.hom := inferInstance
  obtain ⟨-, hprim, -⟩ := GlobalTheory.T.abelian_variety_h1_axes_primitive_rank K A g hab hsm
  obtain ⟨n, D, hD, hcov⟩ := GlobalTheory.AbCoh.WedgeSq.exists_fin_affine_cover A.hom
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := GlobalTheory.T.cech_cohomology_structure_sheaf_iso K A.left A.hom (Fin n) D hsep hD hcov
  obtain ⟨hfin, h1, h2⟩ := GlobalTheory.T.cech_cohomology_trivial_bundle_abelian K A g hab hsm (Fin n) D hD hcov
  haveI := hfin 1
  haveI := hfin 2
  haveI : Module.Finite K (HO1 A.hom) := Module.Finite.equiv e1.symm
  haveI : Module.Finite K (HO2 A.hom) := Module.Finite.equiv e2.symm
  have hdim : Module.finrank K (HO2 A.hom) ≤ (Module.finrank K (HO1 A.hom)).choose 2 := by
    rw [e2.finrank_eq, e1.finrank_eq, h1]; exact h2
  have hrel : ∀ t : HO1 A.hom ⊗[K] HO1 A.hom, TensorProduct.lift (cup (OAff A.hom)) t = 0 →
      TensorProduct.comm K _ _ t = t := fun t ht ↦ symm_of_prim A hprim t (by simp [ht])
  obtain ⟨hw, hsurj, hsym⟩ := GlobalTheory.T.exteriorSquare_of_symmetric_tensor_relations K (HO1 A.hom) (HO2 A.hom) (cup (OAff A.hom)) hdim hrel
  refine ⟨hw, fun z hz ↦ ?_⟩
  obtain ⟨t, rfl⟩ := hsurj z
  exact hsym t (symm_of_prim A hprim t hz)
