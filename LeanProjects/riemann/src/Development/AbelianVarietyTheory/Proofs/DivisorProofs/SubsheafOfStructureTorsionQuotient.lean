import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

set_option autoImplicit false

theorem GlobalTheory.exists_sub_mono_structure_of_genRank_pos : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → ∀ (F : T.Modules), QCoh.IsFiniteQC F → 0 < genRank F → ∃ (M : T.Modules) (f : M ⟶ structureModule T) (g : M ⟶ F), QCoh.IsFiniteQC M ∧ Mono f ∧ Mono g ∧ genRank (cokernel f) = 0 := by
  intro k _ T _ _ hT F hF hr
  obtain ⟨hprop, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hT.isProjOver
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (strHom k T)
  obtain ⟨n, hg, s, hs⟩ := ((hA.eventually_isGloballyGenerated_twist F).and
    (hA.eventually_exists_mono_cutHom_pow (structureModule T))).exists
  have hN := isLB_lbPow hA.isLB n
  have hP := Twist.isLB_lbZPow hN (-1)
  have hFN : genRank (twist F (lbPow A n)) ≠ 0 := by rw [genRank_twist hN]; omega
  obtain ⟨t, ht⟩ := exists_germ_ne_zero hg hFN
  have hmt := mono_sectionHom t ht
  obtain ⟨e₁⟩ := nonempty_twist_twist_iso_of_cls_eq F hN hP (LB.isLB_triv T)
    (by rw [cls_lbZPow hN (-1) hP, cls_triv]; simp)
  obtain ⟨e₂⟩ := nonempty_twist_iso_of_cls_eq_zero F (LB.isLB_triv T) (cls_triv _)
  have hM : QCoh.IsFiniteQC (twistZ (structureModule T) (lbPow A n) (-1)) :=
    Twist.isFiniteQC_twist hP
  have hmg : Mono (Twist.map (lbZPow (lbPow A n) (-1)) (QCoh.sectionHom t)) :=
    (Twist.mono_map_iff hP _).2 hmt
  refine ⟨_, cutHom (structureModule T) hN s,
    Twist.map (lbZPow (lbPow A n) (-1)) (QCoh.sectionHom t) ≫ e₁.hom ≫ e₂.hom, hM, hs,
    inferInstance, ?_⟩
  have h₁ := genRank_cokernel (cutHom (structureModule T) hN s)
  rw [(isVB_structureModule T).genRank_eq, genRank_twist hP, (isVB_structureModule T).genRank_eq] at h₁
  omega
