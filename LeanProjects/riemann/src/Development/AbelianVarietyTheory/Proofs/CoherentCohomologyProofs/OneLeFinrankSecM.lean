import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHighTwistSectionNeZeroStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.PolSection

open GlobalTheory.SecGrowth

variable {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X)

theorem wchart_le_tw (N t : ℤ) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => π) j ≤
      (tw (L.pull π) (pw (L.pull π) N) t).U ((fun _ => j 0), (fun _ => j 0)) :=
  le_inf (wchart_le_unit L π j) (wchart_le_unit L π j)

theorem lcg_tw (N t : ℤ) (j j' : Fin 1 → L.ι) :
    LB.lcg L (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t) j j' =
      res (inf_le_inf (wchart_le_tw L π N t j) (wchart_le_tw L π N t j'))
        ((tw (L.pull π) (pw (L.pull π) N) t).g ((fun _ => j 0), (fun _ => j 0))
          ((fun _ => j' 0), (fun _ => j' 0))) := by
  have h := SecOn.res_tw_g (M := L.pull π) (H := pw (L.pull π) N) t (fun _ => j 0) (fun _ => j' 0)
    (fun _ => j 0) (fun _ => j' 0) (inf_le_inf (wchart_le_tw L π N t j) (wchart_le_tw L π N t j'))
    (inf_le_inf (wchart_le_unit L π j) (wchart_le_unit L π j'))
    (inf_le_inf (wchart_le_unit L π j) (wchart_le_unit L π j'))
  refine Eq.trans ?_ h.symm
  change _ = res (inf_le_inf (wchart_le_unit L π j) (wchart_le_unit L π j'))
        (LB.lcg L (K := PUnit) (fun _ => π) (fun _ => 1) (fun _ => j 0) (fun _ => j' 0)) *
      res (inf_le_inf (wchart_le_unit L π j) (wchart_le_unit L π j'))
        (LB.lcg L (K := PUnit) (fun _ => π) (fun _ => 1) (fun _ => j 0) (fun _ => j' 0) ^ N) ^ t
  rw [map_zpow, ← zpow_mul, ← zpow_one_add, LB.lcg_pull, LB.res_res, LB.lcg, Fintype.prod_unique]
  rfl

theorem exists_sec_ne_zero [IsIntegral Y] (hL : L.IsLB) (N t : ℤ)
    (σ : LB.Sec (tw (L.pull π) (pw (L.pull π) N) t)) (i : (tw (L.pull π) (pw (L.pull π) N) t).ι)
    (hi : σ.f i ≠ 0) :
    ∃ τ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t)), τ.f ≠ 0 := by
  refine ⟨transSec (M := tw (L.pull π) (pw (L.pull π) N) t)
    (M' := LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t))
    (fun j => ((fun _ => j 0), (fun _ => j 0))) (wchart_le_tw L π N t) (lcg_tw L π N t) σ, fun h => hi ?_⟩
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  have hc := (LB.isLB_linComb hL (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t)).cover
  have hy : y ∈ ⨆ j, (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1 + N * t)).U j := by
    rw [hc]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  haveI : Nonempty (LB.wchart L (fun _ : Fin 1 => π) j) := ⟨⟨y, hj⟩⟩
  exact sec_eq_zero σ (wchart_le_tw L π N t j) (congrFun h j) i

theorem exists_sq_eq (K : Type) [Field K] (N : ℕ) (hN : 1 ≤ N) (t₀ : ℤ) :
    ∃ (n : ℕ) (t : ℤ), (n : K) ≠ 0 ∧ t₀ ≤ t ∧ ((n ^ 2 * 1 : ℕ) : ℤ) = 1 + N * t := by
  have key : ∃ a : ℕ, t₀ ≤ a ∧ ((1 + N * a : ℕ) : K) ≠ 0 := by
    obtain ⟨p, hp⟩ := CharP.exists K
    rcases CharP.char_is_prime_or_zero K p with h | h
    · refine ⟨p * t₀.toNat, ?_, ?_⟩
      · have h1 : t₀.toNat ≤ p * t₀.toNat := Nat.le_mul_of_pos_left _ h.pos
        have h2 := Int.self_le_toNat t₀
        omega
      · push_cast
        rw [CharP.cast_eq_zero K p]
        simp
    · subst h
      haveI := CharP.charP_to_charZero K
      exact ⟨t₀.toNat, Int.self_le_toNat t₀, Nat.cast_ne_zero.2 (by omega)⟩
  obtain ⟨a, ha, hK⟩ := key
  refine ⟨1 + N * a, 2 * a + N * a ^ 2, hK, ?_, ?_⟩
  · have h1 : (0 : ℤ) ≤ a := Int.natCast_nonneg a
    have h2 : (0 : ℤ) ≤ N * a ^ 2 := by positivity
    omega
  · push_cast
    ring

theorem one_le_finrank_secM :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), 1 ≤ Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) := by
  intro K _ _ P
  let T : Over (Spec (CommRingCat.of K)) := baseOver (Spec (CommRingCat.of K))
  let π : (T ⊗ P.A).left ⟶ P.A.left := (snd T P.A).left
  let f : (T ⊗ P.A).left ⟶ Spec (CommRingCat.of K) := (fst T P.A).left
  have hpb : IsPullback π f P.A.hom (𝟙 _) := (IsPullback.of_hasPullback T.hom P.A.hom).flip
  obtain ⟨N, hN, m, s, hH, hs⟩ :=
    GlobalTheory.AbLaw.polAV_veryAmpleBy GlobalTheory.laws_without_cohomology.2.2.1 _ P K (𝟙 _) _ π f hpb
  have hgi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom
    P.isAb.smooth P.isAb.geomConnected
  haveI : IsIntegral (T ⊗ P.A).left := GeometricallyIntegral.geometrically_isIntegral _ _ _ hpb
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.exists_high_twist_section_ne_zero K _ f _ m s (P.L.pull π) hH (LB.isLB_pull P.isLB π) hs
  obtain ⟨n, t, hn, ht, hnt⟩ := exists_sq_eq K N hN t₀
  obtain ⟨σ, i, hi⟩ := ht₀ t ht
  obtain ⟨τ, hτ⟩ := exists_sec_ne_zero P.L π P.isLB N t σ i hi
  have hbig : Nontrivial (SecM P.A P.L (1 + N * t) T) :=
    ⟨SecM.ofSec P.A τ, 0, fun h => hτ (congrArg Subtype.val h)⟩
  rw [← hnt] at hbig
  obtain ⟨e⟩ := (GlobalTheory.AbLaw.FromCube.all_of_cubeGen CubeAssembly.cube_gen).2.2.2.2.2.2.2.2.2 K P n 1 hn le_rfl
  have hone : Nontrivial (SecM P.A P.L ((1 : ℕ) : ℤ) T) := by
    by_contra h
    haveI := not_nontrivial_iff_subsingleton.1 h
    exact not_subsingleton _ e.toEquiv.subsingleton
  have hfin := (CubeAssembly.sections_growth K P).1 1
  letI : Field Γ(T.left, ⊤) :=
    (isField_of_isIntegral_of_subsingleton (Spec (CommRingCat.of K))).toField
  exact Module.finrank_pos (R := Γ(T.left, ⊤)) (M := SecM P.A P.L ((1 : ℕ) : ℤ) T)

end GlobalTheory.PolSection
