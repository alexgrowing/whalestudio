import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.AmpSub

def chartPullPw {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (t : ℤ) :
    ChartPull (AbLaw.pw (L.pull f) t) (AbLaw.pw L t) f where
  idx J := J PUnit.unit
  le _ _ hy := mem_pull.1 hy
  g y J J' hJ hJ' := (map_zpow _ _ _).trans
    ((congrArg (· ^ t) ((Geo.Tor.chartPullPull L f f rfl).g y J J' hJ hJ')).trans (map_zpow _ _ _).symm)

theorem hasGen_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i : L.ι)
    (h : ∀ y, f y ∈ L.U i) : MulPull.HasGen L (K := PUnit) (fun _ => f) (fun _ => 1) := by
  have le : ∀ J : PUnit → L.ι, (L.pull f).U J ≤ f ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U i) :=
    fun J y hy => ⟨mem_pull.1 hy, h y⟩
  refine ⟨⟨fun J => res (le J) (pullU f _ (L.g (J PUnit.unit) i))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans (gm_rp₁ f y _ _ (le J) hy.1 _)).trans (Eq.symm ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) (gm_pull_g L f (𝟙 Y) y J J' hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (gm_rp₁ f y _ _ (le J') hy.2 _))).trans ?_)))
  rw [Category.id_comp]
  exact gm_cocycle hL f y (mem_pull.1 hy.1) (mem_pull.1 hy.2) (h y)

theorem exists_chart_local {X S : Scheme.{0}} {L : LB X} (hL : L.IsLB) [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    (f : S ⟶ X) : ∃ i, ∀ y, f y ∈ L.U i := by
  obtain ⟨i, hi⟩ := exists_chart hL ((S.isoSpec.inv ≫ f) (IsLocalRing.closedPoint Γ(S, ⊤)))
  have e : (S.isoSpec.inv ≫ f) ⁻¹ᵁ L.U i = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 hi
  refine ⟨i, fun y => ?_⟩
  have : S.isoSpec.hom y ∈ (S.isoSpec.inv ≫ f) ⁻¹ᵁ L.U i := by rw [e]; trivial
  have h2 : (S.isoSpec.hom ≫ S.isoSpec.inv ≫ f) y ∈ L.U i := this
  rwa [Iso.hom_inv_id_assoc] at h2

theorem psum_comp {S : Scheme.{0}} {N G : Over S} [GrpObj N] [GrpObj G] (ν : N ⟶ G) [IsMonHom ν]
    {T' T : Over S} {n : ℕ} (x : Fin n → (T' ⟶ N)) (y : Fin n → (T ⟶ G)) (h : T' ⟶ T)
    (e : ∀ k, x k ≫ ν = h ≫ y k) (I : Finset (Fin n)) : psum N x I ≫ ν = h ≫ psum G y I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact (MonObj.one_comp ν).trans (MonObj.comp_one h).symm
  | cons k l ih =>
    exact (MonObj.mul_comp _ _ ν).trans ((congrArg₂ (· * ·) (e k) ih).trans (MonObj.comp_mul h _ _).symm)

theorem ampleCub_pull_and_pullPow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), AmpleCub G L → (∀ (N : Over S) [GrpObj N] (ν : N ⟶ G), IsMonHom ν → IsClosedImmersion ν.left → AmpleCub N (L.pull ν.left)) ∧ (IsLocalRing Γ(S, ⊤) → IsAffine S → ∀ n : ℕ, PullPow ((𝟙 G) ^ n).left L ((n : ℤ) ^ 2)) := by
  intro S G _ _ L ⟨hL, ⟨c, hc⟩, ⟨s, hs⟩, n, hn, ha⟩
  refine ⟨fun N _ ν hν hcl => ⟨pull_isLB hL _, ?_, ?_, n, hn, fun x => ?_⟩, fun _ _ m => ?_⟩
  · refine gen_chartPull (chartPullLinComb L ν.left _ _ _ (ν ⊗ₘ ν ⊗ₘ ν).left fun I => ?_) c hc
    refine congrArg (fun z => z.left) (psum_comp ν (x3 N) (x3 G) (ν ⊗ₘ ν ⊗ₘ ν) (fun k => ?_) I.down)
    fin_cases k <;> simp [x3]
  · refine gen_chartPull (chartPullLinComb L ν.left _ _ _ ν.left fun k => ?_) s hs
    fin_cases k
    · exact congrArg (fun z => z.left) (GrpObj.inv_hom ν)
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · obtain ⟨σ, hx, hσ⟩ := ha (ν.left x)
    have e : Out.nonzeroLocus (chartSec (chartPullPw L ν.left n) σ) = ν.left ⁻¹ᵁ Out.nonzeroLocus σ :=
      nonzeroLocus_chartSec _ σ fun y j hj => ⟨fun _ => j, mem_pull.2 hj⟩
    refine ⟨chartSec (chartPullPw L ν.left n) σ, ?_, ?_⟩ <;> rw [e]
    · exact hx
    · exact hσ.preimage _
  · have hcube : MulPull.HasGen L (thφ G (x3 G)) thε := ⟨c, hc⟩
    have hsym : MulPull.HasGen L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] := ⟨s, hs⟩
    obtain ⟨i, hi⟩ := exists_chart_local (S := S) hL (eSec G)
    have hrig := hasGen_of_chart hL (eSec G) i hi
    have h := MulPull.hasGen_pow hL hcube (𝟙 G) ((hrig.pull (toUnit G).left).of_formEq hL (fun U _ h => by
        simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
          Matrix.cons_val_zero, _root_.mul_one]
        rfl))
      (hsym.inv.of_formEq hL (fun U _ h => by
        rw [Fin.prod_univ_two, Fin.prod_univ_two, Hom.inv_def, Category.id_comp, mul_comm]
        rfl)) m
    refine h.inv.of_formEq hL fun U _ h => ?_
    rw [Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]
    rfl

end GlobalTheory.SS.AmpSub
end
