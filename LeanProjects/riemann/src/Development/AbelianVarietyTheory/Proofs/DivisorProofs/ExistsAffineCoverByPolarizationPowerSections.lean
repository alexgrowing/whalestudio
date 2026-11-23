import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleCover

variable {X : Scheme.{0}} (U : X.Opens) (hU : U = ⊤)

noncomputable def backTop : X ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (𝟙 X) (by
    rw [Scheme.Opens.range_ι, hU]; exact Set.subset_univ _)

theorem backTop_ι : backTop U hU ≫ U.ι = 𝟙 X := IsOpenImmersion.lift_fac _ _ _

theorem backTop_apply (y : X) : U.ι (backTop U hU y) = y :=
  congrArg (fun g : X ⟶ X => g y) (backTop_ι U hU)

instance : IsIso (backTop U hU) :=
  ⟨⟨U.ι, backTop_ι U hU, by rw [← cancel_mono U.ι, Category.assoc, backTop_ι, Category.comp_id, Category.id_comp]⟩⟩

end GlobalTheory.AmpleCover

namespace GlobalTheory.AmpleCover

variable {S : Scheme.{0}} (A : Over S) (L : LB A.left) (N : ℕ)

theorem gm_pow_congr {y : A.left} {r : A.left ⟶ A.left} (hr : r = 𝟙 A.left) (a b : L.ι) :
    gm (𝟙 A.left) y (L.U a ⊓ L.U b) (L.g a b) ^ N = gm r y (L.U a ⊓ L.U b) (L.g a b) ^ N := by
  subst hr; rfl

def chartPullPowTop :
    ChartPull (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 A.left) fun _ => (N : ℤ)) (powOver A L ⊤ N)
      (backTop (A.hom ⁻¹ᵁ ⊤) (by simp)) where
  idx j := fun _ => (j : Fin 1 → L.ι) 0
  le j y hy := Set.mem_iInter.2 fun _ => by
    have e := backTop_apply (A.hom ⁻¹ᵁ ⊤) (by simp) y
    have hy' : y ∈ L.U ((j : Fin 1 → L.ι) 0) := Set.mem_iInter.1 hy 0
    show (A.hom ⁻¹ᵁ ⊤).ι (backTop (A.hom ⁻¹ᵁ ⊤) (by simp) y) ∈ L.U ((j : Fin 1 → L.ι) 0)
    rw [e]; exact hy'
  g y j j' hj hj' := by
    have hb : ∀ (i : Fin 1 → L.ι), y ∈ L.U (i 0) →
        backTop (A.hom ⁻¹ᵁ ⊤) (by simp) y ∈ (powOver A L ⊤ N).U (fun _ => i 0) := fun i hi =>
      Set.mem_iInter.2 fun _ => by
        have e := backTop_apply (A.hom ⁻¹ᵁ ⊤) (by simp) y
        show (A.hom ⁻¹ᵁ ⊤).ι (backTop (A.hom ⁻¹ᵁ ⊤) (by simp) y) ∈ L.U (i 0)
        rw [e]; exact hi
    refine (gm_linComb L _ _ (𝟙 _) y j j' hj hj').trans (Eq.trans ?_
      (gm_linComb L (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1) _ y _ _
        (hb j (Set.mem_iInter.1 hj 0)) (hb j' (Set.mem_iInter.1 hj' 0))).symm)
    rw [Fintype.prod_unique]
    simp only [backTop_ι, Category.id_comp, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      zpow_natCast]
    exact gm_pow_congr A L N (backTop_ι _ _) _ _

end GlobalTheory.AmpleCover

open GlobalTheory.AmpleCover in

theorem GlobalTheory.AmpleCover.exists_affine_cover_secM : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∃ (k : ℕ) (I : Type) (s : I → SecM (𝟙 P₀.A.left) P₀.L k), 1 ≤ k ∧ ⨆ i, Out.nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧ ((Out.nonzeroLocus (s i) : P₀.A.left.Opens) : Set P₀.A.left).Nonempty := by
  intro K _ P₀
  obtain ⟨N, hN, M, s, hcov, hs⟩ := P₀.ample ⊤ (isAffineOpen_top _)
  have hT : P₀.A.hom ⁻¹ᵁ ⊤ = ⊤ := by simp
  let a := chartPullPowTop P₀.A P₀.L N
  have loc : ∀ i, Out.nonzeroLocus (GlobalTheory.chartSec a (s i)) = backTop _ hT ⁻¹ᵁ Out.nonzeroLocus (s i) := fun i =>
    GlobalTheory.nonzeroLocus_chartSec a (s i) fun y j hj => by
      have h0 : (P₀.A.hom ⁻¹ᵁ ⊤).ι (backTop _ hT y) ∈ P₀.L.U ((j : Fin N → P₀.L.ι) ⟨0, hN⟩) :=
        Set.mem_iInter.1 hj ⟨0, hN⟩
      rw [backTop_apply] at h0
      exact ⟨fun _ => (j : Fin N → P₀.L.ι) ⟨0, hN⟩, Set.mem_iInter.2 fun _ => h0⟩
  refine ⟨N, {i : Fin (M + 1) // ((Out.nonzeroLocus (GlobalTheory.chartSec a (s i)) : P₀.A.left.Opens) : Set P₀.A.left).Nonempty},
    fun i => GlobalTheory.chartSec a (s i.1), hN, ?_, fun i => ⟨?_, i.2⟩⟩
  · refine eq_top_iff.2 fun y _ => ?_
    have hy : backTop _ hT y ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    have hy' : y ∈ Out.nonzeroLocus (GlobalTheory.chartSec a (s i)) := by rw [loc]; exact hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, y, hy'⟩, hy'⟩
  · show IsAffineOpen (Out.nonzeroLocus (GlobalTheory.chartSec a (s i.1)))
    rw [loc]
    exact (hs i.1).1.preimage _
