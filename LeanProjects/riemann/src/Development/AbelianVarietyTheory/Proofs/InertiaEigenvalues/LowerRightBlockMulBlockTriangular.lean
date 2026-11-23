import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix

namespace GlobalTheory.FirstBlocksReduction

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ExportSeries GlobalTheory.FlatVecSum

variable {D : D7} {S T : HSp D}
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem exists_reps {G X : Type} [Group G] (J J' : Subgroup G) (φ : G → X) (A : Set X) (hA : A.Finite)
    (hφ : ∀ κ ∈ J, φ κ ∈ A) (h : ∀ u ∈ J, ∀ κ ∈ J, u⁻¹ * κ ∈ J' ↔ φ u = φ κ) :
    ∃ F : Finset G, (∀ u ∈ F, u ∈ J) ∧ ∀ κ ∈ J, ∃! u : G, u ∈ F ∧ u⁻¹ * κ ∈ J' := by
  classical
  have hfin : (φ '' (J : Set G)).Finite := hA.subset (by rintro _ ⟨κ, hκ, rfl⟩; exact hφ κ hκ)
  have hs : ∀ x : ↥(φ '' (J : Set G)), ∃ u, u ∈ J ∧ φ u = x.1 := fun x => x.2
  choose s hsJ hsφ using hs
  haveI := hfin.fintype
  refine ⟨Finset.univ.image s, fun u hu => ?_, fun κ hκ => ⟨s ⟨φ κ, κ, hκ, rfl⟩, ⟨?_, ?_⟩, ?_⟩⟩
  · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hu
    exact hsJ x
  · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · exact (h _ (hsJ _) _ hκ).2 (hsφ _)
  · rintro u ⟨hu, hu'⟩
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hu
    congr 1
    exact Subtype.ext ((hsφ x).symm.trans ((h _ (hsJ x) _ hκ).1 hu'))

theorem extension_by_one_mul {G H : Type} [Group G] [Monoid H] (K : Subgroup G) (f : K →* H) {a b : G} (ha : a ∈ K) (hb : b ∈ K) :
    ext1 K f (a * b) = ext1 K f a * ext1 K f b := by
  unfold ext1
  rw [dif_pos ha, dif_pos hb, dif_pos (mul_mem ha hb), ← map_mul]
  rfl

theorem lowerRightBlock_mul_blockTriangular {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) {a b : GL (Fin n) κ} (ha : a ∈ blockTri (blk2 r))
    (hb : b ∈ blockTri (blk2 r)) : upperLeftBlock hr (a * b) = upperLeftBlock hr a * upperLeftBlock hr b :=
  extension_by_one_mul _ _ ha hb

def firstBlocks (B : Base S T) (ψ : Twist D Circle) (k : Bridge.Gf S) : G0 B.G.Pg T.rank :=
  rTup B.F.βS (B.levS ψ) (Formalism.UG.bc (Lev.swapAE D) k.1)

theorem firstBlocks_mul (B : Base S T) (ψ : Twist D Circle) {a b : Bridge.Gf S} (ha : a ∈ B.levJ ψ) (hb : b ∈ B.levJ ψ) :
    firstBlocks B ψ (a * b) = firstBlocks B ψ a * firstBlocks B ψ b := by
  have pa := lev_le_parLev ha
  have pb := lev_le_parLev hb
  funext PP
  show upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) (a.1 * b.1))) =
    upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1)) * upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) b.1))
  have e : redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1 * Formalism.UG.bc (Lev.swapAE D) b.1) =
      redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1) * redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) b.1) :=
    extension_by_one_mul (St B.F.βS) (redAt B.F.βS PP.1) (Base.mem_St_of_mem_levJ ha) (Base.mem_St_of_mem_levJ hb)
  rw [map_mul, e]
  exact lowerRightBlock_mul_blockTriangular _ (blockTri_blkOf_le _ _ (parLev_g pa PP.2)) (blockTri_blkOf_le _ _ (parLev_g pb PP.2))

theorem mem_princ_iff (B : Base S T) (ψ : Twist D Circle) {k : Bridge.Gf S} (hk : k ∈ B.levJ ψ) :
    k ∈ (princ B).levJ ψ ↔ firstBlocks B ψ k = 1 :=
  ⟨fun h => Subgroup.mem_bot.1 h.2, fun h => ⟨mem_parLev.2 (by exact mem_parLev.1 hk.1), Subgroup.mem_bot.2 h⟩⟩

theorem exists_reps_levJ : ∀ {D : Formalism.BasicNotions.D7} {S T : Formalism.BasicNotions.TH.HSp D} (B : GlobalTheory.ExportSeries.Base S T), GlobalTheory.ExportSeries.Base.Good B → ∀ (ψ : GlobalTheory.ExportSeries.Twist D Circle), GlobalTheory.ExportSeries.Base.admitted B (GlobalTheory.ExportSeries.Twist.Q ψ) → ∃ (F : Finset ↥(Formalism.IndefR.Bridge.Gf S)), (∀ u ∈ F, u ∈ GlobalTheory.ExportSeries.Base.levJ B ψ) ∧ ∀ κ ∈ GlobalTheory.ExportSeries.Base.levJ B ψ, ∃! u : ↥(Formalism.IndefR.Bridge.Gf S), u ∈ F ∧ u⁻¹ * κ ∈ GlobalTheory.ExportSeries.Base.levJ (GlobalTheory.FlatVecSum.princ B) ψ := by
  intro D S T B _ ψ _
  refine exists_reps _ _ (firstBlocks B ψ) (B.G.P.H : Set _) (Set.finite_coe_iff.1 (finite_H B.G.P)) (fun κ hκ => hκ.2)
    fun u hu κ hκ => ?_
  have hm := mul_mem (inv_mem hu) hκ
  have e := firstBlocks_mul B ψ hu hm
  rw [mul_inv_cancel_left] at e
  rw [mem_princ_iff B ψ hm, e]
  exact left_eq_mul.symm

end GlobalTheory.FirstBlocksReduction

end
