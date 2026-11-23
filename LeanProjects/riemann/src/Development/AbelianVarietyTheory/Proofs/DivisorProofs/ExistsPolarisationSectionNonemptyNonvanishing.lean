import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusIffChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FibreTheta

theorem exists_sec_nonempty : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S),
    IsIntegral (Over.mk t ⊗ P.A).left → ∃ θ : LB.Sec (LB.LinComb P.L (K := Fin 1) ![(snd (Over.mk t) P.A).left] ![1]),
      (nonzeroLocus θ : Set (Over.mk t ⊗ P.A).left).Nonempty := by
  intro S P K _ t hI
  let T : Over S := Over.mk t
  obtain ⟨⟨b, hb⟩, -⟩ := GlobalTheory.abelianSchemeLaws_all.2.secTwist S P 1 le_rfl K t (1 : T ⟶ P.A)
  have := P.isAb.comm
  have e : translPt P.A (1 : T ⟶ P.A) = snd T P.A := by
    show (fst T P.A ≫ 1) * snd T P.A = _
    rw [MonObj.comp_one, _root_.one_mul]
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)

  have nz : ∃ j, (b i₀).f j ≠ 0 := by
    by_contra hz
    push_neg at hz
    obtain ⟨r, -, hu⟩ := hb (b i₀)
    have h0 : ∀ r' : Fin (1 ^ P.g) → Γ(T.left, ⊤), ∀ j, (b i₀).f j = ∑ i, ((T ⊗ P.A).left.presheaf.map
        (homOfLE le_top).op).hom ((fst T P.A).left.appTop.hom (r' i)) * (b i).f j := fun r' j => by
      rw [su, hz j, mul_zero]
    have := (hu (fun _ => 0) (h0 _)).trans (hu (fun _ => 1) (h0 _)).symm
    exact zero_ne_one ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective
      ((map_zero _).trans ((congrFun this i₀).trans (map_one _).symm)))
  obtain ⟨j, hj⟩ := nz
  haveI : IsReduced (T ⊗ P.A).left := inferInstance
  obtain ⟨y, hy⟩ : ∃ y, y ∈ (T ⊗ P.A).left.basicOpen ((b i₀).f j) := by
    by_contra h
    push_neg at h
    exact hj (eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy' => (h y hy').elim))
  have hy₀ : y ∈ nonzeroLocus (b i₀) := TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩
  have hF : FormEq (![(snd T P.A).left, (translPt P.A (1 : T ⟶ P.A)).left] : Fin 2 → _)
      ![((1 : ℕ) : ℤ) - 1, 1] (![(snd T P.A).left] : Fin 1 → _) ![1] := by
    intro U _ h
    rw [e]; simp [Fin.prod_univ_succ]
  obtain ⟨s, hs⟩ := exists_sec P.isLB hF (b i₀)
  choose J hJ using fun χ : (T ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ y)
  have hJ' : Good P.L y J := hJ
  refine ⟨s, y, ?_⟩
  show y ∈ nonzeroLocus s
  rw [GlobalTheory.AbVarProj.mem_nonzeroLocus_iff_sval s y hJ', hs _ (𝟙 _) y J hJ']
  exact (GlobalTheory.AbVarProj.mem_nonzeroLocus_iff_sval (b i₀) y hJ').1 hy₀

end GlobalTheory.FibreTheta
