import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataCubicalStructureValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiValuesThroughBundleIsoStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

theorem cmp_mul (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x y : N'.A) (j : Fin r) :
    cmp T ν ν' (x * y) j = cmp T ν ν' x j * cmp T ν ν' y j := by
  haveI := T.pr_hom j
  simp only [TensTor.cmp, map_mul]
  rw [← map_mul ν.eA.symm]
  congr 1
  exact GlobalTheory.TorusDefect.mul_comp_of_pullback (jK R) (T.pr j) (jFK F) (jFK F ≫ jK R) rfl (ν'.eA x) (ν'.eA y)

theorem cmp_bijective (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') : Function.Bijective (cmp T ν ν') := by
  constructor
  · intro x y h
    apply ν'.eA.injective
    refine Fan.IsLimit.hom_ext T.lim _ _ fun j => ?_
    have := congrFun h j
    simpa [TensTor.cmp] using this
  · intro f
    refine ⟨ν'.eA.symm (Fan.IsLimit.lift T.lim fun j => ν.eA (f j)), funext fun j => ?_⟩
    simp only [TensTor.cmp, MulEquiv.apply_symm_apply]
    refine (congrArg ν.eA.symm (Fan.IsLimit.fac T.lim _ j)).trans ?_
    simp

theorem chi_add (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ χ' : N'.X) (i : Fin r) :
    chi T ν ν' (χ + χ') i = chi T ν ν' χ i + chi T ν ν' χ' i := by
  simp [TensTor.chi, map_add]

theorem chi_bijective (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') : Function.Bijective (chi T ν ν') := by
  have : chi T ν ν' = ν'.eX.trans (T.xe.trans (AddEquiv.piCongrRight fun _ => ν.eX.symm)) := by
    funext χ i; rfl
  rw [this]; exact AddEquiv.bijective _

theorem cmp_c (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ' : N'.X) (j : Fin r) :
    cmp T ν ν' (N'.c χ') j = N.c (chi T ν ν' χ' j) := by
  simp only [TensTor.cmp, TensTor.chi]
  rw [ν.eA.symm_apply_eq, ν.c_eq, ν'.c_eq, ν.eX.apply_symm_apply]
  simp only [DegPre.cF, Category.assoc, T.c_pr]

theorem wv_ne_zero (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) : wv T ν ν' x ≠ 0 := by
  unfold TensTor.wv valF
  rw [dif_pos]
  · exact (((T.w.s _).isUnit.map _).map _).ne_zero
  · intro p _
    refine ⟨Set.mem_iInter.2 fun k => ?_, ν'.good _ trivial⟩
    exact ν.good ((ν'.eA x).left ≫ tensφ T.pr k) (show p ∈ (⊤ : (Sp F).Opens) from trivial)

end GlobalTheory.Mum.TensTor

open GlobalTheory.Mum.TensTor in

theorem GlobalTheory.Mum.TensTor.tensFacts_holds : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), TensFacts W (cmp T ν ν') (chi T ν ν') (wv T ν ν') := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν'
  exact ⟨cmp_mul T ν ν', cmp_bijective T ν ν', chi_add T ν ν', chi_bijective T ν ν', cmp_c T ν ν', wv_ne_zero T ν ν',
    GlobalTheory.T.tensorData_cubicalStructure_values R hB D D' W T F N N' ν ν', GlobalTheory.T.tensorData_psi_values_through_bundleIso R hB D D' W T F N N' ν ν'⟩

end
