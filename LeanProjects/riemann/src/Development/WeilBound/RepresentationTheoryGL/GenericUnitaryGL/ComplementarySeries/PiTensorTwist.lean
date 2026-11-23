import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarizableComplexRepOfSupercuspidalUnitaryCentralCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealExponentAbsSmoothCharacterLocalField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
  GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RgGu.NR

namespace Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prodIrr_congr {h N : ℕ} {y z : Fin h → IrrGL k} (e : y = z) (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (z a).1 = N) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr z hz)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem piTensor_twist (x : IrrGL k) (s : ℝ) :
    piTensor (fun a : Fin 2 => twist x.rep (detChar (Fin x.1) (absPow k (![-(s : ℂ), (s : ℂ)] a)))) =
      twist (piTensor fun _ : Fin 2 => x.rep) (chi k x.1 s) := by
  ext g : 1
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  have ht : ∀ {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
      (χ : GL (Fin n) k →* ℂˣ) (g : GL (Fin n) k), twist ρ χ g = ((χ g : ℂ) • ρ g) := fun _ _ _ => rfl
  have ht2 : ∀ (g : Levi k fun _ : Fin 2 => Fin x.1), twist (piTensor fun _ : Fin 2 => x.rep) (chi k x.1 s) g =
      ((chi k x.1 s g : ℂ) • (piTensor fun _ : Fin 2 => x.rep) g) := fun _ => rfl
  simp only [LinearMap.compMultilinearMap_apply, piTensor_tprod, ht, ht2, LinearMap.smul_apply]
  rw [MultilinearMap.map_smul_univ]
  congr 1
  simp [chi, Fin.prod_univ_two, Units.val_mul]

end Model

open Model in
theorem prodModel (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ProdModel k := by
  intro x s hd
  let π : ∀ a : Fin 2, Representation ℂ (GL (Fin x.1) k) x.2.rep.V :=
    fun a => twist x.rep (detChar (Fin x.1) (absPow k (![-(s : ℂ), (s : ℂ)] a)))
  have hs : ∀ a, IsSmooth (π a) := fun a => isSmooth_twist x.2.rep.smooth (isSmoothChar_absPow _).detChar
  have hi : ∀ a, (π a).IsIrreducible := fun a => isIrreducible_twist x.2.rep.irr _
  have e1 := prodIrrEquiv (d := fun _ : Fin 2 => x.1) (sum_two x.1) π hs hi
  have hy : (fun a => IrrGL.of (π a) (hs a) (hi a)) = ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] := by
    funext a
    have key : ∀ c : ℂ, IrrGL.of (twist x.rep (detChar (Fin x.1) (absPow k c))) (isSmooth_twist x.2.rep.smooth
        (isSmoothChar_absPow c).detChar) (isIrreducible_twist x.2.rep.irr _) = x.nu c := fun c =>
      (IrrGL.tw_of x.rep x.2.rep.smooth x.2.rep.irr (absPow k c) (isSmoothChar_absPow c)).symm.trans
        (congrArg (fun y => IrrGL.tw y (absPow k c) (isSmoothChar_absPow c)) (IrrGL.of_rep x))
    fin_cases a
    · exact key _
    · exact key _
  obtain ⟨e2⟩ := prodIrr_congr hy (sum_two x.1) hd
  have e3 : (multiProd (stdBlocks (fun _ : Fin 2 => x.1) (sum_two x.1)) π).Equiv
      (parInd (blk2 x.1) (twist (piTensor fun _ : Fin 2 => x.rep) (chi k x.1 s))) :=
    parIndEquiv (blk2 x.1) ((piTensor_twist x s) ▸ Representation.Equiv.refl _)
  exact ⟨(e2.symm.trans e1.symm).trans e3⟩

theorem cuspUnit (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    CuspUnit k := by
  intro y hy
  obtain ⟨ω, hωs, hω⟩ := exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr
  obtain ⟨s, hs⟩ := GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow k ω hωs
  have hN : (y.1 : ℝ) ≠ 0 := by exact_mod_cast hy.1.ne'
  refine ⟨y.nu ((-(s / y.1) : ℝ) : ℂ), s / y.1, hy.nu _, ?_, ?_⟩
  · have hρc : (y.nu ((-(s / y.1) : ℝ) : ℂ)).IsCusp := hy.nu _
    have hcc := UnitaryOrder.hasCentralChar_nu y hω ((-(s / y.1) : ℝ) : ℂ)
    have hi := (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.irr
    have hsm := (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.smooth
    haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hi
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.V)
    obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hsm (GlobalTheory.SqIntUnit.compactOpen_basis k _) hv₀
    refine GlobalTheory.isUnitarisable_of_isSupercuspidal _ _ _ (l : Module.Dual ℂ _) l.2
      (fun e => hl (by rw [e]; rfl)) hi (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k _ _ _ hρc.2) ?_
    intro g hg
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨a, rfl⟩ := hg
    refine ⟨_, ?_, hcc a⟩
    have h1 := UnitaryOrder.log_norm_mul_absPow ω (-(s / y.1)) y.1 a
    have hpos := nabs_pos' k a
    rw [hs a, Real.log_rpow hpos] at h1
    have h2 : Real.log ‖(((ω * absPow k ((-(s / y.1) : ℝ) : ℂ) ^ y.1) a : ℂˣ) : ℂ)‖ = 0 := by
      rw [h1]; field_simp; ring
    exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.2 (Units.ne_zero _)) h2
  · rw [IrrGL.nu_nu, show ((-(s / y.1) : ℝ) : ℂ) + ((s / y.1 : ℝ) : ℂ) = 0 by push_cast; ring, IrrGL.nu_zero]

end PositivityTheory.RgGu.NR

end
