import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFrameCol
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialFourierInversion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KappaModel

theorem finv_hat_neg_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψk : AddChar k Circle) (ν : Measure k), Continuous ψk → ψk ≠ 1 → ν.IsAddHaarMeasure → ∃ C : ℂ, ∀ c : Matrix n Unit k → ℂ, c ∈ SB (Matrix n Unit k) → ∀ Φ : Matrix Unit n k → ℂ, (∀ η, Φ η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c (Matrix.of fun r _ => y r)) (η ())) → GlobalTheory.KappaModel.finv ψk ν C Φ = c := by
  intro k _ _ _ _ _ _ n _ _ ψk ν hψ hne hν
  have := secondCountable k
  have := t2Space k
  let ψ' : AddChar k Circle :=
    { toFun := fun u => ψk (-u)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by intro a b; rw [neg_add, AddChar.map_add_eq_mul] }
  have hψ'app : ∀ u, ψ' u = ψk (-u) := fun _ => rfl
  have hψ' : Continuous ψ' := hψ.comp continuous_neg
  have hne' : ψ' ≠ 1 := by
    intro h
    apply hne
    refine DFunLike.ext _ _ fun u => ?_
    have := congrArg (fun χ : AddChar k Circle => χ (-u)) h
    simpa [hψ'app] using this
  obtain ⟨C', hC'pos, hC'⟩ :=
    GlobalTheory.LocFlat.PartialFourier.partial_fourier_inversion k ψ' ν hψ' hne' hν n
  refine ⟨((C' : ℂ))⁻¹, fun c hc Φ hΦ => ?_⟩
  funext x
  let e : (n → k) ≃ₜ Matrix n Unit k :=
    { toFun := fun y => Matrix.of fun r _ => y r
      invFun := fun M r => M r ()
      left_inv := fun _ => rfl
      right_inv := fun M => by ext i j; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  set g : (n → k) → ℂ := fun y => c (Matrix.of fun r _ => y r) with hgdef
  have hg : g ∈ SB (n → k) := ⟨hc.1.comp_continuous e.continuous, hc.2.comp_homeomorph e⟩
  let p : (n → k) × (Empty → k) ≃ₜ (n → k) := Homeomorph.prodUnique (n → k) (Empty → k)
  set f : (n → k) × (Empty → k) → ℂ := fun q => g q.1 with hfdef
  have hf : f ∈ SB ((n → k) × (Empty → k)) := ⟨hg.1.comp_continuous p.continuous, hg.2.comp_homeomorph p⟩
  set a : n → k := fun r => x r () with hadef
  obtain ⟨-, hinv⟩ := hC' Empty a f hf
  set μJ : Measure (Empty → k) := Measure.pi fun _ => ν with hμJ
  have hJ : μJ.real Set.univ = 1 := by
    rw [hμJ, Measure.pi_of_empty (x := (fun e => e.elim))]
    simp
  have h1 : ∀ l : n → k, ∫ q : (n → k) × (Empty → k), f q * (ψ' (l ⬝ᵥ q.1) : ℂ) ∂((Measure.pi fun _ => ν).prod μJ) =
      ∫ y : n → k, g y * (ψk (-1 * (l ⬝ᵥ y)) : ℂ) ∂(Measure.pi fun _ => ν) := by
    intro l
    rw [hfdef]
    simp only [hψ'app, neg_one_mul]
    rw [integral_fun_fst (f := fun y : n → k => g y * (ψk (-(l ⬝ᵥ y)) : ℂ)), hJ, one_smul]
  have h2 : ∫ y : Empty → k, f (a, y) ∂μJ = g a := by
    rw [hfdef]
    simp only
    rw [integral_const, hJ, one_smul]
  simp only [h1, h2] at hinv
  simp only [hψ'app, neg_neg] at hinv
  have h3 : g a = c x := by
    rw [hgdef]; congr 1
  have hC0 : (C' : ℂ) ≠ 0 := by exact_mod_cast hC'pos.ne'
  simp only [finv, hΦ]
  rw [← h3, show ∫ η : n → k, GlobalTheory.StepData.hat ψk ν (-1) g ((Matrix.of fun _ r => η r : Matrix Unit n k) ()) * (ψk (η ⬝ᵥ fun r => x r ()) : ℂ) ∂(Measure.pi fun _ => ν) = ∫ l : n → k, (ψk (l ⬝ᵥ a) : ℂ) * ∫ y : n → k, g y * (ψk (-1 * (l ⬝ᵥ y)) : ℂ) ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν) from by
    congr 1; funext η; rw [mul_comm]; rfl]
  rw [hinv]
  field_simp

end GlobalTheory.KappaModel
