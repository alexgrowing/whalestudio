import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PhzEqFlat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfSec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbCos
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbKey

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
theorem phz_eq_flat_k {s₁ z : ℂ} {f : d.G → ℂ} : _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z = flat d.a f s₁ z := by
  funext x
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k, flat, _root_.PositivityTheory.SiegelWeilFormula.kunf.ht_eq_k]
theorem phz_law_k {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    Law d.χ (z - s₁ + (s₁ + (d.n : ℂ) / 2)) (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_eq_flat_k]
  exact Law.flat hf.law d.ok.hgt (_root_.PositivityTheory.SiegelWeilFormula.kunf.a_pos_k d) z
theorem phz_par_k {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {p : d.G} {t : GL (Fin d.n) (AE F E)}
    (hp : IsPar p t) (ht : Matrix.GeneralLinearGroup.det t = 1) (g : d.G) : _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (p * g) = _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z g := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_law_k hf z p t g hp, ht, map_one, map_one]
  simp
theorem phz_rat_k {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {p : d.G} (hp : p ∈ par2 σ d.Y)
    (hr : p ∈ rat2 σ d.Y) (g : d.G) : _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (p * g) = _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z g :=
  (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_law_k hf z).rat d.ok.hecke hp hr g
theorem key_id_k {nb : nA σ d.Y d.b → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb : IsNMap d.b nb)
    (hnb' : IsNMap L.b nb') {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (h : G2 σ L.Y) (β : nA σ d.Y d.b) (u : Fin L.n → AE F E)
    (x : d.G) : ∃ p t, IsPar p t ∧ Matrix.GeneralLinearGroup.det t = 1 ∧
      L.j h * (nb β * (uM u * x)) = p * (L.j (h * nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x) := by
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.key_id_pf_k L hnb hnb' hU h β u x
theorem tr_sub_k {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (β : nA σ d.Y d.b) :
    Matrix.trace (T.1.1 * β.1) = Matrix.trace (T'.1.1 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β).1) := by
  obtain ⟨h0, h1⟩ := hT
  have hout : ∀ i, i ∉ Set.range L.em → i = L.i₀ := fun i hi => by
    by_contra h
    exact hi ((L.rng i).1 h)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, h1, Matrix.submatrix_apply]
  symm
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun i hi => ?_) (fun a => ?_)
  · rw [hout i hi]
    simp [(h0 _).1]
  · refine Fintype.sum_of_injective L.em L.inj _ _ (fun k hk => ?_) (fun b => rfl)
    rw [hout k hk]
    simp [(h0 _).2]
theorem cos_bij_k : ∃ e : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd ≃ {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ∀ q', ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
    _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1 = p * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') := by
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.cos_bij_pf_k L
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
