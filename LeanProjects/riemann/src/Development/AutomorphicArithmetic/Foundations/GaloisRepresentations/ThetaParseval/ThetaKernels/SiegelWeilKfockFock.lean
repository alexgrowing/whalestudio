import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LiftExOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockAlg

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fockMem_k : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k := by
  intro F E _ _ _ _ _ σ d R
  exact ⟨_root_.PositivityTheory.SiegelWeilFormula.KFock.fock_le_k d R, fun w Ψ hΨ => ⟨fun P => _root_.PositivityTheory.SiegelWeilFormula.KFock.away_tens_k R w Ψ hΨ P, _root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ⟩, fun w f hf => _root_.PositivityTheory.SiegelWeilFormula.KFock.fock_dec_k R w f hf⟩
theorem T_sub_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Φ' : d.Fn) : d.T (Φ - Φ') = d.T Φ - d.T Φ' := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.T_add_k d (Φ - Φ') Φ'
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm
theorem T_inj_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) (e : d.T Φ = d.T Φ') : Φ = Φ' :=
  sub_eq_zero.mp ((hB F E σ d).2.2 _ (d.sch.sub_mem h h') (by rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.T_sub_k, e, sub_self]))
theorem linLift_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {V : Type} [AddCommGroup V] [Module ℂ V] (t : V →ₗ[ℂ] (Mx F E d.m d.n → ℂ))
    (ht : ∀ v, t v ∈ d.schM) : ∃ φ : V →ₗ[ℂ] d.Fn, ∀ v, φ v ∈ d.sch ∧ d.T (φ v) = t v := by
  choose φ0 hφ0 using fun v => (hB F E σ d).2.1 (t v) (ht v)
  refine ⟨{ toFun := φ0, map_add' := fun v v' => ?_, map_smul' := fun a v => ?_ }, fun v => hφ0 v⟩
  · refine _root_.PositivityTheory.SiegelWeilFormula.KFock.T_inj_k hB d (hφ0 (v + v')).1 (d.sch.add_mem (hφ0 v).1 (hφ0 v').1) ?_
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.T_add_k, (hφ0 _).2, (hφ0 _).2, (hφ0 _).2, map_add]
  · refine _root_.PositivityTheory.SiegelWeilFormula.KFock.T_inj_k hB d (hφ0 (a • v)).1 (d.sch.smul_mem a (hφ0 v).1) ?_
    rw [RingHom.id_apply, _root_.PositivityTheory.SiegelWeilFormula.KFock.T_smul_k, (hφ0 _).2, (hφ0 _).2, map_smul]
def tensP_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : PX d.m d.n →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun P := R.tens w (fP P) Ψ
  map_add' P Q := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, fP_add, Pi.add_apply, add_mul]
  map_smul' a P := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, fP_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
theorem liftEx_of_k : _root_.PositivityTheory.SiegelWeilFormula.TBij_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k := by
  intro hB hF F E _ _ _ _ _ σ d R w Ψ hΨ
  obtain ⟨φ, hφ⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.linLift_k hB d (_root_.PositivityTheory.SiegelWeilFormula.KFock.tensP_k R w Ψ) fun P => (hF F E σ d R).1 (((hF F E σ d R).2.1 w Ψ hΨ).1 P)
  exact ⟨φ, hφ⟩
theorem liftEx_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.liftEx_of_k hB _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k
theorem liftSw1_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (hf : IsSw f)
    (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) : ∃ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ :=
  (hB F E σ d).2.1 _ (_root_.PositivityTheory.SiegelWeilFormula.KFock.tens_mem_k d R w f hf Ψ hΨ)
end PositivityTheory.SiegelWeilFormula.KFock
end
end
