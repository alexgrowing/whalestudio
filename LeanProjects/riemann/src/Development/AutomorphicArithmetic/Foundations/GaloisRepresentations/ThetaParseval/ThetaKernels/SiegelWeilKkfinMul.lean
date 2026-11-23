import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.PolyKFinOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinBase
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinGsT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinVac
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinKc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinTDer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinVarB

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def Tl_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' Φ Ψ := funext fun X => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.add_apply, ← map_add]
    congr 1
    funext z
    exact mul_add _ _ _
  map_smul' c Φ := funext fun X => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.smul_apply, RingHom.id_apply, ← map_smul]
    congr 1
    funext z
    exact mul_left_comm _ _ _
def TK_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Submodule ℂ (Mx F E d.m d.n → ℂ) := (_root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d).map (_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d)
theorem D_dg_mem_k {Φ : d.Fn} (hΦ : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d) {Z : Mx F E d.m d.n} (hZ : At (evI F) Z) :
    Box.D (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d :=
  _root_.PositivityTheory.SiegelWeilFormula.KK.D_kfS_k (fun c hc => by rw [← Matrix.smul_mul, hZ c hc, Matrix.zero_mul]) hΦ
theorem mul_var_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : Fin d.m × Fin d.n × Bool) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) : (fun X => evX (MvPolynomial.X k) (R.loc w X) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  obtain ⟨Φ, hΦ, rfl⟩ := hf
  obtain ⟨Z₁, Z₂, c₁, c₂, h1, h2, e⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.var_span'_k R w k
  have hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨(c₁ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ +
    (c₂ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ,
    add_mem (Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.KK.D_dg_mem_k hΦ h1)) (Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.KK.D_dg_mem_k hΦ h2)), funext fun X => ?_⟩
  have t := congrFun ((_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d).map_add ((c₁ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ)
    ((c₂ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ)) X
  simp only [map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at t
  change d.T _ X = _ at t
  change d.T _ X = _ * d.T Φ X
  rw [t]
  change _ * d.T _ X + _ * d.T _ X = _
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_k (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k hΦ) h1, _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_k (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k hΦ) h2, e X]
  field_simp
theorem mul_pol_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (Q : PX d.m d.n) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) :
    (fun X => evX Q (R.loc w X) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  induction Q using MvPolynomial.induction_on generalizing f with
  | C a =>
    have : (fun X => evX (MvPolynomial.C a) (R.loc w X) * f X) = a • f := funext fun X => by
      simp [evX]
    rw [this]; exact Submodule.smul_mem _ _ hf
  | add p q hp hq =>
    have : (fun X => evX (p + q) (R.loc w X) * f X) = (fun X => evX p (R.loc w X) * f X) + fun X => evX q (R.loc w X) * f X :=
      funext fun X => by simp [evX, add_mul]
    rw [this]; exact add_mem (hp hf) (hq hf)
  | mul_X p k hp =>
    have : (fun X => evX (p * MvPolynomial.X k) (R.loc w X) * f X) =
        fun X => evX (MvPolynomial.X k) (R.loc w X) * (evX p (R.loc w X) * f X) := funext fun X => by
      simp only [evX, map_mul]; ring
    rw [this]; exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_var_k R w k (hp hf)
theorem mul_prod_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (P : InfinitePlace F → PX d.m d.n) (s : Finset (InfinitePlace F)) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) : (fun X => (∏ w ∈ s, evX (P w) (R.loc w X)) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | insert w s hw ih =>
    have : (fun X => (∏ w ∈ insert w s, evX (P w) (R.loc w X)) * f X) =
        fun X => evX (P w) (R.loc w X) * ((∏ w ∈ s, evX (P w) (R.loc w X)) * f X) := funext fun X => by
      rw [Finset.prod_insert hw, mul_assoc]
    rw [this]; exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_pol_k R w (P w) ih
theorem vac_mem_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ}
    (hg : g ∈ SB _) : _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  have hgen : _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g ∈ R.fock := Submodule.subset_span ⟨fun _ => 1, g, hg, funext fun X => by
    simp [_root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k, fP, evX]⟩
  obtain ⟨Φ, hΦ, e⟩ := (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 hgen)
  refine ⟨Φ, _root_.PositivityTheory.SiegelWeilFormula.KK.vac_kfS_k (_root_.PositivityTheory.SiegelWeilFormula.KK.thA_k R) (_root_.PositivityTheory.SiegelWeilFormula.KK.thB_k d R.ε) (fun k hk w => _root_.PositivityTheory.SiegelWeilFormula.KK.commute_thB_k R hk w) (fun _ => 1) hΦ fun u u' hu hu' hr => ?_, e⟩
  have m1 : Box.D (d.dd.e u') Φ ∈ d.sch := Box.DP_mem hΦ _ _
  have m2 : Box.D (d.dd.e u) Φ ∈ d.sch := Box.DP_mem hΦ _ _
  refine sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (sub_mem m1 (Submodule.smul_mem _ _ m2)) (funext fun X => ?_))
  have t := congrFun ((_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d).map_sub (Box.D (d.dd.e u') Φ) (Complex.I • Box.D (d.dd.e u) Φ)) X
  simp only [map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at t
  change d.T _ X = d.T _ X - Complex.I * d.T _ X at t
  rw [t, _root_.PositivityTheory.SiegelWeilFormula.KK.vac_rel_k R g hΦ e hu hu' hr X, sub_self]
  rfl
theorem fock_le_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨P, g, hg, rfl⟩
  have e : (fun X => (∏ w ∈ Finset.univ, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2) =
      fun X => (∏ w ∈ Finset.univ, evX (P w) (R.loc w X)) * _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g X := funext fun X => by
    simp only [fP, _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k, Finset.prod_mul_distrib]; ring
  rw [SetLike.mem_coe, e]
  exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_prod_k R P _ (_root_.PositivityTheory.SiegelWeilFormula.KK.vac_mem_k hT hF R hg)
theorem polyKFin_of_k : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k := by
  intro hT hF F E _ _ _ _ _ σ d R Φ hΦ hf
  obtain ⟨Φ', h', e⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.fock_le_k hT hF R hf
  have : Φ = Φ' := (sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (sub_mem hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k h')) (by
    rw [show d.T (Φ - Φ') = _root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d (Φ - Φ') from rfl, map_sub]
    exact sub_eq_zero.2 e.symm))).symm ▸ rfl
  rw [this]
  exact _root_.PositivityTheory.SiegelWeilFormula.KK.kFin_of_mem_k h'
end PositivityTheory.SiegelWeilFormula.KK
end
end
