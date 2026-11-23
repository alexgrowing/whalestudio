import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RdLaw

variable {D : D7}

theorem finM_rfl (V : HSp D) (g : GA D V) : finM V rfl g = (Formalism.L2.Theta.mt V g).map (toEAf D) := by
  simp [finM]

theorem infM_eq (θ : InfFam D) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V rfl g τ = (Formalism.L2.Theta.mt V g).map ((θ τ).comp (infPart D)) := by
  simp [infM, Formalism.IndefR.Datum.compAt]; rfl

theorem infM_rfl (θ : InfFam D) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V rfl g τ = infMat D.sp.cm.sig V.gram (θ τ) g := by
  rw [infM_eq]; rfl

theorem mt_mul (V : HSp D) (g h : GA D V) : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  simp [Formalism.L2.Theta.mt, map_mul]

theorem finM_mul (V : HSp D) (g h : GA D V) : finM V rfl (g * h) = finM V rfl g * finM V rfl h := by
  simp only [finM_rfl, mt_mul, Matrix.map_mul]

theorem infM_mul (θ : InfFam D) (V : HSp D) (g h : GA D V) (τ) :
    infM θ V rfl (g * h) τ = infM θ V rfl g τ * infM θ V rfl h τ := by
  simp only [infM_eq, mt_mul, Matrix.map_mul]

theorem infM_fin (θ : InfFam D) (V : HSp D) (k : GA D V) (hk : k ∈ GfC V) (τ) : infM θ V rfl k τ = 1 := by
  have h : (infHom V k) = 1 := hk
  have h2 : (infHom V k).val = 1 := by rw [h]; rfl
  rw [infM_eq]
  have e : (Formalism.L2.Theta.mt V k).map ((θ τ).comp (infPart D)) = (infHom V k).val.map (θ τ) := rfl
  rw [e, h2, Matrix.map_one _ (map_zero _) (map_one _)]

theorem finM_inf (V : HSp D) (k : GA D V) (hk : k ∈ GinfC V) : finM V rfl k = 1 := by
  have h : (finHom V k) = 1 := hk
  have h2 : (finHom V k).val = 1 := by rw [h]; rfl
  rw [finM_rfl]
  have e : (Formalism.L2.Theta.mt V k).map (toEAf D) = (finHom V k).val.map
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) := rfl
  rw [e, h2, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.AdForm.RdLaw

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

theorem rat_mt (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    ∃ γ0 : GL (Fin V.rank) D.host.E, γ0 ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram ∧
      Formalism.L2.Theta.mt V γ = γ0.val.map (incA D) := by
  have h : matHom V γ ∈ HFin (AF D.host.F) D.sp.cm.sig V.gram := hγ
  obtain ⟨γ0, h0, e⟩ := Subgroup.mem_map.1 h
  refine ⟨γ0, h0, ?_⟩
  show (matHom V γ).val = _
  rw [← e]; rfl

theorem rat_finM (V : HSp D) (γ0 : GL (Fin V.rank) D.host.E) (γ : GA D V) (e : Formalism.L2.Theta.mt V γ = γ0.val.map (incA D)) :
    finM V rfl γ = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0).val := by
  rw [finM_rfl, e, Matrix.map_map]; rfl

theorem rat_infM (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (γ0 : GL (Fin V.rank) D.host.E) (γ : GA D V)
    (e : Formalism.L2.Theta.mt V γ = γ0.val.map (incA D)) (τ) :
    infM θ V rfl γ τ = atInf (embT D) γ0.val τ := by
  rw [infM_eq, e, Matrix.map_map]
  ext i j
  simp only [Matrix.map_apply, atInf, Function.comp_apply, RingHom.coe_comp]
  exact (hθ τ).1 _

end GlobalTheory.AdForm.RdLaw

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

def e0 (D : D7) : AF D.host.F := ((0, 1) : Ainf D.host.F × Af D.host.F)

theorem finiteAdeleIdempotentOfF_mul_self : e0 D * e0 D = e0 D := Prod.ext (zero_mul _) (one_mul _)

def eps (D : D7) : AE D := e0 D ⊗ₜ[D.host.F] (1 : D.host.E)

theorem eps_mul_self : eps D * eps D = eps D := by
  rw [eps, Algebra.TensorProduct.tmul_mul_tmul, mul_one, finiteAdeleIdempotentOfF_mul_self]

theorem eps_mul_one_sub : eps D * (1 - eps D) = 0 := by
  rw [mul_sub, mul_one, eps_mul_self, sub_self]

theorem one_sub_mul_self : (1 - eps D) * (1 - eps D) = 1 - eps D := by
  rw [sub_mul, one_mul, mul_sub, mul_one, eps_mul_self]; abel

theorem sig_eps : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig (eps D) = eps D := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig (_ ⊗ₜ _) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]; rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem infPart_eps : infPart D (eps D) = 0 := by
  have h1 : infPart D (eps D) = fstA D.host.F (e0 D) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E 1) :=
    Algebra.TensorProduct.map_tmul _ _ _ _
  have : fstA D.host.F (e0 D) = 0 := rfl
  rw [h1, this, TensorProduct.zero_tmul]

set_option synthInstance.maxHeartbeats 400000 in
theorem finPart_eps : finPart D (eps D) = 1 := by
  have h1 : finPart D (eps D) = sndA D.host.F (e0 D) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E 1) :=
    Algebra.TensorProduct.map_tmul _ _ _ _
  have : sndA D.host.F (e0 D) = 1 := rfl
  rw [h1, this]; rfl

theorem toEAf_eps : toEAf D (eps D) = 1 := by
  show (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) (finPart D (eps D)) = 1
  rw [finPart_eps, map_one]

def PM {r : ℕ} (M : Matrix (Fin r) (Fin r) (AE D)) : Matrix (Fin r) (Fin r) (AE D) :=
  eps D • M + (1 - eps D) • (1 : Matrix (Fin r) (Fin r) (AE D))

theorem PM_mul {r : ℕ} (M N : Matrix (Fin r) (Fin r) (AE D)) : PM (M * N) = PM M * PM N := by
  simp only [PM, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    eps_mul_self, one_sub_mul_self, eps_mul_one_sub, mul_comm (1 - eps D) (eps D), zero_smul, add_zero, zero_add]

theorem PM_one {r : ℕ} : PM (1 : Matrix (Fin r) (Fin r) (AE D)) = 1 := by
  simp only [PM, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.AdForm.RdLaw
