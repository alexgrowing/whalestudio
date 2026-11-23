import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.AdelicLocalPoint

section Cut

variable {S : Type} [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι]

def cut (ε : S) (A : Matrix ι ι S) : Matrix ι ι S := ε • A + (1 - ε) • 1

theorem cut_mul {ε : S} (he : ε * ε = ε) (A B : Matrix ι ι S) : cut ε A * cut ε B = cut ε (A * B) := by
  have h1 : ε * (1 - ε) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h1' : (1 - ε) * ε = 0 := by rw [mul_comm, h1]
  have h2 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination he
  simp only [cut, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, he, h1,
    h1', h2, zero_smul, add_zero, zero_add]

theorem cut_one (ε : S) : cut ε (1 : Matrix ι ι S) = 1 := by
  rw [cut, ← add_smul, add_sub_cancel, one_smul]

theorem cut_transpose (ε : S) (A : Matrix ι ι S) : (cut ε A)ᵀ = cut ε Aᵀ := by
  simp [cut, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]

theorem cut_map {G : Type} [FunLike G S S] [RingHomClass G S S] (ε : S) (c : G) (hc : c ε = ε) (A : Matrix ι ι S) : (cut ε A).map c = cut ε (A.map c) := by
  ext i j
  simp only [cut, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> simp [hc]

theorem cut_mul_mul {ε : S} (he : ε * ε = ε) (A J B : Matrix ι ι S) :
    cut ε A * J * cut ε B = ε • (A * J * B) + (1 - ε) • J := by
  have h1 : ε * (1 - ε) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h1' : (1 - ε) * ε = 0 := by rw [mul_comm, h1]
  have h2 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination he
  simp only [cut, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, he, h1,
    h1', h2, zero_smul, add_zero, zero_add]

end Cut

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_one_mul_eq (v : Pl F) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem liftV_one_idem (v : Pl F) : GlobalTheory.LatVac.liftV v 1 * GlobalTheory.LatVac.liftV v 1 = (GlobalTheory.LatVac.liftV v 1 : AF F) := by
  rw [liftV_one_mul_eq, GlobalTheory.LatVac.evFin_liftV]

def idem (v : Pl F) : AE F E := algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)

theorem idem_mul (v : Pl F) : (idem v : AE F E) * idem v = idem v := by
  rw [idem, ← map_mul, liftV_one_idem]

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem mat_mul_inv (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  simp [mat]

theorem mat_inv_mul (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  simp [mat]

theorem mat_unitary (g : UA σ J) : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2

def atV (v : Pl F) (g : UA σ J) : UA σ J :=
  ⟨⟨cut (idem v) (mat g), cut (idem v) (mat g⁻¹),
    by rw [cut_mul (idem_mul v), mat_mul_inv, cut_one],
    by rw [cut_mul (idem_mul v), mat_inv_mul, cut_one]⟩, by
    have hc : (cA σ) (idem v) = idem v := (cA σ).commutes _
    show (cut (idem v) (mat g))ᵀ * incM F J * (cut (idem v) (mat g)).map (cA σ) = incM F J
    rw [cut_transpose, cut_map _ _ hc, cut_mul_mul (idem_mul v), mat_unitary, ← add_smul, add_sub_cancel, one_smul]⟩

theorem mat_atV (v : Pl F) (g : UA σ J) : mat (atV v g) = cut (idem v) (mat g) := rfl

end Adelic

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_eq_alg {ι : Type} (u : AF F) (B : Matrix ι ι (AE F E)) : u • B = algebraMap (AF F) (AE F E) u • B := by
  ext i j
  simp [Matrix.smul_apply, Algebra.smul_def]

theorem cut_sub_one {S ι : Type} [CommRing S] [Fintype ι] [DecidableEq ι] (ε : S) (A : Matrix ι ι S) :
    cut ε A - 1 = ε • (A - 1) := by
  simp only [cut, smul_sub, sub_smul, one_smul]
  abel

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

end Main

theorem localComponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d : ℕ) (W : Spc F E d) (hf : UA σ W.J), ∃ h : Pl F → UA σ W.J, ∀ v, h v ∈ UAt σ W (evFin F v) ∧
      ∀ u : AF F, At (evFin F v) u → u • mat (h v) = u • mat hf := by
  intro F E _ _ _ _ _ σ d W hf
  refine ⟨fun v => atV v hf, fun v => ⟨?_, ?_⟩⟩
  · intro w hw
    rw [mat_atV, cut_sub_one, smul_eq_alg, smul_smul, idem, ← map_mul, mul_comm, liftV_one_mul_eq, hw, map_zero,
      map_zero, zero_smul]
  · intro u hu
    have h1 : evFin F v (1 - GlobalTheory.LatVac.liftV v 1) = 0 := by
      rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self]
    have h2 : (1 - GlobalTheory.LatVac.liftV v 1) * u = 0 := hu _ h1
    have h3 : u * GlobalTheory.LatVac.liftV v 1 = u := by linear_combination -h2
    have h4 : u * (1 - GlobalTheory.LatVac.liftV v 1) = 0 := by linear_combination h2
    rw [mat_atV, smul_eq_alg, smul_eq_alg u (mat hf), cut, smul_add, smul_smul, smul_smul, idem, ← map_mul, h3,
      ← map_one (algebraMap (AF F) (AE F E)), ← map_sub, ← map_mul, h4, map_zero, zero_smul, add_zero]

end GlobalTheory.AdelicLocalPoint
