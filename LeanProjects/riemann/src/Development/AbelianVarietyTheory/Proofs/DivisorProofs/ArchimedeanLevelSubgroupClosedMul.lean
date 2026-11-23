import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt

noncomputable section

namespace GlobalTheory.KInfGroup

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {d : ℕ} {W : Spc F E d}

theorem mat_mul' (g h : UA σ W.J) : mat (g * h) = mat g * mat h := rfl

theorem mat_inj {g h : UA σ W.J} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

variable (F) in

def eInf : AF F := (1, 0)

variable (F) in

def eFin : AF F := (0, 1)

theorem unit_split : eInf F + eFin F = 1 := by
  refine Prod.ext ?_ ?_
  · show (1 : InfiniteAdeleRing F) + 0 = 1
    exact add_zero _
  · show (0 : FiniteAdeleRing (𝓞 F) F) + 1 = 1
    exact zero_add _

theorem evI_eFin : evI F (eFin F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
  exact map_zero _

theorem eInf_fin : (eInf F).2 = 0 := rfl

end GlobalTheory.KInfGroup

namespace GlobalTheory

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem kInf_one_mul_commute_finPt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ, ∀ k' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ, k * k' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ) ∧ ∀ l ∈ GlobalTheory.ThKAdm.FinPt σ W, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ, l * k = k * l := by
  intro F E _ _ _ _ _ σ d W τ
  refine ⟨⟨fun u _ => ?_, fun w => ?_⟩, fun k hk k' hk' => ⟨fun u hu => ?_, fun w => ?_⟩, fun l hl k hk => ?_⟩
  · show u • (mat (1 : UA σ W.J) - 1) = 0
    rw [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, smul_zero]
  · show Commute ((mat (1 : UA σ W.J)).map (piInf (τ w))) (W.θ w)
    rw [show mat (1 : UA σ W.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Commute.one_left _
  · show u • (mat (k * k') - 1) = 0
    have e : mat (k * k') - 1 = (mat k - 1) * mat k' + (mat k' - 1) := by
      rw [GlobalTheory.KInfGroup.mat_mul', Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul, hk.1 u hu, hk'.1 u hu, Matrix.zero_mul, add_zero]
  · show Commute ((mat (k * k')).map (piInf (τ w))) (W.θ w)
    rw [GlobalTheory.KInfGroup.mat_mul', Matrix.map_mul]
    exact (hk.2 w).mul_left (hk'.2 w)
  · apply GlobalTheory.KInfGroup.mat_inj
    rw [GlobalTheory.KInfGroup.mat_mul', GlobalTheory.KInfGroup.mat_mul']
    set A := mat l - 1 with hA
    set B := mat k - 1 with hB
    have hlA : GlobalTheory.KInfGroup.eInf F • A = 0 := hl _ GlobalTheory.KInfGroup.eInf_fin
    have hkB : GlobalTheory.KInfGroup.eFin F • B = 0 := hk.1 _ GlobalTheory.KInfGroup.evI_eFin
    have hA' : A = GlobalTheory.KInfGroup.eFin F • A := by
      conv_lhs => rw [← one_smul (AF F) A, ← GlobalTheory.KInfGroup.unit_split, add_smul, hlA, zero_add]
    have hB' : B = GlobalTheory.KInfGroup.eInf F • B := by
      conv_lhs => rw [← one_smul (AF F) B, ← GlobalTheory.KInfGroup.unit_split, add_smul, hkB, add_zero]
    have hAB : A * B = 0 := by
      rw [hB', Matrix.mul_smul, ← Matrix.smul_mul, hlA, Matrix.zero_mul]
    have hBA : B * A = 0 := by
      rw [hA', Matrix.mul_smul, ← Matrix.smul_mul, hkB, Matrix.zero_mul]
    have el : mat l = A + 1 := by rw [hA]; abel
    have ek : mat k = B + 1 := by rw [hB]; abel
    rw [el, ek, add_mul, mul_add, mul_add, hAB, add_mul, mul_add, hBA]
    simp only [mul_one, one_mul, zero_add]
    abel

end GlobalTheory
