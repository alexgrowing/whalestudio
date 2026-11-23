import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LatSplit

open GlobalTheory.AdelicU.Supp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem singleTens_tmul (v : Pl F) (a : Fv F v) (x : E) :
    singleTens E v (a ⊗ₜ[F] x) = GlobalTheory.LatVac.liftV v a ⊗ₜ[F] x := rfl

theorem tmul_smul_gen_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {a : Fv F v}
    (ha : a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) {c : AF F} (hc : At (evFin F v) c)
    (hcv : evFin F v c ∈ v.adicCompletionIntegers F) {x : Fin n → E} (hx : x ∈ X.L) {y : Fin d → E} (hy : y ∈ W.L) :
    singleTens E v (a ⊗ₜ[F] (o : E)) • (c • incM F (Matrix.vecMulVec x y)) ∈ latAtV X W v := by
  refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a * c, ?_, ?_, o • x, X.L.smul_mem o hx, y, hy, ?_⟩
  · intro u hu
    rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u c, hc u hu, mul_zero]
  · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
    exact mul_mem ha hcv
  · ext i j
    simp only [singleTens_tmul, Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, smul_eq_mul,
      Pi.smul_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, inclR]
    change _ * ((c ⊗ₜ[F] (1:E)) * ((1:AF F) ⊗ₜ[F] (x i * y j))) =
      ((GlobalTheory.LatVac.liftV v a * c) ⊗ₜ[F] (1:E)) * ((1:AF F) ⊗ₜ[F] ((o:E) * x i * y j))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_assoc]

theorem singleTens_smul_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {y : Fv F v ⊗[F] E}
    (hy : y ∈ intLoc F E v) {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    singleTens E v y • γ ∈ latAtV X W v := by
  refine intLoc_induction (p := fun y => singleTens E v y • γ ∈ latAtV X W v) ?_ ?_ ?_ ?_ hy
  · intro a ha o
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, hcv, x, hx, y', hy', rfl⟩ := hz
      exact tmul_smul_gen_mem X W v ha o hc hcv hx hy'
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  · show singleTens E v 0 • γ ∈ latAtV X W v
    rw [map_zero, zero_smul]; exact zero_mem _
  · intro y z h h'
    show singleTens E v (y + z) • γ ∈ latAtV X W v
    rw [map_add, add_smul]; exact add_mem h h'
  · intro y h
    show singleTens E v (-y) • γ ∈ latAtV X W v
    rw [map_neg, neg_smul]; exact neg_mem h

theorem piW_splitIdemAd {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    piW t (splitIdemAd hcm t) = 1 ∧ piW (t.comp σ) (splitIdemAd hcm t) = 0 := by
  constructor
  · change splitProj t (compFin F E v (singleTens E v (splitIdem hcm t))) = 1
    rw [compFin_singleTens_self, splitProj_splitIdem]
  · change splitProj (t.comp σ) (compFin F E v (singleTens E v (splitIdem hcm t))) = 0
    rw [compFin_singleTens_self, splitProj_comp_splitIdem]

theorem latAtV_decomp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v), ∀ γ ∈ latAtV X W v,
      ∃ γ₁ ∈ latAtV X W v, ∃ γ₂ ∈ latAtV X W v, γ = γ₁ + γ₂ ∧ γ₁.map (piW (t.comp σ)) = 0 ∧ γ₂.map (piW t) = 0 := by
  intro F E _ _ _ _ _ σ n d hcm X W v t γ hγ
  have h1 : splitIdemAd hcm t • γ ∈ latAtV X W v := singleTens_smul_mem X W v (splitIdem_mem hcm t) hγ
  obtain ⟨e1, e0⟩ := piW_splitIdemAd hcm t
  refine ⟨splitIdemAd hcm t • γ, h1, γ - splitIdemAd hcm t • γ, sub_mem hγ h1, (add_sub_cancel _ _).symm, ?_, ?_⟩
  · ext i j
    simp [smul_eq_mul, e0]
  · ext i j
    simp [smul_eq_mul, e1]

end GlobalTheory.LatSplit
