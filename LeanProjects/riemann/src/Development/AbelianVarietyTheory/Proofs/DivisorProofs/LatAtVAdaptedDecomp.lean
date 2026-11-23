import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictionAndProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosHomApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.ThK.AdaptEv.VacuumBlock.Dec

open GlobalTheory.ThK.AdaptEv.VacuumBlock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_add' {m k : Type} (A B : Matrix m k E) : incM F (A + B) = incM F A + incM F B := by
  ext i j; simp [incM]

theorem gen_mem_latAtV {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {v : Pl F} {a : AF F}
    (ha : At (evFin F v) a) (hi : evFin F v a ∈ v.adicCompletionIntegers F) {x : Fin n → E} {y : Fin d → E}
    (hx : x ∈ X.L) (hy : y ∈ W.L) : a • incM F (Matrix.vecMulVec x y) ∈ latAtV X W v :=
  AddSubgroup.subset_closure ⟨a, ha, hi, x, hx, y, hy, rfl⟩

theorem spanA_add {n d n₁ d₁ : ℕ} {H : Plane E n n₁} {H' : Plane E d d₁} {p p' : Matrix (Fin n) (Fin d) (AE F E)}
    (hp : p ∈ spanA (F := F) H H') (hp' : p' ∈ spanA (F := F) H H') : p + p' ∈ spanA (F := F) H H' := by
  obtain ⟨y, z, rfl⟩ := hp
  obtain ⟨y', z', rfl⟩ := hp'
  refine ⟨y + y', z + z', ?_⟩
  simp only [Matrix.add_vecMulVec, Matrix.mulVec_add, Matrix.vecMulVec_add]
  abel

theorem spanA_neg {n d n₁ d₁ : ℕ} {H : Plane E n n₁} {H' : Plane E d d₁} {p : Matrix (Fin n) (Fin d) (AE F E)}
    (hp : p ∈ spanA (F := F) H H') : -p ∈ spanA (F := F) H H' := by
  obtain ⟨y, z, rfl⟩ := hp
  refine ⟨-y, -z, ?_⟩
  simp only [Matrix.neg_vecMulVec, Matrix.mulVec_neg, Matrix.vecMulVec_neg]
  abel

theorem spanAd_add {n d n₁ d₁ : ℕ} {H : Plane E n n₁} {H' : Plane E d d₁} {p p' : Matrix (Fin n) (Fin d) (AE F E)}
    (hp : p ∈ spanAd (F := F) H H') (hp' : p' ∈ spanAd (F := F) H H') : p + p' ∈ spanAd (F := F) H H' := by
  obtain ⟨y, z, rfl⟩ := hp
  obtain ⟨y', z', rfl⟩ := hp'
  refine ⟨y + y', z + z', ?_⟩
  simp only [Matrix.add_vecMulVec, Matrix.mulVec_add, Matrix.vecMulVec_add]
  abel

theorem spanAd_neg {n d n₁ d₁ : ℕ} {H : Plane E n n₁} {H' : Plane E d d₁} {p : Matrix (Fin n) (Fin d) (AE F E)}
    (hp : p ∈ spanAd (F := F) H H') : -p ∈ spanAd (F := F) H H' := by
  obtain ⟨y, z, rfl⟩ := hp
  refine ⟨-y, -z, ?_⟩
  simp only [Matrix.neg_vecMulVec, Matrix.mulVec_neg, Matrix.vecMulVec_neg]
  abel

theorem two_terms_eq {n d d₁ : ℕ} (a : AF F) (x x₀ : Fin n → E) (w : Fin d → E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (s s' : E) (u' : Fin d₁ → E) :
    a • incM F (Matrix.vecMulVec x (s' • w)) + a • incM F (Matrix.vecMulVec (s • x₀) (ι' *ᵥ u')) =
      Matrix.vecMulVec (fun i => a • inclR (F := F) (AF F) (x i * s')) (incV F w) +
        Matrix.vecMulVec (incV F x₀) (incM F ι' *ᵥ fun m => a • inclR (F := F) (AF F) (s * u' m)) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, incM, incV, Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.mulVec,
    dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, map_sum]
  simp only [Algebra.smul_def, Finset.mul_sum, map_mul]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun m _ => by ring

theorem last_term_eq {n d n₁ d₁ : ℕ} (a : AF F) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (u : Fin n₁ → E) (u' : Fin d₁ → E) :
    a • incM F (Matrix.vecMulVec (ι *ᵥ u) (ι' *ᵥ u')) = incM F ι * (a • incM F (Matrix.vecMulVec u u')) * (incM F ι')ᵀ := by
  have h : Matrix.vecMulVec (ι *ᵥ u) (ι' *ᵥ u') = ι * Matrix.vecMulVec u u' * ι'ᵀ := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  rw [h, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [incM, Matrix.map_mul, Matrix.transpose_map]

end GlobalTheory.ThK.AdaptEv.VacuumBlock.Dec

namespace GlobalTheory.ThK.AdaptEv.VacuumBlock

open GlobalTheory.ThK.AdaptEv.VacuumBlock.Dec

theorem latAtV_adapted_decomp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (i₀ i₁ j₀ j₁ : ℕ), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Pl F, ∀ γ ∈ latAtV X W v,
    ∃ p ∈ GlobalTheory.ThK.AdaptEv.VacuumBlock.spanA (F := F) H H', ∃ q ∈ GlobalTheory.ThK.AdaptEv.VacuumBlock.spanAd (F := F) H H', ∃ g ∈ latAtV X₁ W₁ v,
      p ∈ latAtV X W v ∧ q ∈ latAtV X W v ∧ γ = p + q + incM F H.ι * g * (incM F H'.ι)ᵀ := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' i₀ i₁ j₀ j₁ hH hH' v γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hi, x, hx, y, hy, rfl⟩ := hz
    obtain ⟨s, t, u, hs, ht, hu, hxe⟩ := hH.split x hx
    obtain ⟨s', t', u', hs', ht', hu', hye⟩ := hH'.split y hy
    have hu'W : H'.ι *ᵥ u' ∈ W.L := (hH'.low u').1 hu'
    have hmid : Matrix.vecMulVec x (H'.ι *ᵥ u') = Matrix.vecMulVec (s • H.x) (H'.ι *ᵥ u') +
        Matrix.vecMulVec (H.ι *ᵥ u) (H'.ι *ᵥ u') + Matrix.vecMulVec (t • H.y) (H'.ι *ᵥ u') := by
      rw [hxe, Matrix.add_vecMulVec, Matrix.add_vecMulVec]
    have key : Matrix.vecMulVec x y = Matrix.vecMulVec x (s' • H'.x) + Matrix.vecMulVec (s • H.x) (H'.ι *ᵥ u') +
        (Matrix.vecMulVec x (t' • H'.y) + Matrix.vecMulVec (t • H.y) (H'.ι *ᵥ u')) +
        Matrix.vecMulVec (H.ι *ᵥ u) (H'.ι *ᵥ u') := by
      rw [hye, Matrix.vecMulVec_add, Matrix.vecMulVec_add, hmid]
      abel
    refine ⟨_, ⟨_, _, two_terms_eq a x H.x H'.x H'.ι s s' u'⟩, _, ⟨_, _, two_terms_eq a x H.y H'.y H'.ι t t' u'⟩,
      a • incM F (Matrix.vecMulVec u u'), gen_mem_latAtV ha hi hu hu',
      add_mem (gen_mem_latAtV ha hi hx hs') (gen_mem_latAtV ha hi hs hu'W),
      add_mem (gen_mem_latAtV ha hi hx ht') (gen_mem_latAtV ha hi ht hu'W), ?_⟩
    rw [← last_term_eq, key]
    simp only [incM_add', smul_add]
  | zero =>
    refine ⟨0, ⟨0, 0, by ext; simp [Matrix.vecMulVec_apply]⟩, 0, ⟨0, 0, by ext; simp [Matrix.vecMulVec_apply]⟩, 0, zero_mem _, zero_mem _, zero_mem _, by simp⟩
  | add γ₁ γ₂ _ _ ih₁ ih₂ =>
    obtain ⟨p₁, hp₁, q₁, hq₁, g₁, hg₁, hp₁L, hq₁L, e₁⟩ := ih₁
    obtain ⟨p₂, hp₂, q₂, hq₂, g₂, hg₂, hp₂L, hq₂L, e₂⟩ := ih₂
    refine ⟨p₁ + p₂, spanA_add hp₁ hp₂, q₁ + q₂, spanAd_add hq₁ hq₂, g₁ + g₂, add_mem hg₁ hg₂,
      add_mem hp₁L hp₂L, add_mem hq₁L hq₂L, ?_⟩
    rw [e₁, e₂, Matrix.mul_add, Matrix.add_mul]
    abel
  | neg γ₁ _ ih =>
    obtain ⟨p₁, hp₁, q₁, hq₁, g₁, hg₁, hp₁L, hq₁L, e₁⟩ := ih
    refine ⟨-p₁, spanA_neg hp₁, -q₁, spanAd_neg hq₁, -g₁, neg_mem hg₁, neg_mem hp₁L, neg_mem hq₁L, ?_⟩
    rw [e₁, Matrix.mul_neg, Matrix.neg_mul]
    abel

end GlobalTheory.ThK.AdaptEv.VacuumBlock
