import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section

namespace GlobalTheory.LatHatStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def finToAd : Af F →ₗ[F] AF F := LinearMap.inr F (Ainf F) (Af F)

theorem finToAd_mul (c : Af F) (a : AF F) : finToAd c * a = finToAd (c * a.2) :=
  Prod.ext (zero_mul _) rfl

def putAt (v : Pl F) : Fv F v ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  TensorProduct.map (finToAd.comp (singleFin v)) LinearMap.id

theorem putAt_tmul (v : Pl F) (b : Fv F v) (y : E) :
    putAt (E := E) v (b ⊗ₜ[F] y) = finToAd (singleFin v b) ⊗ₜ[F] y := rfl

theorem singleFin_mul_eq (v : Pl F) (b : Fv F v) (c : Af F) :
    singleFin v b * c = singleFin v (b * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c) := by
  refine af_ext fun u => ?_
  rw [map_mul]
  by_cases h : u = v
  · subst h; rw [evalV_singleFin_self, evalV_singleFin_self]
  · rw [evalV_singleFin_ne h, evalV_singleFin_ne h, zero_mul]

theorem single_mul_eq (v : Pl F) (b : Fv F v) (a : AF F) :
    finToAd (singleFin v b) * a = finToAd (singleFin v (b * evFin F v a)) := by
  rw [finToAd_mul, singleFin_mul_eq]; rfl

theorem putAt_mul (v : Pl F) (t : Fv F v ⊗[F] E) (a : AF F) (y : E) :
    putAt v t * (a ⊗ₜ[F] y) = putAt v (t * (evFin F v a ⊗ₜ[F] y)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b e =>
    rw [putAt_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, putAt_tmul, single_mul_eq]
  | add x y hx hy => rw [map_add, add_mul, hx, hy, add_mul, map_add]

end GlobalTheory.LatHatStab

namespace GlobalTheory.LatHatStab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mat_emb (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (k : GLoc σ J v) (r s : Fin n) :
    (HA.mat (AF F) σ J (emb σ J v k)).1 r s =
      (1 - putAt v 1) * (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) r s + putAt v ((HA.mat (Fv F v) σ J k).1 r s) := by
  have e1 : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (LinearMap.inr F (Ainf F) (Af F)) (fun _ _ => Prod.ext (mul_zero _).symm rfl)
      (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) (singleFin v) (singleFin_mul v) t) = putAt v t := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | tmul b e => rfl
    | add x y hx hy => simp only [map_add, hx, hy]; rfl
  change (HA.mat (AF F) σ J (ofFin σ J (embLocFin σ J v k))).1 r s = _
  erw [GlobalTheory.AutFunCompare.mat_extH]
  rw [embLocFin, GlobalTheory.AutFunCompare.mat_extH, map_add]
  erw [e1]
  by_cases h : r = s
  · subst h
    simp only [Matrix.one_apply_eq, mul_one, map_sub]
    erw [e1]
    ring
  · simp only [Matrix.one_apply_ne h, mul_zero, map_zero, zero_add]
end GlobalTheory.LatHatStab

namespace GlobalTheory.LatHatStab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_incV {n : ℕ} (c : AF F) (x : Fin n → E) (i : Fin n) : (c • incV F x) i = c ⊗ₜ[F] x i := by
  simp [incV, inclR, TensorProduct.smul_tmul']

theorem evI_finToAd (c : Af F) : evI F (finToAd c) = 0 := by
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F) 0 = 0
  exact map_zero _

theorem evFin_finToAd (u : Pl F) (c : Af F) : evFin F u (finToAd c) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u c := rfl

theorem gen_mem {n : ℕ} (X : Spc F E n) {c : AF F} (h0 : evI F c = 0)
    (h1 : ∀ u, evFin F u c ∈ u.adicCompletionIntegers F) {x : Fin n → E} (hx : x ∈ X.L) : c • incV F x ∈ latHat X :=
  AddSubgroup.subset_closure ⟨c, h0, h1, x, hx, rfl⟩

theorem single_int (v u : Pl F) {b : Fv F v} (hb : b ∈ v.adicCompletionIntegers F) :
    evFin F u (finToAd (singleFin v b)) ∈ u.adicCompletionIntegers F := by
  rw [evFin_finToAd]
  by_cases h : u = v
  · subst h; rw [evalV_singleFin_self]; exact hb
  · rw [evalV_singleFin_ne h]; exact zero_mem _

theorem putVec_mem {n : ℕ} (X : Spc F E n) (v : Pl F) {y : Fin n → Fv F v ⊗[F] E} (hy : y ∈ latLoc F X.L v) :
    (fun i => putAt v (y i)) ∈ latHat X := by
  refine latLoc_induction (p := fun y => (fun i => putAt v (y i)) ∈ latHat X) (fun b hb x hx => ?_) ?_ ?_ ?_ hy
  · have e : (fun i => putAt v (b ⊗ₜ[F] x i)) = finToAd (singleFin v b) • incV F x := funext fun i => by
      rw [smul_incV, putAt_tmul]
    rw [e]
    exact gen_mem X (evI_finToAd _) (fun u => single_int v u hb) hx
  · have e : (fun i => putAt v ((0 : Fin n → Fv F v ⊗[F] E) i)) = 0 := funext fun i => map_zero _
    rw [e]; exact zero_mem _
  · intro y z hy hz
    have e : (fun i => putAt v ((y + z) i)) = (fun i => putAt v (y i)) + fun i => putAt v (z i) :=
      funext fun i => map_add _ _ _
    rw [e]; exact add_mem hy hz
  · intro y hy
    have e : (fun i => putAt v ((-y) i)) = -fun i => putAt v (y i) := funext fun i => map_neg _ _
    rw [e]; exact neg_mem hy

theorem putAt_one (v : Pl F) : putAt (E := E) v 1 = finToAd (singleFin v 1) ⊗ₜ[F] (1 : E) := by
  rw [Algebra.TensorProduct.one_def, putAt_tmul]

theorem mulVec_gen (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (k : GLoc σ J v) (a : AF F)
    (x : Fin n → E) :
    (HA.mat (AF F) σ J (emb σ J v k) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ (a • incV F x) =
      ((1 - finToAd (singleFin v 1)) * a) • incV F x +
        fun i => putAt v (((HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
          fun s => evFin F v a ⊗ₜ[F] x s) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, mat_emb, add_mul, Finset.sum_add_distrib, smul_incV, putAt_mul, map_sum,
    Pi.add_apply]
  congr 1
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [putAt_one, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end GlobalTheory.LatHatStab

namespace GlobalTheory.LatHatStab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mulVec_mem_latHat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (X : Spc F E n) (v : Pl F), ∀ k ∈ stabLoc σ J X.L v,
      ∀ z ∈ latHat X, (HA.mat (AF F) σ J (emb σ J v k) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ z ∈ latHat X := by
  intro F E _ _ _ _ _ σ n J X v k hk z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha0, ha1, x, hx, rfl⟩ := hz
    rw [mulVec_gen]
    refine add_mem (gen_mem X ?_ (fun u => ?_) hx) (putVec_mem X v ?_)
    · change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((1 - finToAd (singleFin v 1)).1 * a.1) = 0
      rw [map_mul]
      exact mul_eq_zero_of_right _ ha0
    · rw [map_mul, map_sub, map_one, evFin_finToAd]
      by_cases h : u = v
      · subst h; rw [evalV_singleFin_self, sub_self, zero_mul]; exact zero_mem _
      · rw [evalV_singleFin_ne h, sub_zero, one_mul]; exact ha1 u
    · exact (mem_stabLoc.1 hk _).1 (tmul_mem_latLoc (ha1 v) hx)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | neg y _ hy => rw [Matrix.mulVec_neg]; exact neg_mem hy

end GlobalTheory.LatHatStab

end
