import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.AdjLatO

variable {D : D7}

theorem incA_mul_tmul' (g e : D.host.E) (x : AF D.host.F) :
    incA D g * (x ⊗ₜ[D.host.F] e) = x ⊗ₜ[D.host.F] (g * e) := by
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] g) * _ = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem tmul_mul_incA' (g e : D.host.E) (x : AF D.host.F) :
    (x ⊗ₜ[D.host.F] e) * incA D g = x ⊗ₜ[D.host.F] (e * g) := by
  change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] g) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

def tensM (x : AF D.host.F) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  M.map fun e => x ⊗ₜ[D.host.F] e

theorem rat_mul_tensM (x : AF D.host.F) {l m n : ℕ} (G : Matrix (Fin l) (Fin m) D.host.E)
    (M : Matrix (Fin m) (Fin n) D.host.E) : rat G ⬝ tensM x M = tensM x (G * M) := by
  ext i j
  simp only [tensM, rat, Matrix.mul_apply, Matrix.map_apply, incA_mul_tmul', TensorProduct.tmul_sum]

theorem tensM_mul_rat (x : AF D.host.F) {l m n : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E)
    (G : Matrix (Fin m) (Fin n) D.host.E) : tensM x M ⬝ rat G = tensM x (M * G) := by
  ext i j
  simp only [tensM, rat, Matrix.mul_apply, Matrix.map_apply, tmul_mul_incA', TensorProduct.tmul_sum]

theorem adj_tensM (x : AF D.host.F) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    adj (tensM x M) = tensM x Mᴴ := by
  ext i j; rfl

theorem xi0_inv_smul_starAdj (S T : HSp D) (x : WO S T) :
    incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T x = giA S ⬝ (adj x ⬝ gA T) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj, smul_smul, ← map_mul, inv_mul_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_one, one_smul]

def genT (T : HSp D) {n : ℕ} (x : AF D.host.F) (t : Fin T.rank → D.host.E) (u : Fin n → D.host.E) :
    Matrix (Fin n) (Fin T.rank) (AE D) :=
  Matrix.of fun p q => x ⊗ₜ[D.host.F] (u p * ∑ i, star (t i) * T.gram i q)

theorem genT_add (T : HSp D) {n : ℕ} (x : AF D.host.F) (t : Fin T.rank → D.host.E) (u v : Fin n → D.host.E) :
    genT T x t (u + v) = genT T x t u + genT T x t v := by
  ext p q
  simp only [genT, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, add_mul, TensorProduct.tmul_add]

theorem genT_zero (T : HSp D) {n : ℕ} (x : AF D.host.F) (t : Fin T.rank → D.host.E) :
    genT T x t (0 : Fin n → D.host.E) = 0 := by
  ext p q
  simp only [genT, Matrix.of_apply, Pi.zero_apply, zero_mul, TensorProduct.tmul_zero, Matrix.zero_apply]

theorem starAdj_gen (S T : HSp D) (x : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T
        (Matrix.of fun i j => x ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      genT T x t (star a • s) := by
  have e : (Matrix.of fun i j => x ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
      tensM x ((Matrix.of fun i k => a * t i * star (s k)) * S.gram) := by
    ext i j
    simp only [tensM, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]
  rw [xi0_inv_smul_starAdj, e, adj_tensM, Matrix.conjTranspose_mul, gram_conjTranspose, gA, tensM_mul_rat, giA,
    rat_mul_tensM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det S), Matrix.one_mul]
  ext p q
  simp only [tensM, genT, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [star_mul', star_star]
  ring

theorem genT_mem_of_mem_span (S T : HSp D) (LS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : GlobalTheory.FinPl.Pl D → Prop)
    (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (hP : ∀ v, ¬ P v → evalV D.host.F v α = 0)
    (t : Fin T.rank → D.host.E) (ht : t ∈ LT) (u : Fin S.rank → D.host.E)
    (hu : u ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ LS', y = a' • s'}) :
    genT T (pairA D.host.F 0 α) t u ∈ latO T S (LT : Set _) (LS' : Set _) P := by
  suffices h : ∀ c : 𝓞 D.host.E, genT T (pairA D.host.F 0 α) t (c • u) ∈ latO T S (LT : Set _) (LS' : Set _) P by
    simpa using h 1
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a', ha', s', hs', rfl⟩ := hy
    intro c
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, hP, a', ha', t, ht, c • s', LS'.smul_mem c hs', ?_⟩
    ext p q
    simp only [genT, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def]
    ring
  | zero => intro c; rw [smul_zero, genT_zero]; exact zero_mem _
  | add y z _ _ hy hz => intro c; rw [smul_add, genT_add]; exact add_mem (hy c) (hz c)
  | smul r y _ hy => intro c; rw [smul_smul]; exact hy (c * r)

theorem incA_inv_xi0_smul_starAdj_mem_latO : ∀ (D : D7) (S T : HSp D) (LS LS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : GlobalTheory.FinPl.Pl D → Prop), (∀ a ∈ D.host.AA, ∀ s ∈ LS, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ LS', y = a' • s'}) → ∀ x ∈ latO S T (LS : Set _) (LT : Set _) P, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T x ∈ latO T S (LT : Set _) (LS' : Set _) P := by
  intro D S T LS LS' LT P hA x hx
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    rw [starAdj_gen]
    exact genT_mem_of_mem_span S T LS' LT P α hα hP t ht _ (hA a ha s hs)
  | zero =>
    rw [xi0_inv_smul_starAdj, adj_zero, Matrix.zero_mul, Matrix.mul_zero]; exact zero_mem _
  | add y z _ _ hy hz =>
    rw [xi0_inv_smul_starAdj] at hy hz ⊢
    rw [adj_add, Matrix.add_mul, Matrix.mul_add]; exact add_mem hy hz
  | neg y _ hy =>
    rw [xi0_inv_smul_starAdj] at hy ⊢
    rw [adj_neg, Matrix.neg_mul, Matrix.mul_neg]; exact neg_mem hy

end GlobalTheory.AdjLatO
