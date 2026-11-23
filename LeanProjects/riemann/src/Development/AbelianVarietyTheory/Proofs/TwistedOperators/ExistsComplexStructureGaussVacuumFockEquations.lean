import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHasTemperateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanAdeleCMPrescribedEmbeddingValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.GaussFockJ

open GlobalTheory.ThK.EvAt0.PolD

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem dHeis_eq_dOp {κ : Type} [Fintype κ] (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : SInf F κ) (x : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F κ) w ⇑f x = dOp w.1 w.2 f x := by
  rw [dOp_apply]; simp [GlobalTheory.GaussLine.dHeis, GlobalTheory.GaussLine.pairInf_apply, lin]

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evIHom_apply (a : AF F) : evIHom a = evI F a := rfl

theorem evI_zero_c : evI F (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) : AF F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
  exact map_zero _

theorem eq_liftA_of_mul {a : AF F} (ha : ∀ c : AF F, evI F c = 0 → c * a = 0) : a = liftA (evI F a) := by
  have h2 : a.2 = 0 := by
    have h := congrArg Prod.snd (ha _ evI_zero_c)
    change (1 : FiniteAdeleRing (𝓞 F) F) * a.2 = 0 at h
    simpa using h
  refine Prod.ext ?_ ?_
  · change a.1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1)
    exact ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply a.1).symm
  · simp [liftA, h2]

theorem liftA_add (a b : mixedEmbedding.mixedSpace F) : liftA (a + b) = liftA a + liftA b := by
  unfold liftA; rw [map_add, map_add]; rfl

theorem liftA_mul (a b : mixedEmbedding.mixedSpace F) : liftA (a * b) = liftA a * liftA b := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a * b) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm b
    exact map_mul _ _ _
  · change (0 : FiniteAdeleRing (𝓞 F) F) = 0 * 0
    simp

theorem realAd_eq (t : ℝ) : realAd F t = liftA (algebraMap ℝ _ t) := rfl

theorem liftA_smul (t : ℝ) (a : mixedEmbedding.mixedSpace F) : liftA (t • a) = realAd F t * liftA a := by
  rw [realAd_eq, ← liftA_mul, Algebra.smul_def]

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ _ t := by
  rw [realAd_eq, evI_liftA]

theorem mul_liftA {c : AF F} (hc : evI F c = 0) (v : mixedEmbedding.mixedSpace F) : c * liftA v = 0 :=
  smul_liftA hc v

section Model

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def lift {κ : Type} (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    (κ → AF F) × (κ → AF F) := (fun i => liftA (w.1 i), fun i => liftA (w.2 i))

def Phi (M : Model σ X W)
    (w : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    Matrix (Fin n) (Fin d) (AE F E) := M.co.e.symm (lift w)

def Psi (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  (arc (M.co.e u).1, arc (M.co.e u).2)

theorem at_Phi (M : Model σ X W) (w) : At (evI F) (Phi M w) := by
  intro c hc
  rw [Phi, ← map_smul]
  have : c • (lift w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) = 0 := by
    ext i <;> simp only [lift, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Prod.fst_zero, Prod.snd_zero,
      Pi.zero_apply, smul_eq_mul] <;> exact mul_liftA hc _
  rw [this, map_zero]

theorem Psi_Phi (M : Model σ X W) (w) : Psi M (Phi M w) = w := by
  simp only [Psi, Phi, LinearEquiv.apply_symm_apply, lift]
  ext i <;> simp [arc, evI_liftA]

theorem e_eq_lift (M : Model σ X W) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) :
    M.co.e u = lift (Psi M u) := by
  have key : ∀ c : AF F, evI F c = 0 → c • M.co.e u = 0 := fun c hc => by rw [← map_smul, hu c hc, map_zero]
  ext i
  · exact eq_liftA_of_mul fun c hc => by have := congrArg (fun p => p.1 i) (key c hc); simpa using this
  · exact eq_liftA_of_mul fun c hc => by have := congrArg (fun p => p.2 i) (key c hc); simpa using this

theorem Phi_Psi (M : Model σ X W) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) : Phi M (Psi M u) = u := by
  rw [Phi, ← e_eq_lift M hu, LinearEquiv.symm_apply_apply]

theorem Phi_add (M : Model σ X W) (w w') : Phi M (w + w') = Phi M w + Phi M w' := by
  rw [Phi, Phi, Phi, ← map_add]; congr 1
  ext i <;> simp [lift, liftA_add]

theorem Phi_smul (M : Model σ X W) (t : ℝ) (w) : Phi M (t • w) = realAd F t • Phi M w := by
  rw [Phi, Phi, ← map_smul]; congr 1
  ext i <;> simp [lift, liftA_smul]

theorem Psi_add (M : Model σ X W) (u v : Matrix (Fin n) (Fin d) (AE F E)) : Psi M (u + v) = Psi M u + Psi M v := by
  ext i <;> simp [Psi, arc, ← evIHom_apply, map_add]

theorem Psi_neg (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) : Psi M (-u) = -Psi M u := by
  ext i <;> simp [Psi, arc, ← evIHom_apply, map_neg]

end Model

section Places

theorem exists_mat_at (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)
    {m k : Type} (z : InfinitePlace F → Matrix m k ℂ) :
    ∃ u : Matrix m k (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = z w := by
  choose a ha using fun i j => GlobalTheory.PolRangeInf.exists_at_inf_values hcm τ (fun w => z w i j)
  refine ⟨Matrix.of a, fun x hx => ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact (ha i j).1 x hx
  · ext i j
    simp [(ha i j).2 w]

theorem eq_of_map_piInf (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) {m k : Type}
    {u v : Matrix m k (AE F E)} (hu : At (evI F) u) (hv : At (evI F) v)
    (h : ∀ w, u.map (piInf (τ w)) = v.map (piInf (τ w))) : u = v := by
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hcm τ (u i j - v i j) (fun c hc => ?_) fun w => ?_)
  · have h1 := congrFun (congrFun (hu c hc) i) j
    have h2 := congrFun (congrFun (hv c hc) i) j
    simp only [Matrix.smul_apply, Matrix.zero_apply] at h1 h2
    rw [smul_sub, h1, h2, sub_zero]
  · have := congrFun (congrFun (h w) i) j
    simp only [Matrix.map_apply] at this
    rw [map_sub, this, sub_self]

theorem map_smul_piInf {w : InfinitePlace F} (τ : GlobalTheory.AdelicU.EmbOver E w) {m k : Type} (c : AF F) (u : Matrix m k (AE F E)) :
    (c • u).map (piInf τ) = piInf τ (algebraMap (AF F) (AE F E) c) • u.map (piInf τ) := by
  ext i j
  simp [Algebra.smul_def, map_mul]

end Places

section Line

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem evI_add' (a b : AF F) : evI F (a + b) = evI F a + evI F b := by
  rw [← evIHom_apply, map_add]; rfl

theorem evI_realAd_mul (t : ℝ) (a : AF F) : evI F (realAd F t * a) = t • evI F a := by
  rw [← evIHom_apply, map_mul, evIHom_apply, evIHom_apply, evI_realAd, Algebra.smul_def]

theorem at_realAd_mul {c : AF F} (hc : evI F c = 0) (t : ℝ) (a : AF F) : c * (realAd F t * a) = 0 := by
  rw [← mul_assoc, realAd_eq, mul_liftA hc, zero_mul]

theorem actsD_Phi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W)
    (w : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
    (f : SInf F (Fin n × Fin d)) : ActsD (evI F) (M.heisLine ψ (Phi M w)) f (dOp w.1 w.2 f) := by
  intro r hr z
  set x : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (z i) with hx
  set A : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * w.2 i) with hA
  set B0 : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (evI F (⅟(2 : AF F) * ((lift w).1 ⬝ᵥ (lift w).2))) with hB0
  have key : ∀ t : ℝ, M.heisLine ψ (Phi M w) t (tens (evI F) (⇑f) r) z =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * A + t ^ 2 * B0 : ℝ) : ℂ)) * (f (x + t • w.1) * r z) := by
    intro t
    have he : M.co.e (realAd F t • Phi M w) = realAd F t • lift w := by
      rw [map_smul, Phi, LinearEquiv.apply_symm_apply]
    have hAt1 : At (evI F) ((realAd F t • lift w).1) := fun c hc => by
      funext i
      simp only [lift, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact at_realAd_mul hc t _
    have hr' : r (z + (realAd F t • lift w).1) = r z := hr.1 z _ hAt1
    have harg : z ⬝ᵥ (realAd F t • lift w).2 + ⅟(2 : AF F) * ((realAd F t • lift w).1 ⬝ᵥ (realAd F t • lift w).2) =
        realAd F t * (z ⬝ᵥ (lift w).2) + realAd F t * (realAd F t * (⅟(2 : AF F) * ((lift w).1 ⬝ᵥ (lift w).2))) := by
      simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
    have hAt2 : At (evI F) (z ⬝ᵥ (realAd F t • lift w).2 +
        ⅟(2 : AF F) * ((realAd F t • lift w).1 ⬝ᵥ (realAd F t • lift w).2)) := fun c hc => by
      rw [harg, smul_eq_mul, mul_add, at_realAd_mul hc, at_realAd_mul hc, add_zero]
    have hdot : evI F (z ⬝ᵥ (lift w).2) = ∑ i, x i * w.2 i := by
      simp only [dotProduct, lift]
      rw [← evIHom_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, evIHom_apply, evIHom_apply, evI_liftA]
    have hev : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (z ⬝ᵥ (realAd F t • lift w).2 +
        ⅟(2 : AF F) * ((realAd F t • lift w).1 ⬝ᵥ (realAd F t • lift w).2))) = t * A + t ^ 2 * B0 := by
      rw [harg, evI_add', evI_realAd_mul, evI_realAd_mul, evI_realAd_mul, hdot, map_add, map_smul, map_smul, map_smul,
        ← hA, ← hB0, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      ring
    have hpt : (fun i => evI F ((z + (realAd F t • lift w).1) i)) = x + t • w.1 := by
      funext i
      simp only [Pi.add_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, lift]
      rw [← evIHom_apply, map_add, map_mul, evIHom_apply, evIHom_apply, evIHom_apply, evI_realAd, evI_liftA,
        ← Algebra.smul_def]
    simp only [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, he]
    rw [hψ.2.2 _ hAt2, hev, tens, hr', hpt]
  have hl : HasDerivAt (fun t : ℝ => x + t • w.1) w.1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w.1).const_add x
  have hf : HasDerivAt (fun t : ℝ => f (x + t • w.1)) (fderiv ℝ f x w.1) 0 := by
    have h0 : HasFDerivAt (⇑f) (fderiv ℝ f (x + (0 : ℝ) • w.1)) (x + (0 : ℝ) • w.1) :=
      (f.differentiableAt).hasFDerivAt
    have h4 := h0.comp_hasDerivAt (0 : ℝ) hl
    simp only [zero_smul, add_zero] at h4
    exact h4
  have h1 : HasDerivAt (fun t : ℝ => t * A + t ^ 2 * B0) A 0 := by
    have h := ((hasDerivAt_id' (0 : ℝ)).mul_const A).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const B0)
    convert h using 1 <;> first | rfl | (funext t; simp) | simp
  have h2 := ((h1.ofReal_comp).const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 := h2.mul (hf.mul_const (r z))
  rw [show (fun t => M.heisLine ψ (Phi M w) t (tens (evI F) (⇑f) r) z) = _ from funext key]
  refine h3.congr_deriv ?_
  simp only [tens, dOp_apply, lin]
  rw [← hx, ← hA]
  simp
  ring

end Line

theorem exists_complex_structure : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ f₀ : SInf F (Fin a × Fin (a + a')), G.M.IsGauss B.ψ B.emb f₀ →
    ∃ J₀ : ((Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)),
      (∀ w, J₀ (J₀ w) = -w) ∧ ∀ w x, GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a'))) (J₀ w) ⇑f₀ x =
        Complex.I * GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a'))) w ⇑f₀ x := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT f₀ hG
  have hcm := hT.base.cm
  have hψ := hT.base.std
  obtain ⟨ε, hε⟩ := hG
  let rel : Matrix (Fin a) (Fin (a + a')) (AE F E) → InfinitePlace F → Matrix (Fin a) (Fin (a + a')) ℂ :=
    fun u w => (((ε w : ℤ) : ℂ) * Complex.I) • (G.V.θ w * u.map (piInf (B.emb w)) * (G.W.θ w)ᵀ)
  choose R hRat hRmap using fun u => exists_mat_at hcm B.emb (rel u)
  have hRadd : ∀ u v, R (u + v) = R u + R v := by
    intro u v
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_add, hRat u c hc, hRat v c hc, add_zero])
      fun w => ?_
    rw [hRmap, Matrix.map_add _ (map_add _), hRmap, hRmap]
    simp only [rel, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add]
  have hRsmul : ∀ (c : AF F) u, R (c • u) = c • R u := by
    intro c u
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c' hc' => by rw [smul_comm, hRat u c' hc', smul_zero])
      fun w => ?_
    rw [hRmap, map_smul_piInf, hRmap]
    simp only [rel, map_smul_piInf, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]
  have hRR : ∀ u, At (evI F) u → R (R u) = -u := by
    intro u hu
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_neg, hu c hc, neg_zero]) fun w => ?_
    rw [hRmap, Matrix.map_neg _ (map_neg _)]
    simp only [rel, hRmap]
    have hV := (hT.geo.hV.cartan w).1
    have hW := (hT.geo.hW.cartan w).1
    have hWt : (G.W.θ w)ᵀ * (G.W.θ w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hW, Matrix.transpose_one]
    have he : (((ε w : ℤ) : ℂ) * Complex.I) * (((ε w : ℤ) : ℂ) * Complex.I) = -1 := by
      have h1 : ((ε w : ℤ) : ℂ) * ((ε w : ℤ) : ℂ) = 1 := by
        rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
      linear_combination (Complex.I * Complex.I) * h1 + Complex.I_mul_I
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, he, neg_one_smul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.mul_assoc, hWt, Matrix.mul_one]
  let J : ((Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)) →
      ((Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)) :=
    fun w => Psi G.M (R (Phi G.M w))
  have hJPhi : ∀ w, Phi G.M (J w) = R (Phi G.M w) := fun w => Phi_Psi G.M (hRat _)
  have hPsi_smul : ∀ (t : ℝ) v, At (evI F) v → Psi G.M (realAd F t • v) = t • Psi G.M v := by
    intro t v hv
    rw [← Phi_Psi G.M hv, ← Phi_smul, Psi_Phi, Psi_Phi]
  let J₀ : ((Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)) :=
    { toFun := J
      map_add' := fun w w' => by
        show Psi G.M (R (Phi G.M (w + w'))) = Psi G.M (R (Phi G.M w)) + Psi G.M (R (Phi G.M w'))
        rw [Phi_add, hRadd, Psi_add]
      map_smul' := fun t w => by
        show Psi G.M (R (Phi G.M (t • w))) = t • Psi G.M (R (Phi G.M w))
        rw [Phi_smul, hRsmul, hPsi_smul t _ (hRat _)] }
  refine ⟨J₀, fun w => ?_, fun w x => ?_⟩
  · show Psi G.M (R (Phi G.M (Psi G.M (R (Phi G.M w))))) = -w
    rw [Phi_Psi G.M (hRat _), hRR _ (at_Phi G.M w), Psi_neg, Psi_Phi]
  · have h := hε (Phi G.M w) (R (Phi G.M w)) (at_Phi G.M w) (hRat _) (hRmap _) _ _ (actsD_Phi hψ G.M w f₀)
      (by rw [← hJPhi]; exact actsD_Phi hψ G.M (J w) f₀)
    rw [dHeis_eq_dOp, dHeis_eq_dOp]
    show dOp (J w).1 (J w).2 f₀ x = _
    rw [h]
    rfl

end GlobalTheory.GaussFockJ
