import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensInclInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JmConjTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedRealLineSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialsInclusionLe
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl

namespace GlobalTheory.LeviBeta

open GlobalTheory.FockBottom

private noncomputable def cen {R S : ℕ} (r₀ : Fin R) (s₀ : Fin S) : Mat R S :=
  Eab (.inl r₀) (.inl r₀) + Eab (.inr s₀) (.inr s₀)

private theorem cen_apply {R S : ℕ} (r₀ : Fin R) (s₀ : Fin S) (a b : Ix R S) :
    cen r₀ s₀ a b = if a = b then (if b = .inl r₀ ∨ b = .inr s₀ then 1 else 0) else 0 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [cen, Eab, Matrix.single_apply] <;> aesop

private theorem isKC_cen {R S : ℕ} (r₀ : Fin R) (s₀ : Fin S) : IsKC (cen r₀ s₀) := fun a b h => by
  rw [cen_apply, if_neg]
  rintro rfl
  apply h
  rcases a with a | a <;> simp [sameBlock]

private theorem trace_cen {R S : ℕ} (r₀ : Fin R) (s₀ : Fin S) : (cen r₀ s₀).trace = 2 := by
  rw [cen, Matrix.trace_add, Eab, Eab, Matrix.trace_single_eq_same, Matrix.trace_single_eq_same]; norm_num

private theorem cen_conjTranspose {R S : ℕ} (r₀ : Fin R) (s₀ : Fin S) : (cen r₀ s₀)ᴴ = cen r₀ s₀ := by
  simp [cen, Eab, Matrix.conjTranspose_single]

private theorem fock_cen_polIncl {P Q R S : ℕ} (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (f : Formalism.BasicNotions.TH.Pol P Q R S) :
    fockAct2 P Q (R + 1) (S + 1) (cen r₀ s₀) (polIncl P Q r₀ s₀ f) = 0 := by
  have hz : ∀ v : Ln P Q (R + 1) (S + 1), (∀ m, Prod.map id (skipIx r₀ s₀) m ≠ v) →
      MvPolynomial.pderiv v (polIncl P Q r₀ s₀ f) = 0 := fun v hv =>
    GlobalTheory.FockSplit.pderiv_rename_eq_zero _ v hv f
  rw [cen, map_add, fockAct2_Eab, fockAct2_Eab, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.sum_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  have hs : sameBlock a a := by rcases a with a | a <;> simp [sameBlock]
  rw [GlobalTheory.FockInclHarm.omE_free a a _ hs _ (hz _ (GlobalTheory.FockInclHarm.incl_ne_left r₀ s₀ a))
      (hz _ (GlobalTheory.FockInclHarm.incl_ne_left r₀ s₀ a)),
    GlobalTheory.FockInclHarm.omE_free a a _ hs _ (hz _ (GlobalTheory.FockInclHarm.incl_ne_right r₀ s₀ a))
      (hz _ (GlobalTheory.FockInclHarm.incl_ne_right r₀ s₀ a)), if_pos rfl, if_pos rfl, ← add_smul]
  rcases a with a | a <;> simp [lineSign] <;> norm_num

private theorem atPl_cen_tensIncl {F : Type} [Field F] [NumberField F] {P Q R S : ℕ} (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1))
    [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (T : Tens F P Q R S) :
    atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q (R + 1) (S + 1)) w
      (fockAct2 P Q (R + 1) (S + 1) (cen r₀ s₀)) (tensIncl F P Q r₀ s₀ T) = 0 := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    rw [map_smul, map_smul, tensIncl, PiTensorProduct.map_tprod, atPl, PiTensorProduct.map_tprod,
      MultilinearMap.map_coord_zero _ w, smul_zero]
    rw [Function.update_self]
    exact fock_cen_polIncl r₀ s₀ (f w)
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

end GlobalTheory.LeviBeta

open GlobalTheory.LeviBeta GlobalTheory.FockBottom in
theorem _root_.GlobalTheory.T.configuration_b_global_integral : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ (P Q R₀ S₀ : ℕ) (A : InfinitePlace F → Matrix (Fin a) (Ix P Q) ℂ)
        (C₁ : InfinitePlace F → Matrix (Fin (a + b)) (Ix R₀ S₀) ℂ)
        (C : InfinitePlace F → Matrix (Fin (a + (b + 2))) (Ix (R₀ + 1) (S₀ + 1)) ℂ)
        (Φ₁ : Tens F P Q R₀ S₀ →ₗ[ℂ] SInf F (Fin a × Fin (a + b)))
        (Φ : Tens F P Q (R₀ + 1) (S₀ + 1) →ₗ[ℂ] SInf F (Fin a × Fin (a + (b + 2)))) (r₀ : Fin (R₀ + 1)) (s₀ : Fin (S₀ + 1)),
        GlobalTheory.FockBridge.IsFockData B G₁.M A C₁ Φ₁ → GlobalTheory.FockBridge.IsFockData B G.M A C Φ →
        GlobalTheory.FockBridge.IsAdaptedFrame B H' C r₀ s₀ → IsCompat B H' C C₁ r₀ s₀ →
        ∀ k ∈ KInf σ G.W B.emb, ∀ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ G₁.W.J) k → ∀ T : Tens F P Q R₀ S₀,
          Acts (evI F) (om (1, k)) (Φ (tensIncl F P Q r₀ s₀ T))
            ⇑(((X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)) • Φ (tensIncl F P Q r₀ s₀ T)) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hCfg X om om' Rm Rf om₁ om₁' R₁ Rf₁ hM hM₁ P Q R₀ S₀ A C₁ C Φ₁ Φ r₀ s₀
    _ hD hAd _ k hk t hL T
  classical
  have hT := hM.triple
  have hC := hD.1.1.2.2
  have hθ := hD.1.2.2
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hT.weil
  have hsec : LieSecond :=
    Main.i_liesecond hKP.base Main.i_derex (Main.i_fockex Main.i_derex) (Main.i_vacline Main.i_derex)
      (Main.i_liescalar hKP.base Main.i_derex (Main.i_vacline Main.i_derex))
  have hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q _ _) fun w => (B.mβ w : ℂ) / 2 :=
    hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hT.base.cm hT.base.std hD.1.1 hD.2
      hwp.1 hT.chars.expβ
  have hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin a × Fin (a + (b + 2))),
      l ∘ₗ om g ∈ (adeleClass F).adm (Fin a × Fin (a + (b + 2))) := fun g => (hwp.isUSplitting).adm g
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.adapted_real_line_second F E σ B _ _ _ _ _ _ _ _ G.W G₁.W H' hT.base hT.geo.hW hM₁.triple.geo.hW hCfg.hH'
    _ _ r₀ s₀ C hC hθ hAd k hk t hL
  let θ : InfinitePlace F → ℝ := fun w => Complex.arg (piInf (B.emb w) (t : AE F E))
  have ht : ∀ w, piInf (B.emb w) (t : AE F E) = Complex.exp (θ w * Complex.I) := fun w => by
    have := Complex.norm_mul_exp_arg_mul_I (piInf (B.emb w) (t : AE F E))
    rw [(h3 w).1, Complex.ofReal_one, one_mul] at this
    exact this.symm
  obtain ⟨k', hk', hkC, U, hU, hAc⟩ := exp_of_skew hT.base.cm hC hθ hact hadm (fun w => (θ w * Complex.I) • cen r₀ s₀)
    (fun w => GlobalTheory.FockKStab.isKC_smul (isKC_cen r₀ s₀) _)
    (fun w => by simp [Matrix.conjTranspose_smul, cen_conjTranspose])
  have hkk : k = k' := eq_of_frame hT.base.cm hC hk.1 hk'.1 fun w => by
    ext i c
    rw [hkC]
    by_cases e1 : c = .inl r₀
    · rw [e1, (h3 w).2.1, ht]
      exact (mul_exp_col _ _ _ _ (fun a => by simp [cen_apply]) i).symm
    by_cases e2 : c = .inr s₀
    · rw [e2, (h3 w).2.2.1, ht]
      exact (mul_exp_col _ _ _ _ (fun a => by simp [cen_apply]) i).symm
    rw [(h3 w).2.2.2 c e1 e2, mul_exp_col _ _ c 0 (fun a => by simp [cen_apply, e1, e2]) i, Complex.exp_zero, one_mul]
  subst hkk
  have hχ : (X.β t : ℂ) = Complex.exp (∑ w, θ w * Complex.I * B.mβ w) := by
    rw [hT.chars.expβ t h1, Complex.exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [ht, Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, div_one, mul_comm _ (B.mβ w : ℂ), Complex.exp_int_mul]
  have hUT : U (tensIncl F P Q r₀ s₀ T) = Complex.exp (∑ w, θ w * Complex.I * B.mβ w) • tensIncl F P Q r₀ s₀ T := by
    refine isExp_eig hU LinearMap.id _ (fun _ => rfl) ?_
    rw [LinearMap.id_apply, genOp_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_smul, Main.atPl_smul, LinearMap.smul_apply, atPl_cen_tensIncl, smul_zero, zero_add, Matrix.trace_smul,
      trace_cen]
    congr 1
    rw [smul_eq_mul]; ring
  have := hAc (tensIncl F P Q r₀ s₀ T)
  rwa [h2, Real.one_rpow, Complex.ofReal_one, mul_one, hχ, ← map_smul, ← hUT]
