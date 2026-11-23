import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaReal

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeTateSupp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem trace_mul_dual {m : ℕ} (b₀ : Module.Basis (Fin m) F E) (i : Fin m) : ∃ c : E, ∀ x : AE F E,
    Algebra.trace (AF F) (AE F E) (x * inclR (F := F) (AF F) c) = (Algebra.TensorProduct.basis (AF F) b₀).equivFun x i := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨b₀.traceDual i, fun x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy, Pi.add_apply]
  | tmul r x =>
    have h1 := Module.Basis.traceDual_repr_apply b₀.traceDual x i
    rw [Module.Basis.traceDual_traceDual, Algebra.traceForm_apply] at h1
    have h2 : (r ⊗ₜ[F] x : AE F E) * inclR (F := F) (AF F) (b₀.traceDual i) =
        r • ((1 : AF F) ⊗ₜ[F] (x * b₀.traceDual i)) := by
      simp [inclR, TensorProduct.smul_tmul']
    rw [h2, map_smul, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply,
      ← h1]
    simp [Algebra.TensorProduct.basis_repr_tmul]

theorem symp_shift (hcm : IsCMExt F E σ) {n d n₁ d₁ : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (JW j i) = -JW i j) (H : Plane E n n₁) (H' : Plane E d d₁) (hH : form σ JX H.x H.y = 1)
    (hH' : form σ JW H'.x H'.y = 1) (l : AE F E) (a : AF F) (c : E) :
    symp (cA σ) (-1) (incM F JX) (incM F JW) (l • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
      (a • inclR (F := F) (AF F) (σ c) • Matrix.vecMulVec (incV F H.y) (incV F H'.x)) =
      a * Algebra.trace (AF F) (AE F E) (l * inclR (F := F) (AF F) c) := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  rw [← smul_assoc, symp, GlobalTheory.XTermSupp.hTens_vv, GlobalTheory.XTermSupp.form_inc, GlobalTheory.XTermSupp.form_inc, hH,
    GlobalTheory.XTermSupp.form_skew hcm hJ, hH', map_smul, hc, GlobalTheory.XTermSupp.invol hcm,
    ← smul_eq_mul a, ← map_smul (Algebra.trace (AF F) (AE F E))]
  congr 1
  simp

theorem rho_fixed {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∀ᶠ t in 𝓝 (0 : Af F), M.co.rho ψ (pairA F 0 t • u) Φ = Φ := by
  filter_upwards [GlobalTheory.XTermSupp.schA_fixed_smul ψ hψ Φ hΦ (isCompact_univ (X := Unit)) (fun _ => M.co.e u)
    continuous_const] with t ht
  rw [Darboux.rho, map_smul]
  exact ht () (Set.mem_univ _)

end GlobalTheory.ConeTateSupp

theorem GlobalTheory.ConeTateSupp.finsupp : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ y : Fin b × Fin (b + a') → AF F, ∀ (m : ℕ) (b₀ : Module.Basis (Fin m) F E), ∃ K : Set (Fin m → FiniteAdeleRing (𝓞 F) F), IsCompact K ∧ ∀ a, (fun i => ((Algebra.TensorProduct.basis (AF F) b₀).equivFun a i).2) ∉ K → (fun a : AE F E => e (G.M.co.rho B.ψ (a • Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Φ) y) a = 0 := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT _ Φ hΦ y m b₀
  have hstd := hT.base.std
  choose c hc using GlobalTheory.ConeTateSupp.trace_mul_dual (F := F) (E := E) b₀
  have hO := fun i => GlobalTheory.ConeTateSupp.rho_fixed G.M B.ψ hstd.1 Φ hΦ
    (inclR (F := F) (AF F) (σ (c i)) • Matrix.vecMulVec (incV F H.y) (incV F H'.x))
  obtain ⟨U, hU, hUm⟩ := GlobalTheory.ScalarAnnih.exists_compact_annihilator_finiteAdeles_traceChar F B.ψ hstd.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hstd) _
    (Filter.eventually_all.2 hO)
  refine ⟨Set.pi Set.univ fun _ => U, isCompact_univ_pi fun _ => hU, fun l hl => ?_⟩
  by_contra hne
  refine hl fun i _ => hUm _ fun t ht => ?_
  have hfix := ht i
  have h1 := congrArg e (GlobalTheory.XTermSupp.rho_comm G.M.co B.ψ (l • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
    (pairA F 0 t • inclR (F := F) (AF F) (σ (c i)) • Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Φ)
  rw [hfix, map_smul, he.inv _ (Or.inl ⟨pairA F 0 t • inclR (F := F) (AF F) (σ (c i)) • incV F H.y, by
      rw [Matrix.smul_vecMulVec, Matrix.smul_vecMulVec]⟩) _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd _ _ hΦ),
    GlobalTheory.ConeTateSupp.symp_shift hT.base.cm hT.geo.hW.skew H H' hC.hH.xy hC.hH'.xy, hc] at h1
  have h2 : pairA F 0 t * (Algebra.TensorProduct.basis (AF F) b₀).equivFun l i =
      pairA F 0 (t * ((Algebra.TensorProduct.basis (AF F) b₀).equivFun l i).2) := Prod.ext (zero_mul _) rfl
  rw [h2] at h1
  have h3 := congrFun h1 y
  rw [Pi.smul_apply, smul_eq_mul] at h3
  exact ((mul_eq_right₀ hne).1 h3.symm)
