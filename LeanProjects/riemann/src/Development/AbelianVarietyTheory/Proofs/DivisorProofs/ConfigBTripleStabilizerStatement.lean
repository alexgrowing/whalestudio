import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeFinSupp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem cA_cA (hcm : IsCMExt F E σ) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = a ⊗ₜ[F] e
    rw [GlobalTheory.XTermSupp.invol hcm]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem symp_shiftB (hcm : IsCMExt F E σ) {n d n₁ d₁ : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (JW j i) = -JW i j) (H : Plane E n n₁) (H' : Plane E d d₁) (hH : form σ JX H.x H.y = 1)
    (hH' : form σ JW H'.x H'.y = 1) (l : (AE F E)ˣ) (a : AF F) (c : E) :
    symp (cA σ) (-1) (incM F JX) (incM F JW)
      (a • inclR (F := F) (AF F) c • Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (shiftB σ H H' l) =
      a * Algebra.trace (AF F) (AE F E) ((l : AE F E) * inclR (F := F) (AF F) c) := by
  rw [← smul_assoc, symp, shiftB, GlobalTheory.XTermSupp.hTens_vv, GlobalTheory.XTermSupp.form_inc, GlobalTheory.XTermSupp.form_inc, hH,
    GlobalTheory.XTermSupp.form_skew hcm hJ, hH', cA_cA hcm, ← smul_eq_mul a, ← map_smul (Algebra.trace (AF F) (AE F E))]
  congr 1
  simp [mul_comm]

private theorem I_zero {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (h : UA σ W.J) :
    M.I om 0 h = 0 := by
  simp [Model.I, theta, thetaSum]

private theorem finsupp : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h, ∃ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U ∧
      ∀ (k : K) (l : (AE F E)ˣ), (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∉ U →
        G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) 1 = 0 := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e he K hK X om om' om₁ om₁' hT _ Φ hΦ h
  have hstd := hT.base.std
  have hΦ' : Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) := by
    refine (Submodule.span_le.2 ?_ : PolData B G.M' ≤ _) hΦ.1
    rintro Φ ⟨f, -, φ, hSB, hvac, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hvac.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2)
  have hKc : IsCompact (K : Set (UA σ G.V'.J)) := by
    obtain ⟨K', -, -, hK', hc, -⟩ := GlobalTheory.StabHaar.stabEx hKP.base F E σ B (b + 2) G.V' _ _ hT.base hT.geo.hV'
    have : K = K' := Subgroup.ext fun g => (hK g).trans (hK' g).symm
    rwa [this]
  choose c hc using GlobalTheory.XTermSupp.trace_mul_dual (F := F) (E := E)
  have hO := fun i => GlobalTheory.XTermSupp.rho_om_fixed G.M' B.ψ hstd.1 hT.weil' hKc h Φ hΦ'
    (inclR (F := F) (AF F) (c i) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
  obtain ⟨U, hU, hUm⟩ := GlobalTheory.ScalarAnnih.exists_compact_annihilator_finiteAdeles_traceChar F B.ψ hstd.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hstd) _
    (Filter.eventually_all.2 hO)
  refine ⟨Set.pi Set.univ fun _ => U, isCompact_univ_pi fun _ => hU, fun k l hl => ?_⟩
  suffices h0 : e (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ)) = 0 by rw [h0, I_zero]
  by_contra hne
  refine hl fun i _ => hUm _ fun t ht => ?_
  have hfix := ht i k.1 k.2
  have hΨ : om' (k.1, h) Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) :=
    (IsUWeilPair.isUSplitting hT.weil').pres _ _ hΦ'
  have h1 := congrArg e (GlobalTheory.XTermSupp.rho_comm G.M'.co B.ψ (pairA F 0 t • inclR (F := F) (AF F) (c i) •
    Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (shiftB σ H H' l) (om' (k.1, h) Φ))
  rw [hfix, map_smul, he.inv _ (Or.inl ⟨pairA F 0 t • inclR (F := F) (AF F) (c i) • incV F H'.y, by
      rw [Matrix.vecMulVec_smul, Matrix.vecMulVec_smul]⟩) _ (GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hstd _ _ hΨ),
    symp_shiftB hT.base.cm hT.geo.hW.skew H H' hC.hH.xy hC.hH'.xy, hc] at h1
  have h2 : pairA F 0 t * GlobalTheory.XTermMaj.crd F E (l : AE F E) i = pairA F 0 (t * (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) :=
    Prod.ext (zero_mul _) rfl
  rw [h2] at h1
  exact (smul_left_injective ℂ hne (h1.symm.trans (one_smul ℂ _).symm))

end GlobalTheory.ConeFinSupp

end

theorem _root_.GlobalTheory.T.config_B_triple_stabilizer : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h, ∃ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U ∧
      ∀ (k : K) (l : (AE F E)ˣ), (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∉ U →
        G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) 1 = 0 :=
  GlobalTheory.ConeFinSupp.finsupp
