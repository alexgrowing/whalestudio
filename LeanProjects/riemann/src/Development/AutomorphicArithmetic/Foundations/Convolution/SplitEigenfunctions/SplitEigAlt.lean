import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Splt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.KeyFock
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.FstDetFin
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SpanCont
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem mc_fix {G V H : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] (ι : H →* G)
    (hsm : ∀ f, ∀ᶠ h in 𝓝 (1 : H), ρ (ι h) f = f) {c : G → ℂ} (hc : c ∈ I.MC ρ)
    (hinv : ∀ g h, c (g * ι h) = c g) :
    c ∈ Submodule.span ℂ {c | ∃ (Λ : V →ₗ[ℂ] ℂ) (f : V), (∀ h, ρ (ι h) f = f) ∧ c = fun x => Λ (ρ x f)} := by
  obtain ⟨n, a, b, hab⟩ := Submodule.mem_span_set'.1 hc
  choose Λ f hb using fun i => (b i).2
  have hval : ∀ x, c x = ∑ i, a i * Λ i (ρ x (f i)) := by
    intro x
    rw [← hab]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb i]
  let R : H →* Module.End ℂ (Fin n → V) :=
    { toFun := fun h => LinearMap.pi fun i => (ρ (ι h)).comp (LinearMap.proj i)
      map_one' := LinearMap.ext fun x => funext fun i => by simp
      map_mul' := fun p q => LinearMap.ext fun x => funext fun i => by simp }
  have hR : ∀ h (x : Fin n → V) i, R h x i = ρ (ι h) (x i) := fun _ _ _ => rfl
  obtain ⟨s, hs, hfix⟩ := UpperTheory.ConvolutionTheory.R2.H.avg H (Fin n → V) R f (by
    have : ∀ᶠ h in 𝓝 (1 : H), ∀ i, ρ (ι h) (f i) = f i := Filter.eventually_all.2 fun i => hsm (f i)
    filter_upwards [this] with h hh
    funext i
    exact hh i)
  let S : Fin n → V := ∑ k ∈ s, R k f
  have hS : ∀ i, S i = ∑ k ∈ s, ρ (ι k) (f i) := fun i => by
    simp only [S, Finset.sum_apply, hR]
  have hcard : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hs)
  have key : c = (s.card : ℂ)⁻¹ • ∑ i, a i • fun x => Λ i (ρ x (S i)) := by
    funext x
    have h1 : (s.card : ℂ) * c x = ∑ k ∈ s, c (x * ι k) := by
      simp only [hinv, Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ k ∈ s, c (x * ι k) = ∑ i, a i * Λ i (ρ x (S i)) := by
      simp only [hval, hS, map_sum, map_mul, Module.End.mul_apply, Finset.mul_sum]
      exact Finset.sum_comm
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [← h2, ← h1, inv_mul_cancel_left₀ hcard]
  rw [key]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Λ i, S i, fun h => ?_, rfl⟩))
  have := congrFun (hfix h) i
  exact this

private theorem tj_fin {K : Type} [Field K] [NumberField K] (w : P K) (n : ℕ) {ϖ : Kv w} (hϖ : Formalism.UG.IsUnifV K w ϖ) (j : ℕ) :
    (Function.support fun c : GL (Fin n) (Kv w) ⧸ GlobalTheory.LFun.KGL w n => Formalism.UG.Tj ℂ n (Formalism.UG.Ov K w) ϖ j c.out).Finite := by
  have := GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm K w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ j)
    (1 : Representation ℂ (GL (Fin n) (Kv w)) ℂ) (1 : ℂ)
  simpa using this

private theorem tj_sum {K : Type} [Field K] [NumberField K] (w : P K) (n : ℕ) {ϖ : Kv w} (hϖ : Formalism.UG.IsUnifV K w ϖ) (j : ℕ)
    (W : GL (Fin n) (Kv w) → ℂ) (g : GL (Fin n) (Kv w)) :
    ∑ᶠ c : GL (Fin n) (Kv w) ⧸ GlobalTheory.LFun.KGL w n, Formalism.UG.Tj ℂ n (Formalism.UG.Ov K w) ϖ j c.out * W (g * c.out) =
      ∑ c ∈ (tj_fin w n hϖ j).toFinset, Formalism.UG.Tj ℂ n (Formalism.UG.Ov K w) ϖ j c.out * W (g * c.out) := by
  refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
  simp only [Set.Finite.coe_toFinset, Function.mem_support] at hc ⊢
  exact left_ne_zero_of_mul hc

private theorem eig_span {K : Type} [Field K] [NumberField K] (w : P K) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (Kv w)) V) {B : Multiset ℂˣ} (hB : GlobalTheory.LFun.HasSatGL w ρ B)
    {c : GL (Fin n) (Kv w) → ℂ}
    (hc : c ∈ Submodule.span ℂ {c | ∃ (Λ : V →ₗ[ℂ] ℂ) (f : V), (∀ k ∈ GlobalTheory.LFun.KGL w n, ρ k f = f) ∧ c = fun x => Λ (ρ x f)}) :
    Eig w B c := by
  induction hc using Submodule.span_induction with
  | mem c h =>
    obtain ⟨Λ, f, hf, rfl⟩ := h
    refine ⟨hB.card, fun g k hk => ?_, fun ϖ hϖ j hj g => ?_⟩
    · rw [map_mul, Module.End.mul_apply, hf k hk]
    · by_cases h0 : f = 0
      · subst h0
        simp
      have he := (hB.2 f (GlobalTheory.LGrp.mem_fixed.2 hf) h0).2.2.2 ϖ hϖ j hj
      let L : V →+ ℂ := (Λ.comp (ρ g)).toAddMonoidHom
      have hs := L.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm K w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ f)
      refine Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans ((congrArg L he).trans ?_))
      · simp [L, map_mul]
      · simp [L]
  | zero => exact ⟨hB.card, by simp, by simp⟩
  | add a b _ _ ha hb =>
    refine ⟨hB.card, fun g k hk => ?_, fun ϖ hϖ j hj g => ?_⟩
    · simp only [Pi.add_apply, ha.inv g k hk, hb.inv g k hk]
    · have e1 := ha.eig ϖ hϖ j hj g
      have e2 := hb.eig ϖ hϖ j hj g
      rw [tj_sum w n hϖ j] at e1 e2 ⊢
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, e1, e2]
  | smul z a _ ha =>
    refine ⟨hB.card, fun g k hk => ?_, fun ϖ hϖ j hj g => ?_⟩
    · simp only [Pi.smul_apply, ha.inv g k hk]
    · have e1 := ha.eig ϖ hϖ j hj g
      rw [tj_sum w n hϖ j] at e1 ⊢
      simp only [Pi.smul_apply, smul_eq_mul]
      calc _ = z * ∑ c ∈ (tj_fin w n hϖ j).toFinset, Formalism.UG.Tj ℂ n (Formalism.UG.Ov K w) ϖ j c.out * a (g * c.out) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _
        _ = _ := by rw [e1, mul_left_comm]

private theorem kgl_map {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] {n : ℕ} {v : P K} {w : P M}
    (c : Kv v ≃+* Kv w) (hc : ∀ x, Valued.v (c x) = Valued.v x) (g : GL (Fin n) (Kv v)) :
    g ∈ GlobalTheory.LFun.KGL v n ↔ Matrix.GeneralLinearGroup.map c.toRingHom g ∈ GlobalTheory.LFun.KGL w n := by
  have hO : ∀ x, c x ∈ Formalism.UG.Ov M w ↔ x ∈ Formalism.UG.Ov K v := fun x => by
    change Valued.v (c x) ≤ 1 ↔ Valued.v x ≤ 1
    rw [hc]
  have hGv : ∀ (g : GL (Fin n) (Kv v)) i j, (Matrix.GeneralLinearGroup.map c.toRingHom g).1 i j = c (g.1 i j) := fun _ _ _ => rfl
  simp only [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff, ← map_inv, hGv, hO]

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.splitEig :
    SplitEig := by
  intro E _ _ _ D W M N P π Φ hΦ v w hs B hB hFix g
  obtain ⟨hq, i, hc, hx, hv⟩ := hs
  obtain ⟨θ, hθ⟩ := UpperTheory.ConvolutionTheory.R2.I.splt ℚ E D v w i hc hx
  have hmc := UpperTheory.ConvolutionTheory.R2.I.key ℚ E D W M π v θ _ hθ Φ hΦ g
  let gm : GL (Fin 2) (Kv v) →* GL (Fin 2) (Kv w) := Matrix.GeneralLinearGroup.map i.toRingHom
  let gi : GL (Fin 2) (Kv w) →* GL (Fin 2) (Kv v) := Matrix.GeneralLinearGroup.map i.symm.toRingHom
  have hgm : ∀ y, gm (gi y) = y := fun y => by
    ext a b
    simp [gm, gi]
  have hgi : ∀ y, gi (gm y) = y := fun y => by
    ext a b
    simp [gm, gi]
  let c : GL (Fin 2) (Kv v) → ℂ := fun x => WE D Φ.1 (g * lc w (gm x))
  have hinv : ∀ x (k : GlobalTheory.LFun.KGL v 2), c (x * (GlobalTheory.LFun.KGL v 2).subtype k) = c x := by
    intro x k
    have hk : gm k.1 ∈ GlobalTheory.LFun.KGL w 2 := (kgl_map i hv k.1).1 k.2
    change WE D Φ.1 (g * lc w (gm (x * k.1))) = WE D Φ.1 (g * lc w (gm x))
    unfold WE
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [map_mul, map_mul, ← mul_assoc g, ← mul_assoc _ _ (lc w (gm k.1)), hFix _ _ hk]
  haveI : CompactSpace (GlobalTheory.LFun.KGL v 2) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL v 2).2
  have hsm : ∀ f, ∀ᶠ h in 𝓝 (1 : GlobalTheory.LFun.KGL v 2), π.locRep v ((GlobalTheory.LFun.KGL v 2).subtype h) f = f := fun f =>
    (continuous_subtype_val.tendsto (1 : GlobalTheory.LFun.KGL v 2)).eventually
      (((UpperTheory.ConvolutionTheory.R2.I.locSm ℚ π v).1 f).mem_nhds (by simp))
  have h1 := mc_fix (π.locRep v) (GlobalTheory.LFun.KGL v 2).subtype hsm hmc hinv
  let ρ' : Representation ℂ (GL (Fin 2) (Kv w)) π.V := (π.locRep v).comp gi
  have hq' : Formalism.UG.qV E w = Formalism.UG.qV ℚ v := by
    simpa [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply, normV] using hq
  have hB' : GlobalTheory.LFun.HasSatGL w ρ' B :=
    GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i hv hq' (LinearEquiv.refl ℂ _) (fun x f => by
      change π.locRep v (gi (gm x)) f = π.locRep v x f
      rw [hgi]) hB
  have e : (fun y => WE D Φ.1 (g * finGL E 2 (locGL E 2 w y))) = LinearMap.funLeft ℂ ℂ gi c := by
    funext y
    change _ = WE D Φ.1 (g * lc w (gm (gi y)))
    rw [hgm]
    rfl
  rw [e]
  refine eig_span w ρ' hB' ((Submodule.map_span_le _ _ _).2 ?_ (Submodule.mem_map_of_mem h1))
  rintro _ ⟨Λ, f, hf, rfl⟩
  refine Submodule.subset_span ⟨Λ, f, fun k hk => ?_, rfl⟩
  have : gi k ∈ GlobalTheory.LFun.KGL v 2 := (kgl_map i hv (gi k)).2 (by rwa [hgm])
  exact hf ⟨gi k, this⟩
