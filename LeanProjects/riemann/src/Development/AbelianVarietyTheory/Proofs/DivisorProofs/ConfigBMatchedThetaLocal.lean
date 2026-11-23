import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JmConjTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterComponentDegreeLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedRealFrameExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedRealLineFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedRealLineSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedRealLineThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowIrreducibleEigenspaceSupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartInvariantSubmoduleDenseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartLeFixedPartImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowDegreeLeFixedDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanThetaPolynomialLiftExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPolynomialTensorCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestDegreeComponentNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartTensorSpanStatement

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.RealLift Formalism.BasicNotions.TH GlobalTheory.FockBridge

namespace GlobalTheory.FockBottom

section Centre

variable {R S : ℕ}

def cen (r₀ : Fin R) (s₀ : Fin S) : Mat R S := Eab (.inl r₀) (.inl r₀) + Eab (.inr s₀) (.inr s₀)

theorem cen_apply (r₀ : Fin R) (s₀ : Fin S) (a b : Ix R S) :
    cen r₀ s₀ a b = if a = b then (if b = .inl r₀ ∨ b = .inr s₀ then 1 else 0) else 0 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [cen, Eab, Matrix.single_apply] <;> aesop

theorem isKC_cen (r₀ : Fin R) (s₀ : Fin S) : IsKC (cen r₀ s₀) :=
  GlobalTheory.FockKStab.isKC_add (GlobalTheory.FockLowDeg.isKC_Eab_diag _) (GlobalTheory.FockLowDeg.isKC_Eab_diag _)

theorem trace_cen (r₀ : Fin R) (s₀ : Fin S) : (cen r₀ s₀).trace = 2 := by
  rw [cen, Matrix.trace_add, GlobalTheory.FockLowDeg.trace_Eab_diag, GlobalTheory.FockLowDeg.trace_Eab_diag]; norm_num

theorem cen_conjTranspose (r₀ : Fin R) (s₀ : Fin S) : (cen r₀ s₀)ᴴ = cen r₀ s₀ := by
  simp [cen, Eab, Matrix.conjTranspose_single]

end Centre

section Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ Y W} {om : Rep σ Y W}
  {C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ} {Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)}
  {c : InfinitePlace F → ℂ} {Z : Type} [AddCommGroup Z] [Module ℂ Z] {p : SInf F (Fin n × Fin d) →ₗ[ℂ] Z}

theorem q_genOp {q : Tens F P Q R S →ₗ[ℂ] Z} (hq : Function.Surjective q)
    (hK : ∀ w X, Keeps q (atPl w (fockAct2 P Q R S X))) (Yg : InfinitePlace F → Mat R S) (T : Tens F P Q R S) :
    q (genOp P Q c Yg T) = (∑ w, (fockOp q w (Yg w) + (c w * (Yg w).trace) • 1)) (q T) := by
  rw [genOp_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_add, map_smul, LinearMap.add_apply, fockOp_apply hq (hK w)]
  rfl

theorem centLine (hcm : IsCMExt F E σ) (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    (hθ : ∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    (r₀ : Fin R) (s₀ : Fin S) (θ : InfinitePlace F → ℝ) :
    ∃ k ∈ KInf σ W B.emb, (∀ w,
      (∀ i, ((mat k).map (piInf (B.emb w)) * C w) i (.inl r₀) = Complex.exp (θ w * Complex.I) * C w i (.inl r₀)) ∧
      (∀ i, ((mat k).map (piInf (B.emb w)) * C w) i (.inr s₀) = Complex.exp (θ w * Complex.I) * C w i (.inr s₀)) ∧
      ∀ b, b ≠ .inl r₀ → b ≠ .inr s₀ → ∀ i, ((mat k).map (piInf (B.emb w)) * C w) i b = C w i b) ∧
      ∃ U : Module.End ℂ (Tens F P Q R S), IsExp (genOp P Q c fun w => (θ w * Complex.I) • cen r₀ s₀) U ∧
        ∀ T, Acts (evI F) (om (1, k)) (Φ T) (Φ (U T)) := by
  obtain ⟨k, hk, hkC, hU⟩ := exp_of_skew hcm hC hθ hact hadm (fun w => (θ w * Complex.I) • cen r₀ s₀)
    (fun w => GlobalTheory.FockKStab.isKC_smul (isKC_cen r₀ s₀) _)
    (fun w => by simp [Matrix.conjTranspose_smul, cen_conjTranspose])
  refine ⟨k, hk, fun w => ⟨fun i => ?_, fun i => ?_, fun b h1 h2 i => ?_⟩, hU⟩
  · rw [hkC]; exact mul_exp_col _ _ _ _ (fun a => by simp [cen_apply]) i
  · rw [hkC]; exact mul_exp_col _ _ _ _ (fun a => by simp [cen_apply]) i
  · rw [hkC, mul_exp_col _ _ b 0 (fun a => by simp [cen_apply, h1, h2]) i, Complex.exp_zero, one_mul]

theorem chr_eq {χ : Chr F E} {m : InfinitePlace F → ℤ} (hχ : HasExp B.emb χ m) {t : (AE F E)ˣ}
    (ht : At (evI F) ((t : AE F E) - 1)) (θ : InfinitePlace F → ℝ)
    (h : ∀ w, piInf (B.emb w) (t : AE F E) = Complex.exp (θ w * Complex.I)) :
    (χ t : ℂ) = Complex.exp (∑ w, θ w * Complex.I * m w) := by
  rw [hχ t ht, Complex.exp_sum]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [h, Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, div_one, mul_comm _ (m w : ℂ), Complex.exp_int_mul]

theorem isTwEig_iff {H' : Plane E d d₁} {i₀ i₁ r s r₁ s₁ : ℕ} (hB : B.IsGood σ) (hW : W.IsSkew σ B r s)
    (hW₁ : W₁.IsSkew σ B r₁ s₁) (hH : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    (hθ : ∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S) {r₀ : Fin R} {s₀ : Fin S} (hAd : IsAdaptedFrame B H' C r₀ s₀)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    (hr : LinearMap.range Φ = M.Pol B.ψ B.emb) (hq : Function.Surjective (p ∘ₗ Φ))
    (hK : ∀ w X, Keeps (p ∘ₗ Φ) (atPl w (fockAct2 P Q R S X))) {χ : Chr F E} {m : InfinitePlace F → ℤ}
    (hχ : HasExp B.emb χ m) (z : ℝ) (x : Z) :
    IsTwEig B M om p W₁ H' χ z x ↔ ∀ w, fockOp (p ∘ₗ Φ) w (cen r₀ s₀) x = ((m w : ℂ) - 2 * c w) • x := by
  have hA := GlobalTheory.T.adapted_real_line_second F E σ B d d₁ i₀ i₁ r s r₁ s₁ W W₁ H' hB hW hW₁ hH R S r₀ s₀ C hC hθ hAd
  constructor
  · intro h w
    obtain ⟨T, rfl⟩ := hq x
    set q := p ∘ₗ Φ with hqdef
    let θ : ℝ → InfinitePlace F → ℝ := fun s => Pi.single w s
    let L : Module.End ℂ (Tens F P Q R S) := genOp P Q c fun w' => (θ 1 w' * Complex.I) • cen r₀ s₀
    have hL : ∀ s : ℝ, (genOp P Q c fun w' => (θ s w' * Complex.I) • cen r₀ s₀) = (s : ℂ) • L := fun s => by
      rw [← genOp_smul]
      congr 1
      funext w'
      by_cases e : w' = w
      · subst e; simp [θ, smul_smul]
      · simp [θ, Pi.single_eq_of_ne e]
    have hs : ∀ s : ℝ, ∃ U, IsExp ((s : ℂ) • L) U ∧ q (U T) = Complex.exp (s * (Complex.I * m w)) • q T := fun s => by
      obtain ⟨k, hk, hcol, U, hU, hAc⟩ := centLine hB.cm hC hθ hact hadm r₀ s₀ (θ s)
      obtain ⟨t, hL1, ht⟩ := GlobalTheory.T.adapted_real_line_third F E σ B d d₁ i₀ i₁ r _ r₁ s₁ W W₁ H' hB hW hW₁ hH R S r₀ s₀ C hC hθ hAd _
        (fun w' => Complex.norm_exp_ofReal_mul_I _) k hk.1 hcol
      obtain ⟨h1, h2, -⟩ := hA k hk t hL1
      refine ⟨U, hL s ▸ hU, ?_⟩
      have := h k hk t hL1 (Φ T) (hr ▸ LinearMap.mem_range_self Φ T) _ (hAc T) rfl
      rw [h2, Real.one_rpow, Complex.ofReal_one, mul_one, chr_eq hχ h1 (θ s) ht, Finset.sum_eq_single w] at this
      · simp only [θ, Pi.single_eq_same, mul_assoc] at this
        exact this
      · intro w' _ e; simp [θ, Pi.single_eq_of_ne e]
      · simp
    have hmem := GlobalTheory.FockKStab.mem_of_exp L (genOp_locFin c fun w' => GlobalTheory.FockKStab.isKC_smul (isKC_cen r₀ s₀) _)
      ((Submodule.span ℂ {q T}).comap q) T fun s => by
        obtain ⟨U, hU, e⟩ := hs s
        exact ⟨U, hU, by rw [Submodule.mem_comap, e]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1 (Submodule.mem_comap.1 hmem)
    have hL0 : ∀ v, q (L v) = Complex.I • (fockOp q w (cen r₀ s₀) (q v) + (2 * c w) • q v) := fun v => by
      rw [q_genOp hq hK, Finset.sum_eq_single w]
      · simp only [θ, Pi.single_eq_same, Complex.ofReal_one, one_mul, map_smul, Matrix.trace_smul, trace_cen,
          LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, smul_add, smul_smul, smul_eq_mul]
        congr 2; ring
      · intro w' _ e; simp [θ, Pi.single_eq_of_ne e]
      · simp
    by_cases h0 : q T = 0
    · simp [h0]
    have hμm : μ = Complex.I * m w := exp_mul_eq fun s => by
      obtain ⟨U, hU, e⟩ := hs s
      have := isExp_eig hU q (((s : ℂ) * Complex.I) • (fockOp q w (cen r₀ s₀) + (2 * c w) • 1))
        (fun v => by rw [LinearMap.smul_apply, map_smul, hL0, smul_smul]; rfl) (T := T) (μ := s * μ)
        (by rw [mul_smul (s : ℂ) μ, hμ, hL0, smul_smul]; rfl)
      exact smul_left_injective ℂ h0 (this.symm.trans e)
    rw [hL0, hμm, mul_smul] at hμ
    have := smul_right_injective Z Complex.I_ne_zero hμ
    rw [sub_smul, this]; simp
  · intro h k hk t hL f hf f₁ hf₁ hx
    obtain ⟨h1, h2, h3⟩ := hA k hk t hL
    let θ : InfinitePlace F → ℝ := fun w => Complex.arg (piInf (B.emb w) (t : AE F E))
    have ht : ∀ w, piInf (B.emb w) (t : AE F E) = Complex.exp (θ w * Complex.I) := fun w => by
      have := Complex.norm_mul_exp_arg_mul_I (piInf (B.emb w) (t : AE F E))
      rw [(h3 w).1, Complex.ofReal_one, one_mul] at this
      exact this.symm
    obtain ⟨k', hk', hcol, U, hU, hAc⟩ := centLine hB.cm hC hθ hact hadm r₀ s₀ θ
    have hkk : k = k' := eq_of_frame hB.cm hC hk.1 hk'.1 fun w => by
      ext i b
      by_cases e1 : b = .inl r₀
      · rw [e1, (h3 w).2.1, (hcol w).1, ht]
      by_cases e2 : b = .inr s₀
      · rw [e2, (h3 w).2.2.1, (hcol w).2.1, ht]
      rw [(h3 w).2.2.2 b e1 e2, (hcol w).2.2 b e1 e2]
    subst hkk
    obtain ⟨T, rfl⟩ := Main.pol_eq B M Φ hr hf
    rw [acts_unique hf₁ (hAc T), h2, Real.one_rpow, Complex.ofReal_one, mul_one, chr_eq hχ h1 θ ht, ← hx]
    refine isExp_eig hU (p ∘ₗ Φ) _ (q_genOp hq hK _) ?_
    rw [LinearMap.sum_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hw := h w
    rw [← hx] at hw
    change fockOp (p ∘ₗ Φ) w (cen r₀ s₀) ((p ∘ₗ Φ) T) = _ • (p ∘ₗ Φ) T at hw
    simp only [map_smul, Matrix.trace_smul, trace_cen, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, hw,
      smul_smul, smul_eq_mul, ← add_smul]
    congr 1; ring

end Model

section Triple

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {a a' P Q R S : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {Rm : RealMaps F a a'}
  {Rf : FinMaps F a a'} {A : InfinitePlace F → Matrix (Fin a) (Ix P Q) ℂ}
  {C : InfinitePlace F → Matrix (Fin (a + a')) (Ix R S) ℂ} {Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin a × Fin (a + a'))}

theorem range_eq (hT : IsTriple B G X om om') (hD : IsFockData B G.M A C Φ) : LinearMap.range Φ = G.M.Pol B.ψ B.emb :=
  Main.i_polrange Main.i_actslaws Main.i_derex (Main.i_vacline Main.i_derex) F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ
    hT.base.cm hT.base.std hD.1.1 hD.1.2.1 hD.1.2.2 hD.2

theorem lieSecond (hKP : KP) : LieSecond :=
  Main.i_liesecond hKP.base Main.i_derex (Main.i_fockex Main.i_derex) (Main.i_vacline Main.i_derex)
    (Main.i_liescalar hKP.base Main.i_derex (Main.i_vacline Main.i_derex))

theorem actsBy_second (hKP : KP) (hT : IsTriple B G X om om') (hD : IsFockData B G.M A C Φ) :
    ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) fun w => (B.mβ w : ℂ) / 2 := by
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hT.weil
  exact lieSecond hKP F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hT.base.cm hT.base.std hD.1.1 hD.2
    hwp.1 hT.chars.expβ

theorem admissible_weil_action (hT : IsTriple B G X om om') :
    ∀ g, ∀ l ∈ (adeleClass F).adm (Fin a × Fin (a + a')), l ∘ₗ om g ∈ (adeleClass F).adm (Fin a × Fin (a + a')) := by
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hT.weil
  exact fun g => (hwp.isUSplitting).adm g

theorem surj_q (hM : IsMatched B G X om om' Rm Rf) (hD : IsFockData B G.M A C Φ) : Function.Surjective (Rm.p ∘ₗ Φ) := by
  rw [← LinearMap.range_eq_top, LinearMap.range_comp, range_eq hM.triple hD]
  exact hM.real.quot.onto

theorem keeps_q (hKP : KP) (hM : IsMatched B G X om om' Rm Rf) (hD : IsFockData B G.M A C Φ) (w : InfinitePlace F)
    (Z : Mat R S) : Keeps (Rm.p ∘ₗ Φ) (atPl w (fockAct2 P Q R S Z)) := by
  have key : ∀ Y ∈ upq R S, Keeps (Rm.p ∘ₗ Φ) (atPl w (fockAct2 P Q R S Y)) := by
    intro Y hY T hT0
    obtain ⟨γ, hγ, hgen⟩ := Main.i_lineex F E σ (Fin (a + a')) R S B.emb (incM F G.W.J) Complex.I C hM.triple.base.cm
      hD.1.1.2.2 (Pi.single w Y) fun w' => by
        by_cases h : w' = w
        · subst h; simpa using hY
        · simpa [Pi.single_eq_of_ne h] using Main.zero_mem_upq R S
    have hsd := actsBy_second hKP hM.triple hD γ hγ _ hgen T
    have h1 := (Main.i_actslaws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) hsd
    have h0 : ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) (0 : SInf F (Fin a' × Fin (a + a')))
        (0 : SInf F (Fin a' × Fin (a + a'))) := by
      intro r _ x
      have e : tens (evI F) (0 : SInf F (Fin a' × Fin (a + a'))) r = 0 := by funext y; simp [tens]
      simp only [e, map_zero]
      exact hasDerivAt_const _ _
    have h2 := hM.real.lie γ hγ (Φ T) (range_eq hM.triple hD ▸ LinearMap.mem_range_self Φ T) 0 (Submodule.zero_mem _) _ 0
      h1 h0 (by rw [map_zero]; exact hT0)
    rw [map_zero] at h2
    change (Rm.p ∘ₗ Φ) (genOp P Q _ (Pi.single w Y) T) = 0 at h2
    rwa [genOp_single, map_add, map_smul, hT0, smul_zero, add_zero] at h2
  obtain ⟨Y₁, h₁, Y₂, h₂, rfl⟩ := upq_decomp Z
  intro T hT0
  rw [map_add, map_smul, Main.atPl_add, Main.atPl_smul, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    key Y₁ h₁ T hT0, key Y₂ h₂ T hT0, smul_zero, add_zero]

theorem fockOp_mem (hKP : KP) (hM : IsMatched B G X om om' Rm Rf) (hD : IsFockData B G.M A C Φ) (I : Set (Ix R S))
    (N : Submodule ℂ Rm.Pi)
    (hN : ∀ k ∈ KInf σ G.W B.emb, (∀ w, ∀ b ∈ I, ∀ i, ((mat k).map (piInf (B.emb w)) * C w) i b = C w i b) →
      ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, k)) f f₁ → Rm.p f ∈ N → Rm.p f₁ ∈ N)
    (w : InfinitePlace F) (Z : Mat R S) (hZ : IsKC Z) (hI : ∀ b ∈ I, ∀ a, Z a b = 0 ∧ Z b a = 0) {v : Rm.Pi} (hv : v ∈ N) :
    fockOp (Rm.p ∘ₗ Φ) w Z v ∈ N := by
  obtain ⟨T, rfl⟩ := surj_q hM hD v
  rw [fockOp_apply (surj_q hM hD) (keeps_q hKP hM hD w)]
  exact stab_of_fix hM.triple.base.cm hD.1.1.2.2 hD.1.2.2 (actsBy_second hKP hM.triple hD) (admissible_weil_action hM.triple) I
    (N.comap (Rm.p ∘ₗ Φ)) (fun k hk hfix T hT T' hA =>
      hN k hk hfix (Φ T) (range_eq hM.triple hD ▸ LinearMap.mem_range_self Φ T) _ hA hT) w Z hZ hI hv

theorem low_stab (hKP : KP) (hM : IsMatched B G X om om' Rm Rf) (hD : IsFockData B G.M A C Φ) (w : InfinitePlace F)
    (Z : Mat R S) (hZ : IsKC Z) {v : Rm.Pi} (hv : v ∈ lowPartInf B G.M Rm.p) :
    fockOp (Rm.p ∘ₗ Φ) w Z v ∈ lowPartInf B G.M Rm.p :=
  fockOp_mem hKP hM hD ∅ _ (fun k hk _ => (GlobalTheory.T.low_part_compact_stable hKP F E σ B a a' G X om om' Rm Rf hM).1 k hk) w Z hZ
    (fun _ h => h.elim) hv

theorem low_irr (hKP : KP) (hM : IsMatched B G X om om' Rm Rf) (hD : IsFockData B G.M A C Φ) (N : Submodule ℂ Rm.Pi)
    (hle : N ≤ lowPartInf B G.M Rm.p) (hN : ∀ w Z, IsKC Z → ∀ v ∈ N, fockOp (Rm.p ∘ₗ Φ) w Z v ∈ N) :
    N = ⊥ ∨ N = lowPartInf B G.M Rm.p := by
  refine GlobalTheory.T.lowPart_invariant_submodule_dense hKP F E σ B a a' G X om om' Rm Rf hM N hle fun k hk f hf f₁ hf₁ hfN => ?_
  obtain ⟨T, rfl⟩ := Main.pol_eq B G.M Φ (range_eq hM.triple hD) hf
  obtain ⟨Yg, U, hKC, hU, hA⟩ := exp_of_kInf hM.triple.base.cm hD.1.1.2.2 hD.1.2.2 (actsBy_second hKP hM.triple hD)
    (admissible_weil_action hM.triple) hk
  rw [acts_unique hf₁ (hA T)]
  refine isExp_mem hU (N.comap (Rm.p ∘ₗ Φ)) (fun v hv => ?_) hfN
  rw [Submodule.mem_comap, q_genOp (surj_q hM hD) (keeps_q hKP hM hD), LinearMap.sum_apply]
  exact N.sum_mem fun w _ => N.add_mem (hN w _ (hKC w) _ hv) (N.smul_mem _ hv)

theorem kone_stab (hKP : KP) (hM : IsMatched B G X om om' Rm Rf) (hD : IsFockData B G.M A C Φ) {d₁ i₀ i₁ r₁ s₁ : ℕ}
    {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} (hW₁ : W₁.IsSkew σ B r₁ s₁) (hH : H'.IsAdapted σ B G.W W₁ i₀ i₁)
    {r₀ : Fin R} {s₀ : Fin S} (hAd : IsAdaptedFrame B H' C r₀ s₀) (N : Submodule ℂ Rm.Pi)
    (hN : KStabL B G.M om Rm.p W₁ H' N) (w : InfinitePlace F) (Z : Mat R S) (hZ : IsKC Z)
    (h0 : ∀ a, Z a (.inl r₀) = 0 ∧ Z (.inl r₀) a = 0 ∧ Z a (.inr s₀) = 0 ∧ Z (.inr s₀) a = 0) {v : Rm.Pi} (hv : v ∈ N) :
    fockOp (Rm.p ∘ₗ Φ) w Z v ∈ N := by
  refine fockOp_mem hKP hM hD {.inl r₀, .inr s₀} N (fun k hk hfix => ?_) w Z hZ ?_ hv
  · obtain ⟨k₁, hk₁, hL⟩ := GlobalTheory.T.adapted_real_line_first F E σ B _ d₁ i₀ i₁ _ _ r₁ s₁ G.W W₁ H' hM.triple.base hM.triple.geo.hW hW₁ hH R S r₀ s₀ C
      hD.1.1.2.2 hD.1.2.2 hAd k hk fun w => ⟨hfix w _ (by simp), hfix w _ (by simp)⟩
    exact hN k hk k₁ hk₁ hL
  · rintro b (rfl | rfl) a
    · exact ⟨(h0 a).1, (h0 a).2.1⟩
    · exact ⟨(h0 a).2.2.1, (h0 a).2.2.2⟩

end Triple

section Weights

theorem tprod_ne_zero {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V] (v : ι → V)
    (hv : ∀ w, v w ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  choose ℓ hℓ using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  intro h
  have := congrArg (GlobalTheory.TensIrr.prodForm (V := fun _ : ι => V) ℓ) h
  rw [GlobalTheory.TensIrr.prodForm_tprod, map_zero] at this
  simp [hℓ] at this

open GlobalTheory.KFixIrr in

theorem chi_le_tensSpan {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (x : ι → ℚ) (hPR : P ≤ R) (hQS : Q ≤ S)
    (k k' : ι → ℕ) (hk : ∀ w, 0 < k w) (hk' : ∀ w, 0 < k' w) (ek : ∀ w, x w - cPair R S = k w)
    (ek' : ∀ w, x w + cPair R S = k' w) (m : ℕ) (hm : ∀ m' < m, chiPart ι P Q R S x ⊓ degLE ι P Q R S m' = ⊥) :
    chiPart ι P Q R S x ⊓ degLE ι P Q R S m ≤ tensSpan fun w => lowOne P Q R S (x w) (P * k w + Q * k' w) := by
  have hmD : m ≤ ∑ w, (P * k w + Q * k' w) := by
    by_contra hlt
    choose v hv hv0 using fun w => Submodule.exists_mem_ne_zero_of_ne_bot
      (GlobalTheory.T.lowest_degree_component_nonzero P Q R S (x w) (k w) (k' w) hPR hQS (hk w) (hk' w) (ek w) (ek' w))
    refine tprod_ne_zero v hv0 ((Submodule.eq_bot_iff _).1 (hm _ (not_le.1 hlt)) _ ⟨?_, tprod_mem_degLE v ?_⟩)
    · rw [SetLike.mem_coe, mem_chiPart]
      intro w X hX
      rw [GlobalTheory.TensIrr.atPl_tprod, (mem_chiOne _ _).1 ((mem_lowOne _ _ _).1 (hv w)).1 X hX, MultilinearMap.map_update_smul,
        Function.update_eq_self]
    · exact Finset.sum_le_sum fun w _ => ((mem_lowOne _ _ _).1 (hv w)).2
  intro T hT
  refine (Submodule.span_le.2 ?_) (GlobalTheory.T.character_part_tensor_span ι P Q R S x _ T hT)
  rintro _ ⟨g, hg, hs, rfl⟩
  by_cases h0 : ∃ w, g w = 0
  · obtain ⟨w, hw⟩ := h0
    rw [MultilinearMap.map_coord_zero _ w hw]
    exact Submodule.zero_mem _
  push Not at h0
  have hle : ∀ w, P * k w + Q * k' w ≤ (g w).totalDegree := fun w =>
    GlobalTheory.FockLowDeg.lowerDeg P Q R S (x w) (k w) (k' w) (ek w) (ek' w) (g w) (hg w) (h0 w)
  have heq : ∑ w, (P * k w + Q * k' w) = ∑ w, (g w).totalDegree :=
    le_antisymm (Finset.sum_le_sum fun w _ => hle w) (hs.trans hmD)
  exact tprod_mem_tensSpan _ g fun w => (mem_lowOne _ _ _).2
    ⟨hg w, ((Finset.sum_eq_sum_iff_of_le (fun w _ => hle w)).1 heq w (Finset.mem_univ w)).symm.le⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {Rm : RealMaps F a a'}
  {Rf : FinMaps F a a'} {A : InfinitePlace F → Matrix (Fin a) (Ix (a - G.p) G.p) ℂ}
  {C : InfinitePlace F → Matrix (Fin (a + a')) (Ix (a + a' - (G.p + G.q)) (G.p + G.q)) ℂ}
  {Φ : Tens F (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin a × Fin (a + a'))}

open GlobalTheory.KFixIrr in

theorem low_weights (hKP : KP) (hM : IsMatched B G X om om' Rm Rf) (hD : IsFockData B G.M A C Φ) (w : InfinitePlace F)
    (r : Fin (a + a' - (G.p + G.q))) (s : Fin (G.p + G.q)) :
    lowPartInf B G.M Rm.p ≤ ⨆ n : ℕ × ℕ,
      (fockOp (Rm.p ∘ₗ Φ) w (Eab (.inl r) (.inl r))).eigenspace ((((a - G.p : ℕ) : ℂ) - G.p) / 2 + n.1) ⊓
      (fockOp (Rm.p ∘ₗ Φ) w (Eab (.inr s) (.inr s))).eigenspace (-((((a - G.p : ℕ) : ℂ) - G.p) / 2) + n.2) := by
  obtain ⟨hb, hg, hc, hw, hw'⟩ := hM.triple
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := Main.i_liefirst (lieSecond hKP) F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std
    hD.1.1 hD.2 hd hB1 (Main.hasExp_div B.emb hc.expβ hc.expα)
  let c : InfinitePlace F → ℚ := fun w => ((B.mα w - B.mβ w : ℤ) : ℚ) / 2
  have ec : (fun w => -((c w : ℚ) : ℂ)) = fun w => ((B.mβ w - B.mα w : ℤ) : ℂ) / 2 := by
    funext w; simp only [c]; push_cast; ring
  have hW1' : ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ (fockAct1 _ _ _ _) (fun w => -((c w : ℚ) : ℂ)) := by
    rw [ec]; exact hW1
  have hinj : Function.Injective Φ := hD.2.1
  have L1 := GlobalTheory.T.archimedean_theta_polynomial_lift_exists Main.i_actslaws Main.i_derex (Main.i_vacline Main.i_derex) F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb
    A C Φ hb.cm hb.std hD.1.1 hD.1.2.1 hD.1.2.2 hD.2
  have L2 := GlobalTheory.T.archimedean_polynomial_tensor_character Main.i_actslaws Main.i_lineex (Main.i_kline Main.i_lineex) F E σ B _ _ _ _ _ _ G.V G.W om A Φ c
    hb.cm hD.1.1.2.1 hD.1.2.1 hinj hW1' (admissible_weil_action hM.triple)
  have key : ∀ k, fixPart B G.M om k = (chiPart (InfinitePlace F) _ _ _ _ c ⊓ degLE (InfinitePlace F) _ _ _ _ k).map Φ := by
    intro k
    have hs : {f | f ∈ fockDeg G.M B.ψ B.emb k ∧ IsKFix B om f} =
        Φ '' ((chiPart (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) c ⊓
          degLE (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) k : Submodule ℂ _) : Set _) := by
      ext f
      constructor
      · rintro ⟨hf, hfix⟩
        rw [L1 k] at hf
        obtain ⟨T, hT, rfl⟩ := hf
        exact ⟨T, ⟨(L2 T).1 hfix, hT⟩, rfl⟩
      · rintro ⟨T, ⟨h1, h2⟩, rfl⟩
        exact ⟨by rw [L1 k]; exact ⟨T, h2, rfl⟩, (L2 T).2 h1⟩
    rw [fixPart, hs, Submodule.span_image, Submodule.span_eq]
  have bot : ∀ k < fixDeg B G.M om, chiPart (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) c ⊓
      degLE (InfinitePlace F) _ _ _ _ k = ⊥ := by
    intro k hk
    have h0 := fixPart_eq_bot_of_lt B G.M om hk
    rw [key] at h0
    rw [← Submodule.comap_map_eq_of_injective hinj (_ ⊓ _), h0, Submodule.comap_bot, LinearMap.ker_eq_bot.2 hinj]
  have hPR : a - G.p ≤ a + a' - (G.p + G.q) := by have := hg.aBig; omega
  have hQS : G.p ≤ G.p + G.q := Nat.le_add_right _ _
  have hnum : ∀ w, ∃ k k' : ℕ, 0 < k ∧ 0 < k' ∧ c w - cPair (a + a' - (G.p + G.q)) (G.p + G.q) = k ∧
      c w + cPair (a + a' - (G.p + G.q)) (G.p + G.q) = k' := by
    intro w
    have hk := hg.kappa w
    obtain ⟨j, hj⟩ := Main.i_parity F E σ B a a' G X om om' hM.triple w
    obtain ⟨i, hi⟩ := hg.even
    have h1 := hg.eBig
    have h2 := hg.aBig
    have hle : G.p + G.q ≤ a + a' := by omega
    have hR : ((a + a' - (G.p + G.q) : ℕ) : ℚ) = (i : ℚ) + i - ((G.p : ℚ) + G.q) := by
      rw [Nat.cast_sub hle, hi]; push_cast; ring
    refine ⟨(j - i + (G.p + G.q : ℕ)).toNat, (j + i - (G.p + G.q : ℕ)).toNat, by omega, by omega, ?_, ?_⟩
    · rw [show (((j - i + (G.p + G.q : ℕ)).toNat : ℕ) : ℚ) = ((j - i + (G.p + G.q : ℕ) : ℤ) : ℚ) from by
        exact_mod_cast Int.toNat_of_nonneg (by omega)]
      simp only [c, cPair, hj, hR]; push_cast; ring
    · rw [show (((j + i - (G.p + G.q : ℕ)).toNat : ℕ) : ℚ) = ((j + i - (G.p + G.q : ℕ) : ℤ) : ℚ) from by
        exact_mod_cast Int.toNat_of_nonneg (by omega)]
      simp only [c, cPair, hj, hR]; push_cast; ring
  choose k k' hk hk' ek ek' using hnum
  have hdeg := GlobalTheory.T.low_degree_le_fixed_degree hKP F E σ B a a' G X om om' Rm Rf hM
  refine (GlobalTheory.T.low_part_le_fixed_part_image hKP F E σ B a a' G X om om' Rm Rf hM).trans ?_
  rw [key, ← Submodule.map_comp, Submodule.map_le_iff_le_comap]
  refine (chi_le_tensSpan c hPR hQS k k' hk hk' ek ek' _ fun m' hm' => bot m' (hm'.trans_le hdeg)).trans ?_
  rw [tensSpan, Submodule.span_le]
  rintro _ ⟨g, hg', rfl⟩
  have hwt := GlobalTheory.T.low_irreducible_eigenspace_sup _ _ _ _ (c w) (k w) (k' w) (ek w) (ek' w) r s (hg' w)
  let ℓ := (Rm.p ∘ₗ Φ) ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap g w
  have hℓ : ∀ Z f, fockOp (Rm.p ∘ₗ Φ) w Z (ℓ f) = ℓ (fockAct2 _ _ _ _ Z f) := fun Z f => by
    simp only [ℓ, LinearMap.comp_apply _ ((PiTensorProduct.tprod ℂ).toLinearMap g w), MultilinearMap.toLinearMap_apply]
    rw [fockOp_apply (surj_q hM hD) (keeps_q hKP hM hD w), GlobalTheory.TensIrr.atPl_tprod]
    simp
  have e : (Rm.p ∘ₗ Φ) (PiTensorProduct.tprod ℂ g) = ℓ (g w) := by simp [ℓ]
  rw [SetLike.mem_coe, Submodule.mem_comap, e]
  have h2 := Submodule.mem_map_of_mem (f := ℓ) hwt
  rw [Submodule.map_iSup] at h2
  refine SetLike.le_def.1 (iSup_mono fun n => ?_) h2
  rintro _ ⟨f, ⟨h1, h2⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at h1 ⊢
    rw [hℓ, h1, map_smul]
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at h2 ⊢
    rw [hℓ, h2, map_smul]

end Weights

theorem eab_lie {R S : ℕ} {a b : Ix R S} (h : b ≠ a) : Eab a a * Eab b a - Eab b a * Eab a a = -Eab b a := by
  simp [Eab, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ h.symm]

theorem isKC_Eab {R S : ℕ} {a b : Ix R S} (h : sameBlock a b) : IsKC (Eab a b) := fun a' b' h' => by
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h' h

theorem bridge_beta : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ (Rn Sn : ℕ) (r₀ : Fin Rn) (s₀ : Fin Sn) (act : InfinitePlace F → Formalism.BasicNotions.TH.Mat Rn Sn →ₗ[ℂ] Module.End ℂ R.Pi)
        (c c' : InfinitePlace F → ℂ),
        (∀ w X Y, Formalism.BasicNotions.TH.IsKC X → Formalism.BasicNotions.TH.IsKC Y → act w (X * Y - Y * X) = act w X * act w Y - act w Y * act w X) ∧
        (∀ w w', w ≠ w' → ∀ X Y, Formalism.BasicNotions.TH.IsKC X → Formalism.BasicNotions.TH.IsKC Y → act w X * act w' Y = act w' Y * act w X) ∧
        (∀ w X, Formalism.BasicNotions.TH.IsKC X → ∀ v ∈ lowPartInf B G.M R.p, act w X v ∈ lowPartInf B G.M R.p) ∧
        (∀ N : Submodule ℂ R.Pi, N ≤ lowPartInf B G.M R.p → (∀ w X, Formalism.BasicNotions.TH.IsKC X → ∀ v ∈ N, act w X v ∈ N) →
          N = ⊥ ∨ N = lowPartInf B G.M R.p) ∧
        (∀ v, v ∈ twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p) ↔ v ∈ lowPartInf B G.M R.p ∧
          ∀ w, act w (Formalism.BasicNotions.TH.Eab (.inl r₀) (.inl r₀)) v = c w • v ∧ act w (Formalism.BasicNotions.TH.Eab (.inr s₀) (.inr s₀)) v = c' w • v) ∧
        (∀ v ∈ twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p), ∀ w, (∀ i, i ≠ r₀ → act w (Formalism.BasicNotions.TH.Eab (.inl r₀) (.inl i)) v = 0) ∧
          ∀ j, j ≠ s₀ → act w (Formalism.BasicNotions.TH.Eab (.inr s₀) (.inr j)) v = 0) ∧
        ∀ N : Submodule ℂ R.Pi, N ≤ lowPartInf B G.M R.p → KStabL B G.M om R.p G₁.W H' N →
          ∀ w X, Formalism.BasicNotions.TH.IsKC X → (∀ a, X a (.inl r₀) = 0 ∧ X (.inl r₀) a = 0 ∧ X a (.inr s₀) = 0 ∧ X (.inr s₀) a = 0) →
            ∀ v ∈ N, act w X v ∈ N := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hCfg X om om' Rm Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hb := hM.triple.base
  have hg := hM.triple.geo
  have hg₁ := hM₁.triple.geo
  obtain ⟨r₀, s₀, C, hC, hCθ, hAd⟩ := GlobalTheory.T.adapted_real_frame_exists F E σ B _ _ _ _ _ _ _ _ G.W G₁.W H' hb hg.hW hg₁.hW hCfg.hH'
    (by have := hCfg.ep; have := hCfg.eq; have := hg.aBig; omega) (by have := hCfg.ep; have := hCfg.eq; omega)
  choose A hA hAθ using fun w => Main.i_frameex _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [Main.incM_map_piInf, one_smul]; exact hA w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC⟩
  obtain ⟨Φ, hΦ⟩ := Main.i_fockex Main.i_derex F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hD : IsFockData B G.M A C Φ := ⟨⟨fr, hAθ, hCθ⟩, hΦ⟩
  have hq := surj_q hM hD
  have hK := keeps_q hKP hM hD
  set q := Rm.p ∘ₗ Φ with hqdef
  set x₂ : ℂ := (((a - G.p : ℕ) : ℂ) - G.p) / 2 with hx₂
  have hact : ∀ w Z, twAct false q w Z = fockOp q w (negT _ _ Z) := fun _ _ => rfl
  have htw : ∀ v, v ∈ twPart B G.M om Rm.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M Rm.p) ↔ v ∈ lowPartInf B G.M Rm.p ∧
      ∀ w, fockOp q w (Eab (.inl r₀) (.inl r₀)) v = x₂ • v ∧ fockOp q w (Eab (.inr s₀) (.inr s₀)) v = (-x₂) • v := by
    have hs : {x | x ∈ lowPartInf B G.M Rm.p ∧ IsTwEig B G.M om Rm.p G₁.W H' X.β ((a : ℝ) / 2) x} =
        ((lowPartInf B G.M Rm.p ⊓ ⨅ w, LinearMap.ker (fockOp q w (cen r₀ s₀)) : Submodule ℂ Rm.Pi) : Set Rm.Pi) := by
      ext x
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
      rw [isTwEig_iff hb hg.hW hg₁.hW hCfg.hH' hC hCθ hAd (actsBy_second hKP hM.triple hD) (admissible_weil_action hM.triple)
        (range_eq hM.triple hD) hq hK hM.triple.chars.expβ]
      simp only [mul_div_cancel₀ _ (two_ne_zero (α := ℂ)), sub_self, zero_smul]
      rfl
    intro v
    rw [twPart, hs, Submodule.span_eq]
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, cen, map_add, LinearMap.add_apply]
    refine and_congr_right fun hv => forall_congr' fun w => ⟨fun h => ?_, fun h => ?_⟩
    · exact bottom_of_sum _ _ x₂ (low_weights hKP hM hD w r₀ s₀ hv) h
    · rw [h.1, h.2, neg_smul, add_neg_cancel]
  have hlow : ∀ w (i j : Ix _ _) (μ : ℂ) (v : Rm.Pi), j ≠ i → fockOp q w (Eab i i) v = μ • v →
      fockOp q w (Eab i i) (fockOp q w (Eab j i) v) = (μ - 1) • fockOp q w (Eab j i) v := by
    intro w i j μ v hji hv
    have := LinearMap.congr_fun (fockOp_lie hq (hK w) (Eab i i) (Eab j i)) v
    rw [eab_lie hji, map_neg, LinearMap.neg_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hv,
      map_smul, eq_sub_iff_add_eq] at this
    rw [← this, sub_smul, one_smul]; abel
  refine ⟨_, _, r₀, s₀, twAct false q, fun _ => -x₂, fun _ => x₂, fun w Y Z _ _ => twAct_lie hq (hK w) _ Y Z,
    fun w w' hw Y Z _ _ => twAct_comm hq hK _ hw Y Z, fun w Z hZ v hv => low_stab hKP hM hD w _ (isKC_negT hZ) hv,
    fun N hle hN => low_irr hKP hM hD N hle fun w Z hZ v hv => ?_, fun v => ?_, fun v hv w => ⟨fun i hi => ?_, fun j hj => ?_⟩,
    fun N _ hN w Z hZ h0 v hv => kone_stab hKP hM hD hg₁.hW hCfg.hH' hAd N hN w _ (isKC_negT hZ) (fun c => ?_) hv⟩
  · have := hN w _ (isKC_negT hZ) v hv
    rwa [hact, negT_negT] at this
  · rw [htw]
    refine and_congr_right fun _ => forall_congr' fun w => ?_
    rw [hact, hact, negT_Eab, negT_Eab, map_neg, map_neg, LinearMap.neg_apply, LinearMap.neg_apply, neg_smul, neg_inj,
      neg_eq_iff_eq_neg]
  · obtain ⟨hv1, hv2⟩ := (htw v).1 hv
    rw [hact, negT_Eab, map_neg, LinearMap.neg_apply, neg_eq_zero]
    exact eq_zero_of_below _ x₂ Prod.fst _ (fun _ => inf_le_left)
      (low_weights hKP hM hD w r₀ s₀ (low_stab hKP hM hD w _ (isKC_Eab (by trivial)) hv1))
      (hlow w _ _ _ v (by simpa using hi) (hv2 w).1)
  · obtain ⟨hv1, hv2⟩ := (htw v).1 hv
    rw [hact, negT_Eab, map_neg, LinearMap.neg_apply, neg_eq_zero]
    exact eq_zero_of_below _ (-x₂) Prod.snd _ (fun _ => inf_le_right)
      (low_weights hKP hM hD w r₀ s₀ (low_stab hKP hM hD w _ (isKC_Eab (by trivial)) hv1))
      (hlow w _ _ _ v (by simpa using hj) (hv2 w).2)
  · simp [negT_apply, h0 c]

end GlobalTheory.FockBottom

end
