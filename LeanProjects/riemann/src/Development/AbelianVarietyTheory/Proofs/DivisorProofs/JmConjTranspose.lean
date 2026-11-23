import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPolynomialTensorWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.RealLift Formalism.BasicNotions.TH GlobalTheory.FockBridge

namespace GlobalTheory.FockBottom

section Alg

variable {V Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]

theorem isExp_mem {L U : Module.End ℂ V} (hU : IsExp L U) (N : Submodule ℂ V) (hN : ∀ v ∈ N, L v ∈ N) {T : V}
    (hT : T ∈ N) : U T ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l'
  have hp : ∀ n : ℕ, (L ^ n) T ∈ N := fun n => by
    induction n with
    | zero => simpa using hT
    | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hN _ ih
  have h := hU T (l' ∘ₗ N.mkQ)
  have e : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * (l' ∘ₗ N.mkQ) ((L ^ n) T)) = fun _ => 0 := by
    funext n
    simp [(Submodule.Quotient.mk_eq_zero N).2 (hp n)]
  rw [e] at h
  exact h.unique hasSum_zero

theorem isExp_eig {L U : Module.End ℂ V} (hU : IsExp L U) (q : V →ₗ[ℂ] Z) (L0 : Module.End ℂ Z)
    (h : ∀ v, q (L v) = L0 (q v)) {T : V} {μ : ℂ} (hT : L0 (q T) = μ • q T) : q (U T) = Complex.exp μ • q T := by
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_)
  rw [map_sub, sub_eq_zero, map_smul, smul_eq_mul]
  have hp : ∀ n : ℕ, q ((L ^ n) T) = μ ^ n • q T := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Module.End.mul_apply, h, ih, map_smul, hT, smul_smul, pow_succ]
  have a := hU T (l ∘ₗ q)
  simp only [LinearMap.comp_apply, hp, map_smul, smul_eq_mul] at a
  have b := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ).mul_right (l (q T))
  rw [← Complex.exp_eq_exp_ℂ] at b
  simp only [smul_eq_mul, mul_assoc] at b
  exact a.unique b

theorem exp_mul_eq {a b : ℂ} (h : ∀ s : ℝ, Complex.exp (s * a) = Complex.exp (s * b)) : a = b := by
  have d : ∀ z : ℂ, HasDerivAt (fun s : ℝ => Complex.exp (s * z)) z 0 := fun z => by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const z
    simpa using h1.cexp
  have e : (fun s : ℝ => Complex.exp (s * a)) = fun s : ℝ => Complex.exp (s * b) := funext h
  exact (d a).unique (e ▸ d b)

theorem bottom_of_sum (D₁ D₂ : Module.End ℂ V) (a : ℂ) {v : V}
    (hv : v ∈ ⨆ n : ℕ × ℕ, D₁.eigenspace (a + n.1) ⊓ D₂.eigenspace (-a + n.2)) (h0 : D₁ v + D₂ v = 0) :
    D₁ v = a • v ∧ D₂ v = (-a) • v := by
  have hle : (⨆ n : ℕ × ℕ, D₁.eigenspace (a + n.1) ⊓ D₂.eigenspace (-a + n.2)) ≤
      (D₁.eigenspace a ⊓ D₂.eigenspace (-a)) ⊔ ⨆ μ ≠ (0 : ℂ), (D₁ + D₂).eigenspace μ := by
    refine iSup_le fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · refine le_sup_of_le_right (le_iSup₂_of_le ((n.1 + n.2 : ℕ) : ℂ) ?_ ?_)
      · rw [Nat.cast_ne_zero]
        intro h; apply hn; ext <;> simp <;> omega
      · intro x hx
        have h1 := Module.End.mem_eigenspace_iff.1 hx.1
        have h2 := Module.End.mem_eigenspace_iff.1 hx.2
        rw [Module.End.mem_eigenspace_iff, LinearMap.add_apply, h1, h2, ← add_smul]
        congr 1; push_cast; ring
  obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1 (hle hv)
  have h1 := Module.End.mem_eigenspace_iff.1 hy.1
  have h2 := Module.End.mem_eigenspace_iff.1 hy.2
  have hz0 : z ∈ (D₁ + D₂).eigenspace 0 := by
    rw [Module.End.mem_eigenspace_iff, zero_smul, show z = v - y by rw [← e]; abel, map_sub, LinearMap.add_apply, h0,
      LinearMap.add_apply, h1, h2]
    simp
  have := (Submodule.disjoint_def.1 ((Module.End.eigenspaces_iSupIndep (D₁ + D₂)) 0)) z hz0 hz
  rw [this, add_zero] at e
  exact e ▸ ⟨h1, h2⟩

theorem eq_zero_of_below (D : Module.End ℂ V) (a : ℂ) {ι : Type} (f : ι → ℕ) (N : ι → Submodule ℂ V)
    (hN : ∀ i, N i ≤ D.eigenspace (a + f i)) {v : V} (hv : v ∈ ⨆ i, N i) (h : D v = (a - 1) • v) : v = 0 := by
  have hle : (⨆ i, N i) ≤ ⨆ μ ≠ (a - 1), D.eigenspace μ := by
    refine iSup_le fun i => le_iSup₂_of_le (a + f i) ?_ (hN i)
    intro e
    have : ((f i + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination e
    exact Nat.succ_ne_zero _ (Nat.cast_eq_zero.1 this)
  exact (Submodule.disjoint_def.1 ((Module.End.eigenspaces_iSupIndep D) (a - 1))) v
    (Module.End.mem_eigenspace_iff.2 h) (hle hv)

end Alg

section Mat

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_col {n : Type} [Fintype n] [DecidableEq n] (Y : Matrix n n ℂ) (c : n) (μ : ℂ)
    (h : ∀ a, Y a c = if a = c then μ else 0) (a : n) :
    NormedSpace.exp Y a c = if a = c then Complex.exp μ else 0 := by
  have hp : ∀ (k : ℕ) a, (Y ^ k) a c = if a = c then μ ^ k else 0 := fun k => by
    induction k with
    | zero => intro a; simp [Matrix.one_apply]
    | succ k ih =>
      intro a
      rw [pow_succ', Matrix.mul_apply]
      simp only [ih, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, h]
      split_ifs <;> simp [pow_succ']
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y).mapL
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a c))
  have e : ∀ M : Matrix n n ℂ, LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a c) M = M a c := fun _ => rfl
  simp only [e, Matrix.smul_apply, hp] at h1
  split_ifs at h1 ⊢
  · rw [Complex.exp_eq_exp_ℂ]
    exact h1.unique (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ)
  · simp only [smul_zero] at h1
    exact h1.unique hasSum_zero

theorem mul_exp_col {m n : Type} [Fintype n] [DecidableEq n] (C : Matrix m n ℂ) (Y : Matrix n n ℂ) (c : n) (μ : ℂ)
    (h : ∀ a, Y a c = if a = c then μ else 0) (i : m) :
    (C * NormedSpace.exp Y) i c = Complex.exp μ * C i c := by
  rw [Matrix.mul_apply]
  simp [exp_col Y c μ h, mul_comm]

end Mat

theorem jm_conjTranspose (R S : ℕ) : (Formalism.BasicNotions.TH.Jm R S)ᴴ = Formalism.BasicNotions.TH.Jm R S := by
  simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem upq_decomp {R S : ℕ} (Z : Mat R S) : ∃ Y₁ ∈ upq R S, ∃ Y₂ ∈ upq R S, Z = Y₁ + Complex.I • Y₂ := by
  set J := Formalism.BasicNotions.TH.Jm R S
  have hJ : J * J = 1 := GlobalTheory.FockKStab.jm_mul_jm R S
  have hJ' : Jᴴ = J := jm_conjTranspose R S
  have h1 : ∀ M : Mat R S, J * (J * M) = M := fun M => by rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Z - J * Zᴴ * J), ?_, (1 / (2 * Complex.I)) • (Z + J * Zᴴ * J), ?_, ?_⟩
  · show _ * J + J * _ = 0
    rw [Matrix.conjTranspose_smul, show star (1 / 2 : ℂ) = 1 / 2 by simp, Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ', Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_assoc, hJ, h1, Matrix.mul_one]
    simp
  · show _ * J + J * _ = 0
    rw [Matrix.conjTranspose_smul, show star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by simp, neg_smul,
      Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, neg_add_eq_zero]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ', Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_assoc, hJ, h1, Matrix.mul_one]
    rw [add_comm]
  · rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [show Z - J * Zᴴ * J + (Z + J * Zᴴ * J) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]; norm_num

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d}

def genOp (P Q : ℕ) (c : InfinitePlace F → ℂ) (Yg : InfinitePlace F → Mat R S) : Module.End ℂ (Tens F P Q R S) :=
  sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) fun w => fockAct2 P Q R S (Yg w) + (c w * (Yg w).trace) • 1

theorem genOp_apply (c : InfinitePlace F → ℂ) (Yg : InfinitePlace F → Mat R S) (T : Tens F P Q R S) :
    genOp P Q c Yg T = ∑ w, (atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S (Yg w)) T +
      (c w * (Yg w).trace) • T) := by
  simp [genOp, sumPl, LinearMap.sum_apply, Main.atPl_add, Main.atPl_smul, Main.atPl_one]

theorem genOp_single (c : InfinitePlace F → ℂ) (w : InfinitePlace F) (Z : Mat R S) (T : Tens F P Q R S) :
    genOp P Q c (Pi.single w Z) T = atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Z) T +
      (c w * Z.trace) • T := by
  rw [genOp_apply, Finset.sum_eq_single w]
  · simp
  · intro w' _ h
    simp [Pi.single_eq_of_ne h, Main.atPl_zero]
  · simp

theorem genOp_smul (c : InfinitePlace F → ℂ) (Yg : InfinitePlace F → Mat R S) (s : ℂ) :
    genOp P Q c (s • Yg) = s • genOp P Q c Yg := by
  refine LinearMap.ext fun T => ?_
  rw [LinearMap.smul_apply, genOp_apply, genOp_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.smul_apply, map_smul, Main.atPl_smul, LinearMap.smul_apply, Matrix.trace_smul, smul_add, smul_smul,
    smul_eq_mul]
  congr 2; ring

theorem genOp_locFin (c : InfinitePlace F → ℂ) {Yg : InfinitePlace F → Mat R S} (h : ∀ w, IsKC (Yg w)) :
    LocFin (genOp P Q c Yg) :=
  Main.i_locfin _ _ _ fun w => Main.locFin_fock2 P Q R S (Yg w) (h w) _

variable {B : Base F E} {om : Rep σ Y W} {C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ}
  {Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)} {c : InfinitePlace F → ℂ}

theorem acts_unique {T : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ} {f f₁ f₂ : SInf F (Fin n × Fin d)}
    (h₁ : Acts (evI F) T f f₁) (h₂ : Acts (evI F) T f f₂) : f₁ = f₂ :=
  (Main.i_actslaws F _ f f₁ f₂).2.2.2.1 T h₁ h₂

theorem exp_of_gen (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    {γ : Multiplicative ℝ →* UG (cA σ) (incM F W.J)} (hγ : γ ∈ RLines σ (incM F W.J)) {Yg : InfinitePlace F → Mat R S}
    (hY : IsGen B.emb C γ Yg) (hKC : ∀ w, IsKC (Yg w)) :
    ∃ U : Module.End ℂ (Tens F P Q R S), IsExp (genOp P Q c Yg) U ∧
      ∀ T, Acts (evI F) (om (1, γ (Multiplicative.ofAdd 1))) (Φ T) (Φ (U T)) := by
  obtain ⟨U, hU, hSA⟩ := Main.i_expact F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ)
    (genOp_locFin c hKC) (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hY T)
  exact ⟨U, hU, fun T => (Main.i_actslaws F _ (Φ T) (Φ (U T)) (Φ T)).2.1 _ (map_zero _) (hSA T)⟩

theorem exp_of_kInf (hcm : IsCMExt F E σ) (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    (hθ : ∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb) :
    ∃ (Yg : InfinitePlace F → Mat R S) (U : Module.End ℂ (Tens F P Q R S)), (∀ w, IsKC (Yg w)) ∧
      IsExp (genOp P Q c Yg) U ∧ ∀ T, Acts (evI F) (om (1, k)) (Φ T) (Φ (U T)) := by
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ :=
    Main.i_kline Main.i_lineex F E σ (Fin d) R S B.emb (incM F W.J) Complex.I C W.θ hcm hC hθ k hk.1 hk.2
  obtain ⟨U, hU, hA⟩ := exp_of_gen hact hadm hγ hgen hKC
  exact ⟨Yg, U, hKC, hU, hγ1 ▸ hA⟩

theorem exp_of_skew (hcm : IsCMExt F E σ) (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    (hθ : ∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    (Yg : InfinitePlace F → Mat R S) (hKC : ∀ w, IsKC (Yg w)) (hs : ∀ w, (Yg w)ᴴ = -Yg w) :
    ∃ k ∈ KInf σ W B.emb, (∀ w, (mat k).map (piInf (B.emb w)) * C w = C w * NormedSpace.exp (Yg w)) ∧
      ∃ U : Module.End ℂ (Tens F P Q R S), IsExp (genOp P Q c Yg) U ∧ ∀ T, Acts (evI F) (om (1, k)) (Φ T) (Φ (U T)) := by
  obtain ⟨γ, hγ, hgen⟩ := Main.i_lineex F E σ (Fin d) R S B.emb (incM F W.J) Complex.I C hcm hC Yg
    fun w => GlobalTheory.FockKStab.mem_upq (hKC w) (hs w)
  have h1 : ∀ w, (mat (γ (Multiplicative.ofAdd 1))).map (piInf (B.emb w)) * C w = C w * NormedSpace.exp (Yg w) := fun w => by
    have := hgen 1 w
    rwa [one_smul] at this
  refine ⟨γ (Multiplicative.ofAdd 1), ⟨hγ.2 _, fun w => ?_⟩, h1, exp_of_gen hact hadm hγ hgen hKC⟩
  obtain ⟨A', hA'⟩ := (hC w).2
  exact GlobalTheory.FockKStab.commute_of_frame hA' (GlobalTheory.FockKStab.frame_inv (hC w) hA') (h1 w) (hθ w)
    (Commute.exp_left (GlobalTheory.FockKStab.commute_jm (hKC w)))

theorem eq_of_frame (hcm : IsCMExt F E σ) (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    {k k' : UA σ W.J} (hk : k ∈ UAt σ W (evI F)) (hk' : k' ∈ UAt σ W (evI F))
    (h : ∀ w, (mat k).map (piInf (B.emb w)) * C w = (mat k').map (piInf (B.emb w)) * C w) : k = k' := by
  apply Subtype.ext; apply Units.ext
  show mat k = mat k'
  ext i j
  rw [← sub_eq_zero]
  refine GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hcm B.emb _ (fun u hu => ?_) fun w => ?_
  · have a := congrFun (congrFun (hk u hu) i) j
    have b := congrFun (congrFun (hk' u hu) i) j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply] at a b
    rw [show mat k i j - mat k' i j = (mat k i j - (1 : Matrix (Fin d) (Fin d) (AE F E)) i j) -
      (mat k' i j - (1 : Matrix (Fin d) (Fin d) (AE F E)) i j) by ring, smul_sub, a, b, sub_zero]
  · obtain ⟨A', hA'⟩ := (hC w).2
    have e := congrArg (· * A') (h w)
    simp only [Matrix.mul_assoc, hA', Matrix.mul_one] at e
    have := congrFun (congrFun e i) j
    simp only [Matrix.map_apply] at this
    rw [map_sub, this, sub_self]

theorem stab_of_fix (hcm : IsCMExt F E σ) (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    (hθ : ∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    (I : Set (Ix R S)) (N : Submodule ℂ (Tens F P Q R S))
    (hN : ∀ k ∈ KInf σ W B.emb, (∀ w, ∀ b ∈ I, ∀ i, ((mat k).map (piInf (B.emb w)) * C w) i b = C w i b) →
      ∀ T ∈ N, ∀ T', Acts (evI F) (om (1, k)) (Φ T) (Φ T') → T' ∈ N)
    (w : InfinitePlace F) (Z : Mat R S) (hZ : IsKC Z) (hI : ∀ b ∈ I, ∀ a, Z a b = 0 ∧ Z b a = 0) {T : Tens F P Q R S}
    (hT : T ∈ N) : atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Z) T ∈ N := by
  have key : ∀ Y : Mat R S, IsKC Y → Yᴴ = -Y → (∀ b ∈ I, ∀ a, Y a b = 0) →
      atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Y) T ∈ N := by
    intro Y hY hs h0
    have hKC : ∀ (s : ℂ) w', IsKC ((s • (Pi.single w Y : InfinitePlace F → Mat R S)) w') := fun s w' => by
      refine GlobalTheory.FockKStab.isKC_smul ?_ s
      by_cases h : w' = w
      · subst h; simpa using hY
      · simpa [Pi.single_eq_of_ne h] using GlobalTheory.FockKStab.isKC_zero R S
    have hmem := GlobalTheory.FockKStab.mem_of_exp (genOp P Q c (Pi.single w Y)) (genOp_locFin c (by simpa using hKC 1)) N T
      fun s => by
        obtain ⟨k, hk, hkC, U, hU, hA⟩ := exp_of_skew hcm hC hθ hact hadm ((s : ℂ) • Pi.single w Y) (hKC s) fun w' => by
          by_cases h : w' = w
          · subst h; simp [Matrix.conjTranspose_smul, hs]
          · simp [Pi.single_eq_of_ne h]
        refine ⟨U, genOp_smul c _ (s : ℂ) ▸ hU, hN k hk (fun w' b hb i => ?_) T hT _ (hA T)⟩
        rw [hkC, mul_exp_col _ _ b 0, Complex.exp_zero, one_mul]
        intro a
        by_cases h : w' = w
        · subst h; simp [h0 b hb a]
        · simp [Pi.single_eq_of_ne h]
    rw [genOp_single] at hmem
    simpa using N.sub_mem hmem (N.smul_mem (c w * Y.trace) hT)
  have hZh : IsKC Zᴴ := GlobalTheory.FockKStab.isKC_conjTranspose hZ
  have hZ' : Z = (1 / 2 : ℂ) • (Z - Zᴴ) + Complex.I • (1 / (2 * Complex.I)) • (Z + Zᴴ) := by
    rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [show Z - Zᴴ + (Z + Zᴴ) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]; norm_num
  rw [hZ', map_add, map_smul _ Complex.I, Main.atPl_add, Main.atPl_smul, LinearMap.add_apply, LinearMap.smul_apply]
  refine N.add_mem (key _ ?_ ?_ ?_) (N.smul_mem _ (key _ ?_ ?_ ?_))
  · exact GlobalTheory.FockKStab.isKC_smul (fun a b h => by rw [Matrix.sub_apply, hZ a b h, hZh a b h, sub_zero]) _
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_neg, neg_sub]
  · intro b hb a; simp [Matrix.conjTranspose_apply, hI b hb a]
  · exact GlobalTheory.FockKStab.isKC_smul (GlobalTheory.FockKStab.isKC_add hZ hZh) _
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    rw [show star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by simp, neg_smul, add_comm]
  · intro b hb a; simp [Matrix.conjTranspose_apply, hI b hb a]

end Tens

end GlobalTheory.FockBottom
