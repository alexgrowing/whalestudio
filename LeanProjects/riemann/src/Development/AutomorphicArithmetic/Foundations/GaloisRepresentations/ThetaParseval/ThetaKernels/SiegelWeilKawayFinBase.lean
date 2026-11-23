import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.FinBase
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlumb

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem cw_eInf_k (w : InfinitePlace F) {p q : Type} (Z : Matrix p q (AE F E)) : d.cw w (eInf F • Z) = d.cw w Z := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.smul_apply, St.piInf_smul, eInf_fst_apply, map_one, one_mul]
theorem cw_finOne_k (w : InfinitePlace F) {p q : Type} (Z : Matrix p q (AE F E)) : d.cw w (finOne F • Z) = 0 := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.smul_apply, Place.piInf_finOne, Matrix.zero_apply]
theorem cw_zero_iff_k {p q : Type} (Z : Matrix p q (AE F E)) : (∀ w, d.cw w Z = 0) ↔ eInf F • Z = 0 := by
  constructor
  · intro h
    refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w => ?_) ?_
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, h w]
      ext i j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
    · rw [smul_smul, finOne_mul_eInf, zero_smul, smul_zero]
  · intro h w
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k d w Z, h]
    ext i j
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
theorem cw_one_iff_k {p : Type} [DecidableEq p] (M : Matrix p p (AE F E)) :
    (∀ w, d.cw w M = 1) ↔ eInf F • M = eInf F • (1 : Matrix p p (AE F E)) := by
  have h1 : ∀ w, d.cw w (1 : Matrix p p (AE F E)) = 1 := fun w => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  constructor
  · intro h
    refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w => ?_) ?_
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, h w, h1 w]
    · rw [smul_smul, smul_smul, finOne_mul_eInf, zero_smul, zero_smul]
  · intro h w
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k d w M, h, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, h1 w]
def InvFin_k (f : Mx F E d.m d.n → ℂ) : Prop := ∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X
def InvInf_k (G : Mx F E d.m d.n → ℂ) : Prop := ∀ X Z, finOne F • Z = 0 → G (X + Z) = G X
def fcrd_k (X : Mx F E d.m d.n) : Fin d.m × Fin d.n × Fin 2 → Af F := fun k => (d.crd X k).2
theorem gram_add_left_k (X X' Z : Mx F E d.m d.n) : d.gram (X + X') Z = d.gram X Z + d.gram X' Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_add, Matrix.add_mul]
theorem gram_add_right_k (X Z Z' : Mx F E d.m d.n) : d.gram X (Z + Z') = d.gram X Z + d.gram X Z' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
  rw [Matrix.map_add _ (map_add _), Matrix.mul_add]
theorem gram_smul_left_k (c : AF F) (X Z : Mx F E d.m d.n) : d.gram (c • X) Z = c • d.gram X Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul]
theorem gram_smul_right_k (c : AF F) (X Z : Mx F E d.m d.n) : d.gram X (c • Z) = c • d.gram X Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
  have : (c • Z).map (cA σ) = c • Z.map (cA σ) := by
    ext i j
    simp [map_smul]
  rw [this, Matrix.mul_smul]
theorem gram_fin_inf_k {X Z : Mx F E d.m d.n} (hX : eInf F • X = 0) (hZ : finOne F • Z = 0) : d.gram X Z = 0 := by
  have eX : X = finOne F • X := by
    conv_lhs => rw [← smul_split X, hX, zero_add]
  rw [eX, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_right_k, hZ]
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
theorem gram_inf_fin_k {X Z : Mx F E d.m d.n} (hX : finOne F • X = 0) (hZ : eInf F • Z = 0) : d.gram X Z = 0 := by
  have eZ : Z = finOne F • Z := by
    conv_lhs => rw [← smul_split Z, hZ, zero_add]
  rw [eZ, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_right_k, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, hX]
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
theorem tt_add_k (M M' : Mx F E d.n d.n) : d.tt (M + M') = d.tt M + d.tt M' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_add, map_add]
theorem crd_add_k (X Z : Mx F E d.m d.n) (k) : d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.add_apply, map_add, Finsupp.add_apply]
theorem crd_smul_k (c : AF F) (X : Mx F E d.m d.n) (k) : d.crd (c • X) k = c * d.crd X k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
theorem cmb_crd_k (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  conv_rhs => rw [← (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
theorem cmb_smul_k (c : AF F) (x : Fin d.m × Fin d.n × Fin 2 → AF F) : d.cmb (fun k => c * x k) = c • d.cmb x := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Matrix.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul]
theorem fcrd_invInf_k (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d (fun X => g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X)) := by
  intro X Z hZ
  show g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d (X + Z)) = g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X)
  congr 1
  funext k
  show (d.crd (X + Z) k).2 = (d.crd X k).2
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.crd_add_k]
  change (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
  have : (d.crd Z k).2 = 0 := by
    rw [← finOne_snd_mul (d.crd Z k), ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.crd_smul_k, hZ]
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  rw [this, add_zero]
theorem invInf_fcrd_k {G : Mx F E d.m d.n → ℂ} (hG : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G) (X : Mx F E d.m d.n) :
    G X = G (d.cmb fun k => pairA F 0 (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X k)) := by
  set Y := d.cmb fun k => pairA F 0 (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X k) with hY
  have hp : ∀ c : AF F, finOne F * c = pairA F 0 c.2 := fun c =>
    Prod.ext (finOne_fst_mul c) (finOne_snd_mul c)
  have e1 : finOne F • X = Y := by
    conv_lhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cmb_crd_k d X]
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cmb_smul_k]
    simp only [hp, hY, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k]
  have e2 : finOne F • Y = Y := by
    rw [hY, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cmb_smul_k]
    congr 1
    funext k
    rw [hp]
    rfl
  have h := hG Y (X - Y) (by rw [smul_sub, e1, e2, sub_self])
  rw [add_sub_cancel] at h
  exact h
def StepF_k (x : d.G) (A B : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ) : Prop :=
  (∀ f, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f → _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d (A f)) ∧ ∀ G, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G → _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d (B G) ∧
    ∀ f, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f → ∀ Φ ∈ d.sch, d.T Φ = (fun X => f X * G X) → d.T (d.om x Φ) = fun X => A f X * B G X
theorem step_comp_k {x x' : d.G} {A A' B B' : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ}
    (h : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x A B) (h' : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x' A' B') : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d (x * x') (A ∘ A') (B ∘ B') := by
  refine ⟨fun f hf => h.1 _ (h'.1 f hf), fun G hG => ⟨(h.2 _ (h'.2 G hG).1).1, fun f hf Φ hΦ hT => ?_⟩⟩
  have e1 := (h'.2 G hG).2 f hf Φ hΦ hT
  have e2 := (h.2 (B' G) (h'.2 G hG).1).2 (A' f) (h'.1 f hf) (d.om x' Φ) (d.om_sch x' Φ hΦ) e1
  rw [map_mul, Module.End.mul_apply]
  exact e2
theorem key_split_k {f G A' B' : Mx F E d.m d.n → ℂ} (hf : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f) (hA : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d A') (hG : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G)
    (hB : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d B') (h : ∀ X, f X * G X = A' X * B' X) : ∀ X Y, f X * G Y = A' X * B' Y := by
  intro X Y
  have hW1 : eInf F • X + finOne F • Y = X + finOne F • (Y - X) := by
    calc eInf F • X + finOne F • Y = (eInf F • X + finOne F • X) + finOne F • (Y - X) := by rw [smul_sub]; abel
      _ = X + finOne F • (Y - X) := by rw [smul_split]
  have hW2 : eInf F • X + finOne F • Y = Y + eInf F • (X - Y) := by
    calc eInf F • X + finOne F • Y = (eInf F • Y + finOne F • Y) + eInf F • (X - Y) := by rw [smul_sub]; abel
      _ = Y + eInf F • (X - Y) := by rw [smul_split]
  have hfin : ∀ w, d.cw w (finOne F • (Y - X)) = 0 := fun w => _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_finOne_k d w _
  have hinf : finOne F • (eInf F • (X - Y)) = 0 := by rw [smul_smul, finOne_mul_eInf, zero_smul]
  have e := h (eInf F • X + finOne F • Y)
  rw [hW1, hf X _ hfin, hA X _ hfin, ← hW1, hW2, hG Y _ hinf, hB Y _ hinf] at e
  exact e
theorem step_conj_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {x₁ x₂ x' : d.G} {A₁ A₂ B₁ B₂ B' : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ}
    (h₁ : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x₁ A₁ B₁) (h₂ : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x₂ A₂ B₂) (h' : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x' id B') (h1 : x₁ * x₂ = 1) :
    ∃ B, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d (x₁ * x' * x₂) id B := by
  have hc := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d h₁ h') h₂
  have h0 := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d h₁ h₂
  refine ⟨fun G => if h : ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 then
      (G h.choose / B₁ (B₂ G) h.choose) • B₁ (B' (B₂ G)) else 0,
    fun f hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · dsimp only
    split_ifs with h
    · intro X Z hZ
      simp only [Pi.smul_apply, smul_eq_mul]
      have e := (hc.2 G hG).1 X Z hZ
      simp only [Function.comp_apply] at e
      rw [e]
    · intro X Z _
      rfl
  · have e := (hc.2 G hG).2 f hf Φ hΦ hTΦ
    have e0 := (h0.2 G hG).2 f hf Φ hΦ hTΦ
    rw [h1, map_one, Module.End.one_apply, hTΦ] at e0
    have key := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.key_split_k d hf (h0.1 f hf) hG (h0.2 G hG).1 (fun X => congrFun e0 X)
    by_cases hz : (∀ X, f X = 0) ∨ ∀ X, G X = 0
    · have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by
        rw [hTΦ]
        funext X
        rcases hz with hz | hz <;> simp [hz])
      subst hΦ0
      rw [map_zero, d.T_zero]
      funext X
      rcases hz with hz | hz
      · simp [hz]
      · have hn : ¬ ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 := fun ⟨X₀, h, _⟩ => h (hz X₀)
        simp [dif_neg hn]
    · push Not at hz
      obtain ⟨⟨u₀, hu₀⟩, ⟨X₁, hX₁⟩⟩ := hz
      have hex : ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 := by
        refine ⟨X₁, hX₁, fun h0' => ?_⟩
        have := key u₀ X₁
        simp only [Function.comp_apply] at this
        rw [h0', mul_zero] at this
        exact mul_ne_zero hu₀ hX₁ this
      have hB0 := hex.choose_spec.2
      have hA : ∀ u, A₁ (A₂ f) u = f u * (G hex.choose / B₁ (B₂ G) hex.choose) := by
        intro u
        have := key u hex.choose
        simp only [Function.comp_apply] at this
        rw [mul_div_assoc', eq_div_iff hB0]
        linear_combination -this
      rw [e]
      funext X
      simp only [Function.comp_apply, id_eq, dif_pos hex, Pi.smul_apply, smul_eq_mul, hA]
      ring
end SDf
end PositivityTheory.SiegelWeilFormula.KAway
end
end
