import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdDecomp
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.FockLatticeInjective
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OppositeUnipotentWeylConj
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OmSch
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (F) in

def eInf : AF F := 1 - finOne F

theorem finOne_mul_eInf : finOne F * eInf F = 0 := by
  change ((0 : Ainf F) * (1 - 0), (1 : Af F) * (1 - 1)) = ((0 : Ainf F), (0 : Af F))
  simp

theorem eInf_mul_finOne : eInf F * finOne F = 0 := by
  change ((1 - 0 : Ainf F) * 0, (1 - 1 : Af F) * 1) = ((0 : Ainf F), (0 : Af F))
  simp

theorem eInf_mul_self : eInf F * eInf F = eInf F := by
  change ((1 - 0 : Ainf F) * (1 - 0), (1 - 1 : Af F) * (1 - 1)) = ((1 - 0 : Ainf F), (1 - 1 : Af F))
  simp

theorem eInf_fst_apply (w : InfinitePlace F) : (eInf F).1 w = 1 := by
  change ((1 : Ainf F) - 0) w = 1
  rw [sub_zero]
  rfl

theorem finOne_snd_mul (c : AF F) : (finOne F * c).2 = c.2 := by
  change (1 : Af F) * c.2 = c.2
  exact one_mul _

theorem finOne_fst_mul (c : AF F) : (finOne F * c).1 = 0 := by
  change (0 : Ainf F) * c.1 = 0
  exact zero_mul _

theorem eInf_fst_mul (c : AF F) : (eInf F * c).1 = c.1 := by
  change ((1 : Ainf F) - 0) * c.1 = c.1
  simp

theorem smul_split {p q : Type} (Z : Matrix p q (AE F E)) : eInf F • Z + finOne F • Z = Z := by
  rw [← add_smul, eInf, sub_add_cancel, one_smul]

namespace SDf

variable (d : SD σ)

theorem cw_eInf (w : InfinitePlace F) {p q : Type} (Z : Matrix p q (AE F E)) : d.cw w (eInf F • Z) = d.cw w Z := by
  ext i j
  simp only [SD.cw, Matrix.map_apply, Matrix.smul_apply, St.piInf_smul, eInf_fst_apply, map_one, one_mul]

theorem cw_finOne (w : InfinitePlace F) {p q : Type} (Z : Matrix p q (AE F E)) : d.cw w (finOne F • Z) = 0 := by
  ext i j
  simp only [SD.cw, Matrix.map_apply, Matrix.smul_apply, Place.piInf_finOne, Matrix.zero_apply]

theorem cw_zero_iff {p q : Type} (Z : Matrix p q (AE F E)) : (∀ w, d.cw w Z = 0) ↔ eInf F • Z = 0 := by
  constructor
  · intro h
    refine Place.cw_ext d (fun w => ?_) ?_
    · rw [cw_eInf, h w]
      ext i j
      simp [SD.cw]
    · rw [smul_smul, finOne_mul_eInf, zero_smul, smul_zero]
  · intro h w
    rw [← cw_eInf d w Z, h]
    ext i j
    simp [SD.cw]

theorem cw_one_iff {p : Type} [DecidableEq p] (M : Matrix p p (AE F E)) :
    (∀ w, d.cw w M = 1) ↔ eInf F • M = eInf F • (1 : Matrix p p (AE F E)) := by
  have h1 : ∀ w, d.cw w (1 : Matrix p p (AE F E)) = 1 := fun w => by
    simp only [SD.cw]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  constructor
  · intro h
    refine Place.cw_ext d (fun w => ?_) ?_
    · rw [cw_eInf, cw_eInf, h w, h1 w]
    · rw [smul_smul, smul_smul, finOne_mul_eInf, zero_smul, zero_smul]
  · intro h w
    rw [← cw_eInf d w M, h, cw_eInf, h1 w]

def InvFin (f : Mx F E d.m d.n → ℂ) : Prop := ∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X

def InvInf (G : Mx F E d.m d.n → ℂ) : Prop := ∀ X Z, finOne F • Z = 0 → G (X + Z) = G X

def fcrd (X : Mx F E d.m d.n) : Fin d.m × Fin d.n × Fin 2 → Af F := fun k => (d.crd X k).2

theorem gram_add_left (X X' Z : Mx F E d.m d.n) : d.gram (X + X') Z = d.gram X Z + d.gram X' Z := by
  simp only [SD.gram, Matrix.transpose_add, Matrix.add_mul]

theorem gram_add_right (X Z Z' : Mx F E d.m d.n) : d.gram X (Z + Z') = d.gram X Z + d.gram X Z' := by
  simp only [SD.gram]
  rw [Matrix.map_add _ (map_add _), Matrix.mul_add]

theorem gram_smul_left (c : AF F) (X Z : Mx F E d.m d.n) : d.gram (c • X) Z = c • d.gram X Z := by
  simp only [SD.gram, Matrix.transpose_smul, Matrix.smul_mul]

theorem gram_smul_right (c : AF F) (X Z : Mx F E d.m d.n) : d.gram X (c • Z) = c • d.gram X Z := by
  simp only [SD.gram]
  have : (c • Z).map (cA σ) = c • Z.map (cA σ) := by
    ext i j
    simp [map_smul]
  rw [this, Matrix.mul_smul]

theorem gram_fin_inf {X Z : Mx F E d.m d.n} (hX : eInf F • X = 0) (hZ : finOne F • Z = 0) : d.gram X Z = 0 := by
  have eX : X = finOne F • X := by
    conv_lhs => rw [← smul_split X, hX, zero_add]
  rw [eX, gram_smul_left, ← gram_smul_right, hZ]
  simp [SD.gram]

theorem gram_inf_fin {X Z : Mx F E d.m d.n} (hX : finOne F • X = 0) (hZ : eInf F • Z = 0) : d.gram X Z = 0 := by
  have eZ : Z = finOne F • Z := by
    conv_lhs => rw [← smul_split Z, hZ, zero_add]
  rw [eZ, gram_smul_right, ← gram_smul_left, hX]
  simp [SD.gram]

theorem tt_add (M M' : Mx F E d.n d.n) : d.tt (M + M') = d.tt M + d.tt M' := by
  simp only [SD.tt, Matrix.trace_add, map_add]

theorem crd_add (X Z : Mx F E d.m d.n) (k) : d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  simp only [SD.crd, Matrix.add_apply, map_add, Finsupp.add_apply]

theorem crd_smul (c : AF F) (X : Mx F E d.m d.n) (k) : d.crd (c • X) k = c * d.crd X k := by
  simp only [SD.crd, Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem cmb_crd (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
  ext i j
  simp only [SD.cmb, SD.crd]
  conv_rhs => rw [← (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem cmb_smul (c : AF F) (x : Fin d.m × Fin d.n × Fin 2 → AF F) : d.cmb (fun k => c * x k) = c • d.cmb x := by
  ext i j
  simp only [SD.cmb, Matrix.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul]

theorem fcrd_invInf (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) : InvInf d (fun X => g (fcrd d X)) := by
  intro X Z hZ
  show g (fcrd d (X + Z)) = g (fcrd d X)
  congr 1
  funext k
  show (d.crd (X + Z) k).2 = (d.crd X k).2
  rw [crd_add]
  change (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
  have : (d.crd Z k).2 = 0 := by
    rw [← finOne_snd_mul (d.crd Z k), ← crd_smul, hZ]
    simp [SD.crd]
  rw [this, add_zero]

theorem invInf_fcrd {G : Mx F E d.m d.n → ℂ} (hG : InvInf d G) (X : Mx F E d.m d.n) :
    G X = G (d.cmb fun k => pairA F 0 (fcrd d X k)) := by
  set Y := d.cmb fun k => pairA F 0 (fcrd d X k) with hY
  have hp : ∀ c : AF F, finOne F * c = pairA F 0 c.2 := fun c =>
    Prod.ext (finOne_fst_mul c) (finOne_snd_mul c)
  have e1 : finOne F • X = Y := by
    conv_lhs => rw [← cmb_crd d X]
    rw [← cmb_smul]
    simp only [hp, hY, fcrd]
  have e2 : finOne F • Y = Y := by
    rw [hY, ← cmb_smul]
    congr 1
    funext k
    rw [hp]
    rfl
  have h := hG Y (X - Y) (by rw [smul_sub, e1, e2, sub_self])
  rw [add_sub_cancel] at h
  exact h

def StepF (x : d.G) (A B : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ) : Prop :=
  (∀ f, InvFin d f → InvFin d (A f)) ∧ ∀ G, InvInf d G → InvInf d (B G) ∧
    ∀ f, InvFin d f → ∀ Φ ∈ d.sch, d.T Φ = (fun X => f X * G X) → d.T (d.om x Φ) = fun X => A f X * B G X

theorem step_comp {x x' : d.G} {A A' B B' : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ}
    (h : StepF d x A B) (h' : StepF d x' A' B') : StepF d (x * x') (A ∘ A') (B ∘ B') := by
  refine ⟨fun f hf => h.1 _ (h'.1 f hf), fun G hG => ⟨(h.2 _ (h'.2 G hG).1).1, fun f hf Φ hΦ hT => ?_⟩⟩
  have e1 := (h'.2 G hG).2 f hf Φ hΦ hT
  have e2 := (h.2 (B' G) (h'.2 G hG).1).2 (A' f) (h'.1 f hf) (d.om x' Φ) (d.om_sch x' Φ hΦ) e1
  rw [map_mul, Module.End.mul_apply]
  exact e2

theorem key_split {f G A' B' : Mx F E d.m d.n → ℂ} (hf : InvFin d f) (hA : InvFin d A') (hG : InvInf d G)
    (hB : InvInf d B') (h : ∀ X, f X * G X = A' X * B' X) : ∀ X Y, f X * G Y = A' X * B' Y := by
  intro X Y
  have hW1 : eInf F • X + finOne F • Y = X + finOne F • (Y - X) := by
    calc eInf F • X + finOne F • Y = (eInf F • X + finOne F • X) + finOne F • (Y - X) := by rw [smul_sub]; abel
      _ = X + finOne F • (Y - X) := by rw [smul_split]
  have hW2 : eInf F • X + finOne F • Y = Y + eInf F • (X - Y) := by
    calc eInf F • X + finOne F • Y = (eInf F • Y + finOne F • Y) + eInf F • (X - Y) := by rw [smul_sub]; abel
      _ = Y + eInf F • (X - Y) := by rw [smul_split]
  have hfin : ∀ w, d.cw w (finOne F • (Y - X)) = 0 := fun w => cw_finOne d w _
  have hinf : finOne F • (eInf F • (X - Y)) = 0 := by rw [smul_smul, finOne_mul_eInf, zero_smul]
  have e := h (eInf F • X + finOne F • Y)
  rw [hW1, hf X _ hfin, hA X _ hfin, ← hW1, hW2, hG Y _ hinf, hB Y _ hinf] at e
  exact e

theorem step_conj (hT : TAll) {x₁ x₂ x' : d.G} {A₁ A₂ B₁ B₂ B' : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ}
    (h₁ : StepF d x₁ A₁ B₁) (h₂ : StepF d x₂ A₂ B₂) (h' : StepF d x' id B') (h1 : x₁ * x₂ = 1) :
    ∃ B, StepF d (x₁ * x' * x₂) id B := by
  have hc := step_comp d (step_comp d h₁ h') h₂
  have h0 := step_comp d h₁ h₂
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
    have key := key_split d hf (h0.1 f hf) hG (h0.2 G hG).1 (fun X => congrFun e0 X)
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
