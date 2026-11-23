import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LinMulti
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.DenseWeakVectors
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.Garding
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselDerivatives.ExpSup

noncomputable section

open MeasureTheory Matrix Filter Topology Set Metric
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.SmLinSub

section Smoothing

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PI.UpqRep PI.KFinSmoothW

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem expS_mul_neg (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • Z) * NormedSpace.exp (t • -Z) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Z).neg_right.smul_left t).smul_right t)]
  simp [smul_neg]

theorem expS_neg_mul (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • -Z) * NormedSpace.exp (t • Z) = 1 := by
  have h := expS_mul_neg (-Z) t
  rwa [neg_neg] at h

def expU (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  ⟨NormedSpace.exp (t • Z), NormedSpace.exp (t • -Z), expS_mul_neg Z t, expS_neg_mul Z t⟩

def dKer (Z : Matrix (Fin n) (Fin n) ℂ) (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun m => fderiv ℝ Φ m (-Z * m)

end Smoothing

end GlobalTheory.SmLinSub

namespace GlobalTheory.SmLinSub

section Rep

open Formalism.MainNotions.S GlobalTheory.Ell

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Matrix (Fin n) (Fin n) ℂ} {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem lie_smulR (c : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) : c • X ∈ lieOf G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  show (c • X)ᴴ * G + G * (c • X) = 0
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, h1, smul_zero]

theorem exp_mem {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH G :=
  CCRuleCW.exp_mem_UH G (t • X) (lie_smulR t hX)

theorem listProd_mem : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ g ∈ l, g ∈ Formalism.QuantumDeterminants.UH G) →
    l.prod ∈ Formalism.QuantumDeterminants.UH G
  | [], _ => by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * 1 = G
    simp
  | g :: l, h => by
    rw [List.prod_cons]
    exact CCRuleCW.UH_mul G _ _ (h g (by simp)) (listProd_mem l fun x hx => h x (by simp [hx]))

theorem expProd_mem {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i, Xs i ∈ lieOf G)
    (t : Fin k → ℝ) : (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.QuantumDeterminants.UH G :=
  listProd_mem _ fun g hg => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact exp_mem (hX i) _

theorem isUnit_of_mem (hG : IsUnit G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) : IsUnit g := by
  have h : gᴴ * G * g = G := hg
  exact isUnit_of_mul_isUnit_right (h.symm ▸ hG : IsUnit (gᴴ * G * g))

theorem conj_mem_lie (hG : IsUnit G) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (hX : X ∈ lieOf G) : g⁻¹ * X * g ∈ lieOf G := by
  have h : gᴴ * G * g = G := hg
  have hX' : Xᴴ * G + G * X = 0 := hX
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem hG hg)
  have h1 : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← h]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hd]; simp
  show (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = gᴴ * Xᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * X * g := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * G + G * X) * g := by rw [h1, h2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX']; simp

theorem rep_mul (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) (hg' : g' ∈ Formalism.QuantumDeterminants.UH G) (w : H) : ρ (g * g') w = ρ g (ρ g' w) := by
  rw [hπ.1.2 g hg g' hg']; rfl

theorem exp_conj_inv {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g := by
  rw [← Matrix.exp_conj' _ _ hg, Matrix.mul_smul, Matrix.smul_mul]

theorem hasDerivAt_dR {w : H} (hw : SmV (lieOf G) ρ w) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) :
    HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) w) (dR ρ X w) 0 := by
  have h1 := hw 1 (fun _ => X) (fun _ => hX)
  have h2 : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t := contDiff_pi.2 fun _ => contDiff_id
  have h3 : ContDiff ℝ ∞ fun t : ℝ => ρ (NormedSpace.exp (t • X)) w := by
    simpa [Function.comp_def] using h1.comp h2
  exact (h3.differentiable (by simp) 0).hasDerivAt

theorem contDiff_deriv_snoc {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    {F : (Fin (k + 1) → ℝ) → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => deriv (fun s : ℝ => F (Fin.snoc t s)) 0 := by
  have hs : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simp only [Fin.snoc_castSucc]
      fun_prop
  have h1 : ContDiff ℝ ∞ (Function.uncurry fun (t : Fin k → ℝ) (s : ℝ) => F (Fin.snoc t s)) := hF.comp hs
  have h2 := ContDiff.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (g := fun _ : Fin k → ℝ => (0 : ℝ)) h1 contDiff_const
    (le_of_eq rfl)
  exact h2.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem dR_mem (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {w : H} (hw : SmV (lieOf G) ρ w)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieOf G) : SmV (lieOf G) ρ (dR ρ X w) := by
  intro k Xs hXs
  have h1 := hw (k + 1) (Fin.snoc Xs X) (fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using hXs j)
  convert contDiff_deriv_snoc h1 using 2 with t
  have h2 := (((ρ _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dR hw hX) :
    HasDerivAt (fun s : ℝ => ρ (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod
      (ρ (NormedSpace.exp (s • X)) w)) _ 0)
  refine h2.deriv.symm.trans ?_
  congr 1
  funext s
  show ρ _ (ρ _ w) = _
  rw [← rep_mul hπ (expProd_mem hXs t) (exp_mem hX s)]
  simp [List.ofFn_succ', -List.ofFn_succ]

theorem prod_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    g * (l.map fun x => g⁻¹ * x * g).prod = l.prod * g := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hg
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc x, ← ih]
    simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]

theorem rep_mem (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {w : H} (hw : SmV (lieOf G) ρ w)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) : SmV (lieOf G) ρ (ρ g w) := by
  intro k Xs hXs
  have hu := isUnit_of_mem hG hg
  have hY : ∀ i, g⁻¹ * Xs i * g ∈ lieOf G := fun i => conj_mem_lie hG hg (hXs i)
  have h1 := ((ρ g).restrictScalars ℝ).contDiff.comp (hw k _ hY)
  convert h1 using 2 with t
  show _ = ρ g _
  rw [← rep_mul hπ (expProd_mem hXs t) hg, ← rep_mul hπ hg (expProd_mem hY t), ← prod_conj hu,
    List.map_ofFn]
  simp only [exp_conj_inv hu, Function.comp_def]

theorem dR_rep (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) ρ) {w : H} (hw : SmV (lieOf G) ρ w)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) (hX : X ∈ lieOf G) :
    dR ρ X (ρ g w) = ρ g (dR ρ (g⁻¹ * X * g) w) := by
  have hu := isUnit_of_mem hG hg
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hu
  have hY := conj_mem_lie hG hg hX
  have h2 := (((ρ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dR hw hY) :
    HasDerivAt (fun s : ℝ => ρ g (ρ (NormedSpace.exp (s • (g⁻¹ * X * g))) w)) _ 0)
  refine Eq.trans ?_ h2.deriv
  unfold dR
  congr 1
  funext s
  show _ = ρ g (ρ _ w)
  rw [← rep_mul hπ hg (exp_mem hY s), ← rep_mul hπ (exp_mem hX s) hg, exp_conj_inv hu]
  simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]

end Rep

end GlobalTheory.SmLinSub
