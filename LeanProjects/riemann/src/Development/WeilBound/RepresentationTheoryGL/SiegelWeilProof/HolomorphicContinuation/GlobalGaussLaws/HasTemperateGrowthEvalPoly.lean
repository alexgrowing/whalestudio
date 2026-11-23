import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem trace_frame {m : ℕ} {M fr : Matrix (Fin m) (Fin m) ℂ} (h1 : IsUnit fr.det) (h2 : frᴴ * M * fr = 1)
    (z : Matrix (Fin m) (Fin n) ℂ) :
    Matrix.trace (zᴴ * M * z) = ((∑ a, ∑ i, ‖(fr⁻¹ * z) a i‖ ^ 2 : ℝ) : ℂ) := by
  set y := fr⁻¹ * z with hy
  have hz : z = fr * y := by rw [hy, Matrix.mul_nonsing_inv_cancel_left _ _ h1]
  have e : zᴴ * M * z = yᴴ * y := by
    rw [hz, Matrix.conjTranspose_mul]
    calc yᴴ * frᴴ * M * (fr * y) = yᴴ * (frᴴ * M * fr) * y := by simp only [Matrix.mul_assoc]
      _ = yᴴ * y := by rw [h2, Matrix.mul_one]
  rw [e, Matrix.trace]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_apply, ← Complex.conj_mul']
  rfl

theorem gauss_split {V : HSp D} {τ : D.what₂.Tau} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (l : D.what₂.Tau → ℝ)
    (hfr : IsTauFrame V τ s ε fr) (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) :
    gauss V l s z = gs (cLoc l τ) (fr⁻¹ * z τ) * gAway V l s τ z := by
  classical
  unfold gauss gAway gs cLoc
  rw [← Complex.exp_add]
  congr 1
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ τ), trace_frame hfr.1 hfr.2.2 (z τ)]
  have hf : (Finset.univ.filter fun τ' => τ' ≠ τ) = Finset.univ.erase τ := by
    ext x; simp
  rw [hf]
  push_cast
  ring

theorem evalPoly_add {m : ℕ} (p q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : evalPoly (p + q) z = evalPoly p z + evalPoly q z := by
  simp [evalPoly]

theorem evalPoly_mul {m : ℕ} (p q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : evalPoly (p * q) z = evalPoly p z * evalPoly q z := by
  simp [evalPoly]

theorem evalPoly_C {m : ℕ} (a : ℂ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    evalPoly (MvPolynomial.C a : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) z = a := by
  simp [evalPoly]

theorem evalPoly_X {m : ℕ} (v : D.what₂.Tau × Fin m × Fin n × Bool) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    evalPoly (MvPolynomial.X v : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) z =
      if v.2.2.2 then conj (z v.1 v.2.1 v.2.2.1) else z v.1 v.2.1 v.2.2.1 := by
  simp [evalPoly]

theorem eval_bind₁' {σ ι : Type*} (f : σ → ℂ) (g : ι → MvPolynomial σ ℂ) (p : MvPolynomial ι ℂ) :
    MvPolynomial.eval f (MvPolynomial.bind₁ g p) = MvPolynomial.eval (fun i => MvPolynomial.eval f (g i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

def polyAt {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) :
    MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ :=
  MvPolynomial.bind₁ (fun k : Fin m × Fin n × Bool => if k.2.2 then
      ∑ a, MvPolynomial.C (star ((fr⁻¹) k.1 a)) * MvPolynomial.X (τ, a, k.2.1, true)
    else ∑ a, MvPolynomial.C ((fr⁻¹) k.1 a) * MvPolynomial.X (τ, a, k.2.1, false)) P

theorem evalPoly_polyAt {m : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (P : PX m n)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : evalPoly (polyAt τ fr P) z = evX P (fr⁻¹ * z τ) := by
  unfold evalPoly polyAt evX
  refine (eval_bind₁' _ _ _).trans (congrArg (fun f => MvPolynomial.eval f P) (funext fun k => ?_))
  obtain ⟨c, i, b⟩ := k
  cases b <;> simp [Matrix.mul_apply, star_sum]

theorem poly_split {m : ℕ} (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ} (hfr : IsUnit fr.det)
    (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    ∃ (k : ℕ) (Pi : Fin k → PX m n) (pi : Fin k → MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ),
      (∀ i, ∀ v ∈ (pi i).vars, v.1 ≠ τ) ∧
      ∀ z, evalPoly p z = ∑ i, evX (Pi i) (fr⁻¹ * z τ) * evalPoly (pi i) z := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨1, fun _ => MvPolynomial.C a, fun _ => 1, by simp, fun z => ?_⟩
    simp [evalPoly, evX]
  | add p q hp hq =>
    obtain ⟨k1, P1, p1, h1, e1⟩ := hp
    obtain ⟨k2, P2, p2, h2, e2⟩ := hq
    refine ⟨k1 + k2, Fin.append P1 P2, Fin.append p1 p2, ?_, fun z => ?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using h1 j
      · simpa using h2 j
    · rw [Fin.sum_univ_add, evalPoly_add, e1, e2]
      simp
  | mul_X p v hp =>
    obtain ⟨k, Pi, pi, h, e⟩ := hp
    by_cases hv : v.1 = τ
    · refine ⟨k, fun i => Pi i * (if v.2.2.2 then ∑ c, MvPolynomial.C (star (fr v.2.1 c)) * MvPolynomial.X (c, v.2.2.1, true)
          else ∑ c, MvPolynomial.C (fr v.2.1 c) * MvPolynomial.X (c, v.2.2.1, false)), pi, h, fun z => ?_⟩
      have hz : z τ = fr * (fr⁻¹ * z τ) := (Matrix.mul_nonsing_inv_cancel_left _ _ hfr).symm
      have hw : (if v.2.2.2 then conj (z v.1 v.2.1 v.2.2.1) else z v.1 v.2.1 v.2.2.1) =
          evX (if v.2.2.2 then ∑ c, MvPolynomial.C (star (fr v.2.1 c)) * MvPolynomial.X (c, v.2.2.1, true)
            else ∑ c, MvPolynomial.C (fr v.2.1 c) * MvPolynomial.X (c, v.2.2.1, false)) (fr⁻¹ * z τ) := by
        rw [hv]
        conv_lhs => rw [hz]
        split_ifs <;> simp [evX, Matrix.mul_apply, map_sum]
      rw [evalPoly_mul, e, evalPoly_X, hw, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [evX, map_mul]
      ring
    · refine ⟨k, Pi, fun i => pi i * MvPolynomial.X v, fun i w hw => ?_, fun z => ?_⟩
      · have := MvPolynomial.vars_mul (pi i) (MvPolynomial.X v) hw
        rw [Finset.mem_union, MvPolynomial.vars_X] at this
        rcases this with h' | h'
        · exact h i w h'
        · rw [Finset.mem_singleton] at h'
          rw [h']
          exact hv
      · rw [evalPoly_mul, e, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [evalPoly_mul]
        ring

theorem splitFock : SplitFock := by
  intro D n V θ l s τ ε fr _ hfr Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, hg, rfl⟩ := hφ
    obtain ⟨k, Pi, pi, hpi, e⟩ := poly_split τ hfr.1 p
    refine ⟨k, Pi, fun i x => evalPoly (pi i) (fun τ => compAt θ τ x) * gAway V l s τ (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j)), fun i => Submodule.subset_span ⟨pi i, g, hg, hpi i, rfl⟩, ?_⟩
    funext x
    rw [Finset.sum_apply, e, gauss_split l hfr, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [tens, fP]
    ring
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k1, P1, Ψ1, h1, e1⟩ := hx
    obtain ⟨k2, P2, Ψ2, h2, e2⟩ := hy
    refine ⟨k1 + k2, Fin.append P1 P2, Fin.append Ψ1 Ψ2,
      fun i => Fin.addCases (fun j => by simpa using h1 j) (fun j => by simpa using h2 j) i, ?_⟩
    rw [Fin.sum_univ_add, e1, e2]
    simp
  | smul a x _ hx =>
    obtain ⟨k, Qs, Ψi, h, e⟩ := hx
    refine ⟨k, Qs, fun i => a • Ψi i, fun i => Submodule.smul_mem _ a (h i), ?_⟩
    rw [e, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp only [tens, Pi.smul_apply, smul_eq_mul]
    ring

theorem tens_zero {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (f : (Fin m → Fin n → ℂ) → ℂ) : tens θ τ fr f (0 : Mx D m n → ℂ) = 0 := by
  funext x; simp [tens]

theorem tens_add {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (f : (Fin m → Fin n → ℂ) → ℂ) (Ψ Ψ' : Mx D m n → ℂ) : tens θ τ fr f (Ψ + Ψ') = tens θ τ fr f Ψ + tens θ τ fr f Ψ' := by
  funext x; simp [tens, mul_add]

theorem tens_smul {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ)
    (f : (Fin m → Fin n → ℂ) → ℂ) (a : ℂ) (Ψ : Mx D m n → ℂ) : tens θ τ fr f (a • Ψ) = a • tens θ τ fr f Ψ := by
  funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring

theorem tensMem_fock {V : HSp D} {θ : InfFam D} {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr)
    {Ψ : Mx D V.rank n → ℂ} (hΨ : Ψ ∈ awayA θ V n l s τ) (P : PX V.rank n) :
    tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ fockA θ V n l s := by
  induction hΨ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, hg, -, rfl⟩ := hφ
    refine Submodule.subset_span ⟨polyAt τ fr P * p, g, hg, ?_⟩
    funext x
    simp only [tens, fP, evalPoly_mul, evalPoly_polyAt, gauss_split l hfr]
    ring
  | zero => rw [tens_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [tens_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [tens_smul]; exact Submodule.smul_mem _ a hx

def coordCLM {m : ℕ} (v : D.what₂.Tau × Fin m × Fin n × Bool) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) v.2.2.1).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) v.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) v.1))

theorem hasTemperateGrowth_evalPoly {m : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly p (fun τ => Matrix.of (w τ))) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (MvPolynomial.C a) (fun τ => Matrix.of (w τ))) =
        fun _ => a := funext fun w => evalPoly_C a _
    rw [e]
    exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have e : (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p + q) (fun τ => Matrix.of (w τ))) =
        (fun w => evalPoly p (fun τ => Matrix.of (w τ))) + fun w => evalPoly q (fun τ => Matrix.of (w τ)) :=
      funext fun w => evalPoly_add p q _
    rw [e]
    exact hp.add hq
  | mul_X p v hp =>
    have hc : Function.HasTemperateGrowth (fun w : D.what₂.Tau → Fin m → Fin n → ℂ =>
        if v.2.2.2 then conj (w v.1 v.2.1 v.2.2.1) else w v.1 v.2.1 v.2.2.1) := by
      split_ifs
      · exact (Complex.conjCLE.toContinuousLinearMap.comp (coordCLM v)).hasTemperateGrowth
      · exact (coordCLM v).hasTemperateGrowth
    have e : (fun w : D.what₂.Tau → Fin m → Fin n → ℂ => evalPoly (p * MvPolynomial.X v) (fun τ => Matrix.of (w τ))) =
        (fun w => evalPoly p (fun τ => Matrix.of (w τ))) *
          fun w => if v.2.2.2 then conj (w v.1 v.2.1 v.2.2.1) else w v.1 v.2.1 v.2.2.1 :=
      funext fun w => by rw [evalPoly_mul, evalPoly_X]; rfl
    rw [e]
    exact hp.mul hc

theorem fockA_le_schwartzA {V : HSp D} {θ : InfFam D} {l : D.what₂.Tau → ℝ} (hl : ∀ τ, l τ ≠ 0)
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) :
    fockA θ V n l s ≤ schwartzA θ V.rank n := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨p, g, hg, rfl⟩
  obtain ⟨f, hf⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_gauss D n V l hl s hs
  refine Submodule.subset_span ⟨SchwartzMap.smulLeftCLM ℂ (fun w => evalPoly p (fun τ => Matrix.of (w τ))) f, g, hg, ?_⟩
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_evalPoly p), hf, smul_eq_mul]
  rfl

theorem tensMem : TensMem := by
  intro D n V θ l s τ ε fr _ hl hs hfr Ψ hΨ P
  have h := tensMem_fock hfr hΨ P
  exact ⟨fockA_le_schwartzA hl hs h, h⟩

end PositivityTheory.Rg.Sw.Glob
