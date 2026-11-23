import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.Coef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ V}

def act (E : Fin n → Fin n → Module.End ℂ V) (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ V :=
  ∑ a, ∑ b, X a b • E a b

theorem act_apply (X : Matrix (Fin n) (Fin n) ℂ) (v : V) : act E X v = ∑ a, ∑ b, X a b • E a b v := by
  simp [act]

private lemma act_add_smul' (X Y : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v : V) :
    act E (X + c • Y) v = act E X v + c • act E Y v := by
  simp only [act_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, Finset.smul_sum]

private lemma act_single_one' (a b : Fin n) (v : V) : act E (Matrix.single a b (1 : ℂ)) v = E a b v := by
  rw [act_apply]
  simp [Matrix.single_apply, ite_smul, ite_and]

theorem act_cpart (ε : Fin n → Bool) (a b : Fin n) (v : V) :
    act E (cpart1 ε (Matrix.single a b 1)) v + Complex.I • act E (cpart2 ε (Matrix.single a b 1)) v = E a b v := by
  rw [← act_add_smul', ← (Formalism.REAL.cpartMem n ε (Matrix.single a b (1 : ℂ))).2.2.1, act_single_one']

theorem uj_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) : inUJ ε (g * h) := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hh' : hᴴ * Formalism.REAL.Jm ε * h = Formalism.REAL.Jm ε := hh
  show (g * h)ᴴ * Formalism.REAL.Jm ε * (g * h) = Formalism.REAL.Jm ε
  calc (g * h)ᴴ * Formalism.REAL.Jm ε * (g * h) = hᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * h := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hg', hh']

theorem rep_mul (hσ : IsURepOn (UJset ε) σ) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) (v : H) :
    σ (g * h) v = σ g (σ h v) := by
  rw [hσ.1.2 g hg h hh, ContinuousLinearMap.comp_apply]

theorem rep_one (hσ : IsURepOn (UJset ε) σ) (v : H) : σ 1 v = v := by
  rw [hσ.1.1, ContinuousLinearMap.one_apply]

theorem der_right (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (hg : inUJ ε g) (v : V) :
    HasDerivAt (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • X)) (v : H)) (σ g (act E X v : V)) 0 := by
  obtain ⟨-, -, hD3, -⟩ := hD
  have hfun : (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • X)) (v : H)) =
      fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) := by
    funext t
    exact rep_mul hσ hg (Formalism.REAL.expUJ n ε X hX t) _
  rw [hfun, act_apply]
  exact ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hD3 X hX v)

theorem der_flow (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (v : V) (s : ℝ) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))
      (σ (NormedSpace.exp ((s : ℂ) • X)) (act E X v : V)) s := by
  have hg := Formalism.REAL.expUJ n ε X hX s
  have h1 := der_right hσ hD hX hg v
  have h1' : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)) (v : H))
      (σ (NormedSpace.exp ((s : ℂ) • X)) (act E X v : V)) (s - s) := by
    rw [sub_self]; exact h1
  have h2 := HasDerivAt.comp_sub_const s s h1'
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have ht : s + (t - s) = t := by ring
  show σ (NormedSpace.exp ((t : ℂ) • X)) (v : H) =
    σ (NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp (((t - s : ℝ) : ℂ) • X)) (v : H)
  rw [← Formalism.REAL.oneParam n X s (t - s), ht]

theorem rd_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (hg : inUJ ε g) (v : V) (y : H) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hf : ∀ x, inUJ ε x → f x = ⟪y, σ x (v : H)⟫_ℂ) : Rd X f g = ⟪y, σ g (act E X v : V)⟫_ℂ := by
  have hfun : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => ⟪y, σ (g * NormedSpace.exp ((t : ℂ) • X)) (v : H)⟫_ℂ := by
    funext t
    exact hf _ (uj_mul hg (Formalism.REAL.expUJ n ε X hX t))
  have hd := (((innerSL ℂ y).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) (der_right hσ hD hX hg v)
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 = _
  rw [hfun]
  exact hd.deriv

theorem eword_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E) (w : List (Fin n × Fin n)) (v : V) (y : H) :
    ∀ g ∈ UJset ε, Eword ε w (fun x => ⟪y, σ x (v : H)⟫_ℂ) g = ⟪y, σ g (ew E w v : V)⟫_ℂ := by
  induction w with
  | nil =>
    intro g _
    rfl
  | cons p w ih =>
    intro g hg
    have hZ := Formalism.REAL.cpartMem n ε (Matrix.single p.1 p.2 (1 : ℂ))
    have hF : ∀ x, Formalism.REAL.inUJ ε x →
        Formalism.REAL.Eword ε w (fun x => ⟪y, σ x (v : H)⟫_ℂ) x = ⟪y, σ x (Formalism.REAL.ew E w v : V)⟫_ℂ :=
      fun x hx => ih x hx
    have r1 := rd_coef hσ hD hZ.1 hg (Formalism.REAL.ew E w v) y _ hF
    have r2 := rd_coef hσ hD hZ.2.1 hg (Formalism.REAL.ew E w v) y _ hF
    have key : (Formalism.REAL.ew E (p :: w) v : V) =
        act E (Formalism.REAL.cpart1 ε (Matrix.single p.1 p.2 1)) (Formalism.REAL.ew E w v) +
          Complex.I • act E (Formalism.REAL.cpart2 ε (Matrix.single p.1 p.2 1)) (Formalism.REAL.ew E w v) := by
      rw [act_cpart]
      rfl
    show Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single p.1 p.2 1))
        (Formalism.REAL.Eword ε w (fun x => ⟪y, σ x (v : H)⟫_ℂ)) g +
      Complex.I * Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single p.1 p.2 1))
        (Formalism.REAL.Eword ε w (fun x => ⟪y, σ x (v : H)⟫_ℂ)) g = _
    rw [r1, r2, key, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, inner_add_right,
      inner_smul_right]

theorem exp_zero_smul (X : Matrix (Fin n) (Fin n) ℂ) : NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by
  simp

theorem inK_smul {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) : inK ε ((t : ℂ) • X) := by
  obtain ⟨h1, h2⟩ : Formalism.REAL.inG ε X ∧ X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X := hX
  have h1' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := h1
  show (((t : ℂ) • X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * ((t : ℂ) • X) = 0) ∧
    ((t : ℂ) • X) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * ((t : ℂ) • X)
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, h1', smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, h2]

theorem inK_entry {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) {a b : Fin n} (hab : ε a ≠ ε b) : X a b = 0 := by
  obtain ⟨-, h2⟩ : Formalism.REAL.inG ε X ∧ X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X := hX
  have h := congrFun (congrFun h2 a) b
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have key : X a b * ((if ε b then (1 : ℂ) else -1) - (if ε a then 1 else -1)) = 0 := by
    rw [mul_sub, h]; ring
  rcases mul_eq_zero.mp key with h0 | h0
  · exact h0
  · exfalso
    revert h0 hab
    generalize ε a = p
    generalize ε b = q
    cases p <;> cases q <;> norm_num

theorem cpart_inK {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z * Jm ε = Jm ε * Z) :
    inK ε (cpart1 ε Z) ∧ inK ε (cpart2 ε Z) := by
  have hJ2 : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJH : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hZH : Zᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Zᴴ := by
    have h := congrArg Matrix.conjTranspose hZ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJH] at h
    exact h.symm
  have hW : Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε =
      Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε) := by
    calc Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε
        = Formalism.REAL.Jm ε * Zᴴ * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) := by rw [Matrix.mul_assoc (Formalism.REAL.Jm ε * Zᴴ)]
      _ = Zᴴ * Formalism.REAL.Jm ε := by rw [hJ2, Matrix.mul_one, hZH]
      _ = (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) * Zᴴ * Formalism.REAL.Jm ε := by rw [hJ2, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε) := by simp only [Matrix.mul_assoc]
  have hG := Formalism.REAL.cpartMem n ε Z
  have h1 : Formalism.REAL.cpart1 ε Z * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Formalism.REAL.cpart1 ε Z := by
    simp only [Formalism.REAL.cpart1, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, hZ, hW]
  have h2 : Formalism.REAL.cpart2 ε Z * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Formalism.REAL.cpart2 ε Z := by
    simp only [Formalism.REAL.cpart2, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, hZ, hW]
  exact ⟨(show Formalism.REAL.inG ε (Formalism.REAL.cpart1 ε Z) ∧ _ from ⟨hG.1, h1⟩),
    (show Formalism.REAL.inG ε (Formalism.REAL.cpart2 ε Z) ∧ _ from ⟨hG.2.1, h2⟩)⟩

theorem single_comm {a b : Fin n} (hab : ε a = ε b) :
    Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [hab]
  · simp [h]

theorem flow_stable (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (W : Submodule ℂ V) [FiniteDimensional ℂ W] (hW : ∀ w ∈ W, act E X w ∈ W) :
    ∀ v ∈ W.map V.subtype, σ (NormedSpace.exp X) v ∈ W.map V.subtype := by
  intro v hv
  obtain ⟨w0, hw0, rfl⟩ := Submodule.mem_map.mp hv
  haveI : FiniteDimensional ℝ W := FiniteDimensional.complexToReal W
  haveI : CompleteSpace W := FiniteDimensional.complete ℝ W
  let B : W →L[ℝ] W := LinearMap.toContinuousLinearMap (((act E X).restrict hW).restrictScalars ℝ)
  have hB : ∀ x : W, ((B x : W) : V) = act E X (x : V) := fun x => rfl
  let u : ℝ → W := fun t => NormedSpace.exp (((1 : ℝ) - t) • B) ⟨w0, hw0⟩
  have hu : ∀ t, HasDerivAt u (-(B (u t))) t := by
    intro t
    have h1 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) B ((1 : ℝ) - t)
    have h2 : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have h3 := h1.scomp t h2
    have h4 := (ContinuousLinearMap.apply ℝ W (⟨w0, hw0⟩ : W)).hasFDerivAt.comp_hasDerivAt t h3
    have h5 : HasDerivAt (fun s : ℝ => NormedSpace.exp (((1 : ℝ) - s) • B) (⟨w0, hw0⟩ : W))
        (-(B (NormedSpace.exp (((1 : ℝ) - t) • B) (⟨w0, hw0⟩ : W)))) t := by
      simpa [ContinuousLinearMap.mul_apply, Function.comp_def] using h4
    exact h5
  let b := Module.finBasis ℂ W
  have e1 : ∀ (g : Matrix (Fin n) (Fin n) ℂ) (y : W),
      ∑ i, b.repr y i • σ g (((b i : W) : V) : H) = σ g ((y : V) : H) := by
    intro g y
    conv_rhs => rw [← b.sum_repr y]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  have e2 : ∀ (g : Matrix (Fin n) (Fin n) ℂ) (y : W),
      ∑ i, b.repr y i • σ g ((act E X ((b i : W) : V) : V) : H) = σ g ((act E X (y : V) : V) : H) := by
    intro g y
    conv_rhs => rw [← b.sum_repr y]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  have hφ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (((u s : W) : V) : H)) 0 t := by
    intro t
    have hsum : HasDerivAt (fun s : ℝ => ∑ i, b.repr (u s) i • σ (NormedSpace.exp ((s : ℂ) • X)) (((b i : W) : V) : H))
        (∑ i, (b.repr (u t) i • σ (NormedSpace.exp ((t : ℂ) • X)) ((act E X ((b i : W) : V) : V) : H) +
          b.repr (-(B (u t))) i • σ (NormedSpace.exp ((t : ℂ) • X)) (((b i : W) : V) : H))) t := by
      refine HasDerivAt.fun_sum (u := Finset.univ)
        (A := fun i s => b.repr (u s) i • σ (NormedSpace.exp ((s : ℂ) • X)) (((b i : W) : V) : H)) fun i _ => ?_
      have hc : HasDerivAt (fun s => b.repr (u s) i) (b.repr (-(B (u t))) i) t := by
        have h5 := (LinearMap.toContinuousLinearMap ((b.coord i).restrictScalars ℝ)).hasFDerivAt.comp_hasDerivAt t (hu t)
        exact h5
      exact hc.smul (der_flow hσ hD hX ((b i : W) : V) t)
    have heq : (fun s : ℝ => ∑ i, b.repr (u s) i • σ (NormedSpace.exp ((s : ℂ) • X)) (((b i : W) : V) : H)) =
        fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (((u s : W) : V) : H) := funext fun s => e1 _ (u s)
    rw [heq] at hsum
    convert hsum using 1
    rw [Finset.sum_add_distrib, e2, e1, Submodule.coe_neg, Submodule.coe_neg, hB, map_neg, add_neg_cancel]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hφ s).differentiableAt) (fun s => (hφ s).deriv) 1 0
  have hu1 : u 1 = ⟨w0, hw0⟩ := by simp [u]
  rw [hu1, exp_zero_smul, rep_one hσ, Complex.ofReal_one, one_smul] at hconst
  exact Submodule.mem_map.mpr ⟨(u 0 : V), (u 0).2, hconst.symm⟩

theorem act_stable (hD : IsDer ε σ V E) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (W : Submodule ℂ V) [FiniteDimensional ℂ W] (hW : IsKStableOn ε σ (W.map V.subtype)) :
    ∀ w ∈ W, act E X w ∈ W := by
  intro w hw
  have hXg : Formalism.REAL.inG ε X := (show Formalism.REAL.inG ε X ∧ X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X from hX).1
  have hd := hD.2.2.1 X hXg w
  have hcl : IsClosed ((W.map V.subtype : Submodule ℂ H) : Set H) :=
    Submodule.closed_of_finiteDimensional _
  have hmem : ∀ t : ℝ, σ (NormedSpace.exp ((t : ℂ) • X)) (w : H) ∈ W.map V.subtype := fun t =>
    hW _ ((Formalism.REAL.kFacts n ε).2.2.2.1 _ (inK_smul hX t)) _ (Submodule.mem_map_of_mem hw)
  have hin : ((∑ a, ∑ b, X a b • E a b w : V) : H) ∈ W.map V.subtype := by
    refine hcl.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.mp hd) (Filter.Eventually.of_forall fun t => ?_)
    rw [slope_def_module]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ (hmem t) (hmem 0))
  rw [← act_apply] at hin
  obtain ⟨u, hu, hu'⟩ := Submodule.mem_map.mp hin
  have hue : u = act E X w := Subtype.ext hu'
  exact hue ▸ hu

theorem kStable_iff (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    KStable ε E W ↔ IsKStableOn ε σ (W.map V.subtype) := by
  constructor
  · intro hK k hk
    obtain ⟨Y, hY, hYk, -⟩ := Formalism.REAL.compact_exists_log_bounded ε k hk
    have hYg : Formalism.REAL.inG ε Y := (show Formalism.REAL.inG ε Y ∧ Y * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Y from hY).1
    have hst : ∀ w ∈ W, act E Y w ∈ W := by
      intro w hw
      rw [act_apply]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      by_cases hab : ε a = ε b
      · exact Submodule.smul_mem _ _ (hK a b hab w hw)
      · rw [inK_entry hY hab, zero_smul]
        exact Submodule.zero_mem _
    rw [← hYk]
    exact flow_stable hσ hD hYg W hst
  · intro hK a b hab w hw
    have hc := cpart_inK (single_comm (ε := ε) hab)
    rw [← act_cpart ε a b w]
    exact Submodule.add_mem _ (act_stable hD hc.1 W hK w hw)
      (Submodule.smul_mem _ _ (act_stable hD hc.2 W hK w hw))

theorem diag_inK (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    inK ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  show ((Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)ᴴ * Formalism.REAL.Jm ε +
      Formalism.REAL.Jm ε * (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) = 0) ∧
    (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) * Formalism.REAL.Jm ε =
      Formalism.REAL.Jm ε * (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)
  refine ⟨?_, ?_⟩
  · rw [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_zero]
    congr 1
    funext a
    simp only [Pi.star_apply, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I, Pi.add_apply,
      Pi.zero_apply]
    ring
  · rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

theorem exp_diag (θ : Fin n → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) =
      Matrix.diagonal (fun a => Complex.exp (((t * θ a : ℝ) : ℂ) * Complex.I)) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext a
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem act_diag (d : Fin n → ℂ) (v : V) : act E (Matrix.diagonal d) v = ∑ a, d a • E a a v := by
  rw [act_apply]
  simp [Matrix.diagonal_apply, ite_smul]

theorem der_exp_smul (c : ℂ) (v : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * c) • v) (c • Complex.exp ((t : ℂ) * c) • v) t := by
  have h1 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * c)) (Complex.exp ((t : ℂ) * c) * c) t := by
    have h0 := ((hasDerivAt_id (t : ℂ)).mul_const c).cexp
    simpa using h0.comp_ofReal
  convert h1.smul_const v using 1
  rw [smul_smul, mul_comm]

theorem weight_iff (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E) (μ : Fin n → ℝ) (v : V) :
    IsWeight E μ v ↔ IsWtOn (Kset ε) σ μ (v : H) := by
  constructor
  · intro hw θ _
    have hw' : ∀ a, E a a v = ((μ a : ℝ) : ℂ) • v := hw
    have hDk0 : Formalism.REAL.inG ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) ∧
        (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) * Formalism.REAL.Jm ε =
          Formalism.REAL.Jm ε * (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := diag_inK ε θ
    have hDg := hDk0.1
    have hact : act E (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) v =
        (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • v := by
      rw [act_diag]
      simp only [hw', smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    have hu : ∀ s : ℝ, HasDerivAt (fun t : ℝ =>
        σ (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)) (v : H))
        ((((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) •
          σ (NormedSpace.exp ((s : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)) (v : H)) s := by
      intro s
      have h0 := der_flow hσ hD hDg v s
      rw [hact, Submodule.coe_smul, map_smul] at h0
      exact h0
    have hφ : ∀ s : ℝ, HasDerivAt (fun t : ℝ =>
        Complex.exp ((t : ℂ) * (-(((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I))) •
          σ (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)) (v : H)) 0 s := by
      intro s
      have h1 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * (-(((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I))))
          (Complex.exp ((s : ℂ) * (-(((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I))) *
            (-(((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I))) s :=
        ((hasDerivAt_id (s : ℂ)).mul_const _).cexp.comp_ofReal.congr_deriv (by simp)
      refine (h1.smul (hu s)).congr_deriv ?_
      rw [smul_smul, ← add_smul, mul_neg (Complex.exp _), add_neg_cancel, zero_smul]
    have hconst := is_const_of_deriv_eq_zero (fun s => (hφ s).differentiableAt) (fun s => (hφ s).deriv) 1 0
    simp only [Complex.ofReal_one, one_mul, one_smul, Complex.ofReal_zero, zero_mul, zero_smul,
      Complex.exp_zero, NormedSpace.exp_zero] at hconst
    rw [rep_one hσ] at hconst
    have hexp : NormedSpace.exp (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) =
        Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := by
      have h2 := exp_diag θ 1
      simpa using h2
    rw [← hexp]
    calc σ (NormedSpace.exp (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)) (v : H)
        = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) •
          (Complex.exp (-(((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I)) •
            σ (NormedSpace.exp (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)) (v : H)) := by
          rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
      _ = _ := by rw [hconst]
  · intro hw a
    obtain ⟨e, he⟩ : ∃ e : Fin n → ℝ, e = Pi.single a (1 : ℝ) := ⟨_, rfl⟩
    have hDk := diag_inK ε e
    have hDk0 : Formalism.REAL.inG ε (Matrix.diagonal fun b => (e b : ℂ) * Complex.I) ∧
        (Matrix.diagonal fun b => (e b : ℂ) * Complex.I) * Formalism.REAL.Jm ε =
          Formalism.REAL.Jm ε * (Matrix.diagonal fun b => (e b : ℂ) * Complex.I) := hDk
    have hDg := hDk0.1
    have key : ∀ t : ℝ, σ (NormedSpace.exp ((t : ℂ) •
          Matrix.diagonal fun b => (e b : ℂ) * Complex.I)) (v : H) =
        Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H) := by
      intro t
      have hmem := (Formalism.REAL.kFacts n ε).2.2.2.1 _ (inK_smul hDk t)
      rw [exp_diag] at hmem ⊢
      refine (hw (fun b => t * e b) hmem).trans ?_
      congr 1
      congr 1
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [he, Pi.single_apply, hb]) (by simp)]
      simp only [he, Pi.single_eq_same, mul_one]
      push_cast
      ring
    have hL := der_flow hσ hD hDg v 0
    have hR := der_exp_smul ((μ a : ℂ) * Complex.I) (v : H) 0
    have hfun : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) •
          Matrix.diagonal fun b => (e b : ℂ) * Complex.I)) (v : H)) =
        fun s : ℝ => Complex.exp ((s : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H) := funext key
    rw [hfun] at hL
    have hu := hL.unique hR
    rw [exp_zero_smul, rep_one hσ, act_diag] at hu
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul] at hu
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [he, Pi.single_apply, hb]) (by simp)] at hu
    simp only [he, Pi.single_eq_same, Complex.ofReal_one, one_mul] at hu
    apply smul_right_injective V Complex.I_ne_zero
    apply Subtype.ext
    simp only [Submodule.coe_smul] at hu ⊢
    rw [hu, smul_smul, mul_comm]

theorem coef_flow : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V), IsURepOn (UJset ε) σ → IsDer ε σ V E → (∀ (w : List (Fin n × Fin n)) (v : V) (y : H), ∀ g ∈ UJset ε, Eword ε w (fun x => ⟪y, σ x (v : H)⟫_ℂ) g = ⟪y, σ g (ew E w v : V)⟫_ℂ) ∧ (∀ W : Submodule ℂ V, FiniteDimensional ℂ W → (KStable ε E W ↔ IsKStableOn ε σ (W.map V.subtype))) ∧ ∀ (μ : Fin n → ℝ) (v : V), IsWeight E μ v ↔ IsWtOn (Kset ε) σ μ (v : H) := by
  intro n ε H _ _ _ σ V E hσ hD
  exact ⟨fun w v y => eword_coef hσ hD w v y, fun W hW => (haveI := hW; kStable_iff hσ hD W),
    fun μ v => weight_iff hσ hD μ v⟩

end GlobalTheory.Jet.Coef
