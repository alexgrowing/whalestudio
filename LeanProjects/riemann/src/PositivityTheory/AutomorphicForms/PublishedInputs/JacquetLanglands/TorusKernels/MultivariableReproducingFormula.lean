import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk

abbrev PG (F : Type) [Field F] : Type := GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F)

structure Dat (F I Gf : Type) [Field F] [Group Gf] where

  σ : I → F →+* ℝ

  j : GL (Fin 2) F →* Gf

  H : Subgroup Gf

  χ : H →* ℂˣ

  hf : (Fin 2 → F) → Gf → ℝ
  cenH : ∀ γ ∈ Subgroup.center (GL (Fin 2) F), j γ ∈ H
  cenC : ∀ γ ∈ Subgroup.center (GL (Fin 2) F), j γ ∈ Subgroup.center Gf

abbrev X (I : Type) : Type := I → P

theorem center_smul (g : GL (Fin 2) ℝ) (hb : g 0 1 = 0) (hc : g 1 0 = 0) (h : g 0 0 = g 1 1) (z : P) : g • z = z := by
  refine Subtype.ext ?_
  have h0 := den_ne g z.2
  rw [coe_smul, div_eq_iff h0]
  simp [num, den, hb, hc, h, mul_comm]

theorem center_entries {F : Type} [Field F] {γ : GL (Fin 2) F} (h : γ ∈ Subgroup.center (GL (Fin 2) F)) :
    γ 0 1 = 0 ∧ γ 1 0 = 0 ∧ γ 0 0 = γ 1 1 := by
  have h1 := Subgroup.mem_center_iff.1 h ⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
  have h2 := Subgroup.mem_center_iff.1 h ⟨!![1, 0; 1, 1], !![1, 0; -1, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
  have a1 := congrArg (fun g : GL (Fin 2) F => g 0 0) h1
  have a2 := congrArg (fun g : GL (Fin 2) F => g 0 1) h1
  have a3 := congrArg (fun g : GL (Fin 2) F => g 0 0) h2
  simp [Matrix.mul_apply, Fin.sum_univ_two] at a1 a2 a3
  exact ⟨a3, a1, by linear_combination -a2⟩

namespace Dat

variable {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf)

def r (v : I) : GL (Fin 2) F →* GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.map (D.σ v)

def act (γ : GL (Fin 2) F) (z : X I) : X I := fun v => D.r v γ • z v

def Xs (_ : Dat F I Gf) : Type := X I

def Om : Type := Gf ⧸ D.H

def Cj (_ : Dat F I Gf) : Type := PG F

instance : TopologicalSpace D.Xs := inferInstanceAs (TopologicalSpace (I → P))
instance : MeasurableSpace D.Xs := inferInstanceAs (MeasurableSpace (I → P))
instance [Fintype I] : MeasureSpace D.Xs := inferInstanceAs (MeasureSpace (I → P))
instance : MeasurableSpace D.Om := ⊤
instance : DiscreteMeasurableSpace D.Om := ⟨fun _ => trivial⟩
instance : MeasurableSpace D.Cj := ⊤
instance : DiscreteMeasurableSpace D.Cj := ⟨fun _ => trivial⟩

def permX : GL (Fin 2) F →* Equiv.Perm D.Xs :=
  (MulAction.toPermHom (I → GL (Fin 2) ℝ) (I → P)).comp (MonoidHom.pi D.r)

def permO : GL (Fin 2) F →* Equiv.Perm D.Om := (MulAction.toPermHom Gf (Gf ⧸ D.H)).comp D.j

instance : MulAction (PG F) D.Xs :=
  MulAction.compHom _ (QuotientGroup.lift _ D.permX fun γ h => Equiv.ext fun z => funext fun v => by
    obtain ⟨h1, h2, h3⟩ := center_entries h
    exact center_smul (D.r v γ) (by change D.σ v (γ 0 1) = 0; rw [h1, map_zero]) (by change D.σ v (γ 1 0) = 0; rw [h2, map_zero])
      (by change D.σ v (γ 0 0) = D.σ v (γ 1 1); rw [h3]) (z v))

instance : MulAction (PG F) D.Om :=
  MulAction.compHom _ (QuotientGroup.lift _ D.permO fun γ h => Equiv.ext fun x => by
    induction x using QuotientGroup.induction_on with
    | H x =>
      refine (QuotientGroup.eq.2 ?_ : ((D.j γ * x : Gf) : Gf ⧸ D.H) = (x : Gf ⧸ D.H))
      rw [← Subgroup.mem_center_iff.1 (D.cenC γ h) x, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact inv_mem (D.cenH γ h))

def el (γ : D.Cj) : PG F := γ

instance : MulAction (PG F) D.Cj where
  smul δ γ := (δ * D.el γ * δ⁻¹ : PG F)
  one_smul γ := by change (1 * D.el γ * 1⁻¹ : PG F) = D.el γ; simp
  mul_smul a b γ := by change (a * b * D.el γ * (a * b)⁻¹ : PG F) = a * (b * D.el γ * b⁻¹) * a⁻¹; group

theorem mk_smulX (γ : GL (Fin 2) F) (z : D.Xs) : (γ : PG F) • z = D.act γ z := rfl

theorem mk_smulO (γ : GL (Fin 2) F) (x : Gf) : (γ : PG F) • (show D.Om from (x : Gf ⧸ D.H)) = ((D.j γ * x : Gf) : Gf ⧸ D.H) := rfl

theorem smulC (δ : PG F) (γ : D.Cj) : D.el (δ • γ) = δ * D.el γ * δ⁻¹ := rfl

abbrev Y : Type := D.Om × D.Xs

def rep (ω : D.Om) : Gf := Quotient.out (s := QuotientGroup.leftRel D.H) ω

variable [Fintype I]

def μY : Measure D.Y := Measure.count.prod volume

def μC : Measure ((D.Cj × D.Om) × D.Xs) := Measure.count.prod volume

def Ht (s : Fin 2 → F) (z : X I) (x : Gf) : ℝ := (∏ v, |(z v).1.im| / ‖(D.σ v (s 0) : ℂ) * (z v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2) * D.hf s x

def HtY (s : Fin 2 → F) (y : D.Y) : ℝ := D.Ht s y.2 (D.rep y.1)

end Dat

def Near {I : Type} (δ : ℝ) (z w : X I) : Prop := ∀ v, δ ≤ kap (z v) (w v)

def Sg {I : Type} (C c : ℝ) (z : X I) : Prop := ∀ v, |(z v).1.re| ≤ C ∧ c ≤ |(z v).1.im| ∧ ∀ v', |(z v).1.im| ≤ C * |(z v').1.im|

def Fix {F : Type} [Field F] (s : Fin 2 → F) (γ : PG F) : Prop := ∃ c : F, s ᵥ* (γ.out : Matrix (Fin 2) (Fin 2) F) = c • s

def IsEll {F : Type} [Field F] (γ : PG F) : Prop := ∀ s : Fin 2 → F, s ≠ 0 → ¬ Fix s γ

namespace Dat

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

structure Ax : Prop where
  cF : Countable F
  cO : Countable D.Om
  two : Nontrivial I
  χn : ∀ h, ‖(D.χ h : ℂ)‖ = 1
  pos : ∀ s, s ≠ 0 → ∀ x, 0 < D.hf s x
  rat : ∀ s, s ≠ 0 → ∀ γ x, D.hf s (D.j γ * x) * ∏ v, |D.σ v γ.val.det| = D.hf (s ᵥ* γ.val) x
  smul : ∀ s, s ≠ 0 → ∀ a : F, a ≠ 0 → ∀ x, D.hf (a • s) x = D.hf s x * ∏ v, D.σ v a ^ 2
  lev : ∀ s, s ≠ 0 → ∀ x, ∀ h ∈ D.H, D.hf s (x * h) = D.hf s x
  mul : ∀ a, ∃ C, ∀ s, s ≠ 0 → ∀ x, D.hf s (x * a) ≤ C * D.hf s x
  dbl : ∀ a : Gf, {ω : Gf ⧸ D.H | ∃ h ∈ D.H, ω = ((h * a : Gf) : Gf ⧸ D.H)}.Finite
  prod : ∀ s s' : Fin 2 → F, s 0 * s' 1 - s 1 * s' 0 ≠ 0 → ∀ x, D.hf s x * D.hf s' x ≤ ∏ v, D.σ v (s 0 * s' 1 - s 1 * s' 0) ^ 2
  mink : ∃ c₀, 0 < c₀ ∧ ∀ z x, ∃ s, s ≠ 0 ∧ c₀ ≤ D.Ht s z x
  normal : ∀ c₀, 0 < c₀ → ∃ (S : Finset Gf) (C c : ℝ), 0 < c ∧ ∀ z x, c₀ ≤ D.Ht ![0, 1] z x →
    ∃ b : GL (Fin 2) F, b 1 0 = 0 ∧ (∃ x' ∈ S, ∃ h ∈ D.H, D.j b * x = x' * h) ∧ Sg C c (D.act b z)
  count : ∀ (ω : D.Om) (δ C c : ℝ), 0 < δ → 0 < c → ∃ C' : ℝ, ∀ z : D.Xs, Sg C c z →
    {γ : PG F | γ • ω = ω ∧ Near δ z (γ • z)}.Finite ∧
      ({γ : PG F | γ • ω = ω ∧ Near δ z (γ • z)}.ncard : ℝ) ≤ C' * (1 + ∏ v, |(z v).1.im|)

def Compat (k : I → ℕ) : Prop :=
  ∀ γ (h : γ ∈ Subgroup.center (GL (Fin 2) F)), (D.χ ⟨D.j γ, D.cenH γ h⟩ : ℂ) = ∏ v, ((SignType.sign (D.σ v (γ 0 0)) : ℝ) : ℂ) ^ k v

def J (k : I → ℕ) (γ : GL (Fin 2) F) (z : X I) : ℂ := ∏ v, j1 (k v) (D.r v γ) (z v)

end Dat

def qq {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : ℂ := ∏ v, q1 (k v) (z v) (w v)

def Kap {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : ℝ := ∏ v, kap (z v) (w v) ^ ((k v : ℝ) / 2)

def nrm {I : Type} [Fintype I] (k : I → ℕ) (z : X I) : ℝ := ∏ v, |(z v).1.im| ^ ((k v : ℝ) / 2)

open Classical in

def SepHol {I : Type} (f : X I → ℂ) : Prop := Continuous f ∧ ∀ z v, Hol1 fun t => f (Function.update z v t)

namespace Dat

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

structure IsForm (k : I → ℕ) (f : X I × Gf → ℂ) : Prop where
  hol : ∀ x, SepHol fun z => f (z, x)
  aut : ∀ γ z x, f (D.act γ z, D.j γ * x) = D.J k γ z * f (z, x)
  lev : ∀ z x (h : D.H), f (z, x * h) = D.χ h * f (z, x)
  bdd : ∃ C, ∀ z x, ‖f (z, x)‖ * nrm k z ≤ C

def M (k : I → ℕ) : Submodule ℂ (X I × Gf → ℂ) := Submodule.span ℂ {f | D.IsForm k f}

def Op {ι : Type} [Fintype ι] (a : ι → Gf) : Module.End ℂ (X I × Gf → ℂ) where
  toFun f p := ∑ i, f (p.1, p.2 * a i)
  map_add' f g := by funext p; simp [Finset.sum_add_distrib]
  map_smul' c f := by funext p; simp [Finset.mul_sum]

def Good {ι : Type} [Fintype ι] (a : ι → Gf) : Prop :=
  ∀ f : Gf → ℂ, (∀ x (h : D.H), f (x * h) = D.χ h * f x) → ∀ x (h : D.H), ∑ i, f (x * h * a i) = D.χ h * ∑ i, f (x * a i)

def Reg {ι : Type} (a : ι → Gf) : Prop :=
  ∀ (γ : GL (Fin 2) F) x i, (a i)⁻¹ * (x⁻¹ * D.j γ * x) ∈ D.H → γ.val.trace ≠ 0 ∧ γ.val.trace ^ 2 ≠ 4 * γ.val.det

open Classical in

def ee (x : Gf) : ℂ := if h : x ∈ D.H then D.χ ⟨x, h⟩ else 0

def Te {ι : Type} [Fintype ι] (a : ι → Gf) (γ : GL (Fin 2) F) (x : Gf) : ℂ := ∑ i, D.ee (x⁻¹ * (D.j γ)⁻¹ * x * a i)

def kt {ι : Type} [Fintype ι] (k : I → ℕ) (a : ι → Gf) (γ : GL (Fin 2) F) (z : X I) (x : Gf) : ℂ :=
  D.Te a γ x * (qq k z (D.act γ z) * D.J k γ z)

def kk {ι : Type} [Fintype ι] (k : I → ℕ) (a : ι → Gf) (γ : PG F) (y : D.Y) : ℂ := D.kt k a γ.out y.2 (D.rep y.1)

def Kern (k : I → ℕ) (y : D.Y) (p : X I × Gf) : ℂ :=
  ∑' γ : PG F, D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2) * (qq k p.1 (D.act γ.out y.2) * D.J k γ.out y.2)

def abelian₂ (T : ℝ) : Set D.Y := {y | ∀ s, s ≠ 0 → D.HtY s y ≤ T}

def LamF (T : ℝ) (γ : PG F) : Set D.Y := {y | ∀ s, s ≠ 0 → Fix s γ → D.HtY s y ≤ T}

def TotEll (γ : GL (Fin 2) F) : Prop := ∀ v, D.σ v γ.val.trace ^ 2 < 4 * D.σ v γ.val.det

def orb (k : I → ℕ) (γ : GL (Fin 2) F) : ℂ :=
  ∏ v, -((ch (D.σ v γ.val.trace) (D.σ v γ.val.det) (k v - 1) * D.σ v γ.val.det ^ (1 - (k v : ℝ) / 2) : ℝ) : ℂ)

structure Hyp {ι : Type} [Fintype ι] (k : I → ℕ) (a : ι → Gf) : Prop where
  ax : D.Ax
  four : ∀ v, 4 ≤ k v
  compat : D.Compat k
  good : D.Good a
  reg : D.Reg a

end Dat

def AllD (p : ∀ (F I Gf : Type) [Field F] [Group Gf] [Fintype I], Dat F I Gf → Prop) : Prop :=
  ∀ (F I Gf : Type) [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf), D.Ax → p F I Gf D

def AllH (p : ∀ (F I Gf ι : Type) [Field F] [Group Gf] [Fintype I] [Fintype ι], Dat F I Gf → (I → ℕ) → (ι → Gf) → Prop) : Prop :=
  ∀ (F I Gf ι : Type) [Field F] [Group Gf] [Fintype I] [Fintype ι] (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf), D.Hyp k a → p F I Gf ι D k a

def E0a : Prop := AllD fun F I _ _ _ _ D =>
  Countable (PG F) ∧ SigmaFinite (volume : Measure D.Xs) ∧ Pres (PG F) (volume : Measure D.Xs) ∧ Pres (PG F) D.μY ∧ Pres (PG F) D.μC ∧
    (∀ γ : PG F, Continuous fun z : D.Xs => γ • z) ∧ BorelSpace D.Xs ∧
    ∀ δ : ℝ, δ < 1 → ∃ c : ℝ≥0, 0 < c ∧ ∀ z : X I, MeasurableSet {w | Near δ z w} ∧ (c : ℝ≥0∞) ≤ volume {w : X I | Near δ z w}

def FormsStableUnderOperators : Prop := AllD fun _ _ Gf _ _ _ D => ∀ k, (∀ f, f ∈ D.M k ↔ D.IsForm k f) ∧
  ∀ (ι : Type) [Fintype ι] (a : ι → Gf), D.Good a → ∀ f ∈ D.M k, Dat.Op a f ∈ D.M k

def KernelTermsInvariantBounded : Prop := AllH fun F _ Gf _ _ _ _ _ D k a =>
  (∀ (γ : GL (Fin 2) F) (z : D.Xs) (x : Gf), D.kk k a γ ((x : Gf ⧸ D.H), z) = D.kt k a γ z x) ∧
  (∀ (δ γ : PG F) y, D.kk k a (δ * γ * δ⁻¹) (δ • y) = D.kk k a γ y) ∧ (∀ γ, Measurable (D.kk k a γ)) ∧
  (∃ C : ℝ, ∀ γ y, ‖D.kk k a γ y‖ ≤ C * Kap k y.2 (γ • y.2 : D.Xs)) ∧
  (∀ (γ : PG F) y, D.Te a γ.out (D.rep y) ≠ 0 → ∃ i, γ • y = ((D.rep y * a i : Gf) : Gf ⧸ D.H)) ∧
  ∀ (γ : PG F) y i, γ • y = ((D.rep y * a i : Gf) : Gf ⧸ D.H) → γ.out.val.trace ≠ 0 ∧ γ.out.val.trace ^ 2 ≠ 4 * γ.out.val.det

def E0d : Prop := AllD fun F _ Gf _ _ _ D =>
  (∀ s, s ≠ 0 → ∀ (z : D.Xs) (x : Gf), D.HtY s ((x : Gf ⧸ D.H), z) = D.Ht s z x) ∧
  (∀ s, s ≠ 0 → ∀ (γ : GL (Fin 2) F) y, D.HtY s ((γ : PG F) • y) = D.HtY (s ᵥ* γ.val) y) ∧
  (∀ s, s ≠ 0 → ∀ c : F, c ≠ 0 → D.HtY (c • s) = D.HtY s) ∧ (∀ s, s ≠ 0 → ∀ y, 0 < D.HtY s y) ∧
  (∀ s s' : Fin 2 → F, s 0 * s' 1 - s 1 * s' 0 ≠ 0 → ∀ y, D.HtY s y * D.HtY s' y ≤ 1) ∧ (∀ s, Measurable (D.HtY s)) ∧
  (∀ T, MeasurableSet (D.abelian₂ T) ∧ ∀ (δ : PG F) y, δ • y ∈ D.abelian₂ T ↔ y ∈ D.abelian₂ T) ∧
  (∀ T γ, MeasurableSet (D.LamF T γ) ∧ ∀ (δ : PG F) y, δ • y ∈ D.LamF T (δ * γ * δ⁻¹) ↔ y ∈ D.LamF T γ) ∧
  (∀ y, ∃ T₀, ∀ T, T₀ ≤ T → y ∈ D.abelian₂ T) ∧
  (∀ s : Fin 2 → F, s ≠ 0 → ∃ γ : GL (Fin 2) F, ![0, 1] ᵥ* γ.val = s) ∧
  ∀ (s : Fin 2 → F) (γ δ : GL (Fin 2) F), Fix s ((δ : PG F) * γ * (δ : PG F)⁻¹) ↔ ∃ c : F, (s ᵥ* δ.val) ᵥ* γ.val = c • (s ᵥ* δ.val)

def Mult : Prop := AllD fun F _ _ _ _ _ D => ∀ δ c₀ : ℝ, 0 < δ → 0 < c₀ → ∃ C : ℝ, ∀ (y : D.Y) s, s ≠ 0 → c₀ ≤ D.HtY s y →
  {γ : PG F | γ • y.1 = y.1 ∧ Near δ y.2 (γ • y.2 : D.Xs)}.Finite ∧
    ({γ : PG F | γ • y.1 = y.1 ∧ Near δ y.2 (γ • y.2 : D.Xs)}.ncard : ℝ) ≤ C * (1 + D.HtY s y)

def Pack : Prop := AllD fun F _ _ _ _ _ D => ∃ C : ℝ≥0, ∀ (y : D.Y) (ω' : D.Om) (h : D.Xs → ℝ≥0∞) (A : ℝ≥0), Measurable h →
  (∀ w w' : D.Xs, Near (1 / 2) w w' → h w ≤ A * h w') → {γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}.Finite →
  ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2) ≤
    C * A * ({γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}.ncard : ℝ≥0∞) * ∫⁻ w, h w

def KapInt : Prop := ∀ (I : Type) [Fintype I] (k : I → ℕ), (∀ v, 4 ≤ k v) → ∃ C A : ℝ≥0, ∀ z : X I,
  Measurable (Kap k z) ∧ ∫⁻ w, ENNReal.ofReal (Kap k z w) ≤ C ∧
  ∫⁻ w, ENNReal.ofReal (Kap k z w * ∏ v, (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)) ≤ C ∧
  ∀ w w', Near (1 / 2) w w' → Kap k z w ≤ A * Kap k z w' ∧
    Kap k z w * ∏ v, (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2) ≤ A * (Kap k z w' * ∏ v, (|(z v).1.im| / |(w' v).1.im|) ^ ((1 : ℝ) / 2))

def KapSum : Prop := AllD fun F I _ _ _ _ D => ∀ k : I → ℕ, (∀ v, 4 ≤ k v) → ∀ c₀ : ℝ, 0 < c₀ → ∃ C : ℝ, ∀ (y : D.Y) s, s ≠ 0 → c₀ ≤ D.HtY s y →
  ∀ (ω' : D.Om) (z : X I), ∑' γ : {γ : PG F // γ • y.1 = ω'}, ENNReal.ofReal (Kap k z (γ.1 • y.2 : D.Xs)) ≤ ENNReal.ofReal (C * (1 + D.HtY s y))

def E1 : Prop := AllH fun F _ _ _ _ _ _ _ D k a => ∀ c₀ : ℝ, 0 < c₀ → ∃ C : ℝ≥0, ∀ (y : D.Y) s, s ≠ 0 → c₀ ≤ D.HtY s y →
  ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a γ.1 y‖ₑ ≤ C

def E2 : Prop := AllH fun F _ _ _ _ _ _ _ D k a => (∀ y, Summable fun γ : PG F => ‖D.kk k a γ y‖) ∧
  ∀ T : ℝ, ∃ C : ℝ≥0, ∀ y ∈ D.abelian₂ T, ∑' γ : PG F, ‖D.kk k a γ y‖ₑ ≤ C

def Ecut : Prop := AllD fun F _ _ _ _ _ D => (∃ b : D.Y → ℝ, IsCut (PG F) b) ∧
  ∀ (ω : D.Om) (S : Subgroup (PG F)), S ≤ MulAction.stabilizer (PG F) ω → ∃ b : D.Xs → ℝ, IsCut S b

def E3 : Prop := AllD fun F _ _ _ _ _ D => ∀ b : D.Y → ℝ, IsCut (PG F) b → ∫⁻ y, ENNReal.ofReal (b y) ∂D.μY < ⊤

def E4 : Prop := AllD fun _ I _ _ _ _ D => ∀ k : I → ℕ, (∀ v, 4 ≤ k v) → D.Compat k → ∀ y, D.IsForm k (D.Kern k y)

def faceMap_zero_comp_eq_one : Prop := AllD fun F I _ _ _ _ D => ∀ k : I → ℕ, (∀ v, 4 ≤ k v) → D.Compat k → ∀ p,
  (∀ y : D.Y, Summable fun γ : PG F => ‖D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * p.2) * (qq k p.1 (D.act γ.out y.2) * D.J k γ.out y.2)‖) ∧
  Measurable (fun y => D.Kern k y p) ∧ ∃ C, ∀ y, ‖D.Kern k y p‖ ≤ C * nrm k y.2

def MultivariableReproducingFormula : Prop := ∀ (I : Type) [Fintype I] (k : I → ℕ), (∀ v, 4 ≤ k v) → ∀ f : X I → ℂ, SepHol f → (∃ C, ∀ z, ‖f z‖ * nrm k z ≤ C) → ∀ z,
  Integrable (fun w => qq k z w * f w) ∧ ∫ w, qq k z w * f w = f z

def E5 : Prop := AllD fun F I _ _ _ _ D => ∀ k : I → ℕ, (∀ v, 4 ≤ k v) → D.Compat k → ∀ b : D.Y → ℝ, IsCut (PG F) b →
  ∀ f, D.IsForm k f → ∀ p, ∫ y, b y • (D.Kern k y p * f (y.2, D.rep y.1)) ∂D.μY = f p

def E6 : Prop := AllH fun F _ _ _ _ _ _ _ D k a => FiniteDimensional ℂ (D.M k) → ∀ h : ∀ f ∈ D.M k, Dat.Op a f ∈ D.M k,
  ∀ b : D.Y → ℝ, IsCut (PG F) b → Integrable (fun y => b y • ∑' γ : PG F, D.kk k a γ y) D.μY ∧
    LinearMap.trace ℂ (D.M k) ((Dat.Op a).restrict h) = ∫ y, b y • ∑' γ : PG F, D.kk k a γ y ∂D.μY

def Fsum : Prop := AllD fun F _ _ _ _ _ D => ∀ b : D.Y → ℝ, IsCut (PG F) b →
  IsCut (PG F) (fun p : (D.Cj × D.Om) × D.Xs => b (p.1.2, p.2)) ∧
  ∀ u : PG F → D.Y → ℂ, (∀ γ, Measurable (u γ)) → ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY < ⊤ →
    Measurable (fun p : (D.Cj × D.Om) × D.Xs => u (D.el p.1.1) (p.1.2, p.2)) ∧
    Integrable (fun p : (D.Cj × D.Om) × D.Xs => b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2)) D.μC ∧
    Integrable (fun y => b y • ∑' γ, u γ y) D.μY ∧
    ∫ y, b y • ∑' γ, u γ y ∂D.μY = ∫ p, b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2) ∂D.μC

def Fcen : Prop := ∀ (F : Type) [Field F] (γ δ : GL (Fin 2) F), γ.val.trace ≠ 0 → (δ : PG F) * γ * (δ : PG F)⁻¹ = γ → δ * γ = γ * δ

def F2 : Prop := AllH fun F _ _ _ _ _ _ _ D k a => ∀ (γ : PG F) (ω : D.Om), ¬ D.TotEll γ.out →
  ∀ β : D.Xs → ℝ, IsCut (MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)) β → Integrable (fun z => β z • D.kk k a γ (ω, z)) →
    ∫ z, β z • D.kk k a γ (ω, z) = 0

def F3 : Prop := AllH fun F _ _ _ _ _ _ _ D k a => ∀ (γ : PG F) (ω : D.Om), D.TotEll γ.out → D.Te a γ.out (D.rep ω) ≠ 0 →
  Finite (MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)) ∧
  ∀ β : D.Xs → ℝ, IsCut (MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)) β →
    ∫ z, β z • D.kk k a γ (ω, z) =
      (Nat.card (MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)) : ℂ)⁻¹ * (D.Te a γ.out (D.rep ω) * D.orb k γ.out)

def F4 : Prop := AllD fun F _ Gf _ _ _ D => ∀ a : Gf, ∃ S : Set (D.Cj × D.Om), S.Finite ∧ ∀ (γ : PG F) (ω : D.Om), D.TotEll γ.out →
  γ • ω = ((D.rep ω * a : Gf) : Gf ⧸ D.H) → ∃ δ : PG F, δ • ((γ, ω) : D.Cj × D.Om) ∈ S

def ConstantTermVanishingAlt : Prop := ∀ (I : Type) [Fintype I] [Nontrivial I] (φ : I → ℝ → ℂ), (∀ v, Continuous (φ v) ∧ Integrable (φ v) ∧
    Integrable (fun x => (Real.log (1 + x ^ 2) : ℂ) * φ v x) ∧ ∫ x, φ v x = 0 ∧ ∀ x, φ v x ≠ 0) →
  ∀ β : X I → ℝ, Measurable β → (∀ z, 0 ≤ β z) →
  (∀ (x x' y : I → ℝ) (hy : ∀ v, y v ≠ 0) (t : ℝ) (ht : 0 < t),
    β (fun v => pt (x v) (y v) (hy v)) = β fun v => pt (x' v) (t * y v) (mul_ne_zero ht.ne' (hy v))) →
  ∀ A B : ℝ, 0 < A → A < B → ∀ u : X I → ℂ,
  (∀ (x y : I → ℝ) (hy : ∀ v, y v ≠ 0), u (fun v => pt (x v) (y v) (hy v)) =
    if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |y v| ∧ ∏ v, |y v| ≤ B then ∏ v, φ v (x v) else 0) →
  Integrable (fun z => β z • u z) → ∫ z, β z • u z = 0

def DiagonalTruncatedIntegralZero : Prop := AllH fun F _ _ _ _ _ _ _ D k a => ∀ T : ℝ, 1 < T → ∀ (γ : GL (Fin 2) F) (ω : D.Om), γ 0 1 = 0 → γ 1 0 = 0 →
  ∀ β : D.Xs → ℝ, IsCut (MulAction.stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om)) β →
    Integrable (fun z => β z • (D.LamF T γ).indicator (D.kk k a γ) (ω, z)) → ∫ z, β z • (D.LamF T γ).indicator (D.kk k a γ) (ω, z) = 0

def F6 : Prop := AllH fun F _ _ _ _ _ _ _ D k a => ∀ T : ℝ, 1 < T → ∀ (γ : PG F) (ω : D.Om), ¬ IsEll γ →
  ∀ β : D.Xs → ℝ, IsCut (MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)) β →
    Integrable (fun z => β z • (D.LamF T γ).indicator (D.kk k a γ) (ω, z)) → ∫ z, β z • (D.LamF T γ).indicator (D.kk k a γ) (ω, z) = 0

open Classical in

def F5 : Prop := AllH fun F _ _ _ _ _ _ _ D k a => ∃ C : ℝ≥0, ∀ T : ℝ, 1 < T → ∀ y,
  (y ∈ D.abelian₂ T → ∀ γ, y ∈ D.LamF T γ) ∧ (y ∉ D.abelian₂ T → ∑' γ : PG F, ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ ≤ C)

open Classical in

def Fhyp : Prop := AllH fun F _ _ _ _ _ _ _ D k a => ∀ b : D.Y → ℝ, IsCut (PG F) b →
  Integrable (fun y => b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) D.μY →
    ∫ y, b y • (∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) ∂D.μY = 0

def Fam {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (S : Finset (D.Cj × D.Om)) : Prop :=
  ∀ p ∈ S, D.TotEll ((D.el p.1).out) ∧ Finite (MulAction.stabilizer (PG F) p)

def geo {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι] (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (S : Finset (D.Cj × D.Om)) : ℂ :=
  ∑ p ∈ S, (Nat.card (MulAction.stabilizer (PG F) p) : ℂ)⁻¹ *
    (D.Te a ((D.el p.1).out) (D.rep p.2) * D.orb k ((D.el p.1).out))

open Classical in

def Fell : Prop := AllD fun F I Gf _ _ _ D => ∀ (ι : Type) [Fintype ι] (a : ι → Gf), ∃ S : Finset (D.Cj × D.Om), Fam D S ∧
  ∀ k : I → ℕ, D.Hyp k a → ∀ b : D.Y → ℝ, IsCut (PG F) b →
    Integrable (fun y => b y • ∑' γ : PG F, if IsEll γ then D.kk k a γ y else 0) D.μY ∧
    ∫ y, b y • (∑' γ : PG F, if IsEll γ then D.kk k a γ y else 0) ∂D.μY = geo D k a S

def TF : Prop := AllD fun _ I Gf _ _ _ D => ∀ (ι : Type) [Fintype ι] (a : ι → Gf), ∃ S : Finset (D.Cj × D.Om), Fam D S ∧
  ∀ k : I → ℕ, D.Hyp k a → FiniteDimensional ℂ (D.M k) → ∀ h : ∀ f ∈ D.M k, Dat.Op a f ∈ D.M k,
    LinearMap.trace ℂ (D.M k) ((Dat.Op a).restrict h) = geo D k a S

end UpperTheory.Esk
