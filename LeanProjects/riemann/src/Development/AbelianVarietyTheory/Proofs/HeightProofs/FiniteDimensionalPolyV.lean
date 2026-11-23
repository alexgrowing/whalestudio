import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory Matrix Formalism.REAL

variable {n : ℕ}

def coord (ε : Fin n → Bool) (c : Fin n × Fin n × Bool) (k : KG ε) : ℂ :=
  if c.2.2 then toMK k c.1 c.2.1 else star (toMK k c.1 c.2.1)

def polyV (ε : Fin n → Bool) (d : ℕ) : Submodule ℂ (KG ε → ℂ) :=
  Submodule.span ℂ {φ | ∃ s : List (Fin n × Fin n × Bool), s.length ≤ d ∧
    φ = fun k => (s.map fun c => coord ε c k).prod}

def lowV (ε : Fin n → Bool) : ℕ → Submodule ℂ (KG ε → ℂ)
  | 0 => ⊥
  | i + 1 => polyV ε i

def IsKer (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ) : Prop :=
  e ∈ polyV ε i ∧ (∀ q ∈ lowV ε i, ∫ k, e k * q k ∂(muK ε) = 0) ∧
    ∀ p ∈ polyV ε i, (∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0) → ∫ k, e k * p k ∂(muK ε) = p 1

open Classical in

def kerE (ε : Fin n → Bool) (i : ℕ) : KG ε → ℂ :=
  if h : ∃ e, IsKer ε i e then h.choose else 0

theorem isKer_kerE {ε : Fin n → Bool} {i : ℕ} (h : ∃ e, IsKer ε i e) : IsKer ε i (kerE ε i) := by
  unfold kerE
  rw [dif_pos h]
  exact h.choose_spec

def rder (ε : Fin n → Bool) (l : List (Matrix (Fin n) (Fin n) ℂ)) (φ : KG ε → ℂ) : KG ε → ℂ :=
  l.foldr (fun X ψ => fun k => deriv (fun t : ℝ => ψ (k * expK ε X t)) 0) φ

@[simp] theorem rder_nil (ε : Fin n → Bool) (φ : KG ε → ℂ) : rder ε [] φ = φ := rfl

theorem rder_cons (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (φ : KG ε → ℂ) (k : KG ε) :
    rder ε (X :: l) φ k = deriv (fun t : ℝ => rder ε l φ (k * expK ε X t)) 0 := rfl

theorem rder_left (ε : Fin n → Bool) (l : List (Matrix (Fin n) (Fin n) ℂ)) (φ : KG ε → ℂ) (a k : KG ε) :
    rder ε l (fun x => φ (a * x)) k = rder ε l φ (a * k) := by
  induction l generalizing k with
  | nil => rfl
  | cons X l ih =>
    rw [rder_cons, rder_cons]
    congr 1
    funext t
    rw [ih, mul_assoc]

def avgK (ε : Fin n → Bool) (e : KG ε → ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (y : Matrix (Fin n) (Fin n) ℂ) :
    KG ε → ℂ :=
  fun k' => ∫ k, e k * f (y * toMK k' * toMK k) ∂(muK ε)

theorem toMK_mul (ε : Fin n → Bool) (a b : KG ε) : toMK (a * b) = toMK a * toMK b := rfl

theorem toMK_one (ε : Fin n → Bool) : toMK (1 : KG ε) = 1 := rfl

theorem toMK_expK {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inK ε X) (t : ℝ) :
    toMK (expK ε X t) = NormedSpace.exp ((t : ℂ) • X) := by
  unfold expK
  rw [dif_pos h]
  exact toM_expG ε X t h.1

theorem inK_of_skew {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h1 : X ∈ GlobalTheory.SmoothGlob.lieSet ε)
    (h2 : Xᴴ = -X) : inK ε X := by
  refine ⟨h1, ?_⟩
  have h3 : Xᴴ * Jm ε + Jm ε * X = 0 := h1
  rw [h2, neg_mul] at h3
  exact neg_add_eq_zero.1 h3

end GlobalTheory.KFourier

namespace GlobalTheory.KFourier

open MeasureTheory Matrix Formalism.REAL

variable {n : ℕ}

def mono (ε : Fin n → Bool) (s : List (Fin n × Fin n × Bool)) : KG ε → ℂ :=
  fun k => (s.map fun c => coord ε c k).prod

theorem mono_mem {ε : Fin n → Bool} {d : ℕ} {s : List (Fin n × Fin n × Bool)} (h : s.length ≤ d) :
    mono ε s ∈ polyV ε d := Submodule.subset_span ⟨s, h, rfl⟩

theorem polyV_mono (ε : Fin n → Bool) {d d' : ℕ} (h : d ≤ d') : polyV ε d ≤ polyV ε d' := Submodule.span_mono (fun _ ⟨s, hs, e⟩ => ⟨s, hs.trans h, e⟩)

theorem mono_append (ε : Fin n → Bool) (s s' : List (Fin n × Fin n × Bool)) :
    mono ε (s ++ s') = mono ε s * mono ε s' := by
  funext k
  simp only [mono, List.map_append, List.prod_append, Pi.mul_apply]

theorem polyV_eq (ε : Fin n → Bool) (d : ℕ) :
    polyV ε d = Submodule.span ℂ {φ | ∃ s : List (Fin n × Fin n × Bool), s.length ≤ d ∧ φ = mono ε s} := rfl

theorem continuous_coord (ε : Fin n → Bool) (c : Fin n × Fin n × Bool) : Continuous (coord ε c) := by
  have hK : Continuous (fun k : KG ε => toMK k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have he : Continuous (fun k : KG ε => toMK k c.1 c.2.1) :=
    (continuous_apply c.2.1).comp ((continuous_apply c.1).comp hK)
  rcases c with ⟨i, j, b⟩
  cases b
  · exact he.star
  · exact he

theorem continuous_mono (ε : Fin n → Bool) (s : List (Fin n × Fin n × Bool)) : Continuous (mono ε s) := by
  unfold mono
  exact continuous_list_prod s (fun c _ => continuous_coord ε c)

theorem continuous_of_mem {ε : Fin n → Bool} {d : ℕ} {φ : KG ε → ℂ} (h : φ ∈ polyV ε d) : Continuous φ := by
  let S : Submodule ℂ (KG ε → ℂ) :=
    { carrier := {f | Continuous f}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := continuous_zero
      smul_mem' := fun c _ hf => hf.const_smul c }
  have hle : polyV ε d ≤ S := by
    rw [polyV_eq, Submodule.span_le]
    rintro _ ⟨s, _, rfl⟩
    exact continuous_mono ε s
  exact hle h

theorem finite_gen (ε : Fin n → Bool) (d : ℕ) :
    {φ : KG ε → ℂ | ∃ s : List (Fin n × Fin n × Bool), s.length ≤ d ∧ φ = fun k => (s.map fun c => coord ε c k).prod}.Finite := by
  refine ((List.finite_length_le (Fin n × Fin n × Bool) d).image (mono ε)).subset ?_
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨s, hs, rfl⟩

instance finiteDimensional_polyV (ε : Fin n → Bool) (d : ℕ) : FiniteDimensional ℂ (polyV ε d) :=
  FiniteDimensional.span_of_finite ℂ (finite_gen ε d)

theorem mul_mem {ε : Fin n → Bool} {a b : ℕ} {φ ψ : KG ε → ℂ} (hφ : φ ∈ polyV ε a) (hψ : ψ ∈ polyV ε b) :
    φ * ψ ∈ polyV ε (a + b) := by
  have key : polyV ε a * polyV ε b ≤ polyV ε (a + b) := by
    rw [polyV_eq, polyV_eq, polyV_eq, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨x, ⟨s, hs, rfl⟩, y, ⟨t, ht, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨s ++ t, by rw [List.length_append]; omega, (mono_append ε s t).symm⟩
  exact key (Submodule.mul_mem_mul hφ hψ)

theorem const_mem (ε : Fin n → Bool) (d : ℕ) (c : ℂ) : (fun _ : KG ε => c) ∈ polyV ε d := by
  have e : (fun _ : KG ε => c) = c • mono ε [] := by
    funext k
    simp [mono]
  rw [e]
  exact Submodule.smul_mem _ c (mono_mem (by simp))

theorem coord_mem (ε : Fin n → Bool) (c : Fin n × Fin n × Bool) : coord ε c ∈ polyV ε 1 := by
  have e : coord ε c = mono ε [c] := by
    funext k
    simp [mono]
  rw [e]
  exact mono_mem (by simp)

private theorem mono_comp_mem_polyV_of_coord_mem {ε : Fin n → Bool} (T : KG ε → KG ε)
    (hT : ∀ c, (fun k => coord ε c (T k)) ∈ polyV ε 1) (s : List (Fin n × Fin n × Bool)) :
    (fun k => mono ε s (T k)) ∈ polyV ε s.length := by
  induction s with
  | nil => simpa [mono] using GlobalTheory.KFourier.const_mem ε 0 1
  | cons c s ih =>
    have h := GlobalTheory.KFourier.mul_mem (hT c) ih
    have e : (fun k => mono ε (c :: s) (T k)) = (fun k => coord ε c (T k)) * (fun k => mono ε s (T k)) := by
      funext k
      simp [mono]
    rw [e, List.length_cons, Nat.add_comm]
    exact h

theorem comp_mem {ε : Fin n → Bool} (T : KG ε → KG ε) (hT : ∀ c, (fun k => coord ε c (T k)) ∈ polyV ε 1)
    {d : ℕ} {φ : KG ε → ℂ} (h : φ ∈ polyV ε d) : (fun k => φ (T k)) ∈ polyV ε d := by
  have hle : polyV ε d ≤ (polyV ε d).comap (LinearMap.funLeft ℂ ℂ T) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, rfl⟩
    exact polyV_mono ε hs (mono_comp_mem_polyV_of_coord_mem T hT s)
  exact hle h

theorem coord_mul_right_mem (ε : Fin n → Bool) (a : KG ε) (c : Fin n × Fin n × Bool) :
    (fun k => coord ε c (k * a)) ∈ polyV ε 1 := by
  rcases c with ⟨i, j, b⟩
  cases b
  · have e : (fun k => coord ε (i, j, false) (k * a)) = ∑ l, star (toMK a l j) • coord ε (i, l, false) := by
      funext k
      simp only [coord, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toMK_mul, Matrix.mul_apply, star_sum,
        star_mul', Bool.false_eq_true, if_false, ↓reduceIte]
      all_goals (refine Finset.sum_congr rfl (fun l _ => ?_); ring)
    rw [e]
    exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (coord_mem ε _))
  · have e : (fun k => coord ε (i, j, true) (k * a)) = ∑ l, toMK a l j • coord ε (i, l, true) := by
      funext k
      simp only [coord, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toMK_mul, Matrix.mul_apply,
        if_true, ↓reduceIte]
      all_goals (refine Finset.sum_congr rfl (fun l _ => ?_); ring)
    rw [e]
    exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (coord_mem ε _))

theorem coord_mul_left_mem (ε : Fin n → Bool) (a : KG ε) (c : Fin n × Fin n × Bool) :
    (fun k => coord ε c (a * k)) ∈ polyV ε 1 := by
  rcases c with ⟨i, j, b⟩
  cases b
  · have e : (fun k => coord ε (i, j, false) (a * k)) = ∑ l, star (toMK a i l) • coord ε (l, j, false) := by
      funext k
      simp only [coord, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toMK_mul, Matrix.mul_apply, star_sum,
        star_mul', Bool.false_eq_true, if_false, ↓reduceIte]
      all_goals (refine Finset.sum_congr rfl (fun l _ => ?_); ring)
    rw [e]
    exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (coord_mem ε _))
  · have e : (fun k => coord ε (i, j, true) (a * k)) = ∑ l, toMK a i l • coord ε (l, j, true) := by
      funext k
      simp only [coord, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toMK_mul, Matrix.mul_apply,
        if_true, ↓reduceIte]
      all_goals (refine Finset.sum_congr rfl (fun l _ => ?_); ring)
    rw [e]
    exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (coord_mem ε _))

theorem mul_right_mem {ε : Fin n → Bool} (a : KG ε) {d : ℕ} {φ : KG ε → ℂ} (h : φ ∈ polyV ε d) :
    (fun k => φ (k * a)) ∈ polyV ε d := GlobalTheory.KFourier.comp_mem (fun k => k * a) (fun c => coord_mul_right_mem ε a c) h

theorem mul_left_mem {ε : Fin n → Bool} (a : KG ε) {d : ℕ} {φ : KG ε → ℂ} (h : φ ∈ polyV ε d) :
    (fun k => φ (a * k)) ∈ polyV ε d := GlobalTheory.KFourier.comp_mem (fun k => a * k) (fun c => coord_mul_left_mem ε a c) h

def flipC (c : Fin n × Fin n × Bool) : Fin n × Fin n × Bool := (c.1, c.2.1, !c.2.2)

theorem star_coord (ε : Fin n → Bool) (c : Fin n × Fin n × Bool) (k : KG ε) :
    star (coord ε c k) = coord ε (flipC c) k := by
  rcases c with ⟨i, j, b⟩
  cases b <;> simp [coord, flipC]

theorem star_mono (ε : Fin n → Bool) (s : List (Fin n × Fin n × Bool)) (k : KG ε) :
    star (mono ε s k) = mono ε (s.map flipC) k := by
  induction s with
  | nil => simp [mono]
  | cons c s ih =>
    simp only [mono, List.map_cons, List.prod_cons, star_mul'] at ih ⊢
    rw [ih, star_coord]

theorem star_mem {ε : Fin n → Bool} {d : ℕ} {φ : KG ε → ℂ} (h : φ ∈ polyV ε d) :
    (fun k => star (φ k)) ∈ polyV ε d := by
  rw [polyV_eq] at h
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    show (fun k => star (mono ε s k)) ∈ polyV ε d
    have e : (fun k => star (mono ε s k)) = mono ε (s.map flipC) := funext (star_mono ε s)
    rw [e]
    exact mono_mem (by simpa using hs)
  | zero =>
    have e : (fun k => star ((0 : KG ε → ℂ) k)) = 0 := by
      funext k
      simp
    rw [e]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have e : (fun k => star ((x + y) k)) = (fun k => star (x k)) + (fun k => star (y k)) := by
      funext k
      simp
    rw [e]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have e : (fun k => star ((c • x) k)) = star c • (fun k => star (x k)) := by
      funext k
      simp [star_mul']
    rw [e]
    exact Submodule.smul_mem _ _ hx

theorem toMK_inv (ε : Fin n → Bool) (k : KG ε) : toMK k⁻¹ = star (toMK k) := by
  have hk : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ := ((Formalism.REAL.mem_KG ε k.1).1 k.2).1
  have h1 : toMK k * star (toMK k) = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  have h2 : toMK k⁻¹ * toMK k = 1 := by rw [← toMK_mul, inv_mul_cancel, toMK_one]
  calc toMK k⁻¹ = toMK k⁻¹ * (toMK k * star (toMK k)) := by rw [h1, mul_one]
    _ = star (toMK k) := by rw [← mul_assoc, h2, one_mul]

theorem coord_inv_mem (ε : Fin n → Bool) (c : Fin n × Fin n × Bool) :
    (fun k : KG ε => coord ε c k⁻¹) ∈ polyV ε 1 := by
  rcases c with ⟨i, j, b⟩
  have e : (fun k : KG ε => coord ε (i, j, b) k⁻¹) = coord ε (j, i, !b) := by
    funext k
    cases b <;> simp only [coord, toMK_inv, Matrix.star_apply, star_star, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ↓reduceIte]
  rw [e]
  exact coord_mem ε _

theorem inv_mem {ε : Fin n → Bool} {d : ℕ} {φ : KG ε → ℂ} (h : φ ∈ polyV ε d) :
    (fun k => φ k⁻¹) ∈ polyV ε d := GlobalTheory.KFourier.comp_mem (fun k => k⁻¹) (fun c => coord_inv_mem ε c) h

theorem kFinFun_of_mem {ε : Fin n → Bool} {d : ℕ} {φ : KG ε → ℂ} (h : φ ∈ polyV ε d) :
    GlobalTheory.TypeSum.KFinFun ε φ := by
  unfold GlobalTheory.TypeSum.KFinFun
  exact ⟨polyV ε d, inferInstance, h, fun ψ hψ => continuous_of_mem hψ,
    fun ψ hψ k₀ => ⟨GlobalTheory.KFourier.mul_left_mem k₀ hψ, GlobalTheory.KFourier.mul_right_mem k₀ hψ⟩⟩

end GlobalTheory.KFourier

end
