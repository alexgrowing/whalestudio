import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalDet

noncomputable section

namespace PI.UnitaryGroupMassFormula.PolyCoef

open MeasureTheory Matrix

abbrev UG (N : ℕ) := ↥(Matrix.unitaryGroup (Fin N) ℂ)

lemma isCompact_UG (N : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) := by
  have hc : IsClosed ((Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) := by
    have : ((Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) =
        {g | star g * g = 1} ∩ {g | g * star g = 1} := by
      ext g; exact Unitary.mem_iff
    rw [this]
    exact (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_star) continuous_const)
  have hb : IsCompact (Set.pi Set.univ fun _ : Fin N =>
      Set.pi Set.univ fun _ : Fin N => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hb.of_isClosed_subset hc ?_
  intro g hg i _ j _
  simpa using entry_norm_bound_of_unitary hg i j

instance instCompactUG (N : ℕ) : CompactSpace (UG N) :=
  isCompact_iff_compactSpace.mp (isCompact_UG N)

instance instMeasUG (N : ℕ) : MeasurableSpace (UG N) := borel _

instance instBorelUG (N : ℕ) : BorelSpace (UG N) := ⟨rfl⟩

def ent {N : ℕ} (g : UG N) : Fin N × Fin N → ℂ := fun ij => (g : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2

def IsPD {N : ℕ} (f : UG N → ℂ) : Prop :=
  ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ),
    ∀ g : UG N, f g * (g : Matrix (Fin N) (Fin N) ℂ).det ^ k = MvPolynomial.eval (ent g) P

def detP (N : ℕ) : MvPolynomial (Fin N × Fin N) ℂ := (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).det

lemma mapX_eval {N : ℕ} (g : UG N) :
    (MvPolynomial.eval (ent g)).mapMatrix (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ) =
      (g : Matrix (Fin N) (Fin N) ℂ) :=
  Matrix.mvPolynomialX_mapMatrix_eval (g : Matrix (Fin N) (Fin N) ℂ)

lemma eval_detP {N : ℕ} (g : UG N) :
    MvPolynomial.eval (ent g) (detP N) = (g : Matrix (Fin N) (Fin N) ℂ).det := by
  unfold detP
  rw [RingHom.map_det, mapX_eval]

lemma IsPD.const {N : ℕ} (c : ℂ) : IsPD (fun _ : UG N => c) :=
  ⟨0, MvPolynomial.C c, fun g => by simp⟩

lemma IsPD.add {N : ℕ} {f f' : UG N → ℂ} (hf : IsPD f) (hf' : IsPD f') : IsPD (fun g => f g + f' g) := by
  obtain ⟨k, P, hP⟩ := hf
  obtain ⟨k', P', hP'⟩ := hf'
  refine ⟨k + k', P * detP N ^ k' + P' * detP N ^ k, fun g => ?_⟩
  simp only [map_add, map_mul, map_pow, eval_detP, ← hP g, ← hP' g]
  ring

lemma IsPD.mul {N : ℕ} {f f' : UG N → ℂ} (hf : IsPD f) (hf' : IsPD f') : IsPD (fun g => f g * f' g) := by
  obtain ⟨k, P, hP⟩ := hf
  obtain ⟨k', P', hP'⟩ := hf'
  refine ⟨k + k', P * P', fun g => ?_⟩
  simp only [map_mul, ← hP g, ← hP' g]
  ring

lemma IsPD.sum {N : ℕ} {ι : Type*} (s : Finset ι) {F : ι → UG N → ℂ} (hF : ∀ i ∈ s, IsPD (F i)) :
    IsPD (fun g => ∑ i ∈ s, F i g) := by
  first | exact UpperTheory.Reformulated.B.Qi25.sum .. | (apply UpperTheory.Reformulated.B.Qi25.sum <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qi25.sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi25.sum <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qi25.sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi25.sum <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qi25.sum N ι s F hF | exact @UpperTheory.Reformulated.B.Qi25.sum N ι s F | exact @UpperTheory.Reformulated.B.Qi25.sum N ι s | exact @UpperTheory.Reformulated.B.Qi25.sum N ι | exact @UpperTheory.Reformulated.B.Qi25.sum N

lemma IsPD.entry {N : ℕ} (i j : Fin N) : IsPD (fun g : UG N => (g : Matrix (Fin N) (Fin N) ℂ) i j) :=
  ⟨0, MvPolynomial.X (i, j), fun g => by simp [ent]⟩

lemma adjugate_eq {N : ℕ} (g : UG N) :
    (g : Matrix (Fin N) (Fin N) ℂ).adjugate =
      (g : Matrix (Fin N) (Fin N) ℂ).det • star (g : Matrix (Fin N) (Fin N) ℂ) := by
  have h1 : star (g : Matrix (Fin N) (Fin N) ℂ) * (g : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_star_mul_self g
  calc (g : Matrix (Fin N) (Fin N) ℂ).adjugate
      = (star (g : Matrix (Fin N) (Fin N) ℂ) * (g : Matrix (Fin N) (Fin N) ℂ)) *
          (g : Matrix (Fin N) (Fin N) ℂ).adjugate := by rw [h1, Matrix.one_mul]
    _ = star (g : Matrix (Fin N) (Fin N) ℂ) * ((g : Matrix (Fin N) (Fin N) ℂ) *
          (g : Matrix (Fin N) (Fin N) ℂ).adjugate) := by rw [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]

lemma IsPD.conjEntry {N : ℕ} (i j : Fin N) :
    IsPD (fun g : UG N => star ((g : Matrix (Fin N) (Fin N) ℂ) i j)) := by
  refine ⟨1, (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).adjugate j i, fun g => ?_⟩
  have h : MvPolynomial.eval (ent g) ((Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).adjugate j i) =
      ((MvPolynomial.eval (ent g)).mapMatrix (Matrix.mvPolynomialX (Fin N) (Fin N) ℂ).adjugate) j i := rfl
  rw [h, RingHom.map_adjugate, mapX_eval, adjugate_eq]
  show star ((g : Matrix (Fin N) (Fin N) ℂ) i j) * (g : Matrix (Fin N) (Fin N) ℂ).det ^ 1 = _
  simp [Matrix.star_apply, mul_comm]

def coordC {N : ℕ} (i j : Fin N) : C(UG N, ℂ) :=
  ⟨fun g => (g : Matrix (Fin N) (Fin N) ℂ) i j,
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)⟩

def algA (N : ℕ) : StarSubalgebra ℂ C(UG N, ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range fun ij : Fin N × Fin N => coordC ij.1 ij.2)

lemma algA_dense (N : ℕ) (F : C(UG N, ℂ)) {ε : ℝ} (hε : 0 < ε) : ∃ f ∈ algA N, ‖F - f‖ < ε := by
  have hsep : (algA N).SeparatesPoints := by
    intro x y hxy
    have hne : (x : Matrix (Fin N) (Fin N) ℂ) ≠ y := fun h => hxy (Subtype.ext h)
    obtain ⟨i, j, hij⟩ : ∃ i j, (x : Matrix (Fin N) (Fin N) ℂ) i j ≠ (y : Matrix (Fin N) (Fin N) ℂ) i j := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hne (Matrix.ext hcon)
    refine ⟨coordC i j, ⟨coordC i j, StarAlgebra.subset_adjoin ℂ _ ⟨(i, j), rfl⟩, rfl⟩, hij⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (algA N) hsep
  have hF : F ∈ closure ((algA N : Set C(UG N, ℂ))) := by
    rw [← StarSubalgebra.topologicalClosure_coe, htop]; trivial
  obtain ⟨f, hf, hd⟩ := Metric.mem_closure_iff.mp hF ε hε
  exact ⟨f, hf, by rwa [dist_eq_norm] at hd⟩

def Sep {N : ℕ} (f : UG N → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a b : ι → UG N → ℂ), (∀ i, IsPD (a i)) ∧ (∀ i, Continuous (b i)) ∧
    ∀ h y : UG N, f (h⁻¹ * y) = ∑ i, a i h * b i y

lemma Sep.const {N : ℕ} (c : ℂ) : Sep (fun _ : UG N => c) :=
  ⟨Unit, inferInstance, fun _ _ => c, fun _ _ => 1, fun _ => IsPD.const c, fun _ => continuous_const,
    fun h y => by simp⟩

lemma Sep.add {N : ℕ} {f f' : UG N → ℂ} (hf : Sep f) (hf' : Sep f') : Sep (fun g => f g + f' g) := by
  obtain ⟨ι, _, a, b, ha, hb, he⟩ := hf
  obtain ⟨ι', _, a', b', ha', hb', he'⟩ := hf'
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim a a', Sum.elim b b', ?_, ?_, fun h y => ?_⟩
  · rintro (i | i); exacts [ha i, ha' i]
  · rintro (i | i); exacts [hb i, hb' i]
  · simp [Fintype.sum_sum_type, he, he']

lemma Sep.mul {N : ℕ} {f f' : UG N → ℂ} (hf : Sep f) (hf' : Sep f') : Sep (fun g => f g * f' g) := by
  obtain ⟨ι, _, a, b, ha, hb, he⟩ := hf
  obtain ⟨ι', _, a', b', ha', hb', he'⟩ := hf'
  refine ⟨ι × ι', inferInstance, fun p g => a p.1 g * a' p.2 g, fun p g => b p.1 g * b' p.2 g,
    fun p => (ha p.1).mul (ha' p.2), fun p => (hb p.1).mul (hb' p.2), fun h y => ?_⟩
  show f (h⁻¹ * y) * f' (h⁻¹ * y) = ∑ p : ι × ι', (a p.1 h * a' p.2 h) * (b p.1 y * b' p.2 y)
  rw [he, he', Fintype.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma Sep.coord {N : ℕ} (i j : Fin N) : Sep (fun g : UG N => (g : Matrix (Fin N) (Fin N) ℂ) i j) := by
  refine ⟨Fin N, inferInstance, fun k h => star ((h : Matrix (Fin N) (Fin N) ℂ) k i),
    fun k y => (y : Matrix (Fin N) (Fin N) ℂ) k j, fun k => IsPD.conjEntry k i,
    fun k => (coordC k j).continuous, fun h y => ?_⟩
  show (star (h : Matrix (Fin N) (Fin N) ℂ) * (y : Matrix (Fin N) (Fin N) ℂ)) i j = _
  rw [Matrix.mul_apply]
  simp [Matrix.star_apply]

lemma Sep.conjCoord {N : ℕ} (i j : Fin N) :
    Sep (fun g : UG N => star ((g : Matrix (Fin N) (Fin N) ℂ) i j)) := by
  refine ⟨Fin N, inferInstance, fun k h => (h : Matrix (Fin N) (Fin N) ℂ) k i,
    fun k y => star ((y : Matrix (Fin N) (Fin N) ℂ) k j), fun k => IsPD.entry k i,
    fun k => (coordC k j).continuous.star, fun h y => ?_⟩
  show star ((star (h : Matrix (Fin N) (Fin N) ℂ) * (y : Matrix (Fin N) (Fin N) ℂ)) i j) = _
  rw [Matrix.mul_apply]
  simp [Matrix.star_apply]

lemma sep_of_mem {N : ℕ} {f : C(UG N, ℂ)} (hf : f ∈ algA N) : Sep (⇑f) := by
  have hf' : f ∈ Algebra.adjoin ℂ ((Set.range fun ij : Fin N × Fin N => coordC ij.1 ij.2) ∪
      star (Set.range fun ij : Fin N × Fin N => coordC ij.1 ij.2)) := by
    rw [← StarAlgebra.adjoin_toSubalgebra]; exact hf
  clear hf
  induction hf' using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨⟨i, j⟩, rfl⟩ | hx
    · exact Sep.coord i j
    · obtain ⟨⟨i, j⟩, hij⟩ := (Set.mem_star.mp hx)
      have : x = star (coordC i j) := by rw [show coordC i j = star x from hij, star_star]
      subst this
      exact Sep.conjCoord i j
  | algebraMap r => exact Sep.const r
  | add x y _ _ hx hy => exact Sep.add hx hy
  | mul x y _ _ hx hy => exact Sep.mul hx hy

end PI.UnitaryGroupMassFormula.PolyCoef
