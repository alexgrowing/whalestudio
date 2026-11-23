import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.Jet.Line

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

theorem smooth_comb {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') : SmoothOnG ε (fun h => f h + c * f' h) := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', e'⟩ := hf' g hg
  refine ⟨U ∩ U', fun h => F h + c * F' h, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (contDiffOn_const.mul (hF'.mono Set.inter_subset_right)), ?_⟩
  intro x hx hxJ
  simp only [e x hx.1 hxJ, e' x hx.2 hxJ]

theorem smooth_word {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    (w : List (Fin n × Fin n)) : SmoothOnG ε (Eword ε w f) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    have hc := cpartMem n ε (Matrix.single p.1 p.2 1)
    exact smooth_comb Complex.I (rdSmooth n ε _ _ ih hc.1) (rdSmooth n ε _ _ ih hc.2.1)

theorem word_comb {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') (w : List (Fin n × Fin n)) :
    ∀ g, inUJ ε g → Eword ε w (fun h => f h + c * f' h) g = Eword ε w f g + c * Eword ε w f' g := by
  induction w with
  | nil => intro g _; rfl
  | cons p w ih =>
    intro g hg
    have hc := cpartMem n ε (Matrix.single p.1 p.2 1)
    have h1 := Eword_congr ε ih [p] g hg
    have h2 := fun X hX => (rdLin n ε _ _ X X 0 c g (smooth_word hf w) (smooth_word hf' w) hX hX hg).2.2
    refine Eq.trans h1 ?_
    simp only [Eword, Eab, Ec, id, h2 _ hc.1, h2 _ hc.2.1]
    ring

theorem word_append (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (w v : List (Fin n × Fin n)) :
    Eword ε (w ++ v) f = Eword ε w (Eword ε v f) := by
  induction w with
  | nil => rfl
  | cons p w ih => simp only [List.cons_append, Eword, ih]

def ZeroJet (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  SmoothOnG ε f ∧ ∀ w : List (Fin n × Fin n), Eword ε w f 1 = 0

theorem one_mem : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]

theorem zeroJet_zero : ZeroJet ε (fun _ => 0) := by
  refine ⟨fun g _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, fun w => ?_⟩
  cases w with
  | nil => rfl
  | cons p w => rw [Eword_const]

theorem zeroJet_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, ZeroJet ε (F i)) : ZeroJet ε (fun g => ∑ i ∈ s, c i * F i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zeroJet_zero
  | insert i s hi ih =>
    have e : (fun g => ∑ j ∈ insert i s, c j * F j g) = fun g => (∑ j ∈ s, c j * F j g) + c i * F i g := by
      funext g; rw [Finset.sum_insert hi, add_comm]
    rw [e]
    refine ⟨smooth_comb _ ih.1 (hF i).1, fun w => ?_⟩
    rw [word_comb _ ih.1 (hF i).1 w 1 one_mem, ih.2, (hF i).2]
    simp

theorem cpart1_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (c • Z) = c.re • cpart1 ε Z + (-c.im) • cpart2 ε Z := by
  have hI : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
    field_simp; simp
  simp only [cpart1, cpart2, hI, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  generalize Jm ε * Zᴴ * Jm ε = W
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Complex.real_smul]
  apply Complex.ext <;> simp <;> ring

theorem cpart2_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (c • Z) = c.re • cpart2 ε Z + c.im • cpart1 ε Z := by
  have hI : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
    field_simp; simp
  simp only [cpart1, cpart2, hI, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  generalize Jm ε * Zᴴ * Jm ε = W
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Complex.real_smul]
  apply Complex.ext <;> simp <;> ring

theorem rd_eq_sum {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    Rd X f g = ∑ p : Fin n × Fin n, X p.1 p.2 * Eab ε p.1 p.2 f g := by
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  have hE : ∀ Z, Ec ε Z f g =
      fderiv ℝ F g (g * cpart1 ε Z) + Complex.I * fderiv ℝ F g (g * cpart2 ε Z) := fun Z => by
    have hc := cpartMem n ε Z
    simp only [Ec, rdExt n ε f F U g _ hU hgU hg hF e hc.1, rdExt n ε f F U g _ hU hgU hg hF e hc.2.1]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun Z => Ec ε Z f g
      map_add' := fun Y Z => by
        have h1 : cpart1 ε (Y + Z) = cpart1 ε Y + cpart1 ε Z := by
          simp only [cpart1, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
          congr 1; abel
        have h2 : cpart2 ε (Y + Z) = cpart2 ε Y + cpart2 ε Z := by
          simp only [cpart2, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, ← smul_add]
          congr 1; abel
        simp only [hE, h1, h2, Matrix.mul_add, map_add]
        ring
      map_smul' := fun c Z => by
        simp only [hE, cpart1_smul, cpart2_smul, Matrix.mul_add, Matrix.mul_smul, map_add, map_smul,
          RingHom.id_apply, smul_eq_mul, Complex.real_smul]
        apply Complex.ext <;> simp <;> ring }
  have hc := (cpartMem n ε X).2.2.2 hX
  have h0 : Rd X f g = L X := by
    change _ = Ec ε X f g
    rw [hE, hc.1, hc.2, rdExt n ε f F U g _ hU hgU hg hF e hX]
    simp
  have h1 : X = ∑ p : Fin n × Fin n, X p.1 p.2 • Matrix.single p.1 p.2 (1 : ℂ) := by
    rw [Fintype.sum_prod_type]
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp
  rw [h0]
  conv_lhs => rw [h1]
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul]
  rfl

theorem zeroJet_rd {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : ZeroJet ε f) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) : ZeroJet ε (Rd X f) := by
  refine ⟨rdSmooth n ε _ _ hf.1 hX, fun w => ?_⟩
  rw [Eword_congr ε (rd_eq_sum hf.1 hX) w 1 one_mem]
  refine (zeroJet_sum Finset.univ (fun p : Fin n × Fin n => X p.1 p.2) (fun p => Eab ε p.1 p.2 f)
    (fun p => ⟨smooth_word hf.1 [p], fun v => ?_⟩)).2 w
  have := hf.2 (v ++ [p])
  rwa [word_append] at this

theorem deriv_line (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    deriv (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => Rd X f (NormedSpace.exp ((t : ℂ) • X)) := by
  funext s
  simp only [Rd, ← oneParam n X s]
  rw [deriv_comp_const_add (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) s 0, add_zero]

theorem iteratedDeriv_line {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (j : ℕ) :
    ∀ f : Matrix (Fin n) (Fin n) ℂ → ℂ, ZeroJet ε f →
      iteratedDeriv j (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) 0 = 0 := by
  induction j with
  | zero =>
    intro f hf
    simpa [Eword] using hf.2 []
  | succ j ih =>
    intro f hf
    rw [iteratedDeriv_succ', deriv_line]
    exact ih _ (zeroJet_rd hf hX)

theorem vanish_of_zero_jet : ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ), SmoothOnG ε f → inG ε X → (∀ w : List (Fin n × Fin n), Eword ε w f 1 = 0) → AnalyticOnNhd ℝ (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) Set.univ → f (NormedSpace.exp X) = 0 := by
  intro n ε f X hf hX hw hA
  have htop : analyticOrderAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) 0 = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.2 fun m => ?_
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hA 0 trivial)).2
      fun i _ => iteratedDeriv_line hX i f ⟨hf, hw⟩
  have h := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    (analyticOrderAt_eq_top.1 htop) (Set.mem_univ 1)
  simpa using h

end GlobalTheory.Jet.Line
