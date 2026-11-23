import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Loc (m : ℕ∞) (f : Mat k r → E) (g : Mat k r) : Prop :=
  ∃ U : Set (Mat k r), ∃ f' : Mat k r → E, IsOpen U ∧ g ∈ U ∧ ContDiffOn ℝ (m : WithTop ℕ∞) f' U ∧
    ∀ x ∈ U, x ∈ GV k r → f x = f' x

theorem loc_mono {m m' : ℕ∞} (hmm : m ≤ m') {f : Mat k r → E} {g : Mat k r} (h : Loc m' f g) : Loc m f g := by
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h
  exact ⟨U, f', hU, hgU, hf'.of_le (WithTop.coe_le_coe.2 hmm), he⟩

theorem loc_spread {m : ℕ∞} {f : Mat k r → E} {g : Mat k r} (h : Loc m f g) :
    ∃ U : Set (Mat k r), IsOpen U ∧ g ∈ U ∧ ∀ x ∈ U, Loc m f x := by
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h
  exact ⟨U, hU, hgU, fun x hx => ⟨U, f', hU, hx, hf', he⟩⟩

theorem loc_hasDerivAt {m : ℕ∞} (hm : 1 ≤ m) {f : Mat k r → E} {g X : Mat k r} (h : Loc m f g)
    (hg : g ∈ GV k r) (hX : inLie k r X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (RdV X f g) 0 := by
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h
  have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt g X 0
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hgU)
  have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), f (g * NormedSpace.exp ((t : ℂ) • X)) = f' (g * NormedSpace.exp ((t : ℂ) • X)) := by
    filter_upwards [hmem] with t ht
    exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hg hX t)
  have hf'd : DifferentiableAt ℝ f' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [hγ0]
    exact (hf'.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by exact_mod_cast (show m ≠ 0 from fun h0 => by simp [h0] at hm))
  exact ((hf'd.comp (0 : ℝ) hγ.differentiableAt).congr_of_eventuallyEq hev).hasDerivAt

theorem loc_RdV {m : ℕ∞} {f : Mat k r → E} {g X : Mat k r} (hX : inLie k r X) (h : Loc (m + 1) f g) :
    Loc m (RdV X f) g := by
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h
  refine ⟨U, fun x => fderiv ℝ f' x (x * X), hU, hgU, ?_, ?_⟩
  · have h1 := hf'.fderiv_of_isOpen (m := (m : WithTop ℕ∞)) hU (by push_cast; exact le_rfl)
    exact h1.clm_apply (mulRightRealCLM X).contDiff.contDiffOn
  · intro x hx hxG
    have hd : DifferentiableAt ℝ f' x :=
      (hf'.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    exact (hasDerivAt_of_ext hU hx hxG hX hd he).deriv

theorem loc_Rw {N : ℕ} {f : Mat k r → E} {g : Mat k r} (h : Loc (N : ℕ∞) f g) (w : List (Mat k r))
    (hw : ∀ X ∈ w, inLie k r X) (m : ℕ) (hle : m + w.length ≤ N) : Loc (m : ℕ∞) (Rw w f) g := by
  induction w generalizing m with
  | nil =>
    simp only [List.length_nil, add_zero] at hle
    exact loc_mono (by exact_mod_cast hle) h
  | cons X w ih =>
    have h1 : Loc ((m + 1 : ℕ) : ℕ∞) (Rw w f) g :=
      ih (fun Y hY => hw Y (List.mem_cons_of_mem X hY)) (m + 1) (by simp at hle; omega)
    have h2 : Loc ((m : ℕ∞) + 1) (Rw w f) g := by simpa using h1
    exact loc_RdV (hw X (by simp)) h2

theorem rdV_congr {f₁ f₂ : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) {g X : Mat k r} (hg : g ∈ U)
    (hgG : g ∈ GV k r) (hX : inLie k r X) (he : ∀ x ∈ U, x ∈ GV k r → f₁ x = f₂ x) :
    RdV X f₁ g = RdV X f₂ g := by
  have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt g X 0
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
  show deriv (fun t : ℝ => f₁ (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f₂ (g * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hmem] with t ht
  exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)

theorem rdV_sum {ι : Type*} (L : List ι) (c : ι → ℂ) (h : ι → Mat k r → E) {g X : Mat k r}
    (hg : g ∈ GV k r) (hX : inLie k r X) (hL : ∀ i ∈ L, Loc 1 (h i) g) :
    RdV X (fun x => (L.map fun i => c i • h i x).sum) g = (L.map fun i => c i • RdV X (h i) g).sum := by
  have key : HasDerivAt (fun t : ℝ => (L.map fun i => c i • h i (g * NormedSpace.exp ((t : ℂ) • X))).sum)
      ((L.map fun i => c i • RdV X (h i) g).sum) 0 := by
    induction L with
    | nil => simpa using hasDerivAt_const (0 : ℝ) (0 : E)
    | cons i L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact ((loc_hasDerivAt le_rfl (hL i (by simp)) hg hX).const_smul (c i)).add
        (ih (fun j hj => hL j (by simp [hj])))
  exact key.deriv

def Xa (k r : ℕ) (a b : Fin (2 * r + k + 1)) : Mat k r := hpart1 (Hpk k r) (Matrix.single a b 1)

def Xb (k r : ℕ) (a b : Fin (2 * r + k + 1)) : Mat k r := hpart2 (Hpk k r) (Matrix.single a b 1)

theorem hpk_entry (i j : Fin (2 * r + k + 1)) : ‖Hpk k r i j‖ ≤ 1 := by
  unfold Hpk
  split_ifs <;> simp

theorem conj_entry (a b i j : Fin (2 * r + k + 1)) :
    ‖((Hpk k r)⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * Hpk k r) i j‖ ≤ 1 := by
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, Matrix.conjTranspose_single, star_one]
  have e : (Hpk k r * Matrix.single b a (1 : ℂ) * Hpk k r) i j = Hpk k r i b * Hpk k r a j := by
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul, Finset.sum_ite_eq]
  rw [e, norm_mul]
  exact mul_le_one₀ (hpk_entry i b) (norm_nonneg _) (hpk_entry a j)

theorem single_entry (a b i j : Fin (2 * r + k + 1)) : ‖(Matrix.single a b (1 : ℂ) : Mat k r) i j‖ ≤ 1 := by
  simp only [Matrix.single_apply]
  split_ifs <;> simp

theorem Xa_unit (a b : Fin (2 * r + k + 1)) : unitLie k r (Xa k r a b) := by
  refine ⟨Formalism.FourierDecayAlt.P.Qx2.hpart1_lie _, fun i j => ?_⟩
  simp only [Xa, hpart1, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, norm_mul]
  have h1 := single_entry (k := k) (r := r) a b i j
  have h2 := conj_entry (k := k) (r := r) a b i j
  have h3 := norm_sub_le ((Matrix.single a b (1 : ℂ) : Mat k r) i j)
    (((Hpk k r)⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * Hpk k r) i j)
  have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hn]
  linarith

theorem Xb_unit (a b : Fin (2 * r + k + 1)) : unitLie k r (Xb k r a b) := by
  refine ⟨Formalism.FourierDecayAlt.P.Qx2.hpart2_lie _, fun i j => ?_⟩
  have h1 := single_entry (k := k) (r := r) a b i j
  have h2 := conj_entry (k := k) (r := r) a b i j
  have h3 := norm_add_le ((Matrix.single a b (1 : ℂ) : Mat k r) i j)
    (((Hpk k r)⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * Hpk k r) i j)
  have h4 := norm_sub_le ((Matrix.single a b (1 : ℂ) : Mat k r) i j)
    (((Hpk k r)⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * Hpk k r) i j)
  simp only [Xb, hpart2, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul, norm_mul]
  norm_num at h1 h2 h3 h4 ⊢
  linarith

theorem top_apply' (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (u : ℂ) (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) (g : Mat k r) :
    Top Eop u c d f g = (if c = d then u • f g else 0) + Eop c d f g := rfl

theorem EH_apply (a b : Fin (2 * r + k + 1)) (f : Mat k r → E) (g : Mat k r) :
    Q.EH k r a b f g = RdV (Xa k r a b) f g + Complex.I • RdV (Xb k r a b) f g := rfl

def expand (k r : ℕ) : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → List (ℂ × List (Mat k r))
  | [] => [(1, [])]
  | t :: ts =>
    (expand k r ts).map (fun cw => ((if t.2.1 = t.2.2 then t.1 else 0) * cw.1, cw.2)) ++
    (expand k r ts).map (fun cw => (cw.1, Xa k r t.2.1 t.2.2 :: cw.2)) ++
    (expand k r ts).map (fun cw => (Complex.I * cw.1, Xb k r t.2.1 t.2.2 :: cw.2))

theorem expand_words (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ cw ∈ expand k r ts, (∀ X ∈ cw.2, unitLie k r X) ∧ cw.2.length ≤ ts.length := by
  induction ts with
  | nil =>
    intro cw hcw
    simp [expand] at hcw
    subst hcw
    simp
  | cons t ts ih =>
    intro cw hcw
    simp only [expand, List.mem_append, List.mem_map] at hcw
    rcases hcw with (⟨cw', hcw', rfl⟩ | ⟨cw', hcw', rfl⟩) | ⟨cw', hcw', rfl⟩
    · obtain ⟨h1, h2⟩ := ih cw' hcw'
      exact ⟨h1, by simpa using Nat.le_succ_of_le h2⟩
    · obtain ⟨h1, h2⟩ := ih cw' hcw'
      refine ⟨?_, by simpa using h2⟩
      intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact Xa_unit _ _
      · exact h1 X hX
    · obtain ⟨h1, h2⟩ := ih cw' hcw'
      refine ⟨?_, by simpa using h2⟩
      intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact Xb_unit _ _
      · exact h1 X hX

def foldT (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (f : Mat k r → E) : Mat k r → E :=
  (ts.map fun t => Top (Q.EH k r) t.1 t.2.1 t.2.2).foldr (fun T h => T h) f

theorem sum_map_mul_smul {ι : Type*} (L : List ι) (c : ℂ) (a : ι → ℂ) (x : ι → E) :
    (L.map fun i => (c * a i) • x i).sum = c • (L.map fun i => a i • x i).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, smul_add, mul_smul]

theorem expand_eq (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ (f : Mat k r → E) (g : Mat k r), g ∈ GV k r → Loc (ts.length : ℕ∞) f g →
      foldT ts f g = ((expand k r ts).map fun cw => cw.1 • Rw cw.2 f g).sum := by
  induction ts with
  | nil =>
    intro f g _ _
    simp [foldT, expand, Rw]
  | cons t ts ih =>
    intro f g hg hloc
    obtain ⟨U, hU, hgU, hUloc⟩ := loc_spread (loc_mono (m := (ts.length : ℕ∞))
      (by exact_mod_cast Nat.le_succ ts.length) hloc)
    have heq : ∀ x ∈ U, x ∈ GV k r →
        foldT ts f x = ((expand k r ts).map fun cw => cw.1 • Rw cw.2 f x).sum :=
      fun x hx hxG => ih f x hxG (hUloc x hx)
    have hlocw : ∀ cw ∈ expand k r ts, Loc 1 (Rw cw.2 f) g := by
      intro cw hcw
      obtain ⟨h1, h2⟩ := expand_words ts cw hcw
      simpa using loc_Rw hloc cw.2 (fun X hX => And.left (h1 X hX)) 1
        (by simp only [List.length_cons]; omega)
    have hR : ∀ Y, inLie k r Y → RdV Y (foldT ts f) g =
        ((expand k r ts).map fun cw => cw.1 • Rw (Y :: cw.2) f g).sum := by
      intro Y hY
      rw [rdV_congr hU hgU hg hY heq]
      exact rdV_sum (expand k r ts) (fun cw => cw.1) (fun cw => Rw cw.2 f) hg hY hlocw
    have hXa : inLie k r (Xa k r t.2.1 t.2.2) := And.left (Xa_unit _ _)
    have hXb : inLie k r (Xb k r t.2.1 t.2.2) := And.left (Xb_unit _ _)
    show Top (Q.EH k r) t.1 t.2.1 t.2.2 (foldT ts f) g = _
    rw [top_apply', EH_apply, hR _ hXa, hR _ hXb, heq g hgU hg]
    simp only [expand, List.map_append, List.sum_append, List.map_map, Function.comp_def, sum_map_mul_smul]
    split_ifs <;> simp [add_assoc]

theorem sum_flatMap {α β : Type*} (l : List α) (φ : α → List β) (ψ : β → E) :
    ((l.flatMap φ).map ψ).sum = (l.map fun a => ((φ a).map ψ).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem cvWordSumG (k r : ℕ) (Y : ℂ) : ∃ L : List (ℂ × List (B.Mat k r)),
    (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ 2 * r + k + 1) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
      B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
        Q.CV k r Y f g = (L.map fun cw => cw.1 • B.Rw cw.2 f g).sum := by
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  let ts : Equiv.Perm (Fin (Q.mdim k r 0)) → List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
    fun σ => List.ofFn fun j : Fin (Q.mdim k r 0) =>
      (Q.uC k r 0 Y - ((j : ℕ) : ℂ), Q.posL k r 0 (σ j), Q.posL k r 0 j)
  refine ⟨(Finset.univ : Finset (Equiv.Perm (Fin (Q.mdim k r 0)))).toList.flatMap
      (fun σ => (expand k r (ts σ)).map fun cw => (((Equiv.Perm.sign σ : ℤ) : ℂ) * cw.1, cw.2)), ?_, ?_⟩
  · intro cw hcw
    simp only [List.mem_flatMap, List.mem_map] at hcw
    obtain ⟨σ, _, cw', hm', rfl⟩ := hcw
    have := expand_words (k := k) (r := r) (ts σ) cw' hm'
    refine ⟨this.1, this.2.trans ?_⟩
    simp [ts, hm]
  · intro E _ _ UU f hf g hgU hg
    have hloc : ∀ σ, Loc ((ts σ).length : ℕ∞) f g := by
      intro σ
      obtain ⟨U, f', a, b, c, d⟩ := hf g hgU
      refine ⟨U, f', a, b, ?_, d⟩
      simpa [ts, hm] using c
    have e1 : Q.CV k r Y f g = ∑ σ, (((Equiv.Perm.sign σ : ℤ) : ℂ)) • foldT (ts σ) f g := by
      simp only [Q.CV, Q.capL, qminorOp, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      congr 1
      simp only [foldT, ts, List.map_ofFn]
      rfl
    rw [e1, sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [expand_eq (ts σ) f g hg (hloc σ), List.map_map, ← sum_map_mul_smul]
    rfl

end Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

theorem Formalism.FourierDecayAlt.P.capelli_word_sum_general (k r : ℕ) (Y : ℂ) : ∃ L : List (ℂ × List (Formalism.FourierDecayAlt.B.Mat k r)),
    (∀ cw ∈ L, (∀ X ∈ cw.2, Formalism.FourierDecayAlt.B.unitLie k r X) ∧ cw.2.length ≤ 2 * r + k + 1) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (Formalism.FourierDecayAlt.B.Mat k r))
      (f : Formalism.FourierDecayAlt.B.Mat k r → E),
      Formalism.FourierDecayAlt.B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ Formalism.FourierDecayAlt.B.GV k r →
        Formalism.FourierDecayAlt.Q.CV k r Y f g = (L.map fun cw => cw.1 • Formalism.FourierDecayAlt.B.Rw cw.2 f g).sum :=
  Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.cvWordSumG k r Y

theorem Formalism.FourierDecayAlt.P.capelli_word_sum : Formalism.FourierDecayAlt.JF.CVWordSum :=
  fun k r Y => Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.cvWordSumG k r Y
