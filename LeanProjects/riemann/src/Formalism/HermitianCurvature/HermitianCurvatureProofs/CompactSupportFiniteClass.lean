import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaConjOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def mulRb (k r : ℕ) : Mat k r →L[ℝ] Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)
      map_add' := fun X Y => by ext g : 1; simp [Matrix.mul_add]
      map_smul' := fun c X => by ext g : 1; simp }

def mulLb (k r : ℕ) : Mat k r →L[ℝ] Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)
      map_add' := fun X Y => by ext g : 1; simp [Matrix.add_mul]
      map_smul' := fun c X => by ext g : 1; simp }

theorem vf_eq_b (b : Bool) (X g : Mat k r) :
    vf b X g = (if b then -(mulLb k r X g) else mulRb k r X g) := by
  cases b
  · first
    | rfl
    | simp [vf, mulLb, mulRb, mulL, mulR]
  · first
    | rfl
    | simp [vf, mulLb, mulRb, mulL, mulR]

theorem vf_contDiff {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (b : Bool) {X g : P → Mat k r}
    (hX : ContDiff ℝ ∞ X) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun q => vf b (X q) (g q)) := by
  cases b
  · have h := ((mulRb k r).contDiff.comp hX).clm_apply hg
    first
    | exact h.congr fun q => by rw [vf_eq_b]; rfl
    | (convert h using 1; funext q; rw [vf_eq_b]; rfl)
  · have h := (((mulLb k r).contDiff.comp hX).clm_apply hg).neg
    first
    | exact h.congr fun q => by rw [vf_eq_b]; rfl
    | (convert h using 1; funext q; rw [vf_eq_b]; rfl)

def Phi (F' : Mat k r → E) : (j : ℕ) → (Fin j → Bool) → (Fin j → Mat k r) × Mat k r → E
  | 0, _, q => F' q.2
  | j + 1, bs, q => fderiv ℝ (fun g => Phi F' j (fun i => bs i.succ) ((fun i => q.1 i.succ), g)) q.2
      (vf (bs 0) (q.1 0) q.2)

theorem top_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  first
  | (rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])
  | simp
  | exact le_of_eq (by norm_cast)

theorem phi_contDiffAt (F' : Mat k r → E) {U : Set (Mat k r)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F' U) :
    ∀ (j : ℕ) (bs : Fin j → Bool) (q : (Fin j → Mat k r) × Mat k r), q.2 ∈ U → ContDiffAt ℝ ∞ (Phi F' j bs) q := by
  intro j
  induction j with
  | zero =>
    intro bs q hq
    exact (hF.contDiffAt (hU.mem_nhds hq)).comp q contDiffAt_snd
  | succ j ih =>
    intro bs q hq
    have hsh : ContDiff ℝ ∞ (fun p : ((Fin (j + 1) → Mat k r) × Mat k r) × Mat k r =>
        ((fun i : Fin j => p.1.1 i.succ), p.2)) :=
      (contDiff_pi.2 fun (i : Fin j) => (contDiff_apply ℝ (Mat k r) i.succ).comp (contDiff_fst.comp contDiff_fst)).prodMk
        contDiff_snd
    have h1 : ContDiffAt ℝ ∞ (Function.uncurry fun (p : (Fin (j + 1) → Mat k r) × Mat k r) (g : Mat k r) =>
        Phi F' j (fun i => bs i.succ) ((fun i => p.1 i.succ), g)) (q, q.2) :=
      (ih (fun i => bs i.succ) ((fun i => q.1 i.succ), q.2) hq).comp (q, q.2) hsh.contDiffAt
    have h2 := ContDiffAt.fderiv h1 contDiffAt_snd top_add_one_le
    have h3 : ContDiff ℝ ∞ (fun p : (Fin (j + 1) → Mat k r) × Mat k r => vf (bs 0) (p.1 0) p.2) :=
      vf_contDiff (bs 0) ((contDiff_apply ℝ (Mat k r) 0).comp contDiff_fst) contDiff_snd
    exact h2.clm_apply h3.contDiffAt

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem W_eq_phi {F F' : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F' U)
    (hff : ∀ x ∈ U, x ∈ GV k r → F x = F' x) :
    ∀ (j : ℕ) (bs : Fin j → Bool) (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) →
      ∀ x ∈ U, x ∈ GV k r → W (List.ofFn fun i => (bs i, Xs i)) F x = Phi F' j bs (Xs, x) := by
  intro j
  induction j with
  | zero => intro bs Xs _ x hx hxG; exact hff x hx hxG
  | succ j ih =>
    intro bs Xs hXs x hx hxG
    rw [List.ofFn_succ, W_cons]
    have hd : DifferentiableAt ℝ (fun g => Phi F' j (fun i => bs i.succ) ((fun i => Xs i.succ), g)) x :=
      ((phi_contDiffAt F' hU hF j _ ((fun i => Xs i.succ), x) hx).comp x
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    exact (hasDerivAt_ext (bs 0) hU hx hxG hd (fun h hh hhG => ih _ _ (fun i => hXs i.succ) h hh hhG)
      (hXs 0)).deriv

theorem W_local_zero {F : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V) (h : ∀ x ∈ V, x ∈ GV k r → F x = 0) :
    ∀ (w : List (Bool × Mat k r)), AllLie w → ∀ x ∈ V, x ∈ GV k r → W w F x = 0 := by
  intro w
  induction w with
  | nil => intro _ x hx hxG; exact h x hx hxG
  | cons a w ih =>
    intro hw x hx hxG
    rw [W_cons]
    have hw' : AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hc := (cv_hasDerivAt a.1 a.2 x).continuousAt
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, cv a.1 a.2 t x ∈ V :=
      hc.preimage_mem_nhds (by rw [cv_zero]; exact hV.mem_nhds hx)
    have he : (fun t : ℝ => W w F (cv a.1 a.2 t x)) =ᶠ[𝓝 0] fun _ => (0 : E) := by
      filter_upwards [hmem] with t ht
      exact ih hw' _ ht (cv_mem (hw a List.mem_cons_self) hxG t)
    show deriv (fun t : ℝ => W w F (cv a.1 a.2 t x)) 0 = 0
    rw [he.deriv_eq, deriv_const]

def Box (k r : ℕ) : Set (Mat k r) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1

theorem box_compact : IsCompact (Box k r) := by
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1

theorem mem_box {X : Mat k r} (h : ∀ i j, ‖X i j‖ ≤ 1) : X ∈ Box k r := by
  exact fun i _ j _ => mem_closedBall_zero_iff.mpr (h i j)

theorem local_bound {F : Mat k r → E} (hF : CkOn ⊤ (GV k r) F) (m : ℕ) {g₀ : Mat k r} (hg₀ : g₀ ∈ GV k r) :
    ∃ V ∈ 𝓝 g₀, ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ V, x ∈ GV k r → ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool)
      (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) F x‖ ≤ c := by
  obtain ⟨U, F', hU, hgU, hc, hff⟩ := hF g₀ hg₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU g₀ hgU
  have hsub : Metric.closedBall g₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hc' : ContDiffOn ℝ ∞ F' U := by exact_mod_cast hc
  have hb : ∀ (j : ℕ) (bs : Fin j → Bool), ∃ c : ℝ, ∀ q ∈ (Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ
      Metric.closedBall g₀ (ε / 2), ‖Phi F' j bs q‖ ≤ c := by
    intro j bs
    have hK : IsCompact ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall g₀ (ε / 2)) :=
      (isCompact_univ_pi fun _ => box_compact).prod (isCompact_closedBall g₀ _)
    exact hK.exists_bound_of_continuousOn fun q hq =>
      (phi_contDiffAt F' hU hc' j bs q (hsub hq.2)).continuousAt.continuousWithinAt
  choose c hcb using hb
  refine ⟨Metric.closedBall g₀ (ε / 2), Metric.closedBall_mem_nhds g₀ (by linarith),
    ∑ j : Fin (m + 1), ∑ bs : Fin j → Bool, |c j bs|, by positivity, ?_⟩
  intro x hx hxG j hj bs Xs hL hB
  rw [W_eq_phi hU hc' hff j bs Xs hL x (hsub hx) hxG]
  calc ‖Phi F' j bs (Xs, x)‖ ≤ |c j bs| := (hcb j bs (Xs, x) ⟨fun i _ => hB i, hx⟩).trans (le_abs_self _)
    _ = |c (⟨j, by omega⟩ : Fin (m + 1)) bs| := rfl
    _ ≤ ∑ bs' : Fin (⟨j, by omega⟩ : Fin (m + 1)) → Bool, |c (⟨j, by omega⟩ : Fin (m + 1)) bs'| :=
        Finset.single_le_sum (f := fun bs' => |c (⟨j, by omega⟩ : Fin (m + 1)) bs'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ bs)
    _ ≤ ∑ j' : Fin (m + 1), ∑ bs' : Fin j' → Bool, |c j' bs'| :=
        Finset.single_le_sum (f := fun j' : Fin (m + 1) => ∑ bs' : Fin j' → Bool, |c j' bs'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ _)

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem compact_support_finite_class : Formalism.FourierDecayAlt.P.JFxG.CptInCC := by
  intro k r E _ _ F C hF hC hCF A m
  have hCG : IsCompact (C ∩ GV k r) := hC.inter_right B5.GV_closed
  have hloc : ∀ g₀ ∈ C ∩ GV k r, ∃ V, V ∈ 𝓝 g₀ ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ V, x ∈ GV k r → ∀ (j : ℕ), j ≤ m →
      ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) F x‖ ≤ c := fun g₀ hg₀ => by
    obtain ⟨V, hV, c, hc0, hc⟩ := local_bound hF m hg₀.2
    exact ⟨V, hV, c, hc0, hc⟩
  choose! V hV c hc0 hc using hloc
  obtain ⟨t, htC, hcov⟩ := hCG.elim_nhds_subcover V hV
  have hcW : ∀ g ∈ C ∩ GV k r, ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r),
      (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) F g‖ ≤ ∑ x ∈ t, c x := by
    intro g hg j hj bs Xs hL hB
    obtain ⟨x, hxt, hgx⟩ := Set.mem_iUnion₂.1 (hcov hg)
    exact (hc x (htC x hxt) g hgx hg.2 j hj bs Xs hL hB).trans
      (Finset.single_le_sum (fun y hy => hc0 y (htC y hy)) hxt)
  obtain ⟨cg, hcg⟩ := hCG.exists_bound_of_continuousOn (f := fun g : Mat k r => gN g ^ A)
    fun g hg => ((B6.gN_continuous.continuousAt).rpow_const (Or.inl (B6.gN_pos hg.2).ne')).continuousWithinAt
  have hsum0 : 0 ≤ ∑ x ∈ t, c x := Finset.sum_nonneg fun y hy => hc0 y (htC y hy)
  refine ⟨|cg| * ∑ x ∈ t, c x, B5.ckOn_mono le_top hF, ?_⟩
  intro u v hu hv hl g hg
  rw [dLR_eq]
  have hmemlr : ∀ y ∈ lr u v, unitLie k r y.2 := by
    intro y hy
    simp only [lr, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact hu X hX
    · exact hv X hX
  by_cases hgC : g ∈ C
  · have hw : lr u v = List.ofFn fun i : Fin (lr u v).length => ((lr u v)[i].1, (lr u v)[i].2) := by
      simp
    have hlen : (lr u v).length ≤ m := by simp [lr]; omega
    have hb := hcW g ⟨hgC, hg⟩ _ hlen (fun i => (lr u v)[i].1) (fun i => (lr u v)[i].2)
      (fun i => (hmemlr _ (List.getElem_mem _)).1) (fun i => mem_box (hmemlr _ (List.getElem_mem _)).2)
    rw [← hw] at hb
    have hg1 : gN g ^ A ≤ |cg| := by
      have := hcg g ⟨hgC, hg⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_abs_self _))
    exact mul_le_mul hg1 hb (norm_nonneg _) (abs_nonneg _)
  · have h0 := W_local_zero hC.isClosed.isOpen_compl (fun x hx _ => hCF x hx) (lr u v)
      (fun y hy => (hmemlr y hy).1) g hgC hg
    rw [h0, norm_zero, mul_zero]
    positivity

theorem jf_radAdj_of_parts : Formalism.FourierDecayAlt.P.JFxG.Exhaust → Formalism.FourierDecayAlt.JF.JDom → Formalism.FourierDecayAlt.P.JFxG.JThetaAdjC →
    Formalism.FourierDecayAlt.P.JFxG.BetaAdjC → Formalism.FourierDecayAlt.JF.RadAdj := by
  intro hE hJ hA hB
  exact radial_adjoint_of_parts hE (theta_conj_of_parts hJ compact_support_finite_class hA) hB

end Formalism.FourierDecayAlt.P
