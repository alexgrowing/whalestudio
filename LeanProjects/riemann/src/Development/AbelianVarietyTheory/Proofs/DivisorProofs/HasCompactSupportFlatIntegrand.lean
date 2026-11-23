import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}

theorem isLocallyConstant_of_isTensor {ϖ : kˣ} {e : ℕ} {γ : List Edge} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) :
    IsLocallyConstant T := by
  classical
  refine (IsLocallyConstant.iff_eventually_eq T).2 fun x => ?_
  have h : ∀ᶠ y in nhds x, ∀ b ∈ γ.toFinset, ∀ i j, (((ϖ ^ e)⁻¹ : kˣ) : k) * (y b i j - x b i j) ∈ 𝒪[k] := by
    refine (Filter.eventually_all_finset _).2 fun b _ => Filter.eventually_all.2 fun i =>
      Filter.eventually_all.2 fun j => ?_
    have hc : Continuous fun y : G.Args => (((ϖ ^ e)⁻¹ : kˣ) : k) * (y b i j - x b i j) :=
      continuous_const.mul (((continuous_apply b).matrix_elem i j).sub continuous_const)
    exact (Model.isOpen_int.preimage hc).mem_nhds (by simp)
  filter_upwards [h] with y hy
  rw [← hT.2.2 x (fun b => if b ∈ γ then y b - x b else 0) fun b => ?_]
  · exact hT.1 fun b hb => by simp [show b ∈ γ from hb]
  · split_ifs with hb
    · exact fun i => (mem_smul_lat _ _ _).2 (mem_stdLat.2 fun j => hy b (List.mem_toFinset.2 hb) i j)
    · exact zero_mem _

theorem continuous_stepPt {n n' : Type*} {c : ℕ} (x₀ : Matrix n n' k) :
    Continuous fun e : StepVar n c n' → k => stepPt x₀ e := by
  refine continuous_const.add (continuous_matrix fun r s => ?_)
  simp only [of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_fill (hs : 1 ≤ G.s) (x : ColArgs G) (y : RowArgs G) : Continuous (fill hs x y) := by
  refine continuous_pi ?_
  rintro (⟨i, j⟩ | ⟨i, j⟩) <;> simp only [fill] <;> split_ifs
  · refine Continuous.matrix_transpose (Continuous.matrix_submatrix ?_ _ _)
    unfold downMap
    split_ifs with h
    · exact ((continuous_stepPt _).comp (continuous_apply (⟨j, h⟩ : Fin (G.m - 1)))).matrix_reindex _ _
    · exact continuous_const
    · exact continuous_const
  all_goals exact continuous_const

theorem continuous_phase (x : ColArgs G) : Continuous (phase x) := by
  have hp : ∀ (j : Fin (G.m - 1)) r s, Continuous fun e : Vars G => stepPt (x j) (e j) r s := fun j r s =>
    ((continuous_stepPt _).comp (continuous_apply j)).matrix_elem r s
  refine continuous_finsetSum _ fun j _ => (continuous_finsetSum _ fun i _ => hp j _ _).add ?_
  split_ifs
  · refine continuous_finsetSum _ fun r _ => Continuous.mul ?_ (hp j _ _)
    unfold rowVar
    split_ifs with h
    · refine continuous_finsetSum _ fun l _ => ?_
      split_ifs
      · exact hp ⟨_, h⟩ _ _
      · exact continuous_const
    · exact continuous_const
  · exact continuous_const

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem exists_fill_entry (hs : 1 ≤ G.s) (x : ColArgs G) (y : RowArgs G) (j : Fin (G.m - 1))
    (rs : StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j))) :
    ∃ a b c, ∀ e : Vars G, e j rs = fill hs x y e (.theta G.m j) a b - c := by
  refine ⟨frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; have := j.2; omega) rs.1.2,
    frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); have := j.2; omega) rs.1.1,
    basePt _ (x j) rs.1.1 rs.1.2, fun e => ?_⟩
  rw [fill_theta, transpose_apply, downMap, dif_pos j.2]
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, stepPt, Matrix.add_apply, of_apply]
  rw [dif_pos rs.2, add_sub_cancel_left]

theorem exists_isCompact_of_mul_mem {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : GL m k) (B : GL n k) :
    ∃ K : Set (Matrix m n k), IsCompact K ∧ ∀ X, A.val * X * B.val ∈ matLat m (stdLat k n) → X ∈ K := by
  have hO : IsCompact (𝒪[k] : Set k) := isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[k]))
  have hC : IsCompact (Set.univ.pi fun _ : m => Set.univ.pi fun _ : n => (𝒪[k] : Set k)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO
  have hc : Continuous fun M : Matrix m n k => (A⁻¹).val * M * (B⁻¹).val :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ⟨_, hC.image hc, fun X hX => ⟨A.val * X * B.val, fun i _ j _ => mem_matLat_stdLat.1 hX i j, ?_⟩⟩
  show (A⁻¹).val * (A.val * X * B.val) * (B⁻¹).val = X
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul]

theorem continuous_flatIntegrand (hs : 1 ≤ G.s) {ψ : AddChar k Circle} (hψ : Continuous ψ) {ϖ : kˣ} {e : ℕ}
    {γ : List Edge} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) (keep : Bool) (g : G.VertexGroup)
    (x : ColArgs G) (y : RowArgs G) : Continuous (flatIntegrand hs ψ (moved G keep g T) x y) := by
  have hm : Continuous (G.moveArgs .one g) := continuous_pi fun b =>
    (continuous_const.matrix_mul (continuous_apply b)).matrix_mul continuous_const
  exact (continuous_const.mul (continuous_const.mul
    ((isLocallyConstant_of_isTensor hT).continuous.comp (hm.comp (continuous_fill hs x y))))).mul
    (continuous_subtype_val.comp (hψ.comp (continuous_phase x).neg))

theorem hasCompactSupport_flatIntegrand (hs : 1 ≤ G.s) (ψ : AddChar k Circle) {ϖ : kˣ} {e : ℕ}
    {T : G.Args → ℂ} (hT : G.IsTensor ϖ e (oppositePath G.m) T) (keep : Bool) (g : G.VertexGroup)
    (x : ColArgs G) (y : RowArgs G) : HasCompactSupport (flatIntegrand hs ψ (moved G keep g T) x y) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  choose a b c h using exists_fill_entry hs x y
  choose K hK hK' using fun j : Fin (G.m - 1) => exists_isCompact_of_mul_mem
    (Assignment.one.read (g (Edge.theta G.m j).tgt))⁻¹ (Assignment.one.read (g (Edge.theta G.m j).src))
  refine HasCompactSupport.intro (K := Set.univ.pi fun j => Set.univ.pi fun rs =>
    (fun M => M (a j rs) (b j rs) - c j rs) '' K j) (isCompact_univ_pi fun j => isCompact_univ_pi fun rs =>
      (hK j).image ((continuous_id.matrix_elem _ _).sub continuous_const)) fun v hv => ?_
  have h0 : T (G.moveArgs .one g (fill hs x y v)) = 0 := by
    by_contra hne
    refine hv fun j _ rs _ => ⟨_, hK' j _ ?_, (h j rs v).symm⟩
    by_contra hn
    exact hne (hT.2.1 _ (.theta G.m j) (by have := j.2; simp [oppositePath]; omega) hn)
  simp [flatIntegrand, moved, Grid.pathAct, h0]

theorem flatIntegrable_of_isTensor [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ G.s) (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hψ : Continuous ψ)
    (hT : G.IsTensor ϖ e (oppositePath G.m) T) : FlatIntegrable hs ψ ν T := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  intro g x y
  unfold varsVol
  exact (continuous_flatIntegrand hs hψ hT true g x y).integrable_of_hasCompactSupport
    (hasCompactSupport_flatIntegrand hs ψ hT true g x y)

theorem flatIntegrable [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ G.s) (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} :
    IsUnif ϖ → Continuous ψ → G.IsTensor ϖ e (oppositePath G.m) T → FlatIntegrable hs ψ ν T :=
  fun _ hψ hT => flatIntegrable_of_isTensor hs ψ ν hψ hT

end GlobalTheory.FunObj
