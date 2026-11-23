import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerTraceAlmostSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumMulLeftTransversal

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CycInvariants

theorem exists_reps {G : Type} [Group G] (H N : Subgroup G) [(N.subgroupOf H).FiniteIndex] :
    ∃ S : Finset G, (∀ s ∈ S, s ∈ H) ∧ ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N := by
  classical
  have : Fintype (H ⧸ N.subgroupOf H) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : H ⧸ N.subgroupOf H => ((q.out : H) : G)), ?_, ?_⟩
  · intro s hs
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    exact q.out.2
  · intro h hh
    refine ⟨((QuotientGroup.mk (⟨h, hh⟩ : H) : H ⧸ N.subgroupOf H).out : H),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · have h1 := QuotientGroup.out_eq' (QuotientGroup.mk (⟨h, hh⟩ : H) : H ⧸ N.subgroupOf H)
      have h2 := QuotientGroup.eq.1 h1
      simpa [Subgroup.mem_subgroupOf] using h2
    · rintro s ⟨hs, hsN⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
      have : (QuotientGroup.mk q.out : H ⧸ N.subgroupOf H) = QuotientGroup.mk (⟨h, hh⟩ : H) :=
        QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hsN)
      rw [QuotientGroup.out_eq'] at this
      rw [this]

theorem sum_reps_invariant {G M : Type} [Group G] [AddCommMonoid M] (H N : Subgroup G)
    (S : Finset G) (hS : ∀ s ∈ S, s ∈ H) (hu : ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N)
    (f : G → M) (hf : ∀ g, ∀ n ∈ N, f (g * n) = f g) (h : G) (hh : h ∈ H) :
    ∑ s ∈ S, f (h * s) = ∑ s ∈ S, f s := by
  first
  | exact @_root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal
  | exact _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal
  | (apply _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal ..)

variable {l : ℕ} [Fact l.Prime]

theorem stabilizer_finiteIndex (x : Om l) : (MulAction.stabilizer (GQ l) x).FiniteIndex := by
  refine ⟨?_⟩
  rw [MulAction.index_stabilizer]
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hfin : (MulAction.orbit (GQ l) x).Finite := by
    refine ((minpoly ℚ_[l] x).rootSet_finite (Om l)).subset ?_
    rintro _ ⟨g, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    change Polynomial.aeval (g x) _ = 0
    rw [Polynomial.aeval_algEquiv]
    simp
  exact ((Set.ncard_pos hfin).2 ⟨x, MulAction.mem_orbit_self x⟩).ne'

theorem exists_field (F : IntermediateField ℚ_[l] (Om l)) (x : Om l) :
    ∃ (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)), x ∈ L ∧ F ≤ L ∧
      (∀ h ∈ F.fixingSubgroup, ∀ x ∈ L, h x ∈ L) ∧ (∀ s ∈ S, s ∈ F.fixingSubgroup) ∧
      (∀ h ∈ F.fixingSubgroup, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) := by
  have := stabilizer_finiteIndex x
  set N := (MulAction.stabilizer (GQ l) x).normalCore with hN
  set L := IntermediateField.fixedField (F.fixingSubgroup ⊓ N) with hL
  have hle : F.fixingSubgroup ⊓ N ≤ L.fixingSubgroup :=
    (IntermediateField.le_iff_le _ _).1 le_rfl
  have hfi : (L.fixingSubgroup.subgroupOf F.fixingSubgroup).FiniteIndex := by
    refine Subgroup.finiteIndex_of_le (H := N.subgroupOf F.fixingSubgroup) ?_
    intro g hg
    exact hle ⟨g.2, hg⟩
  obtain ⟨S, hS, hu⟩ := exists_reps F.fixingSubgroup L.fixingSubgroup
  refine ⟨L, S, ?_, ?_, ?_, hS, hu⟩
  · rw [hL, IntermediateField.mem_fixedField_iff]
    intro g hg
    exact Subgroup.normalCore_le _ hg.2
  · exact (IntermediateField.le_iff_le _ _).2 inf_le_left
  · intro h hh y hy
    rw [hL, IntermediateField.mem_fixedField_iff] at hy ⊢
    intro g hg
    have h1 : h⁻¹ * g * h ∈ F.fixingSubgroup ⊓ N :=
      ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hg.1) hh,
        by simpa using (Subgroup.normalCore_normal _).conj_mem g hg.2 h⁻¹⟩
    have h2 := congrArg h (hy _ h1)
    simpa using h2

theorem fixed_iff_mem_Ohat : ∀ (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act →
    ∀ (K : FinExt l) (y : PadicComplex l), ‖y‖ ≤ 1 →
      ((∀ h ∈ Hinf K, act h y = y) ↔ y ∈ Ohat K) := by
  intro l _ act hact K y hy
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  constructor
  · intro hfix
    rw [Ohat, Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := min (ε / 2) 1 with hδ
    have hδ0 : 0 < δ := lt_min (by linarith) one_pos
    obtain ⟨x, hx⟩ := (UniformSpace.Completion.denseRange_coe (α := Om l)).exists_dist_lt y
      (div_pos hδ0 hl0)
    rw [dist_eq_norm] at hx
    obtain ⟨L, S, hxL, hKL, hst, hS, hu⟩ := exists_field (Kinf K) x
    have hnl : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
      rw [← map_natCast (algebraMap ℚ_[l] (Om l))]
      exact (PadicAlgCl.norm_extends l _).trans Padic.norm_p
    have hlne : (l : Om l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    obtain ⟨b, hbL, hb1, hb⟩ := GlobalTheory.T.cyclotomicTower_trace_almost_surjective l K L S hKL hst hS hu (l : Om l)
      (natCast_mem _ _) (by rw [hnl]; exact inv_lt_one_of_one_lt₀ hl1)
    set w : Om l := ∑ s ∈ S, s (b * x) with hw
    have hwK : w ∈ Kinf K := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (Kinf K), IntermediateField.mem_fixedField_iff]
      intro h hh
      rw [hw, map_sum]
      refine sum_reps_invariant _ _ S hS hu (fun g => g (b * x)) ?_ h hh
      intro g n hn
      have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hn _ (L.mul_mem hbL hxL)
      simp only [AlgEquiv.mul_apply, this]
    set ι := algebraMap (Om l) (PadicComplex l) with hι
    have hιn : ∀ u, ‖ι u‖ = ‖u‖ := fun u => PadicComplex.norm_extends l u
    have hιa : ∀ g u, act g (ι u) = ι (g u) := hact.1
    have hdiff : ι l * y - ι w = ∑ s ∈ S, act s (ι b * (y - ι x)) := by
      rw [← hb, hw, map_sum, map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [map_mul (act s), map_sub, hfix s (hS s hs), hιa, hιa, map_mul, map_mul, mul_sub]
    have hle : ‖ι l * y - ι w‖ ≤ δ / l := by
      rw [hdiff]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_pos hδ0 hl0).le ?_
      intro s _
      rw [hact.2, norm_mul, hιn]
      calc ‖b‖ * ‖y - ι x‖ ≤ 1 * (δ / l) := mul_le_mul hb1 hx.le (norm_nonneg _) one_pos.le
        _ = δ / l := one_mul _
    have hle' : ‖y - ι (w / l)‖ ≤ δ := by
      have h1 : ι l * y - ι w = ι l * (y - ι (w / l)) := by
        rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hlne]
      rw [h1, norm_mul, hιn, hnl, div_eq_inv_mul δ] at hle
      exact le_of_mul_le_mul_left hle (inv_pos.2 hl0)
    refine ⟨ι (w / l), ⟨⟨w / l, div_mem hwK (natCast_mem _ _), rfl⟩, ?_⟩, ?_⟩
    · have h1 : ι (w / l) = y + -(y - ι (w / l)) := by ring
      rw [h1]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy ?_)
      rw [norm_neg]
      exact hle'.trans (min_le_right _ _)
    · rw [dist_eq_norm]
      exact lt_of_le_of_lt (hle'.trans (min_le_left _ _)) (by linarith)
  · intro hyO h hh
    have hc : Continuous (act h) :=
      (AddMonoidHomClass.isometry_of_norm (act h) (hact.2 h)).continuous
    refine closure_minimal (t := {z | act h z = z}) ?_ (isClosed_eq hc continuous_id) hyO
    rintro _ ⟨⟨u, hu, rfl⟩, -⟩
    change act h (u : PadicComplex l) = (u : PadicComplex l)
    rw [hact.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh u hu]

end GlobalTheory.CycInvariants
