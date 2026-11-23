import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesClosed

variable {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)

def lowPart {m : ℕ} (M : Mx D m m) : Mx D m m := Matrix.of fun i j => if j ≤ i then M i j else 0

theorem continuous_lowPart {m : ℕ} : Continuous (lowPart (D := D) (m := m)) :=
  continuous_pi fun i => continuous_pi fun j => by
    show Continuous fun a : Mx D m m => if j ≤ i then a i j else 0
    split_ifs
    · exact (continuous_apply j).comp (continuous_apply i)
    · exact continuous_const

theorem lowPart_eq_iff {m : ℕ} (M : Mx D m m) :
    lowPart M = lowPart 1 ↔ ∀ i j : Fin m, (j < i → M i j = 0) ∧ M i i = 1 := by
  constructor
  · intro h i j
    refine ⟨fun hji => ?_, ?_⟩
    · have := congrFun (congrFun h i) j
      simp only [lowPart, Matrix.of_apply, if_pos hji.le] at this
      rwa [Matrix.one_apply_ne hji.ne'] at this
    · have := congrFun (congrFun h i) i
      simp only [lowPart, Matrix.of_apply, if_pos (le_refl i), Matrix.one_apply_eq] at this
      exact this
  · intro h
    ext i j
    simp only [lowPart, Matrix.of_apply]
    split_ifs with hji
    · rcases hji.lt_or_eq with hlt | heq
      · rw [(h i j).1 hlt, Matrix.one_apply_ne hlt.ne']
      · subst heq; rw [(h j j).2, Matrix.one_apply_eq]
    · rfl

theorem strictUp_sub_one {m : ℕ} {M : Mx D m m} (h : ∀ i j : Fin m, (j < i → M i j = 0) ∧ M i i = 1) :
    GlobalTheory.BesselChar.StrictUp (M - 1) := by
  intro j i hij
  rcases hij.lt_or_eq with hlt | heq
  · rw [Matrix.sub_apply, (h j i).1 hlt, Matrix.one_apply_ne hlt.ne', sub_zero]
  · subst heq; rw [Matrix.sub_apply, (h i i).2, Matrix.one_apply_eq, sub_self]

theorem mem_jacGrp_iff_mat (g : GA D S) : g ∈ jacGrp d ↔
    (d.p0 ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.jX) = 0 ∧
      ∀ i j : Fin ρ, (j < i → (d.pX ⬝ (mt S g ⬝ d.jX)) i j = 0) ∧ (d.pX ⬝ (mt S g ⬝ d.jX)) i i = 1) := by
  constructor
  · intro hg
    obtain ⟨n, hn, h, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.1 g).1 hg
    obtain ⟨u, hu, b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).1 n).1 hn
    have e : mt S (d.levi u * (d.nB b * d.nC c) * d.emb0 h) ⬝ d.jX = d.jX ⬝ u.1 := by
      rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, GlobalTheory.MixPer.Decomp.mt_flag_jX]
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_jX, d.pY_jX, d.pX_jX, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.one_mul]
    exact ⟨rfl, rfl, fun i j => hu i j⟩
  · rintro ⟨h0, hY, hX⟩
    obtain ⟨u, hu, hu1⟩ := GlobalTheory.MixPer.Decomp.exists_unit (strictUp_sub_one hX)
    have hu' : u.1 = d.pX ⬝ (mt S g ⬝ d.jX) := by rw [hu1, add_sub_cancel]
    have hgX : mt S g ⬝ d.jX = d.jX ⬝ u.1 := by
      rw [hu']
      conv_lhs => rw [GlobalTheory.MixPer.Decomp.decomp d (mt S g ⬝ d.jX)]
      rw [h0, hY, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero]
    have hst : (d.levi u)⁻¹ * g ∈ stabX d := mem_fixer.2 (GlobalTheory.MixPer.Decomp.fix_of_eq (by rw [d.levi_jX, hgX]))
    obtain ⟨n, hn, h, hnh⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.1 _).1 hst
    have hn' : n ∈ flagN d := (Subgroup.mem_inf.1 (show n ∈ flagN d ⊓ fixer S d.jX from hn)).1
    have e : g = d.levi u * n * d.emb0 h := by rw [mul_assoc, ← hnh, mul_inv_cancel_left]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem (d.levi_mem_NFlag hu) hn')) (Subgroup.mem_sup_right ⟨h, rfl⟩)

theorem jacGrp_closed : IsClosed (jacGrp d : Set (GA D S)) := by
  haveI : T2Space (Mx D S₀.rank ρ) := (lattice_Mx D _ _).2.2.2.1
  haveI : T2Space (Mx D ρ ρ) := (lattice_Mx D _ _).2.2.2.1
  have hc : Continuous fun g : GA D S => mt S g ⬝ d.jX := (continuous_mt S).matrix_mul continuous_const
  have e : (jacGrp d : Set (GA D S)) = {g | d.p0 ⬝ (mt S g ⬝ d.jX) = 0} ∩ {g | d.pY ⬝ (mt S g ⬝ d.jX) = 0} ∩
      {g | lowPart (d.pX ⬝ (mt S g ⬝ d.jX)) = lowPart 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_jacGrp_iff_mat, Set.mem_inter_iff, Set.mem_setOf_eq, lowPart_eq_iff, and_assoc]
  rw [e]
  exact ((isClosed_eq (continuous_const.matrix_mul hc) continuous_const).inter
    (isClosed_eq (continuous_const.matrix_mul hc) continuous_const)).inter
    (isClosed_eq (continuous_lowPart.comp (continuous_const.matrix_mul hc)) continuous_const)

theorem flagUnipotent_anisotropic_projection_eq_one {n : GA D S} (hn : n ∈ flagN d) : d.p0 ⬝ (mt S n ⬝ d.j0) = 1 := by
  obtain ⟨u, -, b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).1 n).1 hn
  rw [mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]
  rw [d.nC_j0, d.nB_j0, ← Matrix.mul_assoc d.p0 (mt S (d.levi u)), d.wittDecomp_projAnisotropic_levi, Matrix.mul_add, d.p0_j0,
    ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, add_zero]

theorem witt_anisotropic_block_flag_mul_embedded {n : GA D S} (hn : n ∈ flagN d) (k : GA D S₀) :
    d.p0 ⬝ (mt S (n * d.emb0 k) ⬝ d.j0) = mt S₀ k := by
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt S n) d.j0, ← Matrix.mul_assoc d.p0, flagUnipotent_anisotropic_projection_eq_one d hn,
    Matrix.one_mul]

set_option maxHeartbeats 1000000 in

theorem exists_emb_of_fix {k : GA D S₀} (hk : mt S₀ k ⬝ o.jB = o.jB) : ∃ a : GA D A, o.emb (a, 1) = k := by
  have h1 : o.pB ⬝ (mt S₀ k ⬝ o.jA) = 0 := by
    have e : adj o.jB ⬝ (gA S₀ ⬝ (mt S₀ k ⬝ o.jA)) = 0 := by
      conv_lhs => rw [← hk]
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S₀) (mt S₀ k) o.jA,
        ← Matrix.mul_assoc (adj (mt S₀ k)) (gA S₀ ⬝ mt S₀ k) o.jA, mt_unitary, o.gram_BA]
    rw [o.pB_eq, Matrix.mul_assoc, Matrix.mul_assoc, e, Matrix.mul_zero]
  obtain ⟨M, hM⟩ : ∃ M : Mx D A.rank A.rank, M = o.pA ⬝ (mt S₀ k ⬝ o.jA) := ⟨_, rfl⟩
  have hA : mt S₀ k ⬝ o.jA = o.jA ⬝ M := by
    calc mt S₀ k ⬝ o.jA = (o.jA ⬝ o.pA + o.jB ⬝ o.pB) ⬝ (mt S₀ k ⬝ o.jA) := by rw [o.sum_eq_one, Matrix.one_mul]
      _ = o.jA ⬝ M := by rw [Matrix.add_mul, Matrix.mul_assoc o.jB, h1, Matrix.mul_zero, add_zero, Matrix.mul_assoc, hM]
  have hu : adj M * (gA A * M) = gA A := by
    calc adj M * (gA A * M) = adj (o.jA ⬝ M) ⬝ (gA S₀ ⬝ (o.jA ⬝ M)) := by
          rw [adj_mul, ← o.gram_AA]; simp only [Matrix.mul_assoc]
      _ = adj (mt S₀ k ⬝ o.jA) ⬝ (gA S₀ ⬝ (mt S₀ k ⬝ o.jA)) := by rw [hA]
      _ = gA A := by
          rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S₀) (mt S₀ k) o.jA,
            ← Matrix.mul_assoc (adj (mt S₀ k)) (gA S₀ ⬝ mt S₀ k) o.jA, mt_unitary, o.gram_AA]
  have key : mt S₀ k = o.jA ⬝ M ⬝ o.pA + o.jB ⬝ o.pB := by
    have e : mt S₀ k ⬝ (o.jA ⬝ o.pA + o.jB ⬝ o.pB) = mt S₀ k := by rw [o.sum_eq_one]; exact Matrix.mul_one _
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hk] at e
    exact e.symm
  exact ⟨ofMat A M hu, mt_injective S₀ (by rw [o.mt_emb, mt_ofMat, mt_one, Matrix.mul_one, key])⟩

def prodSub : Subgroup (GA D S) where
  carrier := {g | ∃ n ∈ flagN d, ∃ h, g = n * embA d o h}
  one_mem' := ⟨1, one_mem _, 1, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, hn, h, rfl⟩ ⟨n', hn', h', rfl⟩
    refine ⟨n * (embA d o h * n' * (embA d o h)⁻¹), mul_mem hn ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.2.1 n' hn' _), h * h', ?_⟩
    rw [map_mul]; group
  inv_mem' := by
    rintro _ ⟨n, hn, h, rfl⟩
    refine ⟨embA d o h⁻¹ * n⁻¹ * (embA d o h⁻¹)⁻¹, (GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.2.1 _ (inv_mem hn) _, h⁻¹, ?_⟩
    rw [map_inv]; group

theorem besGrp_le_prodSub : besGrp d o ≤ prodSub d o :=
  sup_le (fun n hn => ⟨n, hn, 1, by simp⟩) (by rintro _ ⟨h, rfl⟩; exact ⟨1, one_mem _, h, by simp⟩)

theorem besGrp_eq_inter :
    (besGrp d o : Set (GA D S)) = (jacGrp d : Set (GA D S)) ∩ {g | d.p0 ⬝ (mt S g ⬝ d.j0) ⬝ o.jB = o.jB} := by
  ext g
  constructor
  · intro hg
    obtain ⟨n, hn, h, rfl⟩ := besGrp_le_prodSub d o hg
    refine ⟨mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨o.emb (h, 1), rfl⟩), ?_⟩
    show d.p0 ⬝ (mt S (n * d.emb0 (o.emb (h, 1))) ⬝ d.j0) ⬝ o.jB = o.jB
    rw [witt_anisotropic_block_flag_mul_embedded d hn, o.emb_jB, mt_one, Matrix.mul_one]
  · rintro ⟨hg, he⟩
    obtain ⟨n, hn, k, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D S S₀ ρ d).2.2.2.1 g).1 hg
    have he' : d.p0 ⬝ (mt S (n * d.emb0 k) ⬝ d.j0) ⬝ o.jB = o.jB := he
    rw [witt_anisotropic_block_flag_mul_embedded d hn] at he'
    obtain ⟨a, ha⟩ := exists_emb_of_fix o he'
    exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨a, by rw [embA_apply, ha]⟩)

theorem besGrp_isClosed : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L),
    IsClosed (besGrp d o : Set (GA D S)) := by
  intro D S S₀ A L ρ d o
  rw [besGrp_eq_inter]
  haveI : T2Space (Mx D S₀.rank L.rank) := (lattice_Mx D _ _).2.2.2.1
  exact (jacGrp_closed d).inter (isClosed_eq
    ((continuous_const.matrix_mul ((continuous_mt S).matrix_mul continuous_const)).matrix_mul continuous_const)
    continuous_const)

end GlobalTheory.BesClosed
