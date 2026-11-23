import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacterIm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceThetaFunctionVacuumConjugatePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactShellNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticTraceFormAlternatingSwap
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

open GlobalTheory.SplitInvFormF

theorem exists_detect {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hσ : ∀ x, σ (σ x) = x) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0)
    (hσξ : σ ξ₀ = -ξ₀) {e : AEF F E} (he : IsSplitIdemF σ e) (y : WOF F E nS nT)
    (hy : ∀ i j, cAF σ e * y i j = y i j) (hy0 : y ≠ 0) :
    ∃ g : WOF F E nS nT, (∀ i j, e * g i j = g i j) ∧
      ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) ≠ 1 := by
  classical
  let P : Matrix (Fin nS) (Fin nS) (AEF F E) := (JS⁻¹).map (incAF F E)
  let Q : Matrix (Fin nT) (Fin nT) (AEF F E) := JT.map (incAF F E)
  let Y : Matrix (Fin nS) (Fin nT) (AEF F E) := (y.map (cAF σ))ᵀ
  have hP : IsUnit P.det := by
    have := (Matrix.isUnit_nonsing_inv_det JS (Ne.isUnit hS.2)).map (incAF F E)
    rwa [RingHom.map_det] at this
  have hQ : IsUnit Q.det := by
    have := (Ne.isUnit hT.2).map (incAF F E)
    rwa [RingHom.map_det] at this
  have hm : P * Y * Q ≠ 0 := by
    intro h0
    apply hy0
    have h1 : Y = 0 := by
      rw [← Matrix.nonsing_inv_mul_cancel_left P Y hP, ← Matrix.mul_nonsing_inv_cancel_right Q (P * Y) hQ, h0,
        Matrix.zero_mul, Matrix.mul_zero]
    ext i j
    have h2 : cAF σ (y i j) = 0 := congrFun (congrFun h1 j) i
    rw [← GlobalTheory.SymplSkew.cAF_cAF σ hσ (y i j), h2, map_zero]
    rfl
  obtain ⟨a, d, had⟩ : ∃ a d, (P * Y * Q) a d ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hm (Matrix.ext hc)
  have hval : (P * Y * Q) a d = ∑ b, ∑ c, incAF F E (JS⁻¹ a b) * cAF σ (y c b) * incAF F E (JT c d) := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    rfl
  have hem : (P * Y * Q) a d * e = (P * Y * Q) a d := by
    rw [hval, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e1 : cAF σ (y c b) = e * cAF σ (y c b) := by
      conv_lhs => rw [← hy c b]
      rw [map_mul, cAF_cAF he]
    linear_combination (-(incAF F E (JS⁻¹ a b) * incAF F E (JT c d))) * e1
  have hξm : incAF F E ξ₀ * (P * Y * Q) a d ≠ 0 := fun h =>
    had (((Ne.isUnit hξ).map (incAF F E)).mul_right_eq_zero.1 h)
  obtain ⟨z, hz⟩ := GlobalTheory.AdelicTraceNondeg.trace_pairing_nondeg F E ψ hψ _ hξm
  refine ⟨Matrix.single d a (e * z), fun i j => ?_, ?_⟩
  · simp only [Matrix.single_apply]
    split_ifs
    · rw [← mul_assoc, he.1]
    · rw [mul_zero]
  · have hh : hOF σ JS JT (Matrix.single d a (e * z)) y = (P * Y * Q) a d * z := by
      rw [← hem, mul_assoc, hval]
      unfold hOF
      rw [Finset.sum_eq_single a (fun a' _ ha => by simp [Matrix.single_apply, Ne.symm ha])
        (fun h => absurd (Finset.mem_univ a) h), Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_eq_single d (fun d' _ hd => by simp [Matrix.single_apply, Ne.symm hd])
        (fun h => absurd (Finset.mem_univ d) h), Matrix.single_apply_same]
    have h2 : algebraMap F (AF F) (1 / 2) + algebraMap F (AF F) (1 / 2) = 1 := by
      rw [← map_add, show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]
    unfold symplOHF
    rw [GlobalTheory.SymplSkew.symplOF_swap F E σ hσ nS nT JS JT hS hT ξ₀ hσξ (Matrix.single d a (e * z)) y, mul_neg,
      sub_neg_eq_add, ← add_mul, h2, one_mul, symplOF, hh, ← mul_assoc]
    exact hz

theorem exists_finset_ann_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) →
        ∃ G : Finset (WOF F E nS nT), (∀ g ∈ G, ∀ i j, e * g i j = g i j) ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            (∀ g ∈ G, B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) = 1) → y ∈ U := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he U hU
  classical
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AEF F E) := eh.isEmbedding.t2Space
  have hψ : Continuous B.ψ := hB.std.1
  obtain ⟨he1, he2, v, ε, hpl, hsum⟩ := id he
  obtain ⟨N, Φ, hΦc, hΦi, hΦr⟩ := GlobalTheory.PlaceCoordsF.coords_at_place F E v ε hpl nS nT
  have hV : (Φ ⁻¹' (U : Set (WOF F E nS nT))) ∈ nhds (0 : Fin N → v.adicCompletion F) :=
    (hU.preimage hΦc).mem_nhds (by rw [Set.mem_preimage, map_zero]; exact U.zero_mem)
  obtain ⟨K, hK, hK0, hKn⟩ := GlobalTheory.NonarchShell.exists_compact_shell_nsmul F v N _ hV
  let Y : Set (WOF F E nS nT) := {y | ∀ i j, cAF σ e * y i j = y i j}
  have hYc : IsClosed Y := by
    simp only [Y, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
        ((continuous_apply j).comp (continuous_apply i))
  have hcc : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, he1]
  have hYε : ∀ y ∈ Y, ∀ i j, algebraMap (AF F) (AEF F E) ε * y i j = y i j := by
    intro y hy i j
    rw [← hsum, ← hy i j]
    linear_combination (y i j) * he2 + (y i j) * hcc
  have hYn : ∀ y ∈ Y, ∀ n : ℕ, n • y ∈ Y := by
    intro y hy n i j
    show cAF σ e * (n • y i j) = n • y i j
    rw [mul_smul_comm, hy i j]
  let χ : WOF F E nS nT → WOF F E nS nT → ℂ := fun g y =>
    B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g)
  have hχc : ∀ g, Continuous (χ g) := fun g =>
    hψ.comp ((GlobalTheory.HeisThetaF.continuous_symplOHF_right g).sub (GlobalTheory.HeisThetaF.continuous_symplOHF_left g))
  have hχn : ∀ g y (n : ℕ), χ g (n • y) = χ g y ^ n := by
    intro g y n
    induction n with
    | zero =>
      simp only [χ, zero_smul, GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero,
        AddChar.map_zero_eq_one, pow_zero]
    | succ n ih =>
      rw [succ_nsmul, pow_succ, ← ih]
      simp only [χ]
      rw [GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right, ← AddChar.map_add_eq_mul]
      congr 1
      ring
  let S : Set (WOF F E nS nT) := Φ '' K ∩ Y
  have hSc : IsCompact S := (hK.image hΦc).inter_right hYc
  have hSdet : ∀ s ∈ S, ∃ g : WOF F E nS nT, (∀ i j, e * g i j = g i j) ∧ χ g s ≠ 1 := by
    rintro s ⟨⟨k, hk, rfl⟩, hsY⟩
    refine exists_detect (GlobalTheory.SplitDetCharF.sig_invol hB.cm) hB.std hS hT hξ hσξ he _ hsY ?_
    intro h0
    apply hK0
    rw [← map_zero Φ] at h0
    rwa [hΦi h0] at hk
  choose! gs hgsX hgsχ using hSdet
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover (fun s : S => {y | χ (gs s.1) y ≠ 1})
    (fun s => isOpen_ne_fun (hχc _) continuous_const) (fun s hs => Set.mem_iUnion.2 ⟨⟨s, hs⟩, hgsχ s hs⟩)
  refine ⟨t.image (fun s : S => gs s.1), ?_, ?_⟩
  · intro g hg
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hg
    exact hgsX s.1 s.2
  · intro y hy hG
    by_contra hyU
    obtain ⟨t0, rfl⟩ := hΦr _ (hYε _ hy)
    obtain ⟨n, hn⟩ := hKn t0 hyU
    have hmem : Φ (n • t0) ∈ S := ⟨⟨_, hn, rfl⟩, by rw [map_nsmul]; exact hYn _ hy n⟩
    obtain ⟨s, hs, hsy⟩ := Set.mem_iUnion₂.1 (ht hmem)
    apply hsy
    show χ (gs s.1) (Φ (n • t0)) = 1
    rw [map_nsmul, hχn]
    have := hG (gs s.1) (Finset.mem_image_of_mem (fun s : S => gs s.1) hs)
    simp only [χ] at this ⊢
    rw [this, one_pow]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}

theorem isClosed_conjHalf (e : AEF F E) : IsClosed (conjHalf σ e nS nT : Set (WOF F E nS nT)) := by
  have hc : ∀ c : AEF F E, Continuous fun x : AEF F E => c * x := by
    intro c
    have : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
    have : ContinuousAdd (AEF F E) := IsModuleTopology.toContinuousAdd (AF F) (AEF F E)
    exact IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF F) c)
  have hs : (conjHalf σ e nS nT : Set (WOF F E nS nT)) = {u | cAF σ e • u = u} := by
    ext u
    constructor
    · intro h
      funext i j
      exact h i j
    · intro h i j
      exact congrFun (congrFun h i) j
  have hT2 : T2Space (WOF F E nS nT) := (GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT).2.2.2.1
  have hcs : Continuous (fun u : WOF F E nS nT => cAF σ e • u) :=
    continuous_pi fun i => continuous_pi fun j => (hc _).comp ((continuous_apply j).comp (continuous_apply i))
  rw [hs]
  exact isClosed_eq hcs continuous_id

variable (σ nS nT) in

def projH {e : AEF F E} (he : e * e = e) : WOF F E nS nT →+ conjHalf σ e nS nT where
  toFun y := ⟨cAF σ e • y, fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, he]⟩
  map_zero' := Subtype.ext (smul_zero _)
  map_add' a b := Subtype.ext (smul_add _ a b)

theorem projH_coe {e : AEF F E} (he : e * e = e) (y : conjHalf σ e nS nT) : projH σ nS nT he y = y := by
  exact Subtype.ext (by funext i j; exact y.2 i j)

theorem continuous_projH {e : AEF F E} (he : e * e = e) : Continuous (projH σ nS nT he) := by
  have hc : ∀ c : AEF F E, Continuous fun x : AEF F E => c * x := by
    intro c
    have : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
    have : ContinuousAdd (AEF F E) := IsModuleTopology.toContinuousAdd (AF F) (AEF F E)
    exact IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF F) c)
  exact (continuous_pi fun i => continuous_pi fun j => (hc _).comp ((continuous_apply j).comp (continuous_apply i))).subtype_mk _

theorem exists_compact_open {e : AEF F E} (he : IsSplitIdemF σ e) :
    ∃ K : AddSubgroup (conjHalf σ e nS nT), IsOpen (K : Set (conjHalf σ e nS nT)) ∧
      IsCompact (K : Set (conjHalf σ e nS nT)) := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  obtain ⟨he1, he2, v, ε, hpl, hsum⟩ := id he
  obtain ⟨N, Φ, hΦc, -, hΦr⟩ := GlobalTheory.PlaceCoordsF.coords_at_place F E v ε hpl nS nT
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  have hcc : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, he1]
  let J : (Fin N → v.adicCompletion F) →+ conjHalf σ e nS nT := (projH σ nS nT he1).comp Φ
  have hJ : Continuous J := (continuous_projH he1).comp hΦc
  have hJs : Function.Surjective J := fun y => by
    obtain ⟨t, ht⟩ := hΦr y.1 fun i j => by
      rw [← hsum, ← y.2 i j]
      linear_combination (y.1 i j) * he2 + (y.1 i j) * hcc
    exact ⟨t, by show projH σ nS nT he1 (Φ t) = y; rw [ht, projH_coe]⟩
  haveI : LocallyCompactSpace (conjHalf σ e nS nT) :=
    (isClosed_conjHalf e).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : T2Space (conjHalf σ e nS nT) := inferInstance
  haveI : R1Space (conjHalf σ e nS nT) := T2Space.r1Space
  haveI : BaireSpace (conjHalf σ e nS nT) := BaireSpace.of_t2Space_locallyCompactSpace
  have hopen : IsOpenMap J := AddMonoidHom.isOpenMap_of_sigmaCompact J hJs hJ
  let Bl : AddSubgroup (Fin N → v.adicCompletion F) :=
    { carrier := Metric.closedBall 0 1
      add_mem' := fun {a b} ha hb => by
        rw [mem_closedBall_zero_iff] at ha hb ⊢
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := Metric.mem_closedBall_self zero_le_one
      neg_mem' := fun {a} ha => by
        rw [mem_closedBall_zero_iff] at ha ⊢
        rwa [norm_neg] }
  refine ⟨Bl.map J, ?_, ?_⟩
  · rw [AddSubgroup.coe_map]
    exact hopen _ (IsUltrametricDist.isOpen_closedBall 0 one_ne_zero)
  · rw [AddSubgroup.coe_map]
    exact (isCompact_closedBall 0 1).image hJ

theorem exists_compact_of_finite {Y T : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    {K₀ : Set Y} (hK : IsCompact K₀) (φ : Y → T) (A : Set Y) (hfin : (φ '' A).Finite)
    (h : ∀ y y', φ y = φ y' → y - y' ∈ K₀) : ∃ K, IsCompact K ∧ A ⊆ K := by
  classical
  let r : T → Y := fun t => if ht : t ∈ φ '' A then Classical.choose ht else 0
  have hr : ∀ t ∈ φ '' A, φ (r t) = t := by
    intro t ht
    simp only [r, dif_pos ht]
    exact (Classical.choose_spec ht).2
  refine ⟨⋃ t ∈ φ '' A, (fun k => r t + k) '' K₀, hfin.isCompact_biUnion fun t _ => hK.image (continuous_const.add continuous_id), ?_⟩
  intro y hy
  have ht : φ y ∈ φ '' A := ⟨y, hy, rfl⟩
  exact Set.mem_biUnion ht ⟨y - r (φ y), h y (r (φ y)) (hr _ ht).symm, by simp⟩

variable {B : Base F E}

theorem exists_open_sep (hB : B.IsGood σ) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {e : AEF F E} (he : IsSplitIdemF σ e) (U : AddSubgroup (conjHalf σ e nS nT))
    (hU : IsOpen (U : Set (conjHalf σ e nS nT))) :
    ∃ G : Finset (WOF F E nS nT), (∀ g ∈ G, g ∈ conjHalf σ (cAF σ e) nS nT) ∧
      ∀ y : conjHalf σ e nS nT, (∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g y = 1) → y ∈ U := by
  obtain ⟨G, hG1, hG2⟩ := exists_finset_ann_le F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he
    (U.comap (projH σ nS nT he.1)) (hU.preimage (continuous_projH he.1))
  refine ⟨G, fun g hg => GlobalTheory.SplitVacF.mem_conjHalf_conj he (hG1 g hg), fun y hy => ?_⟩
  have := hG2 y.1 y.2 hy
  rwa [AddSubgroup.mem_comap, projH_coe] at this

theorem exists_compact_ann (hB : B.IsGood σ) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {e : AEF F E} (he : IsSplitIdemF σ e) (P : WOF F E nS nT → Prop)
    (hP : ∀ g ∈ conjHalf σ (cAF σ e) nS nT, ∃ k : ℕ, 0 < k ∧ P (k • g)) :
    ∃ K : Set (conjHalf σ e nS nT), IsCompact K ∧
      ∀ y : conjHalf σ e nS nT, (∀ g, P g → commF σ JS JT ξ₀ B.ψ g y = 1) → y ∈ K := by
  obtain ⟨i1, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  obtain ⟨K₀, hKo, hKc⟩ := exists_compact_open (nS := nS) (nT := nT) he
  obtain ⟨G, hG1, hG2⟩ := exists_open_sep hB hS hT hξ hσξ he K₀ hKo
  choose! k hk0 hk using hP
  refine (exists_compact_of_finite hKc
    (fun (y : conjHalf σ e nS nT) (g : G) => commF σ JS JT ξ₀ B.ψ g y)
    {y | ∀ g, P g → commF σ JS JT ξ₀ B.ψ g y = 1} ?_ ?_).imp fun K h => ⟨h.1, fun y hy => h.2 hy⟩
  · refine (Set.Finite.pi' (t := fun g : G => ((Polynomial.nthRoots (k g) (1 : ℂ)).toFinset : Set ℂ))
      fun g => Finset.finite_toSet _).subset ?_
    rintro _ ⟨y, hy, rfl⟩ g
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots (hk0 _ (hG1 _ g.2)),
      ← GlobalTheory.SplitVacF.commF_nsmul_left]
    exact hy _ (hk _ (hG1 _ g.2))
  · intro y y' h
    refine hG2 _ fun g hg => ?_
    have h1 : commF σ JS JT ξ₀ B.ψ g y = commF σ JS JT ξ₀ B.ψ g y' := congrFun h ⟨g, hg⟩
    rw [sub_eq_neg_add, AddSubgroup.coe_add, AddSubgroup.coe_neg, GlobalTheory.SplitVacF.commF_add_right, h1,
      GlobalTheory.SplitVacF.commF_neg_right]

end GlobalTheory.SplitLagrF

end
