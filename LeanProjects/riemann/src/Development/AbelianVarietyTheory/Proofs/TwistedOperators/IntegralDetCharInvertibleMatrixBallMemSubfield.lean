import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.GLBallInt
open MeasureTheory
open scoped Pointwise

theorem integral_eq_sum_of_rightInv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKt : μ K ≠ ⊤) {S : Set G} (hS : IsCompact S)
    (hSK : ∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) (f : G → ℂ) (hf : ∀ s ∈ S, ∀ k ∈ K, f (s * k) = f s) :
    ∃ t : Finset (G ⧸ K), ∫ g in S, f g ∂μ = ∑ Q ∈ t, f Q.out * μ.real K := by
  classical
  set q : G → G ⧸ K := QuotientGroup.mk

  have hcov : S ⊆ ⋃ s ∈ S, s • (K : Set G) := fun s hs =>
    Set.mem_biUnion hs ⟨1, one_mem K, by simp⟩
  obtain ⟨b, hbS, hbf, hb⟩ := hS.elim_finite_subcover_image (fun s _ => hKo.smul s) hcov
  have hfin : (q '' S).Finite := by
    refine (hbf.image q).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨g, hg, hy⟩ := Set.mem_iUnion₂.1 (hb hs)
    refine ⟨g, hg, ?_⟩
    obtain ⟨y, hy, rfl⟩ := hy
    simp only [smul_eq_mul, q]
    exact (QuotientGroup.mk_mul_of_mem g hy).symm
  have hout : ∀ Q ∈ q '' S, Q.out ∈ S := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K s
    rw [hh]; exact hSK s hs h h.2
  obtain ⟨T, hT⟩ : ∃ T : Finset (G ⧸ K), ∀ Q, Q ∈ T ↔ Q ∈ q '' S :=
    ⟨hfin.toFinset, fun Q => hfin.mem_toFinset⟩
  have hSeq : S = ⋃ Q ∈ T, Q.out • (K : Set G) := by
    ext g
    simp only [Set.mem_iUnion, hT, exists_prop]
    constructor
    · intro hg
      refine ⟨q g, ⟨g, hg, rfl⟩, ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
      refine ⟨h⁻¹, (h⁻¹).2, ?_⟩
      simp [q, hh, mul_assoc]
    · rintro ⟨Q, hQ, y, hy, rfl⟩
      exact hSK _ (hout Q hQ) y hy
  have hconst : ∀ Q ∈ q '' S, ∀ y ∈ Q.out • (K : Set G), f y = f Q.out := by
    rintro Q hQ _ ⟨y, hy, rfl⟩
    exact hf _ (hout Q hQ) y hy
  refine ⟨T, ?_⟩
  rw [hSeq, integral_biUnion_finset]
  · refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [hT] at hQ
    rw [setIntegral_congr_fun (hKo.smul _).measurableSet (hconst Q hQ), setIntegral_const,
      measureReal_def, measure_smul, ← measureReal_def, Complex.real_smul, mul_comm]
  · exact fun Q _ => (hKo.smul _).measurableSet
  · intro Q _ Q' _ hne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', he⟩
    apply hne
    have h1 : q (Q.out * y) = Q := by
      simp only [q]; rw [QuotientGroup.mk_mul_of_mem _ hy]; exact QuotientGroup.out_eq' Q
    have h2 : q (Q'.out * y') = Q' := by
      simp only [q]; rw [QuotientGroup.mk_mul_of_mem _ hy']; exact QuotientGroup.out_eq' Q'
    simp only [smul_eq_mul] at he
    rw [← h1, ← h2, he]
  · intro Q hQ
    rw [hT] at hQ
    refine (integrableOn_congr_fun (hconst Q hQ) (hKo.smul _).measurableSet).2 ?_
    refine integrableOn_const ?_
    rw [measure_smul]; exact hKt

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory
open scoped Pointwise

theorem measureReal_eq_inv_natCast {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] {J K : Subgroup G}
    (hJc : IsCompact (J : Set G)) (hJ1 : μ J = 1) (hKo : IsOpen (K : Set G)) (hKJ : K ≤ J) :
    ∃ n : ℕ, μ.real K = (n : ℝ)⁻¹ := by
  have hKt : μ K ≠ ⊤ := ((measure_mono (show (K : Set G) ⊆ J from hKJ)).trans_lt (by simp [hJ1])).ne
  obtain ⟨t, ht⟩ := integral_eq_sum_of_rightInv μ K hKo hKt hJc (fun s hs k hk => J.mul_mem hs (hKJ hk))
    (fun _ => (1 : ℂ)) (fun _ _ _ _ => rfl)
  rw [setIntegral_const, measureReal_def, hJ1, Finset.sum_const, nsmul_eq_mul, one_mul] at ht
  simp only [ENNReal.toReal_one, one_smul] at ht
  refine ⟨t.card, eq_inv_of_mul_eq_one_right ?_⟩
  exact_mod_cast ht.symm

def rightStab {G : Type} [Group G] (S : Set G) : Subgroup G where
  carrier := {k | ∀ g, g ∈ S ↔ g * k ∈ S}
  one_mem' := fun g => by simp
  mul_mem' := fun {a b} ha hb g => by rw [ha g, hb (g * a), mul_assoc]
  inv_mem' := fun {a} ha g => by rw [ha (g * a⁻¹), inv_mul_cancel_right]

theorem isOpen_rightStab {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {S : Set G}
    (hSc : IsCompact S) (hSo : IsOpen S) : IsOpen (rightStab S : Set G) := by
  obtain ⟨V, hV, hSV⟩ := compact_open_separated_mul_right hSc hSo subset_rfl
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (Filter.inter_mem hV (inv_mem_nhds_one G hV)) ?_)
  rintro k ⟨hk, hk'⟩ g
  refine ⟨fun hg => hSV (Set.mul_mem_mul hg hk), fun hg => ?_⟩
  have := hSV (Set.mul_mem_mul hg hk')
  rwa [mul_inv_cancel_right] at this

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A' : Type} [Fintype A'] [DecidableEq A']

def matBall (x : Matrix A' A' k) (c : kˣ) : Set (Matrix A' A' k) :=
  {y | ∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)}

theorem matBall_eq_preimage (x : Matrix A' A' k) (c : kˣ) :
    matBall x c = ⋂ i, ⋂ j, (fun y : Matrix A' A' k => (y i j - x i j) / (c : k)) ⁻¹' (𝒪[k] : Set k) := by
  have h0 : 0 < valuation k (c : k) := zero_lt_iff.2 (by simp)
  ext y
  simp only [matBall, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe,
    Valuation.mem_integer_iff, map_div₀, div_le_one₀ h0]

theorem isOpen_matBall (x : Matrix A' A' k) (c : kˣ) : IsOpen (matBall x c) := by
  rw [matBall_eq_preimage]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    IsOpen.preimage (by fun_prop) Valuation.isOpen_integer

theorem isCompact_matBall (x : Matrix A' A' k) (c : kˣ) : IsCompact (matBall x c) := by
  have hc : (c : k) ≠ 0 := c.ne_zero
  have e : matBall x c = (fun A : Matrix A' A' k => (c : k) • A + x) '' {A | ∀ i j, A i j ∈ 𝒪[k]} := by
    ext y
    constructor
    · intro hy
      refine ⟨fun i j => (y i j - x i j) / (c : k), fun i j => ?_, ?_⟩
      · have := (matBall_eq_preimage x c ▸ hy : y ∈ _)
        simp only [Set.mem_iInter, Set.mem_preimage] at this
        exact this i j
      · ext i j
        show (c : k) * ((y i j - x i j) / (c : k)) + x i j = y i j
        rw [mul_div_cancel₀ _ hc, sub_add_cancel]
    · rintro ⟨A, hA, rfl⟩ i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_right, map_mul]
      exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hA i j))
  rw [e]
  exact isCompact_intMatrix.image (by fun_prop)

theorem isCompact_isOpen_glBall (x : Matrix A' A' k) (c : kˣ) (hdet : ∀ y ∈ matBall x c, y.det ≠ 0) :
    IsCompact {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} ∧
    IsOpen {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} := by
  have e : {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} =
      (fun g : GL A' k => g.val) ⁻¹' matBall x c := rfl
  rw [e]
  refine ⟨?_, (isOpen_matBall x c).preimage Units.continuous_val⟩
  rw [isEmbedding_val_GL.isInducing.isCompact_iff]
  convert isCompact_matBall x c using 1
  ext y
  refine ⟨fun ⟨g, hg, hgy⟩ => hgy ▸ hg, fun hy => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero y (hdet y hy), hy, rfl⟩⟩

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

theorem integral_glBall_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A' : Type} [Fintype A'] [DecidableEq A'] (F : Subfield ℂ) {J : Subgroup (GL A' k)}, IsOpen (J : Set (GL A' k)) → J ≤ KO k A' → ∀ (ν : kˣ →* ℂˣ) (z : ℂ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → CondLE ϖ e ν → (∀ u, (ν u : ℂ) ∈ F) → (∀ u : kˣ, apow u z ∈ F) → ∀ (c : kˣ) (x : Matrix A' A' k), (∀ y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)) → y.det ≠ 0) → ∫ g in {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}, (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol J) ∈ F := by
  intro k _ _ _ _ _ _ A' _ _ F J hJo hJK ν z ϖ e _ hcond hνF hapF c x hdet
  haveI := isHaarMeasure_haarVol hJo hJK
  obtain ⟨hSc, hSo⟩ := isCompact_isOpen_glBall x c hdet
  set S := {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} with hSdef
  set K : Subgroup (GL A' k) := J ⊓ GlobalTheory.SplitFlip.glLatCong (ϖ ^ e) (stdLat k A') ⊓ rightStab S with hKdef
  have hKo : IsOpen (K : Set (GL A' k)) := by
    simp only [hKdef, Subgroup.coe_inf]
    exact (hJo.inter (GlobalTheory.FunObj.GivenAdm.isOpen_glLatCong _)).inter (isOpen_rightStab hSc hSo)
  have hKJ : K ≤ J := inf_le_left.trans inf_le_left
  have hJc : IsCompact (J : Set (GL A' k)) := isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo) hJK
  have hKt : haarVol J K ≠ ⊤ :=
    ((measure_mono (show (K : Set (GL A' k)) ⊆ J from hKJ)).trans_lt (by simp [haarVol_self hJo hJK])).ne
  have hinv : ∀ s ∈ S, ∀ k' ∈ K, ((ν (gdet (s * k')) : ℂ) * apow (gdet (s * k')) z) =
      (ν (gdet s) : ℂ) * apow (gdet s) z := by
    intro s _ k' hk
    have hu : gdet k' ∈ unitCong (ϖ ^ e) :=
      GlobalTheory.FunObj.GivenAdm.gdet_mem_unitCong (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).2
    rw [gdet_mul, map_mul, Units.val_mul, apow_mul, hcond _ hu, apow_of_valuation_eq_one hu.1]
    simp
  obtain ⟨t, ht⟩ := integral_eq_sum_of_rightInv (haarVol J) K hKo hKt hSc
    (fun s hs k' hk => ((Subgroup.mem_inf.1 hk).2 s).1 hs) (fun g => (ν (gdet g) : ℂ) * apow (gdet g) z) hinv
  rw [ht]
  obtain ⟨n, hn⟩ := measureReal_eq_inv_natCast (haarVol J) hJc (haarVol_self hJo hJK) hKo hKJ
  refine Subfield.sum_mem _ fun Q _ => F.mul_mem (F.mul_mem (hνF _) (hapF _)) ?_
  rw [hn]
  push_cast
  exact F.inv_mem (natCast_mem F n)

end GlobalTheory.GLBallInt
