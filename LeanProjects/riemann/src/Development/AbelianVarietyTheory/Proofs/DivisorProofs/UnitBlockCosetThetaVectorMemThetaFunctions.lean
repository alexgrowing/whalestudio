import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionsAllLevelsClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open scoped nonZeroDivisors
open GlobalTheory.InertSign

namespace GlobalTheory.FunObj.CosetTT

variable {D : D7}

theorem exists_nat_mul_mem_one (𝔪 : Ideal (𝓞 D.host.E)) : ∃ M : ℕ, 0 < M ∧ ∀ y : D.host.E,
    y ∈ ((((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) →
    (M : D.host.E) * y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  set 𝔫 : Ideal (𝓞 D.host.E) := D.host.conj • 𝔪
  by_cases h : 𝔫 = ⊥
  · refine ⟨1, one_pos, fun y hy => ?_⟩
    have h0 : ((𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = 0 := by
      rw [h]; exact FractionalIdeal.coeIdeal_bot
    rw [h0, div_zero, FractionalIdeal.coe_zero, Submodule.mem_bot] at hy
    rw [hy, mul_zero]; exact Submodule.zero_mem _
  · refine ⟨Ideal.absNorm 𝔫, Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun y hy => ?_⟩
    have hM : ((Ideal.absNorm 𝔫 : ℕ) : D.host.E) ∈ ((𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      rw [FractionalIdeal.mem_coeIdeal]
      exact ⟨(Ideal.absNorm 𝔫 : 𝓞 D.host.E), Ideal.absNorm_mem 𝔫, by simp⟩
    have hne : ((𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    have hm := FractionalIdeal.mul_mem_mul hy hM
    rw [div_mul_cancel₀ _ hne] at hm
    have h1 := FractionalIdeal.coeIdeal_le_one (I := 𝔪) (P := D.host.E) hm
    rw [mul_comm]
    rwa [FractionalIdeal.mem_one_iff, ← Submodule.mem_one] at h1

end GlobalTheory.FunObj.CosetTT

namespace GlobalTheory.FunObj.CosetTT

variable {D : D7}

theorem skewLat_smul (𝔪 : Ideal (𝓞 D.host.E)) (d : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ v ∈ skewLat D 𝔪 d, (M : 𝓞 D.host.E) • v ∈ stdL D d := by
  obtain ⟨M, hM, h⟩ := exists_nat_mul_mem_one (D := D) 𝔪
  refine ⟨M, hM, fun v hv => ?_⟩
  simp only [skewLat, stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hv ⊢
  intro i
  have := h _ (hv i)
  simpa [Pi.smul_apply, Algebra.smul_def] using this

theorem homL_smul {𝔪 : Ideal (𝓞 D.host.E)} {a d M : ℕ}
    (hM : ∀ v ∈ skewLat D 𝔪 d, (M : 𝓞 D.host.E) • v ∈ stdL D d) :
    homL D (stdL D a) (skewLat D 𝔪 d) ≤ (homL D (stdL D a) (stdL D d)).comap
      (LinearMap.lsmul (𝓞 D.host.E) (Matrix (Fin d) (Fin a) D.host.E) (M : 𝓞 D.host.E)) := by
  refine Submodule.span_le.2 fun A hA => ?_
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply]
  refine Submodule.subset_span fun x hx => ?_
  have e : ((M : 𝓞 D.host.E) • A).mulVec x = (M : 𝓞 D.host.E) • A.mulVec x := by
    funext i; simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc]
  rw [e]
  exact hM _ (hA x hx)

theorem YYl_smul {𝔪 : Ideal (𝓞 D.host.E)} {a d M : ℕ}
    (hM : ∀ v ∈ skewLat D 𝔪 d, (M : 𝓞 D.host.E) • v ∈ stdL D d) :
    YYl D (stdL D a) (skewLat D 𝔪 d) ≤ (YYl D (stdL D a) (stdL D d)).comap
      (LinearMap.lsmul (𝓞 D.host.E) (Matrix (Fin d) (Fin a) D.host.E) (M : 𝓞 D.host.E)) := by
  refine Submodule.span_le.2 fun B hB => ?_
  obtain ⟨c, hc, A, hA, rfl⟩ := hB
  have hA' := homL_smul (a := a) hM hA
  simp only [Submodule.mem_comap, LinearMap.lsmul_apply] at hA'
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply]
  rw [Nat.cast_smul_eq_nsmul] at hA' ⊢
  rw [smul_comm]
  exact Submodule.subset_span ⟨c, hc, _, hA', rfl⟩

theorem la_skew_nsmul (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (a d : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ x ∈ La D (tor0 D cc δ) (stdL D a) (skewLat D 𝔪 d), M • x ∈ La0 D (tor0 D cc δ) a d := by
  obtain ⟨M, hM0, hM⟩ := skewLat_smul (D := D) 𝔪 d
  refine ⟨M, hM0, fun x hx => ?_⟩
  have key : La D (tor0 D cc δ) (stdL D a) (skewLat D 𝔪 d) ≤
      (La0 D (tor0 D cc δ) a d).comap (DistribMulAction.toAddMonoidHom (VC D a d) M) := by
    refine (AddSubgroup.closure_le _).2 fun z hz => ?_
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    have hA' := YYl_smul (a := a) hM hA
    simp only [Submodule.mem_comap, LinearMap.lsmul_apply] at hA'
    simp only [SetLike.mem_coe, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply]
    refine AddSubgroup.subset_closure ⟨w, hw, _, hA', ?_⟩
    funext τ i j
    simp [embV, tor0, Algebra.smul_def, nsmul_eq_mul]
    ring
  exact key hx

end GlobalTheory.FunObj.CosetTT

namespace GlobalTheory.FunObj.CosetTT

variable {D : D7}

theorem sd_stdL (n : ℕ) : SD D (stdL D n) := by
  obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
  rw [← h2]; exact (h1 _).2

theorem wd_mem_TT_of_nsmul {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ} {x : VC D a d}
    {M : ℕ} (hM : 0 < M) (hx : M • x ∈ La0 D (tor0 D cc δ) a d) {F : VC D a d → ℂ}
    (hF : F ∈ TT D (tor0 D cc δ) a d) : Wd D (tor0 D cc δ) x F ∈ TT D (tor0 D cc δ) a d := by
  have k : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) a d) := Or.inr ⟨_, _, sd_stdL a, sd_stdL d, rfl⟩
  have n0 := GlobalTheory.ThetaTriple.nice_of_klat hc k
  obtain ⟨hd, m, hm, hF⟩ := hF
  refine ⟨GlobalTheory.ThetaLevels.wd_entire D _ _ hd, m * M, Nat.mul_pos hm hM, fun y hy => ?_⟩
  have hmy := AddSubgroup.nsmul_mem _ hy m
  have h1 : bc D (tor0 D cc δ) ((m * M) • y) x = 1 := by
    rw [mul_comm, mul_smul, GlobalTheory.ThetaLevels.bc_nsmul_left, ← GlobalTheory.ThetaLevels.bc_nsmul_right]
    exact n0.2.1 _ hmy _ hx
  have h2 : bc D (tor0 D cc δ) x ((m * M) • y) = 1 := by
    rw [mul_comm, mul_smul, GlobalTheory.ThetaLevels.bc_nsmul_right, ← GlobalTheory.ThetaLevels.bc_nsmul_left]
    exact n0.2.1 _ hx _ hmy
  have h3 : Wd D (tor0 D cc δ) ((m * M) • y) F = F := by
    rw [mul_smul]; exact hF _ (AddSubgroup.nsmul_mem _ hy M)
  have h4 := Wd_Wd D (tor0 D cc δ) x ((m * M) • y) F
  rw [h3, h2, add_comm] at h4
  rw [Wd_Wd, h1, h4]

theorem iop_mem_TT {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ}
    (B : AddSubgroup (VC D a d)) (hB : ∀ x ∈ B, ∃ M : ℕ, 0 < M ∧ M • x ∈ La0 D (tor0 D cc δ) a d)
    {F : VC D a d → ℂ} (hF : F ∈ TT D (tor0 D cc δ) a d) :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a d) B F ∈ TT D (tor0 D cc δ) a d := by
  set T := tor0 D cc δ
  set A := La0 D T a d
  by_cases hn : (A.addSubgroupOf B).index = 0
  · have h0 : Iop D T A B F = 0 := by funext z; simp [Iop, hn]
    rw [h0]; exact (GlobalTheory.FinWeil.TTs D T a d).zero_mem
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero hn
    letI : Fintype (B ⧸ A.addSubgroupOf B) := Fintype.ofFinite _
    have hI : Iop D T A B F = ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) •
        ∑ q : B ⧸ A.addSubgroupOf B, (al D T ((Quotient.out q : B) : VC D a d) *
          (wdPh D T ((Quotient.out q : B) : VC D a d))⁻¹) • Wd D T ((Quotient.out q : B) : VC D a d) F := by
      funext z
      simp only [Iop, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [finsum_eq_sum_of_fintype]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      have h0 : wdPh D T ((Quotient.out q : B) : VC D a d) ≠ 0 := Complex.exp_ne_zero _
      simp only [Wd]
      rw [mul_assoc, inv_mul_cancel_left₀ h0]
    rw [hI]
    refine (GlobalTheory.FinWeil.TTs D T a d).smul_mem _ (Submodule.sum_mem _ fun q _ => (GlobalTheory.FinWeil.TTs D T a d).smul_mem _ ?_)
    obtain ⟨M, hM, hx⟩ := hB _ (Quotient.out q : B).2
    exact wd_mem_TT_of_nsmul hc hM hx hF

theorem cosetV_mem_TT : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ →
    ∀ (o a d : ℕ) (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
      cosetV D δ 𝔪 o a d e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  intro D δ hc 𝔪 _ o a d e0 he
  have hT := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have he' : e0 ∈ TT D (tor0 D ⊤ δ) a d := hT.1 _ _ (sd_stdL a) (sd_stdL d) e0 he
  obtain ⟨M, hM, hx⟩ := la_skew_nsmul (D := D) ⊤ δ 𝔪 a d
  have hI := iop_mem_TT hc (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) (fun x hx' => ⟨M, hM, hx x hx'⟩) he'
  exact hT.2.2.2 _ _ (hT.2.1 _ _ hI)

end GlobalTheory.FunObj.CosetTT
