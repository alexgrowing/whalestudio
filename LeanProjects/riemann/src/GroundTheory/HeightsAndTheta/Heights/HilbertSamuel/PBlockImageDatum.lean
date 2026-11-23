import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAnResNullForm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageInverse
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageMetrics
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageChi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

namespace BlockImageDatum

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω]

def blockSubst {J : Type} (k₀ : K) (M : Matrix J (ι k₀) ℤ) : MvPolynomial J ℤ →ₐ[ℤ] MRing ι :=
  aeval fun j => ∑ i, C (M j i) * X ⟨k₀, i⟩

theorem eval_blockSubst {J : Type} (k₀ : K) (M : Matrix J (ι k₀) ℤ) (f : MvPolynomial J ℤ)
    (z : (Σ k, ι k) → ℂ) :
    eval z (map (Int.castRingHom ℂ) (blockSubst k₀ M f)) =
      eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [blockSubst]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, hp]
    congr 1
    simp [blockSubst, blockMapC]

variable {r : ℕ} {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix (Fin r)) (ι k₀) ℤ}
  {N : Matrix (ι k₀) (Ix (Fin r)) ℤ} {x : Ix (Fin r) → Ω}

theorem mConeMap_blockSubst (hB : IsBlockImage y k₀ M N x) (f : MvPolynomial (Ix (Fin r)) ℤ) :
    mConeMap y (blockSubst k₀ M f) = Polynomial.aeval (X k₀ : MvPolynomial K Ω) (coneMap ℤ x f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [blockSubst, coneMap, mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, hp]
    congr 1
    simp [blockSubst, coneMap, mConeMap, hB.1 j, Finset.sum_mul, mul_assoc]

theorem blockSubst_mem (hB : IsBlockImage y k₀ M N x) {f : MvPolynomial (Ix (Fin r)) ℤ}
    (hf : f ∈ coordIdeal ℤ x) : blockSubst k₀ M f ∈ mCoordIdeal y := by
  refine RingHom.mem_ker.mpr ?_
  have hf' : coneMap ℤ x f = 0 := RingHom.mem_ker.mp hf
  change mConeMap y (blockSubst k₀ M f) = 0
  rw [mConeMap_blockSubst hB, hf', map_zero]

theorem blockMapC_N (hB : IsBlockImage y k₀ M N x) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (i : ι k₀) : ∑ j, (N i j : ℂ) * blockMapC k₀ M z j = z ⟨k₀, i⟩ := by
  have hc : mConeMap y (X ⟨k₀, i⟩ : MRing ι) =
      Polynomial.aeval (X k₀ : MvPolynomial K Ω) (coneMap ℤ x (∑ j, C (N i j) * X j)) := by
    simp [coneMap, mConeMap, hB.2 i, Finset.sum_mul, mul_assoc]
  have hmem : (X ⟨k₀, i⟩ : MRing ι) - blockSubst k₀ M (∑ j, C (N i j) * X j) ∈ mCoordIdeal y := by
    refine RingHom.mem_ker.mpr ?_
    rw [map_sub, mConeMap_blockSubst hB, hc, sub_self]
  have h0 := hz.2 _ hmem
  rw [map_sub, map_sub, eval_blockSubst, sub_eq_zero] at h0
  simpa [blockMapC] using h0.symm

theorem blockMapC_mem (hB : IsBlockImage y k₀ M N x) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    blockMapC k₀ M z ∈ mcPts (ι := GlobalTheory (Fin r)) (coordIdeal ℤ x) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · cases k
    by_contra h
    push Not at h
    obtain ⟨i, hi⟩ := hz.1 k₀
    apply hi
    rw [← blockMapC_N hB hz i]
    refine Finset.sum_eq_zero fun j _ => ?_
    obtain ⟨⟨⟩, j⟩ := j
    rw [h j, mul_zero]
  · rw [← eval_blockSubst]
    exact hz.2 _ (blockSubst_mem hB hf)

theorem blockMapC_smul {J : Type} (M : Matrix J (ι k₀) ℤ) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    blockMapC k₀ M (fun p => c p.1 * z p) = fun j => c k₀ * blockMapC k₀ M z j := by
  funext j
  simp only [blockMapC, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sameOrbit_blockMapC (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (ι := GlobalTheory (Fin r)) (blockMapC k₀ M z) (blockMapC k₀ M z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun _ => c k₀, fun _ => hc k₀, by rw [blockMapC_smul]⟩

theorem sameOrbit_trans {z₁ z₂ z₃ : (Σ k, ι k) → ℂ} (h₁ : SameOrbit z₁ z₂) (h₂ : SameOrbit z₂ z₃) :
    SameOrbit z₁ z₃ := by
  obtain ⟨c, hc, rfl⟩ := h₁
  obtain ⟨c', hc', rfl⟩ := h₂
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  dsimp only
  ring

theorem mem_mcPts_span_singleton {F : MRing ι} {u : (Σ k, ι k) → ℂ} (hu : ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0)
    (hF : eval u (map (Int.castRingHom ℂ) F) = 0) : u ∈ mcPts (Ideal.span {F}) := by
  refine ⟨hu, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hf
  rw [map_mul, map_mul, hF, mul_zero]

theorem sum_M_N (hB : IsBlockImage y k₀ M N x) (hx : LinearIndependent ℤ x) (j l : Ix (Fin r)) :
    ∑ i, M j i * N i l = if j = l then 1 else 0 := by
  classical
  have hx' := Fintype.linearIndependent_iff.mp hx
  set g : Ix (Fin r) → ℤ := fun l => ∑ i, M j i * N i l - if j = l then 1 else 0 with hg
  have key : ∑ l, g l • x l = 0 := by
    simp only [hg, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, zsmul_eq_mul]
    rw [sub_eq_zero, hB.1 j]
    simp_rw [hB.2]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  exact sub_eq_zero.mp (hx' g key l)

theorem N_injective (hB : IsBlockImage y k₀ M N x) (hx : LinearIndependent ℤ x) :
    ∀ u : Ix (Fin r) → ℂ, (fun i => ∑ j, (N i j : ℂ) * u j) = 0 → u = 0 := by
  classical
  intro u hu
  funext j
  have h1 : ∀ i, ∑ l, (N i l : ℂ) * u l = 0 := fun i => congrFun hu i
  calc u j = ∑ l, ((∑ i, M j i * N i l : ℤ) : ℂ) * u l := by simp [sum_M_N hB hx]
    _ = ∑ i, (M j i : ℂ) * ∑ l, (N i l : ℂ) * u l := by
        push_cast
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ = 0 := by simp [h1]

omit [DecidableEq K] [CharZero Ω] in

theorem exists_blockBasis [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) :
    ∃ (r : ℕ) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (x : Ix (Fin r) → Ω),
      IsBlockImage y k₀ M N x ∧ LinearIndependent ℤ x := by
  set W : Submodule ℤ Ω := Submodule.span ℤ (Set.range fun i : ι k₀ => y ⟨k₀, i⟩) with hW
  have : Module.Finite ℤ W := Module.Finite.span_of_finite ℤ (Set.finite_range _)
  set b := (Module.Free.chooseBasis ℤ W).reindex (Fintype.equivFin _) with hb
  have hc : ∀ j, ∃ c : ι k₀ → ℤ, ∑ i, c i • y ⟨k₀, i⟩ = (b j : Ω) := fun j =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (b j).2
  choose c hc using hc
  refine ⟨_, fun j i => c j.2 i, fun i j => b.repr ⟨y ⟨k₀, i⟩, Submodule.subset_span (Set.mem_range_self i)⟩ j.2,
    fun j => (b j.2 : Ω), ⟨fun j => ?_, fun i => ?_⟩, ?_⟩
  · show (b j.2 : Ω) = ∑ i, (c j.2 i : Ω) * y ⟨k₀, i⟩
    rw [← hc j.2]
    simp [zsmul_eq_mul]
  · have h2 := congrArg Subtype.val (b.sum_repr ⟨y ⟨k₀, i⟩, Submodule.subset_span (Set.mem_range_self i)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    show y ⟨k₀, i⟩ = ∑ j : Ix (Fin _),
      ((b.repr ⟨y ⟨k₀, i⟩, Submodule.subset_span (Set.mem_range_self i)⟩ j.2 : ℤ) : Ω) * (b j.2 : Ω)
    conv_lhs => rw [← h2]
    simp [Fintype.sum_sigma, zsmul_eq_mul]
  · have h1 := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    refine h1.comp (fun j : Ix (Fin _) => j.2) ?_
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, a'⟩ h
    cases h
    rfl

end Lemmas

end BlockImageDatum

open BlockImageDatum

theorem BlockImageDatum.proof (hA : BlockImageArith.Statement) (hI : BlockImageInverse.Statement)
    (hZ : AnResNullForm.Statement) (hMet : BlockImageMetrics.Statement) (hC : BlockImageChi.Statement) :
    BlockImageDatum.Statement := by
  intro D K _ _ ι _ Ω _ _ d
  obtain ⟨r, M, N, x, hB, hx⟩ := exists_blockBasis d.y d.k₀
  have hN := N_injective hB hx
  obtain ⟨F, e, G, dG, hF, hFx, hG, hGP, hGF, hsurj, hJ, hinj⟩ :=
    hI D K ι Ω d.y d.k₀ r M N x d.J d.arith d.birat hB hx d.R.homog d.R.nondeg
  have hFne : ∀ u ∈ mcPts (ι := GlobalTheory (Fin r)) (coordIdeal ℤ x), u ∉ mcPts (Ideal.span {F}) →
      eval u (map (Int.castRingHom ℂ) F) ≠ 0 := fun u hu hnot h0 =>
    hnot (mem_mcPts_span_singleton hu.1 h0)
  let R' : AnRes (ι := GlobalTheory (Fin r)) (coordIdeal ℤ x) (Ideal.span {F}) D :=
    { homog := ⟨{F}, fun f hf => ⟨fun _ => e, by rw [Set.mem_singleton_iff.mp hf]; exact hF⟩, rfl⟩
      nondeg := fun h => hFx (h (Ideal.subset_span (Set.mem_singleton F)))
      X := d.R.X
      A := d.R.A
      U := d.R.U
      isOpen_U := d.R.isOpen_U
      mem_U := d.R.mem_U
      lift := fun a b => blockMapC d.k₀ M (d.R.lift a b)
      holo := fun a j c => by
        have e : ((fun b => blockMapC d.k₀ M (d.R.lift a b) j) ∘ ⇑(d.R.A.chart c).symm) =
            fun v => ∑ i ∈ Finset.univ, (fun i v => (M j i : ℂ) *
              ((fun b => d.R.lift a b ⟨d.k₀, i⟩) ∘ ⇑(d.R.A.chart c).symm) v) i v := rfl
        rw [e]
        exact Finset.analyticOnNhd_fun_sum _ fun i _ => analyticOnNhd_const.mul (d.R.holo a ⟨d.k₀, i⟩ c)
      mem := fun a b hb => blockMapC_mem hB (d.R.mem a b hb)
      compat := fun a a' b hb => sameOrbit_blockMapC M (d.R.compat a a' b hb)
      surj := fun u hu hnot => by
        obtain ⟨z, hz, hzJ, hzu⟩ := hsurj u hu (hFne u hu hnot)
        obtain ⟨a, ha⟩ := d.R.surj z hz hzJ
        exact ⟨a, sameOrbit_trans (sameOrbit_blockMapC M ha) hzu⟩
      inj := fun a a' hnot hsame => by
        have hm := d.R.mem a a (d.R.mem_U a)
        have hm' := d.R.mem a' a' (d.R.mem_U a')
        have hF0 := hFne _ (blockMapC_mem hB hm) hnot
        exact d.R.inj a a' (hJ _ hm hF0) (hinj _ hm _ hm' hF0 hsame)
      null := fun j => by
        refine measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono fun a ha => ?_))
          (hZ D K ι (mCoordIdeal d.y) d.J d.R G dG d.arith hG hGP j)
        change eval (d.R.lift a a) (map (Int.castRingHom ℂ) G) = 0
        rw [hGF]
        exact ha.2 F (Ideal.subset_span (Set.mem_singleton F)) }
  let d' : HSMDatum D Ω (Fin r) :=
    { x := x
      m := linPullMetric N hN
      P0 := ⊥
      J := Ideal.span {F}
      R := R'
      meas := d.meas
      borel := d.borel
      dV := d.dV
      one_le := d.one_le
      arith := hA D K ι Ω d.y d.k₀ r M N x d.arith d.birat hB hx
      indep := hx
      smooth := ((hMet.1 (ι d.k₀) (Fin r) N hN ⊥).1).mono fun z hz k => by
        obtain ⟨p, hp⟩ := Function.ne_iff.mp hz
        exact ⟨p.2, by cases k; exact hp⟩
      conjInv := fun u => by
        change (fsMetric (ι d.k₀)).ρ _ = (fsMetric (ι d.k₀)).ρ _
        rw [← ProjLine.isConjInvariant_fs (fun i => ∑ j, (N i j : ℂ) * u j)]
        congr 1
        funext i
        simp [map_sum]
      normalForm_baseLattice_le_dualSpan_sup_line := bot_le
      semipos := hMet.1 (ι d.k₀) (Fin r) N hN _
      vol := d.vol }
  let d₀ : HSMBlockDatum D K ι Ω :=
    { y := d.y
      k₀ := d.k₀
      A := HermLine.ofMetrics (fun k => fsMetric (ι k)) (unitDeg d.k₀)
      P0 := ⊥
      J := d.J
      R := d.R
      meas := d.meas
      borel := d.borel
      dV := d.dV
      one_le := d.one_le
      arith := d.arith
      birat := d.birat
      deg := rfl
      conjInv := fun z => Finset.prod_congr rfl fun k _ => by
        congr 1
        exact ProjLine.isConjInvariant_fs _
      normalForm_baseLattice_le_dualSpan_sup_line := bot_le
      semipos := hMet.2 K ι d.k₀ _
      vol := d.vol }
  have hh : ∀ z ∈ mcPts (mCoordIdeal d.y), d₀.A.h z = d'.m.ρ (blockMapC d.k₀ M z) := by
    intro z hz
    change ∏ k, (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) ^ (unitDeg d.k₀ k) =
      (fsMetric (ι d.k₀)).ρ (fun i => ∑ j, (N i j : ℂ) * blockMapC d.k₀ M z j)
    rw [Finset.prod_eq_single d.k₀ (fun k _ hk => by simp [unitDeg, hk]) (by simp)]
    simp only [unitDeg, if_true, zpow_one]
    congr 1
    funext i
    exact (blockMapC_N hB hz i).symm
  refine ⟨d₀, r, M, N, d', rfl, rfl, hB, hh, fun n => ?_⟩
  exact hC D K ι Ω d₀ r M N d' hB hh (fun g _ _ => rfl) n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
