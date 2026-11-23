import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalVolumeGrowth

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec.TorusModulus

theorem linear_of_le (L : ℝ →+ ℝ) (A K : ℝ) (h : ∀ s, L s ≤ A + K * |s|) :
    ∃ κ : ℝ, |κ| ≤ K ∧ ∀ s, L s = κ * s := by

  have hup : ∀ s, L s ≤ K * |s| := by
    intro s
    by_contra hlt
    push_neg at hlt
    have hpos : 0 < L s - K * |s| := by linarith
    obtain ⟨m, hm⟩ := exists_nat_gt (A / (L s - K * |s|))
    have hA : A < (m : ℝ) * (L s - K * |s|) := by rwa [div_lt_iff₀ hpos] at hm
    have hm1 := h ((m : ℝ) * s)
    have hlin : L ((m : ℝ) * s) = (m : ℝ) * L s := by
      have := map_nsmul L m s
      rwa [nsmul_eq_mul, nsmul_eq_mul] at this
    rw [hlin, abs_mul, Nat.abs_cast] at hm1
    nlinarith
  have habs : ∀ s, |L s| ≤ K * |s| := by
    intro s
    refine abs_le.2 ⟨?_, hup s⟩
    have := hup (-s)
    rw [map_neg, abs_neg] at this
    linarith
  have hcont : Continuous L :=
    AddMonoidHomClass.continuous_of_bound L K (fun s => by simpa only [Real.norm_eq_abs] using habs s)
  refine ⟨L 1, by simpa using habs 1, fun s => ?_⟩
  have hs := map_real_smul L hcont s 1
  rw [smul_eq_mul, mul_one, smul_eq_mul] at hs
  rw [hs, mul_comm]

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem eq_smul_map (N : Subgroup G) (hN : IsClosed (N : Set G)) {ν : Measure G}
    (h : IsHaarSub (N : Set G) ν) (μ : Measure N) [μ.IsHaarMeasure] :
    ∃ c : NNReal, ν = c • μ.map Subtype.val := by
  obtain ⟨hne, hfin, hnull, hinv⟩ := h
  have hemb : MeasurableEmbedding (Subtype.val : N → G) := MeasurableEmbedding.subtype_coe hN.measurableSet
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  haveI : BorelSpace N := Subtype.borelSpace (N : Set G)
  set ν₀ : Measure N := ν.comap Subtype.val with hν₀

  have hback : ν₀.map Subtype.val = ν := by
    rw [hν₀, hemb.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (measure_mono_null (fun x hx => ?_) hnull))
    intro hxN
    exact hx ⟨⟨x, hxN⟩, rfl⟩
  have hcomap : ∀ ρ : Measure N, (ρ.map Subtype.val).comap Subtype.val = ρ := fun ρ => hemb.comap_map ρ
  haveI : Measure.IsMulLeftInvariant ν₀ := ⟨fun g => by
    rw [← hcomap (ν₀.map (g * ·)), Measure.map_map hemb.measurable (measurable_const_mul g)]
    have hfun : (Subtype.val ∘ fun x : N => g * x) = (fun y : G => (g : G) * y) ∘ Subtype.val := rfl
    rw [hfun, ← Measure.map_map (measurable_const_mul (g : G)) hemb.measurable, hback, hinv g g.2, ← hback,
      hcomap]⟩
  haveI : IsFiniteMeasureOnCompacts ν₀ := ⟨fun K hK => by
    rw [hν₀, hemb.comap_apply]
    haveI := hfin
    exact (hK.image continuous_subtype_val).measure_lt_top⟩
  refine ⟨Measure.haarScalarFactor ν₀ μ, ?_⟩
  have hsm := Measure.isMulLeftInvariant_eq_smul ν₀ μ
  calc ν = ν₀.map Subtype.val := hback.symm
    _ = (Measure.haarScalarFactor ν₀ μ • μ).map Subtype.val := congrArg (Measure.map Subtype.val) hsm
    _ = Measure.haarScalarFactor ν₀ μ • μ.map Subtype.val := Measure.map_smul _ _ _

theorem exists_exp_smul (N : Subgroup G) (hN : IsClosed (N : Set G)) {ν ν' : Measure G}
    (h : IsHaarSub (N : Set G) ν) (h' : IsHaarSub (N : Set G) ν') :
    ∃ t : ℝ, ν' = ENNReal.ofReal (Real.exp t) • ν := by
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  obtain ⟨c, hc⟩ := eq_smul_map N hN h (Measure.haar)
  obtain ⟨c', hc'⟩ := eq_smul_map N hN h' (Measure.haar)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact h.1 (by rw [hc, zero_smul])
  have hc0' : c' ≠ 0 := by
    rintro rfl
    exact h'.1 (by rw [hc', zero_smul])
  have hpos : 0 < (c' : ℝ) / c :=
    div_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc0')) (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc0))
  refine ⟨Real.log ((c' : ℝ) / c), ?_⟩
  rw [Real.exp_log hpos, ← NNReal.coe_div, ENNReal.ofReal_coe_nnreal, hc, hc']
  ext s _
  simp only [ENNReal.smul_def, Measure.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← ENNReal.coe_mul, div_mul_cancel₀ _ hc0]

omit [LocallyCompactSpace G] [SecondCountableTopology G] in

theorem isHaarSub_conj {N : Set G} {ν : Measure G} (hν : IsHaarSub N ν) (g : G)
    (h1 : ∀ m ∈ N, g * m * g⁻¹ ∈ N) (h2 : ∀ m ∈ N, g⁻¹ * m * g ∈ N) :
    IsHaarSub N (ν.map fun m => g * m * g⁻¹) := by
  obtain ⟨hne, hfin, hnull, hinv⟩ := hν
  let e : G ≃ᵐ G := (MeasurableEquiv.mulLeft g).trans (MeasurableEquiv.mulRight g⁻¹)
  have he : (fun m => g * m * g⁻¹) = (e : G → G) := rfl
  rw [he]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    exact hne ((Measure.map_eq_zero_iff e.measurable.aemeasurable).1 h0)
  · refine ⟨fun K hK => ?_⟩
    haveI := hfin
    rw [e.map_apply]
    have hc : IsCompact ((fun x => g⁻¹ * x * g) '' K) := hK.image (by fun_prop)
    refine lt_of_le_of_lt (measure_mono fun x hx => ?_) hc.measure_lt_top
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    show g⁻¹ * (g * x * g⁻¹) * g = x
    group
  · rw [e.map_apply]
    refine measure_mono_null (fun x hx => ?_) hnull
    intro hxN
    exact hx (h1 x hxN)
  · intro m hm
    rw [Measure.map_map (measurable_const_mul m) e.measurable]
    have hcomp : (fun x => m * x) ∘ e = e ∘ (fun x => (g⁻¹ * m * g) * x) := by
      funext x
      show m * (g * x * g⁻¹) = g * ((g⁻¹ * m * g) * x) * g⁻¹
      group
    rw [hcomp, ← Measure.map_map e.measurable (measurable_const_mul _), hinv _ (h2 m hm)]

private theorem eq_of_exp_smul_measure_eq {X : Type} [MeasurableSpace X] {ν : Measure X} {S : Set X} (h0 : ν S ≠ 0)
    (htop : ν S ≠ ⊤) {t t' : ℝ} (h : ENNReal.ofReal (Real.exp t) • ν = ENNReal.ofReal (Real.exp t') • ν) :
    t = t' := by
  have h1 := congrArg (fun ρ : Measure X => (ρ S).toReal) h
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at h1
  exact Real.exp_injective (mul_right_cancel₀ (ENNReal.toReal_pos h0 htop).ne' h1)

theorem modulus (N : Subgroup G) (hN : IsClosed (N : Set G)) {ν : Measure G} (hν : IsHaarSub (N : Set G) ν)
    (a : ℝ → G) (ha : ∀ s t, a (s + t) = a s * a t) (hn : ∀ s, ∀ m ∈ (N : Set G), a s * m * (a s)⁻¹ ∈ (N : Set G))
    (d : G → ℝ) (hmul : ∀ x y, d (x * y) ≤ d x + d y) (hd : ∀ s, d (a s) ≤ |s|)
    (C c : ℝ) (hv : ∀ r : ℝ, 0 ≤ r → ν {m | d m ≤ r} ≤ ENNReal.ofReal (C * Real.exp (c * r))) :
    ∃ κ : ℝ, |κ| ≤ 2 * c ∧ ∀ s, ν.map (fun m => a s * m * (a s)⁻¹) = ENNReal.ofReal (Real.exp (κ * s)) • ν := by

  have a0 : a 0 = 1 := by
    have h := ha 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one (a 0)).symm)
  have aneg : ∀ s, a (-s) = (a s)⁻¹ := by
    intro s
    have h := ha s (-s)
    rw [add_neg_cancel, a0] at h
    exact eq_inv_of_mul_eq_one_right h.symm

  let e : ℝ → G ≃ᵐ G := fun s => (MeasurableEquiv.mulLeft (a s)).trans (MeasurableEquiv.mulRight (a s)⁻¹)
  have he : ∀ s, (e s : G → G) = fun m => a s * m * (a s)⁻¹ := fun s => rfl
  have hconj : ∀ s, IsHaarSub (N : Set G) (ν.map (e s)) := by
    intro s
    rw [he s]
    refine isHaarSub_conj hν (a s) (hn s) (fun m hm => ?_)
    have := hn (-s) m hm
    rwa [aneg, inv_inv] at this
  choose T hT using fun s => exists_exp_smul N hN hν (hconj s)

  obtain ⟨r0, hr0⟩ : ∃ k : ℕ, ν {m | d m ≤ (k : ℝ)} ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hν.1
    rw [← Measure.measure_univ_eq_zero]
    have hU : (Set.univ : Set G) = ⋃ k : ℕ, {m | d m ≤ (k : ℝ)} := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
      exact exists_nat_ge (d x)
    rw [hU]
    exact measure_iUnion_null hcon
  set S := {m | d m ≤ (r0 : ℝ)} with hS
  have hStop : ν S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hv r0 (Nat.cast_nonneg r0))

  have hcomp : ∀ s t, (e (s + t) : G → G) = (e s) ∘ (e t) := by
    intro s t
    funext m
    show a (s + t) * m * (a (s + t))⁻¹ = a s * (a t * m * (a t)⁻¹) * (a s)⁻¹
    rw [ha]
    group
  have hadd : ∀ s t, T (s + t) = T s + T t := by
    intro s t
    apply eq_of_exp_smul_measure_eq hr0 hStop
    rw [← hT (s + t), hcomp, ← Measure.map_map (e s).measurable (e t).measurable, hT t, Measure.map_smul, hT s,
      smul_smul, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_comm (T t) (T s)]

  have hm0 : 0 < (ν S).toReal := ENNReal.toReal_pos hr0 hStop
  have hbound : ∀ s, T s ≤ (Real.log C + c * r0 - Real.log (ν S).toReal) + 2 * c * |s| := by
    intro s
    have hsub : (e s) ⁻¹' S ⊆ {m | d m ≤ (r0 : ℝ) + 2 * |s|} := by
      intro x hx
      have hx' : d (a s * x * (a s)⁻¹) ≤ (r0 : ℝ) := hx
      have hrep : a (-s) * (a s * x * (a s)⁻¹) * a s = x := by
        rw [aneg]
        group
      have h1 := hmul (a (-s) * (a s * x * (a s)⁻¹)) (a s)
      have h2 := hmul (a (-s)) (a s * x * (a s)⁻¹)
      have h3 := hd (-s)
      have h4 := hd s
      rw [abs_neg] at h3
      rw [hrep] at h1
      show d x ≤ (r0 : ℝ) + 2 * |s|
      linarith
    have hle : ν.map (e s) S ≤ ENNReal.ofReal (C * Real.exp (c * ((r0 : ℝ) + 2 * |s|))) := by
      rw [(e s).map_apply]
      exact (measure_mono hsub).trans (hv _ (by positivity))
    rw [hT s, Measure.smul_apply, smul_eq_mul, ← ENNReal.ofReal_toReal hStop,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le] at hle
    have hpos : 0 < Real.exp (T s) * (ν S).toReal := mul_pos (Real.exp_pos _) hm0
    have hle' : Real.exp (T s) * (ν S).toReal ≤ C * Real.exp (c * ((r0 : ℝ) + 2 * |s|)) := by
      rcases (ENNReal.ofReal_le_ofReal_iff').1 hle with h | h
      · exact h
      · linarith
    have hC : 0 < C := by
      by_contra hC
      push_neg at hC
      nlinarith [Real.exp_pos (c * ((r0 : ℝ) + 2 * |s|))]
    have hlog := Real.log_le_log hpos hle'
    rw [Real.log_mul (Real.exp_pos _).ne' hm0.ne', Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_exp] at hlog
    have hexp : c * ((r0 : ℝ) + 2 * |s|) = c * r0 + 2 * c * |s| := by ring
    rw [hexp] at hlog
    linarith
  let L : ℝ →+ ℝ := AddMonoidHom.mk' T hadd
  obtain ⟨κ, hκ, hL⟩ := linear_of_le L _ (2 * c) (fun s => hbound s)
  refine ⟨κ, hκ, fun s => ?_⟩
  have h1 := hT s
  rw [he s] at h1
  have hTs : T s = κ * s := hL s
  rw [h1, hTs]

end General

theorem torus_modulus : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ (a : ℝ → UJ ε) (Hm : Matrix (Fin n) (Fin n) ℂ), inP ε Hm → (∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • Hm)) → (∀ s, dOp (umat (a s)) ≤ |s|) → (∀ s, ∀ m ∈ NW ε W, a s * m * (a s)⁻¹ ∈ NW ε W) → ∃ κ : ℝ, |κ| ≤ 8 * n * rkR ε ∧ ∀ s, ν.map (fun m => a s * m * (a s)⁻¹) = ENNReal.ofReal (Real.exp (κ * s)) • ν := by
  intro n ε W ν hW hν a Hm hP ha hd hn
  have hN : IsClosed ((nwSub ε W : Subgroup (UJ ε)) : Set (UJ ε)) := by
    rw [coe_nwSub]
    exact isClosed_NW ε W
  have hν' : IsHaarSub ((nwSub ε W : Subgroup (UJ ε)) : Set (UJ ε)) ν := by
    rw [coe_nwSub]
    exact hν
  have hn' : ∀ s, ∀ m ∈ ((nwSub ε W : Subgroup (UJ ε)) : Set (UJ ε)),
      a s * m * (a s)⁻¹ ∈ ((nwSub ε W : Subgroup (UJ ε)) : Set (UJ ε)) := by
    rw [coe_nwSub]
    exact hn

  have hadd : ∀ s t, a (s + t) = a s * a t := by
    intro s t
    apply Subtype.ext
    apply Units.ext
    show umat (a (s + t)) = umat (a s) * umat (a t)
    rw [ha, ha, ha, Complex.ofReal_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl Hm).smul_left (s : ℂ)).smul_right (t : ℂ))

  have hmul : ∀ x y : UJ ε, dOp (umat (x * y)) ≤ dOp (umat x) + dOp (umat y) := by
    intro x y
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hz : ∀ g : Matrix (Fin 0) (Fin 0) ℂ, dOp g = 0 := by
        intro g
        rw [Subsingleton.elim g 0]
        simp [dOp]
      rw [hz, hz, hz]
      norm_num
    · have e : umat (x * y) = umat x * umat y := rfl
      rw [e]
      exact GlobalTheory.Count.Cartan.dOp_mul_le hpos (Units.isUnit _) (Units.isUnit _)
  obtain ⟨⟨C, hC⟩, -⟩ := GlobalTheory.RadVol.radical_volume_growth n ε W ν hW hν
  obtain ⟨κ, hκ, hmod⟩ := modulus (nwSub ε W) hN hν' a hadd hn' (fun g => dOp (umat g)) hmul hd C
    (4 * n * rkR ε) hC
  refine ⟨κ, ?_, hmod⟩
  calc |κ| ≤ 2 * (4 * n * rkR ε) := hκ
    _ = 8 * n * rkR ε := by ring

end GlobalTheory.Dec.TorusModulus
