import Development.WeilBound.CoreStatements.LocalThetaKernels.EvlLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

noncomputable section

open Matrix GlobalTheory.WeilM MeasureTheory ValuativeRel Topology Filter PositivityTheory.ThKH.Evl

namespace PositivityTheory.ThK.LinAct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ ι : Type} [Fintype κ] [Fintype ι] {ψ : AddChar k ℂ}

omit [Invertible (2 : k)] in

theorem norm_char (hc : Continuous ψ) (x : k) : ‖ψ x‖ = 1 := by
  have hle : ∀ y, ‖ψ y‖ ≤ 1 := fun y => by
    by_cases h0 : y = 0
    · simp [h0]
    obtain ⟨M, hM⟩ := (GlobalTheory.SplitWeil.isCompact_cball (Units.mk0 y h0)).exists_bound_of_continuousOn hc.continuousOn
    have hm : ∀ n : ℕ, n • y ∈ GlobalTheory.SplitWeil.cball (Units.mk0 y h0) := fun n => by
      induction n with
      | zero => simp [GlobalTheory.SplitWeil.cball]
      | succ n ih =>
        rw [succ_nsmul]
        exact GlobalTheory.SplitWeil.add_mem_cball ih (by simp [GlobalTheory.SplitWeil.cball])
    by_contra hy
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (not_le.1 hy)
    have := hM _ (hm n)
    rw [AddChar.map_nsmul_eq_pow, norm_pow] at this
    exact absurd hn (not_lt.2 this)
  have h1 : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
  refine le_antisymm (hle x) ?_
  calc (1 : ℝ) = ‖ψ x‖ * ‖ψ (-x)‖ := h1.symm
    _ ≤ ‖ψ x‖ * 1 := mul_le_mul_of_nonneg_left (hle _) (norm_nonneg _)
    _ = ‖ψ x‖ := mul_one _

theorem eventually_fix (hc : Continuous ψ) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), schr ψ w φ = φ := by
  have := nonarch_field k
  have hlc := isLocallyConstant_addChar ψ hc
  have h1 : IsLocallyConstant fun z : ((κ → k) × (κ → k)) × (κ → k) => schr ψ z.1 φ z.2 - φ z.2 := by
    refine IsLocallyConstant.sub (IsLocallyConstant.mul ?_ ?_) (hφ.1.comp_continuous continuous_snd)
    · exact hlc.comp_continuous ((continuous_snd.dotProduct continuous_fst.snd).add
        (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd)))
    · exact hφ.1.comp_continuous (continuous_snd.add continuous_fst.fst)
  have h2 : IsLocallyConstant fun z : ((κ → k) × (κ → k)) × (κ → k) => φ (z.2 - z.1.1) - φ z.2 :=
    (hφ.1.comp_continuous (continuous_snd.sub continuous_fst.fst)).sub (hφ.1.comp_continuous continuous_snd)
  have hK : IsCompact (tsupport φ) := hφ.2
  have e1 := hK.eventually_forall_of_forall_eventually (x₀ := (0 : (κ → k) × (κ → k)))
    (P := fun w x => schr ψ w φ x - φ x = 0) fun y _ => by
      simpa [schr] using h1.eventually_eq (0, y)
  have e2 := hK.eventually_forall_of_forall_eventually (x₀ := (0 : (κ → k) × (κ → k)))
    (P := fun w x => φ (x - w.1) - φ x = 0) fun y _ => by
      simpa using h2.eventually_eq (0, y)
  filter_upwards [e1, e2] with w a1 a2
  funext x
  by_cases hx : x ∈ tsupport φ
  · exact sub_eq_zero.1 (a1 x hx)
  have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have h3 : φ (x + w.1) = 0 := by
    by_cases hy : x + w.1 ∈ tsupport φ
    · have := a2 _ hy
      rw [add_sub_cancel_right, h0, zero_sub, neg_eq_zero] at this
      exact this
    · exact image_eq_zero_of_notMem_tsupport hy
  rw [schr, h3, h0, mul_zero]

omit [Invertible (2 : k)] in

theorem exists_compact_ann (hc : Continuous ψ) (h1 : ψ ≠ 1) {U : Set (ι → k)} (hU : U ∈ 𝓝 (0 : ι → k)) :
    ∃ C : Set (ι → k), IsCompact C ∧ ∀ x, (∀ y ∈ U, ψ (x ⬝ᵥ y) = 1) → x ∈ C := by
  classical
  obtain ⟨u, hu⟩ := (GlobalTheory.CompanionTheory.VacLoc.GoodInh.exists_goodChar k).2 ψ hc (norm_char hc) h1
  have : ∀ i, ∃ v : kˣ, ∀ y ∈ 𝒪[k], Pi.single i ((v : k) * y) ∈ U := fun i =>
    hu.basis ((fun t => (Pi.single i t : ι → k)) ⁻¹' U)
      ((continuous_single (A := fun _ => k) i).continuousAt.preimage_mem_nhds (by simpa using hU))
  choose v hv using this
  refine ⟨Set.univ.pi fun i => (fun t => (u : k) * ((v i)⁻¹ : kˣ) * t) '' (𝒪[k] : Set k),
    isCompact_univ_pi fun i => hu.compact.image (continuous_const.mul continuous_id), fun x hx i _ => ?_⟩
  refine ⟨_, (hu.ann (x i * v i)).1 fun y hy => ?_, ?_⟩
  · simpa [mul_assoc] using hx _ (hv i y hy)
  · simp only [Units.val_inv_eq_inv_val]
    field_simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem schr_add {w w' : (κ → k) × (κ → k)} (h : w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (φ : (κ → k) → ℂ) :
    schr ψ w (schr ψ w' φ) = schr ψ (w + w') φ := by
  rw [schr_schr, h, sub_self, mul_zero, AddChar.map_zero_eq_one, one_smul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem schr_comm (w w' : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) • schr ψ w' (schr ψ w φ) := by
  rw [schr_schr, schr_schr, smul_smul, ← AddChar.map_add_eq_mul, add_comm w]
  congr 2
  have h2 : ⅟(2 : k) * 2 = 1 := invOf_mul_self _
  linear_combination (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) * h2

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] in

theorem exists_section (large₂ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (hdim : Module.finrank k large₂ = Fintype.card κ)
    (X : (ι → k) →ₗ[k] (κ → k) × (κ → k)) (hXL : ∀ x, X x ∈ large₂ → x = 0) :
    ∃ S : (ι → k) →ₗ[k] (κ → k) × (κ → k), (∀ y, S y ∈ large₂) ∧
      ∀ x y, (X x).1 ⬝ᵥ (S y).2 - (S y).1 ⬝ᵥ (X x).2 = x ⬝ᵥ y := by
  classical
  let B : (ι → k) →ₗ[k] large₂ →ₗ[k] k :=
    LinearMap.mk₂ k (fun x a => (X x).1 ⬝ᵥ a.1.2 - a.1.1 ⬝ᵥ (X x).2)
      (fun a b c => by simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun a b c => by
        simp only [map_smul, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
      (fun a b c => by simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun a b c => by
        simp only [Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
  have hinj : Function.Injective B := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine hXL x (mem_of_orth large₂ hiso hdim _ fun w hw => ?_)
    exact (sub_eq_zero.1 (LinearMap.congr_fun hx ⟨w, hw⟩)).symm
  have hs : Function.Surjective B.flip := LinearMap.flip_surjective_iff₁.2 hinj
  obtain ⟨s, hs'⟩ := B.flip.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hs)
  refine ⟨large₂.subtype ∘ₗ s ∘ₗ (dotProductBilin k k), fun y => (s _).2, fun x y => ?_⟩
  have := LinearMap.congr_fun (LinearMap.congr_fun hs' (dotProductBilin k k y)) x
  rw [dotProduct_comm x y]
  exact this

theorem coeff_mem (hc : Continuous ψ) (h1 : ψ ≠ 1) (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ)
    (X S : (ι → k) →ₗ[k] (κ → k) × (κ → k)) (hX : ∀ x x', (X x).1 ⬝ᵥ (X x').2 = (X x').1 ⬝ᵥ (X x).2)
    (hS : ∀ y, ∀ φ ∈ SB (κ → k), l (schr ψ (S y) φ) = l φ)
    (hXS : ∀ x y, (X x).1 ⬝ᵥ (S y).2 - (S y).1 ⬝ᵥ (X x).2 = x ⬝ᵥ y) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    (fun x => l (schr ψ (X x) φ)) ∈ SB (ι → k) := by
  have := t2Space_local_field_bis (k := k)
  have cX : Continuous X := X.continuous_on_pi
  have cS : Continuous S := S.continuous_on_pi
  have hf := eventually_fix (ψ := ψ) hc hφ
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have ht : Tendsto (fun y => X (y - x)) (𝓝 x) (𝓝 0) :=
      (cX.comp (continuous_id.sub continuous_const)).tendsto' _ _ (by simp)
    filter_upwards [ht.eventually hf] with y hy
    conv_rhs => rw [← hy, schr_add (hX _ _), ← map_add, add_sub_cancel]
  · obtain ⟨C, hC, h⟩ := exists_compact_ann (ι := ι) hc h1 ((cS.tendsto' 0 0 (map_zero S)).eventually hf)
    refine HasCompactSupport.intro hC fun x hx => ?_
    by_contra hne
    refine hx (h x fun y hy => ?_)
    have e := congrArg l (schr_comm (ψ := ψ) (X x) (S y) φ)
    have hy' : schr ψ (S y) φ = φ := hy
    rw [hy', map_smul, hS y _ (schr_mem hc _ hφ), hXS, smul_eq_mul] at e
    exact (mul_eq_right₀ hne).1 e.symm

theorem exists_avg [DecidableEq ι] (hc : Continuous ψ) (h1 : ψ ≠ 1) (large₂ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (hdim : Module.finrank k large₂ = Fintype.card κ)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w ∈ large₂, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ) (hne : ∃ φ ∈ SB (κ → k), l φ ≠ 0)
    (X : (ι → k) →ₗ[k] (κ → k) × (κ → k)) (hX : ∀ x x', (X x).1 ⬝ᵥ (X x').2 = (X x').1 ⬝ᵥ (X x).2)
    (hXL : ∀ x, X x ∈ large₂ → x = 0) :
    ∃ L : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∃ φ ∈ SB (κ → k), L φ ≠ 0) ∧
      (∀ x, ∀ φ ∈ SB (κ → k), L (schr ψ (X x) φ) = L φ) ∧
      (∀ a ∈ large₂, (∀ x, (X x).1 ⬝ᵥ a.2 = a.1 ⬝ᵥ (X x).2) → ∀ φ ∈ SB (κ → k), L (schr ψ a φ) = L φ) ∧
      ∀ (T : Module.End ℂ ((κ → k) → ℂ)) (g : GL ι k) (a : ℂ), (∀ φ ∈ SB (κ → k), T φ ∈ SB (κ → k)) →
        (∀ x, ∀ φ ∈ SB (κ → k), T (schr ψ (X x) φ) = schr ψ (X (g.val *ᵥ x)) (T φ)) →
        (∀ φ ∈ SB (κ → k), l (T φ) = a * l φ) →
        ∀ φ ∈ SB (κ → k), L (T φ) = ((distribHaarChar k (GeneralLinearGroup.det g) : ℝ) : ℂ) * a * L φ := by
  have := t2Space_local_field_bis (k := k)
  borelize k
  have := GlobalTheory.SplitWeil.secondCountable k
  obtain ⟨S, hSL, hXS⟩ := exists_section large₂ hiso hdim X hXL
  have hS : ∀ y, ∀ φ ∈ SB (κ → k), l (schr ψ (S y) φ) = l φ := fun y => hl _ (hSL y)
  have hF := fun φ hφ => coeff_mem hc h1 l X S hX hS hXS (φ := φ) hφ
  set μ : Measure (ι → k) := Measure.pi fun _ => (Measure.addHaar : Measure k) with hμ
  have hint : ∀ f ∈ SB (ι → k), Integrable f μ := fun f hf => hf.1.continuous.integrable_of_hasCompactSupport hf.2
  let I₀ : SB (ι → k) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, f.1 x ∂μ
      map_add' := fun a b => integral_add (hint _ a.2) (hint _ b.2)
      map_smul' := fun c a => integral_smul c a.1 }
  obtain ⟨I, hI⟩ := I₀.exists_extend
  have hI' : ∀ f ∈ SB (ι → k), I f = ∫ x, f x ∂μ := fun f hf => LinearMap.congr_fun hI ⟨f, hf⟩
  let P : ((κ → k) → ℂ) →ₗ[ℂ] ((ι → k) → ℂ) :=
    { toFun := fun φ x => l (schr ψ (X x) φ)
      map_add' := fun a b => funext fun x => by
        rw [Pi.add_apply, ← map_add]; congr 1; funext z; simp [schr, mul_add]
      map_smul' := fun c a => funext fun x => by
        rw [RingHom.id_apply, Pi.smul_apply, ← map_smul]; congr 1; funext z; simp [schr, mul_left_comm] }
  have hL : ∀ φ ∈ SB (κ → k), (I ∘ₗ P) φ = ∫ x, l (schr ψ (X x) φ) ∂μ := fun φ hφ => hI' _ (hF φ hφ)
  refine ⟨I ∘ₗ P, ?_, fun x φ hφ => ?_, fun a ha h φ hφ => ?_, fun T g a hT hg ha φ hφ => ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨φ, hφ, h0⟩ := hne
    have hz := cyc hc (norm_char hc) h1 (hF φ hφ) (fun h => h0 (by
      have e0 : schr ψ 0 φ = φ := by funext z; simp [schr]
      simpa [e0] using congrFun h 0)) I fun w => by
      have e := hcon _ (schr_mem hc (S w.2) (schr_mem hc (X w.1) hφ))
      have e2 : schr ψ w (fun x => l (schr ψ (X x) φ)) =
          ψ (⅟(2 : k) * (w.1 ⬝ᵥ w.2)) • P (schr ψ (S w.2) (schr ψ (X w.1) φ)) := by
        funext x
        show _ = ψ _ * l (schr ψ (X x) (schr ψ (S w.2) (schr ψ (X w.1) φ)))
        rw [schr_comm, map_smul, hS _ _ (schr_mem hc _ (schr_mem hc _ hφ)), hXS, schr_add (hX _ _), ← map_add, schr,
          AddChar.map_add_eq_mul, smul_eq_mul]
        ring
      rw [e2, map_smul]
      exact smul_eq_zero_of_right _ e
    obtain ⟨U, -, hU⟩ := exists_subgroup (k := k) ι
    have h2 := hz _ hU
    rw [hI' _ hU] at h2
    have h3 := congrArg Complex.re h2
    rw [← RCLike.re_to_complex, ← integral_re (hint _ hU)] at h3
    refine ne_of_gt ?_ h3
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      (RCLike.continuous_re.comp hU.1.continuous) (hU.2.comp_left (g := RCLike.re) (map_zero _)) (fun t => ?_) ?_
    · by_cases ht : t ∈ U <;> simp [ht]
    · simp [U.zero_mem]
  · rw [hL _ (schr_mem hc _ hφ), hL _ hφ]
    simp only [schr_add (hX _ _), ← map_add]
    exact integral_add_right_eq_self (fun t => l (schr ψ (X t) φ)) x
  · rw [hL _ (schr_mem hc _ hφ), hL _ hφ]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show l _ = l _
    rw [schr_comm, h, sub_self, AddChar.map_zero_eq_one, one_smul, hl a ha _ (schr_mem hc _ hφ)]
  · rw [hL _ (hT _ hφ), hL _ hφ, ← integral_comp_mulVec _ g, mul_assoc, ← integral_const_mul a]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show l _ = _
    rw [← hg x φ hφ, ha _ (schr_mem hc _ hφ)]

end PositivityTheory.ThK.LinAct
