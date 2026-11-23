import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CountableOfIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsHermOfMemLZ

namespace GlobalTheory.MaxCusp

open NumberField Complex MeasureTheory Module ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

section Space

variable (ι : Type) (d : ℕ)

def hermSub : Submodule ℝ (ι → Fin d → Fin d → ℂ) where
  carrier := {b | IsHerm b}
  add_mem' {a b} ha hb τ i k := by simp only [Pi.add_apply, map_add, ha τ i k, hb τ i k]
  zero_mem' τ i k := by simp
  smul_mem' c b hb τ i k := by
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, hb τ i k]

def hermEquiv : hermSub ι d ≃ₗ[ℝ] (ι → Fin d → Fin d → ℝ) where
  toFun b τ i k := (b.1 τ i k).re + (b.1 τ i k).im
  map_add' a b := by funext τ i k; simp; ring
  map_smul' c b := by funext τ i k; simp; ring
  invFun y := ⟨fun τ i k => ⟨(y τ i k + y τ k i) / 2, (y τ i k - y τ k i) / 2⟩, fun τ i k => by
    apply Complex.ext <;> simp <;> ring⟩
  left_inv b := by
    apply Subtype.ext
    funext τ i k
    have := b.2 τ i k
    apply Complex.ext <;> simp [this] <;> ring
  right_inv y := by funext τ i k; simp; ring

theorem finrank_hermSub [Fintype ι] : finrank ℝ (hermSub ι d) = d * d * Fintype.card ι := by
  rw [(hermEquiv ι d).finrank_eq]
  simp [Module.finrank_pi_fintype]
  ring

variable {ι d}

def hermSingle (i0 k0 : Fin d) : (ι → ℂ) →ₗ[ℝ] hermSub ι d where
  toFun z := ⟨fun τ i k => (if i = i0 ∧ k = k0 then z τ else 0) +
      (if k = i0 ∧ i = k0 then conj (z τ) else 0), fun τ i k => by
    simp only [map_add, apply_ite conj, map_zero, Complex.conj_conj, add_comm]⟩
  map_add' z w := by
    apply Subtype.ext; funext τ i k
    simp only [Pi.add_apply, map_add, Submodule.coe_add]
    split_ifs <;> ring
  map_smul' c z := by
    apply Subtype.ext; funext τ i k
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, RingHom.id_apply,
      Submodule.coe_smul]
    split_ifs <;> ring

theorem sum_hermSingle (b : hermSub ι d) :
    b = ∑ i0, ∑ k0, hermSingle i0 k0 (fun τ => b.1 τ i0 k0 / 2) := by
  apply Subtype.ext
  funext τ i k
  simp only [Submodule.coe_sum, Finset.sum_apply, hermSingle, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_add_distrib, ite_and]
  simp [b.2 τ k i, map_ofNat]

end Space

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ} (X : Data E r)

theorem span_emb_int : Submodule.span ℝ {z : X.Ψ → ℂ | ∃ γ : E, IsIntegral ℤ γ ∧
    z = fun τ => τ.1 γ} = ⊤ := by
  set V := Submodule.span ℝ {z : X.Ψ → ℂ | ∃ γ : E, IsIntegral ℤ γ ∧ z = fun τ => τ.1 γ}
  have key : ∀ η : E, IsIntegral ℤ η → ∀ p : X.Ψ → ℝ, (fun τ : X.Ψ => τ.1 η * p τ) ∈ V := by
    intro η hη p
    have hp : p ∈ Submodule.span ℝ {p : X.Ψ → ℝ | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧
      p = fun τ => (τ.1 a).re} := by rw [FourierCoefficientLattice.span_fixed_integral_real_parts]; trivial
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, hai, rfl⟩ := hx
      refine Submodule.subset_span ⟨η * a, hη.mul hai, funext fun τ => ?_⟩
      rw [map_mul, ← RealEmbeddingCharacters.emb_real ha]
    | zero => convert V.zero_mem using 1; funext τ; simp
    | add x y _ _ hx hy => convert V.add_mem hx hy using 1; funext τ; simp [mul_add]
    | smul c x _ hx => convert V.smul_mem c hx using 1; funext τ; simp; ring
  obtain ⟨η, hηcc, hηi, hηne⟩ : ∃ η : E, cc η = -η ∧ IsIntegral ℤ η ∧ η ≠ 0 := by
    have halg : IsAlgebraic ℤ X.ξ0 :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic X.ξ0)
    obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
    refine ⟨k • X.ξ0, ?_, hki, smul_ne_zero hk X.ξ0_ne⟩
    rw [show cc (k • X.ξ0) = k • cc X.ξ0 from map_zsmul _ k _, X.ξ0_im, smul_neg]
  have hre : ∀ τ : E →+* ℂ, (τ η).re = 0 := fun τ => by
    have h := emb_cc τ η
    rw [hηcc, map_neg] at h
    have := congrArg Complex.re h
    simp at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ η).im ≠ 0 := fun τ h =>
    hηne ((map_eq_zero τ).1 (Complex.ext (hre τ) h))
  refine eq_top_iff.2 fun z _ => ?_
  convert V.add_mem (key 1 isIntegral_one fun τ => (z τ).re)
    (key η hηi fun τ => (z τ).im / (τ.1 η).im) using 1
  funext τ
  have := him τ.1
  apply Complex.ext
  · simp only [Pi.add_apply, map_one, one_mul, add_re, ofReal_re, mul_re, hre, ofReal_im]; ring
  · simp only [Pi.add_apply, map_one, one_mul, add_im, ofReal_re, mul_im, hre, ofReal_im]
    field_simp
    ring

def latZ (d g : ℕ) : Submodule ℤ (hermSub X.Ψ d) :=
  AddSubgroup.toIntSubmodule
  { carrier := {b | b.1 ∈ LZ X d g}
    add_mem' := by
      rintro a b ⟨β, hβ, hγ, e1⟩ ⟨β', hβ', hγ', e2⟩
      refine ⟨β + β', fun i k => ?_, fun i k => ?_, ?_⟩
      · show cc (β i k + β' i k) = β k i + β' k i
        rw [RealEmbeddingCharacters.cc_add', hβ, hβ']
      · obtain ⟨γ, hγi, e⟩ := hγ i k
        obtain ⟨γ', hγi', e'⟩ := hγ' i k
        exact ⟨γ + γ', hγi.add hγi', by simp only [Matrix.add_apply, e, e']; ring⟩
      · rw [embH_add, ← e1, ← e2]; rfl
    zero_mem' := ⟨0, fun i k => by simp [cc], fun i k => ⟨0, isIntegral_zero, by simp⟩,
      by funext τ i k; simp [embH]⟩
    neg_mem' := by
      rintro a ⟨β, hβ, hγ, e1⟩
      refine ⟨-β, fun i k => ?_, fun i k => ?_, ?_⟩
      · show cc (-β i k) = -β k i
        rw [RealEmbeddingCharacters.cc_neg', hβ]
      · obtain ⟨γ, hγi, e⟩ := hγ i k
        exact ⟨-γ, hγi.neg, by simp only [Matrix.neg_apply, e]; ring⟩
      · funext τ i k; simp [embH, e1] }

theorem mem_latZ {g : ℕ} {b : hermSub X.Ψ d} : b ∈ latZ X d g ↔ b.1 ∈ LZ X d g := Iff.rfl

open FourierCoefficientLattice in
theorem finite_small {g : ℕ} (hg : 0 < g) : {y | y ∈ latZ X d g ∧ ‖y‖ < 1}.Finite := by
  set S := {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ 4}
  have hS : S.Finite := Embeddings.finite_of_norm_le E ℂ 4
  set T : Set (Matrix (Fin d) (Fin d) E) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (fun γ => cE g * γ) '' S
  have hT : T.Finite := Set.Finite.pi fun _ => Set.Finite.pi fun _ => hS.image _
  refine Set.Finite.of_finite_image (f := Subtype.val) ((hT.image fun β => embH X β).subset ?_)
    Subtype.val_injective.injOn
  rintro _ ⟨y, ⟨⟨β, hβ, hγ, e0⟩, hn⟩, rfl⟩
  refine ⟨β, fun i _ k _ => ?_, e0.symm⟩
  obtain ⟨γ, hγi, e⟩ := hγ i k
  refine ⟨γ, ⟨hγi, fun σ => ?_⟩, e.symm⟩
  have hb2 : ∀ τ : X.Ψ, ‖τ.1 (β i k)‖ < 1 := fun τ => by
    have := (norm_le_pi_norm (y.1 τ i) k).trans
      ((norm_le_pi_norm (y.1 τ) i).trans (norm_le_pi_norm y.1 τ))
    have h2 : y.1 τ i k = τ.1 (β i k) := by rw [e0]; rfl
    rw [← h2]
    exact this.trans_lt hn
  have hτ : ∀ τ : X.Ψ, ‖τ.1 γ‖ ≤ 4 := fun τ => by
    have h := hb2 τ
    rw [e, show ((g * dEnat E : ℕ) : E) / 2 * γ = cE g * γ from rfl, map_mul, norm_mul, emb_cE,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cr_pos g hg)] at h
    nlinarith [norm_nonneg (τ.1 γ), cr_ge (E := E) g hg]
  by_cases hσ : σ ∈ X.Ψ
  · exact hτ ⟨σ, hσ⟩
  · have := hτ ⟨_, (X.conj_mem_iff σ).2 hσ⟩
    simpa [ComplexEmbedding.conjugate_coe_eq] using this

theorem discrete_latZ {g : ℕ} (hg : 0 < g) : DiscreteTopology (latZ X d g) := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  set T := {y : hermSub X.Ψ d | y ∈ latZ X d g ∧ ‖y‖ < 1} \ {0}
  have hT : IsClosed T := ((finite_small X hg).subset Set.sdiff_subset).isClosed
  have h0 : (0 : hermSub X.Ψ d) ∈ Tᶜ := by simp [T]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hT.isOpen_compl 0 h0
  rw [Metric.isOpen_iff]
  intro q hq
  rw [Set.mem_singleton_iff] at hq
  subst hq
  refine ⟨min ε 1, lt_min hε one_pos, fun q hq => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hq
  rw [Set.mem_singleton_iff]
  apply Subtype.ext
  have hq' : ‖(q : hermSub X.Ψ d)‖ < min ε 1 := hq
  by_contra hne
  have hmem : (q : hermSub X.Ψ d) ∈ T := ⟨⟨q.2, lt_of_lt_of_le hq' (min_le_right _ _)⟩, hne⟩
  have : (q : hermSub X.Ψ d) ∈ Metric.ball (0 : hermSub X.Ψ d) ε := by
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hq' (min_le_left _ _)
  exact hball this hmem

open FourierCoefficientLattice in
theorem span_latZ {g : ℕ} (hg : 0 < g) :
    Submodule.span ℝ (latZ X d g : Set (hermSub X.Ψ d)) = ⊤ := by
  set Sp := Submodule.span ℝ (latZ X d g : Set (hermSub X.Ψ d))
  have hcr := cr_pos (E := E) g hg
  have key : ∀ (i0 k0 : Fin d) (z : X.Ψ → ℂ), hermSingle i0 k0 z ∈ Sp := by
    intro i0 k0 z
    have hz : z ∈ Submodule.span ℝ {z : X.Ψ → ℂ | ∃ γ : E, IsIntegral ℤ γ ∧
      z = fun τ => τ.1 γ} := by rw [span_emb_int]; trivial
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨γ, hγ, rfl⟩ := hx
      rw [← Sp.smul_mem_iff hcr.ne']
      refine Submodule.subset_span ⟨fun i k => cE g * ((if i = i0 ∧ k = k0 then γ else 0) +
        (if k = i0 ∧ i = k0 then cc γ else 0)), fun i k => ?_, fun i k => ⟨_, ?_, rfl⟩, ?_⟩
      · simp only [FixedPointImaginarySpan.cc_mul'', cc_cE, RealEmbeddingCharacters.cc_add', apply_ite cc,
          RealEmbeddingCharacters.cc_zero', RealEmbeddingCharacters.cc_cc', add_comm]
      · refine IsIntegral.add ?_ ?_ <;> split_ifs
        exacts [hγ, isIntegral_zero, isIntegral_cc hγ, isIntegral_zero]
      · funext τ i k
        simp only [hermSingle, embH, Submodule.coe_smul, Pi.smul_apply, LinearMap.coe_mk,
          AddHom.coe_mk, Complex.real_smul, map_mul, emb_cE, map_add, apply_ite τ.1, map_zero,
          emb_cc]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Sp.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Sp.smul_mem c hx
  refine eq_top_iff.2 fun b _ => ?_
  rw [sum_hermSingle b]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k _ => key _ _ _

theorem exists_isLZBasis {g : ℕ} (hg : 0 < g) : ∃ ω, IsLZBasis (d := d) X g ω := by
  have := discrete_latZ (d := d) X hg
  have : IsZLattice ℝ (latZ X d g) := ⟨span_latZ X hg⟩
  have hrank : Module.finrank ℤ (latZ X d g) = d * d * Fintype.card X.Ψ := by
    rw [ZLattice.rank ℝ (latZ X d g), finrank_hermSub]
  set bZ := Module.finBasisOfFinrankEq ℤ (latZ X d g) hrank
  set eR := bZ.ofZLatticeBasis ℝ (latZ X d g)
  have heR : ∀ j, eR j = (bZ j : hermSub X.Ψ d) := fun j => bZ.ofZLatticeBasis_apply ℝ _ j
  have hli : LinearIndependent ℝ (fun j => (eR j).1) :=
    eR.linearIndependent.map' (hermSub X.Ψ d).subtype (Submodule.ker_subtype _)
  have hc : ∀ (m : ℤ) (v : X.Ψ → Fin d → Fin d → ℂ), (m : ℂ) • v = (m : ℝ) • v := fun m v => by
    rw [← Complex.ofReal_intCast, Complex.coe_smul]
  refine ⟨fun j => (eR j).1, fun j => ?_, fun b hb => ?_, hli⟩
  · rw [← mem_latZ, heR]; exact (bZ j).2
  · set b' : latZ X d g := ⟨⟨b, isHerm_of_mem_LZ X hb⟩, hb⟩
    set n := bZ.repr b'
    have h1 := congrArg (fun v : latZ X d g => v.1.1) (bZ.sum_repr b')
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h1
    have hb' : b = ∑ j, (n j : ℂ) • (eR j).1 := by
      refine h1.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [heR, Int.cast_smul_eq_zsmul]
    refine ⟨n, hb', fun n' hn' => ?_⟩
    have e : ∑ j, (n' j : ℝ) • (eR j).1 = ∑ j, (n j : ℝ) • (eR j).1 := by
      have := hn'.symm.trans hb'
      simpa only [hc] using this
    have hz := Fintype.linearIndependent_iff.1 hli (fun j => (n' j : ℝ) - n j) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [e, sub_self])
    funext j
    have := sub_eq_zero.1 (hz j)
    exact_mod_cast this

theorem IsLZBasis.exists_basis {g : ℕ}
    {ω : Fin (d * d * Fintype.card X.Ψ) → X.Ψ → Fin d → Fin d → ℂ} (hω : IsLZBasis X g ω) :
    ∃ e : Basis (Fin (d * d * Fintype.card X.Ψ)) ℝ (hermSub X.Ψ d), (∀ j, (e j).1 = ω j) ∧
      Submodule.span ℤ (Set.range e) = latZ X d g := by
  set ω' : Fin (d * d * Fintype.card X.Ψ) → hermSub X.Ψ d :=
    fun j => ⟨ω j, isHerm_of_mem_LZ X (hω.1 j)⟩
  have hli : LinearIndependent ℝ ω' := LinearIndependent.of_comp (hermSub X.Ψ d).subtype hω.2.2
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range ω') :=
    (hli.span_eq_top_of_card_eq_finrank' (by rw [finrank_hermSub, Fintype.card_fin])).ge
  refine ⟨Basis.mk hli hsp, fun j => by rw [Basis.mk_apply], le_antisymm ?_ fun b hb => ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Basis.mk_apply]
    exact hω.1 j
  · obtain ⟨n, hn, -⟩ := hω.2.1 b.1 hb
    have : b = ∑ j, n j • Basis.mk hli hsp j := by
      apply Subtype.ext
      rw [hn]
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Basis.mk_apply,
        Int.cast_smul_eq_zsmul, ω']
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

def form : (X.Ψ → Fin d → Fin d → ℂ) →ₗ[ℝ] hermSub X.Ψ d →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun χ b => 2 * pairR X χ b.1)
    (fun χ χ' b => by simp [pairR, add_mul, Finset.sum_add_distrib, mul_add])
    (fun c χ b => by
      simp only [pairR, Pi.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum,
        Complex.re_ofReal_mul, smul_eq_mul]; ring)
    (fun χ b b' => by simp [pairR, Finset.sum_add_distrib, mul_add])
    (fun c χ b => by
      simp only [pairR, Submodule.coe_smul, Pi.smul_apply, Complex.real_smul, mul_left_comm _ (c : ℂ),
        ← Finset.mul_sum, Complex.re_ofReal_mul, smul_eq_mul]; ring)

theorem form_apply (χ : X.Ψ → Fin d → Fin d → ℂ) (b : hermSub X.Ψ d) :
    form X χ b = 2 * pairR X χ b.1 := rfl

theorem form_injective : Function.Injective (form X ∘ₗ (hermSub X.Ψ d).subtype) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro χ h
  have h1 := LinearMap.congr_fun h ⟨fun τ i k => conj (χ.1 τ i k), fun τ i k => by
    exact congrArg conj (χ.2 τ i k)⟩
  simp only [LinearMap.comp_apply, form_apply, pairR, Submodule.subtype_apply, Complex.mul_conj,
    LinearMap.zero_apply, Complex.re_sum, Complex.ofReal_re, mul_eq_zero, OfNat.ofNat_ne_zero,
    false_or] at h1
  apply Subtype.ext
  funext τ i k
  have n := fun τ i k => Complex.normSq_nonneg (χ.1 τ i k)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun k _ => n τ i k).1 h1 τ (Finset.mem_univ _)
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    Finset.sum_nonneg fun k _ => n τ i k).1 h2 i (Finset.mem_univ _)
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => n τ i k).1 h3 k (Finset.mem_univ _)
  exact Complex.normSq_eq_zero.1 h4

theorem exists_form_eq (φ : hermSub X.Ψ d →ₗ[ℝ] ℝ) : ∃ χ, IsHerm χ ∧ form X χ = φ := by
  obtain ⟨χ, h⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := hermSub X.Ψ d)).symm).1 (form_injective X) φ
  exact ⟨χ.1, χ.2, h⟩

theorem isFreqZ_iff {g : ℕ} (χ : X.Ψ → Fin d → Fin d → ℂ) :
    IsFreqZ X g χ ↔ ∀ l ∈ latZ X d g, ∃ k : ℤ, form X χ l = k :=
  ⟨fun h l hl => h l.1 hl, fun h b hb => h ⟨b, isHerm_of_mem_LZ X hb⟩ hb⟩

end

end GlobalTheory.MaxCusp
