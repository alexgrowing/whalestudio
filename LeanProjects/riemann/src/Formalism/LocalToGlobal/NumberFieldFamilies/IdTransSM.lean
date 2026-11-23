import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.LocalToGlobal.UnitaryNorms.UnrAe

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Filter Topology

namespace Formalism.L2.Fam.IdTrans

theorem re_gt_half {b : ℂ} (hb : ‖b‖ = 1) (h : ‖b - 1‖ < 1) : 1 / 2 < b.re := by
  have h1 : b.re * b.re + b.im * b.im = 1 := by
    have h0 := Complex.sq_norm b
    rw [hb, Complex.normSq_apply] at h0
    linarith
  have h3 : ‖b - 1‖ ^ 2 < 1 := by nlinarith [norm_nonneg (b - 1)]
  rw [Complex.sq_norm, Complex.normSq_apply] at h3
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h3
  nlinarith

theorem one_sub_re_sq {b : ℂ} (hb : ‖b‖ = 1) : 1 - (b ^ 2).re = 2 * (1 - b.re) * (1 + b.re) := by
  have h1 : b.re * b.re + b.im * b.im = 1 := by
    have h0 := Complex.sq_norm b
    rw [hb, Complex.normSq_apply] at h0
    linarith
  rw [sq, Complex.mul_re]
  linear_combination h1

theorem eq_one_of_pow {a : ℂ} (h : ∀ n : ℤ, ‖a ^ n - 1‖ < 1) (ha : a ≠ 0) : a = 1 := by
  have hb : ∀ n : ℤ, ‖a‖ ^ n < 2 := fun n => by
    have h2 := h n
    rw [← norm_zpow]
    calc ‖a ^ n‖ = ‖(a ^ n - 1) + 1‖ := by ring_nf
      _ ≤ ‖a ^ n - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ < 2 := by rw [norm_one]; linarith
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  have h1 : ‖a‖ = 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hgt' : 1 < ‖a‖⁻¹ := (one_lt_inv₀ hpos).2 hlt
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt 2 hgt'
      have h2 := hb (-(n : ℤ))
      rw [zpow_neg, zpow_natCast, ← inv_pow] at h2
      linarith
    · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt 2 hgt
      have h2 := hb n
      rw [zpow_natCast] at h2
      linarith
  have hre : ∀ n : ℕ, 1 / 2 < (a ^ (2 ^ n)).re := fun n => by
    have hn := h ((2 ^ n : ℕ) : ℤ)
    rw [zpow_natCast] at hn
    exact re_gt_half (by rw [norm_pow, h1, one_pow]) hn
  have hd : ∀ n : ℕ, 3 ^ n * (1 - a.re) ≤ 1 - (a ^ (2 ^ n)).re := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hnorm : ‖a ^ (2 ^ n)‖ = 1 := by rw [norm_pow, h1, one_pow]
      have e : a ^ (2 ^ (n + 1)) = (a ^ (2 ^ n)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e, one_sub_re_sq hnorm, pow_succ]
      have h3 := hre n
      have h4 : 0 ≤ 1 - (a ^ (2 ^ n)).re := by
        have h5 := Complex.re_le_norm (a ^ (2 ^ n))
        rw [hnorm] at h5
        linarith
      have h6 : 3 * (1 - (a ^ (2 ^ n)).re) ≤ 2 * (1 - (a ^ (2 ^ n)).re) * (1 + (a ^ (2 ^ n)).re) := by nlinarith
      nlinarith
  have hd0 : 1 - a.re ≤ 0 := by
    by_contra hpos0
    push_neg at hpos0
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (1 - a.re)) (by norm_num : (1 : ℝ) < 3)
    have h2 := hd n
    have h5 := hre n
    rw [div_lt_iff₀ hpos0] at hn
    linarith
  have hre1 : a.re = 1 := by
    have h5 := Complex.re_le_norm a
    rw [h1] at h5
    linarith
  have him : a.im = 0 := by
    have h0 := Complex.sq_norm a
    rw [h1, Complex.normSq_apply, hre1] at h0
    have h7 : a.im * a.im = 0 := by nlinarith
    exact mul_self_eq_zero.1 h7
  exact Complex.ext (by simp [hre1]) (by simp [him])

section Top

variable {L : Type} [Field L] [NumberField L]

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 L)) :
    IsOpen (v.adicCompletionIntegers L : Set (v.adicCompletion L)) := by
  exact Valued.isOpen_integer _

open Classical in
theorem finiteSingle_eq (v : HeightOneSpectrum (𝓞 L)) (x : v.adicCompletion L) (hx : x ∈ v.adicCompletionIntegers L) :
    finiteSingle L v x = RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) cofinite
      (Pi.mulSingle v (⟨x, hx⟩ : v.adicCompletionIntegers L)) := by
  apply RestrictedProduct.ext
  intro w
  show (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v x w) =
    ((Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => ↥(w.adicCompletionIntegers L)) v ⟨x, hx⟩ w :
      w.adicCompletionIntegers L) : w.adicCompletion L)
  by_cases h : w = v
  · subst h
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h]
    rfl

theorem single_mem_nhds {S : Set (AdeleRing (𝓞 L) L)} (hS : S ∈ 𝓝 (1 : AdeleRing (𝓞 L) L)) :
    ∃ I : Set (HeightOneSpectrum (𝓞 L)), I.Finite ∧ ∀ v ∉ I, ∀ (x : v.adicCompletion L) (_hx : x ∈ v.adicCompletionIntegers L),
      (((1 : InfiniteAdeleRing L), finiteSingle L v x) : AdeleRing (𝓞 L) L) ∈ S := by
  have hS' : S ∈ 𝓝 (((1 : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L)) : InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L) := hS
  obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.mp hS'
  have hw' : w ∈ Filter.map (RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) cofinite)
      (𝓝 (1 : Π v : HeightOneSpectrum (𝓞 L), v.adicCompletionIntegers L)) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap (fun v => isOpen_integers v)]
    exact hw
  have hw'' : RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) cofinite ⁻¹' w ∈
      𝓝 (1 : Π v : HeightOneSpectrum (𝓞 L), v.adicCompletionIntegers L) := hw'
  rw [nhds_pi, Filter.mem_pi] at hw''
  obtain ⟨I, hI, t, ht, hIt⟩ := hw''
  refine ⟨I, hI, fun v hv x hx => huw ⟨mem_of_mem_nhds hu, ?_⟩⟩
  classical
  have hf : (Pi.mulSingle v (⟨x, hx⟩ : v.adicCompletionIntegers L) : Π v : HeightOneSpectrum (𝓞 L),
      v.adicCompletionIntegers L) ∈ I.pi t := by
    intro w' hw'
    have hne : w' ≠ v := fun h => hv (h ▸ hw')
    rw [Pi.mulSingle_eq_of_ne hne]
    exact mem_of_mem_nhds (ht w')
  have := hIt hf
  show finiteSingle L v x ∈ w
  rw [finiteSingle_eq v x hx]
  exact this

end Top

theorem unrAE {L : Type} [Field L] [NumberField L] : UnrAE L := by
  intro χ hχ
  classical
  set W : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1} with hWdef
  have hWo : IsOpen W := isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have hW1 : (1 : ℂˣ) ∈ W := by simp [hWdef]
  have hN : χ ⁻¹' W ∈ 𝓝 (1 : Ideles L) := by
    apply hχ.continuousAt.preimage_mem_nhds
    rw [map_one]
    exact hWo.mem_nhds hW1
  rw [(Units.isEmbedding_embedProduct (M := AdeleRing (𝓞 L) L)).isInducing.nhds_eq_comap] at hN
  obtain ⟨T, hT, hTN⟩ := hN
  rw [map_one] at hT
  have hT' : T ∈ 𝓝 (((1 : AdeleRing (𝓞 L) L), (1 : (AdeleRing (𝓞 L) L)ᵐᵒᵖ))) := hT
  obtain ⟨T1, hT1, T2, hT2, hT12⟩ := mem_nhds_prod_iff.mp hT'
  have hT2' : MulOpposite.op ⁻¹' T2 ∈ 𝓝 (1 : AdeleRing (𝓞 L) L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by rw [MulOpposite.op_one]; exact hT2)
  obtain ⟨I1, hI1, h1⟩ := single_mem_nhds hT1
  obtain ⟨I2, hI2, h2⟩ := single_mem_nhds hT2'
  have hmem : ∀ v ∉ I1 ∪ I2, ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → χ (localIdele L v x) ∈ W := by
    intro v hv x hx
    have hv1 : v ∉ I1 := fun h => hv (Or.inl h)
    have hv2 : v ∉ I2 := fun h => hv (Or.inr h)
    have hxO : (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact le_of_eq hx
    have hxO' : ((x⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀]
      rw [show Valued.v (x : v.adicCompletion L) = 1 from hx, inv_one]
    apply hTN
    apply hT12
    refine ⟨h1 v hv1 _ hxO, ?_⟩
    show (((localIdele L v x)⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) ∈ MulOpposite.op ⁻¹' T2
    rw [← map_inv]
    exact h2 v hv2 _ hxO'
  refine Filter.mem_of_superset (hI1.union hI2).compl_mem_cofinite fun v hv x hx => ?_
  apply Units.ext
  apply eq_one_of_pow _ (Units.ne_zero _)
  intro n
  have hxn : IsUnitAt v (x ^ n) := by
    show Valued.v (((x ^ n : (v.adicCompletion L)ˣ)) : v.adicCompletion L) = 1
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, show Valued.v (x : v.adicCompletion L) = 1 from hx, one_zpow]
  have := hmem v hv (x ^ n) hxn
  rw [map_zpow, map_zpow] at this
  have h' : ‖(((χ (localIdele L v x)) ^ n : ℂˣ) : ℂ) - 1‖ < 1 := this
  rwa [Units.val_zpow_eq_zpow_val] at h'

theorem unrAe {L : Type} [Field L] [NumberField L] (χ : HChar L) : ∀ᶠ v in cofinite, χ.UnrAt v := (unrAE (L := L) χ.1 χ.2.1).mono fun v hv x hx => hv x hx

section UnitsTriv

variable {L : Type} [Field L] [NumberField L]

def compAt (w : HeightOneSpectrum (𝓞 L)) : Ideles L →* (w.adicCompletion L)ˣ :=
  Units.map { toFun := fun a => a.2 w, map_one' := rfl, map_mul' := fun _ _ => rfl }

variable (L) in

def UnitsTrivP : Prop :=
  ∀ (χ : Ideles L →* ℂˣ), Continuous χ → ∀ (T : Set (HeightOneSpectrum (𝓞 L))), T.Finite →
    (∀ v ∉ T, ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → χ (localIdele L v x) = 1) →
    ∀ u : Ideles L, (u : AdeleRing (𝓞 L) L).1 = 1 → (∀ v, IsUnitAt v (compAt v u)) → (∀ v ∈ T, compAt v u = 1) → χ u = 1

end UnitsTriv

section UnitsTrivPf

variable {L : Type} [Field L] [NumberField L]

def infU : Ideles L →* (InfiniteAdeleRing L)ˣ :=
  Units.map { toFun := fun a => a.1, map_one' := rfl, map_mul' := fun _ _ => rfl }

end UnitsTrivPf

end Formalism.L2.Fam.IdTrans
