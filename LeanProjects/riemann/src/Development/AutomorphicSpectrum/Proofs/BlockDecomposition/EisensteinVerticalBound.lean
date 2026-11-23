import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightContinuousPosStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatSectionGrowthBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesConvergentStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.EisHalf

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem hgt_of_mem {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (ha : IsHgt K a) {k : G2 σ Y} (hk : k ∈ K) : a k = 1 := by
  have h1 : IsPar (1 : G2 σ Y) 1 := isPar_iff.2 ((Matrix.one_mul _).trans (Matrix.mul_one _).symm)
  have := ha.val 1 1 h1 k hk
  simpa using this

theorem hgt_mul {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (ha : IsHgt K a) {p : G2 σ Y} {t} (hp : IsPar p t) {k : G2 σ Y}
    (hk : k ∈ K) (u : G2 σ Y) : a (p * k * u) = a (p * k) * a (k * u) := by
  obtain ⟨q, v, hq, k', hk', e⟩ := ha.iwa (k * u)
  rw [mul_assoc, e, ← mul_assoc, ha.val _ _ (hp.mul hq) k' hk', ha.val p t hp k hk, ha.val q v hq k' hk', map_mul, map_mul,
    NNReal.coe_mul]

theorem exists_nhd_one {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsCompact (K : Set (G2 σ Y))) (ac : Continuous a)
    (ha : IsHgt K a) (a0 : ∀ x, 0 < a x) :
    ∃ W : Set (G2 σ Y), IsOpen W ∧ (1 : G2 σ Y) ∈ W ∧ ∀ g, ∀ u ∈ W, a g / 2 ≤ a (g * u) ∧ a (g * u) ≤ 2 * a g := by
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have hn : IsOpen ((fun y : G2 σ Y × G2 σ Y => a (y.1 * y.2)) ⁻¹' Set.Ioo (1 / 2) 2) :=
    isOpen_Ioo.preimage (ac.comp continuous_mul)
  have hs : (K : Set (G2 σ Y)) ×ˢ ({1} : Set (G2 σ Y)) ⊆ (fun y : G2 σ Y × G2 σ Y => a (y.1 * y.2)) ⁻¹' Set.Ioo (1 / 2) 2 := by
    rintro ⟨k, u⟩ ⟨hk, hu⟩
    have hu' : u = 1 := hu
    subst hu'
    simp only [Set.mem_preimage, mul_one]
    rw [hgt_of_mem ha hk]
    norm_num
  obtain ⟨U, V, -, hV, hKU, h1V, hUV⟩ := generalized_tube_lemma hK isCompact_singleton hn hs
  refine ⟨V, hV, h1V rfl, fun g u hu => ?_⟩
  obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa g
  have h := hUV (show (k, u) ∈ U ×ˢ V from ⟨hKU hk, hu⟩)
  obtain ⟨h1, h2⟩ : 1 / 2 < a (k * u) ∧ a (k * u) < 2 := h
  rw [hgt_mul ha hp hk]
  have := a0 (p * k)
  constructor <;> nlinarith

theorem rpow_le_add {A r c c' : ℝ} (hA : 0 < A) (h1 : c ≤ r) (h2 : r ≤ c') : A ^ r ≤ A ^ c + A ^ c' := by
  have p := Real.rpow_pos_of_pos hA c
  have p' := Real.rpow_pos_of_pos hA c'
  rcases le_total A 1 with h | h
  · linarith [Real.rpow_le_rpow_of_exponent_ge hA h h1]
  · linarith [Real.rpow_le_rpow_of_exponent_le h h2]

theorem rpow_le_of_near {A B : ℝ} (hA : 0 < A) (h1 : A / 2 ≤ B) (h2 : B ≤ 2 * A) (e : ℝ) : B ^ e ≤ 2 ^ |e| * A ^ e := by
  have hB : 0 < B := by linarith
  rcases le_total 0 e with h | h
  · rw [abs_of_nonneg h, ← Real.mul_rpow (by norm_num) hA.le]
    exact Real.rpow_le_rpow hB.le h2 h
  · have k := Real.rpow_le_rpow_of_nonpos (half_pos hA) h1 h
    refine k.trans (le_of_eq ?_)
    rw [abs_of_nonpos h, div_eq_mul_inv, Real.mul_rpow hA.le (by norm_num), Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num),
      mul_comm]

theorem eis_half_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ t₀ : ℝ, ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), t₀ ≤ t → (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → (∀ s : ℂ, t < s.re → (fun x => Ê s x) ∈ modFun σ Y) ∧ ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) ∧ ∀ c c' : ℝ, t < c → ∃ (C : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ C * (ht2 x : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha χ s₁ f hf
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨ac, a0⟩ := GlobalTheory.T.height_function_continuous_pos' F E σ B n Y r s hB hn hY b K a hb hK ha
  have kc := GlobalTheory.T.isCompact_standard_maximal F E σ B n Y r s hB hn hY b K a hb hK ha
  obtain ⟨C, hC⟩ := GlobalTheory.T.flat_section_growth_bound K a kc ha a0 χ s₁ f hf
  obtain ⟨σ₀, hG⟩ := GlobalTheory.T.eisenstein_series_convergent F E σ B n Y r s hB hn hY b K a hb hK ha
  obtain ⟨W, hW, h1W, hWa⟩ := exists_nhd_one kc ac ha a0
  refine ⟨σ₀ - n / 2, fun t Ê ht hE => ?_⟩
  have tb : ∀ (z : ℂ) (c c' : ℝ), c ≤ z.re → z.re ≤ c' → ∀ g,
      ‖flat a f s₁ z g‖ ≤ |C| * (a g ^ (c + (n : ℝ) / 2) + a g ^ (c' + (n : ℝ) / 2)) := fun z c c' h1 h2 g =>
    (hC z g).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_pos_of_pos (a0 g) _).le).trans
      (mul_le_mul_of_nonneg_left (rpow_le_add (a0 g) (by linarith) (by linarith)) (abs_nonneg C)))
  have gr : ∀ c c' : ℝ, t < c → ∃ (D : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ D * (ht2 x : ℝ) ^ N := by
    intro c c' hc
    have h1 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have h2 : σ₀ < max c c' + (n : ℝ) / 2 := by linarith [le_max_left c c']
    obtain ⟨C₁, N₁, H₁⟩ := hG _ h1
    obtain ⟨C₂, N₂, H₂⟩ := hG _ h2
    refine ⟨|C| * (|C₁| + |C₂|), max N₁ N₂, fun z h1z h2z x => ?_⟩
    have hx : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1
    have S := (H₁ x).1.add (H₂ x).1
    have hs := (hE z (by linarith) x).norm_le_of_bounded (S.mul_left |C|).hasSum
      (fun q => tb z c (max c c') h1z (h2z.trans (le_max_right c c')) _)
    refine hs.trans ?_
    rw [tsum_mul_left, (H₁ x).1.tsum_add (H₂ x).1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
    have p1 : (ht2 x : ℝ) ^ N₁ ≤ (ht2 x : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hx (le_max_left _ _)
    have p2 : (ht2 x : ℝ) ^ N₂ ≤ (ht2 x : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hx (le_max_right _ _)
    have q0 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₁ := pow_nonneg (by linarith) _
    have q1 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₂ := pow_nonneg (by linarith) _
    rw [add_mul]
    exact add_le_add ((H₁ x).2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) q0).trans
        (mul_le_mul_of_nonneg_left p1 (abs_nonneg _))))
      ((H₂ x).2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) q1).trans (mul_le_mul_of_nonneg_left p2 (abs_nonneg _))))
  have ct : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) := by
    rintro ⟨z₀, x₀⟩ ⟨hz₀, -⟩
    have hz₁ : t < z₀.re := hz₀
    obtain ⟨c, hc1, hc2⟩ := exists_between hz₁
    obtain ⟨c', hc'⟩ := exists_gt z₀.re
    have h1 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have h2 : σ₀ < c' + (n : ℝ) / 2 := by linarith
    obtain ⟨_, _, H₁⟩ := hG _ h1
    obtain ⟨_, _, H₂⟩ := hG _ h2
    let V : Set (G2 σ Y) := (fun x => x₀⁻¹ * x) ⁻¹' W
    have hV : IsOpen V := hW.preimage (continuous_const.mul continuous_id)
    let S : Set (ℂ × G2 σ Y) := {z : ℂ | c < z.re ∧ z.re < c'} ×ˢ V
    have hS : IsOpen S :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)).prod hV
    have mS : (z₀, x₀) ∈ S := ⟨⟨hc2, hc'⟩, by simpa [V] using h1W⟩
    have sumU : Summable fun q : Cos σ Y => |C| *
        (2 ^ |c + (n : ℝ) / 2| * a ((Quotient.out q).1 * x₀) ^ (c + (n : ℝ) / 2) +
          2 ^ |c' + (n : ℝ) / 2| * a ((Quotient.out q).1 * x₀) ^ (c' + (n : ℝ) / 2)) :=
      (((H₁ x₀).1.mul_left _).add ((H₂ x₀).1.mul_left _)).mul_left _
    have cts : ContinuousOn (fun y : ℂ × G2 σ Y => ∑' q : Cos σ Y, eisTerm (flat a f s₁ y.1) y.2 q) S := by
      refine continuousOn_tsum (fun q => Continuous.continuousOn ?_) sumU ?_
      · have cg : Continuous fun y : ℂ × G2 σ Y => (Quotient.out q).1 * y.2 := continuous_const.mul continuous_snd
        exact ((Complex.continuous_ofReal.comp (ac.comp cg)).cpow (continuous_fst.sub continuous_const)
          fun y => Complex.ofReal_mem_slitPlane.2 (a0 _)).mul (hf.cont.comp cg)
      · rintro q ⟨z, x⟩ ⟨⟨hz1, hz2⟩, hx⟩
        have hu := hWa ((Quotient.out q).1 * x₀) (x₀⁻¹ * x) hx
        rw [show (Quotient.out q).1 * x₀ * (x₀⁻¹ * x) = (Quotient.out q).1 * x by group] at hu
        exact (tb z c c' hz1.le hz2.le _).trans (mul_le_mul_of_nonneg_left (add_le_add
          (rpow_le_of_near (a0 _) hu.1 hu.2 _) (rpow_le_of_near (a0 _) hu.1 hu.2 _)) (abs_nonneg C))
    have ctE : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) S :=
      cts.congr fun y hy => (hE y.1 (hc1.trans hy.1.1) y.2).tsum_eq.symm
    exact (ctE.continuousAt (hS.mem_nhds mS)).continuousWithinAt
  refine ⟨fun z hz => ?_, ct, gr⟩
  obtain ⟨D, N, hD⟩ := gr z.re z.re hz
  have cz : Continuous fun x => Ê z x :=
    ct.comp_continuous (Continuous.prodMk_right z) fun x => ⟨hz, trivial⟩
  have M1 : (1 : ℝ) ≤ max D 1 := le_max_right _ _
  have M0 : (0 : ℝ) < max D 1 := by linarith
  have Mc : ((max D 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 M0.ne'
  have e : (fun x => Ê z x) = ((max D 1 : ℝ) : ℂ) • ((((max D 1 : ℝ) : ℂ))⁻¹ • fun x => Ê z x) := by
    rw [smul_smul, mul_inv_cancel₀ Mc, one_smul]
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨cz.const_smul _, N, fun x => ?_⟩)
  have hx : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1
  have q0 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N := pow_nonneg (by linarith) _
  rw [Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg M0.le, inv_mul_le_iff₀ M0]
  exact (hD z le_rfl le_rfl x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) q0)

end GlobalTheory.CompanionTheory.EisHalf

end
