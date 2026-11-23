import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivMulTwistingSectionIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormMulTwistingSectionEqConstMulStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VAddGeOfMemProdZpow

set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

noncomputable section

namespace GlobalTheory.FlatTw.Good

open scoped nonZeroDivisors

theorem exists_vAdd_ge {K : Type} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (B : ℕ) :
    ∃ a : K, a ≠ 0 ∧ (∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vAdd w a) ∧ ∀ w ∈ S, (B : ℤ) ≤ vAdd w a := by
  classical
  let I : Ideal (𝓞 K) := ∏ w ∈ S, w.asIdeal ^ B
  have hI : I ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)
  obtain ⟨r, hrI, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have ha0 : algebraMap (𝓞 K) K r ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
  have hmem : algebraMap (𝓞 K) K r ∈
      (∏ w ∈ S, (((Equiv.refl (HeightOneSpectrum (𝓞 K))) w).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-((fun _ => -(B : ℤ)) w))) := by
    have e : (∏ w ∈ S, (((Equiv.refl (HeightOneSpectrum (𝓞 K))) w).asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-((fun _ => -(B : ℤ)) w))) = ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
      simp only [Equiv.refl_apply, neg_neg, zpow_natCast, I]
      rw [← FractionalIdeal.coeIdealHom_apply, map_prod]
      simp [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow]
    rw [e]
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hrI, rfl⟩
  refine ⟨_, ha0, fun w => ?_, fun w hw => ?_⟩
  · have h := (GlobalTheory.Core.Int.ProdPrimePow.vAdd_ge_of_mem_prod_zpow K _ (Equiv.refl _) S
      (fun _ => -(B : ℤ)) _ hmem w).resolve_left ha0
    simp only [Equiv.refl_apply, neg_neg] at h
    split_ifs at h
    · exact le_trans (by positivity) h
    · exact h
  · have h := (GlobalTheory.Core.Int.ProdPrimePow.vAdd_ge_of_mem_prod_zpow K _ (Equiv.refl _) S
      (fun _ => -(B : ℤ)) _ hmem w).resolve_left ha0
    simp only [Equiv.refl_apply, neg_neg, if_pos hw] at h
    exact h

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

theorem exists_twist_scalar {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
    {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) :
    ∃ a : c.F, a ≠ 0 ∧ (∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) ∧ ∀ w, s.hi w ≤ (vAdd w a : ℝ) := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 c.F)) := s.finite_lo.toFinset ∪ s.finite_hi.toFinset
  let B : ℕ := ⌈∑ w ∈ S, (|s.lo w| + |s.hi w|)⌉₊
  have hB : ∀ w ∈ S, |s.lo w| + |s.hi w| ≤ B := fun w hw =>
    (Finset.single_le_sum (f := fun w => |s.lo w| + |s.hi w|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hw).trans (Nat.le_ceil _)
  obtain ⟨a, ha0, hpos, hS⟩ := exists_vAdd_ge S B
  refine ⟨a, ha0, fun w => ?_, fun w => ?_⟩
  · by_cases hw : w ∈ S
    · have h1 := hB w hw
      have h2 : ((B : ℤ) : ℝ) ≤ (vAdd w a : ℝ) := by exact_mod_cast hS w hw
      have h3 := neg_abs_le (s.lo w)
      push_cast at h2
      linarith [abs_nonneg (s.hi w)]
    · have : s.lo w = 0 := by
        by_contra h
        exact hw (Finset.mem_union_left _ (s.finite_lo.mem_toFinset.2 h))
      rw [this, add_zero]; exact_mod_cast hpos w
  · by_cases hw : w ∈ S
    · have h1 := hB w hw
      have h2 : ((B : ℤ) : ℝ) ≤ (vAdd w a : ℝ) := by exact_mod_cast hS w hw
      have h3 := le_abs_self (s.hi w)
      push_cast at h2
      linarith [abs_nonneg (s.lo w)]
    · have : s.hi w = 0 := by
        by_contra h
        exact hw (Finset.mem_union_right _ (s.finite_hi.mem_toFinset.2 h))
      rw [this]; exact_mod_cast hpos w

theorem cnorm_smul {ι : Type} [Fintype ι] (k : ℂ) (u : ι → ℂ) : Formalism.HermitianLatticesTheory.cnorm (k • u) = ‖k‖ * Formalism.HermitianLatticesTheory.cnorm u := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  have : ∑ i, ‖(k • u) i‖ ^ 2 = ‖k‖ ^ 2 * ∑ i, ‖u i‖ ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

section Abstract

variable {K : Type} [Field K] [NumberField K] {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem lattice_transfer (φ : V ≃ₗ[K] W) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (a : K) (ha : a ≠ 0)
    (hin : ∀ f ∈ L, a • φ f ∈ L') (hout : ∀ g ∈ L', a • φ.symm g ∈ L) (hFG : L.FG)
    (hspan : Submodule.span K (L : Set V) = ⊤) :
    L'.FG ∧ Submodule.span K (L' : Set W) = ⊤ ∧ Formalism.HN.rkK L' = Formalism.HN.rkK L := by
  let ψ : V →ₗ[𝓞 K] W :=
    { toFun := fun f => a⁻¹ • φ f
      map_add' := fun f f' => by rw [map_add, smul_add]
      map_smul' := fun m f => by
        rw [RingHom.id_apply, ← algebraMap_smul K m f, map_smul, ← algebraMap_smul K m (a⁻¹ • φ f),
          smul_smul, smul_smul, mul_comm] }
  have hle : L' ≤ L.map ψ := fun g hg => by
    refine ⟨a • φ.symm g, hout g hg, ?_⟩
    show a⁻¹ • φ (a • φ.symm g) = g
    rw [map_smul, φ.apply_symm_apply, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hFG' : L'.FG := by
    have := isNoetherian_of_fg_of_noetherian _ (hFG.map ψ)
    exact isNoetherian_submodule.mp this _ hle
  have hspan' : Submodule.span K (L' : Set W) = ⊤ := by
    have hsub : Submodule.span K (L : Set V) ≤ (Submodule.span K (L' : Set W)).comap (φ : V →ₗ[K] W) := by
      refine Submodule.span_le.2 fun f hf => Submodule.mem_comap.2 ?_
      have h2 := Submodule.smul_mem (Submodule.span K (L' : Set W)) a⁻¹ (Submodule.subset_span (R := K) (hin f hf))
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul] at h2
      exact h2
    rw [eq_top_iff]
    intro g _
    have h := hsub (show φ.symm g ∈ Submodule.span K (L : Set V) by rw [hspan]; trivial)
    simpa using h
  refine ⟨hFG', hspan', ?_⟩
  unfold Formalism.HN.rkK
  rw [hspan, hspan', finrank_top, finrank_top]
  exact φ.symm.finrank_eq

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] in

theorem hasGram_transfer (φ : V ≃ₗ[K] W) (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ) (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, 0 < t σ) (h : ∀ σ f, N' σ (φ f) = t σ * N σ f) (hN : HasGram N) : HasGram N' := by
  obtain ⟨⟨n, ⟨b, X⟩, hX⟩⟩ := hN
  refine ⟨⟨n, ⟨(b.map φ, fun v => ((t v.embedding : ℂ)⁻¹) • X v), fun v => ?_⟩⟩⟩
  have hk : ((t v.embedding : ℂ)⁻¹) ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 (ht _).ne')
  have hdet := (hX v).1
  refine ⟨?_, fun y => ?_⟩
  · show IsUnit ((((t v.embedding : ℂ)⁻¹) • X v).det)
    rw [Matrix.det_smul]
    exact (IsUnit.pow _ (Ne.isUnit hk)).mul hdet
  · show Formalism.HermitianLatticesTheory.normAt (b.map φ) (fun v => ((t v.embedding : ℂ)⁻¹) • X v) v y = N' v.embedding y
    have := invertibleOfNonzero hk
    rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.inv_smul _ _ hdet, invOf_eq_inv]
    have hvec : Formalism.HermitianLatticesTheory.vecAt (b.map φ) v y = Formalism.HermitianLatticesTheory.vecAt b v (φ.symm y) := by
      funext i; simp [Formalism.HermitianLatticesTheory.vecAt, Module.Basis.map_repr]
    rw [hvec, Matrix.smul_mulVec, cnorm_smul, ← Formalism.HermitianLatticesTheory.fcoord, ← Formalism.HermitianLatticesTheory.normAt, (hX v).2,
      ← φ.apply_symm_apply y, h, φ.apply_symm_apply]
    rw [inv_inv, Complex.norm_real, Real.norm_of_nonneg (ht _).le]

end Abstract

end GlobalTheory.FlatTw.Good

namespace GlobalTheory.FlatTw.Good

theorem twist_goodOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (_s : TwSec U x Z G₀) (G : WTZ E), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → GoodOn U x V dict Z G → GoodOn U x V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G₀ s G _hU hG hgood
  obtain ⟨hGram, hFG, hspan⟩ := hgood
  obtain ⟨φ, hφ, -, hA, hB⟩ := Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨a, ha0, hlo, hhi⟩ := exists_twist_scalar s
  obtain ⟨hFG', hspan', hrk⟩ := lattice_transfer φ (latOn U Z G) (latOn U Z (G + G₀)) a ha0
    (fun f hf => hA a ha0 hlo f hf _ (Submodule.coe_smul _ _))
    (fun g hg => hB a ha0 hhi g hg _ (Submodule.coe_smul _ _)) hFG hspan
  refine ⟨⟨hasGram_transfer φ _ _ s.cInf s.cInf_pos (fun σ f => ?_) hGram, hFG', hspan'⟩, hrk⟩
  show petOn U x V dict Z (G + G₀) σ (φ f : Rul Xo c) = s.cInf σ * petOn U x V dict Z G σ (f : Rul Xo c)
  rw [hφ, petOn, petOn, GlobalTheory.T.petersson_norm_mul_twistingSection_eq_const_mul E H Dw l Xo c r U x Z G₀ s G hG _ f.2.2]

end GlobalTheory.FlatTw.Good
