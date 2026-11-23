import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.BloIn
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SwapInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ThBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BochnerOfLintegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PseudoEisensteinSectionPfunInBandSlicesReps
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermPairingVanishesOfOrthogonal
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CuspUmg
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsContRep

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem lev_eq {R : Type} [CommRing R] (r s : ℕ) (x : GL (Fin r) R) (y : GL (Fin s) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (x, y) = blk x y := by
  have hs : GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) = finSumFinEquiv := by
    ext (x | x) <;> simp
  refine Units.ext ?_
  rw [GlobalTheory.CompanionTheory.CTFin.lev, GlobalTheory.SmGL.val_emb₂, hs]
  rfl

private theorem blk_nil {R : Type} [CommRing R] (x : GL (Fin 2) R) (y : GL (Fin 0) R) : blk x y = x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (Matrix.fromBlocks x.val 0 0 y.val) (finSumFinEquiv.symm (Fin.castAdd 0 i)) (finSumFinEquiv.symm (Fin.castAdd 0 j)) = _
  rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
  rfl

private theorem ct_nil {K : Type} [Field K] [NumberField K] (ψ : AdelicGLn.AdelicGL K (2 + 0) → ℂ) (g : AdelicGLn.AdelicGL K (2 + 0)) :
    constantTerm 2 ψ g = ψ g := by
  haveI : IsEmpty (UPos (2 + 0) 2) := ⟨fun p => by have := p.2.2; have := p.1.2.isLt; omega⟩
  have h1 : unipFundamentalDomain K (2 + 0) 2 = Set.univ := Set.eq_univ_of_forall fun X p => isEmptyElim p
  have h2 : ∀ X : UPos (2 + 0) 2 → AdeleRing (𝓞 K) K, unipGL X = 1 := fun X => by
    rw [Subsingleton.elim X 0, unipGL_zero]
  rw [constantTerm, h1, Measure.restrict_univ, unipMeasure, Measure.pi_of_empty]
  simp only [h2, one_mul]
  simp

private theorem zt_add (K : Type) [Field K] [NumberField K] (n : ℕ) (a b : ℝ) : BW.zt K n (a + b) = BW.zt K n a * BW.zt K n b := by
  rw [BW.zt, BW.zt, BW.zt, ← map_mul]
  congr 1
  exact Subtype.ext (Real.exp_add a b)

private theorem blk_zt (K : Type) [Field K] [NumberField K] (a : ℝ) : blk (BW.zt K 2 a) (BW.zt K 2 a) = BW.zt K (2 + 2) (2 * a) := by
  have h : rpowHom (((2 : ℕ) * Module.finrank ℚ K : ℝ))⁻¹ ⟨Real.exp a, Real.exp_pos a⟩ =
      rpowHom (((2 + 2 : ℕ) * Module.finrank ℚ K : ℝ))⁻¹ ⟨Real.exp (2 * a), Real.exp_pos _⟩ := by
    refine Subtype.ext ?_
    change Real.exp a ^ _ = Real.exp (2 * a) ^ _
    rw [← Real.exp_mul, ← Real.exp_mul]
    congr 1
    push_cast
    rw [mul_inv, mul_inv]
    ring
  refine Units.ext ?_
  simp only [BW.zt, centralSection, MonoidHom.comp_apply, h, scalarUnits_apply, coe_diagUnits, blk]
  rw [Matrix.fromBlocks_diagonal, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext i
  induction i using Fin.addCases <;> simp

private theorem pt_eq {K : Type} [Field K] [NumberField K] (y₁ y₂ : G1 K 2) (a b : ℝ) :
    blk (BW.zt K 2 a * (y₁ : AdelicGLn.AdelicGL K 2)) (BW.zt K 2 b * (y₂ : AdelicGLn.AdelicGL K 2)) =
      BW.zt K (2 + 2) (a + b) * (lv y₁ y₂ ((a - b) / 2) : G1 K (2 + 2)) := by
  have e : ∀ (t : ℝ) (y : AdelicGLn.AdelicGL K 2), y * UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.zt K t = BW.zt K 2 t * y := fun t y =>
    (centralSection_mul_comm _ y).symm
  rw [blkLaws.1, e, e, show a + b = 2 * ((a + b) / 2) by ring, ← blk_zt, blkLaws.2.2.2.2.2.1, ← mul_assoc, ← mul_assoc,
    ← zt_add, ← zt_add]
  congr 3 <;> ring

private theorem int_pair {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} (b : BW.Blo S 2)
    {τ : Submodule ℂ (L2 (BW.mu1 E 2))} {m B} (hb : BloIn b τ m B) {v : L2 (BW.mu1 E 2)} {φ : G1 E 2 → ℂ} (hc : Continuous φ)
    (hr : Reps (BW.mu1 E 2) v φ) :
    Integrable (fun x : RightCosetSpace (Gam E 2) => φ (Quotient.out x) *
      starRingEnd ℂ (b.f.1 ((Quotient.out x : G1 E 2) : GlobalTheory.CuspRep.GA E 2))) (quotientMeasure (Gam E 2) (BW.mu1 E 2)) := by
  have key : ∀ {w : L2 (BW.mu1 E 2)} {ψ : G1 E 2 → ℂ}, Continuous ψ → Reps (BW.mu1 E 2) w ψ →
      MemLp (fun x : RightCosetSpace (Gam E 2) => ψ (Quotient.out x)) 2 (quotientMeasure (Gam E 2) (BW.mu1 E 2)) := by
    intro w ψ hc hr
    have hinv : ∀ γ ∈ Gam E 2, ∀ y, ψ (γ * y) = ψ y := fun γ hγ => by
      have h1 : (fun y => ψ (γ * y)) =ᵐ[BW.mu1 E 2] ψ := by
        filter_upwards [hr, (measurePreserving_mul_left (BW.mu1 E 2) γ).quasiMeasurePreserving.ae hr] with y a b
        rw [← a, ← b, mk_mul_of_mem hγ]
      exact congrFun (((hc.comp (continuous_const_mul γ)).ae_eq_iff_eq _ hc).1 h1)
    have h3 : (fun x : RightCosetSpace (Gam E 2) => ψ (Quotient.out x)) = quotFun ψ hinv := by
      funext x
      conv_rhs => rw [← Quotient.out_eq x]
      rfl
    rw [h3]
    exact (Lp.memLp w).ae_eq (IsContRep.ae_eq_quotFun (μ := BW.mu1 E 2) (φ := w) (F := ψ) ⟨hc, hinv, hr⟩)
  obtain ⟨w, -, hw⟩ := hb.mem
  have hf : Continuous b.f.1 := ((BW.umgOps E 2).2 b.f (BW.cuspUmg E 2 b.f b.cusp).1).1
  exact (key hc hr).integrable_mul (key (hf.comp continuous_subtype_val) hw).star

private theorem zt_zero (K : Type) [Field K] [NumberField K] : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.zt K 0 = 1 := by
  have : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext Real.exp_zero
  rw [UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.zt, this, map_one]

private theorem ell_swap {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} (b b' : BW.Blo S 2)
    {τ τ' ρ ρ' : Submodule ℂ (L2 (BW.mu1 E 2))} {m B m' B'} (hb : BloIn b τ m B) (hb' : BloIn b' τ' m' B')
    {f : G1 E (2 + 2) → ℂ} (hf : IsSec ρ ρ' f) (k : G1 E (2 + 2)) :
    (∀ m₂ : G1 E 2, Integrable (fun m₁ : RightCosetSpace (Gam E 2) => f (lv (Quotient.out m₁) m₂ 0 * k) *
      starRingEnd ℂ (b.f.1 ((Quotient.out m₁ : G1 E 2) : GlobalTheory.CuspRep.GA E 2))) (quotientMeasure (Gam E 2) (BW.mu1 E 2))) ∧
    ell b b' k f = ∫ m₂, (∫ m₁, f (lv (Quotient.out m₁) (Quotient.out m₂) 0 * k) *
      starRingEnd ℂ (b.f.1 ((Quotient.out m₁ : G1 E 2) : GlobalTheory.CuspRep.GA E 2)) ∂quotientMeasure (Gam E 2) (BW.mu1 E 2)) *
      starRingEnd ℂ (b'.f.1 ((Quotient.out m₂ : G1 E 2) : GlobalTheory.CuspRep.GA E 2)) ∂quotientMeasure (Gam E 2) (BW.mu1 E 2) := by
  haveI hfin : IsFiniteMeasure (quotientMeasure (Gam E 2) (BW.mu1 E 2)) := isFiniteMeasure_quotientMeasure (K := E) (n := 2) (BW.mu1 E 2)
  haveI hsf : SFinite (quotientMeasure (Gam E 2) (BW.mu1 E 2)) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  obtain ⟨d, φ, ψ, hφ, hψ, h⟩ := hf.levi k
  have e : ∀ m₁ m₂ : G1 E 2, f (lv m₁ m₂ 0 * k) = ∑ i, φ i m₁ * ψ i m₂ := fun m₁ m₂ =>
    h m₁ m₂ _ (by rw [Subgroup.coe_mul, blkLaws.1, neg_zero, zt_zero, mul_one, mul_one])
  have i₁ := fun i => int_pair b hb (hφ i).1 (hφ i).2.choose_spec.2
  have i₂ := fun i => int_pair b' hb' (hψ i).1 (hψ i).2.choose_spec.2
  refine ⟨fun m₂ => ?_, ?_⟩
  · simp only [e, Finset.sum_mul]
    refine integrable_finset_sum _ fun i _ => ?_
    simpa only [mul_right_comm] using (i₁ i).mul_const (ψ i m₂)
  · simp only [← integral_mul_const]
    refine integral_integral_swap ?_
    simp only [Function.uncurry_def, e, Finset.sum_mul]
    refine integrable_finset_sum _ fun i _ => ((i₁ i).mul_prod (i₂ i)).congr (Eventually.of_forall fun p => ?_)
    ring

private theorem rep_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} {μ : Measure (normOneGL E n)}
    [μ.IsHaarMeasure] {v : L2 μ} {φ : GlobalTheory.CuspRep.Sm E n} (h : BW.Rep μ v φ) {Φ : G1 E n → ℂ} (hc : Continuous Φ)
    (hr : Reps μ v Φ) (g : G1 E n) : φ.1 (g : GlobalTheory.CuspRep.GA E n) = Φ g := by
  have h1 : Continuous fun g : G1 E n => φ.1 (g : GlobalTheory.CuspRep.GA E n) := ((BW.umgOps E n).2 φ h.umg).1.comp continuous_subtype_val
  refine congrFun ((h1.ae_eq_iff_eq μ hc).1 ?_) g
  filter_upwards [hr, (quasiMeasurePreserving_mk (Gam E n) μ).ae h.ae] with y a b
  rw [← a, b]
  obtain ⟨⟨γ, δ, hδ⟩, hγ⟩ := mk_eq_mk_iff.1 (Quotient.out_eq (mk (Gam E n) y))
  rw [← hγ]
  change _ = φ.1 ((γ : GlobalTheory.CuspRep.GA E n) * y)
  exact (hδ ▸ h.umg.left δ y).symm

set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.compLine :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {μ : Measure (normOneGL E (2 + 2))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : Fam 𝔢) (b b' : BW.Blo 𝔢.S 2), BloIn b 𝔵.τ₂ 𝔵.m₂ 𝔵.B₂ → BloIn b' 𝔵.τ₁ 𝔵.m₁ 𝔵.B₁ →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ k ∈ KG E (2 + 2), ∀ (u : ℝ → Eu 𝔵.d') (U : L (Eu 𝔵.d')) (φ : GlobalTheory.CuspRep.Sm E (2 + 2)), Continuous u → HasCompactSupport u →
        (∀ᵐ x : ℝ, U x = u x) → BW.Rep μ (𝔵.A'.J U) φ → ∀ t : Fin (dat2 b b').len → ℝ,
          (dat2 b b').comp (GlobalTheory.CuspRep.rt E (2 + 2) ((k : G1 E (2 + 2)) : GlobalTheory.CuspRep.GA E (2 + 2)) φ).1 t =
            c * Complex.exp ((t (0 : Fin 2) - t (1 : Fin 2) : ℝ) : ℂ) * ell b b' k (𝔵.A'.sec (u ((t (0 : Fin 2) - t (1 : Fin 2)) / 2))) := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 b b' hb hb'
  haveI : CompactSpace (KG E (2 + 2)) := isCompact_iff_compactSpace.1 (blkLaws.2.2.2.2.2.2.2.2.2.2.2 _).1
  have hv : 0 < volN E := (unf μ (BW.mu1 E 2) (Measure.haar : Measure (KG E (2 + 2)))).2
  refine ⟨volN E, by exact_mod_cast hv.ne', fun k hk u U φ hu hu' hU hφ t => ?_⟩
  obtain ⟨F, hF⟩ : ∃ F : G1 E (2 + 2) → ℂ, ∀ g, F g = Complex.exp (2 * (HH g : ℂ)) * 𝔵.A'.sec (u (HH g)) g := ⟨_, fun _ => rfl⟩
  obtain ⟨hP, hB, hS, hR⟩ := UpperTheory.pseudoEisenstein_section_pfun_inBand_slices_reps μ _ _ _ _ 𝔵.A' 𝔵.pair.irr₂ 𝔵.pair.irr₁ u F hu hu' hF
  have hth := rep_eq hφ (thBasic μ F hP.cont hP.rat hB).2.1 (hR U hU)
  obtain ⟨a, ha⟩ : ∃ a, a = t (0 : Fin 2) := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a, a = t (1 : Fin 2) := ⟨_, rfl⟩
  obtain ⟨hsec, hfix⟩ := (𝔵.A'.onto _).1 ⟨u ((a - a') / 2), rfl⟩
  have hray := (secFun _ _ _ _ 𝔵.pair.irr₂ 𝔵.pair.irr₁ _ hsec hfix).ray
  have hFk : ∀ y₁ y₂, F (lv y₁ y₂ ((a - a') / 2) * k) =
      Complex.exp ((a - a' : ℝ) : ℂ) * 𝔵.A'.sec (u ((a - a') / 2)) (lv y₁ y₂ 0 * k) := fun y₁ y₂ => by
    have h1 := hpSpec.1 0 y₁ y₂ ((a - a') / 2) k
    rw [nn, unipOne_zero, one_mul, (hpSpec.2.1 k hk).1, add_zero] at h1
    rw [hF, h1, ← hray ((a - a') / 2) (lv y₁ y₂ 0 * k), ← mul_assoc, blkLaws.2.1, one_mul, one_mul, add_zero]
    congr 2
    push_cast
    ring
  have hct : ∀ y₁ y₂ : G1 E 2, constantTerm 2 (GlobalTheory.CuspRep.rt E (2 + 2) ((k : G1 E (2 + 2)) : GlobalTheory.CuspRep.GA E (2 + 2)) φ).1
      (blk (BW.zt E 2 a * (y₁ : AdelicGLn.AdelicGL E 2)) (BW.zt E 2 a' * (y₂ : AdelicGLn.AdelicGL E 2))) =
      volN E * Complex.exp ((a - a' : ℝ) : ℂ) * 𝔵.A'.sec (u ((a - a') / 2)) (lv y₁ y₂ 0 * k) +
        ∫ X, F (w0 E * nn X * (lv y₁ y₂ ((a - a') / 2) * k)) ∂unipMeasure E (2 + 2) 2 := fun y₁ y₂ => by
    rw [mul_assoc, ← hFk, ← (thCt F hP hB _).2.2.2, constantTerm, pt_eq]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    have hz : ∀ g : AdelicGLn.AdelicGL E (2 + 2), g * BW.zt E (2 + 2) (a + a') = BW.zt E (2 + 2) (a + a') * g := fun g =>
      (centralSection_mul_comm _ g).symm
    change φ.1 (_ * (k : GlobalTheory.CuspRep.GA E (2 + 2))) = th F (unipOne E (2 + 2) 2 X * (lv y₁ y₂ ((a - a') / 2) * k))
    rw [← hth, ← hφ.cen (a + a') ((unipOne E (2 + 2) 2 X * (lv y₁ y₂ ((a - a') / 2) * k) : G1 E (2 + 2)) : GlobalTheory.CuspRep.GA E (2 + 2))]
    congr 1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_unipOne, ← mul_assoc (unipGL X), hz, mul_assoc, mul_assoc]
  have hbU := (BW.cuspUmg E 2 b.f b.cusp).1
  have hbc : Continuous fun g : G1 E 2 => b.f.1 (g : GlobalTheory.CuspRep.GA E 2) := ((BW.umgOps E 2).2 b.f hbU).1.comp continuous_subtype_val
  have hbi : ∀ γ ∈ Gam E 2, ∀ m : G1 E 2, b.f.1 ((γ * m : G1 E 2) : GlobalTheory.CuspRep.GA E 2) = b.f.1 (m : GlobalTheory.CuspRep.GA E 2) := by
    rintro γ ⟨δ, hδ⟩ m
    have h1 := hbU.left δ (m : GlobalTheory.CuspRep.GA E 2)
    rw [hδ] at h1
    exact h1
  obtain ⟨hI, hE⟩ := ell_swap b b' hb hb' hsec k
  rw [← ha, ← ha', hE, ← integral_const_mul]
  change BW.slice (r := 2) (s := 0) b'.f.1 (t (1 : Fin 2)) (BW.slice (r := 2) (s := 2 + 0) b.f.1 (t (0 : Fin 2)) _) 1 = _
  rw [← ha, ← ha', BW.slice]
  refine integral_congr_ae (Eventually.of_forall fun y₂ => ?_)
  obtain ⟨hL, hL0⟩ := UpperTheory.constantTerm_pairing_vanishes_of_orthogonal (BW.mu1 E 2) _ _ 𝔵.τ₂ F _ hP hB hS 𝔵.pair.orth hbc hbi hb.mem (Quotient.out y₂) ((a - a') / 2) k hk
  simp only
  rw [ct_nil, lev_eq, blk_nil, ← mul_assoc, BW.slice]
  congr 1
  rw [← integral_const_mul, ← add_zero (∫ _, _ * (_ * _) ∂_), ← hL0, ← integral_add ((hI _).const_mul _) hL]
  refine integral_congr_ae (Eventually.of_forall fun y₁ => ?_)
  simp only
  rw [lev_eq]
  erw [hct]
  ring
