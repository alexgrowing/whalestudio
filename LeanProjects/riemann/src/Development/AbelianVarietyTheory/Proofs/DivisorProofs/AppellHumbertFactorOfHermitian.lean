import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowEqThetaLevelChar
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ReFormPosOfThetaNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleHermPos

open Complex Matrix
open CubeValues SymmetricSemicharacter ComplexPoints AffinePointValues AnalyticHom

variable {g : ℕ}

lemma form_smul (c : ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    z ⬝ᵥ ((c : ℂ) • Hm).mulVec (star w) = c * (z ⬝ᵥ Hm.mulVec (star w)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma isHermitian_smul {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (c : ℝ) :
    ((c : ℂ) • Hm).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_smul, hH.eq, Complex.star_def, Complex.conj_ofReal]

lemma theta_add_smul_eq (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (χ : Λ → ℂ) (hχ : ∀ l, ‖χ l‖ = 1)
    {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ)
    (htr : ∀ (l : Λ) z, θ (z + l) =
      (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z)
    {v : Fin g → ℂ} (hv : Hm.mulVec (star v) = 0) (z : Fin g → ℂ) (t : ℂ) :
    θ (z + t • v) = θ z := by
  obtain ⟨C, hC⟩ := ThetaPositivity.exists_norm_le Λ hH χ hχ hθ.continuous htr
  have hq : ∀ t : ℂ, ((z + t • v) ⬝ᵥ Hm.mulVec (star (z + t • v))) = z ⬝ᵥ Hm.mulVec (star z) := by
    intro t
    have h1 : Hm.mulVec (star (t • v)) = 0 := by rw [star_smul, mulVec_smul, hv, smul_zero]
    have h2 : v ⬝ᵥ Hm.mulVec (star z) = 0 := by
      rw [ThetaPositivity.form_conj hH z v, hv, dotProduct_zero, star_zero]
    rw [star_add, mulVec_add, h1, add_zero, add_dotProduct, smul_dotProduct, h2, smul_zero, add_zero]
  have hd : Differentiable ℂ fun t : ℂ => θ (z + t • v) :=
    hθ.comp ((differentiable_const _).add (differentiable_id.smul_const v))
  have hb : Bornology.IsBounded (Set.range fun t : ℂ => θ (z + t • v)) := by
    refine isBounded_iff_forall_norm_le.2
      ⟨C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re), ?_⟩
    rintro _ ⟨t, rfl⟩
    have := hC (z + t • v)
    rwa [hq t] at this
  have := hd.apply_eq_apply_of_bounded hb t 0
  simpa using this

lemma eq_zero_of_smul_mem (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] {v : Fin g → ℂ}
    (h : ∀ t : ℂ, t • v ∈ Λ) : v = 0 := by
  have hc : Continuous fun t : ℂ => (⟨t • v, h t⟩ : Λ) :=
    (continuous_id.smul continuous_const).subtype_mk _
  have := PreconnectedSpace.constant inferInstance hc (x := 1) (y := 0)
  simpa using congrArg Subtype.val this

theorem re_form_pos_of_relAmple :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB →
    Out.RelAmple A L → ∀ (g : ℕ) (u : HolUnif A L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
      Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) →
      (∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
        u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
          Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l)) →
      ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := by
  intro A _ _ hA L hL ha g u Hm χ hH hχ hfr
  haveI : Smooth A.hom := hA.smooth
  haveI := isReduced_of_smooth_complex _ A.hom inferInstance
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  obtain ⟨N, hN, M, s, hcov, hD⟩ := ha ⊤ (isAffineOpen_top _)
  choose hDa r hr hsurj using hD
  have hrg : Set.range (𝟙 A.left : A.left ⟶ A.left) ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι := by
    intro x _
    rw [Scheme.Opens.range_ι]
    trivial
  obtain ⟨σ, hσ⟩ : ∃ σ : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, σ ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrg⟩
  choose s' hs' using fun i => exists_sec_pow L _ σ hσ N A.hom (s i)
  choose θ hθd hθfn _hθu hθper using fun i => ThetaBundleSec.exists_fn u hL N (s' i)
  choose ch hch using fun z => PullHermitian.exists_chart (u.ex z).left hL
  have hU : ∀ z, ⊤ ≤ ((u.ex z).left ≫ σ) ⁻¹ᵁ (Out.powOver A L ⊤ N).U (fun _ => ch z) := fun z =>
    le_preimage_mono (u.ex z).left (chart_le L _ σ hσ N fun _ => ch z)
      ((le_preimage_lbPow _ L N fun _ => ch z).2 (hch z))
  have hval : ∀ i z, valAt' ((u.ex z).left ≫ σ) ((Out.powOver A L ⊤ N).U fun _ => ch z)
      ((s i).f fun _ => ch z) = θ i z * u.fr (ch z) z ^ N := fun i z =>
    have k := (le_preimage_lbPow _ L N fun _ => ch z).2 (hch z)
    (hs' i _ _ k).symm.trans (hθfn i _ z k)
  have hfr0 : ∀ z, u.fr (ch z) z ^ N ≠ 0 := fun z => pow_ne_zero _ (u.fr_ne _ _ (hch z))
  have hmem : ∀ i z, ⊤ ≤ ((u.ex z).left ≫ σ) ⁻¹ᵁ Out.nonzeroLocus (s i) ↔ θ i z ≠ 0 := fun i z => by
    rw [le_preimage_nonzeroLocus _ (s i) _ (hU z), hval, mul_ne_zero_iff_right (hfr0 z)]
  have hcov' : ∀ z, ∃ i, θ i z ≠ 0 := fun z => by
    have hz : ((u.ex z).left ≫ σ) (default : PrimeSpectrum ℂ) ∈ ⨆ i, Out.nonzeroLocus (s i) := by
      rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact ⟨i, (hmem i z).1 ((top_le_preimage_iff_mem _ _).2 hi)⟩

  set HN : Matrix (Fin g) (Fin g) ℂ := ((N : ℝ) : ℂ) • Hm with hHNdef
  have hHN : HN.IsHermitian := isHermitian_smul hH _
  have htr : ∀ i (l : u.Λ) z, θ i (z + l) =
      (χ l ^ N * cexp (Real.pi * (z ⬝ᵥ HN.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ HN.mulVec (star (l : Fin g → ℂ))))) * θ i z := by
    intro i l z
    have hper : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
    rw [hθper i z (z + l) _ hper fun j hj => hfr l j z hj, form_smul, form_smul, mul_pow,
      ← Complex.exp_nat_mul]
    congr 3
    push_cast
    ring
  have hχN : ∀ l, ‖χ l ^ N‖ = 1 := fun l => by rw [norm_pow, hχ, one_pow]

  obtain ⟨i0, hi0⟩ := hcov' 0
  have hne : θ i0 ≠ 0 := fun h => hi0 (by rw [h]; rfl)
  obtain ⟨C, hC⟩ := ThetaPositivity.exists_norm_le u.Λ hHN (fun l => χ l ^ N) hχN
    (hθd i0).continuous (htr i0)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hnn : ∀ w : Fin g → ℂ, 0 ≤ (w ⬝ᵥ Hm.mulVec (star w)).re := fun w => by
    by_contra hw
    push_neg at hw
    have hw' : (w ⬝ᵥ HN.mulVec (star w)).re < 0 := by
      rw [form_smul, re_ofReal_mul]
      exact mul_neg_of_pos_of_neg hNpos hw
    exact hne (ThetaPositivity.eq_zero_of_neg hHN (hθd i0) hC hw')

  have hrval : ∀ i j w, θ i w ≠ 0 →
      valAt' ((u.ex w).left ≫ σ) (Out.nonzeroLocus (s i)) (r i j) * θ i w = θ j w := by
    intro i j w hw
    have hw' := (hmem i w).2 hw
    have k := (le_preimage_inf _ _ _).2 ⟨hw', hU w⟩
    have k₁ := congrArg (valAt' ((u.ex w).left ≫ σ) _) (hr i j fun _ => ch w)
    rw [val_mul _ k, val_resG _ _ k, val_resG _ _ k, val_resG _ _ k, hval, hval,
      ← _root_.mul_assoc] at k₁
    exact (mul_right_cancel₀ (hfr0 w) k₁).symm
  have hc : ∀ w w', ((u.ex w).left ≫ σ) ≫ (A.hom ∣_ ⊤) = ((u.ex w').left ≫ σ) ≫ (A.hom ∣_ ⊤) := by
    intro w w'
    rw [← cancel_mono (⊤ : (Sp ℂ).Opens).ι]
    simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hσ, Over.w]

  have hker : ∀ v : Fin g → ℂ, Hm.mulVec (star v) = 0 → v = 0 := by
    intro v hv
    have hvN : HN.mulVec (star v) = 0 := by rw [hHNdef, Matrix.smul_mulVec, hv, smul_zero]
    have hinv : ∀ i (t : ℂ), θ i (t • v) = θ i 0 := fun i t => by
      simpa using theta_add_smul_eq u.Λ hHN _ hχN (hθd i) (htr i) hvN 0 t
    have hpt : ∀ t : ℂ, (u.ex (t • v)).left ≫ σ = (u.ex 0).left ≫ σ := by
      intro t
      obtain ⟨i, h0⟩ := hcov' 0
      have h0' : θ i (t • v) ≠ 0 := by rw [hinv]; exact h0
      have m0 := (hmem i 0).2 h0
      have mt := (hmem i _).2 h0'
      refine UnifTangent.eq_of_values (hDa i) mt m0 fun f => ?_
      obtain ⟨Q, rfl⟩ := hsurj i f
      induction Q using MvPolynomial.induction_on with
      | C a =>
        rw [MvPolynomial.eval₂Hom_C]
        exact (val_appLE _ (A.hom ∣_ ⊤) ⊤ _ _ a mt).trans
          ((congrArg (fun y => valAt' y ⊤ a) (hc _ 0)).trans (val_appLE _ (A.hom ∣_ ⊤) ⊤ _ _ a m0).symm)
      | add Q Q' h h' => rw [map_add, val_add _ mt, val_add _ m0, h, h']
      | mul_X Q j h =>
        rw [map_mul, val_mul _ mt, val_mul _ m0, h, MvPolynomial.eval₂Hom_X']
        congr 1
        have a1 := hrval i j _ h0'
        have a2 := hrval i j 0 h0
        rw [hinv, hinv] at a1
        exact mul_right_cancel₀ h0 (a1.trans a2.symm)
    refine eq_zero_of_smul_mem u.Λ fun t => (u.ker _).1 ?_
    have e : u.ex (t • v) = u.ex 0 := by
      ext1
      have := hpt t =≫ (A.hom ⁻¹ᵁ ⊤).ι
      rwa [Category.assoc, Category.assoc, hσ, Category.comp_id, Category.comp_id] at this
    have e0 : u.ex 0 = 1 := by
      have h00 := u.ex_add 0 0
      rw [add_zero] at h00
      exact (mul_eq_left.mp h00.symm)
    rw [e, e0]

  intro z hz
  have him : ∀ w : Fin g → ℂ, (w ⬝ᵥ Hm.mulVec (star w)).im = 0 := fun w => by
    have h := congrArg Complex.im (ThetaPositivity.form_conj hH w w)
    simp only [star_def, conj_im] at h
    linarith
  refine lt_of_le_of_ne (hnn z) fun h0 => hz (hker z ?_)
  open scoped ComplexOrder in
  have hpsd : Hm.PosSemidef := by
    refine posSemidef_iff_dotProduct_mulVec.mpr ⟨hH, fun x => ?_⟩
    have h1 := hnn (star x)
    have h2 := him (star x)
    rw [star_star] at h1 h2
    exact Complex.le_def.mpr ⟨h1, h2.symm⟩
  refine (hpsd.dotProduct_mulVec_zero_iff (star z)).mp ?_
  rw [star_star]
  exact Complex.ext h0.symm (him z)

end GlobalTheory.AmpleHermPos
