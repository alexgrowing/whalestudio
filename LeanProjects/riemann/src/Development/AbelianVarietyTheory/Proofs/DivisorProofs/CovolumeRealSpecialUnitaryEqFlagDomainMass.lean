import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnRmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarSpecialUnitaryLyingOverFlagDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarSpecialUnitaryEqSmulHaarStatement

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal Pointwise

noncomputable section

namespace GlobalTheory.SUCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem countable_numberField : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable

theorem countable_GL : Countable (GL (Fin r) E) := by
  haveI := countable_numberField (E := E)
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  exact Function.Injective.countable (f := (Units.val : GL (Fin r) E → Matrix (Fin r) (Fin r) E))
    fun a b h => Units.ext h

def idF (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

def invB {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) : Frame Ψ r :=
  fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

theorem rmul_assoc {Ψ : Finset (E →+* ℂ)} (y b b' : Frame Ψ r) :
    rmul (rmul y b) b' = rmul y (rmul b b') := by
  funext τ; exact Matrix.mul_assoc (mat y τ) (mat b τ) (mat b' τ)

theorem rmul_idF {Ψ : Finset (E →+* ℂ)} (y : Frame Ψ r) : rmul y (idF Ψ r) = y := by
  funext τ; exact Matrix.mul_one (mat y τ)

theorem idF_mem (Ψ : Finset (E →+* ℂ)) (r : ℕ) : idF Ψ r ∈ Bor Ψ r := fun τ =>
  ⟨by show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0; simp,
    fun a c h => by show (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0; exact Matrix.one_apply_ne h.ne'⟩

theorem tri_of_mem {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) (τ : Ψ) :
    (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h

theorem rmul_mem {Ψ : Finset (E →+* ℂ)} {b b' : Frame Ψ r} (hb : b ∈ Bor Ψ r) (hb' : b' ∈ Bor Ψ r) :
    rmul b b' ∈ Bor Ψ r := by
  intro τ
  have hm : mat (rmul b b') τ = mat b τ * mat b' τ := rfl
  refine ⟨by rw [hm, Matrix.det_mul]; exact mul_ne_zero (hb τ).1 (hb' τ).1, fun a c h => ?_⟩
  exact ((tri_of_mem hb τ).mul (tri_of_mem hb' τ)) h

theorem invB_mem {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : invB b ∈ Bor Ψ r := by
  intro τ
  have hm : mat (invB b) τ = (mat b τ)⁻¹ := rfl
  have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.mpr (hb τ).1
  letI := Matrix.invertibleOfIsUnitDet _ hu
  refine ⟨by rw [hm]; exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero, fun a c h => ?_⟩
  exact (Matrix.blockTriangular_inv_of_blockTriangular (tri_of_mem hb τ)) h

theorem rmul_invB {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : rmul b (invB b) = idF Ψ r := by
  funext τ
  exact Matrix.mul_nonsing_inv (mat b τ) (isUnit_iff_ne_zero.mpr (hb τ).1)

theorem lact_rmul {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (y b : Frame Ψ r) :
    lact γ (rmul y b) = rmul (lact γ y) b := by
  funext τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat y τ) (mat b τ)).symm

theorem lact_mul {Ψ : Finset (E →+* ℂ)} (γ δ : GL (Fin r) E) (y : Frame Ψ r) :
    lact (γ * δ) y = lact γ (lact δ y) := by
  funext τ
  show ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ =
    (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem lact_one {Ψ : Finset (E →+* ℂ)} (y : Frame Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ = mat y τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem continuous_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) : Continuous (lact (Ψ := Ψ) γ) := by
  refine continuous_pi fun τ => ?_
  exact continuous_const.matrix_mul (continuous_apply τ : Continuous fun y : Frame Ψ r => mat y τ)

theorem measurableSet_Bor (Ψ : Finset (E →+* ℂ)) (r : ℕ) : MeasurableSet (Bor Ψ r) := by
  have hc : ∀ τ : Ψ, Continuous fun b : Frame Ψ r => mat b τ := fun τ => continuous_apply τ
  have e : Bor Ψ r = ⋂ τ : Ψ, ({b | (mat b τ).det ≠ 0} ∩
      ⋂ a : Fin r, ⋂ c : Fin r, {b : Frame Ψ r | c < a → b τ a c = 0}) := by
    ext b; simp [Bor]
  rw [e]
  refine MeasurableSet.iInter fun τ => (IsOpen.measurableSet ?_).inter
    (MeasurableSet.iInter fun a => MeasurableSet.iInter fun c => ?_)
  · exact isOpen_ne_fun (hc τ).matrix_det continuous_const
  · by_cases h : c < a
    · simp only [h, true_implies]
      exact (isClosed_eq ((continuous_apply c).comp ((continuous_apply a).comp (continuous_apply τ)))
        continuous_const).measurableSet
    · simp [h]

def frOf (X : Data E r) (x : Frame X.Ψ r) (g : realSU X.Ψ X.Gm) : Frame X.Ψ r :=
  X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x

theorem frOf_mul (X : Data E r) (x : Frame X.Ψ r) (h g : realSU X.Ψ X.Gm) :
    frOf X x (h * g) = X.lmulC (fun τ => (((h : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ :
      Matrix (Fin r) (Fin r) ℂ)) (frOf X x g) := by
  funext τ
  show ((((h * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      mat x τ = ((((h : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      (((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ)
  rw [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, Matrix.mul_assoc]

theorem frOf_smul (X : Data E r) (x : Frame X.Ψ r) (h g : realSU X.Ψ X.Gm) (c : GL (Fin r) E)
    (e : embGL X.Ψ r c = (h : X.Ψ → GL (Fin r) ℂ)) : frOf X x (h * g) = lact c (frOf X x g) := by
  rw [frOf_mul, ← e]; rfl

theorem continuous_frOf (X : Data E r) (x : Frame X.Ψ r) : Continuous (frOf X x) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun g : realSU X.Ψ X.Gm =>
    ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ
  exact (Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)).matrix_mul
    continuous_const

end GlobalTheory.SUCovol

namespace GlobalTheory.SUCovol

theorem covolume_realSU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X))) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)], 1 ≤ r → (∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1) → IsOrth X x → IsFundSet X x FF → ENNReal.ofReal (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) * muF X x FF = covolume (inReal X.Ψ X.Gm X.Γ) (realSU X.Ψ X.Gm) (riemHaar X.Ψ X.Gm x) := by
  intro E _ _ _ r X x FF _ _ hr hdet hx hFF
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0∞, C = ENNReal.ofReal (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) *
      Real.sqrt r) ^ fdeg E) := ⟨_, rfl⟩
  rw [← hC]
  obtain ⟨ν, hν, hνφ⟩ := GlobalTheory.T.exists_haar_specialUnitary_lying_over_flagDomain E r X x hr hx
  have hμ : riemHaar X.Ψ X.Gm x = C • ν := by rw [hC]; exact GlobalTheory.T.riemannianHaar_specialUnitary_eq_smul_haar E r X x ν hr hx hν hνφ
  have KF : ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) →
      ∫⁻ g, φ (frOf X x g) ∂riemHaar X.Ψ X.Gm x = C * ∫⁻ z, φ (cpt X x z) ∂muF X x := by
    intro φ hφ hB
    rw [hμ, lintegral_smul_measure, smul_eq_mul]
    exact congrArg (C * ·) (hνφ φ hφ hB)
  obtain ⟨hFFm, hFFO, hFFinj, hFFae⟩ := hFF
  haveI := countable_GL (E := E) (r := r)

  obtain ⟨T, hTdef⟩ : ∃ T : Set (Frame X.Ψ r), T = (fun p : ReciprocityTheory.L2DbarEstimates.V (nd X) × Frame X.Ψ r =>
      rmul (cpt X x p.1) p.2) '' (FF ×ˢ Bor X.Ψ r) := ⟨_, rfl⟩
  have memT : ∀ y, y ∈ T ↔ ∃ z ∈ FF, ∃ b ∈ Bor X.Ψ r, y = rmul (cpt X x z) b := by
    intro y; rw [hTdef]; constructor
    · rintro ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩; exact ⟨z, hz, b, hb, rfl⟩
    · rintro ⟨z, hz, b, hb, rfl⟩; exact ⟨(z, b), ⟨hz, hb⟩, rfl⟩
  have hTm : MeasurableSet T := by
    rw [hTdef]
    haveI : PolishSpace (Frame X.Ψ r) := {}
    haveI : PolishSpace (ReciprocityTheory.L2DbarEstimates.V (nd X) × Frame X.Ψ r) := {}
    refine (hFFm.prod (measurableSet_Bor X.Ψ r)).image_of_continuousOn_injOn ?_ ?_
    · exact ((GlobalTheory.UnitaryInvMeasure.continuous_rmul X).comp
        (((KU.cont_cpt X x).comp continuous_fst).prodMk continuous_snd)).continuousOn
    · intro p hp q hq h
      obtain ⟨h1, h2⟩ := KU.cpt_inj X hx hp.2 hq.2 h
      exact Prod.ext h1 h2
  have hTB : ∀ y, ∀ b ∈ Bor X.Ψ r, rmul y b ∈ T ↔ y ∈ T := by
    intro y b hb
    constructor
    · intro h
      obtain ⟨z, hz, b', hb', e⟩ := (memT _).1 h
      refine (memT _).2 ⟨z, hz, rmul b' (invB b), rmul_mem hb' (invB_mem hb), ?_⟩
      rw [← rmul_assoc, ← e, rmul_assoc, rmul_invB hb, rmul_idF]
    · intro h
      obtain ⟨z, hz, b', hb', e⟩ := (memT _).1 h
      exact (memT _).2 ⟨z, hz, rmul b' b, rmul_mem hb' hb, by rw [e, rmul_assoc]⟩
  have hcptT : ∀ z, cpt X x z ∈ T ↔ z ∈ FF := by
    intro z; constructor
    · intro h
      obtain ⟨z', hz', b, hb, e⟩ := (memT _).1 h
      have e' : rmul (cpt X x z) (idF X.Ψ r) = rmul (cpt X x z') b := by rw [rmul_idF]; exact e
      rw [(KU.cpt_inj X hx (idF_mem X.Ψ r) hb e').1]; exact hz'
    · intro hz; exact (memT _).2 ⟨z, hz, idF X.Ψ r, idF_mem X.Ψ r, (rmul_idF _).symm⟩

  obtain ⟨S, hSdef⟩ : ∃ S : Set (Frame X.Ψ r), S = ⋃ γ : X.Γ, (lact ((γ : GL (Fin r) E)⁻¹)) ⁻¹' T :=
    ⟨_, rfl⟩
  have memS : ∀ y, y ∈ S ↔ ∃ γ ∈ X.Γ, lact γ⁻¹ y ∈ T := by
    intro y; rw [hSdef, Set.mem_iUnion]
    exact ⟨fun ⟨γ, h⟩ => ⟨γ, γ.2, h⟩, fun ⟨γ, hγ, h⟩ => ⟨⟨γ, hγ⟩, h⟩⟩
  have hSm : MeasurableSet S := by
    rw [hSdef]; exact MeasurableSet.iUnion fun γ => (continuous_lact _).measurable hTm
  have hSB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, rmul y b ∈ S ↔ y ∈ S := by
    intro y _ b hb
    rw [memS, memS]
    simp only [lact_rmul]
    exact exists_congr fun γ => and_congr_right fun _ => hTB _ b hb
  have hfm : Measurable (frOf X x) := (continuous_frOf X x).measurable
  have hind : ∀ (A : Set (Frame X.Ψ r)) (y y' : Frame X.Ψ r), (y ∈ A ↔ y' ∈ A) →
      A.indicator (1 : Frame X.Ψ r → ℝ≥0∞) y = A.indicator 1 y' := by
    intro A y y' h
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (h.1 hy)]; rfl
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (mt h.2 hy)]
  have hpre : ∀ A : Set (Frame X.Ψ r), (fun g => A.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (frOf X x g)) =
      (frOf X x ⁻¹' A).indicator 1 := by
    intro A; funext g
    by_cases hg : frOf X x g ∈ A
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (show g ∈ frOf X x ⁻¹' A from hg)]; rfl
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (show g ∉ frOf X x ⁻¹' A from hg)]

  have hnull : riemHaar X.Ψ X.Gm x (frOf X x ⁻¹' Sᶜ) = 0 := by
    have hφm : Measurable (Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞)) := measurable_one.indicator hSm.compl
    have hφB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
        Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul y b) = Sᶜ.indicator 1 y := by
      intro y hy b hb; exact hind _ _ _ (by rw [Set.mem_compl_iff, Set.mem_compl_iff, hSB y hy b hb])
    have h := KF _ hφm hφB
    have hzero : ∫⁻ z, Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x z) ∂muF X x = 0 := by
      rw [← lintegral_zero (μ := muF X x)]
      refine lintegral_congr_ae ?_
      filter_upwards [hFFae] with z hz
      obtain ⟨z', hz', γ, hγ, b, hb, e⟩ := hz
      have hS : cpt X x z ∈ S := (memS _).2 ⟨γ, hγ, by
        rw [e, ← lact_mul, inv_mul_cancel, lact_one]; exact (memT _).2 ⟨z', hz', b, hb, rfl⟩⟩
      exact Set.indicator_of_notMem (Set.notMem_compl_iff.2 hS) _
    rw [hzero, mul_zero] at h
    rw [hpre, lintegral_indicator_one (hfm hSm.compl)] at h
    exact h

  have hcov : ∀ᵐ g ∂riemHaar X.Ψ X.Gm x, ∃ γ' : inReal X.Ψ X.Gm X.Γ, γ' • g ∈ frOf X x ⁻¹' T := by
    have hae : ∀ᵐ g ∂riemHaar X.Ψ X.Gm x, frOf X x g ∈ S := by
      rw [ae_iff]; exact hnull
    filter_upwards [hae] with g hg
    obtain ⟨γ, hγ, hγT⟩ := (memS _).1 hg
    have hδ : γ⁻¹ ∈ X.Γ := X.Γ.inv_mem hγ
    have hmem : embGL X.Ψ r γ⁻¹ ∈ realSU X.Ψ X.Gm :=
      embGL_mem_realSU X.Ψ X.Gm γ⁻¹ (hdet _ hδ) (X.Γ_stab _ hδ).1
    refine ⟨⟨⟨embGL X.Ψ r γ⁻¹, hmem⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ⁻¹, hδ, rfl⟩)⟩, ?_⟩
    rw [Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, frOf_smul X x _ g γ⁻¹ rfl]
    exact hγT
  have hdisj : Pairwise (Function.onFun (AEDisjoint (riemHaar X.Ψ X.Gm x))
      fun γ' : inReal X.Ψ X.Gm X.Γ => γ' • (frOf X x ⁻¹' T)) := by
    intro γ1 γ2 hne
    refine Disjoint.aedisjoint ?_
    rw [Set.disjoint_left]
    intro g hg1 hg2
    obtain ⟨h1, hh1, rfl⟩ := Set.mem_smul_set.1 hg1
    obtain ⟨h2, hh2, he⟩ := Set.mem_smul_set.1 hg2
    apply hne
    obtain ⟨c1, hc1, e1⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ1.2)
    obtain ⟨c2, hc2, e2⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ2.2)
    obtain ⟨z1, hz1, b1, hb1, hf1⟩ := (memT _).1 hh1
    obtain ⟨z2, hz2, b2, hb2, hf2⟩ := (memT _).1 hh2
    have hfr : lact c2 (frOf X x h2) = lact c1 (frOf X x h1) := by
      have := congrArg (frOf X x) he
      rwa [Subgroup.smul_def, Subgroup.smul_def, smul_eq_mul, smul_eq_mul,
        frOf_smul X x _ h2 c2 e2, frOf_smul X x _ h1 c1 e1] at this
    have hc : c2⁻¹ * c1 ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem hc2) hc1
    have h21 : rmul (cpt X x z2) b2 = lact (c2⁻¹ * c1) (rmul (cpt X x z1) b1) := by
      rw [← hf2, ← hf1, lact_mul, ← hfr, ← lact_mul, inv_mul_cancel, lact_one]
    have hz : z1 = z2 := by
      refine hFFinj z1 hz1 z2 hz2 _ hc (rmul b1 (invB b2)) (rmul_mem hb1 (invB_mem hb2)) ?_
      rw [← rmul_assoc, lact_rmul, ← h21, rmul_assoc, rmul_invB hb2, rmul_idF]
    subst hz
    have hfree : lact (c2⁻¹ * c1) (cpt X x z1) = rmul (cpt X x z1) (rmul b2 (invB b1)) := by
      rw [← rmul_assoc, h21, lact_rmul, rmul_assoc, rmul_invB hb1, rmul_idF]
    have h1' := X.Γ_free _ hc (cpt X x z1) (hFFO hz1) _ (rmul_mem hb2 (invB_mem hb1)) hfree
    have hcc : c1 = c2 := (inv_mul_eq_one.1 h1').symm
    subst hcc
    exact Subtype.ext (Subtype.ext (e1.symm.trans e2))

  have hDμ : riemHaar X.Ψ X.Gm x (frOf X x ⁻¹' T) = C * muF X x FF := by
    have hφm : Measurable (T.indicator (1 : Frame X.Ψ r → ℝ≥0∞)) := measurable_one.indicator hTm
    have hφB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
        T.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul y b) = T.indicator 1 y := by
      intro y _ b hb; exact hind _ _ _ (hTB y b hb)
    have h := KF _ hφm hφB
    have e2 : (fun z => T.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x z)) = FF.indicator 1 := by
      funext z
      by_cases hz : z ∈ FF
      · rw [Set.indicator_of_mem ((hcptT z).2 hz), Set.indicator_of_mem hz]; rfl
      · rw [Set.indicator_of_notMem (mt (hcptT z).1 hz), Set.indicator_of_notMem hz]
    rw [hpre, e2, lintegral_indicator_one (hfm hTm), lintegral_indicator_one hFFm] at h
    exact h
  have hfd : IsFundamentalDomain (inReal X.Ψ X.Gm X.Γ) (frOf X x ⁻¹' T) (riemHaar X.Ψ X.Gm x) :=
    ⟨(hfm hTm).nullMeasurableSet, hcov, hdisj⟩
  haveI : Countable (inReal X.Ψ X.Gm X.Γ) := by
    let f : {γ : X.Γ // embGL X.Ψ r (γ : GL (Fin r) E) ∈ realSU X.Ψ X.Gm} → inReal X.Ψ X.Gm X.Γ :=
      fun p => ⟨⟨embGL X.Ψ r p.1, p.2⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨p.1, p.1.2, rfl⟩)⟩
    refine Function.Surjective.countable (f := f) ?_
    rintro ⟨⟨g, hg⟩, hgm⟩
    obtain ⟨c, hc, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hgm)
    exact ⟨⟨⟨c, hc⟩, e ▸ hg⟩, Subtype.ext (Subtype.ext e)⟩
  haveI : MeasurableConstSMul (inReal X.Ψ X.Gm X.Γ) (realSU X.Ψ X.Gm) :=
    ⟨fun c => by
      show Measurable fun a : realSU X.Ψ X.Gm => (c : realSU X.Ψ X.Gm) * a
      exact (continuous_mul_left _).measurable⟩
  haveI : (riemHaar X.Ψ X.Gm x).IsMulLeftInvariant := by rw [hμ]; infer_instance
  haveI : SMulInvariantMeasure (inReal X.Ψ X.Gm X.Γ) (realSU X.Ψ X.Gm) (riemHaar X.Ψ X.Gm x) :=
    ⟨fun c s _ => measure_preimage_mul (riemHaar X.Ψ X.Gm x) (c : realSU X.Ψ X.Gm) s⟩
  rw [hfd.covolume_eq_volume, hDμ]

end GlobalTheory.SUCovol
