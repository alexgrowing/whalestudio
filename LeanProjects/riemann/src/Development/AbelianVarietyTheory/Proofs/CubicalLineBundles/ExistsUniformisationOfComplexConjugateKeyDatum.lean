import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsPolFibreOfKeyPB

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.ConjUnif

open GlobalTheory.ArchMetricCompare

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g : ℕ}

theorem le_pull_id (x : Sp ℂ ⟶ A.left) (j : (L.pull (𝟙 A.left)).ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull (𝟙 A.left)).U j ↔ ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit) := by
  rw [le_pull_iff, Category.comp_id]

def pullId (u : HolUnif A L g) : HolUnif A (L.pull (𝟙 A.left)) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr j := u.fr (j PUnit.unit)
  fr_hol j := by
    have e : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull (𝟙 A.left)).U j} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)} :=
      Set.ext fun z => le_pull_id _ j
    rw [e]
    exact u.fr_hol _
  fr_ne j z hz := u.fr_ne _ z ((le_pull_id _ j).1 hz)
  fr_compat j j' z hz := by
    obtain ⟨hj, hj'⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [val_pull_g L _ _ j j' hz, u.fr_compat _ _ z
      ((top_le_preimage_inf _ _ _).2 ⟨(le_pull_id _ j).1 hj, (le_pull_id _ j').1 hj'⟩)]
    congr 2

variable {ψ : A'.left ⟶ A.left} (h : IsGrpPullback A' A cj ψ)

theorem cj_le (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (j : (L.pull ψ).ι) :
    ⊤ ≤ (cjPt h x).left ⁻¹ᵁ (L.pull ψ).U j ↔ ⊤ ≤ x.left ⁻¹ᵁ L.U (j PUnit.unit) := by
  refine (le_pull_iff L _ _ j).trans ?_
  rw [cjPt_comp]
  exact le_cj_iff _ _

def conjPull (u : HolUnif A L g) : HolUnif A' (L.pull ψ) g where
  ex := (cjUnif h (pullId u)).ex
  ex_add := (cjUnif h (pullId u)).ex_add
  ex_onto := (cjUnif h (pullId u)).ex_onto
  Λ := (cjUnif h (pullId u)).Λ
  ker := (cjUnif h (pullId u)).ker
  discrete := (cjUnif h (pullId u)).discrete
  full := (cjUnif h (pullId u)).full
  hol := (cjUnif h (pullId u)).hol
  fr j z := star (u.fr (j PUnit.unit) (star z))
  fr_hol j := by
    have e : {z | ⊤ ≤ ((cjUnif h (pullId u)).ex z).left ⁻¹ᵁ (L.pull ψ).U j} =
        {z | star z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)}} :=
      Set.ext fun z => cj_le h _ j
    rw [e]
    exact differentiableOn_star (u.hol _ 0).1 (u.fr_hol _)
  fr_ne j z hz := star_ne_zero.2 (u.fr_ne _ _ ((cj_le h _ j).1 hz))
  fr_compat j j' z hz := by
    obtain ⟨hj, hj'⟩ := (top_le_preimage_inf _ _ _).1 hz
    have hm := (top_le_preimage_inf _ _ _).2 ⟨(cj_le h _ j).1 hj, (cj_le h _ j').1 hj'⟩
    rw [val_pull_g L _ _ j j' hz, u.fr_compat _ _ _ hm, star_mul']
    congr 1
    exact ((congrArg (fun x => valAt' x _ _) (cjPt_comp h (u.ex (star z)))).trans (val_cj _ _ _)).symm

theorem conjPull_isAH (u : HolUnif A L g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hA : u.IsAH Hm χ) :
    (conjPull h u).IsAH (Hm.map star) fun l => star (χ ⟨star l.1, l.2⟩) := by
  have h0 : (pullId u).IsAH Hm χ :=
    ⟨hA.1, hA.2.1, hA.2.2.1, fun l j z hj => hA.2.2.2 l _ z ((le_pull_id _ j).1 hj)⟩
  have h1 := cj_isAH h _ h0
  exact ⟨h1.1, h1.2.1, h1.2.2.1, fun l j z hj =>
    h1.2.2.2 l j z ((cj_le_pull h _ j).2 ((le_pull_id _ j).2 ((cj_le h _ j).1 hj)))⟩

theorem exists_inv {X : Scheme.{0}} {M N : LB X} (w : LB.Iso M N) (hw : w.IsGen) :
    ∃ w' : LB.Iso N M, w'.IsGen ∧ ∀ (x : Sp ℂ ⟶ X) (j : N.ι) (i : M.ι), ⊤ ≤ x ⁻¹ᵁ (N.U j ⊓ M.U i) →
      valAt' x (M.U i ⊓ N.U j) (w'.s (i, j)).val = (valAt' x (N.U j ⊓ M.U i) (w.s (j, i)).val)⁻¹ := by
  have le : ∀ p : M.ι × N.ι, M.U p.1 ⊓ N.U p.2 ≤ N.U p.2 ⊓ M.U p.1 := fun p y hy => ⟨hy.2, hy.1⟩
  refine ⟨⟨fun p => (res (le p) (w.s (p.2, p.1)))⁻¹⟩, fun p q => unit_ext fun y hy => ?_, fun x j i hx => ?_⟩
  · have hm : (𝟙 X : X ⟶ X) y ∈ N.U p.2 ⊓ M.U p.1 ⊓ (N.U q.2 ⊓ M.U q.1) := ⟨le p hy.1, le q hy.2⟩
    have e := congrArg (gm (𝟙 X) y (N.U p.2 ⊓ M.U p.1 ⊓ (N.U q.2 ⊓ M.U q.1))) (hw (p.2, p.1) (q.2, q.1))
    have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div M N (𝟙 X) y (p.2, p.1) (q.2, q.1) hm) (gm_res _ y _ hm _))))
    have v : ∀ p : M.ι × N.ι, y ∈ M.U p.1 ⊓ N.U p.2 →
        gm (𝟙 X) y (M.U p.1 ⊓ N.U p.2) (res (le p) (w.s (p.2, p.1)))⁻¹ =
        (gm (𝟙 X) y (N.U p.2 ⊓ M.U p.1) (w.s (p.2, p.1)))⁻¹ := fun p hp =>
      (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))
    refine ((gm_res _ y _ hy _).trans ((v p hy.1).trans (congrArg (·⁻¹) e'))).trans (Eq.symm ?_)
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div N M (𝟙 X) y p q hy)
      ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
    rw [mul_inv, mul_inv, inv_inv, mul_comm (gm (𝟙 X) y _ (M.g p.1 q.1))]
    rfl
  · have hx' : ⊤ ≤ x ⁻¹ᵁ (M.U i ⊓ N.U j) := by rwa [inf_comm]
    exact (valAt'_units_inv x hx' _).trans (congrArg _ (valAt'_res x (le (i, j)) _ hx'))

theorem exists_conj_unif : ∀ (x x' : KeyIn ℂ), KeyPB x' x (starRingEnd ℂ) → ∀ (hg : x'.P.g = x.P.g) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → ∃ (u' : HolUnif x'.P.A x'.P.L g) (χ' : u'.Λ → ℂ) (θ' : (Fin g → ℂ) → ℂ) (Fd' : Set (Fin g → ℂ)), u'.IsAH (Hm.map (starRingEnd ℂ)) χ' ∧ u'.IsRig x'.rig ∧ u'.IsFn x'.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume ∧ (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm (Hm.map (starRingEnd ℂ)) z z).re)) / (volume Fd').toReal = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧ ∀ (cf : Fin x.P.g → ℂ) (w : epsR ℂ ⟶ x.P.A) (w' : epsR ℂ ⟶ x'.P.A) (W : Fin g → ℂ), IsLieComb cf x.v w → IsLieComb (fun i => (starRingEnd ℂ) (cf (i.cast hg))) x'.v w' → u.IsDiff W w → u'.IsDiff (fun i => (starRingEnd ℂ) (W i)) w' := by
  rintro x x' ⟨φ, he, w, hg', F, hφ, hw, hrig, hth, hF, hε, hv⟩ hg g u Hm χ θ Fd ⟨hA, hR, hθ, hFd⟩
  rw [KeyFibre.eq_dualMapR_of_algebraMap _ F hF hε] at hv
  obtain ⟨w', hw', hinv⟩ := exists_inv w hw
  have hP := pull_isLB x.P.isLB φ
  let u₁ := conjPull hφ u
  have me : MeasurableEmbedding (star : (Fin g → ℂ) → Fin g → ℂ) :=
    (starL' ℝ (A := Fin g → ℂ)).toHomeomorph.measurableEmbedding
  have fr : ∀ (j : x.P.L.ι) (i : x'.P.L.ι) (z : Fin g → ℂ),
      ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ ((x.P.L.pull φ).U (fun _ => j) ⊓ x'.P.L.U i) →
      valAt' (u₁.ex z).left ((x.P.L.pull φ).U (fun _ => j) ⊓ x'.P.L.U i) (w.s (fun _ => j, i)).val *
        (carry u₁ hP x'.P.isLB hw').fr i z = star (u.fr j (star z)) := by
    intro j i z hz
    obtain ⟨hj, hi⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [carry_fr u₁ hP x'.P.isLB hw' i (fun _ => j) z hi hj, hinv _ _ _ hz]
    exact mul_inv_cancel_left₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j, i))) _
  refine ⟨carry u₁ hP x'.P.isLB hw', _, fun z => star (θ (star z)), star ⁻¹' Fd,
    carry_isAH hP x'.P.isLB hw' (conjPull_isAH hφ u hA), ?_, ?_, cj_domain hφ (pullId u) hFd, ?_, ?_⟩
  · intro i hi
    have h0 : (u₁.ex 0).left = eSec x'.P.A := by
      rw [(u₁.ker 0).2 u₁.Λ.zero_mem, Hom.one_def]
      simp [eSec]
    have h0' : (u.ex 0).left = eSec x.P.A := by
      rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
      simp [eSec]
    obtain ⟨j, hj⟩ := exists_chart_at hP (u₁.ex 0).left
    have hi' : ⊤ ≤ (u₁.ex 0).left ⁻¹ᵁ x'.P.L.U (i PUnit.unit) := by
      rw [h0]
      exact fun p hp => mem_pull.1 (hi hp)
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hi'⟩
    have e := fr (j PUnit.unit) (i PUnit.unit) 0 hz
    have hj' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ x.P.L.U (j PUnit.unit) := by
      have := (cj_le hφ _ j).1 hj
      rwa [star_zero] at this
    rw [h0'] at hj'
    have hj'' : ⊤ ≤ (x.P.L.pull (eSec x.P.A)).U fun _ => j PUnit.unit := fun p hp => mem_pull.2 (hj' hp)
    rw [star_zero, hR _ hj'', ← val_cj, Category.comp_id, h0] at e
    rw [h0] at hz
    exact mul_left_cancel₀ (valAt'_unit_ne_zero _ hz _)
      (e.trans (val_rig he w x'.rig x.rig hrig (j PUnit.unit) (i PUnit.unit) hz))
  · intro i z hi
    obtain ⟨j, hj⟩ := exists_chart_at hP (u₁.ex z).left
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hi⟩
    have e := fr (j PUnit.unit) i z hz
    have e₁ := val_via w x.th x'.th hth (u₁.ex z).left (j PUnit.unit) i hz
    have e₂ : valAt' ((u₁.ex z).left ≫ φ) (x.P.L.U (j PUnit.unit)) (x.th.f (j PUnit.unit)) =
        star (θ (star z)) * star (u.fr (j PUnit.unit) (star z)) :=
      (congrArg (fun x => valAt' x _ _) (cjPt_comp hφ (u.ex (star z)))).trans ((val_cj _ _ _).trans
        ((congrArg star (hθ _ (star z) ((cj_le hφ _ j).1 hj))).trans (star_mul' _ _)))
    refine mul_left_cancel₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j PUnit.unit, i))) ?_
    refine e₁.symm.trans (e₂.trans ?_)
    rw [← e]
    exact mul_left_comm _ _ _
  · rw [measurePreserving_star.measure_preimage_emb me Fd, ← measurePreserving_star.setIntegral_preimage_emb me _ Fd]
    refine congrArg (fun t : (Fin g → ℂ) → ℝ => (∫ z in star ⁻¹' Fd, t z) / (volume Fd).toReal) (funext fun z => ?_)
    rw [norm_star]
    exact congrArg (fun t : ℝ => ‖θ (star z)‖ ^ 2 * Real.exp (-Real.pi * t)) (hermSq_star Hm z)
  · intro cf v v' W h₁ h₂ hd
    have h₃ : ∀ (n : ℕ) (e : n = x.P.g), IsLieComb (fun i => cf (i.cast e)) (fun i : Fin n => x.v (i.cast e)) v := by
      rintro _ rfl
      exact h₁
    have e := (lieComb_baseChange ℂ ℂ _ _ _ φ hφ _ _ v _ x'.v v' hv (h₃ _ hg)).2 h₂
    exact cj_isDiff hφ (pullId u) (GlobalTheory.Reg.isTangent_of_isLieComb x.basis.1 h₁) e hd

end GlobalTheory.ConjUnif
