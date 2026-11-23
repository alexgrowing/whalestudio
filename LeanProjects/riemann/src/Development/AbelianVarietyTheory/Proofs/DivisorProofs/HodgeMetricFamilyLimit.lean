import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedNormInterpolationBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryDataBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulPowLeRpow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ImaginaryRootNeZero

set_option autoImplicit false

noncomputable section

open NumberField Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff

namespace GlobalTheory.MetFam.InterpFam

section Calc

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {t : ℝ → ℝ} {u : ℝ → CxPts p σ → F} {u₀ : CxPts p σ → F} {y : CxPts p σ}

theorem tendsto_of_famAt (h : FamAt t u u₀ y) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun x : ℝ × CxPts p σ => u x.1 x.2) (atTop ×ˢ 𝓝 y) (𝓝 (u₀ y)) := by
  obtain ⟨ι, _, f, Φ, O, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  have hΦ := h₄.continuousOn.continuousAt (h₂.mem_nhds h₃)
  have hf : Tendsto (fun x : ℝ × CxPts p σ => f x.2) (atTop ×ˢ 𝓝 y) (𝓝 (f y)) :=
    h₁.continuousAt.tendsto.comp tendsto_snd
  rw [h₅.self_of_nhds]
  exact (hΦ.tendsto.comp ((ht.comp tendsto_fst).prodMk_nhds hf)).congr' (h₆.mono fun _ e => e.symm)

theorem famAt_comp (h : FamAt t u u₀ y) {Ψ : F → G} (hΨ : ∀ᶠ v in 𝓝 (u₀ y), ContDiffAt ℝ ∞ Ψ v) :
    FamAt t (fun R z => Ψ (u R z)) (fun z => Ψ (u₀ z)) y :=
  have ⟨_, h₁, h₂, h₃⟩ := eventually_nhds_iff.1 hΨ
  h.comp h₂ h₃ fun v hv => (h₁ v hv).contDiffWithinAt

theorem vInfAt_comp (h : VInfAt u₀ y) {Ψ : F → G} (hΨ : ∀ᶠ v in 𝓝 (u₀ y), ContDiffAt ℝ ∞ Ψ v) :
    VInfAt (fun z => Ψ (u₀ z)) y :=
  have ⟨_, h₁, h₂, h₃⟩ := eventually_nhds_iff.1 hΨ
  h.comp h₂ h₃ fun v hv => (h₁ v hv).contDiffWithinAt

theorem cutWt_eq (κ : ℝ) {R r : ℝ} (hR : 2 ≤ R) (hr : 0 < r) (h : r ≤ R ^ 2) :
    cutWt κ R r = 1 / (1 + R ^ (-κ) * r ^ κ) := by
  rw [cutWt_of_le κ hR hr h, Real.div_rpow hr.le (by linarith), Real.rpow_neg (by linarith), div_eq_inv_mul (r ^ κ)]

theorem contDiffAt_wt (κ : ℝ) {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r) :
    ∀ᶠ v in 𝓝 (a, r), ContDiffAt ℝ ∞ (fun v : ℝ × ℝ => 1 / (1 + v.1 * v.2 ^ κ)) v := by
  have c {v : ℝ × ℝ} (hv : 0 < v.2) : ContDiffAt ℝ ∞ (fun v : ℝ × ℝ => 1 + v.1 * v.2 ^ κ) v :=
    contDiffAt_const.add (contDiffAt_fst.mul (contDiffAt_snd.rpow_const_of_ne hv.ne'))
  have h₀ : (fun v : ℝ × ℝ => 1 + v.1 * v.2 ^ κ) (a, r) ≠ 0 := by positivity
  filter_upwards [(c (v := (a, r)) hr).continuousAt.eventually_ne h₀,
    (continuous_snd.continuousAt (x := (a, r))).eventually (lt_mem_nhds hr)] with v h₁ h₂
  exact contDiffAt_const.div (c h₂) h₁

variable {κ : ℝ} {ρ : CxPts p σ → ℝ}

theorem famAt_cutWt (hρ : VInfAt ρ y) (h : 0 < ρ y) :
    FamAt (fun R => R ^ (-κ)) (fun R z => cutWt κ R (ρ z)) (fun _ => 1) y := by
  refine (famAt_comp ((famAt_param _ y).prodMk (famAt_const hρ _)) (contDiffAt_wt κ le_rfl h)).congr ?_
    (.of_forall fun z => by simp)
  filter_upwards [tendsto_fst.eventually (eventually_ge_atTop (max 2 (ρ y + 1))),
    tendsto_snd.eventually ((hρ.continuousAt.eventually (lt_mem_nhds h)).and
      (hρ.continuousAt.eventually (gt_mem_nhds (lt_add_one (ρ y)))))] with x h₁ h₂
  have h₃ := le_of_max_le_left h₁
  have h₄ := le_of_max_le_right h₁
  exact cutWt_eq κ h₃ h₂.1 (by nlinarith [h₂.2])

theorem vInfAt_cutWt (hρ : VInfAt ρ y) (h : 0 < ρ y) {R : ℝ} (hR : 2 ≤ R) (h' : ρ y < R ^ 2) :
    VInfAt (fun z => cutWt κ R (ρ z)) y := by
  refine (vInfAt_comp ((vInfAt_const (R ^ (-κ)) y).prodMk hρ)
    (contDiffAt_wt κ (Real.rpow_nonneg (by linarith) _) h)).congr ?_
  filter_upwards [hρ.continuousAt.eventually (lt_mem_nhds h), hρ.continuousAt.eventually (gt_mem_nhds h')] with z h₁ h₂
  exact cutWt_eq κ hR h₁ h₂.le

variable {g : ℕ}

def ratExpr (l l₁ : ℂ) (A B C : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (1 + l • (A * C⁻¹ - 1) + (l * (1 - l) / (l₁ * (1 - l₁))) • ((B * C⁻¹ - 1 - l₁ • (A * C⁻¹ - 1)) *
    (1 + (1 - l₁) • (A * C⁻¹ - 1)) * (1 + (1 - l) • (A * C⁻¹ - 1))⁻¹)) * C

theorem ratExpr_zero (l₁ : ℂ) (A B C : Matrix (Fin g) (Fin g) ℂ) : ratExpr 0 l₁ A B C = C := by simp [ratExpr]

abbrev Arg (g : ℕ) : Type := ℂ × ℂ × (Fin g → Fin g → ℂ) × (Fin g → Fin g → ℂ) × (Fin g → Fin g → ℂ)

theorem ratExpr_smooth {l₁ : ℂ} {A B C : Matrix (Fin g) (Fin g) ℂ} (h₁ : l₁ * (1 - l₁) ≠ 0) (hA : IsUnit A.det)
    (hC : IsUnit C.det) : ∀ᶠ v : Arg g in 𝓝 (0, l₁, A, B, C),
      IsUnit (1 + (1 - v.1) • (Matrix.of v.2.2.1 * (Matrix.of v.2.2.2.2)⁻¹ - 1)).det ∧
      MContDiffAt ∞ (fun v : Arg g => ratExpr v.1 v.2.1 (.of v.2.2.1) (.of v.2.2.2.1) (.of v.2.2.2.2)) v := by
  have a (v : Arg g) : MContDiffAt ∞ (fun v : Arg g => Matrix.of v.2.2.1) v := fun i j => by
    simp only [Matrix.of_apply]; fun_prop
  have b (v : Arg g) : MContDiffAt ∞ (fun v : Arg g => Matrix.of v.2.2.2.1) v := fun i j => by
    simp only [Matrix.of_apply]; fun_prop
  have c (v : Arg g) : MContDiffAt ∞ (fun v : Arg g => Matrix.of v.2.2.2.2) v := fun i j => by
    simp only [Matrix.of_apply]; fun_prop
  have o (v : Arg g) : MContDiffAt ∞ (fun _ : Arg g => (1 : Matrix (Fin g) (Fin g) ℂ)) v := mContDiffAt_const _
  have V {v : Arg g} (hv : IsUnit (Matrix.of v.2.2.2.2).det) :
      MContDiffAt ∞ (fun v : Arg g => Matrix.of v.2.2.1 * (Matrix.of v.2.2.2.2)⁻¹ - 1) v :=
    ((a v).mul ((c v).inv hv)).sub (o v)
  have K {v : Arg g} (hv : IsUnit (Matrix.of v.2.2.2.2).det) : MContDiffAt ∞
      (fun v : Arg g => 1 + (1 - v.1) • (Matrix.of v.2.2.1 * (Matrix.of v.2.2.2.2)⁻¹ - 1)) v :=
    (o v).add (MContDiffAt.smul (by fun_prop) (V hv))
  have d {v : Arg g} (hv : v.2.1 * (1 - v.2.1) ≠ 0) :
      ContDiffAt ℝ ∞ (fun v : Arg g => v.1 * (1 - v.1) / (v.2.1 * (1 - v.2.1))) v := by
    simp only [div_eq_mul_inv]
    exact ContDiffAt.mul (by fun_prop) (ContDiffAt.inv (f := fun v : Arg g => v.2.1 * (1 - v.2.1)) (by fun_prop) hv)
  have e₁ : ∀ᶠ v : Arg g in 𝓝 (0, l₁, A, B, C), v.2.1 * (1 - v.2.1) ≠ 0 :=
    ContinuousAt.eventually_ne (g := fun v : Arg g => v.2.1 * (1 - v.2.1)) (by fun_prop) h₁
  have hK : IsUnit (1 + (1 - (0 : ℂ)) • (A * C⁻¹ - 1)).det := by
    rw [sub_zero, one_smul, add_sub_cancel, Matrix.det_mul]
    exact hA.mul (Matrix.isUnit_nonsing_inv_det _ hC)
  filter_upwards [e₁, (c (0, l₁, A, B, C)).eventually_isUnit hC,
    (K (v := (0, l₁, A, B, C)) hC).eventually_isUnit hK] with v h₂ h₃ h₄
  refine ⟨h₄, (((o v).add (MContDiffAt.smul (by fun_prop) (V h₃))).add (MContDiffAt.smul
    (d h₂) ((((((b v).mul ((c v).inv h₃)).sub (o v)).sub
      (MContDiffAt.smul (by fun_prop) (V h₃))).mul ((o v).add (MContDiffAt.smul (by fun_prop) (V h₃)))).mul
        ((K h₃).inv h₄)))).mul (c v)⟩

def IsRat (Γ : ℝ → Matrix (Fin g) (Fin g) ℂ) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ s₀ ∈ Set.Ico (0 : ℝ) 1, ∀ s₁ ∈ Set.Ico (0 : ℝ) 1, s₁ ≠ s₀ →
    IsUnit (1 + (1 - (((1 - s) / (1 - s₀) : ℝ) : ℂ)) • (Γ s₀ * (Γ 1)⁻¹ - 1)).det →
      Γ s = ratExpr ((1 - s) / (1 - s₀) : ℝ) ((1 - s₁) / (1 - s₀) : ℝ) (Γ s₀) (Γ s₁) (Γ 1)

theorem famAt_of_isRat (hκ : 0 < κ) (hρ : VInfAt ρ y) (h : 0 < ρ y) {M : ℝ → CxPts p σ → Matrix (Fin g) (Fin g) ℂ}
    {M₀ : CxPts p σ → Matrix (Fin g) (Fin g) ℂ} (hM : ∀ R, MInfAt (M R) y) (hM₀ : MInfAt M₀ y)
    (hu : ∀ R, IsUnit (M R y).det) (hu₀ : IsUnit (M₀ y).det)
    (H : ∀ᶠ z in 𝓝 y, ∃ Γ, IsRat Γ ∧ M₀ z = Γ 1 ∧ ∀ R, 2 ≤ R → M R z = Γ (cutWt κ R (ρ z))) (a b : Fin g) :
    FamAt (fun R => R ^ (-κ)) (fun R z => M R z a b) (fun z => M₀ z a b) y := by
  obtain ⟨R₀, h₀, h₀'⟩ : ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ρ y < R₀ ^ 2 := ⟨ρ y + 2, by linarith, by nlinarith⟩
  have h₁ : 2 ≤ R₀ + 1 := by linarith
  have h₁' : ρ y < (R₀ + 1) ^ 2 := by nlinarith
  have w₀ := vInfAt_cutWt (κ := κ) hρ h h₀ h₀'
  have w₁ := vInfAt_cutWt (κ := κ) hρ h h₁ h₁'
  have lt {R : ℝ} (hR : 2 ≤ R) (h' : ρ y < R ^ 2) : cutWt κ R (ρ y) < 1 := by
    rw [cutWt_eq κ hR h h'.le, div_lt_one (by positivity), lt_add_iff_pos_right]
    positivity
  have ne : cutWt κ (R₀ + 1) (ρ y) - cutWt κ R₀ (ρ y) ≠ 0 := by
    rw [cutWt_eq κ h₁ h h₁'.le, cutWt_eq κ h₀ h h₀'.le]
    refine (sub_pos.2 (one_div_lt_one_div_of_lt (by positivity) ?_)).ne'
    have := Real.rpow_lt_rpow_of_neg (x := R₀) (y := R₀ + 1) (by linarith) (lt_add_one _) (neg_lt_zero.2 hκ)
    gcongr
  have d₀ := (sub_pos.2 (lt h₀ h₀')).ne'
  have q {s s₀ : ℝ} (hs : 1 - s₀ ≠ 0) : ∀ᶠ v in 𝓝 (s, s₀),
      ContDiffAt ℝ ∞ (fun v : ℝ × ℝ => (((1 - v.1) / (1 - v.2) : ℝ) : ℂ)) v := by
    filter_upwards [ContinuousAt.eventually_ne (g := fun v : ℝ × ℝ => 1 - v.2) (by fun_prop) hs] with v hv
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp v (ContDiffAt.div (by fun_prop) (by fun_prop) hv)
  have fl := (famAt_comp ((famAt_cutWt (κ := κ) hρ h).prodMk (famAt_const w₀ _)) (q d₀)).congr
    (u' := fun R z => (((1 - cutWt κ R (ρ z)) / (1 - cutWt κ R₀ (ρ z)) : ℝ) : ℂ))
    (u₀' := fun _ => 0) (.of_forall fun _ => rfl) (.of_forall fun z => by simp)
  have fl₁ := vInfAt_comp (w₁.prodMk w₀) (q d₀)
  have m {A : CxPts p σ → Matrix (Fin g) (Fin g) ℂ} (hA : MInfAt A y) :
      VInfAt (F := Fin g → Fin g → ℂ) A y := vInfAt_pi fun a => vInfAt_pi fun b => hA a b
  have fa := fl.prodMk (famAt_const (fl₁.prodMk ((m (hM R₀)).prodMk ((m (hM (R₀ + 1))).prodMk (m hM₀)))) _)
  have hl : (((1 - cutWt κ (R₀ + 1) (ρ y)) / (1 - cutWt κ R₀ (ρ y)) : ℝ) : ℂ) *
      (1 - (((1 - cutWt κ (R₀ + 1) (ρ y)) / (1 - cutWt κ R₀ (ρ y)) : ℝ) : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_ne_zero]
    refine mul_ne_zero (div_ne_zero (sub_pos.2 (lt h₁ h₁')).ne' d₀) ?_
    rw [one_sub_div d₀]
    exact div_ne_zero (by rwa [sub_sub_sub_cancel_left]) d₀
  have sm := ratExpr_smooth (B := M (R₀ + 1) y) hl (hu R₀) hu₀
  refine (famAt_comp fa (sm.mono fun v hv => hv.2 a b)).congr ?_ (.of_forall fun z => (congrFun (congrFun (ratExpr_zero _ _ _ _) a) b).symm)
  filter_upwards [(tendsto_of_famAt fa (tendsto_rpow_neg_atTop hκ)).eventually sm,
    tendsto_fst.eventually (eventually_ge_atTop 2), tendsto_snd.eventually (H.and
      ((hρ.continuousAt.eventually (lt_mem_nhds h)).and ((w₀.continuousAt.eventually (gt_mem_nhds (lt h₀ h₀'))).and
      ((w₁.continuousAt.eventually (gt_mem_nhds (lt h₁ h₁'))).and
      ((w₁.continuousAt.sub w₀.continuousAt).eventually_ne ne)))))] with x k₁ k₂ ⟨⟨Γ, k₃, k₄, k₅⟩, k₆, k₇, k₈, k₉⟩
  have k := k₁.1
  simp only [k₄, k₅ _ h₀, k₅ _ h₁, k₅ _ k₂] at k ⊢
  exact congrFun (congrFun (k₃ _ (cutWt_mem κ (by linarith) k₆.le) _ ⟨(cutWt_mem κ (by linarith) k₆.le).1, k₇⟩ _
    ⟨(cutWt_mem κ (by linarith) k₆.le).1, k₈⟩ (sub_ne_zero.1 k₉) k) a) b

end Calc

theorem exists_extend {F : Type} [Field F] [NumberField F] (σ : 𝓞 F →+* ℂ) :
    ∃ σ' : F →+* ℂ, σ'.comp (algebraMap (𝓞 F) F) = σ := by
  have hi : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  refine ⟨IsFractionRing.lift (A := 𝓞 F) (K := F) hi, RingHom.ext fun a => ?_⟩
  rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

theorem exists_chart {k : Type} [CommRing k] {X T : Scheme.{0}} (G : Over X) [GrpObj G] [QuasiSeparated G.hom] {r : ℕ}
    (hV : VB.IsVB (LieVB.omega G) r) (b : T ⟶ X) {q : T ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts q σ) :
    ∃ (c : VB.Chart ((Scheme.Modules.pullback b).obj (LieVB.omega G)) r) (U : X.Opens) (W : G.left.Opens)
      (hU : U ≤ LieVB.unitSec G ⁻¹ᵁ W) (f : Fin r → Γ(G.left, W)), y ∈ ptsIn q σ c.U ∧ y ∈ ptsIn q σ (b ⁻¹ᵁ U) ∧
      ∀ (m : Met q σ ((Scheme.Modules.pullback b).obj (LieVB.omega G)) r), ∀ z ∈ ptsIn q σ (b ⁻¹ᵁ U), ∀ i i',
        m.G c z i i' = m.form (QCoh.pullbackSections b _ (le_refl (b ⁻¹ᵁ U)) (LieVB.dUnit G hU (f i)))
          (QCoh.pullbackSections b _ (le_refl (b ⁻¹ᵁ U)) (LieVB.dUnit G hU (f i'))) z := by
  obtain ⟨V, e, hx₀, he⟩ := hV (b (y.1 (IsLocalRing.closedPoint ℂ)))
  let c : VB.Chart (LieVB.omega G) r := ⟨V, e, he⟩
  obtain ⟨U, W, hx, hle, ch⟩ := Conormal.exists_isChart (LieVB.sec_hom (MonObj.one (X := G))) hx₀
  choose f hf using fun i => ch.d_surjective (LieVB.sec_hom (MonObj.one (X := G)))
    (Twist.resM (LieVB.omega G) hle (c.e i))
  refine ⟨c.pull hV b, U, W, ch.le, f, mem_ptsIn.2 hx₀, mem_ptsIn.2 hx, fun m z hz i i' => ?_⟩
  have hle' : b ⁻¹ᵁ U ≤ (c.pull hV b).U := b.preimage_mono hle
  have e (i) : Twist.resM _ hle' ((c.pull hV b).e i) =
      QCoh.pullbackSections b _ (le_refl (b ⁻¹ᵁ U)) (LieVB.dUnit G ch.le (f i)) :=
    (QCoh.res_pullbackSections b _ le_rfl hle' (c.e i)).trans
      ((QCoh.pullbackSections_res b _ le_rfl hle (c.e i)).symm.trans (congrArg _ (hf i).symm))
  rw [← m.form_frame _ (ptsIn_mono hle' hz), ← m.form_resM _ _ hle' hz, e, e]

theorem vFam_interp : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (T : Scheme.{0}) (b : T ⟶ s.T.Z.X) (q : T ⟶ Sp (𝓞 κ.c.F)), b ≫ s.T.Z.s = q → (∀ w : T, b w ∈ abLocus s.T.Z.t.G) → ∀ (h : ℝ → VMetric q ((Scheme.Modules.pullback b).obj (LieVB.omega s.T.Z.t.G)) (D.R.f * N)) (h₀ : VMetric q ((Scheme.Modules.pullback b).obj (LieVB.omega s.T.Z.t.G)) (D.R.f * N)), VB.IsVB (LieVB.omega s.T.Z.t.G) (D.R.f * N) → (∀ R, (h R).IsCInf) → h₀.IsCInf → (∀ R, IsDualEigOn (fun σ' => x.eigMetAt σ' (some R)) b (h R)) → IsDualEigOn (fun σ' => x.hodge σ') b h₀ → VFam (fun R => R ^ (-x.kap)) h h₀ := by
  intro D A N j S κ s x T b q hb hab h h₀ hvb hh hh₀ hd hd₀ σ y
  have hκ : 0 < x.kap :=
    (add_pos_of_nonneg_of_pos (mul_nonneg zero_le_two x.isMuExp_muExp'.1) two_pos).trans x.lt_kap
  have : FiniteDimensional ℚ κ.c.F := κ.c.fin
  have : NumberField κ.c.F := {}
  obtain ⟨σ', rfl⟩ := exists_extend σ
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.auxiliary_data_base_change _ _ _ _ _ _ s.T.Z x T b q hb hab σ'
  have := s.T.Z.t.semi.separated
  obtain ⟨c, U, W, hU, f, hy, hyU, key⟩ := exists_chart s.T.Z.t.G hvb b y
  have hpos (z) : 0 < ρ z := by
    obtain ⟨-, yc, -, -, e⟩ := hρ z
    exact e ▸ (Real.exp_pos 1).trans_le (x.exp_le_r σ' yc)
  refine ⟨c, hy, famAt_of_isRat (ρ := ρ) (M := fun R => ((h R).met _).G c)
    (M₀ := (h₀.met _).G c) hκ (hρ y).1 (hpos y)
    (fun R => hh R _ _ y hy) (hh₀ _ _ y hy) (fun R => (((h R).met _).posDef _ y hy).det_pos.ne'.isUnit)
    ((h₀.met _).posDef _ y hy).det_pos.ne'.isUnit ?_⟩
  filter_upwards [(isOpen_ptsIn _).mem_nhds hyU, (isOpen_ptsIn _).mem_nhds hy] with z hz hz'
  obtain ⟨-, yc, e, hb, er⟩ := hρ z
  obtain ⟨u, -⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 hb
  let Γ : ℝ → Matrix (Fin (D.R.f * N)) (Fin (D.R.f * N)) ℂ := fun t => .of fun i i' => ∑ τ : D.host.E →+* ℂ,
    form (if τ (A.H.rt : D.host.E) = A.H.rt0 then GradedNorm.mix t (x.gram yc u τ) ((x.hodge σ').gram yc u τ)
      else GradedNorm.mixDual t (x.gram yc u τ) ((x.hodge σ').gram yc u τ))⁻¹
      (fun a => (valR (u.v τ a) W (f i)).snd) fun a => (valR (u.v τ a) W (f i')).snd
  have p₀ (τ) : (x.gram yc u τ).PosDef := (x.eigMet σ').pos yc u τ
  have p₁ (τ) := (x.hodge σ').pos yc u τ
  have e₁ : (h₀.met _).G c z = Γ 1 := by
    ext i i'
    rw [key _ z hz, hd₀ σ' yc z e u U W hU _ _ hz]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [(GradedNorm.mix_values (s := 0)).2.1,
      (GradedNorm.mixDual_values (s := 0) (p₀ τ).det_pos.ne'.isUnit (p₁ τ).det_pos.ne'.isUnit).2.1, ite_self]
  refine ⟨Γ, fun t ht t₀ ht₀ t₁ ht₁ hne hu => ?_, e₁, fun R hR => ?_⟩
  · refine GlobalTheory.T.graded_norm_interpolation_bound _ S.Dw.mult _ ((Pad.length_letters S).symm.trans (Pad.LineTest.length_letters _))
      (fun τ => τ (A.H.rt : D.host.E) = A.H.rt0) _ _ p₀ p₁ (fun i τ a => (valR (u.v τ a) W (f i)).snd) Γ
      (fun t i i' => ?_) (e₁ ▸ ((h₀.met _).posDef _ z hz').det_pos.ne'.isUnit) t ht t₀ ht₀ t₁ ht₁ hne _ _ _ rfl rfl rfl hu
    exact Finset.sum_congr rfl fun τ _ => by congr
  · ext i i'
    rw [key _ z hz, hd R σ' yc z e u U W hU _ _ hz, er, ← x.wt_eq hR hb]
    rfl

end GlobalTheory.MetFam.InterpFam

end
