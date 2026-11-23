import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.NotIsProjOverAffineLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniversalFibreUniformisedTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliNonemptyPositiveDimStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.BdryModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

def iota (R : Type) [CommRing R] : epsR R ≅ epsAt (𝟙 (Sp R)) := Over.isoMk (Iso.refl _) (by simp)

theorem iota_left {R : Type} [CommRing R] {G : Over (Sp R)} (w : epsAt (𝟙 (Sp R)) ⟶ G) :
    ((iota R).hom ≫ w).left = w.left := Category.id_comp _

theorem tan_iff {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (w : epsAt (𝟙 (Sp R)) ⟶ G) :
    IsTangent ((iota R).hom ≫ w) ↔ IsTanAt G (𝟙 _) w := by
  unfold IsTangent IsTanAt
  rw [iota_left]
  have : (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left = η[G].left := by
    rw [Hom.one_def]; simp
  rw [this]

theorem basis_of_isLieBasis {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ}
    (v : Fin n → (epsR R ⟶ G)) (hv : IsLieBasis v) {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (𝟙 _) E) : Nonempty ((Fin n → R) ≃ₗ[R] E) := by
  have h1 : ∀ i, ∃ e, (iota R).hom ≫ M.pt e = v i := fun i => by
    obtain ⟨e, he⟩ := M.onto ((iota R).inv ≫ v i) ((tan_iff _).1 (by simpa using hv.1 i))
    exact ⟨e, by simp [he]⟩
  choose e he using h1
  let F : Multiplicative E →* (epsR R ⟶ G) := MonoidHom.mk' (fun x => (iota R).hom ≫ M.pt x.toAdd)
    (fun a b => by simp [M.add, MonObj.comp_mul])
  have hF : Function.Injective F := fun a b h => M.inj ((cancel_epi (iota R).hom).1 h)
  have hs : ∀ c : Fin n → R, (iota R).hom ≫ M.pt (∑ i, c i • e i) =
      (List.ofFn fun i => (iota R).hom ≫ M.pt (c i • e i)).prod := fun c => by
    change F (Multiplicative.ofAdd (∑ i, c i • e i)) = _
    rw [ofAdd_sum, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  have hl : ∀ (c : R) i, ((iota R).hom ≫ M.pt (c • e i)).left = spMap (epsScaleR c) ≫ (v i).left := fun c i => by
    rw [iota_left, M.smul, ← he, iota_left]; rfl
  have key : ∀ (c : Fin n → R) (x : E), IsLieComb c v ((iota R).hom ≫ M.pt x) ↔ x = ∑ i, c i • e i := by
    intro c x
    constructor
    · rintro ⟨u, hu, hx⟩
      have : u = fun i => (iota R).hom ≫ M.pt (c i • e i) := by
        funext i; ext1; rw [hu, hl]
      rw [this, ← hs] at hx
      exact M.inj ((cancel_epi (iota R).hom).1 hx)
    · rintro rfl
      exact ⟨_, fun i => hl _ i, hs c⟩
  refine ⟨LinearEquiv.ofBijective (Fintype.linearCombination R e) ⟨fun c c' h => ?_, fun x => ?_⟩⟩
  · simp only [Fintype.linearCombination_apply] at h
    exact (hv.2 _ ((tan_iff _).2 (M.tan (∑ i, c i • e i)))).unique ((key _ _).2 rfl) ((key _ _).2 h)
  · obtain ⟨c, hc, -⟩ := hv.2 _ ((tan_iff _).2 (M.tan x))
    exact ⟨c, by rw [Fintype.linearCombination_apply]; exact ((key _ _).1 hc).symm⟩

theorem lieModel_of_isLieBasis {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (v : Fin n → (epsR R ⟶ G)) (hv : IsLieBasis v) : Nonempty (LieModel G (𝟙 _) (Fin n → R)) := by
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists _ G R (𝟙 _)
  obtain ⟨φ⟩ := basis_of_isLieBasis v hv M
  exact ⟨{ pt := fun c => M.pt (φ c), tan := fun c => M.tan _, inj := M.inj.comp φ.injective
           onto := fun w hw => by
             obtain ⟨x, hx⟩ := M.onto w hw
             exact ⟨φ.symm x, by simpa using hx⟩
           add := fun a b => by rw [map_add, M.add]
           smul := fun c a => by rw [map_smul, M.smul] }⟩

theorem card_eq_of_isLieBasis {G : Over (Sp ℂ)} [GrpObj G] [IsCommMonObj G] {n m : ℕ}
    (v : Fin n → (epsR ℂ ⟶ G)) (hv : IsLieBasis v) (w : Fin m → (epsR ℂ ⟶ G)) (hw : IsLieBasis w) : n = m := by
  obtain ⟨M⟩ := lieModel_of_isLieBasis w hw
  obtain ⟨φ⟩ := basis_of_isLieBasis v hv M
  simpa using φ.finrank_eq

theorem half_mem_punct (n a : ℕ) : (fun _ => (1 / 2 : ℂ)) ∈ punct n a 1 := by
  refine ⟨?_, fun _ _ => by norm_num⟩
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro i; norm_num

theorem zero_notMem_punct {n a : ℕ} (ha : 0 < a) (han : a ≤ n) (ρ : ℝ) : (0 : Fin n → ℂ) ∉ punct n a ρ :=
  fun h => h.2 ⟨0, by omega⟩ ha rfl

theorem one_le_logSize {n : ℕ} (a : ℕ) (z : Fin n → ℂ) : 1 ≤ logSize a z :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem logSize_one (u : ℂ) : logSize 1 (fun _ : Fin 1 => u) = 1 + |Real.log ‖u‖| := by
  simp [logSize]

def evalHom {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* ℂ :=
  (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom

theorem spMap_evalHom {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    spMap (evalHom x U h) ≫ hU.fromSpec = x := by
  change Spec.map (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) ≫ hU.fromSpec = x
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) h,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_chart (Xo : Moduli D l) (σ : KA l →+* ℂ) {n a : ℕ} (han : a ≤ n) (Z FinalForm : Scheme.{0}) (T : SAB H Z)
    (g : ℕ) (hg : SmoothOfRelativeDimension g T.G.hom) (j₀ : FinalForm ⟶ Z) [IsOpenImmersion j₀] (k₀ : FinalForm ⟶ Xo.X)
    (To : SAB H FinalForm) (n₁ : SABMap To T j₀) (n₂ : SABMap To Xo.univ.t k₀) (y : (Fin n → ℂ) → (Sp ℂ ⟶ Z))
    (hy : IsHolTo (Metric.ball 0 1) y)
    (hp : ∀ z ∈ punct n a 1, ∃ p : Sp ℂ ⟶ FinalForm, p ≫ j₀ = y z ∧ p ≫ k₀ ≫ Xo.s = spMap σ) :
    ∃ (ρ : ℝ) (C : BdryChart Xo σ n a) (f : Sp C.R ⟶ Z), 0 < ρ ∧ C.g = g ∧ IsOpenImmersion f ∧
      Nonempty (SABMap C.t T f) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ f = y ((ρ : ℂ) • z) := by
  classical
  obtain ⟨-, -, hcomp, hcanc, -⟩ := GlobalTheory.PullCalcTest.all_six
  have := T.semi.smooth
  have hbc := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  obtain ⟨U, hU, hx, -, n', v₀, hv₀⟩ := GlobalTheory.exists_affine_lieBasis_baseChange Z T.G
    (y 0 (default : PrimeSpectrum ℂ)) ⊤ trivial
  have h0 : ⊤ ≤ y 0 ⁻¹ᵁ U := fun p _ => by
    have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [this]; exact hx
  obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.1 (hy U 0).1 0 ⟨Metric.mem_ball_self one_pos, h0⟩
  have hin : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (ρ : ℂ) • z ∈ Metric.ball (0 : Fin n → ℂ) ρ := fun z hz => by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    exact mul_lt_of_lt_one_right hρ hz
  obtain ⟨t, ⟨m⟩⟩ := exists_sab hU.fromSpec T
  have hn : n' = g := by
    obtain ⟨t₀, ⟨m₀⟩⟩ := exists_sab (spMap (evalHom (y 0) U h0) ≫ hU.fromSpec) T
    obtain ⟨v', -, hv'⟩ := hv₀ ℂ _ t₀.G _ m₀.cart
    obtain ⟨w, hw⟩ := GlobalTheory.KeyPow.exists_isLieBasis t₀.G
      (MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) m₀.cart.1 hg)
    exact card_eq_of_isLieBasis v' hv' w hw
  subst hn
  obtain ⟨v', -, hv'⟩ := hv₀ Γ(Z, U) (RingHom.id _) t.G m.cm.F (by
    have : spMap (RingHom.id Γ(Z, U)) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]; exact m.cart)
  obtain ⟨M⟩ := lieModel_of_isLieBasis v' hv'
  let ψ : (Fin n → ℂ) → (Γ(Z, U) →+* ℂ) := fun z =>
    if h : ⊤ ≤ y ((ρ : ℂ) • z) ⁻¹ᵁ U then evalHom _ U h else evalHom _ U h0
  have hψ : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (ψ z) ≫ hU.fromSpec = y ((ρ : ℂ) • z) := fun z hz => by
    simp only [ψ, dif_pos (hB (hin z hz)).2]
    exact spMap_evalHom _ _ _ _
  obtain ⟨tV, ⟨q⟩⟩ := exists_sab (pullback.snd hU.fromSpec j₀) To
  obtain ⟨m₂, -⟩ := hcomp E H _ _ _ _ _ _ _ _ n₂ q
  obtain ⟨q₁, -⟩ := hcomp E H _ _ _ _ _ _ _ _ n₁ q
  rw [← pullback.condition] at q₁
  obtain ⟨m₁, -⟩ := hcanc E H _ _ _ _ _ _ _ _ m q₁
  have hpt : ∀ z ∈ punct n a 1, ∃ p : Sp ℂ ⟶ pullback hU.fromSpec j₀,
      p ≫ pullback.fst _ _ = spMap (ψ z) ∧ p ≫ (pullback.snd _ _ ≫ k₀) ≫ Xo.s = spMap σ := fun z hz => by
    obtain ⟨p, hp₁, hp₂⟩ := hp ((ρ : ℂ) • z) ⟨(hB (hin z hz.1)).1, fun i hi => by
      simpa using ⟨hρ.ne', hz.2 i hi⟩⟩
    refine ⟨pullback.lift (spMap (ψ z)) p ((hψ z hz.1).trans hp₁.symm), pullback.lift_fst _ _ _, ?_⟩
    rw [Category.assoc, pullback.lift_snd_assoc, hp₂]
  obtain ⟨p₀, -⟩ := hpt _ (half_mem_punct n a)
  have : Nonempty (Sp ℂ ⟶ pullback hU.fromSpec j₀) := ⟨p₀⟩
  choose! pt hpt using hpt
  refine ⟨ρ, { a_le := han, R := Γ(Z, U), t := t, g := n'
               dim := MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n') m.cart.1 hg
               M := M, ψ := ψ, hol := ⟨Metric.isOpen_ball, fun r => ?_⟩
               V := pullback hU.fromSpec j₀, j := pullback.fst _ _, j_open := inferInstance
               k := pullback.snd _ _ ≫ k₀, tV := tV, m₁ := m₁, m₂ := m₂, pt := pt, pt_eq := hpt },
    hU.fromSpec, hρ, rfl, inferInstance, ⟨m⟩, hψ⟩
  refine (((hy U r).2.comp (f := fun z => (ρ : ℂ) • z) (by fun_prop) (fun z hz => hB (hin z hz)))).congr
    fun z hz => ?_
  simp only [ψ, Function.comp, valAt', dif_pos (hB (hin z hz)).2]
  rfl

theorem exists_chart_at_point (Xo : Moduli D l) (σ : KA l →+* ℂ) {n a : ℕ} (han : a ≤ n) (x : Sp ℂ ⟶ Xo.X)
    (hx : x ≫ Xo.s = spMap σ) :
    ∃ C : BdryChart Xo σ n a, C.g = Module.finrank ℚ E / 2 * (D.p + D.q) := by
  obtain ⟨To, ⟨m⟩⟩ := exists_sab (𝟙 Xo.X) Xo.univ.t
  obtain ⟨_, C, _, -, h, -⟩ := exists_chart Xo σ han Xo.X Xo.X Xo.univ.t _
    (GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ) (𝟙 _) (𝟙 _) To m m (fun _ => x)
    (fun U f => ⟨by
      by_cases h : ⊤ ≤ x ⁻¹ᵁ U
      · simp only [h, and_true]; exact Metric.isOpen_ball
      · simp [h], differentiableOn_const _⟩)
    (fun z _ => ⟨x, Category.comp_id _, by simpa using hx⟩)
  exact ⟨C, h⟩

theorem exists_chart_pos (D : Datum H) (hD : 1 ≤ D.p + D.q) (l : Level H) {n a : ℕ} (han : a ≤ n) :
    ∃ (Xo : Moduli D l) (C : BdryChart Xo (KA l).val.toRingHom n a),
      C.g = Module.finrank ℚ E / 2 * (D.p + D.q) := by
  obtain ⟨Xo, y, hy, -⟩ := GlobalTheory.T.exists_moduli_nonempty_positive_dim.1 E H D hD l
  obtain ⟨C, hC⟩ := exists_chart_at_point Xo _ han y hy
  exact ⟨Xo, C, hC⟩

variable {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ n a)

theorem exists_isVal (z : Fin n → ℂ) {m : ℕ} (u : Fin m → Fin C.g → C.R) : ∃ v, C.IsVal z u v := by
  refine ⟨fun i => Over.homMk (spMap (dualMap (C.ψ z)) ≫ (C.M.pt (u i)).left) ?_, fun _ => rfl⟩
  rw [Category.assoc, Over.w]
  change Spec.map _ ≫ Spec.map _ ≫ 𝟙 _ = Spec.map _ ≫ Spec.map _
  rw [Category.comp_id, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r : 2
  change dualMap (C.ψ z) (algebraMap _ _ r) = algebraMap ℂ (DualNumber ℂ) (C.ψ z r)
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem hermForm_single {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g) :
    hermForm Hm (Pi.single i 1) (Pi.single j 1) = Hm i j := by
  have : star (Pi.single j (1 : ℂ) : Fin g → ℂ) = Pi.single j 1 := by
    funext k; by_cases h : k = j <;> simp [h]
  simp [hermForm, this]

theorem isRiem_frame {z : Fin n → ℂ} {Hm : Matrix (Fin C.g) (Fin C.g) ℂ} (h : C.IsRiem z Hm)
    (v : Fin C.g → (epsAt (spMap (C.ψ z)) ⟶ C.t.G)) (hv : C.IsVal z (fun i => Pi.single i 1) v)
    (Γ : Matrix (Fin C.g) (Fin C.g) ℂ) :
    IsHodgeGram C.t.G C.t.PP.L (spMap (C.ψ z)) v Γ ↔ ∀ i j, Γ i j = Real.pi * Hm i j := by
  have e : ∀ i : Fin C.g, (fun b => C.ψ z ((Pi.single i 1 : Fin C.g → C.R) b)) = Pi.single i 1 := fun i => by
    funext k; by_cases h : k = i <;> simp [h]
  rw [h _ _ v Γ hv]
  simp only [e, hermForm_single]

theorem isRiemannMatrix_unique {z : Fin n → ℂ} {H₁ H₂ : Matrix (Fin C.g) (Fin C.g) ℂ} (h₁ : C.IsRiem z H₁)
    (h₂ : C.IsRiem z H₂) : H₁ = H₂ := by
  obtain ⟨v, hv⟩ := exists_isVal C z (fun i => Pi.single i 1)
  have := (isRiem_frame C h₂ v hv (Matrix.of fun i j => Real.pi * H₁ i j)).1
    ((isRiem_frame C h₁ v hv _).2 fun _ _ => rfl)
  ext i j
  exact mul_left_cancel₀ (by exact_mod_cast Real.pi_ne_zero) (this i j)

theorem isRiem_herm {z : Fin n → ℂ} {Hm : Matrix (Fin C.g) (Fin C.g) ℂ} (h : C.IsRiem z Hm) : Hm.IsHermitian := by
  obtain ⟨v, hv⟩ := exists_isVal C z (fun i => Pi.single i 1)
  obtain ⟨Q, φ, v', u, H', χ, W, -, -, hA, -, hΓ⟩ :=
    (isRiem_frame C h v hv (Matrix.of fun i j => Real.pi * Hm i j)).2 fun _ _ => rfl
  have e : ∀ i j, Hm i j = hermForm H' (W i) (W j) := fun i j =>
    mul_left_cancel₀ (by exact_mod_cast Real.pi_ne_zero) (hΓ i j)
  ext i j
  rw [Matrix.conjTranspose_apply, e, e]
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hA.1.apply]; ring

theorem isProper_of_isRiem {z : Fin n → ℂ} {Hm : Matrix (Fin C.g) (Fin C.g) ℂ} (h : C.IsRiem z Hm) :
    IsProper (pullback.snd C.t.G.hom (spMap (C.ψ z))) := by
  obtain ⟨Q, φ, -, -, -, -, -, hφ, -⟩ := (h 0 Fin.elim0 (fun i => i.elim0) 0 (fun i => i.elim0)).2 (fun i => i.elim0)
  have := Q.isAb.proper
  rw [← hφ.1.isoPullback_inv_snd]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.Flat.BdryModel
