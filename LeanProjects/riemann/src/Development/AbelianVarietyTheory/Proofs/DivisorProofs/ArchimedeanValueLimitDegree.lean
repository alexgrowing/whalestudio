import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalFlagBundleExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyArithDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyValueUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSectionLiftsMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularCoverDegreeOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCh2Deg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHodgeCh2Omega
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulPowLeRpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullRegCoverIsCInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagValueSecondChernDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexDegreeEqDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLineFamilyConvergenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalBaseCharZeroSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeMetricPullbackPolarizedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeMetricFamilyLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SurfLimit

section Free

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules} {r : ℕ}

theorem isCInf_of_isRegSurf (hX : IsRegSurf p) {h : VMetric p E r} (H : h.IsCInfNorm) : h.IsCInf := by
  have key (ρ : X ⟶ X) (q : X ⟶ Sp k) (w : ρ ≫ p = q) (hq : IsRegSurf q) : (h.pull ρ w).IsCInf := by
    subst w
    exact H.pull_isCInf_of_local ρ (RegGenSmooth.genSmooth_of_isRegSurf k X _ hq).2
  rw [(VMetric.isIsometry_iff _).1 (VMetric.isIsometry_pull_id_comp k X p E r h).1]
  exact (key _ _ (Category.id_comp p) hX).map _

theorem isCh2Deg_of_isIsometry [IsIntegral X] {E' : X.Modules} {h : VMetric p E r} {h' : VMetric p E' r} {α : E ≅ E'}
    (I : h.IsIsometry h' α) {a : ℝ} (ha : h'.IsCh2Deg a) : h.IsCh2Deg a :=
  (IsometryPullback.isCh2Deg_iff_of_isIsometry (Iso.refl X) (Category.id_comp p)
    (IsometryPullback.isIsometry_trans (VMetric.isIsometry_pull_id_comp k X p E r h).1 I) a).1 ha

theorem tendsto_ch2Deg (HP : Hypotheses2) (HR : RegularAlteration) [IsIntegral X] (hX : IsRegSurf p) {t : ℝ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) {h : ℝ → VMetric p E r} {h₀ : VMetric p E r} (H : ∀ R, (h R).IsCInf) (H₀ : h₀.IsCInf)
    (hf : VFam t h h₀) {c : ℝ → ℝ} {c₀ : ℝ} (hc : ∀ R, (h R).IsCh2Deg (c R)) (hc₀ : h₀.IsCh2Deg c₀) :
    Tendsto c atTop (𝓝 c₀) := by
  have hA := hX.toIsArithVar
  have := hA.isLocallyNoetherian
  obtain ⟨⟨F⟩, hF⟩ := GlobalTheory.T.flag_variety_arith_dimension k X p 1 hA E r h₀.isVB
  have hY := (hF F).1
  have := hY.isIntegral
  obtain ⟨e, hs⟩ := FlagCmp.dim_genSmooth hX hY rfl (fun _ => h₀.isVB) F.univ
  rw [← e] at hs
  have ex (g : VMetric p E r) (G : g.IsCInf) := ((HP.p4.arExists k _ _ _ hY).2 _
    (fun z : Σ _ : Unit, Fin r => VMetric.grLB F.fl z.2 (G.pull F.π rfl))).1
  choose Φ hΦ using ex
  have val (g : VMetric p E r) (G : g.IsCInf) (a : ℝ) (ha : g.IsCh2Deg a) :=
    GlobalTheory.T.vertical_flag_bundle_exists HP HP.p4 HR k X F.Y p _ _ hA hY F.π rfl Unit (fun _ => E) (fun _ => r) (fun _ => g) (fun _ => G)
      (fun _ => F.fl) F.univ (fun _ => a) (fun _ => ha) _ (hΦ g G)
  have lim := GlobalTheory.T.arithmetic_function_limit HP.p4 k F.Y _ _ hY hs t ht _ _ _
    (fun z : Σ _ : Unit, Fin r => GlobalTheory.T.graded_line_family_convergence k F.Y _ _ r t _ _ (fun R => (H R).pull F.π rfl) (H₀.pull F.π rfl)
      (hf.pull F.π rfl) F.fl z.2) _ _ (fun R => hΦ _ (H R)) (hΦ _ H₀)
    ((∑ z : Σ _ : Unit, Fin r, MvPolynomial.X z ^ 2) * (∏ a : Unit, ∏ i : Fin r, ∏ i' ∈ Finset.Ioi i,
      (MvPolynomial.X (⟨a, i'⟩ : Σ _ : Unit, Fin r) - MvPolynomial.X ⟨a, i⟩)))
  rw [val _ H₀ _ hc₀, funext fun R => val _ (H R) _ (hc R)] at lim
  have h0 : (r.factorial : ℝ) ≠ 0 := by positivity
  have := lim.const_mul ((r.factorial : ℝ) * 2)⁻¹
  simp only [Finset.univ_unique, Finset.prod_singleton, Finset.sum_singleton, ← mul_assoc] at this
  simpa only [mul_assoc ((r.factorial : ℝ) * 2)⁻¹, inv_mul_cancel₀ (mul_ne_zero h0 two_ne_zero), one_mul] using this

theorem charZero_clo (z : X) [CharZero (X.residueField z)] :
    CharZero Γ((Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme, ⊤) := by
  have e := VdmWd.redι_clo z
  have : CharZero (X.residueField (redι (clo z) (genericPoint _))) := by rwa [e]
  have : CharZero ((Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme.residueField (genericPoint _)) :=
    (RingHom.charZero_iff ((redι (clo z)).residueFieldMap _).hom.injective).1 this
  exact (Scheme.Γevaluation _ (genericPoint _)).hom.charZero

end Free

theorem exists_hodge (HP : Hypotheses2) (HH : HypothesesH) {r : ℝ} (hr : Ch2Const r) {D : D7} {A : Amb D}
    {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) {T : Scheme.{0}} [IsIntegral T] (b : T ⟶ s.T.Z.X)
    {q : T ⟶ Sp (𝓞 κ.c.F)} (w : b ≫ s.T.Z.s = q) (hT : IsRegSurf q) (hab : ∀ y : T, b y ∈ abLocus s.T.Z.t.G) :
    ∃ (n : ℕ) (h₀ : VMetric q ((Scheme.Modules.pullback b).obj (LieVB.omega s.T.Z.t.G)) n),
      IsDualEigOn (fun σ' => x.hodge σ') b h₀ ∧
      h₀.IsCh2Deg (r / 2 * cxDeg q ((Scheme.Modules.pullback b).obj (LieVB.omega s.T.Z.t.G)) n) ∧ h₀.IsCInf := by
  have hA := hT.toIsArithVar
  have := hA.isLocallyNoetherian
  obtain ⟨Q, θ, hθ, hL⟩ := GlobalTheory.T.normal_base_char_zero_sections _ _ _ _ _ _ s.T.Z T (fun y => have := hT.regular y
    isDomain_and_isIntegrallyClosed_of_isRegularLocalRing _) hA.charZero b hab
  obtain ⟨g, G, hg⟩ : ∃ g : VMetric q (LieVB.omega Q.A) Q.g, (PPAS.ofPolAV Q).IsHodge g ∧
    g.IsCh2Deg (r / 2 * cxDeg q (LieVB.omega Q.A) Q.g) := hr _ T q hA (PPAS.ofPolAV Q)
  have : QuasiSeparated s.T.Z.t.G.hom := have := s.T.Z.t.semi.separated; inferInstance
  obtain ⟨α, hα⟩ : ∃ α : (Scheme.Modules.pullback b).obj (LieVB.omega s.T.Z.t.G) ≅ LieVB.omega Q.A,
    α.hom = LieVB.omegaBase hθ := ⟨asIso (LieVB.omegaBase hθ), rfl⟩
  have I : (VMetric.map g α.symm).IsIsometry g α :=
    IsometryPullback.isIsometry_symm (φ := α.symm) ((VMetric.isIsometry_iff _).2 rfl)
  have s₀ : g.IsCInf := isCInf_of_isRegSurf hT (PPAS.isCInfNorm_of_isHodge (PPAS.ofPolAV Q) G)
  refine ⟨Q.g, g.map α.symm, GlobalTheory.T.hodge_metric_pullback_polarized HP HH D A N j S κ s x T b q w Q θ hθ hL g G α hα _ I, ?_, s₀.map _⟩
  rw [cxDeg_congr α]
  exact isCh2Deg_of_isIsometry I hg

theorem tendsto_regSurf (HP : Hypotheses2) (HH : HypothesesH) (HR : RegularAlteration) {r : ℝ} (hr : Ch2Const r) {D : D7} {A : Amb D}
    {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) {T : Scheme.{0}} [IsIntegral T] (b : T ⟶ s.T.Z.X)
    {q : T ⟶ Sp (𝓞 κ.c.F)} (w : b ≫ s.T.Z.s = q) (hT : IsRegSurf q) (hab : ∀ y : T, b y ∈ abLocus s.T.Z.t.G)
    {h : ℝ → VMetric s.T.Z.s (LieVB.omega s.T.Z.t.G) (D.R.f * N)} (H : ∀ R, (h R).IsCInf)
    (hd : ∀ R, IsDualEig (fun σ' => x.eigMetAt σ' (some R)) (h R)) {c : ℝ → ℝ}
    (hc : ∀ R, ((h R).pull b w).IsCh2Deg (c R)) :
    Tendsto c atTop (𝓝 (r / 2 * cxDeg q ((Scheme.Modules.pullback b).obj (LieVB.omega s.T.Z.t.G)) (D.R.f * N))) := by
  obtain ⟨n, h₀, d₀, c₀, s₀⟩ := exists_hodge HP HH hr x b w hT hab
  obtain rfl : n = D.R.f * N := h₀.isVB.rank_unique ((h 0).pull b w).isVB
  have hk : 0 < x.kap := by have := x.isMuExp_muExp'.1; have := x.lt_kap; linarith
  exact tendsto_ch2Deg HP HR hT (tendsto_rpow_neg_atTop hk) (fun R => (H R).pull b w) s₀
    (GlobalTheory.T.hodge_metric_family_limit D A N j S κ s x T b q w hab _ h₀ (h 0).isVB (fun R => (H R).pull b w) s₀
      (fun R => isDualEigOn_pull (hd R) b w) d₀) hc c₀

theorem tendsto_val : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → ∀ r : ℝ, Ch2Const r → OnObj fun _ O _ _ _ _ => ∀ c (M : DRBase O c) (I : M.Emb) (z : M.B), I.Good z 0 → CharZero (M.B.residueField z) → Tendsto (fun R => M.val R z 0) atTop (𝓝 (r * (M.deg z 1 : ℝ))) := by
  intro _ HP HH HR r hr D O _ _ _ _ _ _ c M I z hz hch
  have hS : IsArithVar (redι (clo z) ≫ M.q) 1 :=
    M.ar.of_isClosedImmersion _ (charZero_clo z) ((VdmWd.dim_clo z).trans hz.1)
  have hcov := RegCoverExists.nonempty_regCover HR
  obtain ⟨C⟩ := hcov _ _ _ hS
  have hbd (y : M.B) (hy : y ∈ closure {z}) : M.b y ∈ abLocus O.s.T.Z.t.G := by
    by_contra hn
    have : Nonempty (I.f '' (closure {z} ∩ M.bd)) := ⟨⟨_, y, ⟨hy, hn⟩, rfl⟩⟩
    obtain ⟨u⟩ := this
    have : Nonempty (TopologicalSpace.IrreducibleCloseds (I.f '' (closure {z} ∩ M.bd))) :=
      ⟨⟨closure {u}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have h₁ : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (I.f '' (closure {z} ∩ M.bd)) := Order.krullDim_nonneg
    have h₂ := (add_le_add_left h₁ 3).trans hz.2.1
    exact absurd h₂ (by decide)
  choose a ha using fun R => VMetric.exists_isCh2Deg HP.p4 _ _ _ (hcov _) hS _ _
    (((M.h R).pull M.b rfl).pull (redι (clo z)) rfl) (((M.H R).pull _ _).pull _ _).isCInfNorm
  have hv (R : ℝ) : M.val R z 0 = 2 * a R := by
    have := GlobalTheory.T.flag_value_second_chern_degree HP HP.p4 HR _ _ M.q _ M.ar _ _ _ ((M.H R).pull M.b rfl) M.F (M.lam R) _ (redι (clo z)) hS _ (ha R)
    rwa [VdmWd.redι_clo] at this
  have w₁ : (redι (clo z) ≫ M.b) ≫ O.s.T.Z.s = redι (clo z) ≫ M.q := Category.assoc _ _ _
  have w₂ : (C.ρ ≫ redι (clo z) ≫ M.b) ≫ O.s.T.Z.s = C.ρ ≫ redι (clo z) ≫ M.q := by rw [Category.assoc, w₁]
  choose a' ha' using fun R => VMetric.exists_isCh2Deg HP.p4 _ _ _ (hcov _) C.reg.toIsArithVar _ _
    ((M.h R).pull _ w₂) ((M.H R).pull _ _).isCInfNorm
  have I₁ (R : ℝ) := (VMetric.isIsometry_pull_id_comp _ _ _ _ _ (M.h R)).2 _ _ _ _ M.b (redι (clo z)) rfl rfl w₁
  have I₂ (R : ℝ) := IsometryPullback.isIsometry_trans (IsometryPullback.isIsometry_pull (I₁ R) C.ρ rfl)
    ((VMetric.isIsometry_pull_id_comp _ _ _ _ _ (M.h R)).2 _ _ _ _ _ C.ρ w₁ rfl w₂)
  have e (R : ℝ) : a' R = C.deg * a R := CoverHodge.eq_deg_mul C (I₂ R) (ha R) (ha' R)
  have lim := tendsto_regSurf HP HH HR hr M.x _ w₂ C.reg (fun y => hbd _
    ((range_redι (clo z)).le ⟨C.ρ y, rfl⟩)) M.H M.dual ha'
  have hE := ((M.h 0).pull M.b rfl).isVB
  rw [← cxDeg_congr (((Scheme.Modules.pullback C.ρ).mapIso ((Scheme.Modules.pullbackComp (redι (clo z)) M.b).app _)) ≪≫
    (Scheme.Modules.pullbackComp C.ρ (redι (clo z) ≫ M.b)).app _)] at lim
  erw [CoverHodge.cxDeg_pull hS C (hE.pullback _), GlobalTheory.T.complex_degree_eq_determinant _ _ _ M.q _ hS _ _ hE] at lim
  have h0 : (C.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 C.deg_pos.ne'
  have := lim.const_mul (2 / (C.deg : ℝ))
  convert this using 2
  · rw [hv, e]; field_simp
  · push_cast
    change r * (M.deg z 1 : ℝ) = 2 / C.deg * (r / 2 * (C.deg * (M.deg z 1 : ℝ)))
    field_simp

end GlobalTheory.SurfLimit

end
