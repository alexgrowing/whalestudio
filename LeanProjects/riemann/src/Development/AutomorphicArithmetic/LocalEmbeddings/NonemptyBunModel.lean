import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleExistsArithmeticVarietyAltAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimEqDimGrAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricSmoothOfHodge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeComparisonRootMetrics
import Development.AutomorphicArithmetic.DivisorFrames.ExistsTrueModelOver
import Development.AutomorphicArithmetic.DivisorFrames.ExistsVectorBundleGluing
import Development.AutomorphicArithmetic.DivisorFrames.FrameGenericChart
import Development.AutomorphicArithmetic.DivisorFrames.FrameGenericChartNorm
import Development.AutomorphicArithmetic.DivisorFrames.FrameGenericValuation
import Development.AutomorphicArithmetic.DivisorFrames.FrameGenericIntegral
import Development.AutomorphicArithmetic.DivisorFrames.ExistsGradedSectionFlag
import Development.AutomorphicArithmetic.DivisorFrames.TrueModelChartDivisor
import Development.AutomorphicArithmetic.DivisorFrames.TrueModelChartDivisorMetric
import Development.AutomorphicArithmetic.DivisorFrames.TrueModelChartDivisorAlt
import Development.AutomorphicArithmetic.DivisorFrames.FlagCompactVectorBundle
import Development.AutomorphicArithmetic.DivisorFrames.FlagConnectionAdapted
import Development.AutomorphicArithmetic.DivisorFrames.IsPullbackOfUniquePoints
import Development.AutomorphicArithmetic.DivisorFrames.FlagCompactTriangularOver
import Development.AutomorphicArithmetic.DivisorFrames.FlagPolynomialDimension
import Development.AutomorphicArithmetic.DivisorFrames.GenericFrameTrueModel
import Development.AutomorphicArithmetic.DivisorFrames.SmoothFrameGeneric
import Development.AutomorphicArithmetic.DivisorFrames.EmbeddingBijectiveMultiplicity
import Development.AutomorphicArithmetic.DivisorFrames.EigenvarietyOverFrame
import Development.AutomorphicArithmetic.DivisorFrames.EigenvarietyOverFrameAlt

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BcLie

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F}

omit [NumberField F] in

theorem nonempty_genFrame {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {Y : Var F}
    {ρ : Y.X ⟶ gen Z} (hρ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) : Nonempty (GenFrame e ρ) := by
  have h1 : genericPt Y ≫ Y.str = spMap (algebraMap F Y.Fn) := (GlobalTheory.FlagBundle.ratOf Y).pt_s
  have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    exact CommRingCat.hom_ext (RingHom.ext fun a => e.apply_symm_apply a)
  have h4 : spMap (constF e Y) = spMap (algebraMap F Y.Fn) ≫ spMap e.symm.toRingHom := by rw [← Spec.map_comp]; rfl
  obtain ⟨f⟩ := EigLoc.exists_eigFrame E H Dw l Xo c O β Z _ (constF e Y) (genericPt Y ≫ ρ) (by
    rw [h4, ← h1, ← hρ]; simp only [Category.assoc, h2, Category.comp_id])
  exact ⟨by rw [GenFrame, ← Category.assoc]; exact f⟩

theorem exists_base {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)} {Y : Var F} {ρ : Y.X ⟶ gen Z}
    (hρ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) (g : GenFrame e ρ) :
    ∃ N : GlobalTheory.TrueGeo.Model Y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X ∧ ∀ (τ : E →+* ℂ) (dual : Bool),
      ∃ (M : N.X.Modules) (_ : IsVB M (Dw.mult τ)) (A : Chart M (Dw.mult τ) → Matrix _ _ Y.Fn),
        IsLie g τ N.j dual A ∧ IsLat g τ N.j dual A := by
  obtain ⟨N, ρ', hN, hρ', hS⟩ := UpperTheory.exists_true_model_over E H Dw l Xo c Z F e Y ρ hρ g
  refine ⟨N, hN, fun τ dual => ?_⟩
  have := N.ar.isIntegral
  choose V P hz hVP using hS τ
  have hj : N.j (genericPoint Y.X) = genericPoint N.X := GlobalTheory.ModelBirational.j_genericPoint N
  have hV : ∀ z, ⊤ ≤ (genericPt Y ≫ N.j) ⁻¹ᵁ V z := fun z => (hVP z).choose_spec.choose
  have hP : ∀ z, IsUnit (P z).det := fun z => by
    obtain ⟨_, _, _, _, _, _, -, -, h, -⟩ := hVP z
    exact h
  obtain ⟨M, hM, A, hA, hch⟩ := UpperTheory.exists_vector_bundle_gluing N.X Y.Fn (genericPt Y ≫ N.j)
    (fun p => by
      rw [Scheme.Hom.comp_apply, ← hj]
      exact congrArg N.j ((GlobalTheory.FlagBundle.ratOf Y).pt_apply p))
    _ N.X V hV (fun z => lieMat dual (P z)) (fun z => ⟨z, hz z⟩) (fun z => isUnit_det_lieMat dual (hP z)) fun z z' => by
      obtain ⟨T, hT, h⟩ := UpperTheory.frame_generic_chart E H Dw l Xo c _ _ Z F e Y ρ hρ g τ N.X N.j ρ' hj hρ' _ _ _ _ (hVP z) (hVP z')
        (le_inf_pre (hV z) (hV z'))
      exact ⟨lieMat dual T, by rw [h, lieMat_mul, lieMat_map _ _ hT]⟩
  choose ch hU hch using hch
  have hL : IsLie g τ N.j dual A := isLie_of_exists hA fun y => ⟨ch (N.j y), hU _ ▸ hz _, by
    rw [hch, lieMat_lieMat _ (hP _)]
    exact UpperTheory.frame_generic_chart_norm E H Dw l Xo c _ _ Z F e Y ρ hρ g τ N.X N.j ρ' hρ' _ _ (hVP _) y (hz _)⟩
  refine ⟨M, hM, A, hL, UpperTheory.frame_generic_valuation E H Dw l Xo c _ _ Z F e Y ρ hρ g τ N.X N.j M hM dual A hL fun z =>
    ⟨ch z, hU _ ▸ hz _, ?_⟩⟩
  rw [hch, lieMat_lieMat _ (hP _), hU]
  exact UpperTheory.frame_generic_integral E H Dw l Xo c _ _ Z F e Y ρ hρ g τ N.X N.j ρ' hρ' _ _ (hVP _)

variable {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

theorem induced_grLB (C : FlagCpt Z e) (N : GlobalTheory.TrueGeo.Model C.Y) (τ : E →+* ℂ) (M : N.X.Modules) (dual : Bool)
    (A : Chart M (Dw.mult τ) → Matrix _ _ C.Y.Fn) (fl : Vert.Flag M (Dw.mult τ)) (i : Fin (Dw.mult τ)) (kind : ℕ → Bool)
    (hk : ∀ p, kind p = false) (Ro : Option ℝ) (G : ∀ σ : c.F →+* ℂ, EigMet Z σ) (h : VMetric N.p M (Dw.mult τ))
    (hh : h.IsCInf) (hm : Mets C (cxSt F)) (hG : ∀ σ n, hm Ro σ n = C.met (G (embOf e σ)) n)
    (h₁ : IsLie C.f0 τ N.j dual A) (h₂ : IsLat C.f0 τ N.j dual A) (h₃ : IsMet C.f0 τ N.j dual A G h)
    (h₄ : IsFlag (genericPt C.Y ≫ N.j) dual A fl) :
    (adlOf C hm (Finsupp.single (kind, Ro, Sum.inl (τ, (pos dual i : ℕ))) (cond dual (-1) 1))).Induced N
      (VMetric.grLB fl i hh) 1 0 := by
  obtain ⟨s, hs⟩ := UpperTheory.exists_graded_section_flag F C.Y N.X N.j M _ dual A fl i h₁.1 h₄
  generalize hw : Finsupp.single (kind, Ro, Sum.inl (τ, (pos dual i : ℕ))) (cond dual (-1) 1 : ℤ) = w
  have e₁ := UpperTheory.true_model_chart_divisor E H Dw l Xo c O β Z F e C N τ M dual A fl i s kind Ro w hw.symm h₁ h₄ hs
  have e₂ := UpperTheory.true_model_chart_divisor_metric E H Dw l Xo c O β Z F e C N τ M dual A fl i s kind Ro w hw.symm h₁ h₄ hs G h hh h₃
  have e₃ := UpperTheory.true_model_chart_divisor_alt E H Dw l Xo c O β Z F e C N τ M dual A fl i s kind Ro w hw.symm h₁ h₄ hs h₂ hk
  have hp : parOf w = Ro := by
    have hn : (cond dual (-1) 1 : ℤ) ≠ 0 := by cases dual <;> simp
    have h : w.support.Nonempty := hw ▸ Finsupp.support_nonempty_iff.2 (Finsupp.single_ne_zero.2 hn)
    have h' := h.choose_spec
    rw [parOf, dif_pos h]
    generalize h.choose = a at h'
    rw [← hw] at h'
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h')]
  refine ⟨by simp, s, ⟨LB.isLB_pull (fl.isLB_root i) N.j, hs.1, fun k y hy => ?_⟩, fun σ y y' k f a₁ a₂ a₃ => ?_,
    fun v ε y yt k a₁ a₂ => ?_⟩
  · exact (one_nsmul (divOf C (expo Dw w))).symm ▸ e₁ k y hy
  · have hy : y ∈ Var.eqnSet σ (divOf C (expo Dw w)) (s k) := e₁ k _ a₂
    have hy' : y ∈ Var.eqnSet σ ((1 : ℕ) • divOf C (expo Dw w)) (s k ^ 1) := (e₁ k _ a₂).nsmul 1
    change Real.exp (-(2 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * 0)) * Var.pn C.Y σ _
      (Var.mPow C.Y σ (divOf C (expo Dw w)) 1 (hm (parOf w) σ _)) (C.Y.cx σ f) y = _
    rw [hp, hG, Var.pn_eq hy', Var.mPow_h hy, Var.fval_cx, e₂ σ y y' k a₁ a₂]
    simp
  · simpa [adlOf] using e₃ v ε y yt k a₁ a₂

theorem exists_flag_model (C : FlagCpt Z e) (B : Var F) (ρB : B.X ⟶ gen Z) (f : C.Y.X ⟶ B.X) (φ : B.Fn →+* C.Y.Fn)
    (hf : IsOver e ρB C.π f φ) (hρ : ρB ≫ genStr Z ≫ spMap e.toRingHom = B.str) (g : GenFrame e ρB)
    (g' : GenFrame e C.π) (hg : g.IsMap φ g') {ι : Type} (emb : ι → (E →+* ℂ)) (hemb : Function.Bijective emb)
    (dual : ι → Bool) (N : GlobalTheory.TrueGeo.Model B) (M : ι → N.X.Modules) (hM : ∀ a, IsVB (M a) (Dw.mult (emb a)))
    (A : ∀ a, Chart (M a) (Dw.mult (emb a)) → Matrix _ _ B.Fn) (hA : ∀ a, IsLie g (emb a) N.j (dual a) (A a))
    (X : Scheme.{0}) (π : X ⟶ N.X) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (M a)) (Dw.mult (emb a)))
    (hfl : IsFlagBundle π M (fun a => Dw.mult (emb a)) fl) (d : ℕ) (ar : IsArithVar (π ≫ N.p) d)
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X)
    (hl : ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ B.X), x ≫ ρB ≫ genStr Z = spMap χ →
      ∀ k : EigFrame Z χ (x ≫ ρB ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p k) :
    ∃ (j : C.Y.X ⟶ X) (_ : j ≫ π = f ≫ N.j) (A' : ∀ a, Chart ((Scheme.Modules.pullback π).obj (M a)) (Dw.mult (emb a)) →
        Matrix _ _ C.Y.Fn), IsPullback j C.Y.str (π ≫ N.p) (spMap (algebraMap (𝓞 F) F)) ∧
      ∀ a, IsLie C.f0 (emb a) j (dual a) (A' a) ∧ IsPullCo N.j π (hM a) (dual a) φ g' C.f0 (A a) (A' a) ∧
        IsFlag (genericPt C.Y ≫ j) (dual a) (A' a) (fl a) := by
  choose A₁ hA₁ hP₁ using fun a => (hA a).exists_pull hf hg C.f0 (f ≫ N.j) (𝟙 _) (Category.id_comp _) (hM a)
  choose fl₁ hfl₁ using fun a => UpperTheory.flag_compact_vector_bundle E H Dw l Xo c O β Z F e C (emb a) _ ((hM a).pullback (f ≫ N.j)) (dual a) (A₁ a) (hA₁ a)
  obtain ⟨j, ⟨hj, hc⟩, -⟩ := hfl C.Y.X (f ≫ N.j) fl₁
  choose A' hA' hP' using fun a => (hA a).exists_pull hf hg C.f0 π j hj (hM a)
  have hF : ∀ a, IsFlag (genericPt C.Y ≫ j) (dual a) (A' a) (fl a) := fun a ch had hch => by
    obtain ⟨ch', hU, had', htr⟩ := UpperTheory.flag_connection_adapted N.X X C.Y.X π ι M _ hM fl j _ hj fl₁ hc a ch had
    obtain ⟨U, s, hb, hs⟩ := hM a (N.j (genericPoint B.X))
    let b : Chart (M a) (Dw.mult (emb a)) := ⟨U, s, hs⟩
    have hb₀ : ⊤ ≤ (genericPt B ≫ N.j) ⁻¹ᵁ b.U := gen_le N.j hb
    have hb₁ : ⊤ ≤ (genericPt C.Y ≫ f ≫ N.j) ⁻¹ᵁ b.U := by
      rw [← Category.assoc, hf.2.2.1, Category.assoc]
      exact fun p _ => hb₀ (x := spMap φ p) trivial
    have hb₂ : ⊤ ≤ (genericPt C.Y ≫ j) ⁻¹ᵁ (b.pull (hM a) π).U := by
      change ⊤ ≤ ((genericPt C.Y ≫ j) ≫ π) ⁻¹ᵁ b.U
      rwa [Category.assoc, hj]
    have hb₃ : ⊤ ≤ (genericPt C.Y ≫ 𝟙 _) ⁻¹ᵁ (b.pull (hM a) (f ≫ N.j)).U := by
      rw [Category.comp_id]; exact hb₁
    have hch' : ⊤ ≤ (genericPt C.Y ≫ 𝟙 _) ⁻¹ᵁ ch'.U := by
      rw [Category.comp_id, hU]; exact hch
    have key : A' a ch = A₁ a ch' := by
      rw [(hA' a).1.2 _ ch hb₂ hch, (hA₁ a).1.2 _ ch' hb₃ hch', hP' a b hb₀, hP₁ a b hb₀, Category.comp_id,
        htr _ _ b hb₁ hch]
    rw [key]
    exact hfl₁ a ch' had' hch'
  refine ⟨j, hj, A', UpperTheory.isPullback_of_unique_points F C.Y X _ d ar hX j ?_ (UpperTheory.flag_compact_triangular_over E H Dw l Xo c O β Z F e C B ρB f φ hf hρ g g' hg ι emb hemb dual
    N X j π hj M hM A A' fl hA hA' hP' hF hfl hl), fun a => ⟨hA' a, hP' a, hF a⟩⟩
  rw [← Category.assoc, hj, Category.assoc, N.pb.w, ← Category.assoc, hf.2.1]

end Free

theorem exists_bun {D : D7} (O : Setup D) (hC : O.Core) {R : ℝ} (hR : 2 ≤ R) (c : O.s.Comp)
    (n : D.what₂.Tau × Bool → ℕ)
    (hn : ∀ a : D.what₂.Tau × Bool, O.S.Dw.mult (cond a.2 (DV.tauEmb D a.1) (conjEmb (DV.tauEmb D a.1))) = n a)
    (hd : GlobalTheory.FlagPoly.dimGr D.what₂.Tau O.N O.j + ∑ a, n a * (n a - 1) / 2 = (O.var c).dim) :
    ∃ (V : Cover (O.var c)) (B : Scheme.{0}) (_ : IsIntegral B) (q : B ⟶ Sp (𝓞 D.what₂.LL))
      (_ : IsArithVar q (GlobalTheory.FlagPoly.dimGr D.what₂.Tau O.N O.j)) (π : V.X ⟶ B) (w : π ≫ q = V.p)
      (M : D.what₂.Tau × Bool → B.Modules) (h : ∀ a, VMetric q (M a) (n a)) (H : ∀ a, (h a).IsCInf)
      (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (M a)) (n a)), IsFlagBundle π M n fl ∧
      ∀ a (i : Fin (n a)), V.Induces (adlOf (O.Φ.C c) (O.met.hm c)
        (Finsupp.single (ArIn.ind ∅, some R, Sum.inl (cond a.2 (DV.tauEmb D a.1) (conjEmb (DV.tauEmb D a.1)),
          (pos (!a.2) i : ℕ))) (cond (!a.2) (-1) 1))) (VMetric.grLB (fl a) i ((H a).pull π w)) 1 := by
  obtain rfl := funext hn
  obtain ⟨xa, _, hcw⟩ := hC
  have hm : O.met.hm = metsOf xa O.Φ := hcw.hm_eq
  have := O.s.T.smooth
  let emb := fun a : D.what₂.Tau × Bool => (cond a.2 (DV.tauEmb D a.1) (conjEmb (DV.tauEmb D a.1)) : D.host.E →+* ℂ)
  obtain ⟨B, ρB, f, φ, hρ, hf, hdim, hl⟩ := UpperTheory.flag_polynomial_dimension D O c
  obtain ⟨g⟩ := nonempty_genFrame hρ
  obtain ⟨g', hg⟩ := hf.exists_isMap g
  obtain ⟨N, hN, hex⟩ := exists_base hρ g
  choose M hM A hA hL using fun a : D.what₂.Tau × Bool => hex (emb a) (!a.2)
  let G := fun σ => xa.eigMetAt σ (some R)
  choose h hh using fun a => UpperTheory.generic_frame_true_model _ _ _ _ _ _ _ _ _ _ _ B ρB hρ g (emb a) N (M a) (hM a) (!a.2) (A a) G (hA a)
    fun σ σ' y y' k k' a₁ a₂ a₃ => GlobalTheory.ShFam.ConjMet.eigMetAt_conj xa a₁ a₂ a₃ _ _
  have hH : ∀ a, (h a).IsCInf := fun a => UpperTheory.smooth_frame_generic _ _ _ _ _ _ _ _ _ _ _ B ρB hρ g (emb a) N (M a) (!a.2) (A a) G (h a)
    (hA a) (fun σ => ToroidalCompactificationData.smoothOn_eigMetAt_some _ _ _ _ _ _ _ xa σ R hR (ToroidalCompactificationData.hodge_smoothOn _ _ _ _ _ _ _ xa σ)) (hh a)
  have := N.ar.isIntegral
  have arN : IsArithVar N.p (GlobalTheory.FlagPoly.dimGr D.what₂.Tau O.N O.j) := hdim ▸ N.ar
  obtain ⟨X, hX, π, fl, hfl, ar, nX⟩ := GlobalTheory.FlagEx.main _ N.X N.p _ arN hN _ M _ hM
  rw [hd] at ar
  obtain ⟨j, hj, A', pb, hA'⟩ := exists_flag_model (O.Φ.C c) B ρB f φ hf hρ g g' hg emb (UpperTheory.embedding_bijective_multiplicity D O).1 (fun a => !a.2) N M
    hM A hA X π fl hfl _ ar nX hl
  let P : GlobalTheory.TrueGeo.Model (O.var c) := ⟨X, π ≫ N.p, ar, j, pb⟩
  refine ⟨Cover.ofModel P nX, N.X, inferInstance, N.p, arN, π, rfl, M, h, hH, fl, hfl, fun a i => ?_⟩
  refine Cover.induces_ofModel (M := P) (k := 1) nX (induced_grLB (O.Φ.C c) P (emb a) _ (!a.2) (A' a) (fl a) i _
    (fun p => by simp [ArIn.ind]) (some R) G _ _ _ (fun σ n => by rw [hm]; rfl) (hA' a).1 ?_ ?_ (hA' a).2.2)
  · exact UpperTheory.eigenvariety_over_frame _ _ _ _ _ _ _ _ _ _ _ B _ ρB _ f φ hf hρ g g' _ hg (emb a) _ _ N.j j π hj (M a) (hM a) _ (A a) (A' a) (hA a)
      (hA' a).1 (hA' a).2.1 (hL a)
  · exact UpperTheory.eigenvariety_over_frame_alt _ _ _ _ _ _ _ _ _ _ _ B _ ρB _ f φ hf hρ g g' _ hg (emb a) _ _ N.j j π hj (M a) (hM a) _ (A a) (A' a) (hA a)
      (hA' a).1 (hA' a).2.1 _ _ rfl G (h a) (hh a)

theorem nonempty_bunModel {D : D7} (O : Setup D) (hC : O.Core) {R : ℝ} (hR : 2 ≤ R) (c : O.s.Comp) :
    Nonempty (BunModel O ∅ R c) := by
  obtain ⟨V, B, _, q, ar, π, w, M, h, H, fl, hfl, hI⟩ := exists_bun O hC hR c _ (UpperTheory.embedding_bijective_multiplicity D O).2
    (GlobalTheory.FlagBlockDim.dim_eq_dimGr_add O c)
  refine ⟨BunModel.mk V B q ar π w M h H fl hfl fun a i => ?_⟩
  convert hI a i using 2
  have hp := O.S.p_eq
  have hq := O.S.rank_eq
  have hi := i.2
  obtain ⟨τ, _ | _⟩ := a
  · simp only [rkB, cond_false] at hi
    simp only [rootSym, cond_false, Bool.not_false, cond_true, pos, Fin.val_rev, rkB]
    rw [if_neg (by omega)]
    congr 5
    change _ = ((Fin.rev i : Fin _) : ℕ)
    rw [Fin.val_rev]
    simp only [rkB, cond_false]
    omega
  · simp only [rkB, cond_true] at hi
    simp only [rootSym, cond_false, Bool.not_true, cond_true, pos, zero_add]
    rw [if_pos (by omega)]

end GlobalTheory.BcLie

end
