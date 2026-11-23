import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.AdelicQuotients.AdeleGaloisActionBaseChangeCompat
import Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionBaseChange
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.CharacterColumnKernelsOfBlockChiCOfBlockChiOne
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwUnitary
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.WeilBound.NonsplitUniqueness.Places

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C

open scoped TensorProduct
open GroundTheory.Global.AdeleBaseChange

noncomputable section

section SlopeTestRemainingChoices
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem gal_central (σ : E ≃ₐ[F] E) (n : ℕ) (t : {r : ℝ // 0 < r}) :
    mapGL n (galAd σ) (centralSection E n t) = centralSection E n t := by
  have hd : 0 < Module.finrank F E := Module.finrank_pos
  let s : {r : ℝ // 0 < r} := ⟨t.1 ^ (((Module.finrank F E : ℕ) : ℝ)⁻¹), Real.rpow_pos_of_pos t.2 _⟩
  have hs : s ^ Module.finrank F E = t := by
    apply Subtype.ext
    change (t.1 ^ (((Module.finrank F E : ℕ) : ℝ)⁻¹)) ^ Module.finrank F E = t.1
    exact Real.rpow_inv_natCast_pow t.2.le hd.ne'
  rw [← hs, ← UpperTheory.centralSection_baseChange F E n s]
  exact (UpperTheory.adele_galois_action_baseChange_compat F E σ n).2.2.2.2.1 _

private theorem galOf_mul' {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : E ⊗[F] A ≃ₐ[E] B)
    (σ τ : E ≃ₐ[F] E) (b : B) : galOf e σ (galOf e τ b) = galOf e (σ * τ) b := by
  have h : ∀ x : E ⊗[F] A, Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A)
      (Algebra.TensorProduct.map (τ : E →ₐ[F] E) (AlgHom.id F A) x) =
      Algebra.TensorProduct.map ((σ * τ : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp
    | add a c ha hc => simp only [map_add, ha, hc]
  simp [galOf, h]

private theorem galOf_one' {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : E ⊗[F] A ≃ₐ[E] B)
    (b : B) : galOf e (1 : E ≃ₐ[F] E) b = b := by
  have h : ∀ x : E ⊗[F] A, Algebra.TensorProduct.map ((1 : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) x = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp
    | add a c ha hc => simp only [map_add, ha, hc]
  simp [galOf, h]

private theorem gal_module [IsGalois F E] (σ : E ≃ₐ[F] E) (hσ : σ = 1 ∨ ∀ τ, τ ∈ Subgroup.zpowers σ) (n : ℕ)
    (g : AdelicGLn.AdelicGL E n) : detModule E n (mapGL n (galAd σ) g) = detModule E n g := by
  rcases hσ with rfl | hσ
  · have : mapGL n (galAd (1 : E ≃ₐ[F] E)) g = g :=
      Units.ext (Matrix.ext fun a b => galOf_one' (adeleTensorEquiv F E) _)
    rw [this]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (AdelicGLn.AdelicGL E 0) :=
      ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    rw [Subsingleton.elim (mapGL 0 (galAd σ) g) g]
  · exact (UpperTheory.ConvolutionTheory.G.character_column_kernels_of_block_chi_c_of_block_chi_one F E σ hσ n hn).2.2 g

private theorem e_proj [IsGalois F E] {σ : E ≃ₐ[F] E} (hσ : σ = 1 ∨ ∀ τ, τ ∈ Subgroup.zpowers σ) {n : ℕ}
    {μ : Measure (normOneGL E n)} [μ.IsHaarMeasure] {θ : Twist μ} (hθ : IsGalTwist σ θ)
    {g g' : AdelicGLn.AdelicGL E n} (hg : mapGL n (galAd σ) g = g') {x y : normOneGL E n}
    (hx : (x : AdelicGLn.AdelicGL E n) = g * (centralSection E n (detModule E n g))⁻¹)
    (hy : (y : AdelicGLn.AdelicGL E n) = g' * (centralSection E n (detModule E n g'))⁻¹) :
    θ.e x = y := by
  apply Subtype.ext
  rw [hθ, hx, hy, map_mul, map_inv, gal_central, hg, ← hg, gal_module σ hσ]

private theorem e_finProj [IsGalois F E] {σ : E ≃ₐ[F] E} (hσ : σ = 1 ∨ ∀ τ, τ ∈ Subgroup.zpowers σ) {n : ℕ}
    {μ : Measure (normOneGL E n)} [μ.IsHaarMeasure] {θ : Twist μ} (hθ : IsGalTwist σ θ)
    {u u' : AdelicGLn.FiniteAdelicGL E n} (h : mapGL n (galAd σ) (finEmb E n u) = finEmb E n u') :
    θ.e (MultiplicityOne.finProj E n u) = MultiplicityOne.finProj E n u' :=
  e_proj hσ hθ h rfl rfl

private theorem ad_ext {n : ℕ} {g h : AdelicGLn.AdelicGL E n}
    (hi : UpperTheory.ConvolutionTheory.T4.pI E n g = UpperTheory.ConvolutionTheory.T4.pI E n h)
    (hf : ∀ v : Pl F, UpperTheory.ConvolutionTheory.T4.pE E n v g = UpperTheory.ConvolutionTheory.T4.pE E n v h) : g = h := by
  refine Units.ext (Matrix.ext fun a b => Prod.ext ?_ ?_)
  · exact congrFun (congrFun (congrArg (fun x : GL (Fin n) (InfiniteAdeleRing E) => x.val) hi) a) b
  · refine FiniteAdeleRing.ext E fun w => ?_
    have h1 := congrFun (congrFun (congrArg (fun x : GL (Fin n) (CompletionsOver E (w.under (𝓞 F))) => x.val)
      (hf (w.under (𝓞 F)))) a) b
    exact congrFun h1 ⟨w, inferInstance⟩

private theorem pI_finEmb {n : ℕ} (u : AdelicGLn.FiniteAdelicGL E n) : UpperTheory.ConvolutionTheory.T4.pI E n (finEmb E n u) = 1 :=
  congrArg Prod.fst (prodEquiv_finEmb u)

private theorem cmp_pE {n : ℕ} (p : Pl F) (u : PlacesOver E p) (g : AdelicGLn.AdelicGL E n) :
    GM.cmp u (UpperTheory.ConvolutionTheory.T4.pE E n p g) = finAt u.1 g :=
  Units.ext (Matrix.ext fun _ _ => rfl)

private theorem gl_ext {n : ℕ} {p : Pl F} {x y : GL (Fin n) (CompletionsOver E p)} (h : ∀ u, GM.cmp u x = GM.cmp u y) : x = y :=
  Units.ext (Matrix.ext fun a b => funext fun u =>
    congrFun (congrFun (congrArg (fun z : GL (Fin n) (u.1.adicCompletion E) => z.val) (h u)) a) b)

private theorem over_unique {v p : Pl F} (u : PlacesOver E v) (u' : PlacesOver E p) (h : u.1 = u'.1) : v = p := by
  have h1 : v.asIdeal = u.1.asIdeal.under (𝓞 F) := u.2.over
  have h2 : p.asIdeal = u'.1.asIdeal.under (𝓞 F) := u'.2.over
  exact HeightOneSpectrum.ext (by rw [h1, h2, h])

private theorem fin_local {n : ℕ} (w : Pl E) (x : GL (Fin n) (w.adicCompletion E)) :
    finAt w (finEmb E n (AdelicGLn.localEmbedding w x)) = x :=
  (UpperTheory.ConvolutionTheory.Tf.locEmb E n w).2.1 x

private theorem fin_local_ne {n : ℕ} {w u : Pl E} (h : u ≠ w) (x : GL (Fin n) (w.adicCompletion E)) :
    finAt u (finEmb E n (AdelicGLn.localEmbedding w x)) = 1 :=
  (UpperTheory.ConvolutionTheory.Tf.locEmb E n w).2.2.1 u h x

private theorem pE_local_ne {n : ℕ} {v p : Pl F} (hv : v ≠ p) (w : PlacesOver E p) (x : GL (Fin n) (w.1.adicCompletion E)) :
    UpperTheory.ConvolutionTheory.T4.pE E n v (finEmb E n (AdelicGLn.localEmbedding w.1 x)) = 1 := by
  refine gl_ext fun u => ?_
  rw [cmp_pE, map_one, fin_local_ne (fun e => hv (over_unique u w e))]

private theorem gal_local {σ : E ≃ₐ[F] E} {n : ℕ} {v : Pl F} {w : PlacesOver E v} (hw : ∀ u : PlacesOver E v, u = w)
    {s : Gw n w.1 →* Gw n w.1} (hs : IsLocGal σ w s) (y : Gw n w.1) :
    mapGL n (galAd σ) (finEmb E n (AdelicGLn.localEmbedding w.1 y)) =
      finEmb E n (AdelicGLn.localEmbedding w.1 (s y)) := by
  have hc := UpperTheory.adele_galois_action_baseChange_compat F E σ n
  refine ad_ext (F := F) ?_ fun v' => ?_
  · rw [hc.1, pI_finEmb, pI_finEmb, map_one]
  · rw [hc.2.1 v']
    by_cases hv : v' = v
    · subst hv
      refine gl_ext fun u => ?_
      obtain rfl := hw u
      rw [hs, cmp_pE, cmp_pE, fin_local, fin_local]
    · rw [pE_local_ne hv, pE_local_ne hv, map_one]

private theorem galFin_mul' (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F)
    (y : CompletionsOver E v) :
    galFin σ v (algebraMap (v.adicCompletion F) (CompletionsOver E v) a * y) =
      algebraMap (v.adicCompletion F) (CompletionsOver E v) a * galFin σ v y := by
  obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
  rw [← tensorEquiv'_tmul_mul]
  change tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v ((1 ⊗ₜ a) * t)))) =
    _ * tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v t)))
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply, ← tensorEquiv'_tmul_mul, map_mul,
    Algebra.TensorProduct.map_tmul]
  simp

private theorem galFin_cont' (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (galFin σ v) := by
  let L : CompletionsOver E v →ₗ[v.adicCompletion F] CompletionsOver E v :=
    { toFun := galFin σ v
      map_add' := map_add _
      map_smul' := fun a y => by
        simp only [Algebra.smul_def, RingHom.id_apply]
        exact galFin_mul' σ v a y }
  exact IsModuleTopology.continuous_of_linearMap L

private def eW {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    CompletionsOver E v ≃+* w.1.adicCompletion E :=
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  RingEquiv.piUnique fun u : PlacesOver E v => u.1.adicCompletion E

private theorem eW_apply {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w)
    (y : CompletionsOver E v) : eW w hw y = y w := rfl

private theorem eW_cont {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) : Continuous (eW w hw) :=
  continuous_apply w

private theorem eW_symm_cont {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    Continuous (eW w hw).symm :=
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  (Homeomorph.piUnique fun u : PlacesOver E v => u.1.adicCompletion E).symm.continuous

private def rr (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    w.1.adicCompletion E →+* w.1.adicCompletion E :=
  ((eW w hw : CompletionsOver E v ≃+* _) : CompletionsOver E v →+* _).comp
    ((galFin σ v).comp (((eW w hw).symm : _ ≃+* CompletionsOver E v) : _ →+* CompletionsOver E v))

private theorem rr_apply (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w)
    (y : w.1.adicCompletion E) : rr σ w hw y = eW w hw (galFin σ v ((eW w hw).symm y)) := rfl

private theorem rr_cont (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    Continuous (rr σ w hw) :=
  (eW_cont w hw).comp ((galFin_cont' σ v).comp (eW_symm_cont w hw))

private theorem rr_inv (σ τ : E ≃ₐ[F] E) (h : σ * τ = 1) {v : Pl F} (w : PlacesOver E v)
    (hw : ∀ u : PlacesOver E v, u = w) (y : w.1.adicCompletion E) : rr σ w hw (rr τ w hw y) = y := by
  rw [rr_apply, rr_apply, RingEquiv.symm_apply_apply]
  have h1 : galFin σ v (galFin τ v ((eW w hw).symm y)) = (eW w hw).symm y := by
    change galOf (tensorEquiv' E v) σ (galOf (tensorEquiv' E v) τ _) = _
    rw [galOf_mul', h, galOf_one']
  rw [h1, RingEquiv.apply_symm_apply]

private theorem mapGL_rr_inv (σ τ : E ≃ₐ[F] E) (h : σ * τ = 1) {v : Pl F} (w : PlacesOver E v)
    (hw : ∀ u : PlacesOver E v, u = w) (n : ℕ) (g : Gw n w.1) :
    mapGL n (rr σ w hw) (mapGL n (rr τ w hw) g) = g :=
  Units.ext (Matrix.ext fun a b => rr_inv σ τ h w hw _)

private def sOf (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) (n : ℕ) :
    Gw n w.1 ≃ₜ* Gw n w.1 where
  toFun := mapGL n (rr σ w hw)
  invFun := mapGL n (rr σ⁻¹ w hw)
  left_inv := mapGL_rr_inv σ⁻¹ σ (inv_mul_cancel σ) w hw n
  right_inv := mapGL_rr_inv σ σ⁻¹ (mul_inv_cancel σ) w hw n
  map_mul' := map_mul _
  continuous_toFun := Continuous.units_map _ (continuous_id.matrix_map (rr_cont σ w hw))
  continuous_invFun := Continuous.units_map _ (continuous_id.matrix_map (rr_cont σ⁻¹ w hw))

private theorem sOf_isLocGal (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) (n : ℕ) :
    IsLocGal σ w ((sOf σ w hw n : Gw n w.1 ≃ₜ* Gw n w.1) : Gw n w.1 →* Gw n w.1) := by
  intro g
  refine Units.ext (Matrix.ext fun a b => ?_)
  change (galFin σ v ((g : Matrix (Fin n) (Fin n) (CompletionsOver E v)) a b)) w =
    rr σ w hw (((g : Matrix (Fin n) (Fin n) (CompletionsOver E v)) a b) w)
  rw [rr_apply, eW_apply]
  have : (eW w hw).symm (((g : Matrix (Fin n) (Fin n) (CompletionsOver E v)) a b) w) =
      (g : Matrix (Fin n) (Fin n) (CompletionsOver E v)) a b := by
    rw [RingEquiv.symm_apply_eq]; rfl
  rw [this]

private def twRep {G : Type} [Group G] [TopologicalSpace G] (τ : SmIrr G) (s : G ≃ₜ* G) : SmIrr G where
  V := τ.V
  ρ := τ.ρ.comp (s : G →* G)
  smooth x := (τ.smooth x).preimage s.continuous
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 τ.irred
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g x hx => ?_⟩
    obtain ⟨g, rfl⟩ := s.surjective g
    exact hW g x hx

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.C.locGalEx :
    UpperTheory.ConvolutionTheory.C.LocGalEx := by
  intro F E _ _ _ _ _ _ σ hp n v w hns
  have hw : ∀ u : PlacesOver E v, u = w := fun u => PositivityTheory.tft.PlacesPf.unique_of_not_split hp v hns w u
  have hσ : σ = 1 ∨ ∀ τ, τ ∈ Subgroup.zpowers σ := by
    by_cases h1 : σ = 1
    · exact Or.inl h1
    · right
      intro τ
      haveI : Fact (Module.finrank F E).Prime := ⟨hp⟩
      exact mem_zpowers_of_prime_card (IsGalois.card_aut_eq_finrank F E) h1
  have hloc := sOf_isLocGal σ w hw n
  refine ⟨hw, sOf σ w hw n, hloc, fun μ _ θ hθ => ?_⟩
  have hint : ∀ g x, θ.U (rhoL μ w.1 g x) = rhoL μ w.1 (sOf σ w hw n g) (θ.U x) := fun g x => by
    change θ.U (rightRegularRep (rationalGLOne E n) μ (MultiplicityOne.finProj E n _) x) =
      rightRegularRep (rationalGLOne E n) μ (MultiplicityOne.finProj E n _) (θ.U x)
    rw [(UpperTheory.ConvolutionTheory.Dp.twUnitary E n μ θ).2.2, e_finProj hσ hθ (gal_local hw hloc g)]
    rfl
  refine ⟨hint, fun V τ hV hVU hocc => ?_⟩
  obtain ⟨U, hU, -, -⟩ := UpperTheory.ConvolutionTheory.C.twistUnitary E n μ θ
  have hUa : ∀ x, θ.U x = U x := fun x => by rw [← hU]; rfl
  set s := sOf σ w hw n with hs
  let τ' : SmIrr (Gw n w.1) := twRep τ s.symm
  have hocc' : Occurs μ V w.1 τ' := by
    obtain ⟨f, hf0, hfV, hf⟩ := hocc
    refine ⟨(θ.U : LL μ →ₗ[ℂ] LL μ) ∘ₗ f, ?_, fun x => ?_, fun g (x : τ.V) => ?_⟩
    · intro h0
      refine hf0 (LinearMap.ext fun x => U.injective ?_)
      have h : θ.U (f x) = 0 := LinearMap.congr_fun h0 x
      rw [hUa] at h
      rw [h, LinearMap.zero_apply, map_zero]
    · rw [← hVU]
      exact ⟨f x, hfV x, rfl⟩
    · have e := hint (s.symm g) (f x)
      rw [s.apply_symm_apply, ← hf] at e
      exact e
  letI : MeasurableSpace (Gw n w.1) := borel _
  haveI : BorelSpace (Gw n w.1) := ⟨rfl⟩
  obtain ⟨-, h2, -⟩ := UpperTheory.ConvolutionTheory.C.occursBasics E n μ V w.1 Measure.haar hV
  obtain ⟨J⟩ := h2 τ' τ hocc' hocc
  refine ⟨J.toLinearEquiv, fun g x => ?_⟩
  have e := Representation.IntertwiningMap.isIntertwining _ _ J.toIntertwiningMap (s g) x
  have e2 : τ'.ρ (s g) = τ.ρ g := congrArg τ.ρ (s.symm_apply_apply g)
  rw [e2] at e
  exact e
