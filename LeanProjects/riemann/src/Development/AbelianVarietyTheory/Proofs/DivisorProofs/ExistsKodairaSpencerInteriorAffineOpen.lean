import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechKodairaSpencerClassAbelianTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperAmpleKTriv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfIsTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMovesAlongSemiAbelianTripleMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldImageOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTranslateLiftsSemiAbelianTripleMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPullbackLineBundleTransitionEqAppLEStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianTripleMapIsOpenImmersionOpensRangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionEqBasePointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSInterior

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sab_chartPull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ (t' : SAB H S') (m : SABMap t' t f), Nonempty (ChartPull t'.PP.L t.PP.L m.φ) := by
  have h := isGrpPullback_pullback t.G f
  obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.CubePf.cubePull S S' t.G _ (cubeMapOf h) t.PP t.cub
  have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
      pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
      pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  refine ⟨⟨(Over.pullback f).obj t.G, IsSemiAbelian.pullback f t.G t.semi, OAct.pullback f t.G t.act,
    (cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_⟩, ⟨cubeMapOf h, h, rfl, hact, hc'⟩,
    ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L _ _ rfl⟩⟩
  · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
    refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
    · fin_cases i
      · exact (pa _ a).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
    refine LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L _ U.left (Category.id_comp _))
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
    fin_cases i
    · simp [U]
    · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)

end GlobalTheory.KSInterior

namespace GlobalTheory.KSInterior

theorem exists_derivation_transport {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (D : Derivation ℤ A A) :
    ∃ D' : Derivation ℤ B B, ∀ r, D' (e r) = e (D r) := by
  let f : B →ₗ[ℤ] B :=
    { toFun := fun b => e (D (e.symm b)), map_add' := fun a b => by simp, map_smul' := fun k b => by simp }
  refine ⟨{ toLinearMap := f, map_one_eq_zero' := by simp [f], leibniz' := fun a b => ?_ }, fun r => by simp [f]⟩
  simp only [f, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Derivation.leibniz, smul_eq_mul, map_add,
    RingEquiv.apply_symm_apply]

end GlobalTheory.KSInterior

namespace GlobalTheory.KSInterior

theorem isKS_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) [IsOpenImmersion j] (m : SABMap t' t j), Nonempty (ChartPull t'.PP.L t.PP.L m.φ) → ∀ (V : X.Opens) (W : X.affineOpens) (W' : X'.affineOpens) (hW' : W'.1 = j ⁻¹ᵁ W.1), Function.Bijective (j.appLE W.1 W'.1 hW'.le).hom → W.1 ≤ V → W.1 ≤ j.opensRange → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, W.1)) ⟶ t.G.left)) (v' : Fin n → (Sp (DualNumber Γ(X', W'.1)) ⟶ t'.G.left)), (∀ i, IsTanAtG t (chart W) (v i)) → (∀ i, IsTanAtG t' (chart W') (v' i)) → (∀ i, v' i ≫ m.φ = spMap (dualMap (j.appLE W.1 W'.1 hW'.le).hom) ≫ v i) → ∀ (D : Γ(X, W.1) → Γ(X, W.1)) (D' : Γ(X', W'.1) → Γ(X', W'.1)), (∀ r, D' ((j.appLE W.1 W'.1 hW'.le).hom r) = (j.appLE W.1 W'.1 hW'.le).hom (D r)) → ∀ Θ' : Matrix (Fin n) (Fin n) Γ(X', W'.1), IsKS t' ⊤ W' v' D' Θ' → ∃ Θ, IsKS t V W v D Θ := by
  intro E _ _ _ H X X' t t' j _ m hcp V W W' hW' hbij hWV hWr n v v' hv hv't hvv D D' hD Θ' hKS
  obtain ⟨cp⟩ := hcp
  obtain ⟨J, Wc, jj, d, hsup, hj, hfld, hcomp, htest⟩ := hKS
  obtain ⟨hφo, hφr⟩ := GlobalTheory.T.semiAbelianTripleMap_isOpenImmersion_opensRange E H X X' t t' j m
  set ψ := j.appLE W.1 W'.1 hW'.le with hψ
  let e := RingEquiv.ofBijective ψ.hom hbij
  have sq : m.φ ≫ t.G.hom = t'.G.hom ≫ j := m.cart.1.w
  have hx : chart W' ≫ j = spMap ψ.hom ≫ chart W :=
    (IsAffineOpen.SpecMap_appLE_fromSpec j W.2 W'.2 hW'.le).symm
  have hWc : ∀ i, Wc i ≤ t'.G.hom ⁻¹ᵁ W'.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t'.G.hom.preimage_mono inf_le_left))
  choose d₂ hd₂F hd₂ using fun i => GlobalTheory.T.exists_vectorField_image_openImmersion _ _ m.φ (Wc i) (d i) (hfld i)
  have hpi : ∀ i, m.φ ⁻¹ᵁ (m.φ ''ᵁ Wc i) = Wc i := fun i => m.φ.preimage_image_eq (Wc i)
  have cong : ∀ {A B : Scheme.{0}} {f g : A ⟶ B} (_ : f = g) (U : B.Opens) (U' : A.Opens) (p₁ : U' ≤ f ⁻¹ᵁ U)
      (p₂ : U' ≤ g ⁻¹ᵁ U), f.appLE U U' p₁ = g.appLE U U' p₂ := by
    intros; subst_vars; rfl
  have happ : ∀ (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ W.1) (h' : m.φ ⁻¹ᵁ O ≤ t'.G.hom ⁻¹ᵁ W'.1)
      (r : Γ(X, W.1)), (m.φ.app O).hom ((t.G.hom.appLE W.1 O h).hom r) =
        (t'.G.hom.appLE W'.1 (m.φ ⁻¹ᵁ O) h').hom (ψ.hom r) := by
    intro O h h' r
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, hψ,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, cong sq]
  have vpull : ∀ {A : Type} [CommRing A] (z : Sp A ⟶ t'.G.left) (U₁ : t.G.left.Opens) (U₂ : t'.G.left.Opens)
      (le : U₂ ≤ m.φ ⁻¹ᵁ U₁), ⊤ ≤ z ⁻¹ᵁ U₂ → ∀ y, valR z U₂ ((m.φ.appLE U₁ U₂ le).hom y) = valR (z ≫ m.φ) U₁ y := by
    intro A _ z U₁ U₂ le hz y
    have e : (m.φ.appLE U₁ U₂ le).hom y = resG _ le ((m.φ.app U₁).hom y) := rfl
    rw [e, GlobalTheory.CechKS.valR_resG z le hz, GlobalTheory.CechKS.valR_comp_app]
  refine ⟨e.symm.toRingHom.mapMatrix Θ', J, fun i => m.φ ''ᵁ Wc i, fun i => cp.idx (jj i), d₂, ?_, ?_, hd₂F, ?_, ?_⟩
  · rw [← Scheme.Hom.image_iSup, hsup, inf_top_eq, inf_eq_left.2 hWV, hW']
    have e1 : t'.G.hom ⁻¹ᵁ (j ⁻¹ᵁ W.1) = m.φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ W.1) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq]
    rw [e1, Scheme.Hom.image_preimage_eq_opensRange_inf, hφr, ← Scheme.Hom.preimage_inf, inf_eq_right.2 hWr]
  · intro i y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact cp.le _ (hj i hx)
  · intro i h r
    apply (ConcreteCategory.bijective_of_isIso (m.φ.app (m.φ ''ᵁ Wc i))).1
    have hle : m.φ ⁻¹ᵁ (m.φ ''ᵁ Wc i) ≤ Wc i := (hpi i).le
    rw [hd₂ i _ le_rfl, happ _ h (hle.trans (hWc i)), happ _ h (hle.trans (hWc i)),
      ← GlobalTheory.KSRechart.resG_appLE t'.G.hom W'.1 (hWc i) hle, ← GlobalTheory.KSRechart.resG_appLE t'.G.hom W'.1 (hWc i) hle,
      (hfld i).2.2 (Wc i) _ hle le_rfl, hcomp i (hWc i), hD]
  · intro i i' O hO f S _ φS g₀ w hg₀ hO' hw
    have hOr : ∀ y ∈ O, ∃ x, m.φ.base x = y := fun y hy => by
      obtain ⟨x, -, hx⟩ := (hO hy).1
      exact ⟨x, hx⟩
    have hg₀r : Set.range g₀.base ⊆ Set.range m.φ.base := by
      rintro _ ⟨p, rfl⟩
      exact hOr _ (hO' (Set.mem_univ p))
    set g₀' := IsOpenImmersion.lift m.φ g₀ hg₀r with hg₀'def
    have hg₀'φ : g₀' ≫ m.φ = g₀ := IsOpenImmersion.lift_fac _ _ _
    let φS' : Γ(X', W'.1) →+* S := φS.comp e.symm.toRingHom
    have hφS : φS'.comp ψ.hom = φS := by
      ext r
      show φS (e.symm (ψ.hom r)) = φS r
      congr 1
      exact e.symm_apply_apply r
    have spc : spMap φS' ≫ spMap ψ.hom = spMap (φS'.comp ψ.hom) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hg₀' : g₀' ≫ t'.G.hom = spMap φS' ≫ chart W' := by
      rw [← cancel_mono j, Category.assoc, ← sq, ← Category.assoc, hg₀'φ, hg₀, Category.assoc, hx,
        ← Category.assoc, spc, hφS]
    have hw' : ∀ a, ∃ w', w' ≫ m.φ = w a ∧ IsTranslate t' φS' g₀' (v' a) w' := fun a =>
      GlobalTheory.T.tangentTranslate_lifts_semiAbelianTripleMap E H X X' t t' j m _ _ ψ.hom (chart W) (chart W') hx (v a) (v' a) (hv a) (hv't a) (hvv a) S φS'
        g₀' hg₀' (w a) (by rw [hφS, hg₀'φ]; exact hw a)
    choose w' hw'φ hw'T using hw'
    have hOi : m.φ ⁻¹ᵁ O ≤ Wc i ⊓ Wc i' :=
      le_inf ((m.φ.preimage_mono (hO.trans inf_le_left)).trans (hpi i).le)
        ((m.φ.preimage_mono (hO.trans inf_le_right)).trans (hpi i').le)
    have hO'' : ⊤ ≤ g₀' ⁻¹ᵁ (m.φ ⁻¹ᵁ O) := by
      rw [← Scheme.Hom.comp_preimage, hg₀'φ]
      exact hO'
    have key := htest i i' (m.φ ⁻¹ᵁ O) hOi ((m.φ.app O).hom f) S φS' g₀' w' hg₀' hO'' hw'T
    rw [← hg₀'φ, GlobalTheory.CechKS.valR_comp_app, map_sub, hd₂ i O (hO.trans inf_le_left),
      hd₂ i' O (hO.trans inf_le_right), key]
    have hU' : ⊤ ≤ g₀' ⁻¹ᵁ (t'.PP.L.U (jj i) ⊓ t'.PP.L.U (jj i')) :=
      hO''.trans (g₀'.preimage_mono (hOi.trans (inf_le_inf (hj i) (hj i'))))
    have hgp := GlobalTheory.T.chartPullback_lineBundle_transition_eq_appLE _ _ t'.PP.L t.PP.L m.φ cp (jj i) (jj i')
    set le₀ : t'.PP.L.U (jj i) ⊓ t'.PP.L.U (jj i') ≤ m.φ ⁻¹ᵁ (t.PP.L.U (cp.idx (jj i)) ⊓ t.PP.L.U (cp.idx (jj i'))) :=
      le_inf (inf_le_left.trans (cp.le (jj i))) (inf_le_right.trans (cp.le (jj i')))
    have hgi : ((t'.PP.L.g (jj i) (jj i'))⁻¹ : Γ(t'.G.left, _)ˣ).val =
        (m.φ.appLE _ _ le₀).hom ((t.PP.L.g (cp.idx (jj i)) (cp.idx (jj i')))⁻¹ : Γ(t.G.left, _)ˣ).val := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [hgp, ← map_mul, Units.mul_inv, map_one]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hred := GlobalTheory.T.reduction_eq_basePoint E H X' t' _ _ φS' (chart W') g₀' (v' b) (w' b) hg₀' (hv't b) (hw'T b)
    have hwU : ⊤ ≤ w' b ⁻¹ᵁ (t'.PP.L.U (jj i) ⊓ t'.PP.L.U (jj i')) := GlobalTheory.CechKS.le_preimage_of_red hred hU'
    rw [hgp, hgi, vpull _ _ _ le₀ hwU, vpull _ _ _ le₀ hU', hw'φ, hg₀'φ, ← hw'φ a, ← GlobalTheory.CechKS.valR_comp_app]
    rfl

end GlobalTheory.KSInterior

namespace GlobalTheory.KSInterior

theorem exists_isKS_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (W : Y.X.affineOpens), W.1 ≤ interior Y → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, W.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart W) (v i)) → (∀ w, IsTanAtG Y.t (chart W) w → ∃! cf : Fin n → Γ(Y.X, W.1), IsCombAtG Y.t (chart W) v cf w) → ∀ D : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1), ∃ Θ, IsKS Y.t (interior Y) W v D Θ := by
  intro E _ _ _ H Dw l Xo c Y W hW n v hv hb D
  obtain ⟨t', m, hcp⟩ := exists_sab_chartPull Y.j Y.t
  obtain ⟨m', -⟩ := GlobalTheory.ArcChartExt.exists_sab_cancel_id Y.m m
  obtain ⟨hP, hA, hK⟩ := GlobalTheory.KSObj.proper_ample_kTriv Y.oF m'
  have hWr : W.1 ≤ Y.j.opensRange := hW
  let W' : (Xo.XF c).affineOpens := ⟨Y.j ⁻¹ᵁ W.1, W.2.preimage_of_isOpenImmersion _ hWr⟩
  have hW' : W'.1 = Y.j ⁻¹ᵁ W.1 := rfl
  let ψ := Y.j.appLE W.1 W'.1 hW'.le
  have hx : chart W' ≫ Y.j = spMap ψ.hom ≫ chart W := (IsAffineOpen.SpecMap_appLE_fromSpec Y.j W.2 W'.2 hW'.le).symm
  have hbij : Function.Bijective ψ.hom := by
    have e : Y.j ''ᵁ (Y.j ⁻¹ᵁ W.1) = W.1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hWr]
    have key : ψ = Y.X.presheaf.map (eqToHom e).op ≫ (Y.j.appIso (Y.j ⁻¹ᵁ W.1)).hom := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    rw [key]
    exact ConcreteCategory.bijective_of_isIso _
  obtain ⟨v', hv'φ, hv't, hv'b⟩ := GlobalTheory.T.tangentBasis_moves_along_semiAbelianTripleMap E H _ _ Y.t t' Y.j m _ _ ψ.hom (chart W) (chart W') hx n v hv hb
  obtain ⟨D', hD'⟩ := exists_derivation_transport (RingEquiv.ofBijective ψ.hom hbij) D
  obtain ⟨Θ', hΘ'⟩ := GlobalTheory.T.exists_cech_kodairaSpencer_class_abelianTriple E H _ t' hP hA hK W' n v' hv't hv'b D'
  exact isKS_transport E H _ _ Y.t t' Y.j m hcp (interior Y) W W' hW' hbij hW hWr n v v' hv hv't hv'φ D D'
    (fun r => hD' r) Θ' hΘ'

end GlobalTheory.KSInterior
