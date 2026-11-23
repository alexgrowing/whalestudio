import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechKodairaSpencerClassAbelianTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldImageOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPullbackLineBundleTransitionEqAppLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianTripleMapIsOpenImmersionOpensRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionEqBasePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMovesAlongSemiAbelianTripleMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTranslateLiftsSemiAbelianTripleMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSOpen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull_chart {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
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

theorem proper_ample_kTriv {S S' : Scheme.{0}} [IsAffine S'] {f : S' ⟶ S} {t : SAB H S} {u u' : SAB H S'}
    (m : SABMap u t f) (m' : SABMap u' t f) (hP : IsProper u.G.hom) (hA : Out.RelAmple u.G u.PP.L)
    (hK : Out.KTriv u.G u.PP.L) : IsProper u'.G.hom ∧ Out.RelAmple u'.G u'.PP.L ∧ Out.KTriv u'.G u'.PP.L := by
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := 𝟙 S') m ((Category.id_comp f).symm ▸ m')
  obtain ⟨w, hw, -⟩ := n.lin
  exact ⟨MorphismProperty.of_isPullback n.cart.1 hP,
    relAmple_pull n.cart.1 u.PP.isLB u'.PP.isLB ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S') (fun _ => trivial) hA,
    kTriv_pull n.cart u.PP.isLB u'.PP.isLB ((isGen_iff w).1 hw) hK⟩

theorem bijective_appLE {X X' : Scheme.{0}} (j : X' ⟶ X) [IsOpenImmersion j] {U : X.Opens} {U' : X'.Opens}
    (h : j ''ᵁ U' = U) (e : U' ≤ j ⁻¹ᵁ U) : Function.Bijective (j.appLE U U' e).hom := by
  subst h
  rw [← Scheme.Hom.appIso_hom']
  exact ConcreteCategory.bijective_of_isIso (j.appIso U').hom

theorem resG_appLE {Y Z : Scheme.{0}} (m : Z ⟶ Y) (U : Y.Opens) {V V' : Z.Opens} (h : V ≤ m ⁻¹ᵁ U) (e : V' ≤ V)
    (r : Γ(Y, U)) : resG Z e ((m.appLE U V h).hom r) = (m.appLE U V' (e.trans h)).hom r := by
  rw [← Scheme.Hom.appLE_map m h (homOfLE e).op]
  rfl

theorem app_appLE {X X' G G' : Scheme.{0}} {φ : G' ⟶ G} {p' : G' ⟶ X'} {p : G ⟶ X} {j : X' ⟶ X}
    (sq : φ ≫ p = p' ≫ j) {U : X.Opens} {U' : X'.Opens} (e : U' ≤ j ⁻¹ᵁ U) {O : G.Opens} (h : O ≤ p ⁻¹ᵁ U)
    (h' : φ ⁻¹ᵁ O ≤ p' ⁻¹ᵁ U') (r : Γ(X, U)) :
    (φ.app O).hom ((p.appLE U O h).hom r) = (p'.appLE U' (φ ⁻¹ᵁ O) h').hom ((j.appLE U U' e).hom r) := by
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE]
  congr 3

theorem valR_comp_appLE {Y Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Y) (m : Y ⟶ Z) {O : Z.Opens}
    {O' : Y.Opens} (e : O' ≤ m ⁻¹ᵁ O) (hz : ⊤ ≤ z ⁻¹ᵁ O') (f : Γ(Z, O)) :
    valR (z ≫ m) O f = valR z O' ((m.appLE O O' e).hom f) := by
  rw [GlobalTheory.CechKS.valR_comp_app, ← GlobalTheory.CechKS.valR_resG z e hz]
  rfl

theorem isKS_of_openImmersion {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {j : X' ⟶ X} [IsOpenImmersion j]
    (m : SABMap t' t j) (cp : ChartPull t'.PP.L t.PP.L m.φ) (V : X.Opens) (U : X.affineOpens) (hUV : U.1 ≤ V)
    (U' : X'.affineOpens) (hU : j ''ᵁ U'.1 = U.1) (ψ : Γ(X, U.1) ≃+* Γ(X', U'.1)) (e : U'.1 ≤ j ⁻¹ᵁ U.1)
    (hψ : ∀ r, ψ r = (j.appLE U.1 U'.1 e).hom r) (hch : chart U' ≫ j = spMap ψ.toRingHom ≫ chart U) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (v' : Fin n → (Sp (DualNumber Γ(X', U'.1)) ⟶ t'.G.left))
    (hv : ∀ i, IsTanAtG t (chart U) (v i)) (hv' : ∀ i, IsTanAtG t' (chart U') (v' i))
    (hvv : ∀ i, v' i ≫ m.φ = spMap (dualMap ψ.toRingHom) ≫ v i)
    (D : Γ(X, U.1) → Γ(X, U.1)) (D' : Γ(X', U'.1) → Γ(X', U'.1)) (hD : ∀ r, D' (ψ r) = ψ (D r))
    (Θ : Matrix (Fin n) (Fin n) Γ(X', U'.1)) (h : IsKS t' ⊤ U' v' D' Θ) : IsKS t V U v D (Θ.map ψ.symm) := by
  obtain ⟨J, W, c, d, hcov, hWc, hd, hl, hr⟩ := h
  obtain ⟨hoi, hrange⟩ := GlobalTheory.sabMap_isOpenImmersion_opensRange E H X X' t t' j m
  have sq : m.φ ≫ t.G.hom = t'.G.hom ≫ j := m.cart.1.w
  rw [inf_top_eq] at hcov
  have hWU : ∀ i, W i ≤ t'.G.hom ⁻¹ᵁ U'.1 := fun i => hcov ▸ le_iSup W i
  have hpre : t'.G.hom ⁻¹ᵁ U'.1 = m.φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, sq, Scheme.Hom.comp_preimage, ← hU, Scheme.Hom.preimage_image_eq]
  have hle : ∀ i {O : t.G.left.Opens}, O ≤ m.φ ''ᵁ W i → m.φ ⁻¹ᵁ O ≤ W i := fun i O hO =>
    (m.φ.preimage_mono hO).trans (m.φ.preimage_image_eq (W i)).le
  choose d₂ hd₂ hd₂' using fun i => GlobalTheory.LogKS.isField_image _ _ m.φ (W i) (d i) (hd i)
  refine ⟨J, fun i => m.φ ''ᵁ W i, fun i => cp.idx (c i), d₂, ?_, fun i => ?_, hd₂, fun i hW r => ?_, ?_⟩
  · rw [← Scheme.Hom.image_iSup, hcov, hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, hrange, inf_eq_left.2 hUV,
      inf_eq_right]
    apply t.G.hom.preimage_mono
    rw [← hU]
    exact j.image_le_opensRange _
  · rintro _ ⟨y, hy, rfl⟩
    exact cp.le _ (hWc i hy)
  · have hinj : Function.Injective (m.φ.app (m.φ ''ᵁ W i)).hom :=
      (ConcreteCategory.bijective_of_isIso (m.φ.app (m.φ ''ᵁ W i))).1
    apply hinj
    have h1 := hle i le_rfl
    rw [hd₂' i _ le_rfl, app_appLE sq e hW (h1.trans (hWU i)), app_appLE sq e hW (h1.trans (hWU i)), ← hψ, ← hψ,
      ← hD, ← resG_appLE _ _ (hWU i) h1, (hd i).2.2 _ _ h1 le_rfl, hl i (hWU i), resG_appLE]
  · intro i i' O hO f S _ φ g₀ w hg hO₀ hT
    have hOi : O ≤ m.φ ''ᵁ W i := hO.trans inf_le_left
    have hOi' : O ≤ m.φ ''ᵁ W i' := hO.trans inf_le_right
    obtain ⟨g₁, rfl⟩ : ∃ g₁ : Sp S ⟶ t'.G.left, g₁ ≫ m.φ = g₀ :=
      ⟨IsOpenImmersion.lift m.φ g₀ (by
        rintro _ ⟨y, rfl⟩
        obtain ⟨z, -, hz⟩ := hOi (hO₀ (Set.mem_univ y))
        exact ⟨z, hz⟩), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨φ₁, rfl⟩ : ∃ φ₁ : Γ(X', U'.1) →+* S, φ₁.comp ψ.toRingHom = φ :=
      ⟨φ.comp ψ.symm.toRingHom, RingHom.ext fun r => by simp⟩
    have hg₁ : g₁ ≫ t'.G.hom = spMap φ₁ ≫ chart U' := by
      rw [← cancel_mono j, Category.assoc, ← sq, ← Category.assoc, hg, Category.assoc, hch, ← Category.assoc]
      congr 1
      exact Spec.map_comp (CommRingCat.ofHom ψ.toRingHom) (CommRingCat.ofHom φ₁)
    choose w₁ hw₁ hT₁ using fun a => GlobalTheory.TransLift.lift_isTranslate E H X X' t t' j m _ _ ψ.toRingHom (chart U) (chart U') hch
      (v a) (v' a) (hv a) (hv' a) (hvv a) S φ₁ g₁ hg₁ (w a) (hT a)
    obtain rfl : w = fun a => w₁ a ≫ m.φ := funext fun a => (hw₁ a).symm
    have hO₁ : ⊤ ≤ g₁ ⁻¹ᵁ (m.φ ⁻¹ᵁ O) := hO₀
    have key := hr i i' (m.φ ⁻¹ᵁ O) (le_inf (hle i hOi) (hle i' hOi')) ((m.φ.app O).hom f) S φ₁ g₁ w₁ hg₁ hO₁ hT₁
    have hgc : ⊤ ≤ g₁ ⁻¹ᵁ (t'.PP.L.U (c i) ⊓ t'.PP.L.U (c i')) :=
      hO₁.trans (g₁.preimage_mono (le_inf ((hle i hOi).trans (hWc i)) ((hle i' hOi').trans (hWc i'))))
    have hwc : ∀ b, ⊤ ≤ w₁ b ⁻¹ᵁ (t'.PP.L.U (c i) ⊓ t'.PP.L.U (c i')) := fun b =>
      GlobalTheory.CechKS.le_preimage_of_red (GlobalTheory.LogKS.IsTranslate.fst_comp E H X' t' _ S φ₁ (chart U') g₁ (v' b) (w₁ b) hg₁ (hv' b) (hT₁ b)) hgc
    have hgp := GlobalTheory.chartPull_g_appLE _ _ _ _ m.φ cp (c i) (c i')
    have hgi : ((t'.PP.L.g (c i) (c i'))⁻¹).val = (m.φ.appLE _ _
        (le_inf (inf_le_left.trans (cp.le (c i))) (inf_le_right.trans (cp.le (c i'))))).hom
        ((t.PP.L.g (cp.idx (c i)) (cp.idx (c i')))⁻¹).val :=
      Units.inv_eq_of_mul_eq_one_right (by rw [hgp, ← map_mul, Units.mul_inv, map_one])
    rw [GlobalTheory.CechKS.valR_comp_app, map_sub, hd₂' i O hOi, hd₂' i' O hOi', key]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hgp, hgi]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (by simp) (congrArg₂ (· * ·) (congrArg TrivSqZeroExt.snd ?_) ?_))
      (congrArg TrivSqZeroExt.snd ?_)
    · exact (valR_comp_appLE (w₁ b) m.φ _ (hwc b) _).symm
    · exact (valR_comp_appLE g₁ m.φ _ hgc _).symm
    · exact (GlobalTheory.CechKS.valR_comp_app (w₁ a) m.φ O f).symm

def derivMap {A B : Type} [CommRing A] [CommRing B] (ψ : A ≃+* B) (D : Derivation ℤ A A) : Derivation ℤ B B :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap
    ((ψ.toAddMonoidHom.comp D.toLinearMap.toAddMonoidHom).comp ψ.symm.toAddMonoidHom)) fun a b => by
      simp

theorem derivMap_apply {A B : Type} [CommRing A] [CommRing B] (ψ : A ≃+* B) (D : Derivation ℤ A A) (r : A) :
    derivMap ψ D (ψ r) = ψ (D r) := by
  simp [derivMap]

theorem exists_isKS_of_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens), U.1 ≤ V → ∀ (t' : SAB H (Sp Γ(X, U.1))), Nonempty (SABMap t' t (chart U)) → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ D : Derivation ℤ Γ(X, U.1) Γ(X, U.1), ∃ Θ, IsKS t V U v D Θ := by
  intro E _ _ _ H X t V U hUV t' ⟨m'⟩ hP hA hK n v hv hb D
  obtain ⟨u, m, ⟨cp⟩⟩ := exists_pull_chart (chart U) t
  obtain ⟨hP', hA', hK'⟩ := proper_ample_kTriv m' m hP hA hK
  haveI : IsOpenImmersion (chart U) := U.2.isOpenImmersion_fromSpec
  let U' : (Sp Γ(X, U.1)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hU : chart U ''ᵁ U'.1 = U.1 := by
    show chart U ''ᵁ ⊤ = U.1
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact U.2.opensRange_fromSpec
  have e : U'.1 ≤ chart U ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  let ψ : Γ(X, U.1) ≃+* Γ(Sp Γ(X, U.1), U'.1) := RingEquiv.ofBijective _ (bijective_appLE (chart U) hU e)
  have hch : chart U' ≫ chart U = spMap ψ.toRingHom ≫ chart U :=
    (IsAffineOpen.SpecMap_appLE_fromSpec (chart U) U.2 U'.2 e).symm
  obtain ⟨v', hvv, hv', hb'⟩ := GlobalTheory.SabTan.tanBasis_sabMap E H X _ t u (chart U) m _ _ ψ.toRingHom (chart U) (chart U') hch n v hv hb
  obtain ⟨Θ, hΘ⟩ := GlobalTheory.T.exists_cech_kodairaSpencer_class_abelianTriple E H _ u hP' hA' hK' U' n v' hv' hb' (derivMap ψ D)
  exact ⟨_, isKS_of_openImmersion m cp V U hUV U' hU ψ e (fun _ => rfl) hch v v' hv hv' hvv D _
    (derivMap_apply ψ D) Θ hΘ⟩

end GlobalTheory.KSOpen
