import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAbelianLocusChartRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAffineOpenAbelianPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMovesAlongSemiAbelianTripleMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianTripleMapIsOpenImmersionOpensRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTranslateLiftsSemiAbelianTripleMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionEqBasePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPullbackLineBundleTransitionEqAppLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTripleAbelianLocusProperRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleEqCoboundaryAddLogDerivativesAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechAff

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull_charts {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ (t' : SAB H S') (m : SABMap t' t f) (k : t.PP.L.ι → t'.PP.L.ι),
      (∀ a, t'.PP.L.U (k a) = m.φ ⁻¹ᵁ t.PP.L.U a) ∧
      ∀ a b, ((t'.PP.L.g (k a) (k b)).val : Γ(t'.G.left, t'.PP.L.U (k a) ⊓ t'.PP.L.U (k b))) =
        pbT m.φ (t.PP.L.g a b).val (t'.PP.L.U (k a) ⊓ t'.PP.L.U (k b)) := by
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
    fun a _ => a, fun a => ?_, fun a b => ?_⟩
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
  · ext y
    exact mem_pull
  · refine (GlobalTheory.chartPull_g_appLE _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L (pullback.fst t.G.hom f) (pullback.fst t.G.hom f) rfl)
      (fun _ => a) (fun _ => b)).trans ?_
    exact (GlobalTheory.KS.pbT_of_le _ _ _).symm

end GlobalTheory.CechAff

namespace GlobalTheory.CechAff

open GlobalTheory.KS in

theorem exists_pullField {Y Y' : Scheme.{0}} (io : Y' ⟶ Y) [IsOpenImmersion io] (d : Fld Y) (hd : IsField ⊤ d) :
    ∃ δ : Fld Y', IsField ⊤ δ ∧ ∀ (O₁ : Y.Opens) (O : Y'.Opens) (h : O ≤ io ⁻¹ᵁ O₁) (f : Γ(Y, O₁)),
      δ O ((io.appLE O₁ O h).hom f) = (io.appLE O₁ O h).hom (d O₁ f) := by
  obtain ⟨σ, σ₁, σ₂⟩ := GlobalTheory.LogKSBal.exists_section io
  have hpi : ∀ O : Y'.Opens, O ≤ io ⁻¹ᵁ (io ''ᵁ O) := fun O => (io.preimage_image_eq O).ge
  have hσ : ∀ (O : Y'.Opens) (O₀ : Y.Opens) (h : io ''ᵁ O ≤ O₀) (f : Γ(Y, O₀)),
      σ O (pbT io f O) = resG _ h f := fun O O₀ h f => by
    rw [← pbT_rsT io h (hpi O), σ₂, rsT_of_le h]
  refine ⟨fun O f => pbT io (d (io ''ᵁ O) (σ O f)) O, ⟨fun O _ f f' => ?_, fun O _ f f' => ?_,
    fun O O' h _ f => ?_⟩, fun O₁ O h f => ?_⟩
  · simp only [map_add, hd.1 _ le_top, pbT_add]
  · simp only [map_mul, hd.2.1 _ le_top, pbT_add, pbT_mul, σ₁]
  · have h' := io.image_mono h
    have e : σ O' (resG _ h f) = resG _ h' (σ O f) := by
      rw [← hσ O' _ h', ← rsT_pbT io (hpi O) h, σ₁, rsT_of_le h]
    show pbT io (d (io ''ᵁ O') (σ O' (resG _ h f))) O' = resG _ h (pbT io (d (io ''ᵁ O) (σ O f)) O)
    rw [e, hd.2.2 _ _ h' le_top, ← rsT_of_le h', pbT_rsT _ h' (hpi O'), ← rsT_of_le h, rsT_pbT _ (hpi O) h]
  · have hO : io ''ᵁ O ≤ O₁ := (io.image_mono h).trans (io.image_preimage_le _)
    show pbT io (d (io ''ᵁ O) (σ O _)) O = _
    rw [← pbT_of_le io h, hσ O O₁ hO, hd.2.2 _ _ hO le_top, ← rsT_of_le hO, pbT_rsT _ hO (hpi O), pbT_of_le io h]

end GlobalTheory.CechAff

namespace GlobalTheory.CechAff

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isTranslate_push {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {j : X' ⟶ X} (m : SABMap t' t j)
    {R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R') (u : Sp (DualNumber R) ⟶ t.G.left)
    (u' : Sp (DualNumber R') ⟶ t'.G.left) (huu : u' ≫ m.φ = spMap (dualMap ψ) ≫ u) {S : Type} [CommRing S]
    (φS : R' →+* S) (g₀' : Sp S ⟶ t'.G.left) (w' : Sp (DualNumber S) ⟶ t'.G.left)
    (hw' : IsTranslate t' φS g₀' u' w') : IsTranslate t (φS.comp ψ) (g₀' ≫ m.φ) u (w' ≫ m.φ) := by
  obtain ⟨g', v', h₁, h₂, h₃⟩ := hw'
  have hsq : m.φ ≫ t.G.hom = t'.G.hom ≫ j := m.cart.1.w
  let T : Over X' := tEpsG (g₀' ≫ t'.G.hom)
  have heq : (tEpsG ((g₀' ≫ m.φ) ≫ t.G.hom)).hom = T.hom ≫ j := by
    show spMap _ ≫ (g₀' ≫ m.φ) ≫ t.G.hom = (spMap _ ≫ g₀' ≫ t'.G.hom) ≫ j
    rw [Category.assoc, Category.assoc, Category.assoc, hsq]
  let e : tEpsG ((g₀' ≫ m.φ) ≫ t.G.hom) ⟶ Over.mk (T.hom ≫ j) :=
    Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact heq.symm)
  refine ⟨e ≫ pushHom m.cart T g', e ≫ pushHom m.cart T v', ?_, ?_, ?_⟩
  · show 𝟙 _ ≫ g'.left ≫ m.φ = _
    rw [Category.id_comp, h₁, Category.assoc]
  · show 𝟙 _ ≫ v'.left ≫ m.φ = _
    rw [Category.id_comp, h₂, Category.assoc, huu, ← Category.assoc, GlobalTheory.TransLift.spMap_comp'',
      GlobalTheory.TransLift.dualMap_comp'']
  · rw [← MonObj.comp_mul, ← map_mul]
    show 𝟙 _ ≫ (g' * v').left ≫ m.φ = _
    rw [Category.id_comp, h₃]

end GlobalTheory.CechAff

namespace GlobalTheory.CechAff

set_option maxHeartbeats 1000000 in
open GlobalTheory.KS in

theorem exists_dlog_add_coboundary_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → (∀ i, IsAffineOpen (W i)) → ∀ z : C1 W, IsCoc W z → ∃ (cc : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (y : ∀ i, Γ(t.G.left, W i)), ∀ i i', z i i' = ∑ b, GlobalTheory.HeatV.cst t.G.hom (GlobalTheory.HeatV.bo R c).1 (inf_le_left.trans (hW i)) (cc b) * (dd' b (W i ⊓ W i') (rsT (t.PP.L.g (j i) (j i')).val (W i ⊓ W i')) * rsT (t.PP.L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) + (rsT (y i') (W i ⊓ W i') - rsT (y i) (W i ⊓ W i')) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt htt hab c hc n v' dd' hinv J W j hW hcov hWj hWaff z hz
  subst hc
  set U : (Sp R).affineOpens := GlobalTheory.HeatV.bo R (∏ i, tt i) with hUdef
  let ρ : R →+* Γ(Sp R, U.1) := GlobalTheory.HeatV.resV R (∏ i, tt i)
  have hcU : spMap ρ ≫ 𝟙 (Sp R) = chart U := by
    rw [Category.comp_id]
    show Spec.map _ = U.2.fromSpec
    rw [← (isAffineOpen_top (Sp R)).map_fromSpec U.2 (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec]
    rw [show CommRingCat.ofHom ρ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op from rfl]
    erw [Spec.map_comp]
    rfl
  obtain ⟨hv, hb⟩ := GlobalTheory.KSAbLocus.tanBasis_of_basis t v' ρ
  rw [hcU] at hv hb
  haveI : IsOpenImmersion (chart U) := U.2.isOpenImmersion_fromSpec
  obtain ⟨t', mm, k, hkU, hkg⟩ := exists_pull_charts (chart U) t
  have h2 : (U.1 : (Sp R).Opens) = PrimeSpectrum.basicOpen (∏ i, tt i) :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) (∏ i, tt i)
  have h4 : ∀ q : Sp R, q ∈ ((U.1 : (Sp R).Opens) : Set (Sp R)) → ∏ i, tt i ∉ q.asIdeal := by
    intro q hq
    rw [h2] at hq
    exact hq
  have hx : ∀ s, ∏ i, tt i ∉ ((chart U) s).asIdeal := fun s =>
    h4 _ (by rw [← U.2.range_fromSpec]; exact ⟨s, rfl⟩)
  obtain ⟨hP, hA, hK⟩ := GlobalTheory.AbLocusPol.isProper_relAmple_kTriv_of_abLocus E H R t P m tt htt hab _ (chart U) t' hx ⟨mm⟩
  let U' : (Sp Γ(Sp R, U.1)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hU : chart U ''ᵁ U'.1 = U.1 := by
    show chart U ''ᵁ ⊤ = U.1
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact U.2.opensRange_fromSpec
  have e : U'.1 ≤ chart U ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  let ψ : Γ(Sp R, U.1) ≃+* Γ(Sp Γ(Sp R, U.1), U'.1) :=
    RingEquiv.ofBijective _ (GlobalTheory.KSOpen.bijective_appLE (chart U) hU e)
  have hch : chart U' ≫ chart U = spMap ψ.toRingHom ≫ chart U :=
    (IsAffineOpen.SpecMap_appLE_fromSpec (chart U) U.2 U'.2 e).symm
  obtain ⟨v, hvv, hvt, hvb⟩ := GlobalTheory.SabTan.tanBasis_sabMap E H (Sp R) _ t t' (chart U) mm _ _ ψ.toRingHom (chart U)
    (chart U') hch n _ hv hb
  obtain ⟨hoi, hrange⟩ := GlobalTheory.sabMap_isOpenImmersion_opensRange E H (Sp R) _ t t' (chart U) mm
  have sq : mm.φ ≫ t.G.hom = t'.G.hom ≫ chart U := mm.cart.1.w
  have hrg : mm.φ.opensRange = t.G.hom ⁻¹ᵁ U.1 := by
    rw [hrange, show (chart U).opensRange = U.1 from U.2.opensRange_fromSpec]
  choose δ hδF hδ using fun a => exists_pullField mm.φ (dd' a) (hinv a).1
  let W' : J → t'.G.left.Opens := fun i => mm.φ ⁻¹ᵁ W i
  have hWr : ∀ i, W i ≤ mm.φ.opensRange := fun i => (hW i).trans hrg.ge
  have hW'aff : ∀ i, IsAffineOpen (W' i) := fun i => (hWaff i).preimage_of_isOpenImmersion mm.φ (hWr i)
  have hW'U : ∀ i, W' i ≤ t'.G.hom ⁻¹ᵁ U'.1 := fun _ => le_top
  have hW'cov : ⨆ i, W' i = t'.G.hom ⁻¹ᵁ U'.1 := by
    refine le_antisymm (iSup_le fun i => hW'U i) fun x _ => ?_
    have hx1 : mm.φ x ∈ t.G.hom ⁻¹ᵁ U.1 := hrg ▸ ⟨x, rfl⟩
    rw [← hcov] at hx1
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx1
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  have hj' : ∀ i, W' i ≤ t'.PP.L.U (k (j i)) := fun i => by
    rw [hkU]; exact mm.φ.preimage_mono (hWj i)
  let z' : ∀ i i' : J, Γ(t'.G.left, W' i ⊓ W' i') := fun i i' => pbT mm.φ (z i i') (W' i ⊓ W' i')
  have hz' : ∀ i i' i'', resG t'.G.left (inf_le_left : W' i ⊓ W' i' ⊓ W' i'' ≤ W' i ⊓ W' i') (z' i i') +
      resG t'.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W' i ⊓ W' i' ⊓ W' i'' ≤ W' i' ⊓ W' i'')
        (z' i' i'') =
      resG t'.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W' i ⊓ W' i' ⊓ W' i'' ≤ W' i ⊓ W' i'')
        (z' i i'') := by
    intro i i' i''
    have hT : W' i ⊓ W' i' ⊓ W' i'' ≤ mm.φ ⁻¹ᵁ (W i ⊓ W i' ⊓ W i'') := le_rfl
    have key := congrArg (fun s => pbT mm.φ s (W' i ⊓ W' i' ⊓ W' i'')) (hz i i' i'')
    simp only [pbT_add] at key
    rw [pbT_rsT _ (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') hT,
      pbT_rsT _ (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') hT,
      pbT_rsT _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') hT] at key
    simp only [z', ← rsT_of_le]
    rw [rsT_pbT mm.φ (le_rfl : W' i ⊓ W' i' ≤ mm.φ ⁻¹ᵁ (W i ⊓ W i')) inf_le_left,
      rsT_pbT mm.φ (le_rfl : W' i' ⊓ W' i'' ≤ mm.φ ⁻¹ᵁ (W i' ⊓ W i'')) (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
      rsT_pbT mm.φ (le_rfl : W' i ⊓ W' i'' ≤ mm.φ ⁻¹ᵁ (W i ⊓ W i'')) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)]
    exact key
  have hF3 : ∀ a (O : t'.G.left.Opens), O ≤ t'.G.hom ⁻¹ᵁ U'.1 → ∀ (f : Γ(t'.G.left, O)) (S : Type) [CommRing S]
      (φ : Γ(Sp Γ(Sp R, U.1), U'.1) →+* S) (g₀ : Sp S ⟶ t'.G.left) (w : Sp (DualNumber S) ⟶ t'.G.left),
      g₀ ≫ t'.G.hom = spMap φ ≫ chart U' → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t' φ g₀ (v a) w →
      valR g₀ O (δ a O f) = (valR w O f).snd := by
    intro a O hO f S _ φ g₀ w hg hO₀ hT
    have hpi : O ≤ mm.φ ⁻¹ᵁ (mm.φ ''ᵁ O) := (mm.φ.preimage_image_eq O).ge
    obtain ⟨f₁, rfl⟩ := (GlobalTheory.KSOpen.bijective_appLE mm.φ (rfl : mm.φ ''ᵁ O = mm.φ ''ᵁ O) hpi).2 f
    rw [hδ a _ O hpi f₁]
    have hw₀ : ⊤ ≤ w ⁻¹ᵁ O := GlobalTheory.CechKS.le_preimage_of_red
      (GlobalTheory.LogKS.IsTranslate.fst_comp E H _ t' _ S φ (chart U') g₀ (v a) w hg (hvt a) hT) hO₀
    rw [← GlobalTheory.KSOpen.valR_comp_appLE g₀ mm.φ hpi hO₀, ← GlobalTheory.KSOpen.valR_comp_appLE w mm.φ hpi hw₀]
    have hTr : IsTr t.G ((φ.comp ψ.toRingHom).comp ρ) (g₀ ≫ mm.φ) (v' a) (w ≫ mm.φ) := by
      obtain ⟨g', v'', h₁, h₂, h₃⟩ := isTranslate_push mm ψ.toRingHom _ (v a) (hvv a) φ g₀ w hT
      exact ⟨g', v'', h₁, by rw [h₂, ← Category.assoc, GlobalTheory.TransLift.spMap_comp'', GlobalTheory.TransLift.dualMap_comp''], h₃⟩
    have hgg : (g₀ ≫ mm.φ) ≫ t.G.hom = spMap ((φ.comp ψ.toRingHom).comp ρ) := by
      rw [Category.assoc, sq, ← Category.assoc, hg, Category.assoc, hch, ← hcU, Category.comp_id, ← Category.assoc,
        GlobalTheory.TransLift.spMap_comp'', GlobalTheory.TransLift.spMap_comp'']
    exact ((hinv a).2 S _ (g₀ ≫ mm.φ) (w ≫ mm.φ) _ f₁ hgg (fun p hp => hpi (hO₀ hp)) hTr).symm
  have hF2 : ∀ a (O : t'.G.left.Opens) (h : O ≤ t'.G.hom ⁻¹ᵁ U'.1) (r : Γ(Sp Γ(Sp R, U.1), U'.1)),
      δ a O ((t'.G.hom.appLE U'.1 O h).hom r) = 0 := by
    intro a O hO r
    refine GlobalTheory.LogKSBal.ext_valR _ _ fun B _ y hy => ?_
    haveI : IsIso (chart U') := by
      show IsIso (isAffineOpen_top (Sp Γ(Sp R, U.1))).fromSpec
      rw [IsAffineOpen.fromSpec_top]
      infer_instance
    obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of Γ(Sp Γ(Sp R, U.1), U'.1)) (S := CommRingCat.of B)
      (y ≫ t'.G.hom ≫ inv (chart U'))
    have hg : y ≫ t'.G.hom = spMap φ'.hom ≫ chart U' := by
      show _ = Spec.map φ' ≫ _
      rw [hφ', Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    obtain ⟨w, hw, -⟩ := existsUnique_isTranslate t' φ'.hom hg (hvt a)
    rw [hF3 a O hO _ B φ'.hom y w hg hy hw]
    have hw₀ : ⊤ ≤ w ⁻¹ᵁ O := GlobalTheory.CechKS.le_preimage_of_red
      (GlobalTheory.LogKS.IsTranslate.fst_comp E H _ t' _ B φ'.hom (chart U') y (v a) w hg (hvt a) hw) hy
    rw [← GlobalTheory.KSOpen.valR_comp_appLE w t'.G.hom hO hw₀]
    have hwb : w ≫ t'.G.hom = spMap ((algebraMap B (DualNumber B)).comp φ'.hom) ≫ chart U' := by
      obtain ⟨g', v'', h₁, -, h₃⟩ := hw
      rw [← h₃, Over.w (g' * v'')]
      show spMap _ ≫ y ≫ t'.G.hom = _
      rw [hg, ← Category.assoc, GlobalTheory.TransLift.spMap_comp'']
    rw [hwb, GlobalTheory.LogKSBal.valR_chart]
    simp [valR, TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨θ, h, hid⟩ := GlobalTheory.T.cechCocycle_eq_coboundary_add_logDerivatives_affine E H _ t' hP hA hK U' n v hvt hvb δ (fun a => ⟨fun O _ => (hδF a).1 O le_top,
    fun O _ => (hδF a).2.1 O le_top, fun O O' hO _ => (hδF a).2.2 O O' hO le_top⟩) hF2 hF3 J W' (fun i => k (j i))
    hW'aff hW'cov hW'U hj' z' hz'
  have hWim : ∀ i, mm.φ ''ᵁ W' i = W i := fun i => by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 (hWr i)]
  choose y hy using fun i => (GlobalTheory.KSOpen.bijective_appLE mm.φ (hWim i) le_rfl).2 (-h i)
  have hkg' : ∀ a b, ((t'.PP.L.g (k a) (k b))⁻¹).val = pbT mm.φ ((t.PP.L.g a b)⁻¹).val
      (t'.PP.L.U (k a) ⊓ t'.PP.L.U (k b)) := fun a b => by
    have hle : t'.PP.L.U (k a) ⊓ t'.PP.L.U (k b) ≤ mm.φ ⁻¹ᵁ (t.PP.L.U a ⊓ t.PP.L.U b) := by
      rw [hkU, hkU]; rfl
    exact Units.inv_eq_of_mul_eq_one_right (by rw [hkg, ← pbT_mul, Units.mul_inv, pbT_one _ hle])
  refine ⟨fun b => ψ.symm (θ b), y, fun i i' => ?_⟩
  have hle : W' i ⊓ W' i' ≤ mm.φ ⁻¹ᵁ (W i ⊓ W i') := le_rfl
  have hWim2 : mm.φ ''ᵁ (W' i ⊓ W' i') = W i ⊓ W i' := by
    show mm.φ ''ᵁ (mm.φ ⁻¹ᵁ (W i ⊓ W i')) = _
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 (inf_le_left.trans (hWr i))]
  apply (GlobalTheory.KSOpen.bijective_appLE mm.φ hWim2 hle).1
  rw [← pbT_of_le mm.φ hle, ← pbT_of_le mm.φ hle]
  have e1 : ∀ l (hl : W i ⊓ W i' ≤ W l) (hl' : W' i ⊓ W' i' ≤ W' l),
      pbT mm.φ (rsT (y l) (W i ⊓ W i')) (W' i ⊓ W' i') = resG t'.G.left hl' (-h l) := fun l hl hl' => by
    rw [pbT_rsT mm.φ hl hle, ← rsT_pbT mm.φ (le_rfl : W' l ≤ mm.φ ⁻¹ᵁ W l) hl', pbT_of_le mm.φ le_rfl, hy,
      rsT_of_le hl']
  have e2 : ∀ b, pbT mm.φ (GlobalTheory.HeatV.cst t.G.hom U.1 (inf_le_left.trans (hW i)) (ψ.symm (θ b))) (W' i ⊓ W' i') =
      (t'.G.hom.appLE U'.1 (W' i ⊓ W' i') (inf_le_left.trans (hW'U i))).hom (θ b) := fun b => by
    rw [pbT_of_le mm.φ hle]
    have := GlobalTheory.KSOpen.app_appLE sq e (inf_le_left.trans (hW i))
      (show mm.φ ⁻¹ᵁ (W i ⊓ W i') ≤ t'.G.hom ⁻¹ᵁ U'.1 from
        (inf_le_left : W' i ⊓ W' i' ≤ W' i).trans (hW'U i)) (ψ.symm (θ b))
    rw [Scheme.Hom.app_eq_appLE] at this
    exact this.trans (congrArg _ (ψ.apply_symm_apply (θ b)))
  have e3 : ∀ b (X : Γ(t.G.left, W i ⊓ W i')), pbT mm.φ (dd' b (W i ⊓ W i') X) (W' i ⊓ W' i') =
      δ b (W' i ⊓ W' i') (pbT mm.φ X (W' i ⊓ W' i')) := fun b X => by
    rw [pbT_of_le mm.φ hle, pbT_of_le mm.φ hle, hδ]
  have hUU : t'.PP.L.U (k (j i)) ⊓ t'.PP.L.U (k (j i')) ≤ mm.φ ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i')) := by
    rw [hkU, hkU]; rfl
  have e4 : pbT mm.φ (rsT (t.PP.L.g (j i) (j i')).val (W i ⊓ W i')) (W' i ⊓ W' i') =
      resG t'.G.left (inf_le_inf (hj' i) (hj' i')) (t'.PP.L.g (k (j i)) (k (j i'))).val := by
    rw [pbT_rsT mm.φ (inf_le_inf (hWj i) (hWj i')) hle, hkg, ← rsT_of_le, rsT_pbT mm.φ hUU (inf_le_inf (hj' i) (hj' i'))]
  have e5 : pbT mm.φ (rsT (t.PP.L.g (j i) (j i'))⁻¹.val (W i ⊓ W i')) (W' i ⊓ W' i') =
      resG t'.G.left (inf_le_inf (hj' i) (hj' i')) (t'.PP.L.g (k (j i)) (k (j i')))⁻¹.val := by
    rw [pbT_rsT mm.φ (inf_le_inf (hWj i) (hWj i')) hle, hkg', ← rsT_of_le, rsT_pbT mm.φ hUU (inf_le_inf (hj' i) (hj' i'))]
  show z' i i' = _
  have hs : pbT mm.φ (∑ b, GlobalTheory.HeatV.cst t.G.hom U.1 (inf_le_left.trans (hW i)) (ψ.symm (θ b)) *
      (dd' b (W i ⊓ W i') (rsT (t.PP.L.g (j i) (j i')).val (W i ⊓ W i')) *
        rsT (t.PP.L.g (j i) (j i'))⁻¹.val (W i ⊓ W i'))) (W' i ⊓ W' i') =
      ∑ b, (t'.G.hom.appLE U'.1 (W' i ⊓ W' i') (inf_le_left.trans (hW'U i))).hom (θ b) *
        (δ b (W' i ⊓ W' i') (resG t'.G.left (inf_le_inf (hj' i) (hj' i')) (t'.PP.L.g (k (j i)) (k (j i'))).val) *
          resG t'.G.left (inf_le_inf (hj' i) (hj' i')) (t'.PP.L.g (k (j i)) (k (j i')))⁻¹.val) := by
    rw [pbT_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [pbT_mul, pbT_mul, e2 b, e3 b, e4, e5]
  rw [hid i i', pbT_add, pbT_sub, e1 i' inf_le_right inf_le_right, e1 i inf_le_left inf_le_left]
  rw [hs, map_neg, map_neg]
  abel

end GlobalTheory.CechAff
