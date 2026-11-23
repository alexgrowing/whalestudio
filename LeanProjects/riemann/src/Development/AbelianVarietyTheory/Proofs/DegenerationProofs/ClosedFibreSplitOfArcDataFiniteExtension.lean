import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsIsoPairOfEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRResidueGaloisAutomorphismsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumMatchLengthSymmPreimagesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusPointWithCharactersIffPullDegStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSplitTorusExtensionDescentGaloisInvariantStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.SplitAtTrait

section Torus

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}

def TorPt {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    {T : Scheme.{0}} (z : T ⟶ (thickObj R I e G).left) {X : Type} (ε : X → D.X) (a : X → Γ(T, ⊤)) : Prop :=
  ∃ τ : T ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left,
    τ ≫ g.i.left = z ∧ ∀ x, τ.appTop.hom (charUnit _ D.X (ε x)).val = a x

omit [IsDomain R] in
theorem mono_fstG (e : ℕ) (G : Over (Spec (CommRingCat.of R))) : Mono (fstG I e G).left := by
  have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact inferInstanceAs (Mono (pullback.fst G.hom (thick R I e)))

theorem pull_rel {φ : R →+* R'} {D : DegData R I} {D' : DegData R' I'} {hD : IsPullDeg φ D.toPre D'.toPre}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G} {U : Unif I D A G} {U' : Unif I' D' A' G'}
    (hU : IsPullUnif φ hD bc U U') (e : ℕ) {X : Type} (ε : X → D.toPre.X) (ε' : X ≃ D'.toPre.X)
    (hε : ∀ x, hD.xe (ε' x) = ε x) {T : Scheme.{0}} (z' : T ⟶ (thickObj R' I' e G').left)
    (z : T ⟶ (thickObj R I e G).left)
    (hz : z' ≫ (fstG I' e G').left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = z ≫ (fstG I e G).left) :
    z' ≫ (U'.gt e).pG.left ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ) = z ≫ (U.gt e).pG.left ∧
      ∀ a, TorPt (U'.gt e) z' ε' a ↔ TorPt (U.gt e) z ε a := by
  obtain ⟨_, _, _, _, lev⟩ := hU.lg
  obtain ⟨h, h₁, h₂, h₃, -⟩ := lev e
  have := mono_fstG (I := I) e G
  obtain rfl : z' ≫ h = z := by
    rw [← cancel_mono (fstG I e G).left, Category.assoc, h₁, hz]
  refine ⟨by rw [h₂, Category.assoc], fun a => ?_⟩
  have key := GlobalTheory.T.torusPoint_with_characters_iff_pullDeg R R' I I' φ D.toPre D'.toPre hD G G' e (U.gt e) (U'.gt e) h h₂ h₃ T z' (fun x => a (ε'.symm x))
  constructor
  · rintro ⟨τ, hτ, ha⟩
    obtain ⟨τ₁, k₁, k₂⟩ := key.1 ⟨τ, hτ, fun x => by rw [← ha, Equiv.apply_symm_apply]⟩
    exact ⟨τ₁, k₁, fun x => by rw [← hε, k₂, Equiv.symm_apply_apply]⟩
  · rintro ⟨τ, hτ, ha⟩
    obtain ⟨τ₁, k₁, k₂⟩ := key.2 ⟨τ, hτ, fun x => by rw [← ha, ← hε, Equiv.apply_symm_apply]⟩
    exact ⟨τ₁, k₁, fun x => by rw [k₂, Equiv.symm_apply_apply]⟩

end Torus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {W₀ : ValuationSubring ℂ}
  {Y : Model Xo c (c.V W₀).subtype} {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O'] {b : c.V W₀ →+* O'}
  {a : ArcIn D l (c.V W₀).subtype O' b}

set_option maxHeartbeats 3200000 in

theorem same_rel (hL : Laws) (h2 : Laws2) (h4 : Laws4) (h5 : Laws5) (h6 : Laws6) {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {I : Ideal R} (hadm : AdmBase R I) {f : O' →+* R} {u : R}
    (hf : ∀ x, x ≠ 0 → IsUnit (f x)) (hu' : ¬ IsUnit u) {χ : Sp R ⟶ Y.X} (W W' : ArcWit Y a I f u χ)
    (y : Sp (FractionRing R) ⟶ Xo.XF c) (hy : y ≫ Y.j = jK R ≫ χ) (e : ℕ) {T : Scheme.{0}}
    (z : T ⟶ (thickObj R I e W.t.G).left) (z' : T ⟶ (thickObj R I e W'.t.G).left)
    (hz₁ : z ≫ (fstG I e W.t.G).left ≫ W.m.φ = z' ≫ (fstG I e W'.t.G).left ≫ W'.m.φ)
    (hz₂ : z ≫ (fstG I e W.t.G).left ≫ W.t.G.hom = z' ≫ (fstG I e W'.t.G).left ≫ W'.t.G.hom) :
    z ≫ (W.P.U.gt e).pG.left ≫ W.φ = z' ≫ (W'.P.U.gt e).pG.left ≫ W'.φ ∧
      ∀ s, TorPt (W.P.U.gt e) z W.e s ↔ TorPt (W'.P.U.gt e) z' W'.e s := by
  letI := H.starRing
  have hs := specOf_id R
  have hQ := qkPullExists hL.globalFns
  have hfi : Function.Injective f := (injective_iff_map_eq_zero f).2 fun x hx => by
    by_contra h0
    exact not_isUnit_zero (hx ▸ hf x h0)
  obtain ⟨ψ, hφ, hψ, hact, -⟩ := ArcWit.uwIso W W'
  obtain ⟨bc, D'', hD₂, U'', mod'', oD'', mbc, hbc, hLG, -, hPU₂, xl₂, el₂, lin'', -⟩ :=
    ArcWit.uwMove h4.unifBaseChange h5 hadm W W' ψ hφ hact
  obtain ⟨wL₀, -, g₀, -, m₀, -, -⟩ := exists_iso_pair_of_eq hLG
  obtain ⟨hD₁, hlev, holin⟩ := h6.unifUniq R I hadm W.P.D D'' W.P.A W'.P.A W.t.G W.t.semi W.P.U U'' wL₀ g₀ m₀
  obtain ⟨xl₁, el₁⟩ := holin (𝓞 E) W.P.oD oD'' W.P.oA W'.P.oA W.t.act.toRingAct W.P.lin lin''
  have mR : IsMonHom (Iso.refl W.t.G).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨bc₀, mbc₀, hbc₀⟩ := grpPullback_iso ((isGrpPullback_of_iso (Iso.refl W.t.G)).congr hs.symm rfl)
    (isGrpPullback_pullback W.t.G (specOf (RingHom.id R)))
  have hbc₀' : bc₀.hom.left ≫ pullback.fst W.t.G.hom (specOf (RingHom.id R)) = 𝟙 _ := hbc₀
  have hPU₁ := isPullUnif_of_uniq W.P.U U'' hD₁ wL₀ g₀ m₀ hlev bc₀ hbc₀'
  obtain ⟨he₁, w₁, e₁, hxe₁, -, d1, d2, d3, d4, d5, d6⟩ :=
    ArcWit.witMove h5 hQ hadm W U'' oD'' bc₀ hD₁ hPU₁ xl₁ el₁
  obtain ⟨he₂, w₂, e₂, hxe₂, -, d1', d2', d3', d4', d5', d6'⟩ :=
    ArcWit.witMove h5 hQ hadm W' U'' oD'' bc hD₂ hPU₂ xl₂ el₂
  have M₁ : Match a f u D''.toPre oD'' _ he₁ w₁ e₁ :=
    ⟨d1, d2, d3, d4, d5, fun F _ _ _ _ uF h1 h2 => (d6 F uF h1 h2).1⟩
  have M₂ : Match a f u D''.toPre oD'' _ he₂ w₂ e₂ :=
    ⟨d1', d2', d3', d4', d5', fun F _ _ _ _ uF h1 h2 => (d6' F uF h1 h2).1⟩
  obtain ⟨hφe, hee, -⟩ := GlobalTheory.MatchRigid.rigid hL h2 E H D l c W₀ O' b a R f u hfi D''.toPre oD'' _ _ he₁ he₂ w₁ w₂ e₁ e₂
    D''.tau_bimult M₁ M₂ (GlobalTheory.T.arcDatumMatch_length_symm_preimages E H D l c _ _ O' b a R f u hf hu' D''.toPre oD'' _ _ he₁ he₂ w₁ w₂ e₁ e₂ M₁ M₂)
    (fun F _ _ _ _ uF hF hu v hv q₀ q₁ q₂ hq₀ hy₁ hy₂ hg₁ hg₂ => by
      have hn : 1 ≤ l.M := le_trans (by norm_num) l.three_le
      have hσ : (l.M = l.A ∧ ∃ v', HEq (a.eta v) (a.etaA v') ∧ Y.oF.eta v = Y.oF.etaA v') ∨
          (l.M = l.M ∧ ∃ v' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
            HEq (a.eta v) (a.eta v') ∧ Y.oF.eta v = Y.oF.eta v') := Or.inr ⟨rfl, v, hv, HEq.rfl, rfl⟩
      have hyF : (jFK (R := R) F ≫ y) ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ := by
        rw [Category.assoc, hy]
      have hσw : (Y.oF.eta v).left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w (Y.oF.eta v)
      have hmw : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.jQ ≫ pullback.fst _ _ := Y.m.cart.1.w
      have hc0 : ((jFK (R := R) F ≫ y) ≫ (Y.oF.eta v).left ≫ Y.m.φ) ≫ Y.t.G.hom = (jFK (R := R) F ≫ jK R) ≫ χ := by
        simp only [Category.assoc]
        rw [hmw, reassoc_of% hσw]
        simpa only [Category.assoc, Model.j] using hyF
      have hz₀ := W.m.cart.1.lift_fst _ _ hc0
      have hz₀' := W.m.cart.1.lift_snd _ _ hc0
      let z₁ : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj W.t.G :=
        Over.homMk (pullback.lift _ (jFK (R := R) F) hz₀') (pullback.lift_snd _ _ _)
      let x'' : TFK (R := R) F ⟶ W'.P.A.A := z₁ ≫ U''.gen.hom
      have hx₀ : x''.left ≫ U''.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R) = W.m.cart.1.lift _ _ hc0 := by
        have hgi : U''.gen.hom.left ≫ U''.gen.inv.left = 𝟙 _ := by
          rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
        show (z₁.left ≫ U''.gen.hom.left) ≫ _ = _
        rw [Category.assoc, ← Category.assoc U''.gen.hom.left, hgi, Category.id_comp]
        exact pullback.lift_fst _ _ _
      have A1 := (d6 F uF hF hu).2 _ hyF l.M _ _ hσ q₀ q₁ x'' hq₀ hy₁ hg₁ (by
        rw [show x''.left ≫ U''.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R) ≫ bc₀.hom.left ≫
            pullback.fst W.t.G.hom (specOf (RingHom.id R)) ≫ W.m.φ =
            (x''.left ≫ U''.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R)) ≫
              (bc₀.hom.left ≫ pullback.fst W.t.G.hom (specOf (RingHom.id R))) ≫ W.m.φ by
            simp only [Category.assoc], hx₀, hbc₀', Category.id_comp, hz₀])
      have A2 := (d6' F uF hF hu).2 _ hyF l.M _ _ hσ q₀ q₂ x'' hq₀ hy₂ hg₂ (by
        rw [show x''.left ≫ U''.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R) ≫ bc.hom.left ≫
            pullback.fst W'.t.G.hom (specOf (RingHom.id R)) ≫ W'.m.φ =
            (x''.left ≫ U''.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R)) ≫
              (bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id R))) ≫ W'.m.φ by
            simp only [Category.assoc], hx₀, hbc, hφ, hz₀])
      exact GlobalTheory.TorsionMapInj.qkToAk_injective hL h2 R _ hadm D'' W'.P.A W.t.G W.t.semi U'' F l.M hn q₁ q₂ x'' A1 A2)
  subst hee
  have hzψ : z ≫ (fstG I e W.t.G).left ≫ ψ.hom.left = z' ≫ (fstG I e W'.t.G).left := by
    apply W'.m.cart.1.hom_ext
    · have hφ' : ψ.hom.left ≫ W'.m.cm.F = W.m.φ := hφ
      simp only [Category.assoc, hφ']; exact hz₁
    · simp only [Category.assoc, Over.w ψ.hom]; exact hz₂
  obtain ⟨a₁, b₁⟩ := pull_rel hPU₁ e W.e e₁.toEquiv hxe₁ z z (by rw [hbc₀']; exact congrArg _ (Category.comp_id _))
  obtain ⟨a₂, b₂⟩ := pull_rel hPU₂ e W'.e e₁.toEquiv hxe₂ z z' (by rw [hbc]; exact hzψ)
  refine ⟨?_, fun s => (b₁ s).symm.trans (b₂ s)⟩
  have k := congrArg (z ≫ (U''.gt e).pG.left ≫ ·) hφe
  simp only [Category.assoc] at k
  rw [← reassoc_of% a₁, ← reassoc_of% a₂]
  exact k

theorem bc_rel (hL : Laws) (h2 : Laws2) (h3 : Laws3) (h4 : Laws4) (h5 : Laws5) (h6 : Laws6) {R R' : Type} [CommRing R]
    [IsDomain R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} {f' : O' →+* R'} {u' : R'}
    {χ' : Sp R' ⟶ Y.X} (hf : ∀ x, x ≠ 0 → IsUnit (f' x)) (hu : ¬ IsUnit u') (g : R →+* R') (hg : Function.Injective g)
    (hI : I.map g ≤ I') (e₁ : f' = g.comp f) (e₂ : u' = g u) (e₃ : χ' = spMap g ≫ χ) (W : ArcWit Y a I f u χ)
    (W' : ArcWit Y a I' f' u' χ') (y : Sp (FractionRing R') ⟶ Xo.XF c) (hy : y ≫ Y.j = jK R' ≫ χ') (e : ℕ)
    {T : Scheme.{0}} (z' : T ⟶ (thickObj R' I' e W'.t.G).left) (z : T ⟶ (thickObj R I e W.t.G).left)
    (hz₁ : z' ≫ (fstG I' e W'.t.G).left ≫ W'.m.φ = z ≫ (fstG I e W.t.G).left ≫ W.m.φ)
    (hz₂ : z' ≫ (fstG I' e W'.t.G).left ≫ W'.t.G.hom ≫ spMap g = z ≫ (fstG I e W.t.G).left ≫ W.t.G.hom) :
    z' ≫ (W'.P.U.gt e).pG.left ≫ W'.φ = z ≫ (W.P.U.gt e).pG.left ≫ W.φ ∧
      ∀ s, TorPt (W'.P.U.gt e) z' W'.e s ↔ TorPt (W.P.U.gt e) z W.e s := by
  subst e₁ e₂ e₃
  obtain ⟨W₁, hD, bc, -, hPU, hm, hxe, -, hφ₁, -, -⟩ := ArcWit.baseChange h3.cubePull hL.polBaseChange
    h4.unifBaseChange h5 (qkPullExists hL.globalFns) polOActPull hR hR' W g hg hI
  obtain ⟨ψ, hφ, -⟩ := ArcWit.uwIso W' W₁
  let z₁ : T ⟶ (thickObj R' I' e W₁.t.G).left := z' ≫ ((Over.pullback (thick R' I' e)).map ψ.hom).left
  have k₀ : ((Over.pullback (thick R' I' e)).map ψ.hom).left ≫ (fstG I' e W₁.t.G).left =
      (fstG I' e W'.t.G).left ≫ ψ.hom.left := pullback.lift_fst _ _ _
  have k₁ : z₁ ≫ (fstG I' e W₁.t.G).left = z' ≫ (fstG I' e W'.t.G).left ≫ ψ.hom.left := by
    rw [← k₀]; exact Category.assoc _ _ _
  obtain ⟨a₁, b₁⟩ := same_rel hL h2 h4 h5 h6 hR' hf hu W' W₁ y hy e z' z₁
    (by rw [reassoc_of% k₁, hφ]) (by rw [reassoc_of% k₁, Over.w ψ.hom])
  obtain ⟨a₂, b₂⟩ := pull_rel hPU e W.e W₁.e.toEquiv hxe z₁ z (by
    apply W.m.cart.1.hom_ext
    · have hm' : bc.hom.left ≫ pullback.fst W.t.G.hom (specOf g) ≫ W.m.cm.F = W₁.m.φ := by
        rw [hm, Category.assoc]
      simp only [Category.assoc]
      rw [hm', reassoc_of% k₁, hφ]; exact hz₁
    · have w₁ : bc.hom.left ≫ pullback.snd W.t.G.hom (specOf g) = W₁.t.G.hom := Over.w bc.hom
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% w₁, reassoc_of% k₁, reassoc_of% (Over.w ψ.hom)]; exact hz₂)
  refine ⟨?_, fun s => (b₁ s).trans (b₂ s)⟩
  rw [a₁, hφ₁, ← reassoc_of% a₂]
  simp only [Category.assoc]

theorem torus_ext {S T : Scheme.{0}} {X : Type} [AddCommGroup X] (τ τ' : T ⟶ (splitTorus S X).left)
    (h₁ : τ ≫ (splitTorus S X).hom = τ' ≫ (splitTorus S X).hom)
    (h₂ : ∀ x, τ.appTop.hom (charUnit S X x).val = τ'.appTop.hom (charUnit S X x).val) : τ = τ' := by
  have := GlobalTheory.SplitTorus.hom_ext (T := Over.mk (τ ≫ (splitTorus S X).hom)) (g := Over.homMk τ rfl)
    (g' := Over.homMk τ' h₁.symm) (fun x => by
      rw [GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val]; exact h₂ x)
  exact congrArg (·.left) this

set_option maxHeartbeats 1600000 in

theorem split_of_galois (hL : Laws) (h2 : Laws2) (h3 : Laws3) (h4 : Laws4) (h5 : Laws5) (h6 : Laws6) {V R : Type}
    [CommRing V] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {I : Ideal R} (hR : AdmBase R I)
    (hI : I = IsLocalRing.maximalIdeal R) (f : O' →+* V) (u : V) (χ : Sp V ⟶ Y.X) (t : SAB H (Sp V))
    (m : SABMap t Y.t χ) (g : V →+* R) (hf : ∀ x, x ≠ 0 → IsUnit (g (f x))) (hu : ¬ IsUnit (g u))
    (W : ArcWit Y a I (g.comp f) (g u) (spMap g ≫ χ)) (y : Sp (FractionRing R) ⟶ Xo.XF c)
    (hy : y ≫ Y.j = jK R ≫ spMap g ≫ χ) (k : Type) [Field k] (p : V →+* k) [(I ^ (0 + 1)).IsMaximal]
    (α : k →+* R ⧸ I ^ (0 + 1)) (hα : α.comp p = (Ideal.Quotient.mk _).comp g)
    (hG : letI := Ideal.Quotient.field (I ^ (0 + 1)); letI := α.toAlgebra
      FiniteDimensional k (R ⧸ I ^ (0 + 1)) ∧ IsGalois k (R ⧸ I ^ (0 + 1)) ∧
        ∀ τ : (R ⧸ I ^ (0 + 1)) ≃ₐ[k] (R ⧸ I ^ (0 + 1)), ∃ σ : R ≃+* R, (∀ x, σ (g x) = g x) ∧
          ∀ x, Ideal.Quotient.mk _ (σ x) = τ (Ideal.Quotient.mk _ x)) :
    ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (spMap p)).obj t.G) := by
  letI := Ideal.Quotient.field (I ^ (0 + 1))
  letI := α.toAlgebra
  obtain ⟨hfin, hgal, haut⟩ := hG
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m W.m
  have sq : thick R I 0 ≫ spMap g = spMap α ≫ spMap p :=
    (spMap_comp g _).symm.trans ((congrArg spMap hα.symm).trans (spMap_comp p α))
  have sq' : thick R I 0 ≫ spMap (g.comp f) = spMap α ≫ spMap (p.comp f) := by
    rw [spMap_comp, spMap_comp, reassoc_of% sq]
  have gG : IsGrpPullback (thickObj R I 0 W.t.G) t.G (spMap α ≫ spMap p) ((fstG I 0 W.t.G).left ≫ n.φ) :=
    ((isGrpPullback_pullback W.t.G (thick R I 0)).comp n.cart).congr sq rfl
  have gB : IsGrpPullback (thickObj R I 0 W.P.D.toPre.P.A) a.D₀.P.A (spMap α ≫ spMap (p.comp f))
      (pullback.fst W.P.D.toPre.P.A.hom (thick R I 0) ≫ W.φ) :=
    ((isGrpPullback_pullback W.P.D.toPre.P.A (thick R I 0)).comp W.spec.1).congr sq' rfl
  obtain ⟨φG, G₁, G₂⟩ : ∃ φG : (thickObj R I 0 W.t.G).left ⟶ ((Over.pullback (spMap p)).obj t.G).left,
      φG ≫ pullback.fst t.G.hom (spMap p) = (fstG I 0 W.t.G).left ≫ n.φ ∧
      φG ≫ ((Over.pullback (spMap p)).obj t.G).hom = (thickObj R I 0 W.t.G).hom ≫ spMap α :=
    ⟨pullback.lift _ _ (gG.1.w.trans (Category.assoc _ _ _).symm), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨φB, B₁, B₂⟩ : ∃ φB : (thickObj R I 0 W.P.D.toPre.P.A).left ⟶
      ((Over.pullback (spMap (p.comp f))).obj a.D₀.P.A).left,
      φB ≫ pullback.fst a.D₀.P.A.hom (spMap (p.comp f)) = pullback.fst W.P.D.toPre.P.A.hom (thick R I 0) ≫ W.φ ∧
      φB ≫ ((Over.pullback (spMap (p.comp f))).obj a.D₀.P.A).hom =
        (thickObj R I 0 W.P.D.toPre.P.A).hom ≫ spMap α :=
    ⟨pullback.lift _ _ (gB.1.w.trans (Category.assoc _ _ _).symm), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have haff := (W.P.U.gt 0).q_affine
  refine GlobalTheory.T.exists_splitTorusExtension_descent_galois_invariant k (R ⧸ I ^ (0 + 1)) ((Over.pullback (spMap p)).obj t.G)
    ((Over.pullback (spMap (p.comp f))).obj a.D₀.P.A) (GlobalTheory.isAbelianScheme_pullback_obj _ _ a.D₀.P.isAb)
    (thickObj R I 0 W.t.G) (thickObj R I 0 W.P.D.toPre.P.A) W.P.D.toPre.X φG φB
    ((isGrpPullback_pullback t.G (spMap p)).cancel (gG.congr rfl G₁.symm) G₂)
    ((isGrpPullback_pullback a.D₀.P.A (spMap (p.comp f))).cancel (gB.congr rfl B₁.symm) B₂)
    (W.P.U.gt 0).q (W.P.U.gt 0).i (W.P.U.gt 0).q_hom (W.P.U.gt 0).q_flat (W.P.U.gt 0).q_surj inferInstance
    (W.P.U.gt 0).i_hom (W.P.U.gt 0).isKernel (fun τ s s₁ s₂ => ?_)
  obtain ⟨σ, σ₁, σ₂⟩ := haut τ
  have σg : (σ : R →+* R).comp g = g := RingHom.ext σ₁
  have σI : I.map (σ : R →+* R) ≤ I := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro x hx
    exact (map_mem_nonunits_iff (σ : R →+* R) x).2 hx
  have σt : thick R I 0 ≫ spMap (σ : R →+* R) = spMap (τ : _ →+* _) ≫ thick R I 0 :=
    (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext σ₂)).trans (spMap_comp _ _))
  have τα : spMap (τ : _ →+* _) ≫ spMap α = spMap α :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext τ.commutes))
  have c₀ : (fstG I 0 W.t.G).left ≫ W.t.G.hom = (thickObj R I 0 W.t.G).hom ≫ thick R I 0 := pullback.condition
  have rel := fun (T : Scheme.{0}) (z : T ⟶ (thickObj R I 0 W.t.G).left) =>
    bc_rel hL h2 h3 h4 h5 h6 hR hR hf hu (σ : R →+* R) σ.injective σI
      (by rw [← RingHom.comp_assoc, σg]) (σ₁ u).symm (by rw [← Category.assoc, ← spMap_comp, σg]) W W y hy 0 z (z ≫ s)
      (by rw [hn, ← reassoc_of% G₁, Category.assoc, reassoc_of% s₁])
      (by rw [reassoc_of% c₀, σt, c₀, Category.assoc, reassoc_of% s₂])
  have pq : (W.P.U.gt 0).pG.left = (W.P.U.gt 0).q.left ≫ pullback.fst W.P.D.toPre.P.A.hom (thick R I 0) := rfl
  constructor
  · apply pullback.hom_ext
    · have r₁ := (rel _ (𝟙 _)).1
      rw [Category.id_comp, Category.id_comp, pq] at r₁
      simp only [Category.assoc] at r₁ ⊢
      rw [B₁]; exact r₁.symm
    · have wq : (W.P.U.gt 0).q.left ≫ (thickObj R I 0 W.P.D.toPre.P.A).hom = (thickObj R I 0 W.t.G).hom :=
        Over.w _
      have B₂' : φB ≫ pullback.snd a.D₀.P.A.hom (spMap (p.comp f)) =
        (thickObj R I 0 W.P.D.toPre.P.A).hom ≫ spMap α := B₂
      simp only [Category.assoc]
      rw [B₂', reassoc_of% wq, reassoc_of% s₂, τα]
  · obtain ⟨τ₁, k₁, k₂⟩ := ((rel _ (W.P.U.gt 0).i.left).2 (fun x => (charUnit _ _ (W.e x)).val)).1
      ⟨𝟙 _, Category.id_comp _, fun x => by rw [Scheme.Hom.id_appTop]; rfl⟩
    rw [← k₁]
    congr 1
    have wi : (W.P.U.gt 0).i.left ≫ (thickObj R I 0 W.t.G).hom = (splitTorus _ W.P.D.toPre.X).hom := Over.w _
    refine torus_ext _ _ ?_ fun x => ?_
    · rw [GlobalTheory.SplitTorus.bcMap_hom, ← wi, reassoc_of% k₁, s₂, Category.assoc]
    · obtain ⟨x, rfl⟩ := W.e.surjective x
      refine Eq.trans ?_ (k₂ x).symm
      beta_reduce
      rw [GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.bcMap_appTop_chi]

theorem splitOver_of_hasArcData : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (f : O' →+* V) (u : V), (∀ x, x ≠ 0 → IsUnit (f x)) → ¬ IsUnit u → ∀ (χ : Sp V ⟶ Y.X) (y : Sp (FractionRing V) ⟶ Xo.XF c), y ≫ Y.j = jK V ≫ χ → ∀ (t : SAB H (Sp V)) (_ : SABMap t Y.t χ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'], CDvr V' → ∀ g : V →+* V', Function.Injective g → g.Finite → Y.HasArcData a (IsLocalRing.maximalIdeal V') (g.comp f) (g u) (spMap g ≫ χ) → SplitOver t.G (IsLocalRing.maximalIdeal V) := by
  intro hL h2 h3 h4 h5 h6 E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a V _ _ _ hV f u hf hu χ y hy t m V' _ _ _ hV' g hg hfin hA
  obtain ⟨W'⟩ := (Y.hasArcData_iff a _ _ _ _).1 hA
  obtain ⟨R, _, _, _, j, hR, hj, hjI, hgI, hG⟩ := GlobalTheory.T.exists_completeDVR_residue_galois_automorphisms V V' hV hV'
    (fun n hn => by rw [← map_natCast f]; exact hf _ (Nat.cast_ne_zero.2 hn)) g hg hfin
  have := hR.1
  have := hV'.1
  have aR : AdmBase R (IsLocalRing.maximalIdeal R) := ⟨inferInstance, inferInstance, inferInstance, hR.2.1⟩
  have aV : AdmBase V' (IsLocalRing.maximalIdeal V') := ⟨inferInstance, inferInstance, inferInstance, hV'.2.1⟩
  obtain ⟨W₁, -⟩ := ArcWit.baseChange h3.cubePull hL.polBaseChange h4.unifBaseChange h5 (qkPullExists hL.globalFns)
    polOActPull aV aR W' j hj hjI
  have W : ArcWit Y a (IsLocalRing.maximalIdeal R) ((j.comp g).comp f) ((j.comp g) u) (spMap (j.comp g) ≫ χ) := by
    rw [spMap_comp, Category.assoc]; exact W₁
  let gam : FractionRing V →+* FractionRing R :=
    IsFractionRing.lift (g := (algebraMap R (FractionRing R)).comp (j.comp g))
      ((IsFractionRing.injective R _).comp (hj.comp hg))
  have hgam : ∀ r, gam (algebraMap V _ r) = algebraMap R _ (j.comp g r) := fun r => IsFractionRing.lift_algebraMap _ r
  have sq : spMap gam ≫ jK V = jK R ≫ spMap (j.comp g) :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp (j.comp g) _))
  have hp : IsLocalRing.maximalIdeal R ^ (0 + 1) = IsLocalRing.maximalIdeal R := pow_one _
  haveI : (IsLocalRing.maximalIdeal R ^ (0 + 1)).IsMaximal := by rw [hp]; infer_instance
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V)
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal R ^ (0 + 1))
  let α : V ⧸ IsLocalRing.maximalIdeal V →+* R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1) :=
    Ideal.quotientMap _ (j.comp g) (by rw [hp]; exact Ideal.map_le_iff_le_comap.1 hgI)
  letI := α.toAlgebra
  have hG' := hG (V ⧸ IsLocalRing.maximalIdeal V) (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) (Ideal.Quotient.mk _)
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective (fun _ => rfl)
  exact split_of_galois hL h2 h3 h4 h5 h6 aR rfl f u χ t m (j.comp g) (fun x hx => (hf x hx).map _)
    (Ideal.map_le_iff_le_comap.1 hgI hu) W (spMap gam ≫ y) (by rw [Category.assoc, hy, reassoc_of% sq])
    (V ⧸ IsLocalRing.maximalIdeal V) (Ideal.Quotient.mk _) α (Ideal.quotientMap_comp_mk _) hG'

end GlobalTheory.SplitAtTrait
