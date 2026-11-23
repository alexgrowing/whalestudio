import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrameOfFreeSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataPsiValuationEqHalfForm
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.ArcOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem eval_natMul (φ : InvFun (𝓞 E))
    (hφ : ∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (k : ℕ) (B : X → X → ℝ) :
    φ.eval X (fun a b => k * B a b) = k * φ.eval X B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  rw [φ.eval_eq hr, φ.eval_eq hr]
  exact hφ n k _

theorem exists_sabMap_of_generic {O O₂ : Type} [CommRing O] [CommRing O₂] {β : O →+* c.F} {β₂ : O₂ →+* c.F}
    (Z : Model Xo c β) (Y : Model Xo c β₂) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V)
    (y : Sp (FractionRing V) ⟶ Xo.XF c) (χ : Sp V ⟶ Z.X) (χ' : Sp V ⟶ Y.X) (hZ : jK V ≫ χ = y ≫ Z.j)
    (hY : jK V ≫ χ' = y ≫ Y.j) {t₁ : SAB H (Sp V)} (m₁ : SABMap t₁ Y.t χ') : Nonempty (SABMap t₁ Z.t χ) := by
  have := hV.1
  obtain ⟨tZ, ⟨mZ⟩⟩ := GlobalTheory.TraitOrder.exists_pull χ Z.t
  obtain ⟨u, ⟨n₀⟩⟩ := GlobalTheory.TraitOrder.exists_pull y Z.oF.t
  obtain ⟨a₁⟩ := GlobalTheory.TraitOrder.comp hZ.symm (show SABMap Z.oF.t Z.t Z.j from Z.m) n₀
  obtain ⟨a₂⟩ := GlobalTheory.TraitOrder.cancel rfl mZ a₁
  obtain ⟨n₁⟩ := GlobalTheory.TraitOrder.comp rfl Z.m0.toSABMap n₀
  obtain ⟨n₂⟩ := GlobalTheory.TraitOrder.cancel rfl Y.m0.toSABMap n₁
  obtain ⟨n₃⟩ := GlobalTheory.TraitOrder.comp hY.symm (show SABMap Y.oF.t Y.t Y.j from Y.m) n₂
  obtain ⟨b₂⟩ := GlobalTheory.TraitOrder.cancel rfl m₁ n₃
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H V hV.2.1 t₁ tZ u
    (MorphismProperty.of_isPullback (P := @IsProper) n₀.cart.1 Z.oF.proper) b₂ a₂
  exact GlobalTheory.TraitOrder.comp (Category.id_comp χ) mZ ψ

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.Ex GlobalTheory.OneBasis in

theorem q_eq {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    {a : ArcIn D l β O' b} {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {f : O' →+* W} {u : W}
    {χ : Sp W ⟶ Y.X} (hfi : Function.Injective f) (A : ArcWit Y a (maximalIdeal W) f u χ) {ϖ : W} (hϖ : Irreducible ϖ)
    {Q : A.P.D.toPre.X → ℤ} {n : ℕ} (hQ : QForm.IsQ A.P.D.toPre ϖ Q) (hu : HasVal ϖ (algebraMap W (FractionRing W) u) n)
    (y : a.D₀.X) : Q (A.e y) = n * (a.be y y / 2) := by
  obtain ⟨-, -, -, -, hc, hG⟩ := A.spec
  let F := AlgebraicClosure (FractionRing W)
  let g : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective _ _)
  have hgf : Function.Injective (g.comp f) := hg.comp hfi
  let alg : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hgf).toAlgebra
  have hF : ∀ x, @algebraMap (FractionRing O') F _ _ alg (algebraMap O' _ x) =
      algebraMap (FractionRing W) F (algebraMap W _ (f x)) := fun x =>
    IsFractionRing.lift_algebraMap hgf x
  have z : Sp F := (default : PrimeSpectrum F)
  obtain ⟨j, hj⟩ := exists_chart A.P.D.toPre.P.isLB ((A.P.D.toPre.c (A.e y)).left (cpt W))
  obtain ⟨v, hv⟩ := GlobalTheory.ArcPsiVal.psi_value a f u A.P.D.toPre A.φ A.w y (A.e y) (hc y) F hF ((hG F _ hF rfl).1 y) z j hj
  obtain ⟨d, hd, hd'⟩ := GlobalTheory.ArcPsiVal.value_of_qVal A.P.D.toPre ϖ (A.e y) _ (hQ (A.e y)) F z j hj
  have e1 := (toStk z).injective (hd'.symm.trans hv)
  rw [← map_zpow₀, ← map_mul] at e1
  have e2 := (algebraMap (FractionRing W) F).injective e1
  obtain ⟨s, hs⟩ := hu
  refine hasVal_unique hϖ hd ⟨s ^ (a.be y y / 2) * v, ?_⟩
  rw [e2, hs, mul_zpow, ← zpow_mul, Units.val_mul, map_mul, _root_.mul_assoc]
  congr 2
  exact (map_zpow (((algebraMap W (FractionRing W)) : W →* FractionRing W).comp (Units.coeHom W)) s _).symm

open ReciprocityTheory.ChartRestriction.G.DVR in

theorem exists_form {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O']
    {b : O →+* O'} {a : ArcIn D l β O' b} {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W]
    {f : O' →+* W} {u : W} {χ : Sp W ⟶ Y.X} (hfi : Function.Injective f) (A : ArcWit Y a (maximalIdeal W) f u χ)
    {ϖ : W} (hϖ : Irreducible ϖ) (v : Wˣ) (k : ℕ) (hu : u = v * ϖ ^ k) :
    ∃ be ∈ levelForms H 1 A.P.D.toPre.X, IsMonomial A.P.D.toPre ![ϖ] ![be] ∧
      ∀ y z, be (A.e y) (A.e z) = k * a.be y z := by
  letI := H.starRing
  choose Q hQ using QForm.exists_QVal hϖ A.P.D
  have hQ' : QForm.IsQ A.P.D.toPre ϖ Q := hQ
  have hval : HasVal ϖ (algebraMap W (FractionRing W) u) k := ⟨v, by
    rw [hu]; simp [_root_.mul_comm]⟩
  have hq := fun y => q_eq hfi A hϖ hQ' hval y
  have hex : ∀ χ, ∃ r, PsiCoord A.P.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main W A.P.D inferInstance χ).1).imp fun _ h => h.1
  let es : A.P.D.toPre.X →ₗ[ℤ] a.D₀.X := A.e.symm.toLinearMap.toAddMonoidHom.toIntLinearMap
  let be : LinearMap.BilinForm ℤ A.P.D.toPre.X := (k : ℤ) • a.be.compl₁₂ es es
  have hbe : ∀ y z, be (A.e y) (A.e z) = k * a.be y z := fun y z => by simp [be, es]
  have hs : ∀ y, ∃ y₀, A.e y₀ = y := A.e.surjective
  refine ⟨be, ⟨fun y z => ?_, fun x y z => ?_, fun y z => ?_⟩, fun y => ?_, hbe⟩
  · obtain ⟨y, rfl⟩ := hs y
    obtain ⟨z, rfl⟩ := hs z
    rw [hbe, hbe, a.be_symm]
  · obtain ⟨y, rfl⟩ := hs y
    obtain ⟨z, rfl⟩ := hs z
    rw [← map_smul, ← map_smul, hbe, hbe, a.be_adj]
  · simp
  · obtain ⟨y₀, rfl⟩ := hs y
    obtain ⟨r, hr⟩ := hex (A.e y₀)
    have hv := GlobalTheory.ValForm.hasVal_coord (hQ (A.e y₀)) hr
    have h0 : 0 ≤ a.be y₀ y₀ := by
      by_cases h : y₀ = 0
      · simp [h]
      · exact (a.be_pos y₀ h).le
    obtain ⟨d, hd⟩ : (2 : ℤ) ∣ a.be y₀ y₀ := Dvd.dvd.trans (Dvd.intro _ rfl) (a.be_dvd y₀ y₀)
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ d by omega)
    have hQn : Q (A.e y₀) = ((k * n : ℕ) : ℤ) := by
      rw [hq y₀, hd, hn]; push_cast; congr 1; omega
    rw [hQn] at hv
    obtain ⟨w, hw⟩ := hv
    rw [zpow_natCast, ← map_pow, ← map_mul] at hw
    have e : r = w * ϖ ^ (k * n) := (IsFractionRing.injective W (FractionRing W) hw).trans (_root_.mul_comm _ _)
    refine ⟨w, fun _ => k * n, fun i => ?_, ?_⟩
    · have : i = 0 := Subsingleton.elim _ _
      subst this
      show be (A.e y₀) (A.e y₀) = _
      rw [hbe, hd, hn]; push_cast; ring
    · simpa [e] using hr

theorem order_of_arcWit {O O₂ : Type} [CommRing O] [CommRing O₂] {β : O →+* c.F} {β₂ : O₂ →+* c.F}
    (Z : Model Xo c β) (Y : Model Xo c β₂) (BD : EffCartierData Z.X) (φ : InvFun (𝓞 E))
    (hφ : ∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B)
    (hpol : IsPhiDiv φ Z BD) {O' : Type} [CommRing O'] [IsDomain O'] {b : O₂ →+* O'} {a : ArcIn D l β₂ O' b}
    [Module.Finite (𝓞 E) a.D₀.X] {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) {f : O' →+* V} {u : V}
    {χ' : Sp V ⟶ Y.X} (hfi : Function.Injective f) (A : ArcWit Y a (maximalIdeal V) f u χ')
    (y : Sp (FractionRing V) ⟶ Xo.XF c) (χ : Sp V ⟶ Z.X) (hZ : jK V ≫ χ = y ≫ Z.j) (hY : jK V ≫ χ' = y ≫ Y.j)
    {ϖ : V} (hϖ : Irreducible ϖ) (v : Vˣ) (k : ℕ) (hu : u = v * ϖ ^ k) :
    ∃ n : ℕ, (n : ℝ) = k * φ.eval a.D₀.X (fun p q => (a.be p q : ℝ)) ∧
      idlAlong BD.idealSheaf χ = Ideal.span {ϖ ^ n} := by
  have := hV.1
  have := hV.2.2
  obtain ⟨be, hbe, hmon, hform⟩ := exists_form hfi A hϖ v k hu
  obtain ⟨m⟩ := exists_sabMap_of_generic Z Y hV y χ χ' hZ hY A.m
  have hr : Set.range (jK V ≫ χ) ⊆ Set.range Z.j := by
    rintro _ ⟨p, rfl⟩
    exact ⟨y p, by rw [hZ]; rfl⟩
  obtain ⟨n, hn, hid⟩ := hpol V hV ϖ hϖ χ A.t m A.P hr be hbe hmon
  refine ⟨n, hn.trans ?_, hid⟩
  have e : φ.evalZ be = φ.eval a.D₀.X (fun p q => ((be (A.e p) (A.e q) : ℤ) : ℝ)) := (φ.eval_equiv A.e _).symm
  rw [e]
  simp_rw [hform]
  push_cast
  exact eval_natMul φ hφ k _

theorem idlAlong_eq_top_of_abelian {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) (BD : EffCartierData Z.X)
    (φ : InvFun (𝓞 E)) (hpol : IsPhiDiv φ Z BD) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V)
    (y : Sp (FractionRing V) ⟶ Xo.XF c) (χ : Sp V ⟶ Z.X) (hZ : jK V ≫ χ = y ≫ Z.j) (hab : ∀ p, χ p ∈ abLocus Z.t.G) :
    idlAlong BD.idealSheaf χ = ⊤ := by
  obtain ⟨h₁, h₂, h₃⟩ := hV
  let T : CDVR := { V := V }
  obtain ⟨t₁, ⟨m₁⟩⟩ := GlobalTheory.TraitOrder.exists_pull χ Z.t
  have hp := GlobalTheory.GoodTrait.polAt_of_point Z m₁ (jK V) y hZ.symm
  obtain ⟨T', f, u, hi, hl, ⟨mu⟩, ⟨P⟩⟩ := exists_unif_ext T t₁ hp
  obtain ⟨n'⟩ := GlobalTheory.TraitOrder.comp rfl m₁ mu
  have hW' : CDvr T'.V := ⟨T'.dvr, T'.cpl, T'.ch0⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
  obtain ⟨be, hbe, hmon, -⟩ := exists_periodForm P hϖ
  have hs : Subsingleton P.D.toPre.X := (closed_mem_abLocus_iff T' P).1
    ((abLocus_pullback abLocusOne Z.t.semi n'.cart.1 _).1 ((congrArg (· ∈ abLocus Z.t.G) (Scheme.Hom.comp_apply (spMap f) χ _)).mpr (hab _)))
  have j : Function.Injective ((algebraMap T'.V (FractionRing T'.V)).comp f) :=
    (IsFractionRing.injective T'.V _).comp hi
  let g : FractionRing V →+* FractionRing T'.V := IsFractionRing.lift j
  have e : jK T'.V ≫ spMap f = spMap g ≫ jK V :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  have hr : Set.range (jK T'.V ≫ spMap f ≫ χ) ⊆ Set.range Z.j := by
    rintro _ ⟨p, rfl⟩
    refine ⟨(spMap g ≫ y) p, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, ← hZ, ← Category.assoc, ← e, Category.assoc]
  obtain ⟨k, hk, hid⟩ := hpol T'.V hW' ϖ hϖ _ u n' P hr be hbe hmon
  have h0 : φ.evalZ be = 0 := φ.eval_of_subsingleton _
  obtain rfl : k = 0 := by
    rw [h0] at hk
    exact_mod_cast hk
  rw [GlobalTheory.TraitOrder.idlAlong_comp, pow_zero, Ideal.span_singleton_one] at hid
  exact GlobalTheory.TraitOrder.map_injective f hi (hid.trans (Ideal.map_top f).symm)

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (φ : InvFun (𝓞 E)) (m : ℕ) (BD : GlobalTheory.EffCartierData Z.X),
      (∀ (n : ℕ) (k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) →
      IsPol φ m Z BD →
      ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : c.V W →+* O') (ϖ : O')
        (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
        IsArcBase O' ϖ → IsArcChart Y (GlobalTheory.PolArc.moveV bV hbV b' a) ϖ χ₀ →
        ∀ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j →
        ∃ n : ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : PowerSeries O' →+* V) (gam : FractionRing (PowerSeries O') →+* FractionRing V),
    (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = Out.jK V ≫ χ → GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ψ PowerSeries.X ^ n} := by
  intro E _ _ _ H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ h₁ h₂ h₃ φ m BD hφ hpol O' _ _ _ b' ϖ a χ₀ hbase hchart x₀ hx₀
  obtain ⟨hL, hL₂, hL₃, hL₄, hL₅, hL₆⟩ := GlobalTheory.allSixLaws
  obtain ⟨W₀⟩ := (Y.hasArcData_iff (GlobalTheory.PolArc.moveV bV hbV b' a) _ _ _ _).1 hchart.2.2.2
  have hR : AdmBase (PowerSeries O') (Ideal.span {PowerSeries.X}) := by
    rcases hbase with ⟨hf, -⟩ | ⟨hd, -, -⟩
    · letI := hf.toField
      exact GlobalTheory.ArcPull.admissibleBase_powerSeries_span_X O'
    · exact GlobalTheory.ArcPull.admissibleBase_powerSeries_span_X O'
  haveI : Module.Finite (𝓞 E) (GlobalTheory.PolArc.moveV bV hbV b' a).D₀.X := Module.Finite.equiv W₀.e.symm
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = φ.eval (GlobalTheory.PolArc.moveV bV hbV b' a).D₀.X
      (fun p q => ((GlobalTheory.PolArc.moveV bV hbV b' a).be p q : ℝ)) := ⟨_, rfl⟩
  have inj : ∀ (V : Type) [CommRing V] [IsDomain V] (ψ : PowerSeries O' →+* V)
      (gam : FractionRing (PowerSeries O') →+* FractionRing V),
      (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) → Function.Injective ψ :=
    fun V _ _ ψ gam hg x y e => IsFractionRing.injective (PowerSeries O') (FractionRing (PowerSeries O'))
      (gam.injective (by rw [hg, hg, e]))
  have hYc : ∀ (V : Type) [CommRing V] [IsDomain V] (ψ : PowerSeries O' →+* V)
      (gam : FractionRing (PowerSeries O') →+* FractionRing V),
      (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
      jK V ≫ spMap ψ ≫ χ₀ = (spMap gam ≫ x₀) ≫ Y.j := fun V _ _ ψ gam hg => by
    rw [← Category.assoc, ← ArcExtends.spMap_jK hg, Category.assoc, Category.assoc, hx₀]
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (ψ : PowerSeries O' →+* V)
      (gam : FractionRing (PowerSeries O') →+* FractionRing V),
      (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap V _ (ψ r)) →
      ∀ χ : Sp V ⟶ Z.X, spMap gam ≫ x₀ ≫ Z.j = jK V ≫ χ → ∀ ϖ' : V, Irreducible ϖ' → ∀ (v : Vˣ) (k : ℕ), k ≠ 0 →
      ψ PowerSeries.X = v * ϖ' ^ k →
      ∃ n : ℕ, (n : ℝ) = k * c₀ ∧ GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ϖ' ^ n} := by
    intro V _ _ _ hV ψ gam hg χ hχ ϖ' hϖ' v k hk hu
    have := hV.1
    have hψ := inj V ψ gam hg
    have hsub : (Ideal.span {(PowerSeries.X : PowerSeries O')}).map ψ ≤ maximalIdeal V := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem, hu]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 hϖ'.not_isUnit) _ (Nat.pos_of_ne_zero hk))
    obtain ⟨A, -⟩ := ArcWit.baseChange hL₃.cubePull hL.polBaseChange hL₄.unifBaseChange hL₅ (qkPullExists hL.globalFns)
      polOActPull hR (GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hV) W₀ ψ hψ hsub
    rw [hc₀]
    exact order_of_arcWit Z Y BD φ hφ hpol.1 hV (f := ψ.comp PowerSeries.C)
      (show Function.Injective (ψ.comp PowerSeries.C) from hψ.comp PowerSeries.C_injective) A (spMap gam ≫ x₀) χ
      (by rw [Category.assoc]; exact hχ.symm) (hYc V ψ gam hg) hϖ' v k hu

  have hK : CharZero (FractionRing O') := IsFractionRing.charZero_of_isFractionRing O'
  obtain ⟨ψ₁, hψ₁⟩ : ∃ ψ₁ : PowerSeries O' →+* PowerSeries (FractionRing O'),
      ψ₁ = PowerSeries.map (algebraMap O' (FractionRing O')) := ⟨_, rfl⟩
  have hψi : Function.Injective ψ₁ := hψ₁ ▸ PowerSeries.map_injective _ (IsFractionRing.injective O' _)
  have j : Function.Injective ((algebraMap (PowerSeries (FractionRing O'))
      (FractionRing (PowerSeries (FractionRing O')))).comp ψ₁) := (IsFractionRing.injective _ _).comp hψi
  obtain ⟨gam₁, hg₁⟩ : ∃ gam₁ : FractionRing (PowerSeries O') →+* FractionRing (PowerSeries (FractionRing O')),
      ∀ r, gam₁ (algebraMap (PowerSeries O') _ r) = algebraMap (PowerSeries (FractionRing O')) _ (ψ₁ r) :=
    ⟨IsFractionRing.lift j, fun r => IsFractionRing.lift_algebraMap j r⟩
  have hV₁ : CDvr (PowerSeries (FractionRing O')) := GlobalTheory.ArcPointDescent.cDvr_powerSeries _
  have := isProper_toroidalModel_structureMap Z
  have hjZ : Z.j ≫ Z.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Z.jQ_over]
  have hjY : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c.V W).subtype := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have hb : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV := by
    rw [← spMap_comp]
    exact congrArg spMap (RingHom.ext fun x => (hbV x).symm)
  have hjj : Z.j ≫ Z.s = Y.j ≫ Y.s ≫ spMap bV := by
    rw [hjZ, hb, ← Category.assoc Y.j, hjY, Category.assoc]
  have hs : x₀ ≫ Z.j ≫ Z.s = jK (PowerSeries O') ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' ≫ spMap bV := by
    rw [hjj, ← Category.assoc x₀, ← hx₀, Category.assoc, ← Category.assoc χ₀, hchart.1, Category.assoc]
  obtain ⟨χ₁, hχ₁, -⟩ := val_exists Z.s (spMap gam₁ ≫ x₀ ≫ Z.j)
    (spMap ψ₁ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b' ≫ spMap bV) (by
      rw [Category.assoc, Category.assoc, hs, ← Category.assoc, ArcExtends.spMap_jK hg₁, Category.assoc])
  obtain ⟨n, hn, -⟩ := key _ hV₁ ψ₁ gam₁ hg₁ χ₁ hχ₁.symm PowerSeries.X PowerSeries.X_prime.irreducible 1 1 one_ne_zero
    (by simp [hψ₁])
  refine ⟨n, ?_⟩
  intro V _ _ _ hV ψ gam hg χ hχ
  have := hV.1
  have hψ := inj V ψ gam hg
  have hZc : jK V ≫ χ = (spMap gam ≫ x₀) ≫ Z.j := by rw [Category.assoc]; exact hχ.symm
  by_cases hU : IsUnit (ψ PowerSeries.X)
  · obtain ⟨t₁, ⟨n₁⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap ψ ≫ χ₀) Y.t
    obtain ⟨mZ⟩ := exists_sabMap_of_generic Z Y hV (spMap gam ≫ x₀) χ (spMap ψ ≫ χ₀) hZc (hYc V ψ gam hg) n₁
    have hab : ∀ p, χ p ∈ abLocus Z.t.G := fun p => by
      refine (abLocus_pullback abLocusOne Z.t.semi mZ.cart.1 p).2 ((abLocus_pullback abLocusOne Y.t.semi n₁.cart.1 p).1 ?_)
      refine (congrArg (· ∈ abLocus Y.t.G) (Scheme.Hom.comp_apply (spMap ψ) χ₀ p)).mpr ((hchart.2.1 _).2 fun hX => ?_)
      have h' : ψ PowerSeries.X ∈ p.asIdeal := hX
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hU)
    rw [idlAlong_eq_top_of_abelian Z BD φ hpol.1 hV (spMap gam ≫ x₀) χ hZc hab]
    exact (Ideal.span_singleton_eq_top.2 (hU.pow n)).symm
  · obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible V
    have hne : ψ PowerSeries.X ≠ 0 := fun h => PowerSeries.X_ne_zero (hψ (h.trans (map_zero ψ).symm))
    obtain ⟨k, v, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ'
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hU (by simp [hk])
    obtain ⟨n₂, hn₂, hid⟩ := key V hV ψ gam hg χ hχ ϖ' hϖ' v k hk0 hk
    have e : n₂ = k * n := by
      have : (n₂ : ℝ) = k * n := by rw [hn₂, hn]; simp
      exact_mod_cast this
    rw [hid, e, hk, mul_pow, pow_mul, Ideal.span_singleton_mul_left_unit (v.isUnit.pow n)]

end GlobalTheory.ArcOrder
