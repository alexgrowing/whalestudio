import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtIffOfSpecializes
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusTorsionPointStandardAlternatingForm
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelMapTorsionCharacters
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisTestLattice
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMulPowMemOOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharExistsOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabOntoAndKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaPos
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreConstOfSpecialisationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRankEqRankThetaGroupOfPointPerpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreSemiAbelianEndoTorsionExtendStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIsoSpecialisesToFieldPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrFactorPointPadicAlgClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismMatrixTorsionAdjointOnCharactersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeOfUniformisationEqModelLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackSemiAbelianDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupOfPointEqAlongModelHomStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat

theorem exists_endo_left {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (w : G ⟶ G) (hw : IsMonHom w) :
    ∃ w' : G' ⟶ G', IsMonHom w' ∧ w'.left ≫ φ = φ ≫ w.left := by
  obtain ⟨w', hw', pa⟩ := GlobalTheory.SymBaseChange.exists_endo h w
  refine ⟨w', hw', ?_⟩
  have := congrArg (fun z => z.left) (pa (𝟙 _))
  simpa [pushPt] using this

theorem latAt_of_uTest {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [hA : ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real)
    (Y : RatModel o Ω) (hY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z) (G : Over Y.Z) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (A₀ : Over (Sp Ω)) [GrpObj A₀] (a' : A₀.left ⟶ ρ.P.A.left) (ψ : A₀.left ⟶ G.left)
    (ha' : IsGrpPullback A₀ ρ.P.A (spMap S.R.val.toRingHom) a') (hψ : IsGrpPullback A₀ G Y.pt ψ)
    {I : Type} (e : I → (ρ.P.A ⟶ ρ.P.A)) (he : ∀ i, IsMonHom (e i)) (f : I → (G ⟶ G))
    (hef : ∀ i, ∃ e₀ : A₀ ⟶ A₀, e₀.left ≫ a' = a' ≫ (e i).left ∧ e₀.left ≫ ψ = ψ ≫ (f i).left)
    (gγ : S.Gam → (Over.mk Y.pt ⟶ G))
    (hγ : ∀ b, ∃ w : Sp Ω ⟶ A₀.left, w ≫ A₀.hom = 𝟙 _ ∧ w ≫ a' = spMap S.R.val.toRingHom ≫ (ρ.pt b).left ∧
      w ≫ ψ = (gγ b).left)
    (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z) (hR : S.R ≤ Y.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))))
    (y₀ : S.R →+* PadicAlgCl p) (hy₀ : ∀ a : S.R, y₀ a = Y.val (gPt p ≫ y) a) (u : ρ.UTest p y₀) (l : u.Lab)
    (ζ : oˣ) (hζ : (ζ : o) = S.ζ ^ (S.r * S.N)) (H : AddSubgroup S.Gam) (hH : l.yy.ker = H)
    (hext : ∀ t ∈ S.perp H, ExtNear (gγ t) (y (cPt p))) :
    ∃ (m : I → u.D.toPre.X →+ u.D.toPre.X) (c : S.perp H → u.D.toPre.X →+ ZMod (S.r * S.N)),
      (∀ i, ∃ (F : u.G ⟶ u.G) (eA : u.A.A ⟶ u.A.A), IsMonHom F ∧ eA.left ≫ u.φ = u.φ ≫ (e i).left ∧
        eA.left ≫ genMap u.U = genMap u.U ≫ F.left ∧ EndChar u.U F (m i)) ∧
      (∀ t b α, l.yy b = QuotientAddGroup.mk α → c t α = eStd S.g _ t.1 b) ∧
      LatAt f (fun t : S.perp H => gγ t.1) ζ (S.r * S.N) m c (y (cPt p)) := by
  subst hH
  haveI := hA.ded
  have hL : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  have hζ1 : ζ ^ (S.r * S.N) = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hζ, ← pow_mul, ← pow_two, S.prim.pow_eq_one]; rfl)
  haveI : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hB : GlobalTheory.Mum.Base u.V := ⟨⟨inferInstance, inferInstance, inferInstance, u.complete⟩, inferInstance⟩
  have hgen := GlobalTheory.TauFormHom.isGrpPullback_genMap u.U
  choose eA heA heA' using fun i => exists_endo_left u.cart (e i) (he i)
  choose F hF using fun i => (GlobalTheory.Published.SemiAbelianHomExtension.fractionField_of_isGrpPullback
    GlobalTheory.semiAbelianHomExtension_holds u.semi u.semi hgen hgen (eA i)).exists
  choose m hm using fun i => endChar_exists_of_isMonHom u.V hB u.G u.semi u.D u.A u.U (F i) (hF i).1
  choose c hc using fun t : S.perp l.yy.ker => PerpTorus.exists_form S l.yy l.yy_onto t.1 t.2
  refine ⟨m, c, fun i => ⟨F i, eA i, (hF i).1, heA' i, (hF i).2, hm i⟩, hc, ?_⟩
  obtain ⟨V', _, _, _, fV, fK, κ', iV, ξ, hfV, hfK, hκ, hiV, hiκ, hξ⟩ :=
    GlobalTheory.T.exists_dvr_factor_point_padicAlgClosure o Ω Y p u.V u.complete (algebraMap _ _) u.norm_le y
  let jV := algebraMap V' (FractionRing V')
  have hcl : ξ (closedPoint V') = y (cPt p) := by
    rw [← hξ]
    exact (congrArg ξ (IsLocalRing.comap_closedPoint iV)).symm
  have hg : gPt p ≫ y = spMap κ' ≫ spMap jV ≫ ξ := by
    rw [← hξ, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp']
    congr 2
    exact RingHom.ext hiκ
  have hpt : (gPt p ≫ y) (closedPoint (PadicAlgCl p)) = (spMap jV ≫ ξ) (closedPoint (FractionRing V')) := by
    rw [hg]
    exact congrArg (spMap jV ≫ ξ) (Subsingleton.elim (α := PrimeSpectrum (FractionRing V')) _ _)
  rw [hpt] at hR
  have hyK : ∀ x : S.R, (fK.comp u.yK) x = Y.val (spMap jV ≫ ξ) x := fun x => κ'.injective (by
    have e₁ := RatModel.val_spMap_comp κ' (spMap jV ≫ ξ) (specializes_refl _) ⟨x.1, hR x.2⟩
    rw [RatModel.valLoc_eq_val] at e₁
    rw [← e₁, ← hg, ← hy₀]
    exact (DFunLike.congr_fun hκ (u.yK x)).trans (DFunLike.congr_fun u.fac x))
  have hα := isGrpPullback_pullback u.A.A (spMap fK)
  obtain ⟨Ψ, hΨ, hΨe, hΨp⟩ := GlobalTheory.T.genericFibre_iso_specialises_to_fieldPoints o Ω Y hY G hG S.R ρ.P.A (isSemiAbelian_of_isAbelianScheme _ ρ.P.isAb) A₀ a' ψ ha' hψ
    _ _ hR _ hyK _ _ ((hα.comp u.cart).congr (spMap_comp' _ _) rfl)
  have hj : spMap fK ≫ jK u.V = spMap (jV.comp fV) := (spMap_comp' _ _).trans (congrArg spMap (RingHom.ext hfK))
  obtain ⟨G', _, β, β', ω, hβ, hβ', hω, hωβ, hωβ', hend⟩ := GlobalTheory.T.exists_common_pullback_semiAbelian_dvr Y.Z G hG u.V u.G u.semi V' fV ξ _ _ Ψ
    ((hα.comp hgen).congr hj rfl) hΨ
  obtain ⟨a, ha⟩ := exists_spMap (ξ ≫ Y.s)
  rw [← hcl] at hext ⊢
  obtain ⟨xx, hxx, hsurj⟩ := LabelMap.exists_lift_points u.cart (TFK (R := u.V) (PadicAlgCl p)) ρ.pt ρ.pt_add
  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := (spMap_comp' _ _).trans (congrArg spMap u.fac)
  have hsurj' := hsurj (S.r * S.N) fun z hz =>
    (ρ.pt_bij (PadicAlgCl p) _ z hz).exists.imp fun a ha => congrArg (fun w => w.left) ha
  have hx : ∀ b, (xx (Multiplicative.ofAdd b)).left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left := fun b => by
    rw [← hy]; exact (hxx b _).2 rfl
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have tor := PerpCharacter.exists_torus_point_eStd ⟨h1, h2, h3, h4, h5⟩ uTors_closed o Ω S ρ p y₀ u l
    (fun b => xx (Multiplicative.ofAdd b)) hx (fun b b' => by rw [ofAdd_add, map_mul])
    (fun z hz => (hsurj' z hz).imp fun _ h => h.symm)
  refine GlobalTheory.T.lattice_of_uniformisation_eq_model_lattice o Ω Y G hG I _ f _ ζ _ hL hζ1 u.V hB u.G u.semi u.D u.A u.U F m hm V' fV hfV ξ a ha G' β β' hβ hβ'
    (fun i => ?_) (PadicAlgCl p) (κ'.comp jV) (κ'.injective.comp (IsFractionRing.injective V' _))
    (by rw [← hκ]; ext x; simp [jV, hfK]) c fun t => ⟨hext t.1 t.2, ?_⟩
  · obtain ⟨eK, -, heK⟩ := exists_endo_left hα (eA i) (heA i)
    obtain ⟨e₀, h₀, h₀'⟩ := hef i
    refine hend (F i) (f i) eK ?_ (hΨe (e i) (f i) e₀ h₀ h₀' eK ?_)
    · rw [← Category.assoc, heK, Category.assoc, (hF i).2, Category.assoc]
    · rw [← Category.assoc, heK, Category.assoc, heA', Category.assoc]
  · obtain ⟨q, τ, hq, hτ, hqx, hv⟩ := tor t.1 t.2
    have hw : (xx (Multiplicative.ofAdd t.1)).left ≫ u.A.A.hom = spMap κ' ≫ spMap fK := by
      rw [Over.w, spMap_comp', hκ]; rfl
    let xK : Sp (PadicAlgCl p) ⟶ ((Over.pullback (spMap fK)).obj u.A.A).left := pullback.lift _ _ hw
    have hx₁ : xK ≫ pullback.fst u.A.A.hom (spMap fK) = (xx (Multiplicative.ofAdd t.1)).left := pullback.lift_fst _ _ _
    have hx₂ : xK ≫ ((Over.pullback (spMap fK)).obj u.A.A).hom = spMap κ' := pullback.lift_snd _ _ _
    refine ⟨q, τ, _, xK ≫ ω, hq, hτ, hqx, fun χ => ?_, ?_, ?_, ?_⟩
    · obtain ⟨b, hb⟩ := l.yy_onto (QuotientAddGroup.mk χ)
      rw [hv b χ hb, hc t b χ hb, hy₀, hζ, ← pow_mul]
      have : (gPt p ≫ y) ≫ Y.s = spMap ((κ'.comp jV).comp a) := by
        rw [hg, Category.assoc, Category.assoc, ha, spMap_comp', spMap_comp']
      exact RatModel.val_algebraMap this _
    · rw [Category.assoc, hω, ← Category.assoc, hx₂, spMap_comp']
    · rw [Category.assoc, hωβ, ← Category.assoc, hx₁]
    · obtain ⟨v, hv'⟩ := ExtNear.exists_valAt ξ (hext t.1 t.2)
      obtain ⟨w, hw₁, hw₂, hw₃⟩ := hγ t.1
      have hv₂ := hv'.comp (spMap (κ'.comp jV))
      rw [Category.assoc, hωβ', hΨp (ρ.pt t.1).left (gγ t.1) w (Over.w _) hw₁ hw₂ hw₃ _ xK (spMap (κ'.comp jV) ≫ v) ?_ ?_]
      · exact hv₂
      · rw [← Category.assoc, hx₁, hx, ← Category.assoc, hx₂, ← Category.assoc, spMap_comp', ← RingHom.comp_assoc, hκ, u.fac]
      · rw [← Category.assoc, hx₂, ← Category.assoc, spMap_comp']
        exact hv₂

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

def matAct (X : Type) [AddCommGroup X] (E : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 → X) →+ (Fin 8 → X) :=
  AddMonoidHom.mk' (fun v a => ∑ b, E a b • v b) fun v w => funext fun a => by
    simp [smul_add, Finset.sum_add_distrib]

theorem latAt_of_isLab (X₁ : Setup F W i) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A))
    (hε : IsDiagEnd F W X₁.ρ.P X₁.u ε₁) (Y : RatModel X₁.o₁ X₁.Ω₁) (hY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z)
    (q : Y.Z ⟶ X₁.M.Z) (hq : Y.pt ≫ q = X₁.M.pt) (G : Over Y.Z) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (A₀ : Over (Sp X₁.Ω₁)) [GrpObj A₀] (a₀ : A₀.left ⟶ X₁.ρ.P.A.left) (ψ : A₀.left ⟶ G.left)
    (ha₀ : IsGrpPullback A₀ X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a₀) (hψ : IsGrpPullback A₀ G Y.pt ψ)
    (adj : Matrix (Fin 8) (Fin 8) ℤ → Matrix (Fin 8) (Fin 8) ℤ)
    (hadj : ∀ E, (W + W.transpose) * E = (adj E).transpose * (W + W.transpose)) (f : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G))
    (hf : ∀ E (e₀ : A₀ ⟶ A₀), e₀.left ≫ a₀ = a₀ ≫ (ε₁ (adj E)).left → e₀.left ≫ ψ = ψ ≫ (f E).left)
    (gγ : X₁.S.Gam → (Over.mk Y.pt ⟶ G))
    (hγ : ∀ b (w : Sp X₁.Ω₁ ⟶ A₀.left), w ≫ A₀.hom = 𝟙 _ → w ≫ a₀ = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt b).left →
      w ≫ ψ = (gγ b).left)
    (p : ℕ) [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ Y.Z) (hy : y ≫ q = c.y)
    (yy : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)) (hl : IsLab X₁ ε₁ c yy)
    (ζ : X₁.o₁ˣ) (hζ : (ζ : X₁.o₁) = X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (H : AddSubgroup X₁.S.Gam) (hH : yy.ker = H)
    (hext : ∀ t ∈ X₁.S.perp H, ExtNear (gγ t) (y (cPt p))) :
    ∃ cc : X₁.S.perp H → (Fin 8 → c.T.D.toPre.X) →+ ZMod (X₁.S.r * X₁.S.N),
      (∀ t b mu, yy b = QuotientAddGroup.mk mu → cc t mu = eStd X₁.S.g _ t.1 b) ∧
      LatAt f (fun t : X₁.S.perp H => gγ t.1) ζ (X₁.S.r * X₁.S.N) (matAct _) cc (y (cPt p)) := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', hsame, -, hR', y₀, hy₀, u, l, j, hjq, hyy, hmat⟩ := hl
  have hmon := GlobalTheory.T.isMonHom_rescaled_realisation_same_genericFibre g n F W Z i X₁ ε₁ hε c₀ hc R' fg frac hth hev ρ' ε' hsame
  obtain ⟨P₀, a, a', ε₀, ha, ha', -, -, hε₀, hpts⟩ := hsame
  have key : ∀ b mu, yy b = QuotientAddGroup.mk mu ↔ l.yy b = QuotientAddGroup.mk (j.symm mu) := fun b mu => by
    refine ⟨fun h => ?_, fun h => by rw [hyy b _ h, j.apply_symm_apply]⟩
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy b)
    obtain ⟨v, hv⟩ := QuotientAddGroup.eq.1 ((hyy b χ hχ.symm).symm.trans h)
    rw [← hχ]
    refine QuotientAddGroup.eq.2 ⟨j.symm v, j.injective ?_⟩
    simp only [nsmulAddMonoidHom_apply] at hv ⊢
    rw [map_nsmul, j.apply_symm_apply, hv, map_add, map_neg, j.apply_symm_apply]
  have hker : l.yy.ker = H := by
    rw [← hH]
    ext b
    have := key b 0
    rw [map_zero] at this
    exact this.symm
  have ha₁ : IsGrpPullback P₀.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a := ha
  obtain ⟨E, hE, hEa⟩ := grpPullback_iso ha₁ ha₀
  have hψ' : IsGrpPullback P₀.A G Y.pt (E.hom.left ≫ ψ) :=
    ((isGrpPullback_of_iso E).comp hψ).congr (Category.id_comp _) rfl
  have hom : X₁.M.IsHom Y (AlgHom.id _ _) q :=
    hq.trans ((Category.id_comp _).symm.trans (congrArg (· ≫ X₁.M.pt) (Spec.map_id _).symm))
  have hcy : gPt p ≫ c.y = (gPt p ≫ y) ≫ q := by rw [Category.assoc, hy]
  rw [hcy] at hR' hy₀
  obtain ⟨m, c₁, hm, hc₁, hlat⟩ := latAt_of_uTest (X₁.S.rechart c₀ hc R' fg frac hth hev) ρ' Y hY G hG P₀.A a' _ ha' hψ'
    (fun E => ε' (adj E)) (fun E => hmon _) f (fun E' => ⟨ε₀ (adj E'), (hε₀ _).2, by
      have h := hf E' (E.inv ≫ ε₀ (adj E') ≫ E.hom) (by
        rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hEa, (hε₀ _).1, ← hEa, ← Category.assoc,
          ← Category.assoc, ← Over.comp_left, E.inv_hom_id, Over.id_left, Category.id_comp])
      rw [Category.assoc, ← h, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, ← Category.assoc E.hom.left,
        ← Over.comp_left, E.hom_inv_id, Over.id_left, Category.id_comp]⟩) gγ (fun b => by
      obtain ⟨w, hw, hw'⟩ := hpts b
      have h1 : w ≫ P₀.A.hom = 𝟙 _ := by
        obtain ⟨σ, hσ⟩ := exists_spMap (w ≫ P₀.A.hom)
        have e₁ : σ.comp R'.val.toRingHom = R'.val.toRingHom := ringHom_eq_of_spMap (by
          rw [← spMap_comp', ← hσ, Category.assoc, ← ha'.1.w, ← Category.assoc, hw', Category.assoc, Over.w]
          exact Category.comp_id _)
        have e₂ : σ = RingHom.id _ := RingHom.ext fun x => by
          obtain ⟨a, ha, b, hb, rfl⟩ := frac x
          rw [map_div₀, show σ a = a from DFunLike.congr_fun e₁ ⟨a, ha⟩, show σ b = b from DFunLike.congr_fun e₁ ⟨b, hb⟩]
          rfl
        rw [hσ, e₂]
        exact Spec.map_id _
      refine ⟨w, h1, hw', ?_⟩
      rw [← Category.assoc]
      exact hγ b _ (by rw [Category.assoc, Over.w, h1]) (by rw [Category.assoc, hEa]; exact hw))
    p y (fun x hx => hom.map_mem_O (hR' hx)) y₀ (fun x => (hy₀ x).trans (hom.val_comp _ _ (hR' x.2))) u l ζ hζ H hker hext
  refine ⟨fun t => (c₁ t).comp j.symm.toAddMonoidHom, fun t b mu h => hc₁ t b _ ((key b mu).1 h),
    hlat.equiv j (fun E' χ => ?_) fun t χ => by simp⟩
  obtain ⟨F', eA, h1, h2, h3, h4⟩ := hm E'
  exact GlobalTheory.T.endomorphism_matrix_torsion_adjoint_on_characters _ _ _ ρ' p y₀ u l W X₁.posW _ c.T.β c.T.symm (Trait.beta_pos _ _ _ _ F c.T) c.sc c.scale_pos j hjq
    (ε' (adj E')) (adj E') E' (hadj E') (fun m pk pk' x x' => hmat m pk pk' x x' _) F' eA h1 h2 h3 _ h4 χ

theorem exists_adj (hW : IsE8 W) (E : Matrix (Fin 8) (Fin 8) ℤ) :
    ∃ E' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * E = E'.transpose * (W + W.transpose) :=
  ⟨((W + W.transpose) * E * (W + W.transpose)⁻¹).transpose, by
    rw [Matrix.transpose_transpose, Matrix.mul_assoc _ _ (W + W.transpose),
      Matrix.nonsing_inv_mul _ (by rw [hW.2]; exact isUnit_one), Matrix.mul_one]⟩

theorem eq_of_equiv_fin {A : Type} [AddCommGroup A] {L r r' : ℕ} (hL : 2 ≤ L) (e : A ≃+ (Fin r → ZMod L))
    (e' : A ≃+ (Fin r' → ZMod L)) : r = r' := by
  have := Nat.card_congr (e.symm.trans e').toEquiv
  simp only [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  exact Nat.pow_right_injective hL this

theorem exists_equiv_of_fibre : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (_ : ZHOut X₁.ρ Y U₀ EE) (q : Y.Z ⟶ X₁.M.Z), X₁.S.Over₀ Y U₀ → X₁.S.IsEE Y U₀ EE → IsProper q → Y.pt ≫ q = X₁.M.pt → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), _root_.IsPreconnected (q.base ⁻¹' {z₁}) → ∀ (c c' : CTrait X₁ p z₁) (y y' : Sp (OO p) ⟶ Y.Z), y ≫ q = c.y → y' ≫ q = c'.y → ∀ (yy : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)) (yy' : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c'.T.D.toPre.X)), IsLab X₁ ε₁ c yy → IsLab X₁ ε₁ c' yy' → ∃ θ : (Fin 8 → c.T.D.toPre.X) ≃+ (Fin 8 → c'.T.D.toPre.X), (∀ a mu, yy a = QuotientAddGroup.mk mu → yy' a = QuotientAddGroup.mk (θ mu)) ∧ ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → c.T.D.toPre.X), θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b := by
  intro g n F W Z i X₁ h₁ h₂ h₃ h₄ hW h₆ h₇ ε₁ hε Y U₀ EE FinalForm q hO hE _ hq p _ z₁ hconn c c' y y' hy hy' yy yy' hl hl'
  obtain ⟨-, hker⟩ := isLab_onto_and_ker g n F W Z i X₁ h₁ h₂ h₃ h₄ hW h₆ h₇ ε₁ hε p z₁ c yy hl
  obtain ⟨honto', hker'⟩ := isLab_onto_and_ker g n F W Z i X₁ h₁ h₂ h₃ h₄ hW h₆ h₇ ε₁ hε p z₁ c' yy' hl'
  haveI := X₁.ar.ded
  have hL2 : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  have hL : 0 < X₁.S.r * X₁.S.N := by omega
  have hζp : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) := X₁.S.prim.pow (pow_pos hL 2) (pow_two _)
  let ζ : X₁.o₁ˣ := (hζp.isUnit hL.ne').unit
  have hζ1 : ζ ^ (X₁.S.r * X₁.S.N) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hζp.pow_eq_one)
  have hζκ : ∀ (κ : Type) [Field κ] (a : X₁.o₁ →+* κ), IsPrimitiveRoot (a ζ) (X₁.S.r * X₁.S.N) := fun κ _ a => by
    have : NeZero ((X₁.S.r * X₁.S.N : ℕ) : κ) := ⟨by simpa using (X₁.S.unit.map a).ne_zero⟩
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic _ a]
    exact (hζp.isRoot_cyclotomic hL).map
  obtain ⟨A₀, _, a₀, ψ, ha₀, hψ, hend, hpts⟩ := GlobalTheory.T.genericFibre_semiAbelian_endo_torsion_extend _ _ X₁.S X₁.ρ Y U₀ EE FinalForm hO.ne
  choose adj hadj using exists_adj hW
  choose f hf hf' using fun E => hend (ε₁ (adj E)) (Sep.IsAct.isMonHom hε _)
  choose gγ hγ₁ hγ₂ hγ₃ using hpts
  have hHH : ∀ w, q w = z₁ → X₁.S.HH Y w = X₁.S.HH X₁.M z₁ := fun w hw =>
    hw ▸ GlobalTheory.T.thetaGroupOfPoint_eq_along_modelHom _ _ X₁.S X₁.M Y q hq X₁.div w
  have hle : X₁.S.perp (X₁.S.HH X₁.M z₁) ≤ X₁.S.HH X₁.M z₁ := by
    obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, -, y₀, -, u, l, j, -, hyy, -⟩ := hl
    have hk : l.yy.ker = X₁.S.HH X₁.M z₁ := by
      rw [← hker]
      ext b
      obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy b)
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hyy b χ hχ.symm, ← hχ, QuotientAddGroup.eq_zero_iff,
        QuotientAddGroup.eq_zero_iff]
      constructor
      · rintro ⟨v, hv⟩
        exact ⟨j v, by rw [← hv]; exact (map_nsmul j _ _).symm⟩
      · rintro ⟨v, hv⟩
        exact ⟨j.symm v, j.injective (by rw [← hv]; exact (map_nsmul j _ _).trans (by rw [j.apply_symm_apply]; rfl))⟩
    have h := l.isoFree.1
    rw [TestBasis.perp_perp, hk] at h
    exact h
  have hext : ∀ w, q w = z₁ → ∀ t ∈ X₁.S.perp (X₁.S.HH X₁.M z₁), ExtNear (gγ t) w := fun w hw t ht =>
    hγ₃ t w (by rw [hHH w hw]; exact hle ht)
  have hx : q (y (cPt p)) = z₁ := by rw [← c.cen, ← hy]; rfl
  have hx' : q (y' (cPt p)) = z₁ := by rw [← c'.cen, ← hy']; rfl
  obtain ⟨cc, hcc, hlat⟩ := latAt_of_isLab X₁ ε₁ hε Y hO.normal q hq FinalForm.G FinalForm.semi A₀ a₀ ψ ha₀ hψ adj hadj f hf' gγ hγ₂ p c y hy
    yy hl ζ rfl _ hker (hext _ hx)
  obtain ⟨cc', hcc', hlat'⟩ := latAt_of_isLab X₁ ε₁ hε Y hO.normal q hq FinalForm.G FinalForm.semi A₀ a₀ ψ ha₀ hψ adj hadj f hf' gγ hγ₂ p c' y'
    hy' yy' hl' ζ rfl _ hker' (hext _ hx')
  haveI := RatModel.noetherianSpace_of_isNoetherianRing Y
  have hrk : ∀ a b, q a = z₁ → q b = z₁ → ∃ r, RkAt FinalForm.G a r ∧ RkAt FinalForm.G b r := fun a b ha hb => by
    obtain ⟨r, hr, ⟨e⟩⟩ := GlobalTheory.T.torusRank_eq_rank_thetaGroupOfPoint_perp _ _ X₁.S X₁.ρ Y U₀ EE FinalForm X₁.big hO hE a
    obtain ⟨r', hr', ⟨e'⟩⟩ := GlobalTheory.T.torusRank_eq_rank_thetaGroupOfPoint_perp _ _ X₁.S X₁.ρ Y U₀ EE FinalForm X₁.big hO hE b
    have hT : X₁.S.TT Y b = X₁.S.TT Y a := congrArg X₁.S.perp ((hHH b hb).trans (hHH a ha).symm)
    have := eq_of_equiv_fin hL2 e ((AddEquiv.addSubgroupCongr hT).symm.trans e')
    exact ⟨r, hr, this ▸ hr'⟩
  have hγ₁' : ∀ t : X₁.S.perp (X₁.S.HH X₁.M z₁), gγ t.1 ^ (X₁.S.r * X₁.S.N) = 1 := fun t => hγ₁ t.1
  have hiff := fun a b (hb : q b = z₁) hab r hr hr' => latAt_iff_of_specializes (f := f)
    (gγ := fun t : X₁.S.perp (X₁.S.HH X₁.M z₁) => gγ t.1) FinalForm.semi hL hζ1 X₁.S.unit hf hγ₁' (matAct _) cc (w := a) (w' := b)
    hab (r := r) hr hr' (fun t => hext b hb t.1 t.2)
  have hmove := GlobalTheory.T.fibre_const_of_specialisation_invariant Y.Z X₁.M.Z q q.continuous z₁ hconn _
    (fun a b ha hb hab => (hrk a b ha hb).elim fun r h => hiff a b hb hab r h.1 h.2) (y (cPt p)) (y' (cPt p)) hx hx' hlat
  haveI := FinalForm.semi.separated
  obtain ⟨θ, hθ₁, hθ₂⟩ := LatAt.unique hL hζκ hmove hlat'
  refine ⟨θ, fun a mu h => ?_, fun E v => hθ₁ E v⟩
  obtain ⟨a', ha'⟩ := honto' (QuotientAddGroup.mk (θ mu))
  have hmem : a - a' ∈ yy'.ker := by
    rw [hker', ← TestBasis.perp_perp X₁.S (X₁.S.HH X₁.M z₁)]
    intro t ht
    have e := (hcc' ⟨t, ht⟩ a' _ ha').symm.trans ((hθ₂ ⟨t, ht⟩ mu).trans (hcc ⟨t, ht⟩ a mu h))
    simp only [eStd, Pi.sub_apply] at e ⊢
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at e
    rw [← e]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [← ha', ← sub_eq_zero, ← map_sub]
  exact hmem

end GlobalTheory.Poinc.FibLat
