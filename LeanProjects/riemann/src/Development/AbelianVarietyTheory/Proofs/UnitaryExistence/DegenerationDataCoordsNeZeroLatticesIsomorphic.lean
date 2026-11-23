import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDegenerationDataAlgebraicPointModel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCompleteNormalSubringJoin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordOfIsPullDegId
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DatUniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_of_unif {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (U : PELUnif I t) :
    GlobalTheory.LN.PolAt t (jK R) := by
  have := U.U.gen_hom
  have gp : IsGrpPullback ((Over.pullback (jK R)).obj t.G) U.A.A (𝟙 _) U.U.gen.hom.left :=
    isGrpPullback_of_iso U.U.gen
  have hw : LBIso (U.A.L.pull U.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := U.bundle ▸ U.U.ext
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) gp.1 U.A.isAb.proper,
    amplePt _ _ _ _ _ _ gp _ _ U.A.isLB (LB.isLB_pull t.PP.isLB _) hw.symm U.A.ample U.A.ktriv⟩

theorem polAt_pull {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {K K' : Type} [Field K] [Field K'] {j : Sp K ⟶ S} (hp : GlobalTheory.LN.PolAt t j) (j' : Sp K' ⟶ S') (g : Sp K' ⟶ Sp K)
    (h : g ≫ j = j' ≫ f) : GlobalTheory.LN.PolAt t' j' := by
  have g₁ : IsGrpPullback ((Over.pullback j').obj t'.G) t.G (j' ≫ f) (pullback.fst t'.G.hom j' ≫ m.φ) :=
    (isGrpPullback_pullback t'.G j').comp m.cart
  have g₀ := isGrpPullback_pullback t.G j
  have w : (pullback.fst t'.G.hom j' ≫ m.φ) ≫ t.G.hom = (pullback.snd t'.G.hom j' ≫ g) ≫ j :=
    g₁.1.w.trans (by rw [Category.assoc, h]; rfl)
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t'.G.hom j' ⟶ pullback t.G.hom j,
      ψ ≫ pullback.fst _ _ = pullback.fst t'.G.hom j' ≫ m.φ ∧ ψ ≫ pullback.snd _ _ = pullback.snd t'.G.hom j' ≫ g :=
    ⟨pullback.lift _ _ w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have g₂ : IsGrpPullback ((Over.pullback j').obj t'.G) ((Over.pullback j).obj t.G) g ψ :=
    g₀.cancel (g₁.congr h.symm h₁.symm) h₂
  have hL := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom j)
  have hL' := LB.isLB_pull t'.PP.isLB (pullback.fst t'.G.hom j')
  have e : LBIso (t'.PP.L.pull (pullback.fst t'.G.hom j')) ((t.PP.L.pull (pullback.fst t.G.hom j)).pull ψ) :=
    LBIso.trans hL' (LB.isLB_pull t.PP.isLB _) (LB.isLB_pull hL _)
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) _ rfl)
      (GlobalTheory.LN.GenericPoint.lbIso_pull ⟨Geo.Tor.idIso _, idIso_isGen hL⟩ _ h₁.symm).symm
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) g₂.1 hp.1,
    amplePt _ _ g _ _ ψ g₂ _ _ hL hL' e hp.2.1 hp.2.2⟩

theorem norm_unit {R C : Type} [CommRing R] [NormedField C] (f : R →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (u : Rˣ) :
    ‖f u‖ = 1 := by
  have h : ‖f u‖ * ‖f (u⁻¹ : Rˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (hf _) ?_
  calc (1 : ℝ) = ‖f u‖ * ‖f (u⁻¹ : Rˣ)‖ := h.symm
    _ ≤ ‖f u‖ * 1 := mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
    _ = _ := mul_one _

theorem vPsiAt_eq {R C : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] [NormedField C]
    (hR : IsIntegrallyClosed R) (D : DegData R (maximalIdeal R)) (f : R →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (p : ℕ)
    {χ : D.toPre.X} {r : R} (hr : PsiCoord D.toPre χ r) : vPsiAt D.toPre f p χ = -Real.logb p ‖f r‖ := by
  have h : ∃ r, PsiCoord D.toPre χ r := ⟨r, hr⟩
  obtain ⟨u, hu⟩ := (GlobalTheory.PsiCoordLocal.main R D hR χ).2.1 r _ hr h.choose_spec
  rw [vPsiAt, dif_pos h, hu, map_mul, norm_mul, norm_unit f hf, one_mul]

variable {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

theorem locus_eq (A : DatAt Y P) : A.ι ⁻¹' abLocus Y.t.G = abLocus A.t.G :=
  Set.ext fun x => abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 x

theorem isOpen_locus (A : DatAt Y P) : IsOpen (A.ι ⁻¹' abLocus Y.t.G) := by
  rw [locus_eq]; exact AbLocusOpen.isOpen_abLocus_local _ A.t.semi

theorem ker_mem (A : DatAt Y P) (q : PrimeSpectrum A.R)
    (hq : q.asIdeal = RingHom.ker ((intO ↥C.S).subtype.comp A.f)) : q ∈ A.ι ⁻¹' abLocus Y.t.G := by
  have z : Sp ↥C.S := (default : PrimeSpectrum ↥C.S)
  have e : spMap ((intO ↥C.S).subtype.comp A.f) ≫ A.ι = P.y ≫ Y.j := by
    rw [spMap_comp, Category.assoc, A.fac, P.ext]
  have hz : spMap ((intO ↥C.S).subtype.comp A.f) z = q := by
    refine PrimeSpectrum.ext ?_
    have := PrimeSpectrum.isPrime z
    rw [hq, RingHom.ker_eq_comap_bot, ← Ideal.eq_bot_of_prime (PrimeSpectrum.asIdeal z)]
    rfl
  have h₁ : Y.jQ (P.y z) ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨_, rfl⟩
  have h₂ : A.ι q = Y.j (P.y z) := by
    rw [← hz, ← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  show A.ι q ∈ abLocus Y.t.G
  rw [h₂]
  exact h₁

theorem exists_pull (A : DatAt Y P) (S : Subring ↥C.S) [IsLocalRing S] (hN : IsNoetherianRing S)
    (hI : IsIntegrallyClosed S) (hc : IsAdicComplete (maximalIdeal S) S) (h1 : ∀ z : S, ‖(z : ↥C.S)‖ ≤ 1)
    (hm : ∀ z : S, z ∈ maximalIdeal S ↔ ‖(z : ↥C.S)‖ < 1) (φ : A.R →+* S)
    (hφ : S.subtype.comp φ = (intO ↥C.S).subtype.comp A.f) (t : SAB H (Sp S)) (m : SABMap t A.t (spMap φ))
    (hp : GlobalTheory.LN.PolAt t (jK S)) :
    ∃ (U : PELUnif (maximalIdeal S) t) (e : A.Ylat ≃ₗ[𝓞 E] U.D.toPre.X),
      ∀ χ, vPsiAt U.D.toPre S.subtype p (e χ) = vPsiAt A.U.D.toPre ((intO ↥C.S).subtype.comp A.f) p χ := by
  obtain ⟨L₁, L₂, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨B, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H S t hp
  have hφ' : ∀ a, ((φ a : S) : ↥C.S) = ((A.f a : intO ↥C.S) : ↥C.S) := fun a => RingHom.congr_fun hφ a
  obtain ⟨U, e, he⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H A.R S φ A.t t m A.U _ A.noeth A.normal A.complete
    hN hI hc (fun a ha => (hm _).2 (hφ' a ▸ A.f_loc a ha)) (isOpen_locus A) (locus_eq A).le A.unitOn
    (ker_mem A _ (by rw [← hφ, RingHom.ker_comp_of_injective φ S.subtype_injective])) ⟨B, gen, hg, hw⟩
  refine ⟨U, e, fun χ => ?_⟩
  obtain ⟨r, hr, -⟩ := (GlobalTheory.PsiCoordLocal.main A.R A.U.D A.normal χ).1
  obtain ⟨u, hu⟩ := he χ r hr
  rw [vPsiAt_eq hI U.D S.subtype h1 p hu, vPsiAt_eq A.normal A.U.D _ (fun a => (A.f a).2) p hr, map_mul, norm_mul,
    norm_unit S.subtype h1, one_mul, ← hφ]
  rfl

theorem exists_equiv (hp : p.Prime) (A A₀ : DatAt Y P) [IsDiscreteValuationRing A₀.R] (hfin : Finite (ResidueField A₀.R))
    (hinj : Function.Injective A₀.f) :
    ∃ e : A.Ylat ≃ₗ[𝓞 E] A₀.Ylat, ∀ a b, A₀.beta (e a) (e b) = A.beta a b := by
  have := A₀.complete
  have hpn : ‖(p : ↥C.S)‖ < 1 := by
    rw [C.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  obtain ⟨S, _, hN, hI, hc, hf, hg, h1, hm⟩ := GlobalTheory.exists_complete_normal_subring_join A.R { V := A₀.R } ↥C.S
    ((intO ↥C.S).subtype.comp A.f) ((intO ↥C.S).subtype.comp A₀.f) p hp hpn hfin A.noeth A.complete
    (fun a => (A.f a).2) A.f_loc (fun a => (A₀.f a).2) A₀.f_loc
  let φ : A.R →+* S := ((intO ↥C.S).subtype.comp A.f).codRestrict S hf
  let φ₀ : A₀.R →+* S := ((intO ↥C.S).subtype.comp A₀.f).codRestrict S hg
  let i : S →+* intO ↥C.S := S.subtype.codRestrict (intO ↥C.S) h1
  have hi : Function.Injective i := fun a b h => Subtype.ext (congrArg (fun z : intO ↥C.S => (z : ↥C.S)) h)
  have hdom : IsDominant (spMap i) := by
    refine ⟨?_⟩
    have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical i).2
      (by rw [(RingHom.injective_iff_ker_eq_bot i).1 hi]; exact bot_le)
    exact this
  have hpr : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have hsep : Y.X.IsSeparated := ⟨by rw [← terminal.comp_from Y.s]; infer_instance⟩
  have hξ : spMap φ ≫ A.ι = spMap φ₀ ≫ A₀.ι := by
    refine ext_of_isDominant (spMap i) ?_
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    exact A.fac.trans A₀.fac.symm
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp S), Nonempty (SABMap t Y.t (spMap φ ≫ A.ι)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap φ ≫ A.ι) Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨n, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ A.m m
  obtain ⟨n₀, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ A₀.m (hξ ▸ m)
  obtain ⟨k, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ (𝟙 _) n ((Category.id_comp (spMap φ)).symm ▸ n)
  obtain ⟨gam, hsq⟩ := GlobalTheory.UnifAfterExt.exists_generic_square φ₀ fun a b h =>
    hinj (Subtype.ext (congrArg (fun z : S => (z : ↥C.S)) h))
  have hpol := polAt_pull n₀ (polAt_of_unif A₀.U) (jK S) gam hsq.symm
  obtain ⟨U, e, he⟩ := exists_pull A S hN hI hc h1 hm φ rfl t n hpol
  obtain ⟨U₀, e₀, he₀⟩ := exists_pull A₀ S hN hI hc h1 hm φ₀ rfl t n₀ hpol
  obtain ⟨d, hd⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H S t t k U U₀ hN hI hc
  have key : ∀ χ, vPsiAt A₀.U.D.toPre ((intO ↥C.S).subtype.comp A₀.f) p (((e.trans d).trans e₀.symm) χ) =
      vPsiAt A.U.D.toPre ((intO ↥C.S).subtype.comp A.f) p χ := fun χ => by
    rw [← he, ← he₀, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply]
    obtain ⟨r, hr, -⟩ := (GlobalTheory.PsiCoordLocal.main S U.D hI (e χ)).1
    obtain ⟨u, hu⟩ := hd _ r hr
    rw [vPsiAt_eq hI U₀.D S.subtype h1 p hu, vPsiAt_eq hI U.D S.subtype h1 p hr, map_mul, norm_mul,
      norm_unit S.subtype h1, one_mul]
  refine ⟨(e.trans d).trans e₀.symm, fun a b => ?_⟩
  rw [DatAt.beta, DatAt.beta, betaAt, betaAt, ← map_add, key, key, key]

theorem coord_ne_zero_and_exists_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ) (C : SCF p) (P : PointsOfFlagModel.PtC Y C), p.Prime → ∀ (T : CDVR) (g : T.V →+* intO ↥C.S) (ιT : Sp T.V ⟶ Y.X), T.FinRes → Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → spMap g ≫ ιT = P.yt → ∀ A A' : DatAt Y P, (∀ χ r, PsiCoord A.U.D.toPre χ r → ((A.f r : intO ↥C.S) : ↥C.S) ≠ 0) ∧ ∃ e : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (e a) (e b) = A.beta a b := by
  intro E _ _ _ H Dw l Xo c O _ β Y p C P hp T g ιT hT hg hl hfac A A'
  refine ⟨fun χ r hr => (GlobalTheory.PsiCoordLocal.main A.R A.U.D A.normal χ).2.2 _
    ⟨RingHom.ker ((intO ↥C.S).subtype.comp A.f), RingHom.ker_isPrime _⟩ (isOpen_locus A) (ker_mem A _ rfl)
    (A.unitOn χ) r hr, ?_⟩
  obtain ⟨A₀, ⟨_, hfin⟩, hinj, -⟩ := GlobalTheory.DatAtPoint.exists_datAt E H Dw l Xo c O β Y p C P hp T g ιT hT hg hl hfac
  obtain ⟨e, he⟩ := exists_equiv hp A A₀ hfin hinj
  obtain ⟨e', he'⟩ := exists_equiv hp A' A₀ hfin hinj
  refine ⟨e.trans e'.symm, fun a b => ?_⟩
  rw [← he, ← he', LinearEquiv.trans_apply, LinearEquiv.trans_apply, e'.apply_symm_apply, e'.apply_symm_apply]

end GlobalTheory.DatUniq
