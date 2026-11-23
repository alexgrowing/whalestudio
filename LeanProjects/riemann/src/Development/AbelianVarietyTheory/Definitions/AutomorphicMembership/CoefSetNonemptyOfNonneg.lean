import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonnegAdmissibleIffPositiveDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUniqueIsVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDiscreteValuationRingIntO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartExtensionHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameMoveHolds
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsUniqueH0Section
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.ArcQ (Wit LieImg ArcBasis)
open GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints (EpsPt IsLetters)

namespace GlobalTheory.LocM.FJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

structure DVF (p : ℕ) : Type where

  C : SCF p

  K : Subfield ↥C.S

  closed : IsClosed (K : Set ↥C.S)

  dvr : IsDiscreteValuationRing ↥(intO ↥K)

namespace DVF

variable {p : ℕ} (F : DVF p)

abbrev O : Type := ↥(intO ↥F.K)

instance : IsDiscreteValuationRing F.O := F.dvr

def toLaurent : PowerSeries F.O →+* LaurentSeries ↥F.K :=
  (HahnSeries.ofPowerSeries ℤ ↥F.K).comp (PowerSeries.map (intO ↥F.K).subtype)

theorem toLaurent_injective : Function.Injective F.toLaurent :=
  fun _ _ h => PowerSeries.map_injective (intO ↥F.K).subtype Subtype.val_injective
    (HahnSeries.ofPowerSeries_injective (Γ := ℤ) h)

theorem norm_coeff_toLaurent (g : PowerSeries F.O) (n : ℤ) : ‖(F.toLaurent g).coeff n‖ ≤ 1 := by
  change ‖((PowerSeries.map (intO ↥F.K).subtype g : PowerSeries ↥F.K) : LaurentSeries ↥F.K).coeff n‖ ≤ 1
  rw [PowerSeries.coeff_coe]
  split_ifs
  · simp
  · rw [PowerSeries.coeff_map]
    exact (PowerSeries.coeff _ g).2

theorem isAdicComplete {ϖ : F.O} (h : Irreducible ϖ) : IsAdicComplete (Ideal.span {ϖ}) F.O := by
  haveI : CompleteSpace ↥F.K := F.closed.completeSpace_coe
  have hO : (NormedField.valuation (K := ↥F.K)).Integers F.O :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun x => by
        rw [NormedField.valuation_apply, ← NNReal.coe_le_coe]
        exact x.2
      exists_of_le_one := fun r hr => ⟨⟨r, by
        rw [NormedField.valuation_apply, ← NNReal.coe_le_coe] at hr
        exact hr⟩, rfl⟩ }
  exact NormIntegers.isAdicComplete_span_singleton hO
    ((Cht.mem_maximalIdeal_ball ϖ).1 ((mem_maximalIdeal _).2 h.not_isUnit))

end DVF

theorem exists_dvf {l : Level H} (c : Coeff l) {p : ℕ} {W : ValuationSubring ℂ} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) :
    ∃ (F : DVF p) (b : c.V W →+* F.O), Function.Injective b := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  have hn := SharedLaws.mem_nonunits_V c hp.ne_zero hW
  haveI := (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp.ne_zero hn).1
  haveI : Countable c.F := Countable.of_equiv _ (Module.finBasis ℚ c.F).equivFun.toEquiv.symm
  obtain ⟨C, f, K, hf, -, hK, hd, -⟩ := Cht.CompletedClosure.fieldSt p (c.V W) hp
    ((ValuationSubring.coe_mem_nonunits_iff (A := c.V W) (a := (p : c.V W))).1 (by simpa using hn))
  let g : c.V W →+* ↥K := ((intO ↥C.S).subtype.comp f).codRestrict K fun a =>
    hK ▸ Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨a, rfl⟩)
  exact ⟨⟨C, K, hK ▸ Subfield.isClosed_topologicalClosure _, hd⟩, g.codRestrict (intO ↥K) fun a => (f a).2,
    fun a a' h => hf (Subtype.ext (congrArg (fun z : ↥(intO ↥K) => ((z : ↥K) : ↥C.S)) h))⟩

section Cusp

variable {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {A : Type} [CommRing A] [IsDomain A]

@[reducible] def withForm {b : O →+* A} (a : ArcIn Dw l β A b) (γ : levelForms H l.M' a.D₀.X)
    (h : γ ∈ admitted H l.M' a.D₀.X) : ArcIn Dw l β A b :=
  { a with be := γ.1, be_symm := γ.2.1, be_pos := h.1, be_adj := γ.2.2.1, be_dvd := h.2 }

variable (Dw l β A) in

structure Cusp : Type 1 where

  b : O →+* A

  a : ArcIn Dw l β A b

  e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → EpsPt a.D₀

  letters : ∃ io : c.F →+* FractionRing A, IsLetters a io e

namespace Cusp

variable (t : Cusp Dw l β A)

abbrev Forms : Type := levelForms H l.M' t.a.D₀.X

abbrev Chr : Type := Module.Dual ℤ t.Forms

abbrev Dir : Set t.Forms := admitted H l.M' t.a.D₀.X

theorem dir_nonempty : t.Dir.Nonempty :=
  ⟨⟨t.a.be, t.a.be_symm, t.a.be_adj, fun y z => (dvd_mul_left _ _).trans (t.a.be_dvd y z)⟩, t.a.be_pos, t.a.be_dvd⟩

theorem isFat_dir : IsFat t.Dir := isFat_adm _ H l.M'

theorem nontrivial_forms : Nontrivial t.Forms := by
  haveI := t.a.nontriv
  obtain ⟨γ, hγ⟩ := t.dir_nonempty
  obtain ⟨y, hy⟩ := exists_ne (0 : t.a.D₀.X)
  exact ⟨γ, 0, fun h => by simpa [h] using hγ.1 y hy⟩

end Cusp

section Toric

open GlobalTheory.HostModel GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out

def fracRoot (io : c.F →+* FractionRing A) {n : ℕ} (h : n ∣ l.M') : (FractionRing A)ˣ :=
  Units.map io.toMonoidHom
    (Units.mk0 ⟨zeta n, zeta_mem_coeff_of_dvd c h⟩ fun e => Complex.exp_ne_zero _ (congrArg Subtype.val e))

theorem fracRoot_pow (io : c.F →+* FractionRing A) {n : ℕ} (h : n ∣ l.M') : fracRoot io h ^ n = 1 := by
  rw [fracRoot, ← map_pow, ← map_one (Units.map io.toMonoidHom)]
  exact congrArg _ (Units.ext (Subtype.ext (isPrimitiveRoot_zeta (Nat.pos_of_dvd_of_pos h (LevelExist.M'_pos l))).pow_eq_one))

def toricIn (b : O →+* A) (io : c.F →+* FractionRing A) (hio : io.comp β = (algebraMap A _).comp b) :
    ArcIn (hypDatum H) l β A b where
  D₀ := toricPre A (𝓞 E) fun _ => 1
  oa := arcAct H A
  nontriv := inferInstanceAs (Nontrivial (𝓞 E))
  even := psiEven _ fun _ => rfl
  bimult := tauBimult _ fun _ _ _ => by simp [polar_one]
  gen y := psiUnitOn _ y 1 (by simp)
  w0 := letI := H.starRing; psi_weight_zero_linear_combination _ (𝓞 E) (polar_one_smul A) H.w0 fun _ => polar_one A _ _
  be := arcForm l
  be_symm (y z : 𝓞 E) := congrArg ((2 * l.M' : ℤ) * ·) (trForm_symm H y z)
  be_pos (y : 𝓞 E) hy := mul_pos (mul_pos two_pos (Int.natCast_pos.2 (LevelExist.M'_pos l))) (trForm_pos H hy)
  be_adj a (y z : 𝓞 E) := congrArg ((2 * l.M' : ℤ) * ·) (trForm_adj H a y z)
  be_dvd (y z : 𝓞 E) := ⟨trForm H y z, rfl⟩
  eta := qkPt A (fracRoot io (Nat.dvd_lcm_left l.M l.A)) (fracRoot_pow io _)
  etaA := qkPt A (fracRoot io (Nat.dvd_lcm_right l.M l.A)) (fracRoot_pow io _)
  geom := by
    letI := H.starRing
    intro F _ _ _ r z _ hz f hf
    refine ⟨fun τ => ⟨0, lieMult_zero _ (𝓞 E) (polar_one_smul A) f τ, ?_⟩, ?_⟩
    · rw [hypDatum_p, hypDatum_q, ite_self, zero_add]
      exact Module.finrank_self (𝓞 E)
    haveI := c.fin
    obtain ⟨ζ, hp, hc, hζ⟩ := exists_roots c.F F ((algebraMap (FractionRing A) F).comp io)
    have key : ∀ {n : ℕ} (h : n ∣ l.M') (a : HypLattice H) q,
        QkExt (algebraMap _ F) (qkPt A (fracRoot io h) (fracRoot_pow io h) a) q →
          QkPt.Equiv _ F q ((tateIsoQ H A ζ hp hc).ev n a) := fun {n} h a q hq => by
      rw [qkExt_qkPt A _ (algebraMap (FractionRing A) F) (RingHom.ext fun _ => rfl) (pow_eq_one_of_prim hp n)
        (hζ n (Nat.pos_of_dvd_of_pos h (LevelExist.M'_pos l)) ⟨zeta n, zeta_mem_coeff_of_dvd c h⟩ rfl)] at hq
      subst hq
      exact equiv_refl_split A F _
    exact ⟨tateIsoQ H A ζ hp hc, (hζ l.A l.A_pos (β z) hz).trans
      (by rw [hf]; exact congrArg (algebraMap (FractionRing A) F) (RingHom.congr_fun hio z)), key _, fun a _ => key _ a⟩

end Toric

variable {p : ℕ} {W : ValuationSubring ℂ} {F : DVF p}

theorem exists_io {K : Type} [Field K] {V : ValuationSubring K} {b : V →+* A} (hb : Function.Injective b) :
    ∃ io : K →+* FractionRing A, io.comp V.subtype = (algebraMap A (FractionRing A)).comp b := by
  have h : Function.Injective ((algebraMap A (FractionRing A)).comp b) :=
    fun x y e => hb (IsFractionRing.injective A (FractionRing A) e)
  refine ⟨IsFractionRing.lift (A := V) (K := K) h, RingHom.ext fun x => ?_⟩
  exact IsFractionRing.lift_algebraMap (A := V) (K := K) h x

theorem exists_chart {Xo : Moduli Dw l} {Y : Model Xo c (c.V W).subtype} (hY : Y.N4) {b : c.V W →+* F.O}
    (a : ArcIn Dw l (c.V W).subtype F.O b) :
    ∃ (ϖ : F.O) (χ : Sp (PowerSeries F.O) ⟶ Y.X), Irreducible ϖ ∧ IsArcChart Y a ϖ χ ∧ Nonempty (Wit Y a χ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible F.O
  obtain ⟨χ, hχ, -⟩ := hY F.O b ϖ a (Or.inr ⟨inferInstance, hϖ, F.isAdicComplete hϖ⟩)
  exact ⟨ϖ, χ, hϖ, (hχ χ).1 rfl, (Y.hasArcData_iff _ _ _ _ _).1 ((hχ χ).1 rfl).2.2.2⟩

theorem exists_cusp {Xo : Moduli Dw l} {Y : Model Xo c (c.V W).subtype} (hY : Y.N4) {b : c.V W →+* F.O}
    (hb : Function.Injective b) (a : ArcIn Dw l (c.V W).subtype F.O b) :
    ∃ t : Cusp Dw l (c.V W).subtype F.O, t.b = b ∧ HEq t.a a := by
  obtain ⟨io, hio⟩ := exists_io hb
  obtain ⟨ϖ, χ, -, -, ⟨Wt⟩⟩ := exists_chart hY a
  have hρ : ∀ τ x, algebraMap F.O (FractionRing F.O) (b.comp (IntModelExists.embV c W τ) x) = io (embK c τ x) :=
    fun τ x => (RingHom.congr_fun hio (IntModelExists.embV c W τ x)).symm
  obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_constant_eigenbasis_tangent_arc abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 E H Dw l Xo c _ _ Y F.O b a χ Wt
    (fun τ => b.comp (IntModelExists.embV c W τ)) io hio hρ (IntModelExists.exists_values c W)
  exact ⟨⟨b, a, e, io, (ArcCompare.isLetters_iff Wt io e).2 ⟨hio, _, fun τ => RingHom.ext (hρ τ), he⟩⟩, rfl, HEq.rfl⟩

theorem exists_cusp_hyp {Xo : Moduli (HostModel.hypDatum H) l} {Y : Model Xo c (c.V W).subtype} (hY : Y.N4) (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) : ∃ F : DVF p, Nonempty (Cusp (HostModel.hypDatum H) l (c.V W).subtype F.O) := by
  obtain ⟨F, b, hb⟩ := exists_dvf c hp hW
  obtain ⟨io, hio⟩ := exists_io hb
  exact ⟨F, ⟨(exists_cusp hY hb (toricIn b io hio)).choose⟩⟩

end Cusp

section Bridge

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Type} [CommRing S] (t : SAB H (Sp S))

theorem isTanAtG_id (v : epsR S ⟶ t.G) : IsTanAtG t (𝟙 _) v.left ↔ IsTangent v := by
  have e : (1 : Over.mk (𝟙 (Sp S)) ⟶ t.G).left = η[t.G].left := by
    rw [Hom.one_def, show toUnit (Over.mk (𝟙 (Sp S))) = 𝟙 (𝟙_ (Over (Sp S))) from toUnit_unique _ _]
    exact congrArg (·.left) (Category.id_comp η[t.G])
  exact ⟨fun h => h.2.trans e, fun h => ⟨(Over.w v).trans (Category.comp_id _).symm, Eq.trans h e.symm⟩⟩

theorem isCombAtG_id {n : ℕ} (v : Fin n → (epsR S ⟶ t.G)) (cf : Fin n → S) (w : epsR S ⟶ t.G) :
    IsCombAtG t (𝟙 _) (fun i => (v i).left) cf w.left ↔ IsLieComb cf v w := by
  have e := Category.comp_id (spMap (algebraMap S (DualNumber S)))
  constructor
  · rintro ⟨u, hu, h⟩
    refine ⟨fun i => Over.homMk (u i).left ((Over.w (u i)).trans e), hu, Over.OverMorphism.ext (h.symm.trans ?_)⟩
    exact BaseMdl.prod_left_congr e _ _ fun _ => rfl
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => Over.homMk (u i).left ((Over.w (u i)).trans e.symm), hu, ?_⟩
    exact BaseMdl.prod_left_congr e _ _ fun _ => rfl

theorem isFrame_id {l : Level H} {c : Coeff l} (g : c.F →+* S) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR S ⟶ t.G))
    (h : ∀ τ, (∀ k, IsTangent (u τ k) ∧
        ∀ x : 𝓞 E, (u τ k ≫ t.act.act x).left = spMap (epsScaleR (g (embK c τ x))) ≫ (u τ k).left) ∧
      ∀ w : epsR S ⟶ t.G, IsTangent w → (∀ x : 𝓞 E, (w ≫ t.act.act x).left = spMap (epsScaleR (g (embK c τ x))) ≫ w.left) →
        ∃! cf : Fin (Dw.mult τ) → S, IsLieComb cf (u τ) w) :
    IsFrame (Dw := Dw) t g (𝟙 _) fun τ k => (u τ k).left := by
  refine ⟨fun τ k => ⟨(isTanAtG_id t _).2 ((h τ).1 k).1, ((h τ).1 k).2⟩, fun τ w hw he => ?_⟩
  let w' : epsR S ⟶ t.G := Over.homMk w (hw.1.trans (Category.comp_id _))
  exact (existsUnique_congr fun cf => isCombAtG_id t (u τ) cf w').2 ((h τ).2 w' ((isTanAtG_id t w').1 hw) he)

end Bridge

section Arcs

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

abbrev CuspOn (Z : Mdl Y i₀) (F : DVF p) : Type 1 := Cusp Dw Z.i.l (Z.i.c.V W).subtype F.O

variable {Z : Mdl Y i₀} {F : DVF p} (t : CuspOn Z F)

def IsArc (γ : t.Forms) (x : Sp (LaurentSeries ↥F.K) ⟶ Z.X) (v : Vecs Dw (Y Z.i).t (LaurentSeries ↥F.K)) : Prop :=
  ∃ (h : γ ∈ t.Dir) (ϖ : F.O) (χ : Sp (PowerSeries F.O) ⟶ (Y Z.i).X) (Wt : Wit (Y Z.i) (withForm t.a γ h) χ)
    (w : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (PowerSeries F.O) ⟶ Wt.t.G)),
    Irreducible ϖ ∧ IsArcChart (Y Z.i) (withForm t.a γ h) ϖ χ ∧ (∀ τ k, LieImg Wt (t.e τ k) (w τ k)) ∧
    x ≫ Z.π = spMap F.toLaurent ≫ χ ∧ (∀ τ k, v τ k = spMap (dualMap F.toLaurent) ≫ (w τ k).left ≫ Wt.m.φ) ∧ Z.FlagAt x v

variable {e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ} {M : Z.X.Modules} (T : GrTriv Z e M) (f : Γ(M, Z.genO))

def IsSeries (γ : t.Forms) (r : LaurentSeries ↥F.K) : Prop := ∃ x v, IsArc t γ x v ∧ T.IsVal f x v r

def IsFJ (c : t.Chr → ↥F.K) : Prop := IsExpansion t.Dir (IsSeries t T f) c

def fjNorm (χ : t.Chr) : ℝ := coefNorm t.Dir (IsSeries t T f) χ

example (γ₀ : t.Forms) (h : γ₀ ∈ t.Dir) :
    fjNorm (Z := Z) ⟨t.b, withForm t.a γ₀ h, t.e, t.letters⟩ T f = fjNorm t T f := rfl

theorem le_preimage_genO (hp : p ≠ 0) {k : Type} [Field k] [CharZero k] (x : Sp k ⟶ Z.X) : ⊤ ≤ x ⁻¹ᵁ Z.genO := by
  rw [Mdl.genO, Scheme.preimage_basicOpen_top, map_natCast]
  refine (Scheme.basicOpen_of_isUnit _ ?_).ge
  have := (IsUnit.mk0 (p : k) (Nat.cast_ne_zero.2 hp)).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  rwa [map_natCast] at this

theorem exists_isArc (hY : (Y Z.i).N4) {γ : t.Forms} (h : γ ∈ t.Dir) : ∃ x v, IsArc t γ x v := by
  obtain ⟨ϖ, χ, hϖ, hχ, ⟨Wt⟩⟩ := exists_chart hY (withForm t.a γ h)
  obtain ⟨io, hio⟩ := t.letters
  obtain ⟨hb, ρ, hρ, he⟩ := (ArcCompare.isLetters_iff Wt io t.e).1 hio
  have inj := F.toLaurent_injective
  obtain ⟨g, y, hy, hyj⟩ := (Cht.extendSt E H Dw Xo p W Y i₀).1 Z.i _ (spMap F.toLaurent ≫ χ) (by
    rintro _ ⟨z, rfl⟩
    refine hχ.2.2.1 _ fun hz => mul_ne_zero ((map_ne_zero_iff _ PowerSeries.C_injective).2 hϖ.ne_zero)
      PowerSeries.X_ne_zero ((injective_iff_map_eq_zero _).1 inj _ ?_)
    have hz' : F.toLaurent (PowerSeries.C ϖ * PowerSeries.X) ∈ z.asIdeal := hz
    rwa [show z.asIdeal = ⊥ from @Ideal.eq_bot_of_prime _ _ _ z.2] at hz')
  let j : F.O →+* LaurentSeries ↥F.K := F.toLaurent.comp PowerSeries.C
  have hj : Function.Injective j := inj.comp PowerSeries.C_injective
  have hg : g.comp (Z.i.c.V W).subtype = j.comp t.b := by
    have e₁ : spMap (g.comp (Z.i.c.V W).subtype) = spMap (j.comp t.b) := by
      rw [spMap_comp, ← hy, Category.assoc, ← (Y Z.i).j_s, ← Category.assoc, hyj, Category.assoc, hχ.1, spMap_comp,
        spMap_comp, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e₁)
  have hv : ∀ τ a, g (embK Z.i.c τ a) = j (ρ τ a) := fun τ a => by
    have e₁ : ρ τ a = t.b (IntModelExists.embV Z.i.c W τ a) := IsFractionRing.injective F.O (FractionRing F.O)
      ((RingHom.congr_fun (hρ τ) a).trans (RingHom.congr_fun hb (IntModelExists.embV Z.i.c W τ a)))
    rw [e₁]
    exact RingHom.congr_fun hg (IntModelExists.embV Z.i.c W τ a)
  obtain ⟨t', ⟨m⟩⟩ := exists_sab (spMap F.toLaurent) Wt.t
  obtain ⟨u, hu, hbas⟩ := GlobalTheory.T.constant_arc_eigenbasis_flat_baseChange globalFns_holds E H Dw _ _ _ _ _ (Y Z.i) F.O _ _ χ Wt ρ t.e he _ F.toLaurent
    (IntModelExists.flat_of_injective _ hj) t' m
  choose w hw hw' using hu
  have fr : IsFrame (Dw := Dw) t' g (𝟙 _) fun τ k => (u τ k).left := isFrame_id t' g u (by simpa only [hv] using hbas)
  have fr₁ := (Cht.frameMove E H Dw _ _ Z.i.c Z.i.c _ _ Wt.t t' _ m _ g g _ fun _ _ => rfl).1 _ fr
  have fr₂ := (Cht.frameMove E H Dw _ _ Z.i.c Z.i.c _ _ (Y Z.i).t Wt.t _ Wt.m _ g g _ fun _ _ => rfl).1 _ fr₁
  rw [Category.id_comp, ← hyj] at fr₂
  obtain ⟨x, ⟨hx, hfl⟩, -⟩ := Z.bij _ g y hy _ fr₂
  exact ⟨x, _, h, ϖ, χ, Wt, w, hϖ, hχ, hw, hx.trans hyj, fun τ k => by rw [hw', Category.assoc], hfl⟩

theorem exists_isSeries (hp : p ≠ 0) (hY : (Y Z.i).N4) (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {γ : t.Forms}
    (h : γ ∈ t.Dir) : ∃ r, IsSeries t T f γ r := by
  obtain ⟨x, v, hx⟩ := exists_isArc t hY h
  obtain ⟨_, _, _, _, _, -, -, -, -, -, hfl⟩ := id hx
  haveI : CharZero (LaurentSeries ↥F.K) := charZero_of_injective_ringHom (HahnSeries.C (Γ := ℤ) (R := ↥F.K)).injective
  obtain ⟨r, hr, -⟩ := T.existsUnique_isVal hty f (le_preimage_genO hp x) hfl
  exact ⟨r, x, v, hx, hr⟩

variable (Z) in

structure CuspRec : Type where

  F : DVF p

  m : ℕ

  dir : Set (Fin m → ℤ)

  arc : (Fin m → ℤ) → (Sp (LaurentSeries ↥F.K) ⟶ Z.X) → Vecs Dw (Y Z.i).t (LaurentSeries ↥F.K) → Prop

  ex : ∃ (t : CuspOn Z F) (ε : t.Forms ≃ₗ[ℤ] (Fin m → ℤ)), (∀ γ, ε γ ∈ dir ↔ γ ∈ t.Dir) ∧
    ∀ γ x v, arc (ε γ) x v ↔ IsArc t γ x v

def CuspRec.cusp (s : CuspRec Z) : CuspOn Z s.F := s.ex.choose

def CuspRec.of : CuspRec Z where
  F := F
  m := Module.finrank ℤ t.Forms
  dir := (Module.finBasis ℤ t.Forms).equivFun.symm ⁻¹' t.Dir
  arc γ := IsArc t ((Module.finBasis ℤ t.Forms).equivFun.symm γ)
  ex := ⟨t, (Module.finBasis ℤ t.Forms).equivFun, fun γ => by rw [Set.mem_preimage, LinearEquiv.symm_apply_apply],
    fun γ x v => by rw [LinearEquiv.symm_apply_apply]⟩

theorem CuspRec.exists_equiv : ∃ ε : (CuspRec.of t).cusp.Forms ≃ₗ[ℤ] t.Forms,
    (∀ γ, ε γ ∈ t.Dir ↔ γ ∈ (CuspRec.of t).cusp.Dir) ∧ ∀ γ x v, IsArc t (ε γ) x v ↔ IsArc (CuspRec.of t).cusp γ x v := by
  obtain ⟨ε, h₁, h₂⟩ := (CuspRec.of t).ex.choose_spec
  exact ⟨ε.trans (Module.finBasis ℤ t.Forms).equivFun.symm, h₁, h₂⟩

theorem CuspRec.exists_fjNorm_eq : ∃ ε : t.Chr ≃ₗ[ℤ] (CuspRec.of t).cusp.Chr,
    ∀ (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) (M : Z.X.Modules) (T : GrTriv Z e M) (f : Γ(M, Z.genO)) (χ : t.Chr),
      fjNorm (CuspRec.of t).cusp T f (ε χ) = fjNorm t T f χ := by
  obtain ⟨ε, h₁, h₂⟩ := CuspRec.exists_equiv t
  exact ⟨ε.dualMap, fun e M T f χ => coefNorm_equiv ε h₁
    (fun γ r => exists_congr fun x => exists_congr fun v => and_congr_left' (h₂ γ x v)) χ⟩

end Arcs

example {K : Type} [NormedField K] (a : K) :
    coefNorm {n : ℤ | 0 < n} (fun γ r => r = HahnSeries.single γ a) LinearMap.id = ‖a‖ ∧
      coefNorm {n : ℤ | 0 < n} (fun γ r => r = HahnSeries.single γ a) (2 • LinearMap.id) = 0 := by
  classical
  have h := (isExpansion_single (P := {n : ℤ | 0 < n}) (χ₀ := LinearMap.id) (fun _ h => le_of_lt h) a).coefNorm_eq
    isFat_pos ⟨1, show (0 : ℤ) < 1 from one_pos⟩ fun _ _ => ⟨_, rfl⟩
  refine ⟨(h _).trans (by simp), (h _).trans ?_⟩
  rw [if_neg fun e => by simpa using LinearMap.congr_fun e 1, norm_zero]

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p)

theorem nonempty_lbTriv (l : PsiT D → ℕ → ℤ) : Nonempty (GrTriv ct.YY (ct.expo l) (ct.Lb l).toMod) := by
  have h := GradedPieces.exists_isGrLB _ _ _ _ p ct.W ct.hp ct.hW _ _ ct.YY ct.isYY.2.1 (ct.expo l)
  unfold At.Lb
  rw [dif_pos h]
  exact nonempty_grTriv ct.hp ct.hW h.choose_spec

def lbTriv (l : PsiT D → ℕ → ℤ) : GrTriv ct.YY (ct.expo l) (ct.Lb l).toMod := (nonempty_lbTriv ct l).some

theorem charts_YY : (ct.Y ct.YY.i).N4 := ((S.sys.clauses p ct.W ct.hp ct.hW).2 _).2.2

end GlobalTheory.LocM.FJ

namespace GlobalTheory.LocM

open FJ

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def fjTrue (ct : At S κ p) : FJSt ct where
  FJd := CuspRec ct.YY
  Chr s := s.cusp.Chr
  fjN l f s χ := fjNorm s.cusp (lbTriv ct l) f χ

namespace FJ

variable {ct : At S κ p} {l : PsiT D → ℕ → ℤ} {f : ct.Sec (ct.Lb l)}

theorem fjN_le_iff (B : ℝ) : (∀ s χ, (fjTrue ct).fjN l f s χ ≤ B) ↔
    ∀ (F : DVF p) (t : CuspOn ct.YY F) (χ : t.Chr), fjNorm t (lbTriv ct l) f χ ≤ B := by
  refine ⟨fun h F t χ => ?_, fun h s χ => h _ _ χ⟩
  obtain ⟨ε, hε⟩ := CuspRec.exists_fjNorm_eq t
  exact hε _ _ _ f χ ▸ h (CuspRec.of t) (ε χ)

theorem fjNorm_eq {F : DVF p} {t : CuspOn ct.YY F} {c : t.Chr → ↥F.K} (h : IsFJ t (lbTriv ct l) f c) (χ : t.Chr) :
    fjNorm t (lbTriv ct l) f χ = ‖c χ‖ :=
  h.coefNorm_eq t.isFat_dir t.dir_nonempty (fun _ => exists_isSeries t _ f ct.hp.ne_zero (charts_YY ct) ct.isYY.2.1.1) χ

theorem IsFJ.unique {F : DVF p} {t : CuspOn ct.YY F} {c c' : t.Chr → ↥F.K} (h : IsFJ t (lbTriv ct l) f c)
    (h' : IsFJ t (lbTriv ct l) f c') : c = c' :=
  IsExpansion.unique h h' t.isFat_dir t.dir_nonempty fun _ => exists_isSeries t _ f ct.hp.ne_zero (charts_YY ct) ct.isYY.2.1.1

theorem coefSet_nonempty_of_nonneg {F : DVF p} (t : CuspOn ct.YY F) {χ : t.Chr} (h : Nonneg t.Dir χ) :
    (coefSet t.Dir (IsSeries t (lbTriv ct l) f) χ).Nonempty :=
  coefSet_nonempty t.isFat_dir t.dir_nonempty (fun _ => exists_isSeries t _ f ct.hp.ne_zero (charts_YY ct) ct.isYY.2.1.1) h

theorem fjN_eq_zero (s : (fjTrue ct).FJd) (χ : (fjTrue ct).Chr s) (γ : s.cusp.Forms)
    (hγ : ∀ y, y ≠ 0 → 0 < (γ : LinearMap.BilinForm ℤ s.cusp.a.D₀.X) y y) (h : (show s.cusp.Chr from χ) γ < 0) :
    (fjTrue ct).fjN l f s χ = 0 :=
  coefNorm_eq_zero fun h' => h.not_ge ((nonneg_admissible_iff_positiveDefinite _).1 h' γ hγ)

theorem fjN_le_one (h : ∀ (F : DVF p) (t : CuspOn ct.YY F) γ r, IsSeries t (lbTriv ct l) f γ r →
    r ∈ F.toLaurent.range) (s : (fjTrue ct).FJd) (χ : (fjTrue ct).Chr s) : (fjTrue ct).fjN l f s χ ≤ 1 :=
  coefNorm_le zero_le_one fun γ _ r hr n => by
    obtain ⟨g, rfl⟩ := h _ _ γ r hr
    exact s.F.norm_coeff_toLaurent g n

theorem nonempty_fjd {F : DVF p} {b : ct.YY.i.c.V ct.W →+* F.O} (hb : Function.Injective b)
    (a : ArcIn S.Dw ct.YY.i.l (ct.YY.i.c.V ct.W).subtype F.O b) : Nonempty (fjTrue ct).FJd :=
  ⟨CuspRec.of (exists_cusp (charts_YY ct) hb a).choose⟩

theorem nonempty_fjd_hyp (h : S.Dw = HostModel.hypDatum A.H) : Nonempty (fjTrue ct).FJd := by
  obtain ⟨F, b, hb⟩ := exists_dvf ct.YY.i.c ct.hp ct.hW
  obtain ⟨io, hio⟩ := exists_io hb
  have : Nonempty (ArcIn S.Dw ct.YY.i.l (ct.YY.i.c.V ct.W).subtype F.O b) := by
    generalize ct.YY.i = i at *
    rw [h]
    exact ⟨toricIn b io hio⟩
  exact nonempty_fjd hb this.some

end FJ

end GlobalTheory.LocM
