import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GaloisHolds

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def Base (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] : Prop := AdmBase R (maximalIdeal R) ∧ CharZero R

def FinExt {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') : Prop :=
  AdmBase R' (maximalIdeal R') ∧ Function.Injective ρ ∧ ρ.Finite

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

def Has (D : DegData R (maximalIdeal R)) : Prop :=
  ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Sp (FractionRing R))),
    IsSemiAbelian G ∧ Nonempty (Unif (maximalIdeal R) D A G)

def HasFin (D : DegData R (maximalIdeal R)) : Prop :=
  ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')),
    FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ Has D'

def EvenOn {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G) : Prop :=
  ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
    (Q₀ : GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X) (P₀ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G)),
    GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₀ P ∧ ∃ σ : GlobalTheory.UU.CubTriv P₀.c Q₀.i, σ.Even

end

structure Modif (R : Type) [CommRing R] [IsDomain R] where

  S : Scheme.{0}

  π : S ⟶ Sp R
  proper : IsProper π
  integral : IsIntegral S

  gp : Sp (FractionRing R) ⟶ S
  gp_π : gp ≫ π = jK R
  dominant : IsDominant gp

def Modif.self (R : Type) [CommRing R] [IsDomain R] : Modif R where
  S := Sp R
  π := 𝟙 _
  proper := inferInstance
  integral := inferInstance
  gp := jK R
  gp_π := Category.comp_id _
  dominant := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]; exact bot_le)⟩

section

variable {R : Type} [CommRing R] [IsDomain R]

def IsFactor (D D' : DegPre R) : Prop :=
  letI := D.P.isAb.comm
  letI := D'.P.isAb.comm
  ∃ (O : Type) (_ : Ring O) (_ : StarRing O) (_ : Module O D'.X) (o : D'.OAct O) (e f : O)
    (inc : D.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D.P.A) (xi : D.X →+ D'.X) (xp : D'.X →+ D.X)
    (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D'.P.A D'.P.L).pull
      (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o.onB.act f) : G2 D.P.A ⟶ G2 D'.P.A).left)),
    e * e = e ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o.onB.act e ∧
    (∀ y, xp (xi y) = y) ∧ (∀ z, xi (xp z) = e • z) ∧ (∀ y, D'.c (xi y) = D.c y ≫ inc) ∧
    (Function.Injective (fun y => star e • f • xi y) ∧ ∀ z, ∃ y, star e • z = star e • f • xi y) ∧ w.IsGen ∧
    ∀ a b z J J', Good D'.P.L z J → Good D.P.L z J' →
      val (D.tau a b) (𝟙 _) z J' =
        GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J J' *
          val (D'.tau (xi a) (f • xi b)) (𝟙 _) z J

def PelOK {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dm : Datum H) (D : DegPre R)
    [Module (𝓞 E) D.X] (o : letI := H.starRing; D.OAct (𝓞 E)) : Prop :=
  letI := H.starRing
  Dm.p = Dm.q ∧ 1 ≤ Dm.p ∧ TraceFormTwistIso D o H.w0 ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
      (∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct o.onB.toRingAct)
        (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) τ n ∧ n + Module.finrank (𝓞 E) D.X = Dm.p) ∧
      ∀ ζ : ℕ → Fˣ, (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) →
        ∃ I : TateIsoQ Dm D o F, I.ζ = ζ

end

structure LabCover {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) extends Modif R where

  G : Over S
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G

  P : GlobalTheory.UU.CP G

  A : PolAV (Sp (FractionRing R))

  α : A.A.left ⟶ G.left
  α_cart : IsGrpPullback A.A G gp α
  α_lb : LBIso A.L (P.L.L.pull α)

  n : ℕ
  n_prime : n.Prime
  n_odd : Odd n
  n_unit : IsUnit (n : R)

  lab : ∀ j : ℕ, QkPt D.toPre (AlgebraicClosure (FractionRing R)) (n ^ j) →
    (TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A.A)
  trait : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (D' : DegData W' (maximalIdeal W'))
      (A' : PolAV (Sp (FractionRing W'))) (U' : Unif (maximalIdeal W') D' A' G')
      (hD : IsPullDeg (io.comp φ) D.toPre D'.toPre),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      LBIso U'.LG.L (P.L.L.pull β) ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W') F] [Algebra (FractionRing R) F]
        (em : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] F),
        (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W') F (algebraMap W' _ (io (φ r)))) →
        ∀ (j : ℕ) (p : QkPt D.toPre (AlgebraicClosure (FractionRing R)) (n ^ j)) (p₁ : QkPt D.toPre F (n ^ j))
          (p' : QkPt D'.toPre F (n ^ j)) (x' : TFK (R := W') F ⟶ A'.A),
          QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF (io.comp φ) hD F p₁.g p'.g →
          x'.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK W') ≫ β = spMap em.toRingHom ≫ (lab j p).left ≫ α →
          QkToAkU U'.toUnifPre F (n ^ j) p' x'

attribute [instance] LabCover.grp LabCover.comm

section Inhabitants

def Modif.ofSubalgebra {R : Type} [CommRing R] [IsDomain R] (B : Subalgebra R (FractionRing R)) [Module.Finite R B] :
    Modif R where
  S := Sp B
  π := spMap (algebraMap R B)
  proper := by
    have : IsFinite (spMap (algebraMap R B)) :=
      (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R B))).2 (RingHom.finite_algebraMap.2 inferInstance)
    infer_instance
  integral := inferInstance
  gp := spMap B.val.toRingHom
  gp_π := (Spec.map_comp (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom B.val.toRingHom)).symm
  dominant := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical B.val.toRingHom).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)⟩

theorem Modif.exists_not_isIso {R : Type} [CommRing R] [IsDomain R] (h : ¬ IsIntegrallyClosed R) :
    ∃ M : Modif R, ¬ IsIso M.π := by
  rw [isIntegrallyClosed_iff (FractionRing R)] at h
  push Not at h
  obtain ⟨x, hx, hn⟩ := h
  have : Module.Finite R (Algebra.adjoin R {x}) := Algebra.finite_adjoin_simple_of_isIntegral hx
  refine ⟨Modif.ofSubalgebra (Algebra.adjoin R {x}), fun hi => ?_⟩
  have hi' : IsIso (Spec.map (CommRingCat.ofHom (algebraMap R (Algebra.adjoin R {x})))) := hi
  have hb : Function.Bijective (algebraMap R (Algebra.adjoin R {x})) :=
    (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom (algebraMap R (Algebra.adjoin R {x})))).1
      (isIso_SpecMap_iff.1 hi' |> fun e => (ConcreteCategory.isIso_iff_bijective _).2 e)
  obtain ⟨y, hy⟩ := hb.2 ⟨x, Algebra.self_mem_adjoin_singleton R x⟩
  exact hn y (congrArg Subtype.val hy)

theorem Modif.exists_nontrivial : ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (M : Modif R), ¬ IsIso M.π := by
  have hns : Zsqrtd.Nonsquare 8 := ⟨fun n hn => by
    have : n ≤ 2 := by nlinarith
    interval_cases n <;> omega⟩
  refine ⟨ℤ√((8 : ℕ) : ℤ), inferInstance, inferInstance, Modif.exists_not_isIso fun h => ?_⟩
  have hd : (2 : ℤ√((8 : ℕ) : ℤ)) ^ 2 ∣ Zsqrtd.sqrtd ^ 2 := ⟨2, by decide⟩
  obtain ⟨c, hc⟩ := (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hd
  have := congrArg Zsqrtd.im hc
  simp at this
  omega

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem Has.labCover (hR : Base R) {D : DegData R (maximalIdeal R)} (h : Has D) (n : ℕ) (hn : n.Prime) (ho : Odd n)
    (hu : IsUnit (n : R)) : ∃ C : LabCover D, C.toModif = Modif.self R ∧ C.n = n := by
  obtain ⟨G, iG, cG, A, hG, ⟨U⟩⟩ := h
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have := hR.2
  have hk : ∀ j, 1 ≤ n ^ j := fun j => Nat.one_le_pow _ _ hn.pos
  choose f hf using fun j =>
    GlobalTheory.TorsionIso.torsion_clause R _ hR.1 D A G hG U (AlgebraicClosure (FractionRing R)) (n ^ j) (hk j)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  refine ⟨{ toModif := Modif.self R
            G := G
            grp := iG
            comm := cG
            semi := hG
            P := GlobalTheory.ValueForm.modelCP U.toUnifPre hL.globalFns
            A := A
            α := U.gen.inv.left ≫ pullback.fst G.hom (jK R)
            α_cart := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
            α_lb := LBIso.chartPull (h := U.gen.inv.left) (chartPullSec A.L _ _ hgi)
              (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => rfl) U.ext
            n := n
            n_prime := hn
            n_odd := ho
            n_unit := hu
            lab := f
            trait := ?_ }, rfl, rfl⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain rfl : ξ = spMap φ := (Category.comp_id ξ).symm.trans hξ
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨D', hD, A', U', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR.1 hW' φ hφ (map_maximalIdeal_le φ) hG U
  have hb : (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ) =
      pullback.fst G.hom (specOf φ) := Category.id_comp _
  refine ⟨W, _, inferInstance, inferInstance, RingHom.id W, (Over.pullback (specOf φ)).obj G, inferInstance, inferInstance,
    (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ), D', A', U', hD, hW,
    Function.injective_id, RingHom.Finite.id W, ?_, ⟨hP.lg.choose, hP.lg.choose_spec.1⟩, ?_⟩
  · refine (isGrpPullback_pullback G (spMap φ)).congr ?_ hb.symm
    show spMap φ = Spec.map (𝟙 _) ≫ spMap φ
    rw [Spec.map_id, Category.id_comp]
  · intro F _ _ _ _ em hF j p p₁ p' x' h₁ h₂ h₃ h₄
    obtain ⟨-, hx, hgal⟩ := GlobalTheory.UT.Cl.galois_holds R _ hR.1 D A G hG U _ F em (n ^ j) (hk j) p
    obtain ⟨x, hx⟩ := hx (f j p)
    refine h5.qkBaseChange R W _ _ hR.1 hW' φ D A G U _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hP
      F hF (n ^ j) (hk j) p₁ x p' x' h₂ h₃ ?_ ((hgal p₁ (f j p) x h₁ hx).1 (((hf j).1.1 p _).2 rfl))
    rw [hx, Category.assoc]
    exact h₄

theorem Has.hasFin (hR : Base R) {D : DegData R (maximalIdeal R)} (h : Has D) : HasFin D := by
  have := hR.2
  obtain ⟨G, iG, cG, A, hG, ⟨U⟩⟩ := h
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨D', hD, A', U', -⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR.1 hR.1 (RingHom.id R) Function.injective_id (by simp) hG U
  exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, D', ⟨hR.1, Function.injective_id, RingHom.Finite.id R⟩,
    ⟨hD⟩, _, inferInstance, inferInstance, A', IsSemiAbelian.pullback _ G hG, ⟨U'⟩⟩

theorem base_powerSeries : Base (PowerSeries ℚ) := by
  have hc : IsAdicComplete (maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  exact ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, algebraRat.charZero _⟩

theorem LabCover.exists_toric_rank_one : ∃ D : DegData (PowerSeries ℚ) (maximalIdeal (PowerSeries ℚ)),
    Module.finrank ℤ D.toPre.X = 1 ∧ Has D ∧ HasFin D ∧ ∃ C : LabCover D, C.n = 3 := by
  obtain ⟨A, G, _, _, D, U, hG, -, hr, -⟩ := GlobalTheory.TateUnif.exists_unif_rank_one
  have hu : IsUnit ((3 : ℕ) : PowerSeries ℚ) := by
    rw [← map_natCast (algebraMap ℚ (PowerSeries ℚ))]
    exact (IsUnit.mk0 _ (by norm_num)).map _
  have h : Has D := ⟨G, _, _, A, hG, ⟨U⟩⟩
  obtain ⟨C, -, h₂⟩ := h.labCover base_powerSeries 3 Nat.prime_three (by decide) hu
  exact ⟨D, hr, h, h.hasFin base_powerSeries, C, h₂⟩

end Inhabitants

end GlobalTheory.Mum
