import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPointLiftFiniteSurjectiveMorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalNormalDomainFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionGenericPointFractionMeetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalCompactificationExtensionOfCoverStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MinExt

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp]

theorem exists_factor {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : G''.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (n : IsGrpPullback G'' G k ψ) (e : g ≫ f = k) :
    ∃ φ', IsGrpPullback G'' G' g φ' := by
  subst e
  have w : ψ ≫ G.hom = (G''.hom ≫ g) ≫ f := by rw [n.1.w, Category.assoc]
  exact ⟨h.1.lift ψ (G''.hom ≫ g) w, h.cancel (n.congr rfl (h.1.lift_fst _ _ w).symm) (h.1.lift_snd _ _ w)⟩

theorem exists_ext_of_minAt5 : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z), MinAt5 F z i OZ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ F.X) (α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left), IsGenFibre F y α₁ → ∀ b : cycAway n →+* R, y ≫ F.s = jK R ≫ spMap b → ∃ a : Sp R ⟶ Z, jK R ≫ a = y ≫ i := by
  intro g n F Z z i OZ h R _ _ _ _ _ _ G₁ _ _ hG₁ y α₁ hα₁ b hyb
  obtain ⟨o', _, β, S', s', U, c, π, G, _, e, _, N, ⟨-, hz, -, hiz, -, hOZ, hamp⟩,
    ⟨-, -, -, -, -, hcfin, hcsurj, hUπ, -, -, hπp, -⟩, ⟨hGsa, hGsm, he⟩, ⟨-, hL⟩⟩ := h
  haveI := hcfin
  haveI := hcsurj
  haveI := hπp
  haveI : IsProper z := by
    obtain ⟨m, j, hj, rfl⟩ := hz
    have := isProper_str (cycAway n) m
    infer_instance
  obtain ⟨K', _, _, _, y', hy'⟩ := GlobalTheory.T.exists_fieldPoint_lift_finite_surjective_morphism U.toScheme F.X c (FractionRing R) y
  obtain ⟨R', _, _, _, _, _, ρ, eR, -, hinj, hcomp, hmeet⟩ := GlobalTheory.T.exists_local_normal_domain_finite_extension R K'
  haveI : CharZero R' := charZero_of_injective_ringHom hinj
  let gam : FractionRing R →+* FractionRing R' := (eR.symm : K' →+* FractionRing R').comp (algebraMap (FractionRing R) K')
  have E1 : spMap gam = spMap (eR.symm : K' →+* FractionRing R') ≫ spMap (algebraMap (FractionRing R) K') :=
    spMap_comp_eq _ _
  have E2 : spMap gam ≫ jK R = jK R' ≫ spMap ρ := by
    change spMap gam ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ
    rw [← spMap_comp_eq, ← spMap_comp_eq]
    congr 1
    ext r
    simp only [RingHom.comp_apply, gam]
    rw [← hcomp r]
    simp
  let yy : Sp (FractionRing R') ⟶ S' := spMap (eR.symm : K' →+* FractionRing R') ≫ y' ≫ U.ι
  have E4 : spMap gam ≫ y = (spMap (eR.symm : K' →+* FractionRing R') ≫ y') ≫ c := by
    rw [Category.assoc, hy', E1, Category.assoc]
  have E3 : yy ≫ π = spMap gam ≫ y ≫ i := by
    simp only [yy, Category.assoc]
    rw [hUπ, ← Category.assoc y' c i, hy', E1]
    simp only [Category.assoc]
  let G₁' := (Over.pullback (spMap ρ)).obj G₁
  have hG₁' : IsSemiAbelian G₁' := IsSemiAbelian.pullback (spMap ρ) G₁ hG₁
  haveI : IsCommMonObj G₁' := hG₁'.comm
  have h1 := ((isGrpPullback_pullback G₁' (jK R')).comp (isGrpPullback_pullback G₁ (spMap ρ))).congr E2.symm rfl
  obtain ⟨φ1, hφ1⟩ := exists_factor (isGrpPullback_pullback G₁ (jK R)) h1 rfl
  have h2 := (hφ1.comp hα₁).congr E4 rfl
  obtain ⟨φ2, hφ2⟩ := exists_factor (isGrpPullback_pullback F.univ.A c) h2 rfl
  have h3 := (hφ2.comp he).congr (Category.assoc _ _ _) rfl
  have hyz : yy ≫ π ≫ z = jK R' ≫ spMap (ρ.comp b) := by
    rw [← Category.assoc, E3, Category.assoc, Category.assoc, hiz, hyb, ← Category.assoc, E2, spMap_comp_eq,
      Category.assoc]
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_minimalCompactification_extension_of_cover (cycAway n) g Z S' z π OZ hOZ hamp G N hGsa hGsm hL R' (ρ.comp b) G₁' hG₁' yy _ h3 hyz
  have hmeet' : ∀ (x : FractionRing R) (w : R'), algebraMap R' _ w = gam x → ∃ r : R, algebraMap R _ r = x :=
    fun x w hw => hmeet x w (by rw [hw]; simp [gam])
  exact GlobalTheory.T.exists_extension_generic_point_fraction_meet Z R R' gam hmeet' (y ≫ i) a' (ha'.trans E3)

end GlobalTheory.MinExt
