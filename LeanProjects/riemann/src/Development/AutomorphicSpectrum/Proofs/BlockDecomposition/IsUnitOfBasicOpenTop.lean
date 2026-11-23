import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseCompat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToH0BijectiveOfInitial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHBijOfRes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfEtalePoly
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCohomologyOfFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeUniversal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeFiltrationQuotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeTorsionFree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdSomeZero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.B CrystallineSemistableComparison.Pb DividedPowers CompanionTheory.KM.G4 GlobalTheory.CompanionTheory.KMGys ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.KMGys.Trace

namespace GlobalTheory.CompanionTheory.KMVan

section Sc

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']

structure Sc (Φ : PDF R C) (Λ : Type) [CommRing Λ] where
  ρ : ∀ T : C, Λ →+* Φ.A.obj T
  nat : ∀ {T T' : C} (φ : T ⟶ T') (a : Λ), (Φ.A.map φ).hom (ρ T a) = ρ T' a

variable {Φ : PDF R C} {Λ : Type} [CommRing Λ]

def Sc.A (S : Sc Φ Λ) : C ⥤ CommAlgCat.{0} Λ where
  obj T := letI := (S.ρ T).toAlgebra; CommAlgCat.of Λ (Φ.A.obj T)
  map {T T'} f :=
    letI := (S.ρ T).toAlgebra; letI := (S.ρ T').toAlgebra
    CommAlgCat.ofHom { (Φ.A.map f).hom.toRingHom with commutes' := S.nat f }
  map_id T := by
    letI := (S.ρ T).toAlgebra
    ext x
    exact congrArg (fun g => g.hom x) (Φ.A.map_id T)
  map_comp {T T' T''} f g := by
    letI := (S.ρ T).toAlgebra; letI := (S.ρ T'').toAlgebra
    ext x
    exact congrArg (fun g => g.hom x) (Φ.A.map_comp f g)

def Sc.site (S : Sc Φ Λ) : PDF Λ C where
  A := S.A
  J := ⟨fun T => Φ.J.S T, fun φ _ hx => Φ.J.map_mem φ hx⟩
  dp {T} k x := Φ.dp (T := T) k x
  dp_zero := Φ.dp_zero
  dp_one := Φ.dp_one
  dp_zero_right := Φ.dp_zero_right
  dp_add := Φ.dp_add
  dp_map φ := Φ.dp_map φ

def Sc.poly (S : Sc Φ Λ) (Q : Poly Φ) : Poly S.site where
  P := Q.P
  j := Q.j
  X := Q.X
  X_mem := Q.X_mem
  univ := Q.univ
  span := Q.span

def Sc.frame (S : Sc Φ Λ) {d : ℕ} (E : Frame Φ d) : Frame S.site d where
  D := E.D
  ne := E.ne
  τ := E.τ
  mem := E.mem
  add := E.add
  nat := E.nat
  bij := E.bij

def Sc.res (S : Sc Φ Λ) (G : C' ⥤ C) : Sc (Φ.res G) Λ where
  ρ T := S.ρ (G.obj T)
  nat φ a := S.nat (G.map φ) a

def Sc.loc (S : Sc Φ Λ) (Y : Λ) (G : C' ⥤ C) (hu : ∀ T, IsUnit (S.ρ (G.obj T) Y)) :
    Sc (Φ.res G) (Localization.Away Y) where
  ρ T := IsLocalization.Away.lift Y (hu T)
  nat {T T'} φ a := by
    have e : ((Φ.A.map (G.map φ)).hom.toRingHom).comp (IsLocalization.Away.lift Y (hu T)) =
        IsLocalization.Away.lift (S := Localization.Away Y) Y (hu T') := by
      refine IsLocalization.ringHom_ext (Submonoid.powers Y) (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq]
      exact S.nat (G.map φ) a
    exact RingHom.congr_fun e a

def Sc.mor (S : Sc Φ Λ) (Y : Λ) (G : C' ⥤ C) (hu : ∀ T, IsUnit (S.ρ (G.obj T) Y)) :
    SMor S.site (S.loc Y G hu).site (algebraMap Λ (Localization.Away Y)) where
  G := G
  ρ T := RingHom.id _
  comm T a := (IsLocalization.Away.lift_eq Y (hu T) a).symm
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

end Sc

end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section Loc
open TensorProduct
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

abbrev Fs (S : Sc Φ Λ) : C ⥤ ModuleCat.{0} Λ := sq (IdF.top S.site.A) (IdF.bot S.site.A)

theorem le_top' (S : Sc Φ Λ) (Y : Λ) (G : C' ⥤ C) (hu : ∀ T, IsUnit (S.ρ (G.obj T) Y)) (c : Localization.Away Y) :
    (S.mor Y G hu).LeC c (IdF.top S.site.A) (IdF.top (S.loc Y G hu).site.A) := fun _ _ _ => trivial

theorem le_bot' (S : Sc Φ Λ) (Y : Λ) (G : C' ⥤ C) (hu : ∀ T, IsUnit (S.ρ (G.obj T) Y)) (c : Localization.Away Y) :
    (S.mor Y G hu).LeC c (IdF.bot S.site.A) (IdF.bot (S.loc Y G hu).site.A) := fun T x hx => by
  have h : x = 0 := hx
  subst h
  rw [map_zero, mul_zero]
  exact Ideal.zero_mem _

def mc (S : Sc Φ Λ) (Y : Λ) (G : C' ⥤ C) (hu : ∀ T, IsUnit (S.ρ (G.obj T) Y)) (c : Localization.Away Y) :
    CH.Mor (Fs S) (Fs (S.loc Y G hu)) (algebraMap Λ (Localization.Away Y)) :=
  (S.mor Y G hu).sqC c (le_top' S Y G hu c) (le_bot' S Y G hu c)

end Loc
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct

theorem tens_of_loc {Λ : Type} [CommRing Λ] (Y : Λ) {M M' : Type*} [AddCommGroup M] [Module Λ M] [AddCommGroup M']
    [Module (Localization.Away Y) M'] (f : Localization.Away Y → M → M')
    (f0 : M →+ M') (hf0 : ∀ n x, f n x = n • f0 x) (hs : ∀ (a : Λ) x, f0 (a • x) = algebraMap Λ (Localization.Away Y) a • f0 x)
    (h0 : ∀ x, f0 x = 0 → ∃ n : ℕ, Y ^ n • x = 0)
    (h1 : ∀ y, ∃ (n : ℕ) (x : M), f0 x = algebraMap Λ (Localization.Away Y) (Y ^ n) • y) :
    Tens Λ (N := fun _ : Unit => Localization.Away Y) (M := fun _ => M) (M' := M') fun _ n x => f n x := by
  letI : Module Λ M' := Module.compHom M' (algebraMap Λ (Localization.Away Y))
  haveI : IsScalarTower Λ (Localization.Away Y) M' := ⟨fun a b x => by
    change (a • b) • x = algebraMap Λ (Localization.Away Y) a • b • x
    rw [Algebra.smul_def, mul_smul]⟩
  let g : M →ₗ[Λ] M' := { f0 with map_smul' := fun a x => hs a x }
  have hunit : ∀ x : Submonoid.powers Y, IsUnit (algebraMap Λ (Module.End Λ M') x) := by
    rintro ⟨_, n, rfl⟩
    have hu : IsUnit (algebraMap Λ (Localization.Away Y) (Y ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit Y).pow n
    obtain ⟨u, hu⟩ := hu
    refine (Module.End.isUnit_iff _).2 ⟨fun a b h => ?_, fun b => ⟨(↑u⁻¹ : Localization.Away Y) • b, ?_⟩⟩
    · have h' : algebraMap Λ (Localization.Away Y) (Y ^ n) • a = algebraMap Λ (Localization.Away Y) (Y ^ n) • b := h
      rw [← hu] at h'
      have h2 := congrArg (fun z => (↑u⁻¹ : Localization.Away Y) • z) h'
      simp only [smul_smul, Units.inv_mul, one_smul] at h2
      exact h2
    · change algebraMap Λ (Localization.Away Y) (Y ^ n) • (↑u⁻¹ : Localization.Away Y) • b = b
      rw [← hu, smul_smul, Units.mul_inv, one_smul]
  haveI : IsLocalizedModule (Submonoid.powers Y) g :=
    { map_units := hunit
      surj := fun y => by
        obtain ⟨n, x, hx⟩ := h1 y
        exact ⟨⟨x, ⟨Y ^ n, n, rfl⟩⟩, hx.symm⟩
      exists_of_eq := fun {x y} h => by
        have : f0 (x - y) = 0 := by rw [map_sub]; exact sub_eq_zero.2 h
        obtain ⟨n, hn⟩ := h0 _ this
        refine ⟨⟨Y ^ n, n, rfl⟩, ?_⟩
        change Y ^ n • x = Y ^ n • y
        rw [smul_sub] at hn
        exact sub_eq_zero.1 hn }
  have hb := IsLocalizedModule.isBaseChange (Submonoid.powers Y) (Localization.Away Y) g
  refine ⟨(LinearEquiv.funUnique Unit Λ (Localization.Away Y ⊗[Λ] M)).toAddEquiv.trans hb.equiv.toAddEquiv, fun i n x => ?_⟩
  have e : (LinearEquiv.funUnique Unit Λ (Localization.Away Y ⊗[Λ] M)) (Pi.single i (n ⊗ₜ x)) = n ⊗ₜ x := by
    simp [LinearEquiv.funUnique, Pi.single]
  change hb.equiv ((LinearEquiv.funUnique Unit Λ (Localization.Away Y ⊗[Λ] M)) (Pi.single i (n ⊗ₜ x))) = f n x
  rw [e, IsBaseChange.equiv_tmul, hf0]
  rfl
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct
section D
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

theorem tensD (S : Sc Φ Λ) (Y : Λ) (G : C' ⥤ C) (hu : ∀ T, IsUnit (S.ρ (G.obj T) Y)) {D : C} {D' : C'} (e : D ⟶ G.obj D')
    (h0 : ∀ x, (Φ.A.map e).hom x = 0 → ∃ n : ℕ, S.ρ _ Y ^ n * x = 0)
    (h1 : ∀ y : Φ.A.obj (G.obj D'), ∃ (n : ℕ) (x : Φ.A.obj D), (Φ.A.map e).hom x = S.ρ _ Y ^ n * y) :
    Tens Λ (N := fun _ : Unit => Localization.Away Y) (M := fun _ => (Fs S).obj D) (M' := (Fs (S.loc Y G hu)).obj D')
      fun _ n x => (mc S Y G hu n).τ D' (((Fs S).map e).hom x) := by
  have key : ∀ (n : Localization.Away Y) (a : S.site.A.obj D),
      (((mc S Y G hu n).τ D' (((Fs S).map e).hom (GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D a)) : sqM _ _ D').1) =
      Ideal.Quotient.mk _ ((S.loc Y G hu).ρ D' n * (show (Φ.res G).A.obj D' from (Φ.A.map e).hom a)) := fun n a => rfl
  refine tens_of_loc Y _ (((mc S Y G hu 1).τ D').toAddMonoidHom.comp ((Fs S).map e).hom.toAddMonoidHom) ?_ ?_ ?_ ?_
  · intro n x
    obtain ⟨a, rfl⟩ := (GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D).surjective x
    refine Subtype.ext ?_
    change _ = n • ((mc S Y G hu 1).τ D' (((Fs S).map e).hom (GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D a)) : sqM _ _ D').1
    rw [key, key, map_one, one_mul]
    rfl
  · intro b x
    change (mc S Y G hu 1).τ D' (((Fs S).map e).hom (b • x)) = _
    rw [map_smul, LinearMap.map_smulₛₗ]
    rfl
  · intro x hx
    obtain ⟨a, rfl⟩ := (GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D).surjective x
    have h2 := congrArg (fun z : sqM _ _ D' => z.1) hx
    change ((mc S Y G hu 1).τ D' (((Fs S).map e).hom (GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D a)) : sqM _ _ D').1 = 0 at h2
    rw [key, map_one, one_mul] at h2
    have h3 : (Φ.A.map e).hom a = 0 := Ideal.mem_bot.1 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
    obtain ⟨n, hn⟩ := h0 a h3
    refine ⟨n, ?_⟩
    have h4 := (GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D).map_smul (Y ^ n) a
    refine h4.symm.trans ?_
    have : Y ^ n • a = 0 := by
      rw [Algebra.smul_def]
      have e2 : algebraMap Λ (S.site.A.obj D) (Y ^ n) = S.ρ D Y ^ n := map_pow (S.ρ D) Y n
      rw [e2]
      exact hn
    rw [this, map_zero]
  · intro y
    obtain ⟨b, rfl⟩ := (GlobalTheory.CompanionTheory.LocCmp.qE (S.loc Y G hu).site.A D').surjective y
    obtain ⟨n, x, hx⟩ := h1 b
    refine ⟨n, GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D x, Subtype.ext ?_⟩
    change ((mc S Y G hu 1).τ D' (((Fs S).map e).hom (GlobalTheory.CompanionTheory.LocCmp.qE S.site.A D x)) : sqM _ _ D').1 = _
    rw [key, map_one, one_mul]
    have e3 : (S.loc Y G hu).ρ D' (algebraMap Λ (Localization.Away Y) (Y ^ n)) = S.ρ (G.obj D') Y ^ n :=
      (IsLocalization.Away.lift_eq Y (hu D') (Y ^ n)).trans (map_pow _ _ _)
    change Ideal.Quotient.mk _ (show (Φ.res G).A.obj D' from (Φ.A.map e).hom x) = _
    rw [show (show (Φ.res G).A.obj D' from (Φ.A.map e).hom x) = (S.loc Y G hu).ρ D' (algebraMap Λ (Localization.Away Y) (Y ^ n)) * (show (Φ.res G).A.obj D' from b) from hx.trans (by rw [e3])]
    rfl
end D
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
open TensorProduct
section LT
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Λ : Type} [CommRing Λ]

theorem ladder_tb (S : Sc Φ Λ) (Q : Poly Φ) (hQ : Q.Crit (fun _ => IdF.bot _) 0) :
    (S.poly Q).Ladder (fun _ => IdF.top _) (fun _ => IdF.bot _) 0 where
  le _ _ _ _ := trivial
  ca _ _ _ _ := ⟨fun _ _ => trivial, fun _ => trivial⟩
  cb _ _ T b := hQ T b

theorem local_tens (S : Sc Φ Λ) (Y : Λ) (G : C' ⥤ C) (hu : ∀ T, IsUnit (S.ρ (G.obj T) Y))
    (Q : Poly Φ) (hQ : Q.Crit (fun _ => IdF.bot _) 0) (Q₁ : Poly (Φ.res G)) (hQ₁ : Q₁.Crit (fun _ => IdF.bot _) 0)
    {d : ℕ} (E : Frame Φ d) (E₁ : Frame (Φ.res G) d) (e : E.D ⟶ G.obj E₁.D)
    (he : ∀ (i : Fin d) {T : C'} (s s' : E₁.D ⟶ T), E.τ i (e ≫ G.map s) (e ≫ G.map s') = E₁.τ i s s')
    (h0 : ∀ x, (Φ.A.map e).hom x = 0 → ∃ n : ℕ, S.ρ _ Y ^ n * x = 0)
    (h1 : ∀ y : Φ.A.obj (G.obj E₁.D), ∃ (n : ℕ) (x : Φ.A.obj E.D), (Φ.A.map e).hom x = S.ρ _ Y ^ n * y) (j : ℕ) :
    Tens Λ (N := fun _ : Unit => Localization.Away Y) (M := fun _ => CH.H (Fs S) j)
      (M' := CH.H (Fs (S.loc Y G hu)) j) fun _ n x => (mc S Y G hu n).pull j x := by
  classical
  exact GlobalTheory.CompanionTheory.LocBC.local_base_change (S.mor Y G hu) (S.poly Q) ((S.loc Y G hu).poly Q₁) (S.frame E) ((S.loc Y G hu).frame E₁) e
    (fun i {T} s s' => he i s s') (fun _ _ _ h => h) (ι := Unit) (fun _ => Localization.Away Y)
    (fun _ => LinearMap.id) (fun _ _ => IdF.top _) (fun _ _ => IdF.bot _) (fun _ => IdF.top _) (fun _ => IdF.bot _) 0
    (fun _ => ladder_tb S Q hQ) (ladder_tb (S.loc Y G hu) Q₁ hQ₁) (fun _ n _ => le_top' S Y G hu n)
    (fun _ n _ => le_bot' S Y G hu n) (fun _ _ _ => tensD S Y G hu e h0 h1) j
end LT
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section FV
variable {R : Type} [CommRing R]

theorem framed_vanish : ∀ (d : ℕ) {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ)
    (hQ : Q.Crit (fun _ => IdF.bot _) 0) (E : Frame Φ d) (n : ℕ), d < n →
    Subsingleton (CH.H (sq (IdF.top Φ.A) (IdF.bot Φ.A)) n)
  | 0, C, _, Φ, Q, hQ, E, n, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact GlobalTheory.CompanionTheory.LocGr.H_succ_subsingleton _ E.initial m
  | d + 1, C, _, Φ, Q, hQ, E, n, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hT : ∀ r, Q.Crit (fun _ => IdF.top Φ.A) r := fun r T b => ⟨fun _ _ => trivial, fun _ => trivial⟩
    have hB : ∀ r, Q.Crit (fun _ => IdF.bot Φ.A) r := fun r T b => hQ T b
    obtain ⟨β, b1, b2, b3, -⟩ := GlobalTheory.T.filtration_critical_comparison_map Q E (fun _ => IdF.top Φ.A) (fun _ => IdF.bot Φ.A) 0
      (fun _ T x _ => trivial) (hT _) (hT _) (hB _) (hB _)
    obtain ⟨i1, i2, i3⟩ := CrystallineSemistableComparison.P.ses_cochains _ β b1 b2 b3
    obtain ⟨δ, -, -, e1, -, e3⟩ := CrystallineSemistableComparison.P.les _ _ i1 i2 i3
    have hC : ∀ j, d < j → Subsingleton (CH.H (Cut.P0 Q ⋙ Cut.U E ⋙ sq (IdF.top Φ.A) (IdF.bot Φ.A)) j) := fun j hj => by
      haveI h0 : Subsingleton (CH.H (Cut.U E ⋙ sq (IdF.top Φ.A) (IdF.bot Φ.A)) j) :=
        framed_vanish d (Cut.Q1 Q) (fun Y b => hQ Y.T b) (Cut.E1 E) j hj
      exact (CrystallineSemistableComparison.P.adj (Cut.U E ⋙ sq (IdF.top Φ.A) (IdF.bot Φ.A)) (Cut.P0 Q) (Cut.inc E) (Cut.adj Q) j).2.subsingleton
    have hP : Subsingleton (CH.H (Pt.U E ⋙ sq (IdF.top Φ.A) (IdF.bot Φ.A)) (m + 1)) := by
      refine ⟨fun x y => ?_⟩
      have key : ∀ z : CH.H (Pt.U E ⋙ sq (IdF.top Φ.A) (IdF.bot Φ.A)) (m + 1), z = 0 := fun z => by
        haveI := hC (m + 1) (by omega)
        haveI := hC m (by omega)
        obtain ⟨w, rfl⟩ := (e3 m z).1 (Subsingleton.elim _ _)
        rw [Subsingleton.elim w 0, map_zero]
      rw [key x, key y]
    exact (CrystallineSemistableComparison.P.adj (sq (IdF.top Φ.A) (IdF.bot Φ.A)) (Pt.U E) (Pt.S E) (Pt.adj E) (m + 1)).1.subsingleton
end FV
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section PS
open CrystallineSemistableComparison.Pb.Site GlobalTheory.PDA GlobalTheory.CompanionTheory.ChartLocBc
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem polyS_crit (hp : p ≠ 0) (𝒱 : Set X.Opens) :
    (polyS (γ := γ) (q := q) (κ := κ) hp 𝒱).Crit (fun _ => IdF.bot _) 0 := by
  intro T b
  have key := GlobalTheory.CompanionTheory.SiteTrCrit.repr_sum T.obj.δ b
  refine ⟨fun h k => ?_, fun h => ?_⟩
  · change _ ∈ (⊥ : Ideal _) at h
    rw [Ideal.mem_bot] at h
    have h1 : b = 0 := by
      rw [← key]
      exact (congrArg _ h).trans (map_zero _)
    rw [h1]
    exact Ideal.zero_mem _
  · have h1 : b = 0 := by
      ext k
      exact h k
    subst h1
    exact Ideal.zero_mem _

end PS

section Res
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def polyRes (Q : Poly Φ) (W : ObjectProperty C) (hW : Cosieve W) : Poly (Φ.res W.ι) where
  P T := ⟨Q.P T.obj, hW (Q.j T.obj) T.property⟩
  j T := ObjectProperty.homMk (Q.j T.obj)
  X T := Q.X T.obj
  X_mem T := Q.X_mem T.obj
  univ {T T'} φ x hx := by
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := Q.univ φ.hom x hx
    refine ⟨ObjectProperty.homMk ψ, ⟨ObjectProperty.hom_ext _ h1, h2⟩, ?_⟩
    rintro ψ' ⟨h3, h4⟩
    exact ObjectProperty.hom_ext _ (hu ψ'.hom ⟨congrArg (fun f => f.hom) h3, h4⟩)
  span T z := Q.span T.obj z

theorem polyRes_crit (Q : Poly Φ) (W : ObjectProperty C) (hW : Cosieve W) (hQ : Q.Crit (fun _ => IdF.bot _) 0) :
    (polyRes Q W hW).Crit (fun _ => IdF.bot _) 0 := fun T b => hQ T.obj b

end Res

section Fr
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ}

def chFrame (c : Chart γ p q κ V d) (h : c.Good) {C₀ : Type 1} [Category.{0} C₀] (G : C₀ ⥤ Thick (nlFun γ p X q κ))
    [G.Full] [G.Faithful] (hV : ∀ T, InU V (G.obj T)) (D₀ : C₀) (ε : c.D ⟶ G.obj D₀) [IsIso ε] :
    Frame ((thP (nlFun γ p X q κ)).res G) d where
  D := D₀
  ne T := (h.1 _ (hV T)).map fun s => G.preimage (inv ε ≫ s)
  τ i {T} σ σ' := ((ε ≫ G.map σ').φ (c.t i) - (ε ≫ G.map σ).φ (c.t i) : (G.obj T).B)
  mem i {T} σ σ' := by
    obtain ⟨φ, -, hu⟩ := c.rep (CommRingCat.of ((G.obj T).B ⧸ (G.obj T).J)) (G.obj T).y (hV T)
    have e := (hu _ (ε ≫ G.map σ').pt).trans (hu _ (ε ≫ G.map σ).pt).symm
    exact Ideal.Quotient.eq.1 (RingHom.congr_fun e (Ideal.Quotient.mk _ (c.t i)))
  add i {T} σ σ' σ'' := by
    change (_ : (G.obj T).B) = (_ - _ : (G.obj T).B) + (_ - _ : (G.obj T).B)
    ring
  nat i {T T'} σ σ' φ := by
    rw [G.map_comp, G.map_comp, ← Category.assoc, ← Category.assoc]
    exact (map_sub (G.map φ).φ _ _).symm
  bij {T} σ y hy := by
    obtain ⟨σ', h1, h2⟩ := h.2 (G.obj T) (ε ≫ G.map σ) y hy
    refine ⟨G.preimage (inv ε ≫ σ'), fun i => ?_, fun τ hτ => G.map_injective ?_⟩
    · have : ε ≫ G.map (G.preimage (inv ε ≫ σ')) = σ' := by simp
      change ((ε ≫ G.map (G.preimage (inv ε ≫ σ'))).φ (c.t i) - _ : (G.obj T).B) = _
      rw [this]
      exact h1 i
    · have e := h2 (ε ≫ G.map τ) hτ
      simp [← e]

end Fr
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section CL
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V V' : X.Opens} {d : ℕ}

theorem chart_loc (c : Chart γ p q κ V d) (c' : Chart γ p q κ V' d) (e : c.D ⟶ c'.D) (he : ∀ i, e.φ (c.t i) = c'.t i)
    (g : c.D.B) (hg : IsUnit (e.φ g))
    (hT : ∀ (T : Thick (nlFun γ p X q κ)) (σ : c.D ⟶ T), IsUnit (σ.φ g) → InU V' T) :
    (∀ x, e.φ x = 0 → ∃ n : ℕ, g ^ n * x = 0) ∧ ∀ y, ∃ (n : ℕ) (x : c.D.B), e.φ x = e.φ g ^ n * y := by
  have hc := GlobalTheory.CompanionTheory.ChartMaps.good c
  have hc' := GlobalTheory.CompanionTheory.ChartMaps.good c'
  let σ := locH c.D g
  have hgL : IsUnit (σ.φ g) := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g
  have hL : InU V' (locT c.D g) := hT _ σ hgL
  have hLV : InU V (locT c.D g) := inU_hom σ c.inV
  obtain ⟨s₀⟩ := hc'.1 _ hL
  have hy : ∀ i, σ.φ (c.t i) - s₀.φ (c'.t i) ∈ (locT c.D g).J := fun i => by
    obtain ⟨φ, -, hu⟩ := c.rep (CommRingCat.of ((locT c.D g).B ⧸ (locT c.D g).J)) (locT c.D g).y hLV
    have e1 := (hu _ σ.pt).trans (hu _ (e ≫ s₀).pt).symm
    have e2 := Ideal.Quotient.eq.1 (RingHom.congr_fun e1 (Ideal.Quotient.mk _ (c.t i)))
    have e3 : (e ≫ s₀).φ (c.t i) = s₀.φ (c'.t i) := (congrArg s₀.φ (he i))
    rw [← e3]
    exact e2
  obtain ⟨s₁, h1, -⟩ := hc'.2 _ s₀ _ hy
  have hs₁ : ∀ i, s₁.φ (c'.t i) = σ.φ (c.t i) := fun i => by
    have := h1 i
    linear_combination this
  have hes : e ≫ s₁ = σ := by
    have h0 : ∀ i : Fin d, (0 : (locT c.D g).B) ∈ (locT c.D g).J := fun _ => Ideal.zero_mem _
    refine (hc.2 _ σ (fun _ => 0) h0).unique (fun i => ?_) (fun i => sub_self _)
    have e3 : (e ≫ s₁).φ (c.t i) = s₁.φ (c'.t i) := congrArg s₁.φ (he i)
    rw [e3, hs₁, sub_self]
  let ℓ : Localization.Away g →+* c'.D.B := IsLocalization.Away.lift g hg
  have hℓ : ∀ x, ℓ (algebraMap c.D.B (Localization.Away g) x) = e.φ x := fun x => IsLocalization.Away.lift_eq g hg x
  have hcomp : ℓ.comp (algebraMap c.D.B (Localization.Away g)) = e.φ := RingHom.ext hℓ
  have hdp : (locD c.D g).IsDPMorphism c'.D.δ ℓ := by
    refine IsDPMorphism.on_span _ _ (S := algebraMap c.D.B (Localization.Away g) '' (c.D.J : Set c.D.B)) rfl ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      rw [hℓ]
      exact e.hle ha
    · rintro n _ ⟨a, ha, rfl⟩
      rw [(locD_dp c.D g).dpow_comp a ha, hℓ, hℓ]
      exact (e.dp.dpow_comp a ha).symm
  have hle : (c.D.J.map (algebraMap c.D.B (Localization.Away g))) ≤ c'.D.J.comap ℓ := Ideal.map_le_iff_le_comap.1 hdp.ideal_comp
  let ℓ' : locT c.D g ⟶ c'.D := descOf e ℓ hcomp hdp hle
  have hu : s₁ ≫ ℓ' = 𝟙 c'.D := by
    have h0 : ∀ i : Fin d, (0 : c'.D.B) ∈ c'.D.J := fun _ => Ideal.zero_mem _
    refine (hc'.2 _ (𝟙 c'.D) (fun _ => 0) h0).unique (fun i => ?_) (fun i => sub_self _)
    have e3 : (s₁ ≫ ℓ').φ (c'.t i) = ℓ (σ.φ (c.t i)) := congrArg ℓ (hs₁ i)
    rw [e3]
    have e4 : ℓ (σ.φ (c.t i)) = e.φ (c.t i) := hℓ _
    rw [e4, he]
    exact sub_self _
  have hv : ∀ z, s₁.φ (ℓ z) = z := by
    have : s₁.φ.comp ℓ = RingHom.id _ := by
      refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun x => ?_)
      simp only [RingHom.comp_apply, RingHom.id_apply, hℓ]
      exact congrArg (fun f => f.φ x) hes
    exact fun z => RingHom.congr_fun this z
  have hw : ∀ y, ℓ (s₁.φ y) = y := fun y => congrArg (fun f => f.φ y) hu
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · have h2 : algebraMap c.D.B (Localization.Away g) x = 0 := by
      rw [← hv (algebraMap c.D.B (Localization.Away g) x), hℓ, hx, map_zero]
    obtain ⟨⟨_, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ x).1 h2
    exact ⟨n, hm⟩
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := Localization.Away g) g (s₁.φ y)
    refine ⟨n, a, ?_⟩
    have := congrArg ℓ ha
    rw [map_mul, hw, map_pow, hℓ, hℓ] at this
    rw [← this, mul_comm]
end CL
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section TAU
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU (⊤ : X.Opens) T := fun _ _ => trivial

def evT (T : Thick (nlFun γ p X q κ)) : Γ(X, ⊤) →+* T.B ⧸ T.J := ev T (inU_top T)

theorem evT_nat {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (f : Γ(X, ⊤)) :
    evT T' f = Ideal.quotientMap T'.J φ.φ φ.hle (evT T f) := by
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X)
      (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ ⊤), GlobalTheory.Cris.evalAt y ⊤ hh f = Ideal.quotientMap T'.J φ.φ φ.hle (evT T f) := by
    intro y hy hh
    subst hy
    exact evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (pt T) (inU_top T) hh f
  exact key _ (pt_hom φ) (inU_top T')

theorem isUnit_of_basicOpen_top {B : Type} [CommRing B] (u : B)
    (h : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ (Spec (CommRingCat.of B)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom u)) :
    IsUnit u := by
  by_contra hu
  obtain ⟨m, hm, hum⟩ := exists_max_ideal_of_mem_nonunits hu
  have h1 := h (show (⟨m, hm.isPrime⟩ : Spec (CommRingCat.of B)) ∈ (⊤ : (Spec (CommRingCat.of B)).Opens) from trivial)
  rw [basicOpen_eq_of_affine, PrimeSpectrum.mem_basicOpen] at h1
  exact h1 hum

theorem inU_basicOpen_iff (T : Thick (nlFun γ p X q κ)) (f : Γ(X, ⊤)) :
    InU (X.basicOpen f) T ↔ IsUnit (evT T f) := by
  have e : (pt T).app ⊤ f = (Scheme.ΓSpecIso (CommRingCat.of (T.B ⧸ T.J))).inv.hom (evT T f) := by
    change _ = (Scheme.ΓSpecIso (CommRingCat.of (T.B ⧸ T.J))).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (T.B ⧸ T.J))).hom.hom ((pt T).appLE ⊤ ⊤ _ f))
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
    simp [Scheme.Hom.appLE]
  unfold InU
  rw [Scheme.preimage_basicOpen, e]
  refine ⟨isUnit_of_basicOpen_top _, fun h => ?_⟩
  exact (Scheme.basicOpen_of_isUnit (Spec (CommRingCat.of (T.B ⧸ T.J))) (h.map (Scheme.ΓSpecIso (CommRingCat.of (T.B ⧸ T.J))).inv.hom)).ge
end TAU
end GlobalTheory.CompanionTheory.KMVan

namespace GlobalTheory.CompanionTheory.KMVan
section TAU2
open CrystallineSemistableComparison.Pb.Site
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem pow_eq_of_sub_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {n : ℕ} (hn : (n : B) = 0) {a b : B}
    (h : a - b ∈ J) : a ^ n = b ^ n := by
  obtain ⟨j, hj, rfl⟩ : ∃ j ∈ J, a = j + b := ⟨a - b, h, by ring⟩
  rw [add_pow, Finset.sum_range_succ']
  have : ∀ m ∈ Finset.range n, j ^ (m + 1) * b ^ (n - (m + 1)) * (n.choose (m + 1) : B) = 0 := by
    intro m _
    rw [← δ.factorial_mul_dpow_eq_pow hj]
    have e : ((m + 1).factorial : B) * (n.choose (m + 1) : B) = (n.descFactorial (m + 1) : B) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
    have e2 : (n.descFactorial (m + 1) : B) = 0 := by
      cases n with
      | zero => simp
      | succ n =>
        rw [Nat.succ_descFactorial_succ, Nat.cast_mul, hn, zero_mul]
    calc _ = ((m + 1).factorial : B) * (n.choose (m + 1) : B) * (δ.dpow (m + 1) j * b ^ (n - (m + 1))) := by ring
      _ = 0 := by rw [e, e2, zero_mul]
  rw [Finset.sum_eq_zero this]
  simp

theorem pow_eq_zero_of_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {n : ℕ} (h0 : n ≠ 0) (hn : (n : B) = 0)
    {a : B} (h : a ∈ J) : a ^ n = 0 := by
  have := pow_eq_of_sub_mem δ hn (a := a) (b := 0) (by simpa using h)
  rw [this, zero_pow h0]

theorem isUnit_of_mk {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {n : ℕ} (h0 : n ≠ 0) (hn : (n : B) = 0)
    {a : B} (h : IsUnit (Ideal.Quotient.mk J a)) : IsUnit a := by
  obtain ⟨b, hb⟩ := h.exists_right_inv
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  have h1 : a * c - 1 ∈ J := Ideal.Quotient.eq.1 (by rw [map_mul, hb, map_one])
  have h2 : IsNilpotent (a * c - 1) := ⟨n, pow_eq_zero_of_mem δ h0 hn h1⟩
  have h3 : IsUnit (a * c) := by
    have := h2.isUnit_add_one
    simpa using this
  exact isUnit_of_mul_isUnit_left h3

def lftT (T : Thick (nlFun γ p X q κ)) (f : Γ(X, ⊤)) : T.B :=
  Function.surjInv Ideal.Quotient.mk_surjective (evT T f)

theorem mk_lftT (T : Thick (nlFun γ p X q κ)) (f : Γ(X, ⊤)) : Ideal.Quotient.mk T.J (lftT T f) = evT T f :=
  Function.surjInv_eq _ _

def tau (n : ℕ) (f : Γ(X, ⊤)) (T : Thick (nlFun γ p X q κ)) : T.B := lftT T f ^ n

theorem n_zero (T : Thick (nlFun γ p X q κ)) {n : ℕ} (hn : (n : R) = 0) : (n : T.B) = 0 := by
  rw [← map_natCast T.i, hn, map_zero]

theorem mk_tau (T : Thick (nlFun γ p X q κ)) (n : ℕ) (f : Γ(X, ⊤)) :
    Ideal.Quotient.mk T.J (tau n f T) = evT T f ^ n := by
  rw [tau, map_pow, mk_lftT]

theorem tau_nat {n : ℕ} (hn : (n : R) = 0) {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (f : Γ(X, ⊤)) :
    φ.φ (tau n f T) = tau n f T' := by
  rw [tau, tau, map_pow]
  refine pow_eq_of_sub_mem T'.δ (n_zero T' hn) (Ideal.Quotient.eq.1 ?_)
  rw [mk_lftT, evT_nat φ f, ← mk_lftT T f]
  rfl

theorem isUnit_tau {n : ℕ} (h0 : n ≠ 0) (hn : (n : R) = 0) (T : Thick (nlFun γ p X q κ)) (f : Γ(X, ⊤)) :
    IsUnit (tau n f T) ↔ InU (X.basicOpen f) T := by
  rw [inU_basicOpen_iff]
  constructor
  · intro h
    have := h.map (Ideal.Quotient.mk T.J)
    rw [mk_tau] at this
    exact (isUnit_pow_iff h0).1 this
  · intro h
    refine (IsUnit.pow n ?_)
    exact isUnit_of_mk T.δ h0 (n_zero T hn) (by rw [mk_lftT]; exact h)

end TAU2
end GlobalTheory.CompanionTheory.KMVan
