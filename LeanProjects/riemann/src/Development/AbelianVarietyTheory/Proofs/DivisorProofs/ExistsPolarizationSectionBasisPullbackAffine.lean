import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEndOfEighthPowerOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationModelFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithBaseFiniteContainingRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueOfBasis
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniversalBasisMoveBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.SecBasisPull

open GlobalTheory.VVRank GlobalTheory.EmbPull GlobalTheory.ThetaReal

theorem eq_zero_of_smul_eq_zero (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) {T : Over S}
    [IsAffine T.left] {t : LB.Sec (LPow P.A P.L 1 T)} (ht : IsGenSec P.A P.L 1 t) (r : Γ(T.left, ⊤))
    (hr : r • (SecM.ofSec P.A t : SecM P.A P.L 1 T) = 0) : r = 0 := by
  let I : Ideal Γ(T.left, ⊤) := Submodule.comap (LinearMap.toSpanSingleton Γ(T.left, ⊤) Γ(T.left, ⊤) r) ⊥
  have memI : ∀ a, a ∈ I ↔ a * r = 0 := fun a => by
    simp [I, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have key : ∀ p : T.left, ∃ g ∈ I, p ∈ T.left.basicOpen g := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
    haveI hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
    obtain ⟨g, hg, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨p, hV⟩ trivial
    let W := T.left.basicOpen g
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
      (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hg y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
    have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen g
    haveI : IsAffine (overRes W).left := hW
    obtain ⟨c, -⟩ := exists_basis P 1 b hb (overRes W) l
    let σ := (overResι W).left.appTop.hom
    let k₀ : Fin (1 ^ P.g) := @default _ hq.toInhabited
    obtain ⟨n, u, hu⟩ := exists_pow_extend_secM P 1 g (c k₀)
    obtain ⟨e, he⟩ := ht (SecM.toSec P.A u)
    have hue : u = e • SecM.ofSec P.A t := Subtype.ext (funext he)
    obtain ⟨d, hd⟩ : ∃ d, pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A t) = d • c k₀ := by
      have := c.sum_repr (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A t))
      rw [Fintype.sum_unique] at this
      exact ⟨_, this.symm⟩
    have coef : ∀ x y : Γ((overRes W).left, ⊤), x • c k₀ = y • c k₀ → x = y := fun x y h => by
      have := congrArg (fun v => c.repr v k₀) h
      simp only [LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
        smul_eq_mul, _root_.mul_one] at this
      exact this
    have e1 : σ (g ^ n) = σ e * d := coef _ _ (by
      rw [← hu, hue, LinearMap.map_smulₛₗ, hd, smul_smul])
    have e2 : σ r * d = 0 := coef _ _ (by
      rw [← smul_smul, ← hd, ← LinearMap.map_smulₛₗ, hr, map_zero, zero_smul])
    have e3 : σ (r * g ^ n) = 0 := by rw [map_mul, e1, mul_left_comm, e2, mul_zero]
    have e4 := (congrArg (fun q => q.hom (r * g ^ n)) (Scheme.Opens.ι_appTop W)).symm.trans e3
    obtain ⟨m, hm⟩ := GlobalTheory.AffineThickening.exists_pow_mul_eq_zero (isAffineOpen_top T.left) _ g (r * g ^ n)
      (Scheme.Opens.ι_image_top W) e4
    refine ⟨g ^ (m + n), (memI _).2 (by rw [pow_add, _root_.mul_assoc, mul_comm (g ^ n), hm]), ?_⟩
    rw [Scheme.mem_basicOpen_top] at hp ⊢
    rw [map_pow]
    exact hp.pow _
  have hI : Ideal.span (I : Set Γ(T.left, ⊤)) = ⊤ :=
    (isAffineOpen_top T.left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨g, hg, hp⟩ := key p
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, hg⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  simpa using (memI 1).1 hI

theorem univBasis_of_isGenSec (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) {T : Over S} [IsAffine T.left]
    {th : LB.Sec (LPow P.A P.L 1 T)} (hth : IsGenSec P.A P.L 1 th) :
    UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) := by
  intro T' _ h
  have hg := isGenSec_pullS P hS h hth
  let t' : SecM P.A P.L 1 T' := SecM.ofSec P.A (pullS P.A 1 h th)
  let l := LinearMap.toSpanSingleton Γ(T'.left, ⊤) (SecM P.A P.L 1 T') t'
  have inj : Function.Injective l := (injective_iff_map_eq_zero l).2 fun r hr =>
    eq_zero_of_smul_eq_zero hS P hg r (by simpa only [l, LinearMap.toSpanSingleton_apply] using hr)
  have surj : Function.Surjective l := fun s => by
    obtain ⟨r, hr⟩ := hg (SecM.toSec P.A s)
    exact ⟨r, Subtype.ext (funext fun j => (hr j).symm)⟩
  let E := LinearEquiv.ofBijective l ⟨inj, surj⟩
  refine ⟨(Module.Basis.singleton (Fin 1) Γ(T'.left, ⊤)).map E, fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.singleton_apply]
  show l 1 = _
  rw [LinearMap.toSpanSingleton_apply, one_smul]
  rfl

end GlobalTheory.SecBasisPull
end

open GlobalTheory.SecBasisPull GlobalTheory.ThetaReal in

theorem GlobalTheory.SecBasisPull.exists_secBasis_pull : ∀ {R R' : Type} [CommRing R] [CommRing R'] (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (f : R →+* R') (ψ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap f) ψ → LBIso P'.L (P.L.pull ψ) → ∀ th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R))), IsSecBasis _ (fun _ : Fin 1 => th) → ∃ th' : LB.Sec (LPow P'.A P'.L 1 (baseOver (Sp R'))), IsSecBasis _ (fun _ : Fin 1 => th') := by
  intro R R' _ _ P P' f ψ hp hw th hth
  obtain ⟨-, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  haveI : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Sp R))
  haveI : IsAffine (baseOver (Sp R')).left := inferInstanceAs (IsAffine (Sp R'))
  have hgen : IsGenSec P.A P.L 1 th := fun s => by
    obtain ⟨r, hr, -⟩ := hth s
    exact ⟨r 0, fun j => (hr j).trans (Fin.sum_univ_one _)⟩
  have hU := univBasis_of_isGenSec hL₂.secBaseChangeAny P hgen
  obtain ⟨b, hb⟩ := GlobalTheory.UnivBasisMove.univBasis_move _ _ (spMap f) P P' ψ hp hw 1 (Fin 1) (baseOver (Sp R)) (spMap f)
    (Category.comp_id _) _ hU
  obtain ⟨c, -⟩ := hb.exists_basis
  refine ⟨SecM.toSec P'.A (c 0), fun s => ?_⟩
  have e : ∀ i : Fin 1, c i = c 0 := fun i => congrArg c (Subsingleton.elim _ _)
  have := existsUnique_of_basis c s
  simp only [e] at this
  exact this
