import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaCoset

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank

theorem exists_eq_smul {N n : ℕ} (hN : N ≠ 0) (hn : n ∣ N) {c : ZMod (N ^ 2)} (hc : n • c = 0) :
    ∃ d : ZMod (N ^ 2), N • (N / n) • d = c := by
  obtain ⟨m, rfl⟩ := hn
  have h₀ : 0 < n := Nat.pos_of_ne_zero (left_ne_zero_of_mul hN)
  have : NeZero ((n * m) ^ 2) := ⟨pow_ne_zero _ hN⟩
  obtain ⟨e, rfl⟩ := ZMod.natCast_zmod_surjective c
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff,
    show (n * m) ^ 2 = n * (n * m * m) by ring] at hc
  obtain ⟨d, rfl⟩ := Nat.dvd_of_mul_dvd_mul_left h₀ hc
  refine ⟨d, ?_⟩
  rw [Nat.mul_div_cancel_left _ h₀, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem exists_label {G : Type} [CommGroup G] {r N n : ℕ} (hN : N ≠ 0) (hn : n ∣ N) (p : Fin r → G)
    (hp : ∀ i, p i ^ (N ^ 2) = 1)
    (hb : ∀ y : G, y ^ (N ^ 2) = 1 → ∃! c : Fin r → ZMod (N ^ 2), ∏ i, p i ^ (c i).val = y)
    (a : Fin r → ZMod (N ^ 2)) {z : G} (hz : z ^ n = 1) :
    ∃ c : Fin r → ZMod (N ^ 2), (∏ i, p i ^ ((a + (N / n) • c) i).val) ^ N = (∏ i, p i ^ (a i).val) ^ N * z := by
  have : NeZero (N ^ 2) := ⟨pow_ne_zero _ hN⟩
  let f : (Fin r → ZMod (N ^ 2)) → G := fun c => ∏ i, p i ^ (c i).val
  have f₀ : f 0 = 1 := Finset.prod_eq_one fun i _ => by rw [Pi.zero_apply, ZMod.val_zero, pow_zero]
  have fa : ∀ c d, f (c + d) = f c * f d := fun c d => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hp i), pow_add]
  have fs : ∀ (m : ℕ) c, f (m • c) = f c ^ m := fun m c => by
    induction m with
    | zero => rw [zero_smul, f₀, pow_zero]
    | succ m ih => rw [succ_nsmul, fa, ih, pow_succ]
  obtain ⟨c₀, hc₀, -⟩ := hb z (by
    obtain ⟨m, hm⟩ := hn.trans (dvd_pow_self N two_ne_zero)
    rw [hm, pow_mul, hz, one_pow])
  replace hc₀ : f c₀ = z := hc₀
  have h₁ : n • c₀ = 0 := (hb 1 (one_pow _)).unique ((fs n c₀).trans (by rw [hc₀, hz])) f₀
  choose d hd using fun i => exists_eq_smul hN hn (congrFun h₁ i)
  refine ⟨d, ?_⟩
  change f _ ^ N = f a ^ N * z
  rw [fa, mul_pow, ← fs N (_ • d), ← hc₀]
  exact congrArg (fun c => _ * f c) (funext hd)

variable {S : Scheme.{0}}

theorem ne_zero_of_isGenSec (hB : SecBaseChangeAnySt) (P : PolAV S) {K : Type} [Field K] (x : Sp K ⟶ S)
    {th : LB.Sec (LPow P.A P.L 1 (Over.mk x))} (H : IsGenSec P.A P.L 1 th) : SecM.ofSec P.A th ≠ 0 := by
  obtain ⟨V, hV, b, hb⟩ := hB S P 1 le_rfl (x (IsLocalRing.closedPoint K))
  obtain ⟨t, rfl⟩ : ∃ t : Sp K ⟶ (overRes (T := baseOver S) V).left, t ≫ (overRes (T := baseOver S) V).hom = x :=
    ⟨IsOpenImmersion.lift V.ι x (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      rwa [Subsingleton.elim p (IsLocalRing.closedPoint K)]),
      (congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _)⟩
  obtain ⟨hli, -⟩ := hb K t (fun i => pullS P.A _ (homAt t) (b i)) fun i => isPullSec_pullS _ _ _ _
  have : Nontrivial Γ((baseAt t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have i : Fin (1 ^ P.g) := ⟨0, by rw [one_pow]; exact one_pos⟩
  intro h₀
  obtain ⟨r, hr⟩ := H (pullS P.A _ (homAt t) (b i))
  have e : SecM.ofSec P.A (pullS P.A _ (homAt t) (b i)) = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
  rw [h₀, smul_zero] at e
  exact hli.ne_zero i e

theorem exists_ne_zero_over (h₁ : Laws) (h₂ : Laws2) (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ S) {k n : ℕ} (hn : 2 ≤ n) (hK : (n : K) ≠ 0) {I : Type} {y : I → (Over.mk x ⟶ P.A)}
    {v : I → Γ((Over.mk x).left, ⊤)} (H : IsThetaPtOver P k y v) (a : Over.mk x ⟶ P.A) :
    ∃ z : Over.mk x ⟶ P.A, z ^ n = 1 ∧ ∀ i, y i ^ k = a * z → v i ≠ 0 := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨z, hz, hu⟩ := UT.ExactTerm.exists_good_point h₁.goodPt h₁.polBaseChange P x hn hK th
    (ne_zero_of_isGenSec h₂.secBaseChangeAny P x hth) a
  refine ⟨z, hz, fun i hi h₀ => ?_⟩
  let p : (Over.mk x).left := IsLocalRing.closedPoint K
  choose J hJ using fun χ : (Over.mk x).left ⟶ P.A.left => exists_chart hL (χ p)
  replace hJ : Good P.L p J := hJ
  have b₁ := sv_act (hU i).pt_eq (hs₂ i) (𝟙 _) hJ 1
  have b₂ := sv_mulPull hs₁ (𝟙 _) hJ (y i)
  have b₃ := sv_of_isValueAt (hw i) (𝟙 _) hJ
  rw [Category.id_comp, _root_.mul_one] at b₁
  rw [Category.id_comp] at b₃
  rw [hv, Units.mul_right_eq_zero] at h₀
  rw [b₃, b₂, hi, h₀, UT.ExactTerm.gs_zero' _ _ ⊤ trivial, MulZeroClass.zero_mul] at b₁
  exact ((Units.isUnit _).mul ((Units.isUnit _).mul (hu p J hJ))).ne_zero b₁.symm

theorem coset_bot (h₁ : Laws) (h₂ : Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {s : S ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) {n : ℕ} (hn : 2 ≤ n) (hd : n ∣ N') {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ S) {v : Ix g (N' ^ 2) → K} (H : t.HasTh x v) (a : Ix g (N' ^ 2)) :
    ∃ c, v (a + (N' / n) • c) ≠ 0 := by
  have := t.ab.comm
  let π : Over.mk x ⟶ baseOver S := Over.homMk x (by simp)
  have hK : (n : K) ≠ 0 := by
    have := H.2.1.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    rw [map_natCast] at this
    exact (isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) this).ne_zero
  have : Subsingleton (Over.mk x).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Over.mk x).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨z, hz, hv⟩ := exists_ne_zero_over h₁ h₂ t.pol x hn hK (isThetaPtOver_of_subsingleton t.pol H)
    ((π ≫ t.lab a) ^ N')
  have e : ∀ c, π ≫ t.lab c = ∏ i, (π ≫ t.pt i) ^ (c i).val := fun c => by
    rw [TObj.lab, VVRank.comp_linComb, linComb, List.prod_ofFn]
  obtain ⟨c, hc⟩ := exists_label (G := Over.mk x ⟶ t.A) H.1.pos.ne' hd (fun i => π ≫ t.pt i)
    (fun i => by rw [← MonObj.comp_pow, t.torsion, MonObj.comp_one])
    (fun y hy => by simpa only [linComb, List.prod_ofFn] using t.bij K x y hy) a hz
  rw [← e, ← e] at hc
  refine ⟨c, fun h₀ => hv _ hc ?_⟩
  rw [h₀, map_zero]

end GlobalTheory.ThetaCoset

namespace GlobalTheory

theorem coset_of_hasTh : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (n : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R) (q : Ideal R), 2 ≤ n → n ∣ N' → t.HasTh x v → q.IsPrime → Coset n N' v q := by
  intro h₁ h₂ o _ g N' J b S s t n R _ x v q hn hd H hq a
  let φ : R →+* AlgebraicClosure q.ResidueField :=
    (algebraMap q.ResidueField (AlgebraicClosure q.ResidueField)).comp (algebraMap R q.ResidueField)
  obtain ⟨c, hc⟩ := ThetaCoset.coset_bot h₁ h₂ t hn hd _ (T.hasThetaConstants_ring_baseChange h₂ o g N' J b S s t R _ φ x v H) a
  refine ⟨c, fun hm => hc ?_⟩
  rw [RingHom.comp_apply, Ideal.algebraMap_residueField_eq_zero.2 hm, map_zero]

end GlobalTheory
