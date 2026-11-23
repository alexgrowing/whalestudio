import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenThetaAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegLower

theorem weilIs_lower_field {K : Type} [Field K] [IsAlgClosed K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {n d : ℕ} (hd : d ≠ 0) {T : Over (Sp K)} {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (hx : x ^ (n * d) = 1) (hy : y ^ (n * d) = 1)
    (h : Out.WeilIs A L ((n * d : ℕ) : ℤ) x y c) : Out.WeilIs A L n (x ^ d) (y ^ d) (c ^ d) := by
  obtain ⟨r, hr⟩ := DVR.exists_gen_of_isLB_local (V := K) (L.pull (eSec A)) (pull_isLB hL _)
  let M : RigLB A := ⟨L, r, hL, hr⟩
  obtain ⟨t, ht⟩ := AbLaw.CubeProj.exists_gen_theta_abelianVariety globalFns_holds K A hA
    (AbelianProjective.isProjBy_of_isAbelianScheme K A hA) L hL
  obtain ⟨t', ht', hn⟩ := AbLaw.Cube.exists_normalised hL t ht
  let cub : CubicalStr A M := AbLaw.Cube.cubicalOfNormalised globalFns_holds hA M t' ht' hn
  have hx' : (x ^ d) ^ n = 1 := by rw [← pow_mul, mul_comm, hx]
  have hy' : (y ^ d) ^ n = 1 := by rw [← pow_mul, mul_comm, hy]
  obtain ⟨w, hw⟩ := exists_weil cub hx' hy'
  have h₁ : Out.WeilIs A L n (x ^ d) (y ^ d) w := (weilIs_iff cub globalFns_holds hA hx' hy' hw w).2 rfl
  have h' := CommPairing.weilIs_symm hL h
  have hp : ∀ j : ℕ, Out.WeilIs A L ((n * d : ℕ) : ℤ) (y ^ (j + 1)) x (c⁻¹ ^ (j + 1)) := fun j => by
    induction j with
    | zero => rwa [zero_add, pow_one, pow_one]
    | succ j ih => rw [pow_succ, pow_succ c⁻¹]; exact SiegelTypings.weilIs_mul hA hL ih h'
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have h₂ := CommPairing.weilIs_symm hL (hp j)
  rw [inv_pow, inv_inv, Nat.cast_mul] at h₂
  rw [PairingLevels.weilIs_value_eq globalFns_holds hA hL ht h₂ h₁]
  exact h₁

variable {h N : ℕ} {B' : Type} [CommRing B'] {ζ' : B'} {S : Scheme.{0}} {s' : S ⟶ Sp B'}

theorem weilIs_lower (C : SiegPre h N ζ' s') {K : Type} [Field K] [IsAlgClosed K] (p : Sp K ⟶ S) {n d : ℕ} (hd : d ≠ 0) :
    ∀ (x y : Over.mk p ⟶ C.A) (u : Kˣ), x ^ (n * d) = 1 → y ^ (n * d) = 1 →
      Out.WeilIs C.A C.diag ((n * d : ℕ) : ℤ) x y (unitOn u) →
      Out.WeilIs C.A C.diag n (x ^ d) (y ^ d) (unitOn (u ^ d)) := by
  obtain ⟨c, φ, φ₂, pb, sq, iso, -⟩ := (siegPre_pullback h N B' ζ' S _ s' _ p C rfl).1
  have key : ∀ q : Sp K ⟶ S, q = 𝟙 _ ≫ p → ∀ (x y : Over.mk q ⟶ C.A) (u : Kˣ), x ^ (n * d) = 1 → y ^ (n * d) = 1 →
      Out.WeilIs C.A C.diag ((n * d : ℕ) : ℤ) x y (unitOn u) →
      Out.WeilIs C.A C.diag n (x ^ d) (y ^ d) (unitOn (u ^ d)) := by
    rintro q rfl x y u hx hy H
    let e := ObjPull.pushEquiv pb (Over.mk (𝟙 (Sp K)))
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    have tr := fun (k : ℤ) (a b : Over.mk (𝟙 (Sp K)) ⟶ c.A) (v : Γ(Sp K, ⊤)ˣ) =>
      weilIs_grpPullback_of_comm S _ C.A c.A p φ C.diag c.diag (pull_isLB C.isLB _) (pull_isLB c.isLB _) pb
        (SiegelPull.diag_iso sq iso) (Over.mk (𝟙 _)) k a b (e a) (e b) v rfl rfl
    have hx' : x ^ (n * d) = 1 := e.injective ((map_pow e _ _).trans (hx.trans (map_one e).symm))
    have hy' : y ^ (n * d) = 1 := e.injective ((map_pow e _ _).trans (hy.trans (map_one e).symm))
    have H' := (tr _ _ _ _).1 (weilIs_lower_field c.ab (pull_isLB c.isLB _) hd hx' hy' ((tr _ _ _ _).2 H))
    rw [map_pow, map_pow] at H'
    have e' : unitOn (u ^ d) = unitOn u ^ d := map_pow _ _ _
    rw [e']
    exact H'
  exact key p (Category.id_comp p).symm

def lower (C : SiegPre h N ζ' s') {n d : ℕ} (hN : N = n * d) (h0 : N ≠ 0) {B : Type} [CommRing B] {ζ : B} (j : B →+* B')
    (hj : j ζ = ζ' ^ d) : SiegPre h n ζ (s' ≫ spMap j) where
  A := C.A
  ab := C.ab
  P := C.P
  isLB := C.isLB
  rig₁ := C.rig₁
  rig₂ := C.rig₂
  symm := C.symm
  lev a := C.lev a ^ d
  lev_add a b := by rw [C.lev_add, mul_pow]
  lev_tors a := by rw [← pow_mul, mul_comm, ← hN, C.lev_tors]
  geom k _ _ x β z hx hz := by
    have hn : n ≠ 0 := fun e => h0 (by rw [hN, e, zero_mul])
    have hd : d ≠ 0 := fun e => h0 (by rw [hN, e, mul_zero])
    obtain ⟨β', hβ'⟩ : ∃ β' : B' →+* k, x ≫ s' = spMap β' :=
      ⟨(Spec.preimage (x ≫ s')).hom, (Spec.map_preimage _).symm⟩
    have hβ : β = β'.comp j := by
      have e : Spec.map (CommRingCat.ofHom β) = Spec.map (CommRingCat.ofHom (β'.comp j)) := by
        refine hx.symm.trans ?_
        rw [← Category.assoc, hβ']
        exact (Spec.map_comp _ _).symm
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    have hz' : (z : k) = β' ζ' ^ d := by rw [hz, hβ, RingHom.comp_apply, hj, map_pow]
    have hu : β' ζ' ≠ 0 := fun e => z.ne_zero (by rw [hz', e, zero_pow hd])
    have ez : z = Units.mk0 _ hu ^ d := Units.ext (by rw [hz', Units.val_pow_eq_pow_val, Units.val_mk0])
    obtain ⟨g₁, g₂, g₃⟩ := C.geom k x β' (Units.mk0 _ hu) hβ' rfl
    refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
    · rw [← SiegelTypings.lev_nsmul, g₁]
      refine exists_congr fun b => ?_
      rw [hN, mul_comm, mul_smul]
      exact (smul_right_injective _ hd).eq_iff
    · obtain ⟨a, rfl⟩ := g₂ g ((congrArg (g ^ ·) hN).trans (by rw [pow_mul, hg, one_pow]))
      rw [← MonObj.comp_pow, ← SiegelTypings.lev_nsmul, g₁] at hg
      obtain ⟨b, hb⟩ := hg
      rw [hN, mul_smul] at hb
      exact ⟨b, by rw [smul_right_injective _ hn hb, SiegelTypings.lev_nsmul]⟩
    · have t : ∀ a, (toUnit (Over.mk x) ≫ C.lev a) ^ (n * d) = 1 := fun a => by
        rw [← MonObj.comp_pow, ← hN, C.lev_tors, MonObj.comp_one]
      have H := weilIs_lower C x hd _ _ _ (t a) (t b) (by rw [← hN]; exact g₃ a b)
      have e : (Units.mk0 _ hu ^ d) ^ (2 * omegaStd a b) = (Units.mk0 _ hu ^ (2 * omegaStd a b)) ^ d := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
      show Out.WeilIs C.A C.diag n (toUnit (Over.mk x) ≫ C.lev a ^ d) (toUnit (Over.mk x) ≫ C.lev b ^ d)
        (unitOn (z ^ (2 * omegaStd a b)))
      rw [ez, e, MonObj.comp_pow, MonObj.comp_pow]
      exact H

theorem isGrpPullback_id (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨(IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback (𝟙 G.left) G.hom G.hom (𝟙 S)),
    fun T x y x₀ y₀ hx hy => ?_⟩
  refine Eq.trans ?_ (Category.comp_id _).symm
  exact mul_left_congr (b := T.hom) (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))

theorem lbIso_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) :=
  (LBIso.chartPull (Geo.Tor.chartPullPull L (𝟙 _) (𝟙 _) rfl) (chartPullId L) (lbIso_refl hL)).symm

theorem exists_lower : ∀ (h n N : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (j : B →+* B')
    (S : Scheme.{0}) (s' : S ⟶ Sp B') (C : SiegPre h N ζ' s'), N ≠ 0 → IsUnit (N : B') → n ∣ N → j ζ = ζ' ^ (N / n) →
    ∃ c : SiegPre h n ζ (s' ≫ spMap j), SRel C c (N / n) 1 (𝟙 S) ∧ SRel c C 1 (N / n) (𝟙 S) := by
  intro h n N B B' _ _ ζ ζ' j S s' C h0 _ hn hj
  have sq : IsSquare (G' := C.A) (G := C.A) (𝟙 _) (𝟙 _) := ⟨by simp, by simp⟩
  refine ⟨lower C (Nat.mul_div_cancel' hn).symm h0 j hj,
    ⟨𝟙 _, isGrpPullback_id C.A, ⟨𝟙 _, sq, lbIso_pull_id C.isLB⟩, fun a => ?_⟩,
    ⟨𝟙 _, isGrpPullback_id C.A, ⟨𝟙 _, sq, lbIso_pull_id C.isLB⟩, fun a => ?_⟩⟩
  · rw [pow_one]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [pow_one]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

end GlobalTheory.SiegLower
