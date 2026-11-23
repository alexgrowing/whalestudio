import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CanonicalTauPower
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CanonicalPsiNormOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionTauCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj Matrix

section Data

variable {R : Type} [CommRing R] [IsDomain R]

end Data

section Transport

variable {A : Over (Sp ℂ)} [GrpObj A] {L M : LB A.left} {g : ℕ}

theorem valAt'_resU {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V (res h a).val = valAt' x U a.val :=
  valAt'_res x h _ hV

theorem iso_fr {w : LB.Iso L M} (hw : w.IsGen) (u : HolUnif A L g) (z : Fin g → ℂ) {j j' : M.ι} {i i' : L.ι}
    (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U j) (hj' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U j')
    (hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) (hi' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i') :
    valAt' (u.ex z).left (M.U j ⊓ L.U i) (w.s (j, i)).val * u.fr i z =
      valAt' (u.ex z).left (M.U j ⊓ M.U j') (M.g j j').val *
        (valAt' (u.ex z).left (M.U j' ⊓ L.U i') (w.s (j', i')).val * u.fr i' z) := by
  have hO : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (M.U j ⊓ L.U i ⊓ (M.U j' ⊓ L.U i')) := fun p hp =>
    ⟨⟨hj hp, hi hp⟩, hj' hp, hi' hp⟩
  have hii : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U i') := fun p hp => ⟨hi hp, hi' hp⟩
  have e := congrArg (fun a : Γ(A.left, M.U j ⊓ L.U i ⊓ (M.U j' ⊓ L.U i'))ˣ => valAt' (u.ex z).left _ a.val)
    (hw (j, i) (j', i'))
  have e' : valAt' (u.ex z).left (M.U j ⊓ L.U i) (w.s (j, i)).val =
      valAt' (u.ex z).left (M.U j ⊓ M.U j') (M.g j j').val *
        (valAt' (u.ex z).left (L.U i ⊓ L.U i') (L.g i i').val)⁻¹ *
        valAt' (u.ex z).left (M.U j' ⊓ L.U i') (w.s (j', i')).val := by
    refine (valAt'_resU _ _ _ hO).symm.trans (e.trans ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·)
      ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·) (valAt'_resU _ _ _ hO)
        ((valAt'_units_inv _ hO _).trans (congrArg (·⁻¹) (valAt'_resU _ _ _ hO))))) (valAt'_resU _ _ _ hO))))
  have hne := valAt'_unit_ne_zero _ hii (L.g i i')
  rw [e', u.fr_compat i i' z hii]
  field_simp

theorem valAt'_g_self {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) (x : Sp ℂ ⟶ X) {j : M.ι} (hj : ⊤ ≤ x ⁻¹ᵁ M.U j) :
    valAt' x (M.U j ⊓ M.U j) (M.g j j).val = 1 := by
  rw [← valAt'_resU x (le_inf le_rfl le_rfl : M.U j ≤ M.U j ⊓ M.U j) _ hj, hM.g_self, Units.val_one,
    valAt'_one x hj]

theorem exists_chart_ex (hL : L.IsLB) (u : HolUnif A L g) (z : Fin g → ℂ) :
    ∃ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := by
  obtain ⟨i, hi⟩ := exists_chart hL ((u.ex z).left (default : PrimeSpectrum ℂ))
  exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩

def frT (hL : L.IsLB) (w : LB.Iso L M) (u : HolUnif A L g) (j : M.ι) (z : Fin g → ℂ) : ℂ :=
  valAt' (u.ex z).left (M.U j ⊓ L.U (exists_chart_ex hL u z).choose) (w.s (j, (exists_chart_ex hL u z).choose)).val *
    u.fr (exists_chart_ex hL u z).choose z

theorem frT_eq (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen) (u : HolUnif A L g) {j : M.ι} {i : L.ι}
    {z : Fin g → ℂ} (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U j) (hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) :
    frT hL w u j z = valAt' (u.ex z).left (M.U j ⊓ L.U i) (w.s (j, i)).val * u.fr i z := by
  rw [frT, iso_fr hw u z hj hj (exists_chart_ex hL u z).choose_spec hi, valAt'_g_self hM _ hj, _root_.one_mul]

def transport (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen) (u : HolUnif A L g) : HolUnif A M g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := frT hL w u
  fr_hol j z₀ hz₀ := by
    obtain ⟨i, hi⟩ := exists_chart_ex hL u z₀
    have h₁ := u.hol (M.U j ⊓ L.U i) (w.s (j, i)).val
    have hm : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (M.U j ⊓ L.U i)} ∈ nhds z₀ :=
      h₁.1.mem_nhds ((top_le_preimage_inf _ _ _).2 ⟨hz₀, hi⟩)
    have hd := (h₁.2.mul ((u.fr_hol i).mono fun z hz => ((top_le_preimage_inf _ _ _).1 hz).2)).differentiableAt hm
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hm] with z hz
    exact frT_eq hL hM hw u ((top_le_preimage_inf _ _ _).1 hz).1 ((top_le_preimage_inf _ _ _).1 hz).2
  fr_ne j z hz := by
    have hi := (exists_chart_ex hL u z).choose_spec
    exact mul_ne_zero (valAt'_unit_ne_zero _ ((top_le_preimage_inf _ _ _).2 ⟨hz, hi⟩) _) (u.fr_ne _ _ hi)
  fr_compat j j' z hz :=
    have hi := (exists_chart_ex hL u z).choose_spec
    iso_fr hw u z ((top_le_preimage_inf _ _ _).1 hz).1 ((top_le_preimage_inf _ _ _).1 hz).2 hi hi

theorem isAH_transport (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen) (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) : (transport hL hM hw u).IsAH Hm χ := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun l j z hj => ?_⟩
  obtain ⟨i, hi⟩ := exists_chart_ex hL u z
  have hl : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
  have a := frT_eq hL hM hw u (z := z) hj hi
  have b := frT_eq hL hM hw u (j := j) (i := i) (z := z + l) (by rw [hl]; exact hj) (by rw [hl]; exact hi)
  rw [hl] at b
  refine a.trans (Eq.trans ?_ (congrArg _ b.symm))
  rw [h.2.2.2 l i z hi]
  ring

end Transport

theorem isGen_refl {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) :
    LB.Gen.IsGen (⟨fun p => L.g p.1 p.2⟩ : LB.Iso L L) := by
  refine fun p q => unit_ext fun y hy => ?_
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

def polOfPullback {S S' : Scheme.{0}} (P : Out.PolAV S) {f : S' ⟶ S} (A : Over S') [GrpObj A] [IsCommMonObj A]
    {φ : A.left ⟶ P.A.left} (h : IsGrpPullback A P.A f φ) : Out.PolAV S' where
  A := A
  isAb :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) h.1 P.isAb.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) h.1 P.isAb.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 P.isAb.geomConnected }
  g := P.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
  L := P.L.pull φ
  isLB := pull_isLB P.isLB _
  rigid := PolBaseChange.rigidified_pull h P.rigid
  sym := PolBaseChange.sym_pull h P.sym
  ample :=
    haveI := P.isAb.proper
    AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample h.1
  ktriv := kTriv_pull h P.isLB (pull_isLB P.isLB _) ((isGen_iff _).1 (isGen_refl (pull_isLB P.isLB φ))) P.ktriv

end GlobalTheory.TorsionTauCompare
