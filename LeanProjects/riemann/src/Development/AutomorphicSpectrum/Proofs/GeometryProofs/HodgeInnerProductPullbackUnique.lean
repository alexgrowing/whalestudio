import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertDataEqOfLbIsoPowPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingSmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeUnique

open GlobalTheory.TangentOrigin ReciprocityTheory.ChartRestriction.G.TB.ValAt

section Val

variable {X : Scheme.{0}} {M M' : LB X}

theorem val_unit_inv (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)ˣ) :
    valAt' x U (s⁻¹).val = (valAt' x U s.val)⁻¹ :=
  map_units_inv (valHom x U h) s

theorem val_unit_ne (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)ˣ) : valAt' x U s.val ≠ 0 :=
  (s.isUnit.map (valHom x U h)).ne_zero

theorem val_self (hM : M.IsLB) (x : Sp ℂ ⟶ X) (i : M.ι) (h : ⊤ ≤ x ⁻¹ᵁ M.U i) :
    valAt' x (M.U i ⊓ M.U i) (M.g i i).val = 1 := by
  have e := congrArg (fun t : Γ(X, M.U i)ˣ => valAt' x (M.U i) t.val) (hM.g_self i)
  simp only [Units.val_one] at e
  rw [TB.ValAt.valAt'_one x _ h] at e
  exact (TB.ValAt.valAt'_res x (le_inf le_rfl le_rfl : M.U i ≤ M.U i ⊓ M.U i) h _).symm.trans e

def isoU (w : LB.Iso M M') (a : M'.ι) (b : M.ι) : Γ(X, M'.U a ⊓ M.U b)ˣ := w.s (a, b)

theorem val_iso (w : LB.Iso M M') (hw : w.IsGen) (x : Sp ℂ ⟶ X) (a a' : M'.ι) (b b' : M.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((M'.U a ⊓ M.U b) ⊓ (M'.U a' ⊓ M.U b'))) :
    valAt' x (M'.U a ⊓ M.U b) (isoU w a b).val * valAt' x (M.U b ⊓ M.U b') (M.g b b').val =
      valAt' x (M'.U a ⊓ M'.U a') (M'.g a a').val * valAt' x (M'.U a' ⊓ M.U b') (isoU w a' b').val := by
  have hm : ⊤ ≤ x ⁻¹ᵁ (M.U b ⊓ M.U b') := fun p hp => ⟨(h hp).1.2, (h hp).2.2⟩
  have hunit : res (inf_le_left : (M'.U a ⊓ M.U b) ⊓ (M'.U a' ⊓ M.U b') ≤ M'.U a ⊓ M.U b) (isoU w a b) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (M'.U a ⊓ M.U b) ⊓ (M'.U a' ⊓ M.U b') ≤ M'.U a ⊓ M'.U a') (M'.g a a') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (M'.U a ⊓ M.U b) ⊓ (M'.U a' ⊓ M.U b') ≤ M.U b ⊓ M.U b') (M.g b b'))⁻¹ *
      res (inf_le_right : (M'.U a ⊓ M.U b) ⊓ (M'.U a' ⊓ M.U b') ≤ M'.U a' ⊓ M.U b') (isoU w a' b') :=
    hw (a, b) (a', b')
  have e := congrArg (fun t : Γ(X, (M'.U a ⊓ M.U b) ⊓ (M'.U a' ⊓ M.U b'))ˣ =>
    valAt' x ((M'.U a ⊓ M.U b) ⊓ (M'.U a' ⊓ M.U b')) t.val) hunit
  simp only [Units.val_mul] at e
  rw [TB.ValAt.valAt'_mul, TB.ValAt.valAt'_mul, val_unit_inv x _ h] at e
  have r1 := TB.ValAt.valAt'_res x (inf_le_left : (M'.U a ⊓ M.U b) ⊓ (M'.U a' ⊓ M.U b') ≤ M'.U a ⊓ M.U b) h (isoU w a b).val
  have r2 := TB.ValAt.valAt'_res x (inf_le_right : (M'.U a ⊓ M.U b) ⊓ (M'.U a' ⊓ M.U b') ≤ M'.U a' ⊓ M.U b') h (isoU w a' b').val
  have r3 := TB.ValAt.valAt'_res x (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
    (M'.U a ⊓ M.U b) ⊓ (M'.U a' ⊓ M.U b') ≤ M'.U a ⊓ M'.U a') h (M'.g a a').val
  have r4 := TB.ValAt.valAt'_res x (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
    (M'.U a ⊓ M.U b) ⊓ (M'.U a' ⊓ M.U b') ≤ M.U b ⊓ M.U b') h (M.g b b').val
  have hne := val_unit_ne x _ hm (M.g b b')
  have e' : valAt' x (M'.U a ⊓ M.U b) (isoU w a b).val = valAt' x (M'.U a ⊓ M'.U a') (M'.g a a').val *
      (valAt' x (M.U b ⊓ M.U b') (M.g b b').val)⁻¹ * valAt' x (M'.U a' ⊓ M.U b') (isoU w a' b').val :=
    r1.symm.trans (e.trans (by
      refine congrArg₂ (· * ·) (congrArg₂ (· * ·) r3 (congrArg (·⁻¹) r4)) r2))
  rw [e']
  field_simp

end Val

section Transport

variable {A : Over (Sp ℂ)} [GrpObj A] {M M' : LB A.left} {g : ℕ}

theorem exists_chart_at (hM : M.IsLB) (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) : ∃ b, ⊤ ≤ x.left ⁻¹ᵁ M.U b := by
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q =>
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  have hc : x.left pt ∈ (⨆ i, M.U i) := by
    rw [hM.cover]
    trivial
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
  refine ⟨b, fun q _ => ?_⟩
  rw [hsub q]
  exact hb

def frameAt (u : HolUnif A M g) (w : LB.Iso M M') (b : (Fin g → ℂ) → M.ι) (a : M'.ι) (z : Fin g → ℂ) : ℂ :=
  valAt' (u.ex z).left (M'.U a ⊓ M.U (b z)) (isoU w a (b z)).val * u.fr (b z) z

theorem frameAt_eq (hM' : M'.IsLB) (u : HolUnif A M g) (w : LB.Iso M M') (hw : w.IsGen) {b : (Fin g → ℂ) → M.ι}
    (hb : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U (b z)) (a : M'.ι) (b₁ : M.ι) (z : Fin g → ℂ)
    (ha : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M'.U a) (h₁ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U b₁) :
    frameAt u w b a z = valAt' (u.ex z).left (M'.U a ⊓ M.U b₁) (isoU w a b₁).val * u.fr b₁ z := by
  have hall : ⊤ ≤ (u.ex z).left ⁻¹ᵁ ((M'.U a ⊓ M.U (b z)) ⊓ (M'.U a ⊓ M.U b₁)) :=
    fun p hp => ⟨⟨ha hp, hb z hp⟩, ⟨ha hp, h₁ hp⟩⟩
  have e := val_iso w hw (u.ex z).left a a (b z) b₁ hall
  rw [val_self hM' _ a ha, _root_.one_mul] at e
  have hc := u.fr_compat (b z) b₁ z (fun p hp => ⟨hb z hp, h₁ hp⟩)
  rw [frameAt, hc, ← _root_.mul_assoc, e]

def transport (u : HolUnif A M g) (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M M') (hw : w.IsGen) : HolUnif A M' g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := frameAt u w fun z => Classical.choose (exists_chart_at hM (u.ex z))
  fr_hol := by
    intro a z₀ hz₀
    have hb := fun z => Classical.choose_spec (exists_chart_at hM (u.ex z))
    set b : (Fin g → ℂ) → M.ι := fun z => Classical.choose (exists_chart_at hM (u.ex z)) with hbdef
    set b₀ := b z₀ with hb₀
    let N : Set (Fin g → ℂ) := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (M'.U a ⊓ M.U b₀)}
    have hN : IsOpen N := (u.hol _ 0).1
    have hz : z₀ ∈ N := fun p hp => ⟨hz₀ hp, hb z₀ hp⟩
    have hd1 : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left (M'.U a ⊓ M.U b₀) (isoU w a b₀).val) z₀ :=
      (u.hol _ _).2.differentiableAt (hN.mem_nhds hz)
    have hO : IsOpen {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U b₀} := (u.hol _ 0).1
    have hd2 : DifferentiableAt ℂ (u.fr b₀) z₀ :=
      (u.fr_hol b₀).differentiableAt (hO.mem_nhds (hb z₀))
    refine ((hd1.mul hd2).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hN.mem_nhds hz] with z hzN
    exact frameAt_eq hM' u w hw hb a b₀ z (fun p hp => (hzN hp).1) (fun p hp => (hzN hp).2)
  fr_ne := by
    intro a z hz
    have hb := Classical.choose_spec (exists_chart_at hM (u.ex z))
    have hall : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (M'.U a ⊓ M.U (Classical.choose (exists_chart_at hM (u.ex z)))) :=
      fun p hp => ⟨hz hp, hb hp⟩
    exact mul_ne_zero (val_unit_ne _ _ hall _) (u.fr_ne _ z hb)
  fr_compat := by
    intro i j z hz
    have hb := Classical.choose_spec (exists_chart_at hM (u.ex z))
    have hall : ⊤ ≤ (u.ex z).left ⁻¹ᵁ ((M'.U i ⊓ M.U (Classical.choose (exists_chart_at hM (u.ex z)))) ⊓
        (M'.U j ⊓ M.U (Classical.choose (exists_chart_at hM (u.ex z))))) :=
      fun p hp => ⟨⟨(hz hp).1, hb hp⟩, ⟨(hz hp).2, hb hp⟩⟩
    have e := val_iso w hw (u.ex z).left i j (Classical.choose (exists_chart_at hM (u.ex z)))
      (Classical.choose (exists_chart_at hM (u.ex z))) hall
    rw [val_self hM _ _ hb, _root_.mul_one] at e
    simp only [frameAt]
    rw [e, _root_.mul_assoc]

theorem frameAt_period (hM' : M'.IsLB) (u : HolUnif A M g) (w : LB.Iso M M') (hw : w.IsGen) {b : (Fin g → ℂ) → M.ι}
    (hb : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U (b z)) (i : M'.ι) (z y : Fin g → ℂ) (hex : u.ex y = u.ex z)
    (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M'.U i) (c : ℂ) (hc : ∀ b₁, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U b₁ → u.fr b₁ z = c * u.fr b₁ y) :
    frameAt u w b i z = c * frameAt u w b i y := by
  have h₁ := hb z
  rw [frameAt_eq hM' u w hw hb i (b z) z hz h₁,
    frameAt_eq hM' u w hw hb i (b z) y (by rw [hex]; exact hz) (by rw [hex]; exact h₁), hex, hc _ h₁]
  ring

theorem transport_isAH (u : HolUnif A M g) (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M M') (hw : w.IsGen)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) :
    (transport u hM hM' w hw).IsAH Hm χ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun l i z hz => ?_⟩
  exact frameAt_period hM' u w hw (fun z => Classical.choose_spec (exists_chart_at hM (u.ex z))) i z _
    (by rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]) hz _ (fun b₁ hb₁ => h4 l b₁ z hb₁)

end Transport
section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem isTangent_one' : IsTangent (1 : epsR ℂ ⟶ A) := by
  unfold IsTangent
  have e : (1 : epsR ℂ ⟶ A).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ η[A].left := by
    rw [Hom.one_def, Over.comp_left]
    congr 1
  rw [e, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
    ext x
    simp
  rw [this]
  simp

theorem isDiff_one_of_fderiv (u : HolUnif A L g) {U : A.left.Opens} (hU : IsAffineOpen U)
    (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) {w : Fin g → ℂ}
    (hw : ∀ s : Γ(A.left, U), fderiv ℂ (fun z => valAt' (u.ex z).left U s) 0 w = 0) :
    u.IsDiff w (1 : epsR ℂ ⟶ A) := by
  have hv : IsTangent (1 : epsR ℂ ⟶ A) := isTangent_one'
  have hvU := (tangent_mem_iff (u := u) hv U).2 h0
  refine (isDiff_iff hv hU hvU h0 w).2 ?_
  rw [(isDiff_iff hv hU hvU h0 0).1 (GlobalTheory.UnifDifferential.isDiff_one u)]
  refine RingHom.ext fun s => TrivSqZeroExt.ext rfl ?_
  rw [jet_snd, jet_snd, map_zero]
  exact (hw s).symm

def transl (u : HolUnif A L g) (z : Fin g → ℂ) : A ⟶ A := (toUnit A ≫ u.ex z) * 𝟙 A

theorem ex_comp_transl (u : HolUnif A L g) (z y : Fin g → ℂ) : u.ex y ≫ transl u z = u.ex (z + y) := by
  rw [transl, MonObj.comp_mul, u.ex_add, Category.comp_id, ← Category.assoc, toUnit_unique (u.ex y ≫ toUnit A) (𝟙 _),
    Category.id_comp]

theorem fderiv_eq_zero_of_isDiff_one (u : HolUnif A L g) {w : Fin g → ℂ} (h : u.IsDiff w (1 : epsR ℂ ⟶ A))
    (z : Fin g → ℂ) {W : A.left.Opens} (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W) (s : Γ(A.left, W)) :
    fderiv ℂ (fun y => valAt' (u.ex y).left W s) z w = 0 := by
  have hv : IsTangent (1 : epsR ℂ ⟶ A) := isTangent_one'
  set T := transl u z with hT
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (T.left ⁻¹ᵁ W) := by
    have e : (u.ex 0 ≫ T).left = (u.ex z).left := by rw [hT, ex_comp_transl, add_zero]
    intro p hp
    have := hz hp
    rw [← e] at this
    exact this
  have hvU := (tangent_mem_iff (u := u) hv _).2 h0
  have e1 := h _ hvU ((T.left.app W).hom s)
  have e2 := GlobalTheory.UnifDifferential.isDiff_one u _ hvU ((T.left.app W).hom s)
  have e3 : fderiv ℂ (fun y => valAt' (u.ex y).left (T.left ⁻¹ᵁ W) ((T.left.app W).hom s)) 0 w = 0 := by
    rw [← e1, e2, map_zero]
  have e4 : (fun y => valAt' (u.ex y).left (T.left ⁻¹ᵁ W) ((T.left.app W).hom s)) =
      fun y => valAt' (u.ex (z + y)).left W s := by
    funext y
    rw [← GlobalTheory.HomLinear.valAt'_comp_left, hT, ex_comp_transl]
  rw [e4, fderiv_comp_add_left (f := fun y => valAt' (u.ex y).left W s), add_zero] at e3
  exact e3

theorem eq_zero_of_isDiff_one (u : HolUnif A L g) {w : Fin g → ℂ} (h : u.IsDiff w (1 : epsR ℂ ⟶ A)) : w = 0 := by
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q =>
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤)
    (Set.mem_univ _)
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
    intro q _
    rw [hsub q]
    exact hpU
  have hcont : Continuous fun t : ℂ => t • w := continuous_id.smul continuous_const
  have hopen : IsOpen ((fun t : ℂ => t • w) ⁻¹' {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U}) := (u.hol U 0).1.preimage hcont
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen 0 (by simpa using h0)
  have hconst : ∀ (s : Γ(A.left, U)) (t : ℂ), t ∈ Metric.ball (0 : ℂ) ρ →
      valAt' (u.ex (t • w)).left U s = valAt' (u.ex ((0 : ℂ) • w)).left U s := by
    intro s t ht
    have hder : ∀ t ∈ Metric.ball (0 : ℂ) ρ, HasDerivAt (fun t : ℂ => valAt' (u.ex (t • w)).left U s) 0 t := by
      intro t ht
      have hm : ⊤ ≤ (u.ex (t • w)).left ⁻¹ᵁ U := hball ht
      have hd : DifferentiableAt ℂ (fun y => valAt' (u.ex y).left U s) (t • w) :=
        (u.hol U s).2.differentiableAt ((u.hol U s).1.mem_nhds hm)
      have hl : HasDerivAt (fun t : ℂ => t • w) w t := by
        simpa using (hasDerivAt_id t).smul_const w
      have := hd.hasFDerivAt.comp_hasDerivAt t hl
      rw [fderiv_eq_zero_of_isDiff_one u h _ hm s] at this
      exact this
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (fun t ht => (hder t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hder t ht).deriv) ht (Metric.mem_ball_self hρ)
  have hmem : ∀ t ∈ Metric.ball (0 : ℂ) ρ, t • w ∈ u.Λ := by
    intro t ht
    have hm : ⊤ ≤ (u.ex (t • w)).left ⁻¹ᵁ U := hball ht
    have hm0 : ⊤ ≤ (u.ex ((0 : ℂ) • w)).left ⁻¹ᵁ U := by simpa using h0
    have e : (u.ex (t • w)).left = (u.ex ((0 : ℂ) • w)).left := ext_evalPt hU hm hm0 (RingHom.ext fun s => by
      rw [← valAt'_eq_evalPt _ _ hm, ← valAt'_eq_evalPt _ _ hm0]
      exact hconst s t ht)
    have e' : u.ex (t • w) = u.ex ((0 : ℂ) • w) := Over.OverMorphism.ext e
    rw [← u.ker, e', zero_smul, ex_zero]
  by_contra hw
  have := u.discrete
  obtain ⟨O, hO, hO0⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1
    (isDiscrete_iff_discreteTopology.2 this) 0 u.Λ.zero_mem
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t • w ∈ O ∧ t ∈ Metric.ball (0 : ℂ) ρ := by
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    refine ((hcont.tendsto 0).eventually (hO.mem_nhds ?_)).and (Metric.ball_mem_nhds _ hρ)
    simpa using (hO0.ge rfl).1
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ := (hev.and self_mem_nhdsWithin).exists
  have h3 : t • w = 0 := hO0.le ⟨h1, hmem t h2⟩
  exact hw ((smul_eq_zero.1 h3).resolve_left ht)

theorem exists_affine (u : HolUnif A L g) : ∃ U : A.left.Opens, IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q =>
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤)
    (Set.mem_univ _)
  refine ⟨U, hU, ?_⟩
  intro q _
  rw [hsub q]
  exact hpU

theorem eq_of_isDiff (u : HolUnif A L g) {v : epsR ℂ ⟶ A} (hv : IsTangent v) {d d' : Fin g → ℂ}
    (h : u.IsDiff d v) (h' : u.IsDiff d' v) : d = d' := by
  obtain ⟨U, hU, h0⟩ := exists_affine u
  have hvU := (tangent_mem_iff (u := u) hv U).2 h0
  exact sub_eq_zero.1 (eq_zero_of_isDiff_one u (isDiff_one_of_fderiv u hU h0 fun s => by
    rw [map_sub, ← h U hvU s, ← h' U hvU s, sub_self]))

theorem exists_linear_compare {A' : Over (Sp ℂ)} [GrpObj A'] {L' : LB A'.left} {g' : ℕ} (u : HolUnif A L g)
    (u' : HolUnif A' L' g') (f : A' ⟶ A) [IsMonHom f] :
    ∃ F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u'.ex z ≫ f := by
  letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with
      mul_comm := fun a b => by
        obtain ⟨z, rfl⟩ := u.ex_onto a
        obtain ⟨w, rfl⟩ := u.ex_onto b
        exact (u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }
  let ex : (Fin g → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (u.ex z)) u.ex_add
  let G' : (Fin g' → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (u'.ex z ≫ f)) (fun z w => by
      change u'.ex (z + w) ≫ f = (u'.ex z ≫ f) * (u'.ex w ≫ f)
      rw [u'.ex_add]
      exact MonObj.mul_comp _ _ f)
  have hhol := GlobalTheory.HomLinear.isHolTo_ex_comp u' f
  obtain ⟨U, hU, h0⟩ := exists_affine u
  have hker : (ex.ker : Set (Fin g → ℂ)) = u.Λ := Set.ext fun z => u.ker z
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_separating (ex := ex) (G := G') u.ex_onto
    (hker ▸ isDiscrete_iff_discreteTopology.2 u.discrete)
    (S := {a | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U})
    (f := fun (s : Γ(A.left, U)) a => valAt' (Additive.toMul a).left U s)
    (by rw [← map_zero ex]; exact h0) (by
      intro a ha b hb h
      refine Over.OverMorphism.ext (f := Additive.toMul a) (g := Additive.toMul b)
        (ext_evalPt (R := ℂ) hU ha hb (RingHom.ext fun s => ?_))
      exact (valAt'_eq_evalPt _ U ha s).symm.trans ((h s).trans (valAt'_eq_evalPt _ U hb s)))
    (u.hol U 0).1 (by
      have := (hhol U 0).1
      simp only [Set.mem_univ, true_and] at this
      exact this) (fun s => (u.hol U s).2) (fun s => by
      have := (hhol U s).2
      simp only [Set.mem_univ, true_and] at this
      exact this) (fun w hw => eq_zero_of_isDiff_one u (isDiff_one_of_fderiv u hU h0 hw))
  exact ⟨F, hF⟩

end Unif

section Pull

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ℂ ⟶ X}
  {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ G.left}

def push (h : IsGrpPullback A G z φ) {T : Over (Sp ℂ)} (x : T ⟶ A) : Over.mk (T.hom ≫ z) ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]
    rfl)

theorem one_left_comp (h : IsGrpPullback A G z φ) (T : Over (Sp ℂ)) :
    (1 : T ⟶ A).left ≫ φ = (1 : Over.mk (T.hom ≫ z) ⟶ G).left := by
  have e := h.2 T 1 1 (push h 1) (push h 1) rfl rfl
  rw [_root_.mul_one] at e
  have e' : push h 1 * push h 1 = push h (1 : T ⟶ A) := Over.OverMorphism.ext e
  exact congrArg (·.left) (mul_eq_left.1 e')

theorem one_left {Y : Scheme.{0}} (y : Y ⟶ X) : (1 : Over.mk y ⟶ G).left = y ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

def lft (h : IsGrpPullback A G z φ) (v : epsAt z ⟶ G) : epsR ℂ ⟶ A :=
  Over.homMk (h.1.lift v.left (spMap (algebraMap ℂ (DualNumber ℂ))) (Over.w v)) (h.1.lift_snd _ _ _)

theorem lft_left (h : IsGrpPullback A G z φ) (v : epsAt z ⟶ G) : (lft h v).left ≫ φ = v.left :=
  h.1.lift_fst _ _ _

theorem lft_unique (h : IsGrpPullback A G z φ) {v : epsAt z ⟶ G} {v' : epsR ℂ ⟶ A} (e : v'.left ≫ φ = v.left) :
    v' = lft h v :=
  Over.OverMorphism.ext (h.1.hom_ext (e.trans (lft_left h v).symm) (by rw [Over.w, Over.w]))

theorem lft_mul (h : IsGrpPullback A G z φ) (v w : epsAt z ⟶ G) : lft h (v * w) = lft h v * lft h w :=
  (lft_unique h (h.2 (epsR ℂ) (lft h v) (lft h w) v w (lft_left h v).symm (lft_left h w).symm).symm).symm

theorem isTangent_lft (h : IsGrpPullback A G z φ) {v : epsAt z ⟶ G} (hv : IsTanAt G z v) : IsTangent (lft h v) := by
  unfold IsTangent
  refine h.1.hom_ext ?_ ?_
  · rw [Category.assoc, lft_left]
    refine Eq.trans hv ?_
    have e := one_left_comp h (𝟙_ (Over (Sp ℂ)))
    rw [Hom.one_def, toUnit_unit, Category.id_comp] at e
    rw [e, one_left, one_left]
    simp
  · rw [Category.assoc]
    have e1 : (lft h v).left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w _
    have e2 : η[A].left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
    rw [e1, e2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext x
      simp
    rw [this]
    simp

theorem exists_map (h : IsGrpPullback A G z φ) {A' : Over (Sp ℂ)} [GrpObj A'] {φ' : A'.left ⟶ G.left}
    (h' : IsGrpPullback A' G z φ') : ∃ f : A' ⟶ A, IsMonHom f ∧ f.left ≫ φ = φ' := by
  let f : A' ⟶ A := Over.homMk (h.1.lift φ' A'.hom h'.1.w) (h.1.lift_snd _ _ _)
  have hf : f.left ≫ φ = φ' := h.1.lift_fst _ _ _
  refine ⟨f, isMonHom_of_mul _ fun T x y => ?_, hf⟩
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))
  have e1 := h'.2 T x y (push h' x) (push h' y) rfl rfl
  have e2 := h.2 T (x ≫ f) (y ≫ f) (push h' x) (push h' y)
    (by simp [push, hf]) (by simp [push, hf])
  rw [Over.comp_left, Category.assoc, hf, ← e1, e2]

end Pull

section Tangent

variable {S' S : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

def pushOver (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') : Over.mk (T.hom ≫ f) ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]
    rfl)

theorem one_left_pull (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  have e := h.2 T 1 1 (pushOver h 1) (pushOver h 1) rfl rfl
  rw [_root_.mul_one] at e
  have e' : pushOver h 1 * pushOver h 1 = pushOver h (1 : T ⟶ G') := Over.OverMorphism.ext e
  exact congrArg (·.left) (mul_eq_left.1 e')

theorem isTanAt_iff (h : IsGrpPullback G' G f φ) {x : Sp ℂ ⟶ S'} {v' : epsAt x ⟶ G'} {v : epsAt (x ≫ f) ⟶ G}
    (e : v'.left ≫ φ = v.left) : IsTanAt G' x v' ↔ IsTanAt G (x ≫ f) v := by
  have h1 : x ≫ η[G'].left ≫ φ = (x ≫ f) ≫ η[G].left := by
    have e0 := one_left_pull h (Over.mk x)
    rw [one_left, one_left] at e0
    simpa using e0
  have t1 : IsTanAt G' x v' ↔ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v'.left = x ≫ η[G'].left := by
    unfold IsTanAt
    rw [one_left]
  have t2 : IsTanAt G (x ≫ f) v ↔ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (x ≫ f) ≫ η[G].left := by
    unfold IsTanAt
    rw [one_left]
  rw [t1, t2]
  constructor
  · intro hv
    rw [← e, ← Category.assoc, hv, Category.assoc, h1]
  · intro hv
    refine h.1.hom_ext ?_ ?_
    · have e0 : (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v'.left) ≫ φ = (x ≫ f) ≫ η[G].left := by
        rw [Category.assoc, e, hv]
      exact e0.trans (h1.symm.trans (Category.assoc _ _ _).symm)
    · have e1 : v'.left ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x := Over.w v'
      have e2 : η[G'].left ≫ G'.hom = 𝟙 _ := by simpa using Over.w η[G']
      rw [Category.assoc, Category.assoc, e1, e2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have e3 : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
        ext a
        simp
      rw [e3]
      simp

end Tangent

section Unique

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {L : LB G.left} {z : Sp ℂ ⟶ X} {v w : epsAt z ⟶ G} {c c' : ℂ}

theorem hodgeInnerProduct_eq (h : HodgeIP G L z v w c) (h' : HodgeIP G L z v w c') : c = c' := by
  obtain ⟨hL, hv, hw, A, _, φ, g, u, Hm, χ, v₁, w₁, a, b, hp, hAH, e1, e2, da, db, rfl⟩ := h
  obtain ⟨-, -, -, A', _, φ', g', u', Hm', χ', v₂, w₂, a', b', hp', hAH', e1', e2', da', db', rfl⟩ := h'
  obtain ⟨f, _, hf⟩ := exists_map hp hp'
  obtain ⟨F, hF⟩ := exists_linear_compare u u' f
  have hΛ : ∀ l ∈ u'.Λ, F l ∈ u.Λ := fun l hl => (u.ker _).1 (by
    rw [hF, (u'.ker l).2 hl, MonObj.one_comp])
  have iso : LBIso (lbPow (L.pull φ') 1) (lbPow ((L.pull φ).pull f.left) 1) :=
    GlobalTheory.lbIso_lbPow (GlobalTheory.GenSpread.lbIso_pull_pull hL f.left hf.symm) 1
  have hH := (GlobalTheory.appellHumbert_data_eq_of_lbIso_pow_pull A' A (L.pull φ') (L.pull φ) g' g u' u Hm' Hm χ' χ f F hΛ 1
    one_pos (pull_isLB hL φ') (pull_isLB hL φ) hAH' hAH hF iso).1
  have coord : ∀ {t : epsAt z ⟶ G} {x : epsR ℂ ⟶ A} {x' : epsR ℂ ⟶ A'} {d : Fin g → ℂ} {d' : Fin g' → ℂ},
      IsTanAt G z t → x.left ≫ φ = t.left → x'.left ≫ φ' = t.left → u.IsDiff d x → u'.IsDiff d' x' → F d' = d := by
    intro t x x' d d' ht ex ex' dd dd'
    have hx : IsTangent x := lft_unique hp ex ▸ isTangent_lft hp ht
    have hx' : IsTangent x' := lft_unique hp' ex' ▸ isTangent_lft hp' ht
    have e : x' ≫ f = x := Over.OverMorphism.ext (hp.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, hf, ex', ex]) (by rw [Over.w, Over.w]))
    exact eq_of_isDiff u hx (e ▸ GlobalTheory.HomLinear.isDiff_comp u' u f F hF hx' dd') dd
  have key : hermForm Hm' b' a' = hermForm Hm b a := by
    rw [hH, coord hv e1 e1' da da', coord hw e2 e2' db db']
  exact (congrArg (fun t => (Real.pi : ℂ) * t) key).symm

end Unique

section Pull

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {L : LB G.left} {L' : LB G'.left}
  {z : Sp ℂ ⟶ X} {z' : Sp ℂ ⟶ X'} {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G'} {c : ℂ}

theorem hodgeInnerProduct_transfer (hL' : L'.IsLB) (hv : IsTanAt G' z' v') (hw : IsTanAt G' z' w') (h : HodgeIP G L z v w c)
    (H : ∀ (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ G.left), IsGrpPullback A G z φ →
      ∃ φ' : A.left ⟶ G'.left, IsGrpPullback A G' z' φ' ∧ LBIso (L.pull φ) (L'.pull φ') ∧
        (∀ x : epsR ℂ ⟶ A, x.left ≫ φ = v.left → x.left ≫ φ' = v'.left) ∧
        ∀ x : epsR ℂ ⟶ A, x.left ≫ φ = w.left → x.left ≫ φ' = w'.left) :
    HodgeIP G' L' z' v' w' c := by
  obtain ⟨hL, -, -, A, _, φ, g, u, Hm, χ, x, y, a, b, hp, hAH, e1, e2, da, db, rfl⟩ := h
  obtain ⟨φ', hp', ⟨s, hs⟩, f1, f2⟩ := H A φ hp
  exact ⟨hL', hv, hw, A, inferInstance, φ', g, transport u (pull_isLB hL φ) (pull_isLB hL' φ') s hs, Hm, χ, x, y, a, b, hp',
    transport_isAH u _ _ s hs hAH, f1 x e1, f2 y e2, da, db, rfl⟩

end Pull

theorem lift_eq {S' S : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {p : G'.left ⟶ G.left}
    (hc : IsPullback p G'.hom G.hom f) {A : Over (Sp ℂ)} {a : A.left ⟶ G.left} {φ : A.left ⟶ G'.left} {z : Sp ℂ ⟶ S'}
    (h₁ : φ ≫ p = a) (h₂ : φ ≫ G'.hom = A.hom ≫ z) {x : epsR ℂ ⟶ A} {v' : epsAt z ⟶ G'} {t : Sp (DualNumber ℂ) ⟶ G.left}
    (e : x.left ≫ a = t) (ev : v'.left ≫ p = t) : x.left ≫ φ = v'.left := by
  refine hc.hom_ext ?_ ?_
  · rw [Category.assoc, h₁, e, ev]
  · have e1 : x.left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w x
    have e2 : v'.left ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ z := Over.w v'
    rw [Category.assoc, h₂, e2, ← Category.assoc, e1]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S' S : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (z : Sp ℂ ⟶ S') (v' w' : epsAt z ⟶ t'.G) (v w : epsAt (z ≫ f) ⟶ t.G), v'.left ≫ m.φ = v.left → w'.left ≫ m.φ = w.left → (∀ c, HodgeIP t'.G t'.PP.L z v' w' c ↔ HodgeIP t.G t.PP.L (z ≫ f) v w c) ∧ ∀ c c', HodgeIP t.G t.PP.L (z ≫ f) v w c → HodgeIP t.G t.PP.L (z ≫ f) v w c' → c = c' := by
  intro E _ _ _ H S' S t' t f m z v' w' v w ev ew
  refine ⟨fun c => ⟨fun h => ?_, fun h => ?_⟩, fun c c' h h' => hodgeInnerProduct_eq h h'⟩
  · refine hodgeInnerProduct_transfer t.PP.isLB ((isTanAt_iff m.cart ev).1 h.isTanAt_left) ((isTanAt_iff m.cart ew).1 h.isTanAt_right) h ?_
    intro A _ φ hp
    refine ⟨φ ≫ m.φ, hp.comp m.cart, GlobalTheory.GenSpread.lbIso_pull_of_lbIso (GlobalTheory.Ex.UnifModel.iso_of_map m) φ rfl, ?_, ?_⟩
    · intro x e
      rw [← Category.assoc, e, ev]
    · intro x e
      rw [← Category.assoc, e, ew]
  · refine hodgeInnerProduct_transfer t'.PP.isLB ((isTanAt_iff m.cart ev).2 h.isTanAt_left) ((isTanAt_iff m.cart ew).2 h.isTanAt_right) h ?_
    intro A _ a hp
    have hw' : a ≫ t.G.hom = (A.hom ≫ z) ≫ f := by rw [hp.1.w, Category.assoc]
    let φ := m.cart.1.lift a (A.hom ≫ z) hw'
    have h₁ : φ ≫ m.φ = a := m.cart.1.lift_fst _ _ _
    have h₂ : φ ≫ t'.G.hom = A.hom ≫ z := m.cart.1.lift_snd _ _ _
    refine ⟨φ, m.cart.cancel (by rw [h₁]; exact hp) h₂, ?_, ?_, ?_⟩
    · exact LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_of_lbIso (GlobalTheory.Ex.UnifModel.iso_of_map m) φ h₁.symm)
    · intro x e
      exact lift_eq m.cart.1 h₁ h₂ e ev
    · intro x e
      exact lift_eq m.cart.1 h₁ h₂ e ew

end GlobalTheory.CompanionTheory.Ar.HodgeUnique
