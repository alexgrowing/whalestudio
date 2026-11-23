import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtensionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans

open ReciprocityTheory.ChartRestriction.G.DVR

section Value

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem toStk_valF_fn {Ω : Type} [Field Ω] {Y : Scheme.{0}} (x : Sp Ω ⟶ Y) (U : Y.Opens) (z : Sp Ω) (h : x z ∈ U)
    (a : Γ(Y, U)) : toStk z (valF x U a) = gs x z U a := by
  rw [valF, dif_pos ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp Ω).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp Ω).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

abbrev PowB {Y : Scheme.{0}} (M : LB Y) (n : ℕ) : LB Y := LB.LinComb M (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (n : ℤ))

theorem mem_powB {Y : Scheme.{0}} {M : LB Y} {n : ℕ} {y : Y} {j : Fin 1 → M.ι} : y ∈ (PowB M n).U j ↔ y ∈ M.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by rw [Subsingleton.elim k 0]; exact h⟩

theorem powIso_le (n : ℕ) (p : (PUnit → Fin 1 → L.ι) × (Fin 1 → L'.ι)) :
    ((PowB L n).pull F).U p.1 ⊓ (PowB L' n).U p.2 ≤ (L.pull F).U (fun _ => p.1 PUnit.unit 0) ⊓ L'.U (p.2 0) :=
  fun _ hy => ⟨mem_pull.2 (mem_powB.1 (mem_pull.1 hy.1)), mem_powB.1 hy.2⟩

def powIso (w : LB.Iso L' (L.pull F)) (n : ℕ) : LB.Iso (PowB L' n) ((PowB L n).pull F) where
  s := fun p => res (powIso_le n p) (w.s (fun _ => p.1 PUnit.unit 0, p.2 0)) ^ n

theorem gw_powIso (w : LB.Iso L' (L.pull F)) (n : ℕ) {Y : Scheme.{0}} (f : Y ⟶ X') (y : Y) (j : Fin 1 → L.ι)
    (k : Fin 1 → L'.ι) (hj : F (f y) ∈ L.U (j 0)) (hk : f y ∈ L'.U (k 0)) :
    gw (powIso w n) f y j k = gw w f y (j 0) (k 0) ^ n := by
  have hm : f y ∈ ((PowB L n).pull F).U (fun _ => j) ⊓ (PowB L' n).U k :=
    ⟨mem_pull.2 (mem_powB.2 hj), mem_powB.2 hk⟩
  exact (map_pow _ _ _).trans (congrArg (· ^ n) (gm_res f y _ hm _))

theorem pGen_powIso {w : LB.Iso L' (L.pull F)} (hw : PGen w) (n : ℕ) : PGen (powIso w n) := by
  intro Y f y j j' k k' hj hj' hk hk'
  have a₁ := mem_powB.1 hj
  have a₂ := mem_powB.1 hj'
  have a₃ := mem_powB.1 hk
  have a₄ := mem_powB.1 hk'
  have g₁ : gm (f ≫ F) y ((PowB L n).U j ⊓ (PowB L n).U j') ((PowB L n).g j j') =
      gm (f ≫ F) y _ (L.g (j 0) (j' 0)) ^ n :=
    (gm_linComb L _ _ (f ≫ F) y j j' hj hj').trans (by simp only [Fin.prod_univ_one, Category.comp_id, zpow_natCast])
  have g₂ : gm f y ((PowB L' n).U k ⊓ (PowB L' n).U k') ((PowB L' n).g k k') =
      gm f y _ (L'.g (k 0) (k' 0)) ^ n :=
    (gm_linComb L' _ _ f y k k' hk hk').trans (by simp only [Fin.prod_univ_one, Category.comp_id, zpow_natCast])
  rw [gw_powIso w n f y j k a₁ a₃, gw_powIso w n f y j' k' a₂ a₄, hw Y f y _ _ _ _ a₁ a₂ a₃ a₄, g₁, g₂, mul_pow, mul_pow,
    inv_pow]

def wv {Ω : Type} [Field Ω] (w : LB.Iso L' (L.pull F)) (x : Sp Ω ⟶ X') (j : L.ι) (k : L'.ι) : Ω :=
  valF x ((L.pull F).U (fun _ => j) ⊓ L'.U k) (w.s (fun _ => j, k)).val

theorem toStk_wv {Ω : Type} [Field Ω] (w : LB.Iso L' (L.pull F)) (x : Sp Ω ⟶ X') (z : Sp Ω) {j : L.ι} {k : L'.ι}
    (hj : (x ≫ F) z ∈ L.U j) (hk : x z ∈ L'.U k) : toStk z (wv w x j k) = (gw w x z j k).val :=
  toStk_valF x ((L.pull F).U (fun _ => j) ⊓ L'.U k) z ⟨mem_pull.2 hj, hk⟩ _

theorem wv_ne {Ω : Type} [Field Ω] (w : LB.Iso L' (L.pull F)) (x : Sp Ω ⟶ X') (z : Sp Ω) {j : L.ι} {k : L'.ι}
    (hj : (x ≫ F) z ∈ L.U j) (hk : x z ∈ L'.U k) : wv w x j k ≠ 0 := fun h => by
  have := toStk_wv w x z hj hk
  rw [h, map_zero] at this
  exact (gw w x z j k).ne_zero this.symm

theorem wv_trans {w : LB.Iso L' (L.pull F)} (hw : PGen w) {Ω : Type} [Field Ω] (x : Sp Ω ⟶ X') (z : Sp Ω) {j j' : L.ι}
    {k k' : L'.ι} (hj : (x ≫ F) z ∈ L.U j) (hj' : (x ≫ F) z ∈ L.U j') (hk : x z ∈ L'.U k) (hk' : x z ∈ L'.U k') :
    wv w x j k * valF x _ (L'.g k k').val = valF (x ≫ F) _ (L.g j j').val * wv w x j' k' := by
  apply (toStk z).injective
  rw [map_mul, map_mul, toStk_wv w x z hj hk, toStk_wv w x z hj' hk', toStk_valF x (L'.U k ⊓ L'.U k') z ⟨hk, hk'⟩,
    toStk_valF (x ≫ F) (L.U j ⊓ L.U j') z ⟨hj, hj'⟩, hw _ x z j j' k k' hj hj' hk hk']
  simp only [← Units.val_mul]
  congr 1
  rw [mul_right_comm, _root_.mul_assoc, _root_.mul_assoc, inv_mul_cancel_left]

theorem exists_sec {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (n : ℕ) (s : Out.H0 L n) :
    ∃ s' : Out.H0 L' n, ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ X') (z : Sp Ω) (j : L.ι) (k : L'.ι), (x ≫ F) z ∈ L.U j →
      x z ∈ L'.U k → valF (x ≫ F) _ (s.f fun _ => j) = wv w x j k ^ n * valF x _ (s'.f fun _ => k) := by
  obtain ⟨s', hs'⟩ := sec_pull_down (pGen_powIso hw n) (linComb_isLB L hL _ _) (linComb_isLB L' hL' _ _) s
  refine ⟨s', fun Ω _ x z j k hj hk => ?_⟩
  have h₁ : (x ≫ F) z ∈ (PowB L n).U fun _ => j := mem_powB.2 hj
  have h₂ : x z ∈ (PowB L' n).U fun _ => k := mem_powB.2 hk
  have e := hs' _ x z (fun _ => j) (fun _ => k) h₁ h₂
  rw [gw_powIso w n x z _ _ hj hk] at e
  apply (toStk z).injective
  rw [map_mul, map_pow, toStk_wv w x z hj hk, toStk_valF_fn _ _ z h₁, toStk_valF_fn _ _ z h₂, e, Units.val_pow_eq_pow_val]

end Value

section Frame

open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections

abbrev pt₀ : Sp ℂ := (default : PrimeSpectrum ℂ)

theorem valF_pull_g {Y X₀ : Scheme.{0}} (M : LB X₀) (Φ : Y ⟶ X₀) {Ω : Type} [Field Ω] (x : Sp Ω ⟶ Y) (z : Sp Ω)
    (J J' : PUnit → M.ι) (h : (x ≫ Φ) z ∈ M.U (J PUnit.unit)) (h' : (x ≫ Φ) z ∈ M.U (J' PUnit.unit)) :
    valF x ((M.pull Φ).U J ⊓ (M.pull Φ).U J') ((M.pull Φ).g J J').val =
      valF (x ≫ Φ) (M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit)) (M.g (J PUnit.unit) (J' PUnit.unit)).val := by
  have a : x z ∈ (M.pull Φ).U J := mem_pull.2 h
  have b : x z ∈ (M.pull Φ).U J' := mem_pull.2 h'
  apply (toStk z).injective
  rw [toStk_valF x ((M.pull Φ).U J ⊓ (M.pull Φ).U J') z ⟨a, b⟩,
    toStk_valF (x ≫ Φ) (M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit)) z ⟨h, h'⟩, gm_pull_g M Φ x z J J' a b]

theorem valF_g_self {X₀ : Scheme.{0}} {M : LB X₀} (hM : M.IsLB) {Ω : Type} [Field Ω] (x : Sp Ω ⟶ X₀) (z : Sp Ω) {i : M.ι}
    (h : x z ∈ M.U i) : valF x (M.U i ⊓ M.U i) (M.g i i).val = 1 := by
  apply (toStk z).injective
  rw [toStk_valF x (M.U i ⊓ M.U i) z ⟨h, h⟩, gm_self hM x z h, map_one]
  rfl

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ X'} {g : ℕ}

def chartOf (hL' : L'.IsLB) (x : Sp ℂ ⟶ X') : L'.ι := (exists_chart hL' (x pt₀)).choose

theorem chartOf_mem (hL' : L'.IsLB) (x : Sp ℂ ⟶ X') : x pt₀ ∈ L'.U (chartOf hL' x) :=
  (exists_chart hL' (x pt₀)).choose_spec

def pz (u : HolUnif A (L'.pull φ) g) (z : Fin g → ℂ) : Sp ℂ ⟶ X' := (u.ex z).left ≫ φ

def moveFr (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (u : HolUnif A (L'.pull φ) g) (j : L.ι) (z : Fin g → ℂ) : ℂ :=
  wv w (pz u z) j (chartOf hL' (pz u z)) * u.fr (fun _ => chartOf hL' (pz u z)) z

theorem top_pull (u : HolUnif A (L'.pull φ) g) (z : Fin g → ℂ) (k : L'.ι) :
    ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L'.pull φ).U (fun _ => k) ↔ pz u z pt₀ ∈ L'.U k :=
  (top_le_iff_mem (u.ex z).left _ pt₀).trans mem_pull

theorem top_pull₂ (u : HolUnif A (L'.pull φ) g) (z : Fin g → ℂ) (J : PUnit → L.ι) :
    ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull (φ ≫ F)).U J ↔ (pz u z ≫ F) pt₀ ∈ L.U (J PUnit.unit) :=
  (top_le_iff_mem (u.ex z).left _ pt₀).trans mem_pull

theorem moveFr_eq {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (u : HolUnif A (L'.pull φ) g)
    {j : L.ι} {k : L'.ι} {z : Fin g → ℂ} (hj : (pz u z ≫ F) pt₀ ∈ L.U j) (hk : pz u z pt₀ ∈ L'.U k) :
    moveFr hL' w u j z = wv w (pz u z) j k * u.fr (fun _ => k) z := by
  have h₀ := chartOf_mem hL' (pz u z)
  have e := wv_trans hw (pz u z) pt₀ hj hj h₀ hk
  rw [valF_g_self hL _ pt₀ hj, _root_.one_mul] at e
  have c := u.fr_compat (fun _ => chartOf hL' (pz u z)) (fun _ => k) z
    ((top_le_iff_mem _ _ pt₀).2 ⟨mem_pull.2 h₀, mem_pull.2 hk⟩)
  have v : valAt' (u.ex z).left _ ((L'.pull φ).g (fun _ => chartOf hL' (pz u z)) (fun _ => k)).val =
      valF (pz u z) _ (L'.g (chartOf hL' (pz u z)) k).val := valF_pull_g L' φ (u.ex z).left pt₀ _ _ h₀ hk
  rw [moveFr, c, v, ← _root_.mul_assoc, e]

end Frame

section Move

open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ X'} {g : ℕ}

theorem moveFr_hol {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (u : HolUnif A (L'.pull φ) g)
    (J : PUnit → L.ι) :
    DifferentiableOn ℂ (moveFr hL' w u (J PUnit.unit)) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull (φ ≫ F)).U J} := by
  intro z₀ hz₀
  set j := J PUnit.unit with hjdef
  have hj₀ : (pz u z₀ ≫ F) pt₀ ∈ L.U j := (top_pull₂ u z₀ J).1 hz₀
  set k := chartOf hL' (pz u z₀) with hkdef
  have hk₀ : pz u z₀ pt₀ ∈ L'.U k := chartOf_mem hL' _
  let V : X'.Opens := (L.pull F).U (fun _ => j) ⊓ L'.U k
  have hol := u.hol (φ ⁻¹ᵁ V) ((φ.app V).hom (w.s (fun _ => j, k)).val)
  have mem₀ : z₀ ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ V)} :=
    (top_le_iff_mem (u.ex z₀).left _ pt₀).2 (show pz u z₀ pt₀ ∈ V from ⟨mem_pull.2 hj₀, hk₀⟩)
  have inV : ∀ z, z ∈ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ V)} → pz u z pt₀ ∈ V := fun z hz =>
    (top_le_iff_mem (u.ex z).left _ pt₀).1 hz
  have nhd := hol.1.mem_nhds mem₀
  have d₁ : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left (φ ⁻¹ᵁ V) ((φ.app V).hom (w.s (fun _ => j, k)).val)) z₀ :=
    (hol.2 z₀ mem₀).differentiableAt nhd
  have d₂ : DifferentiableAt ℂ (u.fr (fun _ => k)) z₀ := by
    have open₂ : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L'.pull φ).U (fun _ => k)} ∈ nhds z₀ :=
      Filter.mem_of_superset nhd fun z hz => (top_pull u z k).2 (inV z hz).2
    exact (u.fr_hol (fun _ => k) z₀ (mem_of_mem_nhds open₂)).differentiableAt open₂
  refine ((d₁.mul d₂).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [nhd] with z hz
  have h := inV z hz
  have hjz : (pz u z ≫ F) pt₀ ∈ L.U j := (mem_pull (L := L) (F := F) (J := fun _ => j)).1 h.1
  exact (moveFr_eq hw hL hL' u hjz h.2).trans (congrArg (· * _) (valAt'_comp _ φ V _).symm)

def moveUnif {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (u : HolUnif A (L'.pull φ) g) :
    HolUnif A (L.pull (φ ≫ F)) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr J z := moveFr hL' w u (J PUnit.unit) z
  fr_hol J := moveFr_hol hw hL hL' u J
  fr_ne J z hz := by
    have hj := (top_pull₂ u z J).1 hz
    have h₀ := chartOf_mem hL' (pz u z)
    exact mul_ne_zero (wv_ne w _ pt₀ hj h₀) (u.fr_ne _ z ((top_pull u z _).2 h₀))
  fr_compat J J' z hz := by
    have hm := (top_le_iff_mem _ _ pt₀).1 hz
    have hj := (top_pull₂ u z J).1 ((top_le_iff_mem _ _ pt₀).2 hm.1)
    have hj' := (top_pull₂ u z J').1 ((top_le_iff_mem _ _ pt₀).2 hm.2)
    have h₀ := chartOf_mem hL' (pz u z)
    have e := wv_trans hw (pz u z) pt₀ hj hj' h₀ h₀
    rw [valF_g_self hL' _ pt₀ h₀, _root_.mul_one] at e
    have v : valAt' (u.ex z).left _ ((L.pull (φ ≫ F)).g J J').val =
        valF (pz u z ≫ F) _ (L.g (J PUnit.unit) (J' PUnit.unit)).val :=
      (valF_pull_g L (φ ≫ F) (u.ex z).left pt₀ J J' hj hj').trans (by
        rw [show (u.ex z).left ≫ φ ≫ F = pz u z ≫ F from (Category.assoc _ _ _).symm])
    rw [v, moveFr, moveFr, ← _root_.mul_assoc, e]

theorem moveUnif_fr {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) (u : HolUnif A (L'.pull φ) g)
    {j : L.ι} {k : L'.ι} {z : Fin g → ℂ} (hj : (pz u z ≫ F) pt₀ ∈ L.U j) (hk : pz u z pt₀ ∈ L'.U k) :
    (moveUnif hw hL hL' u).fr (fun _ => j) z = wv w (pz u z) j k * u.fr (fun _ => k) z :=
  moveFr_eq hw hL hL' u hj hk

theorem moveUnif_isAH {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {u : HolUnif A (L'.pull φ) g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) :
    (moveUnif hw hL hL' u).IsAH Hm χ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨h₁, h₂, h₃, fun l J z hz => ?_⟩
  have hj := (top_pull₂ u z J).1 hz
  have ex : u.ex (z + (l : Fin g → ℂ)) = u.ex z := by
    rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
  have ep : pz u (z + (l : Fin g → ℂ)) = pz u z := by rw [pz, pz, ex]
  have h₀ := chartOf_mem hL' (pz u z)
  have e₁ := moveFr_eq hw hL hL' u hj h₀
  have e₂ := moveFr_eq (z := z + (l : Fin g → ℂ)) hw hL hL' u (by rw [ep]; exact hj) (by rw [ep]; exact h₀)
  rw [ep] at e₂
  have e₃ := h₄ l (fun _ => chartOf hL' (pz u z)) z ((top_pull u z _).2 h₀)
  show moveFr hL' w u (J PUnit.unit) z = _ * moveFr hL' w u (J PUnit.unit) (z + (l : Fin g → ℂ))
  rw [e₁, e₂, e₃]
  ring

end Move

section Arch

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {P : RigLB G} {P' : RigLB G'} {w : LB.Iso P'.L (P.L.pull F)} {g : ℕ}

theorem pt_zero {z' : Sp ℂ ⟶ S'} (a' : ArchFrame P' z' g) : pz a'.u 0 = z' ≫ eSec G' := by
  have e : a'.u.ex 0 = 1 := (a'.u.ker 0).2 a'.u.Λ.zero_mem
  have o := Out.PullGtPf.IsGrpPullback.one_left a'.cart
  have e₁ : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ a'.A) = η[a'.A] := by rw [Hom.one_def]; simp
  rw [pz, e, e₁]
  exact o

def moveFrame (gp : IsGrpPullback G' G f F) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) P'.rig P.rig f)
    {z' : Sp ℂ ⟶ S'} {z : Sp ℂ ⟶ S} (hz : z = z' ≫ f) (a' : ArchFrame P' z' g) : ArchFrame P z g where
  A := a'.A
  grp := a'.grp
  φ := a'.φ ≫ F
  cart := (a'.cart.comp gp).congr hz.symm rfl
  u := moveUnif hw P.isLB P'.isLB a'.u
  Hm := a'.Hm
  χ := a'.χ
  ah := moveUnif_isAH hw P.isLB P'.isLB a'.ah
  rig i hi := by
    subst hz
    have hb := pt_zero a'
    have hj : (pz a'.u 0 ≫ F) pt₀ ∈ P.L.U i := (top_le_iff_mem _ _ pt₀).1 hi
    have h₀ := chartOf_mem P'.isLB (pz a'.u 0)
    generalize chartOf P'.isLB (pz a'.u 0) = k at h₀
    have e₀ := moveUnif_fr hw P.isLB P'.isLB a'.u hj h₀
    have e₁ := a'.rig k ((top_le_iff_mem _ _ pt₀).2 h₀)
    rw [hb] at hj h₀ e₀
    have hm' : z' pt₀ ∈ LB.wchart P'.L (fun _ : PUnit => eSec G') (fun _ => k) := Set.mem_iInter.2 fun _ => h₀
    have ec : (z' ≫ eSec G') ≫ F = (z' ≫ f) ≫ eSec G := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (z' ≫ ·) (Out.PullGtPf.IsGrpPullback.one_left gp)
    have hm : (z' ≫ f) pt₀ ∈ LB.wchart P.L (fun _ : PUnit => eSec G) (fun _ => i) := Set.mem_iInter.2 fun _ => by
      have := hj
      rw [ec] at this
      exact this
    have e := hr (Sp ℂ) z' pt₀ (fun _ => i) (fun _ => k) (fun _ => hj) (fun _ => h₀)
    simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one] at e
    refine e₀.trans ?_
    rw [e₁]
    apply (toStk pt₀).injective
    rw [map_mul, toStk_wv w _ pt₀ hj h₀, toStk_valF (z' ≫ f) ((P.L.pull (eSec G)).U fun _ => i) pt₀ hm,
      toStk_valF z' ((P'.L.pull (eSec G')).U fun _ => k) pt₀ hm']
    exact (congrArg Units.val e).symm

theorem moveFrame_isFn (gp : IsGrpPullback G' G f F) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) P'.rig P.rig f)
    {z' : Sp ℂ ⟶ S'} {z : Sp ℂ ⟶ S} (hz : z = z' ≫ f) (a' : ArchFrame P' z' g) {n : ℕ} {s : Out.H0 P.L n}
    {s' : Out.H0 P'.L n}
    (hs : ∀ (x : Sp ℂ ⟶ G'.left) (j : P.L.ι) (k : P'.L.ι), (x ≫ F) pt₀ ∈ P.L.U j → x pt₀ ∈ P'.L.U k →
      valF (x ≫ F) _ (s.f fun _ => j) = wv w x j k ^ n * valF x _ (s'.f fun _ => k)) (θ : (Fin g → ℂ) → ℂ) :
    (moveFrame gp hw hr hz a').IsFn s θ ↔ a'.IsFn s' θ := by
  have hp : ∀ v, (moveFrame gp hw hr hz a').pt v = a'.pt v ≫ F := fun v => (Category.assoc _ _ _).symm
  have hf : ∀ v j k, (a'.pt v ≫ F) pt₀ ∈ P.L.U j → a'.pt v pt₀ ∈ P'.L.U k →
      (moveFrame gp hw hr hz a').u.fr (fun _ => j) v = wv w (a'.pt v) j k * a'.u.fr (fun _ => k) v :=
    fun v j k hj hk => moveUnif_fr hw P.isLB P'.isLB a'.u hj hk
  constructor
  · intro h i v hi
    have hk : a'.pt v pt₀ ∈ P'.L.U i := (top_le_iff_mem _ _ pt₀).1 hi
    obtain ⟨j, hj⟩ := exists_chart P.isLB ((a'.pt v ≫ F) pt₀)
    have e₁ := h j v (by rw [hp]; exact (top_le_iff_mem _ _ pt₀).2 hj)
    rw [hf v j i hj hk, hp, hs _ j i hj hk] at e₁
    apply mul_left_cancel₀ (pow_ne_zero n (wv_ne w _ pt₀ hj hk))
    rw [e₁]
    ring
  · intro h j v hj
    rw [hp] at hj
    have hj' : (a'.pt v ≫ F) pt₀ ∈ P.L.U j := (top_le_iff_mem _ _ pt₀).1 hj
    obtain ⟨k, hk⟩ := exists_chart P'.isLB (a'.pt v pt₀)
    have e₁ := h k v ((top_le_iff_mem _ _ pt₀).2 hk)
    rw [hf v j k hj' hk, hp, hs _ j k hj' hk, e₁]
    ring

end Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem emb_comp {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L'] (σ' : L' →+* ℂ) :
    emb (σ'.comp (algebraMap L L')) = emb σ' ≫ spMap (algebraMap (𝓞 L) (𝓞 L')) := by
  rw [emb, emb, ← spMap_comp]
  congr 1

theorem exists_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') (_ : D.Ext D') (n : ℕ) (s : Out.H0 D.t.PP.L n), ∃ s' : Out.H0 D'.t.PP.L n, (∀ M : (L →+* ℂ) → ℝ, D.SupLe s M → D'.SupLe s' fun σ' => M (σ'.comp (algebraMap L L'))) ∧ ∀ (σ' : L' →+* ℂ) (a' : D'.Frame σ'), ∃ a : ArchFrame D.t.PP (emb (σ'.comp (algebraMap L L'))) D'.g, a.u.Λ = a'.u.Λ ∧ a.Hm = a'.Hm ∧ ∀ θ, a.IsFn s θ ↔ a'.IsFn s' θ := by
  intro E _ _ _ H L _ _ D L' _ _ _ D' e n s
  obtain ⟨w, gw, r, -⟩ := (isPullCubical_iff e.cm D.t.cub D'.t.cub).1 e.lin
  have r' : PMaps w (K := PUnit) (fun _ => eSec D'.t.G) (fun _ => eSec D.t.G) (fun _ => 1) D'.t.PP.rig D.t.PP.rig
      (spMap (algebraMap (𝓞 L) (𝓞 L'))) :=
    (congrArg (fun h => PMaps w (K := PUnit) (fun _ => eSec D'.t.G) (fun _ => eSec D.t.G) (fun _ => 1) D'.t.PP.rig
      D.t.PP.rig h) e.base).mp r
  obtain ⟨s', hs'⟩ := exists_sec gw D.t.PP.isLB D'.t.PP.isLB n s
  have hs := fun (x : Sp ℂ ⟶ D'.t.G.left) j k => hs' ℂ x pt₀ j k
  have hg : D'.g = D.g := ((GlobalTheory.T.polarized_data_field_extension E H L D L').2 D' e).1
  refine ⟨s', fun M hM σ' a' θ hθ v => ?_, fun σ' a' => ⟨moveFrame e.cart gw r' (emb_comp σ') a', rfl, rfl, fun θ =>
    moveFrame_isFn e.cart gw r' (emb_comp σ') a' hs θ⟩⟩
  have key : ∀ (g : ℕ) (_ : g = D.g) (a : ArchFrame D.t.PP (emb (σ'.comp (algebraMap L L'))) g) (θ : (Fin g → ℂ) → ℂ),
      a.IsFn s θ → ∀ v, a.nrm n θ v ≤ M (σ'.comp (algebraMap L L')) := by
    intro g hg'
    subst hg'
    exact hM _
  exact key _ hg (moveFrame e.cart gw r' (emb_comp σ') a') θ ((moveFrame_isFn e.cart gw r' (emb_comp σ') a' hs θ).2 hθ) v

end GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans
end
