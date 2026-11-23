import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndivisibleSection

section Calc

variable {R : Type} [CommRing R] {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem cst_mul' (q : Z ⟶ Sp R) (z : Z) (a b : R) : cst q z (a * b) = cst q z a * cst q z b := by
  unfold cst
  rw [map_mul]
  exact gs_mul _ _ _ (by simp) _ _

theorem cst_one' (q : Z ⟶ Sp R) (z : Z) : cst q z 1 = 1 := by
  unfold cst
  rw [map_one]
  unfold gs
  rw [dif_pos (by simp), map_one, map_one]

theorem gs_scal (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (W : Y.Opens) (hz : r z ∈ W) (a : R) :
    gs r z W (resTop W (scal p a)) = cst (r ≫ p) z a := by
  unfold cst
  exact (gs_res r z le_top hz _).trans (gs_pull r p z ⊤ (by simp) _)

theorem sval_of_secIsMul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {p : Y ⟶ Sp R} {a : R}
    {s t : LB.Sec (LB.LinComb L φ ε)} (h : SecIsMul p a s t) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : sval s r z J = cst (r ≫ p) z a * sval t r z J := by
  have hm := hJ.mem φ r
  unfold sval
  rw [h (fun k => J (r ≫ φ k))]
  exact (gs_mul _ _ _ hm _ _).trans (congrArg (· * _) (gs_scal p r z _ hm _))

def smulSec {M : LB Y} (c : Γ(Y, ⊤)) (t : LB.Sec M) : LB.Sec M where
  f j := resTop _ c * t.f j
  compat i j := by
    have e : ∀ {W W' : Y.Opens} (h : W' ≤ W),
        (Y.presheaf.map (homOfLE h).op).hom (resTop W c) = resTop W' c := fun h => by
      rw [resTop, ← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    rw [map_mul, map_mul, t.compat i j, e, e]
    ring

theorem secIsMul_of_sval (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {p : Y ⟶ Sp R} {a : R}
    {s t : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = cst p y a * sval t (𝟙 Y) y J) : SecIsMul p a s t := by
  unfold SecIsMul
  intro j
  apply fn_ext
  intro y hy
  obtain ⟨J, hJ, -⟩ := exists_good L hL y (Empty.elim : Empty → (Y ⟶ X)) Empty.elim (fun a => a.elim) (fun a => a.elim)
  have hy' := hJ.mem φ (𝟙 Y)
  have e1 : gs (𝟙 Y) y ((LB.LinComb L φ ε).U j) (s.f j) = _ := sec_trans s (𝟙 Y) y hy hy'
  have e2 : gs (𝟙 Y) y ((LB.LinComb L φ ε).U j) (t.f j) = _ := sec_trans t (𝟙 Y) y hy hy'
  have e3 := h y J hJ
  unfold sval at e3
  rw [gs_mul _ _ _ hy, gs_scal p (𝟙 Y) y _ hy, e1, e2, e3]
  simp only [Category.id_comp]
  ring

theorem exists_pull_chart {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (φ' : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = φ' k) : ∃ s' : LB.Sec (LB.LinComb L φ' ε),
      ∀ j (le : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j),
        s'.f j = (Y'.presheaf.map (homOfLE le).op).hom ((h.app _).hom (s.f j)) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext fun k => (e k).symm
  refine ⟨pullSec L φ ε s h, fun j le => ?_⟩
  rfl

theorem exists_pull_val (hL : L.IsLB) {K' : Type} [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) {φ' : K' → (Y' ⟶ X)} {ε' : K' → ℤ}
    (e : FormEq (fun k => h ≫ φ k) ε φ' ε') : ∃ s' : LB.Sec (LB.LinComb L φ' ε'),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J → sval s' r z J = sval s (r ≫ h) z J := by
  obtain ⟨s', hs'⟩ := exists_sec hL e (pullSec L φ ε s h)
  exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (DVR.SectionScalarValuation.sval_pullSec φ ε s h r z hJ)⟩

end Calc

section Deg

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem c_zero_eq_one : D.c 0 = 1 := by
  have e := D.c_add 0 0
  rw [add_zero] at e
  have e' : D.c 0 * D.c 0 = D.c 0 * 1 := by
    rw [_root_.mul_one]
    exact e.symm
  exact mul_left_cancel e'

theorem prod_fam_zero {U : Type} [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ k, h (D.famφB 0 k) ^ DegPre.famε 1 k = h (𝟙 _) := by
  unfold DegPre.famφB DegPre.famε
  rw [c_zero_eq_one, Fin.prod_univ_four]
  have e2 : toUnit D.P.A ≫ (1 : 𝟙_ _ ⟶ D.P.A) = toUnit D.P.A ≫ η := by
    change toUnit D.P.A ≫ (toUnit _ ≫ η) = _
    rw [← Category.assoc, toUnit_unique (toUnit D.P.A ≫ toUnit _) (toUnit D.P.A)]
  have e1 : padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ 1) = 𝟙 D.P.A := by
    rw [e2]
    exact mul_one (𝟙 D.P.A)
  rw [e1, e2]
  simp

theorem exists_generator_of_iso {Y : Scheme.{0}} (π : Y ⟶ D.P.A.left) (σ : D.P.A.left ⟶ Y)
    (h₁ : σ ≫ π = 𝟙 _) (h₂ : π ≫ σ = 𝟙 _) (f : Y ⟶ Sp R) (hf : π ≫ D.P.A.hom = f)
    (β : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => π) (fun _ => ((1 : ℕ) : ℤ))))
    (H : ∀ s : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => π) (fun _ => ((1 : ℕ) : ℤ))),
      ∃! a : R, SecIsMul f a s β) :
    ∃ b : D.SecB 1 0, ∀ s : D.SecB 1 0, ∃! a : R, SecIsMul D.P.A.hom a s b := by
  have hL : D.P.L.IsLB := D.P.isLB
  subst hf
  have hform1 : FormEq (fun _ : Fin 1 => σ ≫ π) (fun _ => ((1 : ℕ) : ℤ)) (D.famφB 0) (DegPre.famε 1) := by
    unfold FormEq
    intro U _ h
    rw [prod_fam_zero D h, h₁]
    simp
  obtain ⟨b, hbv⟩ := exists_pull_val hL β σ hform1
  refine ⟨b, fun s => ?_⟩
  have hform2 : FormEq (fun k => π ≫ D.famφB 0 k) (DegPre.famε 1) (fun _ : Fin 1 => π) (fun _ => ((1 : ℕ) : ℤ)) := by
    unfold FormEq
    intro U _ h
    have e0 := prod_fam_zero D (fun g => h (π ≫ g))
    simp only [Category.comp_id] at e0
    rw [e0]
    simp
  obtain ⟨sY, hsY⟩ := exists_pull_val hL s π hform2
  obtain ⟨a, ha, hau⟩ := H sY
  refine ⟨a, ?_, fun a' ha' => hau a' ?_⟩
  · apply secIsMul_of_sval hL
    intro y J hJ
    have e1 := hsY _ σ y J hJ
    rw [h₁] at e1
    have e2 := hbv _ (𝟙 _) y J hJ
    rw [Category.id_comp] at e2
    rw [← e1, e2, sval_of_secIsMul ha σ y hJ, ← Category.assoc, h₁, Category.id_comp]
  · apply secIsMul_of_sval hL
    intro y J hJ
    have e1 := hsY _ (𝟙 _) y J hJ
    rw [Category.id_comp] at e1
    rw [e1, sval_of_secIsMul ha' π y hJ, hbv _ π y J hJ, h₂]

theorem exists_generator_of_basis (q : Sp R ⟶ Sp R) (hq : q = 𝟙 _)
    (β : LB.Sec (LPow D.P.A D.P.L (1 : ℕ) (Over.mk q)))
    (hli : ∀ r : Γ((Over.mk q).left, ⊤), r • (SecM.ofSec D.P.A β : SecM D.P.A D.P.L (1 : ℕ) (Over.mk q)) = 0 → r = 0)
    (hsp : ∀ s : SecM D.P.A D.P.L (1 : ℕ) (Over.mk q), ∃ r : Γ((Over.mk q).left, ⊤), r • SecM.ofSec D.P.A β = s) :
    ∃ b : D.SecB 1 0, ∀ s : D.SecB 1 0, ∃! a : R, SecIsMul D.P.A.hom a s b := by
  subst hq
  have hw : (snd (Over.mk (𝟙 (Sp R))) D.P.A).left ≫ D.P.A.hom = (fst (Over.mk (𝟙 (Sp R))) D.P.A).left := by
    have w1 := Over.w (fst (Over.mk (𝟙 (Sp R))) D.P.A)
    have w2 := Over.w (snd (Over.mk (𝟙 (Sp R))) D.P.A)
    simp only [Over.mk_hom] at w1
    rw [w2, ← w1]
    simp
  let u : D.P.A ⟶ Over.mk (𝟙 (Sp R)) := Over.homMk D.P.A.hom (by simp)
  have h₁ : (lift u (𝟙 D.P.A)).left ≫ (snd (Over.mk (𝟙 (Sp R))) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]
    rfl
  have h₂ : (snd (Over.mk (𝟙 (Sp R))) D.P.A).left ≫ (lift u (𝟙 D.P.A)).left = 𝟙 _ := by
    rw [← Over.comp_left]
    have e : snd (Over.mk (𝟙 (Sp R))) D.P.A ≫ lift u (𝟙 D.P.A) = 𝟙 _ := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, Category.id_comp]
        ext
        simp only [Over.comp_left, u, Over.homMk_left]
        exact hw
      · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
    rw [e]
    rfl
  refine exists_generator_of_iso D (snd (Over.mk (𝟙 (Sp R))) D.P.A).left (lift u (𝟙 D.P.A)).left h₁ h₂ _ rfl β ?_
  intro s
  obtain ⟨r, hr⟩ := hsp (SecM.ofSec D.P.A (s : (LPow D.P.A D.P.L (↑(1 : ℕ)) (Over.mk (𝟙 (Sp R)))).Sec))
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r, ?_, fun a' ha' => ?_⟩
  · unfold SecIsMul
    intro j
    have hj := congrArg (fun x => x.1 j) hr
    change r • β.f j = s.f j at hj
    rw [← hj, hw]
    unfold resTop scal
    simp only [Iso.hom_inv_id_apply]
    rfl
  · obtain ⟨r', hr'⟩ : ∃ r' : Γ((Over.mk (𝟙 (Sp R))).left, ⊤),
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a' = r' := ⟨_, rfl⟩
    have hs' : r' • SecM.ofSec D.P.A β =
        SecM.ofSec D.P.A (s : (LPow D.P.A D.P.L (↑(1 : ℕ)) (Over.mk (𝟙 (Sp R)))).Sec) := by
      apply Subtype.ext
      funext j
      simp only [Submodule.coe_smul, Pi.smul_apply]
      change r' • β.f j = s.f j
      rw [ha' j, hw, ← hr']
      rfl
    have h0 := hli (r' - r) (by rw [sub_smul, hs', hr, sub_self])
    rw [sub_eq_zero] at h0
    rw [← h0, ← hr']
    simp only [Iso.inv_hom_id_apply]

theorem exists_generator (hS : SecBaseChangeSt) [IsLocalRing R] [IsNoetherianRing R] :
    ∃ b : D.SecB 1 0, ∀ s : D.SecB 1 0, ∃! a : R, SecIsMul D.P.A.hom a s b := by
  unfold SecBaseChangeSt at hS
  obtain ⟨V, hV, b, hb⟩ := hS (Sp R) D.P 1 le_rfl (IsLocalRing.closedPoint R)
  obtain rfl := DVR.eq_top_of_closedPoint_mem V hV
  have hex : ∀ i, ∃ s' : (LPow D.P.A D.P.L (↑(1 : ℕ)) (baseAt (Sp R).topIso.inv)).Sec,
      ∀ j (le : LB.wchart D.P.L (fun _ : Fin 1 => (snd (baseAt (Sp R).topIso.inv) D.P.A).left) j ≤
        (homAt (Sp R).topIso.inv ▷ D.P.A).left ⁻¹ᵁ LB.wchart D.P.L (fun _ : Fin 1 => (snd _ D.P.A).left) j),
        s'.f j = ((baseAt (Sp R).topIso.inv ⊗ D.P.A).left.presheaf.map (homOfLE le).op).hom
          (((homAt (Sp R).topIso.inv ▷ D.P.A).left.app _).hom ((b i).f j)) := fun i =>
    exists_pull_chart (K := Fin 1) (φ := fun _ => (snd _ D.P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) (b i)
      (homAt (Sp R).topIso.inv ▷ D.P.A).left (fun _ => (snd (baseAt (Sp R).topIso.inv) D.P.A).left)
      (fun _ => congrArg (fun g => g.left) (whiskerRight_snd (homAt (Sp R).topIso.inv) D.P.A))
  choose b' hb' using hex
  obtain ⟨hli, hsp⟩ := hb R (Sp R).topIso.inv b' (fun i => by
    unfold IsPullSec
    intro j
    exact hb' i j _)
  have hpos : 0 < 1 ^ D.P.g := by simp
  let i0 : Fin (1 ^ D.P.g) := ⟨0, hpos⟩
  have hone : ∀ i : Fin (1 ^ D.P.g), i = i0 := fun i => Fin.ext (by
    have hi : (i : ℕ) < 1 := lt_of_lt_of_eq i.isLt (_root_.one_pow _)
    show i.val = 0
    omega)
  have : Subsingleton (Fin (1 ^ D.P.g)) := ⟨fun x y => (hone x).trans (hone y).symm⟩
  refine exists_generator_of_basis D _ ?_ (b' i0) ?_ ?_
  · unfold overRes baseOver
    simp
  · intro r hr
    exact Fintype.linearIndependent_iff.mp hli (fun _ => r) (by rw [Fintype.sum_subsingleton _ i0]; exact hr) i0
  · intro s
    have hs := (Submodule.eq_top_iff'.mp hsp) s
    have hr : Set.range (fun i => SecM.ofSec D.P.A (b' i)) = {SecM.ofSec D.P.A (b' i0)} := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        rw [hone y]
        rfl
      · intro h
        exact ⟨i0, h.symm⟩
    rw [hr] at hs
    exact Submodule.mem_span_singleton.mp hs

private theorem scal_mul_divisor {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Sp R) (a b : R) :
    scal p (a * b) = scal p a * scal p b := by
  unfold scal
  rw [map_mul, map_mul]

private theorem resTop_mul' {Y : Scheme.{0}} (W : Y.Opens) (x y : Γ(Y, ⊤)) :
    resTop W (x * y) = resTop W x * resTop W y := by
  unfold resTop
  exact map_mul _ _ _

private theorem scal_one_rings_of_integers {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Sp R) :
    scal p (1 : R) = 1 := by
  unfold scal
  rw [map_one, map_one]

private theorem resTop_one {Y : Scheme.{0}} (W : Y.Opens) : resTop W (1 : Γ(Y, ⊤)) = 1 := by
  unfold resTop
  exact map_one _

end Deg

theorem secBGenerates_of_not_dvd : SecBaseChangeSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (g : D.toPre.SecB 1 0), (¬ ∃ g' : D.toPre.SecB 1 0, SecIsMul D.toPre.P.A.hom ϖ g g') → SecBGenerates (D := D) 1 0 g := by
  intro hS V _ _ _ ϖ hϖ D g hg
  obtain ⟨b, hb⟩ := exists_generator D.toPre hS
  obtain ⟨a, ha, -⟩ := hb g
  have hmul : ∀ (x y : V) (s t w : D.toPre.SecB 1 0), SecIsMul D.toPre.P.A.hom x s t →
      SecIsMul D.toPre.P.A.hom y t w → SecIsMul D.toPre.P.A.hom (x * y) s w := by
    intro x y s t w h1 h2
    unfold SecIsMul at h1 h2 ⊢
    intro j
    rw [h1 j, h2 j, scal_mul_divisor, resTop_mul', _root_.mul_assoc]
  by_cases hu : IsUnit a
  · obtain ⟨u, rfl⟩ := hu
    have hinv : SecIsMul D.toPre.P.A.hom (↑u⁻¹ : V) b g := by
      unfold SecIsMul at ha ⊢
      intro j
      rw [ha j, ← _root_.mul_assoc, ← resTop_mul', ← scal_mul_divisor, Units.inv_mul, scal_one_rings_of_integers, resTop_one,
        _root_.one_mul]
    unfold SecBGenerates
    intro s
    obtain ⟨c, hc, hcu⟩ := hb s
    refine ⟨c * ↑u⁻¹, hmul _ _ _ _ _ hc hinv, fun d hd => ?_⟩
    have hdu := hcu (d * u) (hmul _ _ _ _ _ hd ha)
    rw [← hdu, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
  · exfalso
    apply hg
    have hmax : a ∈ maximalIdeal V := (IsLocalRing.mem_maximalIdeal a).mpr hu
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton'] at hmax
    obtain ⟨a', rfl⟩ := hmax
    refine ⟨smulSec (scal D.toPre.P.A.hom a') b, ?_⟩
    unfold SecIsMul at ha ⊢
    intro j
    rw [ha j, _root_.mul_comm a' ϖ, scal_mul_divisor, resTop_mul', _root_.mul_assoc]
    rfl

end GlobalTheory.IndivisibleSection
