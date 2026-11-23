import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension

noncomputable section
namespace GlobalTheory.ArcPts.Transfer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts GlobalTheory.ConstFam GlobalTheory.FormalValue
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

section Sec
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
  {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}

theorem gs_zero {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) : gs r z U 0 = 0 := by
  unfold gs
  split_ifs <;> simp

theorem exists_secThrough_up (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) [IsIso h]
    (a : LB.Sec (LB.LinComb L' φ' ε)) : ∃ t, SecThrough w φ' φ ε a t h := by
  obtain rfl : φ = fun k => (inv h ≫ φ' k) ≫ F := funext fun k => by
    rw [Category.assoc, hψ, IsIso.inv_hom_id_assoc]
  obtain ⟨t, ht⟩ := exists_sec_up ((isGen_iff w).1 hw) hL hL' (φ' := fun k => inv h ≫ φ' k)
    (ReciprocityTheory.ChartRestriction.G.DVR.pullSec L' φ' ε a (inv h))
  refine ⟨t, fun Z r z p q hp hq => ?_⟩
  have e : ∀ k, (r ≫ h) ≫ inv h ≫ φ' k = r ≫ φ' k := fun k => by simp
  have hq' : (r ≫ h) z ∈ LB.wchart L' (fun k => inv h ≫ φ' k) q := Set.mem_iInter.2 fun k => by
    show ((r ≫ h) ≫ inv h ≫ φ' k) z ∈ L'.U (q k)
    rw [e]; exact hq k
  have hp' : (r ≫ h) z ∈ LB.wchart L (fun k => (inv h ≫ φ' k) ≫ F) p := Set.mem_iInter.2 fun k => by
    show F (((r ≫ h) ≫ inv h ≫ φ' k) z) ∈ L.U (p k)
    rw [e]; exact hp k
  refine (ht Z (r ≫ h) z p q hp' hq').trans (congrArg₂ (· * ·) ?_ ?_)
  · simp only [pw, e]
  · refine (gs_res _ z _ hq' _).trans ((gs_pull (r ≫ h) (inv h) z _ (Out.wchart_comp_le L' φ' (inv h) q hq') _).trans ?_)
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

theorem zero_down (hL : L.IsLB) {a : LB.Sec (LB.LinComb L' φ' ε)}
    {t : LB.Sec (LB.LinComb L φ ε)} (H : SecThrough w φ' φ ε a t h) (ht : ∀ i, t.f i = 0) (q) : a.f q = 0 := by
  refine fn_ext fun y hy => ?_
  choose p hp using fun k => exists_chart hL (F (φ' k y))
  have e := H _ (𝟙 Y') y p q hp (Set.mem_iInter.1 hy)
  exact ((Units.mul_right_eq_zero _).1 (e.symm.trans ((congrArg (gs _ y _) (ht p)).trans (gs_zero _ _ _)))).trans
    (gs_zero _ _ _).symm

theorem zero_up (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) [IsIso h] {a : LB.Sec (LB.LinComb L' φ' ε)}
    {t : LB.Sec (LB.LinComb L φ ε)} (H : SecThrough w φ' φ ε a t h) (ha : ∀ i, a.f i = 0) (p) : t.f p = 0 := by
  refine fn_ext fun y hy => ?_
  choose q hq using fun k => exists_chart hL' (φ' k (inv h y))
  have e := H _ (inv h) y p q (fun k => by
    show (inv h ≫ φ' k ≫ F) y ∈ _
    rw [hψ, IsIso.inv_hom_id_assoc]; exact Set.mem_iInter.1 hy k) hq
  rw [IsIso.inv_hom_id] at e
  exact (e.trans ((congrArg _ ((congrArg (gs _ y _) (ha q)).trans (gs_zero _ _ _))).trans (mul_zero _))).trans
    (gs_zero _ _ _).symm

end Sec

section Frm
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]

def wv (w : LB.Iso L' (L.pull F)) (x : Sp R ⟶ X') (j : L.ι) (k : L'.ι) : R :=
  valR x ((LB.div (L.pull F) L').U (fun _ => j, k)) (w.s (fun _ => j, k)).val

def FrmRel (w : LB.Iso L' (L.pull F)) (x : Sp R ⟶ X') (τ : L.ι → R) (τ' : L'.ι → R) : Prop :=
  ∀ j k, ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, k) → τ j = wv w x j k * τ' k

variable {w : LB.Iso L' (L.pull F)} {x : Sp R ⟶ X'}

theorem div_iff {j : L.ι} {k : L'.ι} : ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, k) ↔
    F (x (cpt R)) ∈ L.U j ∧ x (cpt R) ∈ L'.U k :=
  (top_le_iff_cpt x _).trans (and_congr_left' mem_pull)

theorem toStkA_wv {j : L.ι} {k : L'.ι} (hj : F (x (cpt R)) ∈ L.U j) (hk : x (cpt R) ∈ L'.U k) :
    toStkA (cpt R) (wv w x j k) = (gw w x (cpt R) j k).val :=
  toStkA_valR x _ _ (div_iff.2 ⟨hj, hk⟩) _

theorem isUnit_wv {j : L.ι} {k : L'.ι} (hj : F (x (cpt R)) ∈ L.U j) (hk : x (cpt R) ∈ L'.U k) :
    IsUnit (wv w x j k) := isUnit_valR x _ (div_iff.2 ⟨hj, hk⟩) _

theorem wv_left (hw : w.IsGen) (hL' : L'.IsLB) {j j' : L.ι} {k : L'.ι} (hj : F (x (cpt R)) ∈ L.U j)
    (hj' : F (x (cpt R)) ∈ L.U j') (hk : x (cpt R) ∈ L'.U k) :
    wv w x j k = valR (x ≫ F) (L.U j ⊓ L.U j') (L.g j j').val * wv w x j' k := by
  apply toStkA_injective
  rw [map_mul, toStkA_wv hj hk, toStkA_wv hj' hk,
    toStkA_valR (x ≫ F) (L.U j ⊓ L.U j') _ ((top_le_iff_cpt _ _).2 ⟨hj, hj'⟩),
    (isGen_iff w).1 hw _ x _ j j' k k hj hj' hk hk, gm_self hL' x _ hk, inv_one, mul_one, Units.val_mul]

theorem wv_right (hw : w.IsGen) (hL : L.IsLB) {j : L.ι} {k k' : L'.ι} (hj : F (x (cpt R)) ∈ L.U j)
    (hk : x (cpt R) ∈ L'.U k) (hk' : x (cpt R) ∈ L'.U k') :
    wv w x j k * valR x (L'.U k ⊓ L'.U k') (L'.g k k').val = wv w x j k' := by
  apply toStkA_injective
  rw [map_mul, toStkA_wv hj hk, toStkA_wv hj hk',
    toStkA_valR x (L'.U k ⊓ L'.U k') _ ((top_le_iff_cpt _ _).2 ⟨hk, hk'⟩),
    (isGen_iff w).1 hw _ x _ j j k k' hj hj hk hk', gm_self hL (x ≫ F) _ hj, one_mul, ← Units.val_mul,
    inv_mul_cancel_comm]

theorem exists_frm_up (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) {τ' : L'.ι → R} (h : IsFrm L' x τ') :
    ∃ τ, IsFrm L (x ≫ F) τ ∧ FrmRel w x τ τ' := by
  obtain ⟨k₀, hk₀⟩ := exists_chart hL' (x (cpt R))
  refine ⟨fun j => wv w x j k₀ * τ' k₀, ⟨fun j hj => ?_, fun j j' hj => ?_⟩, fun j k hjk => ?_⟩
  · exact (isUnit_wv ((top_le_iff_cpt _ _).1 hj) hk₀).mul (h.1 k₀ ((top_le_iff_cpt _ _).2 hk₀))
  · have hj := (top_le_iff_cpt _ _).1 hj
    beta_reduce
    rw [← mul_assoc, ← wv_left hw hL' hj.1 hj.2 hk₀]
  · obtain ⟨hj, hk⟩ := div_iff.1 hjk
    beta_reduce
    rw [h.2 k k₀ ((top_le_iff_cpt _ _).2 ⟨hk, hk₀⟩), ← mul_assoc, wv_right hw hL hj hk hk₀]

theorem exists_frm_down (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) {τ : L.ι → R} (h : IsFrm L (x ≫ F) τ) :
    ∃ τ', IsFrm L' x τ' ∧ FrmRel w x τ τ' := by
  obtain ⟨j₀, hj₀⟩ := exists_chart hL (F (x (cpt R)))
  have key : ∀ k, x (cpt R) ∈ L'.U k → wv w x j₀ k * (Ring.inverse (wv w x j₀ k) * τ j₀) = τ j₀ := fun k hk =>
    Ring.mul_inverse_cancel_left _ _ (isUnit_wv hj₀ hk)
  refine ⟨fun k => Ring.inverse (wv w x j₀ k) * τ j₀, ⟨fun k hk => ?_, fun k k' hk => ?_⟩, fun j k hjk => ?_⟩
  · exact (isUnit_wv hj₀ ((top_le_iff_cpt _ _).1 hk)).ringInverse.mul (h.1 j₀ ((top_le_iff_cpt _ _).2 hj₀))
  · have hk := (top_le_iff_cpt _ _).1 hk
    refine (isUnit_wv (w := w) hj₀ hk.1).mul_left_cancel ?_
    beta_reduce
    rw [key k hk.1, ← mul_assoc, wv_right hw hL hj₀ hk.1 hk.2, key k' hk.2]
  · obtain ⟨hj, hk⟩ := div_iff.1 hjk
    beta_reduce
    rw [wv_left hw hL' hj hj₀ hk, mul_assoc, key k hk]
    exact h.2 j j₀ ((top_le_iff_cpt _ _).2 ⟨hj, hj₀⟩)

theorem agree_iff (hL : L.IsLB) (hL' : L'.IsLB) {n : ℕ} {τ a : L.ι → R} {τ' a' : L'.ι → R} {r : R}
    (H : FrmRel w x τ τ') (H' : ∀ j k, F (x (cpt R)) ∈ L.U j → x (cpt R) ∈ L'.U k → a j = wv w x j k ^ n * a' k) :
    (∀ k, ⊤ ≤ x ⁻¹ᵁ L'.U k → a' k = r * τ' k ^ n) ↔ ∀ j, ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j → a j = r * τ j ^ n := by
  constructor
  · intro h j hj
    have hj := (top_le_iff_cpt _ _).1 hj
    obtain ⟨k, hk⟩ := exists_chart hL' (x (cpt R))
    rw [H' j k hj hk, H j k (div_iff.2 ⟨hj, hk⟩), h k ((top_le_iff_cpt _ _).2 hk)]
    ring
  · intro h k hk
    have hk := (top_le_iff_cpt _ _).1 hk
    obtain ⟨j, hj⟩ := exists_chart hL (F (x (cpt R)))
    refine ((isUnit_wv (w := w) hj hk).pow n).mul_left_cancel ?_
    rw [← H' j k hj hk, h j ((top_le_iff_cpt _ _).2 hj), H j k (div_iff.2 ⟨hj, hk⟩)]
    ring

theorem hasVal_iff (hL : L.IsLB) (hL' : L'.IsLB) {p' : Y' ⟶ X'} {p : Y ⟶ X} {h : Y' ⟶ Y} (hψ : p' ≫ F = h ≫ p)
    {n : ℕ} {a : SecP L' p' n} {t : SecP L p n}
    (H : SecThrough w (fun _ : Fin 1 => p') (fun _ => p) (fun _ => (n : ℤ)) a t h) {z : Sp R ⟶ Y'}
    {τ : L.ι → R} {τ' : L'.ι → R} (hτ : FrmRel w (z ≫ p') τ τ') (r : R) :
    HasVal a z τ' r ↔ HasVal t (z ≫ h) τ r := by
  have e : (z ≫ h) ≫ p = (z ≫ p') ≫ F := by rw [Category.assoc, Category.assoc, hψ]
  unfold HasVal
  rw [e]
  refine agree_iff hL hL' (a := fun j => ArcPts.sval t (z ≫ h) j) (a' := fun k => ArcPts.sval a z k) hτ fun j k hj hk => ?_
  apply toStkA_injective
  have hj' : ⊤ ≤ (z ≫ h) ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      show ((z ≫ h) ≫ p) (cpt R) ∈ L.U j
      rw [e]; exact hj)
  have hk' : ⊤ ≤ z ⁻¹ᵁ LB.wchart L' (fun _ : Fin 1 => p') (fun _ => k) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => hk)
  rw [map_mul, map_pow, toStkA_wv hj hk]
  refine (toStkA_valR_eq_gs _ _ _ hj' _).trans
    ((H _ z (cpt R) (fun _ => j) (fun _ => k) (fun _ => hj) (fun _ => hk)).trans
      (congrArg₂ (· * ·) ?_ (toStkA_valR_eq_gs _ _ _ hk' _).symm))
  rw [Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val]

theorem rig_iff (hL : L.IsLB) (hL' : L'.IsLB) {e' : Y' ⟶ X'} {e : Y ⟶ X} {g : Y' ⟶ Y} (hψ : e' ≫ F = g ≫ e)
    {a : LB.Gen (L'.pull e')} {t : LB.Gen (L.pull e)}
    (H : PMaps w (K := PUnit) (fun _ => e') (fun _ => e) (fun _ => 1) a t g) {y : Sp R ⟶ Y'} (hx : x = y ≫ e')
    {τ : L.ι → R} {τ' : L'.ι → R} (hτ : FrmRel w x τ τ') :
    (∀ k, ⊤ ≤ x ⁻¹ᵁ L'.U k → τ' k = valR y ((L'.pull e').U (fun _ => k)) (a.s (fun _ => k)).val) ↔
      ∀ j, ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j → τ j = valR (y ≫ g) ((L.pull e).U (fun _ => j)) (t.s (fun _ => j)).val := by
  subst hx
  have e₀ : (y ≫ g) ≫ e = (y ≫ e') ≫ F := by rw [Category.assoc, Category.assoc, hψ]
  have := agree_iff hL hL' (n := 1) (r := 1)
    (a := fun j => valR (y ≫ g) ((L.pull e).U (fun _ => j)) (t.s (fun _ => j)).val)
    (a' := fun k => valR y ((L'.pull e').U (fun _ => k)) (a.s (fun _ => k)).val) hτ fun j k hj hk => by
      apply toStkA_injective
      have hj' : ⊤ ≤ (y ≫ g) ⁻¹ᵁ (L.pull e).U (fun _ => j) :=
        (top_le_iff_cpt _ _).2 (mem_pull.2 (by
          show ((y ≫ g) ≫ e) (cpt R) ∈ L.U j
          rw [e₀]; exact hj))
      have hk' : ⊤ ≤ y ⁻¹ᵁ (L'.pull e').U (fun _ => k) := (top_le_iff_cpt _ _).2 (mem_pull.2 hk)
      rw [pow_one, map_mul, toStkA_wv hj hk]
      refine (toStkA_valR _ _ _ hj' _).trans ((congrArg Units.val
        (H _ y (cpt R) (fun _ => j) (fun _ => k) (fun _ => hj) (fun _ => hk))).trans ((Units.val_mul _ _).trans
        (congrArg₂ (· * ·) ?_ (toStkA_valR _ _ _ hk' _).symm)))
      rw [Fintype.prod_unique, zpow_one]
  simpa only [pow_one, one_mul, eq_comm] using this

end Frm

section Main
open MonObj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
  {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {R : Type} [CommRing R] (y' : Sp R ⟶ S')

theorem isPullback_fibre : IsPullback (pullback.fst t'.G.hom y' ≫ m.φ) (pullback.snd t'.G.hom y') t.G.hom (y' ≫ f) :=
  (IsPullback.of_hasPullback t'.G.hom y').paste_horiz m.cart.1

def fibIso : pullback t'.G.hom y' ≅ pullback t.G.hom (y' ≫ f) := (isPullback_fibre m y').isoPullback

theorem fibIso_fst : pullback.fst t'.G.hom y' ≫ m.φ = (fibIso m y').hom ≫ pullback.fst t.G.hom (y' ≫ f) :=
  (IsPullback.isoPullback_hom_fst _).symm

theorem fib_fst {G : Over S} {y : Sp R ⟶ S} (x : Over.mk y ⟶ G) : fib x ≫ pullback.fst G.hom y = x.left :=
  pullback.lift_fst _ _ _

theorem fib_fibIso {x' : Over.mk y' ⟶ t'.G} {x : Over.mk (y' ≫ f) ⟶ t.G} (hx : x'.left ≫ m.φ = x.left) :
    fib x' ≫ (fibIso m y').hom = fib x := by
  apply pullback.hom_ext
  · rw [Category.assoc, ← fibIso_fst, ← Category.assoc, fib_fst, fib_fst, hx]
  · rw [Category.assoc, fibIso, IsPullback.isoPullback_hom_snd, fib, fib, pullback.lift_snd, pullback.lift_snd]

theorem left_zero {V : Type} [AddZeroClass V] {G : Over S} [GrpObj G] {y : Sp R ⟶ S} (x : V → (Over.mk y ⟶ G))
    (hx : ∀ v v', x (v + v') = x v * x v') : (x 0).left = y ≫ eSec G := by
  have h := hx 0 0
  rw [add_zero] at h
  have h₁ : x 0 = 1 := mul_eq_left.1 h.symm
  rw [h₁]
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

variable [IsLocalRing R] {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)}

theorem hasVal_fib_iff {n : ℕ} {a : SecP t'.PP.L (pullback.fst t'.G.hom y') n}
    {s : SecP t.PP.L (pullback.fst t.G.hom (y' ≫ f)) n}
    (hs : SecThrough w (fun _ : Fin 1 => pullback.fst t'.G.hom y') (fun _ => pullback.fst t.G.hom (y' ≫ f))
      (fun _ => (n : ℤ)) a s (fibIso m y').hom)
    {x' : Over.mk y' ⟶ t'.G} {x : Over.mk (y' ≫ f) ⟶ t.G} (hx : x'.left ≫ m.φ = x.left)
    {τ : t.PP.L.ι → R} {τ' : t'.PP.L.ι → R} (hτ : FrmRel w x'.left τ τ') (r : R) :
    HasVal a (fib x') τ' r ↔ HasVal s (fib x) τ r := by
  rw [← fib_fibIso m y' hx]
  exact hasVal_iff t.PP.isLB t'.PP.isLB (fibIso_fst m y') hs (by rw [fib_fst]; exact hτ) r

theorem rig_fib_iff (hw : IsRigIso m.cm t'.PP t.PP w)
    {x' : Sp R ⟶ t'.G.left} {x : Sp R ⟶ t.G.left} (hx : x' ≫ m.φ = x) (h₀ : x' = y' ≫ eSec t'.G)
    {τ : t.PP.L.ι → R} {τ' : t'.PP.L.ι → R} (hτ : FrmRel w x' τ τ') :
    (∀ k, ⊤ ≤ x' ⁻¹ᵁ t'.PP.L.U k →
      τ' k = valR y' ((t'.PP.L.pull (eSec t'.G)).U (fun _ => k)) (t'.PP.rig.s (fun _ => k)).val) ↔
    ∀ j, ⊤ ≤ x ⁻¹ᵁ t.PP.L.U j →
      τ j = valR (y' ≫ f) ((t.PP.L.pull (eSec t.G)).U (fun _ => j)) (t.PP.rig.s (fun _ => j)).val := by
  subst hx
  have P := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m.cm.e _
    (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl)).1 hw.2
  have e := m.cm.e_comm
  rw [m.base] at P e
  exact rig_iff t.PP.isLB t'.PP.isLB e P h₀ hτ

end Main

section Gen
open MonObj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {S S' : Scheme.{0}}
  {A : AnArc (𝓞 E)} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} {m : SABMap t' t f}
  {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} {y' : Sp ℂ⸨X⸩ ⟶ S'}

theorem exists_up (hw : IsRigIso m.cm t'.PP t.PP w) (Φ' : GenPts A t' y') :
    ∃ Φ : GenPts A t (y' ≫ f), GenPts.Rel m w Φ' Φ := by
  have hψ : ∀ _ : Fin 1, pullback.fst t'.G.hom y' ≫ m.φ = (fibIso m y').hom ≫ pullback.fst t.G.hom (y' ≫ f) :=
    fun _ => fibIso_fst m y'
  let x : A.V → (Over.mk (y' ≫ f) ⟶ t.G) := fun v => pushPt m.cart.1.w (Φ'.x v)
  have hx : ∀ v, (Φ'.x v).left ≫ m.φ = (x v).left := fun v => rfl
  choose τ hτ hr using fun v => exists_frm_up hw.1 t.PP.isLB t'.PP.isLB (Φ'.frm v)
  choose sig hsig using fun j α th => exists_secThrough_up hw.1 t.PP.isLB t'.PP.isLB hψ (Φ'.sig j α th)
  refine ⟨⟨x, fun v v' => ?_, fun e v => ?_, τ, hτ, ?_, sig, fun j _ α th hth v => ?_, fun j _ s => ?_,
    fun j _ s hs i => ?_⟩, rfl, fun v => ⟨rfl, hr v⟩⟩
  · exact (congrArg (pushPt m.cart.1.w) (Φ'.add v v')).trans (map_mul (pushHom m.cart (Over.mk y')) _ _)
  · refine Over.OverMorphism.ext ?_
    rw [← hx, Φ'.lin, Over.comp_left, Over.comp_left, ← hx, Category.assoc, Category.assoc, m.act]
  · exact (rig_fib_iff m y' hw (hx 0) (left_zero Φ'.x Φ'.add) (hr 0)).1 Φ'.rig
  · exact (hasVal_fib_iff m y' (hsig j α th) (hx v) (hr v) _).1 (Φ'.val j α th hth v)
  · obtain ⟨a, ha⟩ := exists_secThrough hw.1 t.PP.isLB t'.PP.isLB hψ s
    obtain ⟨g, hg, hv⟩ := Φ'.span j a
    exact ⟨g, hg, fun v => (hasVal_fib_iff m y' ha (hx v) (hr v) _).1 (hv v)⟩
  · obtain ⟨a, ha⟩ := exists_secThrough hw.1 t.PP.isLB t'.PP.isLB hψ s
    exact zero_up t'.PP.isLB hψ ha
      (Φ'.sep j a fun v => (hasVal_fib_iff m y' ha (hx v) (hr v) _).2 (hs v)) i

theorem exists_down (hw : IsRigIso m.cm t'.PP t.PP w) (Φ : GenPts A t (y' ≫ f)) :
    ∃ Φ' : GenPts A t' y', GenPts.Rel m w Φ' Φ := by
  have hψ : ∀ _ : Fin 1, pullback.fst t'.G.hom y' ≫ m.φ = (fibIso m y').hom ≫ pullback.fst t.G.hom (y' ≫ f) :=
    fun _ => fibIso_fst m y'
  let x : A.V → (Over.mk y' ⟶ t'.G) := fun v =>
    Over.homMk (m.cart.1.lift (Φ.x v).left y' (Over.w (Φ.x v))) (m.cart.1.lift_snd _ _ _)
  have hx : ∀ v, (x v).left ≫ m.φ = (Φ.x v).left := fun v => m.cart.1.lift_fst _ _ _
  have ext : ∀ a b : Over.mk y' ⟶ t'.G, a.left ≫ m.φ = b.left ≫ m.φ → a = b := fun a b h =>
    Over.OverMorphism.ext (m.cart.1.hom_ext h ((Over.w a).trans (Over.w b).symm))
  have add : ∀ v v', x (v + v') = x v * x v' := fun v v' => ext _ _ (by
    rw [hx, Φ.add]
    exact m.cart.2 (Over.mk y') (x v) (x v') (Φ.x v) (Φ.x v') (hx v).symm (hx v').symm)
  choose τ hτ hr using fun v => exists_frm_down (w := w) (x := (x v).left) (τ := Φ.τ v) hw.1 t.PP.isLB t'.PP.isLB
    (by have := Φ.frm v; rw [← hx v] at this; exact this)
  choose sig hsig using fun j α th => exists_secThrough hw.1 t.PP.isLB t'.PP.isLB hψ (Φ.sig j α th)
  refine ⟨⟨x, add, fun e v => ext _ _ ?_, τ, hτ, ?_, sig, fun j _ α th hth v => ?_, fun j _ s => ?_,
    fun j _ s hs i => ?_⟩, rfl, fun v => ⟨hx v, hr v⟩⟩
  · rw [hx, Φ.lin, Over.comp_left, Over.comp_left, ← hx, Category.assoc, Category.assoc, m.act]
  · exact (rig_fib_iff m y' hw (hx 0) (left_zero x add) (hr 0)).2 Φ.rig
  · exact (hasVal_fib_iff m y' (hsig j α th) (hx v) (hr v) _).2 (Φ.val j α th hth v)
  · obtain ⟨a, ha⟩ := exists_secThrough_up hw.1 t.PP.isLB t'.PP.isLB hψ s
    obtain ⟨g, hg, hv⟩ := Φ.span j a
    exact ⟨g, hg, fun v => (hasVal_fib_iff m y' ha (hx v) (hr v) _).2 (hv v)⟩
  · obtain ⟨a, ha⟩ := exists_secThrough_up hw.1 t.PP.isLB t'.PP.isLB hψ s
    exact zero_down t.PP.isLB ha
      (Φ.sep j a fun v => (hasVal_fib_iff m y' ha (hx v) (hr v) _).1 (hs v)) i

end Gen

end GlobalTheory.ArcPts.Transfer

namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

theorem genPts_transfer (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)]
    (S S' : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (y' : Sp ℂ⸨X⸩ ⟶ S') (y : Sp ℂ⸨X⸩ ⟶ S)
    (hw : IsRigIso m.cm t'.PP t.PP w) (hy : y' ≫ f = y) :
    (∀ Φ' : GenPts A t' y', ∃ Φ : GenPts A t y, GenPts.Rel m w Φ' Φ) ∧
      ∀ Φ : GenPts A t y, ∃ Φ' : GenPts A t' y', GenPts.Rel m w Φ' Φ := by
  subst hy
  exact ⟨Transfer.exists_up hw, Transfer.exists_down hw⟩

end GlobalTheory.ArcPts
