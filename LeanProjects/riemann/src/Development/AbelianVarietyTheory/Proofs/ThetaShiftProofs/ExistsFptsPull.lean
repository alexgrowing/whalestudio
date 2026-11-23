import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.FibrePull

section Val
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {A : Type} [CommRing A] [IsLocalRing A]

abbrev wv (w : LB.Iso L' (L.pull F)) (x : Sp A ⟶ X') (j : L.ι) (k : L'.ι) : A :=
  valR x ((LB.div (L.pull F) L').U (fun _ => j, k)) (w.s (fun _ => j, k)).val

omit [IsLocalRing A] in
theorem le_div_iff (x : Sp A ⟶ X') (j : L.ι) (k : L'.ι) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, k) ↔ ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j ∧ ⊤ ≤ x ⁻¹ᵁ L'.U k :=
  ⟨fun h => ⟨fun _ hz => mem_pull.1 (h hz).1, fun _ hz => (h hz).2⟩,
    fun h _ hz => ⟨mem_pull.2 (h.1 hz), h.2 hz⟩⟩

theorem exists_chart_pt (hL : L.IsLB) (x : Sp A ⟶ X) : ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
  obtain ⟨j, hj⟩ := exists_chart hL (x (cpt A))
  exact ⟨j, (top_le_iff_cpt x _).2 hj⟩

omit [IsLocalRing A] in
theorem toStkA_wv (w : LB.Iso L' (L.pull F)) (x : Sp A ⟶ X') {j : L.ι} {k : L'.ι} (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ L'.U k) (z : Sp A) : toStkA z (wv w x j k) = (gw w x z j k).val :=
  toStkA_valR x _ z ((le_div_iff x j k).2 ⟨hj, hk⟩) _

omit [IsLocalRing A] in
theorem isUnit_wv (w : LB.Iso L' (L.pull F)) (x : Sp A ⟶ X') {j : L.ι} {k : L'.ι} (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ L'.U k) : IsUnit (wv w x j k) :=
  FormalValue.isUnit_valR x _ ((le_div_iff x j k).2 ⟨hj, hk⟩) _

theorem wv_trans {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (x : Sp A ⟶ X') {j j' : L.ι} {k k' : L'.ι}
    (hj : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j') (hk : ⊤ ≤ x ⁻¹ᵁ L'.U k) (hk' : ⊤ ≤ x ⁻¹ᵁ L'.U k') :
    wv w x j k * valR x (L'.U k ⊓ L'.U k') (L'.g k k').val =
      valR (x ≫ F) (L.U j ⊓ L.U j') (L.g j j').val * wv w x j' k' := by
  apply toStkA_injective
  rw [map_mul, map_mul, toStkA_wv w x hj hk, toStkA_wv w x hj' hk',
    toStkA_valR x (L'.U k ⊓ L'.U k') _ (fun _ hz => ⟨hk hz, hk' hz⟩),
    toStkA_valR (x ≫ F) (L.U j ⊓ L.U j') _ (fun _ hz => ⟨hj hz, hj' hz⟩),
    (isGen_iff w).1 hw _ x (cpt A) j j' k k' (hj trivial) (hj' trivial) (hk trivial) (hk' trivial),
    ← Units.val_mul, ← Units.val_mul, mul_right_comm, inv_mul_cancel_right]

theorem valR_g_self (hL : L.IsLB) (x : Sp A ⟶ X) {j : L.ι} (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  apply toStkA_injective
  rw [toStkA_valR x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨hj hz, hj hz⟩), gm_self hL x _ (hj trivial), map_one, Units.val_one]

theorem exists_frm {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (x : Sp A ⟶ X')
    (τ : L.ι → A) (hτ : IsFrm L (x ≫ F) τ) : ∃ τ' : L'.ι → A, IsFrm L' x τ' ∧
      ∀ j k, ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j → ⊤ ≤ x ⁻¹ᵁ L'.U k → τ j = wv w x j k * τ' k := by
  obtain ⟨j₀, h₀⟩ := exists_chart_pt hL (x ≫ F)
  have key : ∀ k, ⊤ ≤ x ⁻¹ᵁ L'.U k → τ j₀ = wv w x j₀ k * (Ring.inverse (wv w x j₀ k) * τ j₀) := fun k hk => by
    rw [Ring.mul_inverse_cancel_left _ _ (isUnit_wv w x h₀ hk)]
  refine ⟨fun k => Ring.inverse (wv w x j₀ k) * τ j₀, ⟨fun k hk => ?_, fun k k' hkk => ?_⟩, fun j k hj hk => ?_⟩
  · exact (isUnit_ringInverse.2 (isUnit_wv w x h₀ hk)).mul (hτ.1 _ h₀)
  · have hk : ⊤ ≤ x ⁻¹ᵁ L'.U k := fun _ hz => (hkk hz).1
    have hk' : ⊤ ≤ x ⁻¹ᵁ L'.U k' := fun _ hz => (hkk hz).2
    refine (isUnit_wv w x h₀ hk).mul_left_cancel ?_
    rw [← key k hk, ← _root_.mul_assoc, wv_trans hw x h₀ h₀ hk hk', valR_g_self hL _ h₀, _root_.one_mul, ← key k' hk']
  · have e := wv_trans hw x hj h₀ hk hk
    rw [valR_g_self hL' _ hk, _root_.mul_one] at e
    rw [e, _root_.mul_assoc, ← key k hk]
    exact hτ.2 j j₀ (fun _ hz => ⟨hj hz, h₀ hz⟩)

variable {w : LB.Iso L' (L.pull F)} {p' : Y' ⟶ X'} {p : Y ⟶ X} {h : Y' ⟶ Y} {n : ℕ}

abbrev TransportedAlt (w : LB.Iso L' (L.pull F)) (a : SecP L' p' n) (t : SecP L p n) (h : Y' ⟶ Y) : Prop :=
  ConstFam.SecThrough w (K := Fin 1) (fun _ => p') (fun _ => p) (fun _ => (n : ℤ)) a t h

theorem TransportedAlt.sval_eq (hp : p' ≫ F = h ≫ p) {a : SecP L' p' n} {t : SecP L p n} (H : TransportedAlt w a t h) (r : Sp A ⟶ Y')
    {j : L.ι} {k : L'.ι} (hj : ⊤ ≤ ((r ≫ p') ≫ F) ⁻¹ᵁ L.U j) (hk : ⊤ ≤ (r ≫ p') ⁻¹ᵁ L'.U k) :
    ArcPts.sval t (r ≫ h) j = wv w (r ≫ p') j k ^ n * ArcPts.sval a r k := by
  have hj' : ⊤ ≤ ((r ≫ h) ≫ p) ⁻¹ᵁ L.U j := by rwa [Category.assoc, ← hp, ← Category.assoc]
  apply toStkA_injective
  have e := H _ r (cpt A) (fun _ => j) (fun _ => k) (fun _ => hj trivial) (fun _ => hk trivial)
  rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val] at e
  rw [map_mul, map_pow, toStkA_wv w _ hj hk]
  exact (FormalValue.toStkA_valR_eq_gs (r ≫ h) (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j)) _
    (fun _ hz => Set.mem_iInter.2 fun _ => hj' hz) _).trans (e.trans (congrArg _
      (FormalValue.toStkA_valR_eq_gs r (LB.wchart L' (fun _ : Fin 1 => p') (fun _ => k)) _
        (fun _ hz => Set.mem_iInter.2 fun _ => hk hz) _).symm))

theorem TransportedAlt.hasVal_iff (hL : L.IsLB) (hL' : L'.IsLB) (hp : p' ≫ F = h ≫ p) {a : SecP L' p' n} {t : SecP L p n}
    (H : TransportedAlt w a t h) (r : Sp A ⟶ Y') {τ : L.ι → A} {τ' : L'.ι → A}
    (hτ : ∀ j k, ⊤ ≤ ((r ≫ p') ≫ F) ⁻¹ᵁ L.U j → ⊤ ≤ (r ≫ p') ⁻¹ᵁ L'.U k → τ j = wv w (r ≫ p') j k * τ' k) (c : A) :
    HasVal a r τ' c ↔ HasVal t (r ≫ h) τ c := by
  have e : (r ≫ h) ≫ p = (r ≫ p') ≫ F := by rw [Category.assoc, ← hp, ← Category.assoc]
  constructor
  · intro Ha j hj
    rw [e] at hj
    obtain ⟨k, hk⟩ := exists_chart_pt hL' (r ≫ p')
    rw [H.sval_eq hp r hj hk, Ha k hk, hτ j k hj hk]
    ring
  · intro Ht k hk
    obtain ⟨j, hj⟩ := exists_chart_pt hL ((r ≫ p') ≫ F)
    refine ((isUnit_wv w _ hj hk).pow n).mul_left_cancel ?_
    rw [← H.sval_eq hp r hj hk, Ht j (by rwa [e]), hτ j k hj hk]
    ring

theorem TransportedAlt.eq_zero (hL : L.IsLB) (hp : p' ≫ F = h ≫ p) {a : SecP L' p' n} {t : SecP L p n} (H : TransportedAlt w a t h)
    (ht : ∀ i, t.f i = 0) (i) : a.f i = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨j, hj⟩ := exists_chart hL (F (p' y))
  have e := H _ (𝟙 _) y (fun _ => j) i (fun _ => hj) (fun k => Set.mem_iInter.1 hy k)
  have hm : (𝟙 Y' ≫ h) y ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) := Set.mem_iInter.2 fun _ => by
    show (h ≫ p) y ∈ L.U j
    rw [← hp]; exact hj
  have z₁ : gs (𝟙 Y' ≫ h) y (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j)) (t.f fun _ => j) = 0 := by
    refine (congrArg (gs _ _ _) (ht fun _ => j)).trans ((gs_eq _ _ _ hm _).trans ?_)
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  rw [z₁] at e
  refine ((Units.mul_right_eq_zero _).1 e.symm).trans ?_
  exact ((gs_eq _ _ _ hy _).trans ((congrArg _ (map_zero _)).trans (map_zero _))).symm

theorem exists_thr_up (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) [IsIso h] (hp : p' ≫ F = h ≫ p)
    (a : SecP L' p' n) : ∃ t : SecP L p n, TransportedAlt w a t h := by
  obtain ⟨t₀, h₀⟩ := ConstFam.exists_sec_up ((isGen_iff w).1 hw) hL hL' a
  obtain rfl : p = inv h ≫ p' ≫ F := by rw [hp, IsIso.inv_hom_id_assoc]
  refine ⟨DVR.pullSec L (fun _ => p' ≫ F) _ t₀ (inv h), fun Z r z P Q hP hQ => ?_⟩
  have e : (r ≫ h) ≫ inv h = r := by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hm : (r ≫ h) z ∈ LB.wchart L (fun _ : Fin 1 => inv h ≫ p' ≫ F) P := Set.mem_iInter.2 fun k => by
    show ((r ≫ h) ≫ inv h ≫ p' ≫ F) z ∈ L.U (P k)
    rw [← Category.assoc, e]; exact hP k
  refine ((gs_res (r ≫ h) z _ hm _).trans
    (gs_pull (r ≫ h) (inv h) z _ (Out.wchart_comp_le L (fun _ => p' ≫ F) (inv h) P hm) _)).trans ?_
  rw [e]
  exact h₀ Z r z P Q (Set.mem_iInter.2 hP) (Set.mem_iInter.2 hQ)

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]

omit [StarRing (𝓞 E)] in

theorem exists_fpts {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (hw : IsRigIso m.cm t'.PP t.PP w) {F : Type} [Field F] {V : Type}
    [AddCommGroup V] {act : 𝓞 E → V → V} {I : ℕ → Type} {φ : ∀ j, I j → V → F} (y' : Sp F ⟶ S') (y : Sp F ⟶ S)
    (hy : y' ≫ f = y) (Θ : FPts act t y φ) : ∃ Θ' : FPts act t' y' φ,
      (∀ v, (Θ'.x v).left ≫ m.φ = (Θ.x v).left ∧ ∀ j j',
        ⊤ ≤ (Θ'.x v).left ⁻¹ᵁ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') →
        Θ.τ v j = valR (Θ'.x v).left _ (w.s (fun _ => j, j')).val * Θ'.τ v j') ∧
      ∀ k ψ (p : Over.mk y ⟶ t.G) (p' : Over.mk y' ⟶ t'.G), p'.left ≫ m.φ = p.left → Θ.Lev k p ψ → Θ'.Lev k p' ψ := by
  subst hy
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  let ρ : (Over.mk y' ⟶ t'.G) →* (Over.mk (y' ≫ f) ⟶ t.G) := pushHom m.cart (Over.mk y')
  have ρl : ∀ x, (ρ x).left = x.left ≫ m.φ := fun _ => rfl
  have inj : Function.Injective ρ := fun a b e => Over.OverMorphism.ext (m.cart.1.hom_ext
    (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))
  have surj : Function.Surjective ρ := fun b =>
    ⟨Over.homMk (m.cart.1.lift b.left y' (Over.w b)) (m.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (m.cart.1.lift_fst _ _ _)⟩
  choose x hx using fun v => surj (Θ.x v)
  have hxl : ∀ v, (x v).left ≫ m.φ = (Θ.x v).left := fun v => congrArg (fun q => q.left) (hx v)
  have sq : IsPullback (pullback.fst t'.G.hom y' ≫ m.φ) (pullback.snd t'.G.hom y') t.G.hom (y' ≫ f) :=
    (IsPullback.of_hasPullback t'.G.hom y').paste_horiz m.cart.1
  let h : pullback t'.G.hom y' ⟶ pullback t.G.hom (y' ≫ f) := sq.isoPullback.hom
  have hp : pullback.fst t'.G.hom y' ≫ m.φ = h ≫ pullback.fst t.G.hom (y' ≫ f) := sq.isoPullback_hom_fst.symm
  have f₁ : ∀ a : Over.mk y' ⟶ t'.G, fib a ≫ pullback.fst t'.G.hom y' = a.left := fun a => pullback.lift_fst _ _ _
  have fh : ∀ a : Over.mk y' ⟶ t'.G, fib a ≫ h = fib (ρ a) := fun a => pullback.hom_ext
    (by rw [Category.assoc, ← hp, ← Category.assoc, f₁]; exact (pullback.lift_fst _ _ _).symm)
    (by rw [Category.assoc, sq.isoPullback_hom_snd]
        exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm)
  choose τ hτ hτw using fun v => exists_frm hw.1 hL hL' (x v).left (Θ.τ v) (by rw [hxl]; exact Θ.frm v)
  choose sig hsig using fun j i => ConstFam.exists_secThrough (K := Fin 1) (φ' := fun _ => pullback.fst t'.G.hom y')
    hw.1 hL hL' (fun _ => hp) (Θ.sig j i)
  have hv : ∀ {n : ℕ} {a : SecP t'.PP.L (pullback.fst t'.G.hom y') n} {b : SecP t.PP.L (pullback.fst t.G.hom (y' ≫ f)) n},
      TransportedAlt w a b h → ∀ v c, HasVal a (fib (x v)) (τ v) c ↔ HasVal b (fib (Θ.x v)) (Θ.τ v) c := fun T v c => by
    rw [← hx v, ← fh]
    exact T.hasVal_iff hL hL' hp _ (by rw [f₁]; exact hτw v) c
  have add : ∀ v v', x (v + v') = x v * x v' := fun v v' => inj (by rw [map_mul, hx, hx, hx, Θ.add])
  have x0 : (x 0).left = y' ≫ eSec t'.G := by
    have : x 0 = 1 := by
      have e := add 0 0
      rw [add_zero] at e
      exact left_eq_mul.1 e
    rw [this]
    show (toUnit _ ≫ η[t'.G]).left = _
    simp [eSec]
  refine ⟨⟨x, add, fun e v => inj ?_, τ, hτ, fun k hk => ?_, sig, fun n hn i v => (hv (hsig n i) v _).2 (Θ.val n hn i v),
    fun n hn s => ?_, fun n hn s hs => ?_⟩, fun v => ⟨hxl v, fun j k hjk => ?_⟩, fun k ψ p p' hpp ⟨l₁, l₂, l₃⟩ => ?_⟩
  · refine Over.OverMorphism.ext ?_
    rw [hx, Θ.lin, ρl, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hxl]
  · obtain ⟨j, hj⟩ := exists_chart_pt hL ((x 0).left ≫ m.φ)
    refine (isUnit_wv w _ hj hk).mul_left_cancel ?_
    rw [← hτw 0 j k hj hk, Θ.rig j (by rw [← hxl]; exact hj)]
    have P := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m.cm.e _
      (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl)).1 hw.2
    rw [x0] at hj hk ⊢
    have e := P _ y' (cpt F) (fun _ => j) (fun _ => k) (fun _ => hj trivial) (fun _ => hk trivial)
    rw [Fintype.prod_unique, zpow_one, m.base] at e
    have hj' : ⊤ ≤ ((y' ≫ f) ≫ eSec t.G) ⁻¹ᵁ t.PP.L.U j := by
      have := m.cm.e_comm
      rw [m.base] at this
      rw [Category.assoc, ← this, ← Category.assoc]; exact hj
    apply toStkA_injective
    rw [map_mul, toStkA_wv w _ hj hk]
    refine (toStkA_valR (y' ≫ f) _ _ (fun _ hz => mem_pull.2 (hj' hz)) _).trans ((congrArg Units.val e).trans ?_)
    rw [Units.val_mul]
    exact congrArg _ (toStkA_valR y' _ _ (fun _ hz => mem_pull.2 (hk hz)) _).symm
  · obtain ⟨b, hb⟩ := exists_thr_up hw.1 hL hL' hp s
    obtain ⟨N, r, i, hi⟩ := Θ.span n hn b
    exact ⟨N, r, i, fun v => (hv hb v _).2 (hi v)⟩
  · obtain ⟨b, hb⟩ := exists_thr_up hw.1 hL hL' hp s
    exact hb.eq_zero hL hp (Θ.sep n hn b fun v => (hv hb v _).1 (hs v))
  · exact hτw v j k ((le_div_iff _ j k).1 hjk).1 ((le_div_iff _ j k).1 hjk).2
  · obtain rfl : ρ p' = p := Over.OverMorphism.ext hpp
    refine ⟨inj (by rw [map_pow, l₁, map_one]), l₂, fun i i' z j' hj' => ?_⟩
    obtain ⟨j, hj⟩ := exists_chart_pt hL ((x z * p').left ≫ m.φ)
    have e := l₃ i i' z j (by rw [← hx, ← map_mul]; exact hj)
    have hj₁ : ⊤ ≤ ((fib (x z * p') ≫ pullback.fst t'.G.hom y') ≫ m.φ) ⁻¹ᵁ t.PP.L.U j := by rw [f₁]; exact hj
    have hj₂ : ⊤ ≤ (fib (x z * p') ≫ pullback.fst t'.G.hom y') ⁻¹ᵁ t'.PP.L.U j' := by rw [f₁]; exact hj'
    rw [← hx, ← map_mul, ← fh, TransportedAlt.sval_eq hp (hsig k i) _ hj₁ hj₂, TransportedAlt.sval_eq hp (hsig k i') _ hj₁ hj₂,
      _root_.mul_assoc, _root_.mul_assoc] at e
    exact ((isUnit_wv w _ hj₁ hj₂).pow k).mul_left_cancel e

theorem exists_fpts_pull : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l bb s) (y : Sp F ⟶ S) (s' : Sp F ⟶ Sp B) (Θ : FPts act o.t y φ), y ≫ s = s' → ∃ (o' : Obj D l bb s') (m : ObjMap o' o y) (w : LB.Iso o'.t.PP.L (o.t.PP.L.pull m.toSABMap.φ)) (Θ' : FPts act o'.t (𝟙 _) φ), IsRigIso m.toSABMap.cm o'.t.PP o.t.PP w ∧ (∀ v, (Θ'.x v).left ≫ m.toSABMap.φ = (Θ.x v).left ∧ ∀ j j', ⊤ ≤ (Θ'.x v).left ⁻¹ᵁ (LB.div (o.t.PP.L.pull m.toSABMap.φ) o'.t.PP.L).U (fun _ => j, j') → Θ.τ v j = valR (Θ'.x v).left _ (w.s (fun _ => j, j')).val * Θ'.τ v j') ∧ ∀ k ψ (p : Over.mk y ⟶ o.t.G) (p' : Over.mk (𝟙 (Sp F)) ⟶ o'.t.G), 1 ≤ k → p'.left ≫ m.toSABMap.φ = p.left → Θ.Lev k p ψ → Θ'.Lev k p' ψ := by
  intro _ _ E _ _ _ H _ D l B _ bb F _ _ _ V _ act I φ S s o y s' Θ hy
  obtain ⟨o', ⟨m⟩⟩ := obj_pull E H D l B B bb bb (RingHom.id B) S (Sp F) s s' y rfl rfl (by
    rw [hy]; exact (Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) o
  obtain ⟨w, h₁, h₂, -⟩ := m.toSABMap.lin
  obtain ⟨Θ', r₁, r₂⟩ := exists_fpts m.toSABMap w ⟨h₁, h₂⟩ (𝟙 _) y (Category.id_comp _) Θ
  exact ⟨o', m, w, Θ', ⟨h₁, h₂⟩, r₁, fun k ψ p p' _ => r₂ k ψ p p'⟩

end GlobalTheory.FibrePull
