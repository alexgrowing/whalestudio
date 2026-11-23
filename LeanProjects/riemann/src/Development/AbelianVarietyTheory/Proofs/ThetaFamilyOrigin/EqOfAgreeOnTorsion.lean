import Mathlib
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.CardZerosOnTorsionCosetLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EndOnTorsion

open CechPic LBGerm TorsionZero

section Sections

variable {X Y : Scheme.{0}}

def tensSec {A B : LB X} (s : A.Sec) (t : B.Sec) : (tens A B).Sec :=
  secOfGerm (fun p => resG X (inf_le_left : A.U p.1 ⊓ B.U p.2 ≤ _) (s.f p.1) *
      resG X (inf_le_right : A.U p.1 ⊓ B.U p.2 ≤ _) (t.f p.2)) fun y p q hp hq => by
    have e : ∀ p : A.ι × B.ι, y ∈ A.U p.1 ⊓ B.U p.2 →
        gs (𝟙 X) y _ (resG X (inf_le_left : A.U p.1 ⊓ B.U p.2 ≤ _) (s.f p.1) *
          resG X (inf_le_right : A.U p.1 ⊓ B.U p.2 ≤ _) (t.f p.2)) =
        gs (𝟙 X) y _ (s.f p.1) * gs (𝟙 X) y _ (t.f p.2) := fun p hp =>
      (gs_mul _ y _ hp _ _).trans (congrArg₂ (· * ·) (gs_res _ y _ hp _) (gs_res _ y _ hp _))
    refine (e p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (congrArg Units.val (gm_tens A B (𝟙 X) y p q hp hq)) (e q hq)).symm)
    rw [gs_compat s (𝟙 X) y hp.1 hq.1, gs_compat t (𝟙 X) y hp.2 hq.2, Units.val_mul]
    exact mul_mul_mul_comm _ _ _ _

theorem nonzeroLocus_tensSec {A B : LB X} (s : A.Sec) (t : B.Sec) :
    nonzeroLocus (tensSec s t) = nonzeroLocus s ⊓ nonzeroLocus t := by
  refine nonzeroLocus_eq_of _ _ (fun y hy => ?_) fun y p hp => ?_
  · obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus hy.1
    obtain ⟨j', hj'⟩ := exists_chart_of_mem_nonzeroLocus hy.2
    exact ⟨(j, j'), hj, hj'⟩
  · have e : gs (𝟙 X) y _ ((tensSec s t).f p) = gs (𝟙 X) y _ (s.f p.1) * gs (𝟙 X) y _ (t.f p.2) :=
      (gs_mul _ y _ hp _ _).trans (congrArg₂ (· * ·) (gs_res _ y _ hp _) (gs_res _ y _ hp _))
    rw [e, IsUnit.mul_iff]
    exact and_congr (mem_nonzeroLocus_iff_isUnit s hp.1).symm (mem_nonzeroLocus_iff_isUnit t hp.2).symm

def subSec {A : LB X} (s t : A.Sec) : A.Sec where
  f i := s.f i - t.f i
  compat i j := by rw [map_sub, map_sub, s.compat i j, t.compat i j, mul_sub]

def IsLocus (c : Pic X) (W : X.Opens) : Prop :=
  ∃ (L : LB X) (hL : L.IsLB) (s : L.Sec), cls L hL = c ∧ nonzeroLocus s = W

theorem IsLocus.add {c c' : Pic X} {W W' : X.Opens} (h : IsLocus c W) (h' : IsLocus c' W') :
    IsLocus (c + c') (W ⊓ W') := by
  obtain ⟨L, hL, s, rfl, rfl⟩ := h
  obtain ⟨L', hL', s', rfl, rfl⟩ := h'
  exact ⟨_, isLB_tens hL hL', tensSec s s', rfl, nonzeroLocus_tensSec s s'⟩

theorem IsLocus.exists_sec {L : LB X} (hL : L.IsLB) {W : X.Opens} (h : IsLocus (cls L hL) W) :
    ∃ s : L.Sec, nonzeroLocus s = W := by
  obtain ⟨L', hL', s', e, rfl⟩ := h
  exact exists_sec_nonzeroLocus_eq_of_lbIso hL hL' ((cls_eq_iff _ _).1 e.symm) s'

theorem isLocus_zero : IsLocus (0 : Pic X) ⊤ := by
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (LB.isLB_triv X)).1 rfl
  exact ⟨_, LB.isLB_triv X, _, rfl, nonzeroLocus_genSec (LB.isLB_triv X) t ht⟩

theorem exists_isLocus_sum {M : LB X} (hM : M.IsLB) {σ I : Type} (s : σ → M.Sec)
    (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (h : I → (Y ⟶ X)) (y : Y) (T : Finset I) :
    ∃ W, y ∈ W ∧ IsLocus (∑ k ∈ T, pull (h k) (cls M hM)) W := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, isLocus_zero⟩
  | insert k T hk ih =>
    obtain ⟨W, hy, hW⟩ := ih
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show h k y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
    rw [Finset.sum_insert hk]
    exact ⟨h k ⁻¹ᵁ nonzeroLocus (s i) ⊓ W, ⟨hi, hy⟩, IsLocus.add
      ⟨_, pull_isLB hM _, secPull (s i) (h k), rfl, nonzeroLocus_secPull _ _⟩ hW⟩

def minor {M : LB X} (f f' : Y ⟶ X) (s t : M.Sec) : (tens (M.pull f) (M.pull f')).Sec :=
  subSec (tensSec (secPull s f) (secPull t f')) (tensSec (secPull t f) (secPull s f'))

variable {F : Type} [Field F]

theorem val_appLE (z : Sp F ⟶ Y) (q : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (e : V ≤ q ⁻¹ᵁ U) (h : ⊤ ≤ z ⁻¹ᵁ V)
    (h' : ⊤ ≤ (z ≫ q) ⁻¹ᵁ U) (a : Γ(X, U)) : val z V h ((q.appLE U V e).hom a) = val (z ≫ q) U h' a :=
  congrArg (fun r => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (r.hom a))
    (Scheme.Hom.appLE_comp_appLE z q U V ⊤ e h)

theorem le_nonzeroLocus_iff {M : LB X} (s : M.Sec) (z : Sp F ⟶ X) (k : M.ι) (hk : ⊤ ≤ z ⁻¹ᵁ M.U k) :
    ⊤ ≤ z ⁻¹ᵁ nonzeroLocus s ↔ val z _ hk (s.f k) ≠ 0 :=
  (TorsionZero.top_le_iff z _).trans ((mem_nonzeroLocus_iff_basicOpen s ((TorsionZero.top_le_iff z _).1 hk)).trans
    ((TorsionZero.top_le_iff z _).symm.trans (val_ne_zero_iff z _ hk _).symm))

theorem le_minor_iff {M : LB X} (f f' : Y ⟶ X) (s t : M.Sec) (z : Sp F ⟶ Y) {x x' : Sp F ⟶ X} (hx : z ≫ f = x)
    (hx' : z ≫ f' = x') (k k' : M.ι) (hk : ⊤ ≤ x ⁻¹ᵁ M.U k) (hk' : ⊤ ≤ x' ⁻¹ᵁ M.U k') :
    ⊤ ≤ z ⁻¹ᵁ nonzeroLocus (minor f f' s t) ↔
      val x _ hk (s.f k) * val x' _ hk' (t.f k') ≠ val x _ hk (t.f k) * val x' _ hk' (s.f k') := by
  subst hx hx'
  have h₁ : ⊤ ≤ z ⁻¹ᵁ (M.pull f).U (fun _ => k) := fun y hy => mem_pull.2 (hk hy)
  have h₂ : ⊤ ≤ z ⁻¹ᵁ (M.pull f').U (fun _ => k') := fun y hy => mem_pull.2 (hk' hy)
  have h : ⊤ ≤ z ⁻¹ᵁ (tens (M.pull f) (M.pull f')).U (fun _ => k, fun _ => k') := fun y hy => ⟨h₁ hy, h₂ hy⟩
  have e : ∀ s t : M.Sec, val z _ h ((tensSec (secPull s f) (secPull t f')).f (fun _ => k, fun _ => k')) =
      val (z ≫ f) _ hk (s.f k) * val (z ≫ f') _ hk' (t.f k') := fun s t =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((val_res z _ h h₁ _).trans (val_appLE z f _ _ _ h₁ hk _))
      ((val_res z _ h h₂ _).trans (val_appLE z f' _ _ _ h₂ hk' _)))
  rw [le_nonzeroLocus_iff _ z _ h, ← e, ← e]
  exact (iff_of_eq (congrArg (· ≠ 0) (map_sub _ _ _))).trans sub_ne_zero

theorem point_eq_of_minors {K : Type} [Field K] (p : X ⟶ Sp K) {M : LB X} {σ : Type} (s : σ → M.Sec)
    (hcov : ⨆ i, nonzeroLocus (s i) = ⊤) (haff : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, σ → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k, resG X (inf_le_right : nonzeroLocus (s i) ⊓ M.U k ≤ _) ((s j).f k) =
      resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))
    (hgen : ∀ i (f : Γ(X, nonzeroLocus (s i))), ∃ G : MvPolynomial σ K,
      f = MvPolynomial.eval₂ (constHom p _) (r i) G)
    (x x' : Sp F ⟶ X) (hp : x ≫ p = x' ≫ p) (k k' : M.ι) (hk : ⊤ ≤ x ⁻¹ᵁ M.U k) (hk' : ⊤ ≤ x' ⁻¹ᵁ M.U k')
    (h : ∀ i j, val x _ hk ((s i).f k) * val x' _ hk' ((s j).f k') =
      val x _ hk ((s j).f k) * val x' _ hk' ((s i).f k')) : x = x' := by
  have hmem : ∀ z : Sp F ⟶ X, ∃ i, ⊤ ≤ z ⁻¹ᵁ nonzeroLocus (s i) := fun z => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show z (default : PrimeSpectrum F) ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact ⟨i, (TorsionZero.top_le_iff z _).2 hi⟩
  have hval : ∀ (z : Sp F ⟶ X) i j k (hi : ⊤ ≤ z ⁻¹ᵁ nonzeroLocus (s i)) (hk : ⊤ ≤ z ⁻¹ᵁ M.U k),
      val z _ hk ((s j).f k) = val z _ hi (r i j) * val z _ hk ((s i).f k) := fun z i j k hi hk => by
    have hW : ⊤ ≤ z ⁻¹ᵁ (nonzeroLocus (s i) ⊓ M.U k) := fun y hy => ⟨hi hy, hk hy⟩
    have h1 := congrArg (val z _ hW) (hr i j k)
    rw [map_mul] at h1
    exact (val_res z _ hW hk _).symm.trans (h1.trans
      (congrArg₂ (· * ·) (val_res z _ hW hi _) (val_res z _ hW hk _)))
  obtain ⟨i, hi⟩ := hmem x
  obtain ⟨j, hj⟩ := hmem x'
  have a := (le_nonzeroLocus_iff _ x k hk).1 hi
  have b := (le_nonzeroLocus_iff _ x' k' hk').1 hj
  have c : val x' _ hk' ((s i).f k') ≠ 0 := fun h0 => mul_ne_zero a b (by rw [h i j, h0, mul_zero])
  have hi' := (le_nonzeroLocus_iff _ x' k' hk').2 c
  refine point_ext (haff i) hi hi' (RingHom.ext fun f => ?_)
  obtain ⟨G, rfl⟩ := hgen i f
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  congr 1
  · refine RingHom.ext fun t => (val_appLE x p ⊤ _ le_top hi le_top _).trans
      (Eq.trans ?_ (val_appLE x' p ⊤ _ le_top hi' le_top _).symm)
    have aux : ∀ {u u' : Sp F ⟶ Sp K} (_ : u = u') h h', val u ⊤ h = val u' ⊤ h' := by
      rintro _ _ rfl _ _; rfl
    exact congrArg (fun q : _ →+* F => q _) (aux hp _ _)
  · funext l
    have e := h i l
    rw [hval x i l k hi hk, hval x' i l k' hi' hk'] at e
    refine mul_right_cancel₀ (mul_ne_zero a c) ?_
    change val x _ hi (r i l) * _ = val x' _ hi' (r i l) * _
    linear_combination -e

end Sections

section Classes

variable {K : Type} [Field K] (P : PolAV (Sp K))

theorem lam_mul_right (hc : CubeSt) {T : Over (Sp K)} (x y z : T ⟶ P.A) :
    lam (cls P.L P.isLB) x (y * z) = lam (cls P.L P.isLB) x y + lam (cls P.L P.isLB) x z := by
  obtain ⟨t, ht⟩ := P.rigid
  obtain ⟨c⟩ := (hc _ P ⟨P.L, t, P.isLB, ht⟩ rfl).1
  rw [lam_comm, lam_mul_left P.isLB ⟨c.t, c.isGen⟩, lam_comm _ y, lam_comm _ z]

theorem lam_self (hm : MulPullSt) : lam (cls P.L P.isLB) (𝟙 P.A) (𝟙 P.A) = 2 • cls P.L P.isLB := by
  have h₀ : pull (eSec P.A) (cls P.L P.isLB) = 0 := (cls_eq_zero_iff (pull_isLB P.isLB _)).2 P.rigid
  have h₁ : pull (1 : P.A ⟶ P.A).left (cls P.L P.isLB) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    exact (congrArg _ h₀).trans (map_zero _)
  have h₂ := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 (hm _ P 2)
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h₂
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, sq, neg_smul, one_smul, add_neg_eq_zero] at h₂
  rw [lam, h₁, ← h₂, Over.id_left, pull_id]
  push_cast
  module

theorem lam_rosati {f g : P.A ⟶ P.A} (h : RosatiAdj P.A P.L f g) {T : Over (Sp K)} (x y : T ⟶ P.A) :
    lam (cls P.L P.isLB) (x ≫ f) y = lam (cls P.L P.isLB) x (y ≫ g) := by
  obtain ⟨U, hU, ht⟩ := h (default : PrimeSpectrum K)
  obtain rfl : U = ⊤ := top_unique fun y _ => by
    obtain rfl : y = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    exact hU
  have : IsIso ((P.A ⊗ P.A).hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso ((P.A ⊗ P.A).left.topIso).hom)
  have h₁ := congrArg (pull ((lift x y).left ≫ inv ((P.A ⊗ P.A).hom ⁻¹ᵁ ⊤).ι))
    ((cls_linComb P.isLB _ _ _).symm.trans ((cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 ht))
  have e : ∀ u v : P.A ⊗ P.A ⟶ P.A, padd P.A u v = u * v := fun _ _ => rfl
  simp only [map_sum, map_zsmul, map_zero, ← pull_comp, Category.assoc, IsIso.inv_hom_id_assoc] at h₁
  simp only [Fin.sum_univ_succ, rosatiφ, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_succ, ← Over.comp_left, e,
    MonObj.comp_mul, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Fin.sum_univ_zero] at h₁
  rw [← sub_eq_zero, ← h₁, lam, lam]
  module

variable {O : Type} [Ring O] [StarRing O] (ρ : P.OAct O)

theorem two_nsmul_pull_act (hm : MulPullSt) (b : O) :
    2 • pull (ρ.act b).left (cls P.L P.isLB) = lam (cls P.L P.isLB) (𝟙 P.A) (ρ.act (star b * b)) := by
  rw [← map_nsmul, ← lam_self P hm, pull_lam, ρ.map_mul, ← lam_rosati P (ρ.rosati b), Category.comp_id,
    Category.id_comp]

theorem sum_pull_act (hm : MulPullSt) (hc : CubeSt) {r c : ℕ} (a : O) (b : Fin r → O)
    (h : star a * a + ∑ i, star (b i) * b i = (c : O)) :
    pull (ρ.act a).left (4 • cls P.L P.isLB) + ∑ i, pull (ρ.act (b i)).left (4 • cls P.L P.isLB) =
      (4 * c) • cls P.L P.isLB := by
  let Φ : O →+ Pic P.A.left := AddMonoidHom.mk' (fun u => lam (cls P.L P.isLB) (𝟙 P.A) (ρ.act u)) fun u v =>
    (congrArg _ (ρ.map_add u v)).trans (lam_mul_right P hc _ _ _)
  have h₁ : Φ 1 = 2 • cls P.L P.isLB := (congrArg (lam _ _) ρ.map_one).trans (lam_self P hm)
  have h₂ : ∀ u, pull (ρ.act u).left (4 • cls P.L P.isLB) = 2 • Φ (star u * u) := fun u => by
    rw [map_nsmul, show 4 = 2 * 2 from rfl, mul_nsmul, two_nsmul_pull_act P ρ hm]
    rfl
  simp only [h₂]
  rw [← Finset.smul_sum, ← smul_add, ← map_sum, ← map_add, h, ← nsmul_one, map_nsmul, h₁]
  module

end Classes

theorem eq_of_agree_on_torsion {K : Type} [Field K] [IsAlgClosed K] (hA : AmpleSt) (hN : MulNSt)
    (P P' : PolAV (Sp K)) {d M : ℕ} (hM : (M : K) ≠ 0) (hg : 1 ≤ P.g) (hd : 4 ^ P.g * P.g.factorial * d < M ^ 2)
    (hZ : ∀ s : (lbPow P.L (4 * d)).Sec, (∃ j, s.f j ≠ 0) →
      Nat.card {x : baseOver (Sp K) ⟶ P.A // x ^ M = 1 ∧ ¬ ⊤ ≤ x.left ⁻¹ᵁ nonzeroLocus s} ≤
        4 ^ P.g * P.g.factorial * d * M ^ (2 * P.g - 2))
    (f f' : P.A ⟶ P'.A) {I : Type} [Fintype I] (h : I → (P.A.left ⟶ P'.A.left))
    (hsum : pull f.left (4 • cls P'.L P'.isLB) + pull f'.left (4 • cls P'.L P'.isLB) +
      ∑ k, pull (h k) (4 • cls P'.L P'.isLB) = (4 * d) • cls P.L P.isLB)
    (hf : ∀ x : baseOver (Sp K) ⟶ P.A, x ^ M = 1 → x ≫ f = x ≫ f') : f = f' := by
  have := polAV_isIntegral_of_isAlgClosed K P
  have := P'.isAb.proper
  obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow hA K P' 4 le_rfl
  choose haff r hr hgen using hs
  have hL := isLB_lbPow P'.isLB 4
  have hchart : ∀ {F : Type} [Field F] (x : Sp F ⟶ P'.A.left), ∃ k, ⊤ ≤ x ⁻¹ᵁ (lbPow P'.L 4).U k := fun {F} _ x => by
    obtain ⟨k, hk⟩ := exists_chart hL (x (default : PrimeSpectrum F))
    exact ⟨k, (TorsionZero.top_le_iff x _).2 hk⟩
  have hM1 : 1 ≤ M := Nat.pos_of_ne_zero fun e => hM (by rw [e, Nat.cast_zero])
  have hcard := (hN (Sp K) P M hM1).2.2.2.2 K (𝟙 _) hM
  rw [← cls_lbPow P'.isLB 4 hL, ← cls_lbPow P.isLB _ (isLB_lbPow P.isLB _)] at hsum
  obtain ⟨W, hW, hloc⟩ := exists_isLocus_sum hL s hcov h (genericPoint P.A.left) Finset.univ
  have hmin : ∀ i j, genericPoint P.A.left ∉ nonzeroLocus (minor f.left f'.left (s i) (s j)) := fun i j hij => by
    have h₁ : IsLocus (pull f.left (cls _ hL) + pull f'.left (cls _ hL))
        (nonzeroLocus (minor f.left f'.left (s i) (s j))) :=
      ⟨_, isLB_tens (pull_isLB hL _) (pull_isLB hL _), _, rfl, rfl⟩
    have h₂ := h₁.add hloc
    rw [hsum] at h₂
    obtain ⟨u, hu⟩ := h₂.exists_sec
    have h₃ : genericPoint P.A.left ∈ nonzeroLocus u := by rw [hu]; exact ⟨hij, hW⟩
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h₃
    have h₄ := hZ u ⟨k, fun e => by rw [e, Scheme.basicOpen_zero] at hk; exact hk⟩
    have h₅ : ∀ x : baseOver (Sp K) ⟶ P.A, x ^ M = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ nonzeroLocus u := fun x hx hx' => by
      obtain ⟨k, hk⟩ := hchart (F := K) (x ≫ f).left
      rw [hu] at hx'
      exact (le_minor_iff f.left f'.left (s i) (s j) (F := K) x.left (x := (x ≫ f).left) (x' := (x ≫ f).left) rfl
        (congrArg (·.left) (hf x hx)).symm k k hk hk).1 (fun y hy => (hx' hy).1) (mul_comm _ _)
    have e : M ^ (2 * P.g) = M ^ 2 * M ^ (2 * P.g - 2) := by rw [← pow_add]; congr 1; omega
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => and_iff_left_of_imp (h₅ x)), hcard, e] at h₄
    exact absurd (Nat.le_of_mul_le_mul_right h₄ (pow_pos hM1 _)) (not_le.2 hd)
  let F : Type := P.A.left.residueField (genericPoint P.A.left)
  let z : Sp F ⟶ P.A.left := P.A.left.fromSpecResidueField (genericPoint P.A.left)
  have hz : ∀ y, z y = genericPoint P.A.left := fun y => Scheme.fromSpecResidueField_apply _ y
  have : IsDominant z := ⟨(genericPoint_spec P.A.left).def.ge |> fun e => dense_iff_closure_eq.2 (top_unique
    (e.trans (closure_mono (Set.singleton_subset_iff.2 ⟨(default : PrimeSpectrum F), hz _⟩))))⟩
  have hw : f.left ≫ P'.A.hom = f'.left ≫ P'.A.hom := (Over.w f).trans (Over.w f').symm
  obtain ⟨k, hk⟩ := hchart (z ≫ f.left)
  obtain ⟨k', hk'⟩ := hchart (z ≫ f'.left)
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated P'.A.hom hw z
    (point_eq_of_minors P'.A.hom s hcov haff r hr hgen _ _ (by rw [Category.assoc, Category.assoc, hw]) k k' hk hk'
      fun i j => ?_))
  by_contra hne
  exact hmin i j (hz _ ▸ (TorsionZero.top_le_iff z _).1
    ((le_minor_iff f.left f'.left (s i) (s j) z rfl rfl k k' hk hk').2 hne))

theorem eq_of_dim_zero {K : Type} [Field K] [IsAlgClosed K] (P P' : PolAV (Sp K)) (hg : P.g = 0) (f f' : P.A ⟶ P'.A)
    (hf : (1 : baseOver (Sp K) ⟶ P.A) ≫ f = 1 ≫ f') : f = f' := by
  have := polAV_isIntegral_of_isAlgClosed K P
  have := P'.isAb.proper
  have : Etale P.A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 (hg ▸ P.smoothDim)
  let e : Sp K ⟶ P.A.left := (1 : baseOver (Sp K) ⟶ P.A).left
  have := isOpenImmersion_of_section_of_etale P.A.hom e (Over.w _)
  have : IsDominant e := ⟨e.isOpenEmbedding.isOpen_range.dense ⟨_, (default : PrimeSpectrum K), rfl⟩⟩
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated P'.A.hom ((Over.w f).trans (Over.w f').symm) e
    (congrArg (·.left) hf))

end GlobalTheory.EndOnTorsion

namespace GlobalTheory

open CechPic EndOnTorsion in

theorem endDeterminedOnTorsion : Out.Laws →
    (∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (b : Out.baseOver (Sp K) ⟶ P.A),
      1 ≤ P.g → 4 ≤ N → (k : K) ≠ 0 → ∀ s : (lbPow P.L (N * d)).Sec, (∃ j, s.f j ≠ 0) →
      Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ k = b ∧ ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus s} ≤
        N ^ P.g * P.g.factorial * d * k ^ (2 * P.g - 2)) →
    EndDeterminedOnTorsionSt := by
  rintro laws hZ g c M hc K _ _ hM P P' rfl - φ ⟨hφ, hφL⟩ O _ _ ρ ρ' a ⟨m, r, b, hm, hb⟩ hx
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · exact eq_of_dim_zero P P' hg _ _ (hx 1 (one_pow _))
  have := ρ'.hom a
  have hl : pull φ.hom.left (cls P'.L P'.isLB) = cls P.L P.isLB :=
    (cls_eq_iff (pull_isLB P'.isLB _) P.isLB).2 hφL
  have e₁ : ρ.act (m * a) ≫ φ.hom = mulA P.A m ≫ ρ.act a ≫ φ.hom := by
    rw [Nat.cast_comm, ρ.map_mul, ThetaPtDet.act_natCast ρ.toRingAct, Category.assoc]
  have e₂ : φ.hom ≫ ρ'.act (m * a) = mulA P.A m ≫ φ.hom ≫ ρ'.act a := by
    rw [Nat.cast_comm, ρ'.map_mul, ← Category.assoc,
      ← ThetaPtDet.conclusion_natCast P P' φ ⟨hφ, hφL⟩ ρ ρ' m, ThetaPtDet.act_natCast ρ.toRingAct, Category.assoc]
  have e₃ : ρ.act (m * a) ≫ φ.hom = (ρ.act a ≫ φ.hom) ^ m := by
    have := ρ.hom a
    rw [e₁, MonObj.pow_comp, Category.id_comp]
  have e₄ : φ.hom ≫ ρ'.act (m * a) = (φ.hom ≫ ρ'.act a) ^ m := by
    rw [e₂, MonObj.pow_comp, Category.id_comp]
  have key : ρ.act (m * a) ≫ φ.hom = φ.hom ≫ ρ'.act (m * a) := by
    refine eq_of_agree_on_torsion laws.ample laws.mulN P P' hM hg hc (hZ K P 4 (2 * c) M 1 hg le_rfl hM) _ _
      (I := Fin r ⊕ Fin r) (Sum.elim (fun l => (ρ.act (b l)).left ≫ φ.hom.left)
        fun l => φ.hom.left ≫ (ρ'.act (b l)).left) ?_ fun x h => ?_
    · have h₁ := sum_pull_act P ρ laws.mulPull laws.cube _ b hb
      have h₂ := congrArg (pull φ.hom.left) (sum_pull_act P' ρ' laws.mulPull laws.cube _ b hb)
      rw [map_add, map_sum, map_nsmul _ (4 * c), hl] at h₂
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Over.comp_left, pull_comp,
        map_nsmul (pull φ.hom.left) 4 (cls P'.L P'.isLB), hl]
      rw [add_add_add_comm, h₁, h₂]
      module
    · rw [e₃, e₄, MonObj.comp_pow, MonObj.comp_pow, hx x h]
  rw [e₁, e₂] at key
  have := polAV_isIntegral_of_isAlgClosed K P
  have := P'.isAb.proper
  have := (laws.mulN _ P m hm).2.2.1
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated P'.A.hom ((Over.w _).trans (Over.w _).symm)
    (mulA P.A m).left (congrArg (·.left) key))

end GlobalTheory
