import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.TorsCoord

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank

variable {S : Scheme.{0}} {T T' : Over S}

theorem isThetaPtOver_pull_of_gen (P : PolAV S) {n : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)}
    (H : IsThetaPtOver P n x v) (h : T' ⟶ T)
    (hg : ∀ th, IsGenSec P.A P.L 1 th → IsGenSec P.A P.L 1 (pullS P.A 1 h th)) :
    IsThetaPtOver P n (fun a => h ≫ x a) (fun a => h.left.appTop.hom (v a)) := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨α', hα', k₁⟩ := exists_twist_pull P.A (ψ := mulT P.A T n) (hm := lift_snd _ _) (b := 1)
    hL hα h (ψ' := mulT P.A T' n) (lift_snd _ _) (mulT_comm P.A h n)
  obtain ⟨τ', hτ', k₂⟩ := exists_gen_pullTo (φ' := fun _ : Fin 1 => (1 : T' ⟶ P.A).left) τ hτ h.left
    (fun _ => by rw [← Over.comp_left, MonObj.comp_one])
  choose U' hU' k₃ using fun a => exists_symLift_act_pull hL h (hU a)
  refine ⟨_, _, α', τ', U', fun a => pullS P.A _ h (s₂ a), fun a => h.left.appTop.hom (w a),
    Units.map h.left.appTop.hom.toMonoidHom u, hg _ hth, hα', hτ', k₁ _ _ hs₁, hU',
    fun a => k₃ a _ _ (hs₂ a), fun a => isValueAt_of_sv hL hτ' fun z J hJ => ?_, fun a => ?_⟩
  · have q := sv_of_isValueAt (hw a) h hJ
    rw [MonObj.comp_one] at q
    rw [sv_pullS _ _ _ _ _ z hJ, ← Over.comp_left, lift_whiskerRight, Category.id_comp, q, k₂ _ _ z J hJ,
      Category.id_comp]
    exact congrArg (· * _) ((gs_pull (𝟙 _) h.left z ⊤ trivial _).trans (by rw [Category.id_comp])).symm
  · exact (congrArg h.left.appTop.hom (hv a)).trans (map_mul _ _ _)

theorem eq_zero_of_smul_gen (P : PolAV S) {n : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)}
    (H : IsThetaPtOver P n x v) (hv : Ideal.span (Set.range v) = ⊤) {th₀ : LB.Sec (LPow P.A P.L 1 T)}
    (h₀ : IsGenSec P.A P.L 1 th₀) {c : Γ(T.left, ⊤)} (hc : c • SecM.ofSec P.A th₀ = 0) : c = 0 := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, -, hα, hτ, hs₁, hU, hs₂, hw, hvw⟩ := H
  obtain ⟨r, hr⟩ := h₀ th
  have e : SecM.ofSec P.A th = r • SecM.ofSec P.A th₀ := Subtype.ext (funext hr)
  have hc' : c • SecM.ofSec P.A th = (0 : Γ(T.left, ⊤)) • SecM.ofSec P.A th := by
    rw [zero_smul, e, smul_comm, hc, smul_zero]
  have key : ∀ i, c * w i = 0 := fun i => fn_ext fun z _ => by
    choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart hL (χ z)
    replace hJ : Good P.L z J := hJ
    have a₃ := ThetaAct.sv_smul c (SecM.ofSec P.A th) (lift (𝟙 T) (x i ^ n)).left z hJ
    rw [hc', ThetaAct.sv_smul _ _ _ _ hJ, lift_fst_left, LBGerm.gs_zero _ z ⊤ trivial, zero_mul] at a₃
    replace a₃ : 0 = gs (𝟙 T.left) z ⊤ c * sv P.A th (lift (𝟙 T) (x i ^ n)).left z J := a₃
    have b₁ := sv_act (hU i).pt_eq (hs₂ i) (𝟙 T) hJ 1
    have b₂ := sv_mulPull hs₁ (𝟙 T) hJ (x i)
    have b₃ := sv_of_isValueAt (hw i) (𝟙 T) hJ
    rw [Category.id_comp, _root_.mul_one] at b₁
    rw [Category.id_comp] at b₃
    rw [b₃, b₂] at b₁
    simp only [Over.id_left] at b₁
    refine (Units.mul_left_inj (val τ (𝟙 T.left) z J)).1 ?_
    rw [gs_mul _ _ ⊤ trivial, LBGerm.gs_zero _ z ⊤ trivial, zero_mul, _root_.mul_assoc, b₁, mul_left_comm,
      mul_left_comm (gs _ z ⊤ c), ← a₃, mul_zero, mul_zero]
  have : Ideal.span (Set.range v) ≤ (Submodule.span Γ(T.left, ⊤) {c}).annihilator := Ideal.span_le.2 (by
    rintro _ ⟨i, rfl⟩
    refine (Submodule.mem_annihilator_span_singleton _ _).2 ?_
    rw [hvw, smul_eq_mul, _root_.mul_assoc, mul_comm (w i), key, mul_zero])
  rw [hv] at this
  simpa using (Submodule.mem_annihilator_span_singleton c 1).1 (this trivial)

theorem secCoord_of_isValueAt {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {I : Type} {t : I → LB.Sec (LPow A L k (Over.mk x))} {w : Over.mk x ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := (Over.mk x).left) (K := Fin 1) (fun _ => w.left) (fun _ => k))} (hτ : τ.IsGen)
    {v : I → R} (H : ∀ a, IsValueAt A L k (t a) w τ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v a))) :
    SecCoord _ t (lift (𝟙 (Over.mk x)) w).left v := by
  have e : (lift (𝟙 (Over.mk x)) w).left ≫ (snd (Over.mk x) A).left = w.left := by rw [← Over.comp_left, lift_snd]
  have mem : ∀ (y : Sp R) j, (lift (𝟙 (Over.mk x)) w).left y ∈ (LPow A L k (Over.mk x)).U j →
      y ∈ LB.wchart L (fun _ : Fin 1 => w.left) j :=
    EmbPull.mem_wchart_of_eq (φ := fun _ : Fin 1 => (snd (Over.mk x) A).left) _ (fun _ => e)
  have le : ∀ j : PUnit → Fin 1 → L.ι, ((LPow A L k (Over.mk x)).pull (lift (𝟙 (Over.mk x)) w).left).U j ≤
      LB.wchart L (fun _ : Fin 1 => w.left) (j PUnit.unit) := fun j y hy => mem y _ (mem_pull.1 hy)
  refine SegreCoord.secCoord_mk (fun j => resG (Sp R) (le j) (τ.s (j PUnit.unit)).val)
    (fun y j => gs (𝟙 (Sp R)) y (LB.wchart L (fun _ : Fin 1 => w.left) j) (τ.s j).val)
    (fun j y hy => gs_res _ y (le j) hy _) (fun y j hy => ?_) (fun y j j' hy hy' => ?_) (fun y j i hy => ?_)
  · exact (congrArg IsUnit (gs_unit (𝟙 (Sp R)) y _ (mem y j hy) _)).mpr (Units.isUnit _)
  · have q := gen_trans hτ (𝟙 (Sp R)) y (mem y j hy) (mem y j' hy')
    refine (gs_unit (𝟙 (Sp R)) y _ (mem y j hy) _).trans ((congrArg Units.val q).trans ((Units.val_mul _ _).trans
      (congrArg₂ (· * ·) (congrArg Units.val ?_) (gs_unit (𝟙 (Sp R)) y _ (mem y j' hy') _).symm)))
    refine Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => (snd (Over.mk x) A).left) (fun _ => k) _ y j j' hy hy').symm
    unfold trF
    simp only [e]
    exact Finset.prod_congr rfl fun i _ => by rw [Category.id_comp (X := Sp R) w.left]
  · have hz := mem y j hy
    have q := ((gs_res (𝟙 (Sp R)) y (val_le A L w j) hz _).trans (gs_pull (𝟙 (Sp R)) (ptSecT A w).left y
      (LB.wchart L (fun _ : Fin 1 => (snd (Over.mk x) A).left) j) (val_le A L w j hz) ((t i).f j))).symm.trans
      ((congrArg (gs (𝟙 (Sp R)) y _) (H i j)).trans ((gs_mul (𝟙 (Sp R)) y _ hz _ _).trans
      (congrArg (· * _) ((gs_res (𝟙 (Sp R)) y le_top hz _).trans (SegreCoord.ev_eq y _).symm))))
    exact (congrArg (fun f : Sp R ⟶ _ => gs f y (LB.wchart L (fun _ : Fin 1 => (snd (Over.mk x) A).left) j)
      ((t i).f j)) (Category.id_comp _)).symm.trans q

theorem exists_unit_value (hG : GlobalFnsSt) (hS : SecBaseChangeAnySt) (P : PolAV S) {g m r N N' : ℕ}
    (hN : N = m ^ 2) (hN' : N' = r * m) (ho : Odd N') [IsAffine T.left] [IsAffine T'.left]
    {pt : Fin (2 * g) → (T ⟶ P.A)} (h : ∀ i, pt i ^ (N' ^ 2) = 1) {ze : Γ(T.left, ⊤)ˣ} (hze : ze ^ (N' ^ 2) = 1)
    (hp : ∀ i j, WeilIs P.A P.L (N' ^ 2 : ℕ) (pt i) (pt j) (ze ^ stdSymp g i j))
    {v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ(T.left, ⊤)} (hs : Ideal.span (Set.range v) = ⊤) {V : T.left.Opens}
    (hv : IsThetaPtOver P N' (fun a => overResι V ≫ lab pt a) (fun a => V.ι.appTop.hom (v a)))
    {th t} (hth : IsGenSec P.A P.L 1 th)
    (ht : IsThetaFamily P N m (fun a : Fin (2 * g) → ZMod (N' ^ 2) => lab pt a ^ r ^ 2) th t)
    (k : T' ⟶ overRes V) (j : T' ⟶ T) (hj : k ≫ overResι V = j) (c : Fin (2 * g) → ZMod (N' ^ 2))
    (w : T' ⟶ P.A) (hw : j ≫ lab pt c ^ N' = w)
    (τ : LB.Gen (LB.LinComb P.L (Y := T'.left) (K := Fin 1) (fun _ => w.left) (fun _ => (N : ℤ)))) (hτ : τ.IsGen) :
    ∃ u : Γ(T'.left, ⊤)ˣ, ∀ a, IsValueAt P.A P.L N (pullS P.A N j (t a)) w τ
      (u * j.left.appTop.hom ((ze ^ thetaCoordExp m r a c : Γ(T.left, ⊤)ˣ) * v (thetaCoordIdx m r a c))) := by
  have := P.isAb.comm
  have hL := P.isLB
  have hg := EmbPull.isGenSec_pullS P hS j hth
  have el : ∀ a : Fin (2 * g) → ZMod (N' ^ 2), j ≫ lab pt a = lab (fun i => j ≫ pt i) a := fun a =>
    comp_linComb j _ _
  have H : IsThetaPtOver P N' (lab (fun i => j ≫ pt i)) (fun a => j.left.appTop.hom (v a)) := by
    have := isThetaPtOver_pull_of_gen P hv k fun th' hth' s => by
      obtain ⟨ρ, hρ⟩ := hth' (pullS P.A 1 (overResι V) th)
      obtain ⟨ρ', hρ'⟩ := hg s
      have e₁ : pullM P.A P.L 1 (overResι V) (SecM.ofSec P.A th) = ρ • SecM.ofSec P.A th' := Subtype.ext (funext hρ)
      have e₂ : SecM.ofSec P.A s = ρ' • pullM P.A P.L 1 j (SecM.ofSec P.A th) := Subtype.ext (funext hρ')
      rw [← hj, ← pullM_comp _ hL, e₁, LinearMap.map_smulₛₗ, ← mul_smul] at e₂
      exact ⟨_, fun i => congrArg (fun q => q.1 i) e₂⟩
    convert this using 2 with a a
    · rw [← Category.assoc, hj, el]
    · exact (congrArg (fun q => q.left.appTop.hom (v a)) hj).symm
  have hs' : Ideal.span (Set.range fun a => j.left.appTop.hom (v a)) = ⊤ := by
    have := congrArg (Ideal.map j.left.appTop.hom) hs
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  obtain ⟨th', hth', H'⟩ := coord_over hG P hN hN' ho (pt := fun i => j ≫ pt i)
    (fun i => by rw [← MonObj.comp_pow, h, MonObj.comp_one])
    (ze := Units.map (j.left.appTop.hom : Γ(T.left, ⊤) →* Γ(T'.left, ⊤)) ze) (by rw [← map_pow, hze, map_one])
    (fun a b => by rw [← map_zpow]; exact weilIs_pull hG P.isAb hL j (hp a b)) H
  obtain ⟨ρ, hρ⟩ := hth' (pullS P.A 1 j th)
  obtain ⟨ρ', hρ'⟩ := hg th'
  have e₁ : SecM.ofSec P.A (pullS P.A 1 j th) = ρ • SecM.ofSec P.A th' := Subtype.ext (funext hρ)
  have e₂ : SecM.ofSec P.A th' = ρ' • SecM.ofSec P.A (pullS P.A 1 j th) := Subtype.ext (funext hρ')
  have hu : IsUnit ρ := IsUnit.of_mul_eq_one ρ' (sub_eq_zero.1 (eq_zero_of_smul_gen P H hs' hg
    (by rw [sub_smul, one_smul, mul_smul, ← e₂, ← e₁, sub_self])))
  obtain rfl : lab (fun i => j ≫ pt i) c ^ N' = w := by rw [← hw, MonObj.comp_pow, el]
  have ht' := isThetaFamily_pull ht j
  simp only [MonObj.comp_pow, el] at ht'
  obtain ⟨u, hu'⟩ := H' _ _ ρ e₁ ht' c τ hτ
  refine ⟨hu.unit * u, fun a => ?_⟩
  convert hu' a using 1
  rw [map_mul, ← _root_.mul_assoc, ← map_pow]
  rfl

theorem pow_eq_one_of_weilIs (hG : GlobalFnsSt) (P : PolAV S) {k n : ℕ} {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (H : WeilIs P.A P.L k x y c) (hx : x ^ n = 1) : c ^ n = 1 := by
  have key : ∀ l : ℕ, WeilIs P.A P.L k (x ^ (l + 1)) y (c ^ (l + 1)) := fun l => by
    induction l with
    | zero => rw [zero_add, pow_one, pow_one]; exact H
    | succ l ih => rw [pow_succ, pow_succ c]; exact weilIs_mul_left hG S P k T _ _ _ _ _ ih H
  have := key n
  rw [pow_succ, hx, _root_.one_mul] at this
  have e := CommutatorPairing.weilIs_unique hG P.isAb P.isLB this H
  rwa [pow_succ, mul_eq_right] at e

theorem exists_root (hG : GlobalFnsSt) (P : PolAV S) {g M : ℕ} {pt : Fin (2 * g) → (T ⟶ P.A)}
    (h : ∀ i, pt i ^ M = 1) {ze : Γ(T.left, ⊤)ˣ} (hp : ∀ i j, WeilIs P.A P.L M (pt i) (pt j) (ze ^ stdSymp g i j)) :
    ∃ ze' : Γ(T.left, ⊤)ˣ, ze' ^ M = 1 ∧ (∀ i j, WeilIs P.A P.L M (pt i) (pt j) (ze' ^ stdSymp g i j)) ∧
      ∀ (m r : ℕ) (a c : Fin (2 * g) → ZMod M), ze' ^ thetaCoordExp m r a c = ze ^ thetaCoordExp m r a c := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · exact ⟨1, one_pow _, fun i => i.elim0, fun m r a c => by simp [thetaCoordExp, labelSymp]⟩
  · refine ⟨ze, ?_, hp, fun _ _ _ _ => rfl⟩
    have := hp ⟨0, by omega⟩ ⟨g, by omega⟩
    rw [show stdSymp g ⟨0, by omega⟩ ⟨g, by omega⟩ = 1 by simp [stdSymp, hg], zpow_one] at this
    exact pow_eq_one_of_weilIs hG P this (h _)

end GlobalTheory.TorsCoord

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.VVRank TorsCoord in

theorem torsion_secCoord : Out.Laws → Out.Laws2 → ∀ (g m N' : ℕ), Odd N' → m ^ 2 ∣ N' → ∃ (e : Ix g (N' ^ 2) → Ix g (N' ^ 2) → ℕ) (idx : Ix g (N' ^ 2) → Ix g (N' ^ 2) → Ix g (N' ^ 2)), ∀ (o : Type) [CommRing o] (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R) σ, x ≫ s = spMap β → t.HasTh x v → Ideal.span (Set.range v) = ⊤ → t.Emb m (Over.mk x) σ → ∀ h (y : Sp R ⟶ (Over.mk x ⊗ t.A).left), y = (lift (𝟙 (Over.mk x)) (((Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.lab h) ^ N')).left → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ SecCoord _ σ (spMap φ ≫ y) (fun a => φ (β (b.ζ ^ e a h : oˣ) * v (idx a h))) := by
  intro h₁ h₂ g m N' ho hm
  obtain ⟨r, hr⟩ : m ∣ N' := (dvd_pow_self m two_ne_zero).trans hm
  have hm0 : 0 < m := (Nat.odd_mul.1 (hr ▸ ho)).1.pos
  have hdiv : N' / m = r := by rw [hr, Nat.mul_div_cancel_left _ hm0]
  refine ⟨thetaCoordExp m r, thetaCoordIdx m r, ?_⟩
  rintro o _ J b S s t R _ β x v σ hx ⟨-, -, hv⟩ hsp ⟨th, s₁, α, U, hth, hα, hs₁, hU, hσ⟩ c y hy p
  have := t.ab.comm
  have hG := h₁.globalFns
  let gR : R →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let π : Over.mk x ⟶ baseOver S := Over.homMk x (by simp)
  have el : ∀ a : Ix g (N' ^ 2), π ≫ t.lab a = lab (fun i => π ≫ t.pt i) a := fun a => comp_linComb π _ _
  obtain ⟨V, hV, hv⟩ := hv p
  let w₀ : Over.mk x ⟶ t.A := (π ≫ t.lab c) ^ N'
  obtain ⟨j₀, hj₀⟩ := exists_chart t.isLB (w₀.left p)
  let O : (Sp R).Opens := V ⊓ w₀.left ⁻¹ᵁ t.L.U j₀
  obtain ⟨_, ⟨f, rfl⟩, hf, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ O from ⟨hV, hj₀⟩) O.2
  let φ := algebraMap R (Localization.Away f)
  have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have hopen : IsOpenImmersion (spMap φ) := inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)))
  have hin : ∀ z, spMap φ z ∈ O := fun z => hle (hrange.le ⟨z, rfl⟩)
  refine ⟨Localization.Away f, inferInstance, φ, hopen, hrange.ge hf, ?_⟩
  let j : Over.mk (spMap φ ≫ x) ⟶ Over.mk x := Over.homMk (spMap φ) rfl
  let k₀ : Sp (Localization.Away f) ⟶ V.toScheme := IsOpenImmersion.lift V.ι (spMap φ) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact (hin z).1)
  have hk₀ : k₀ ≫ V.ι = spMap φ := IsOpenImmersion.lift_fac _ _ _
  let k : Over.mk (spMap φ ≫ x) ⟶ overRes (T := Over.mk x) V := Over.homMk k₀ (by
    change k₀ ≫ V.ι ≫ x = spMap φ ≫ x
    rw [← Category.assoc, hk₀])
  have hk : k ≫ overResι V = j := Over.OverMorphism.ext hk₀
  let ζR : Γ((Over.mk x).left, ⊤)ˣ := unitOn (Units.map (β : o →* R) b.ζ)
  have hp₀ : ∀ a c, WeilIs t.A t.L (N' ^ 2 : ℕ) (π ≫ t.pt a) (π ≫ t.pt c) (ζR ^ stdSymp g a c) := fun a c => by
    have := weilIs_pull hG t.ab t.isLB π (t.pairing a c)
    refine (congrArg (WeilIs t.A t.L _ _ _) ((map_zpow _ _ _).trans (congrArg (· ^ _) (Units.ext ?_)))).mp this
    have q := congrArg (fun q => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom b.ζ)) hx
    exact q.trans (congrArg (fun q => q.hom (b.ζ : o))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  obtain ⟨τ, hτ⟩ := WeilCube.exists_gen_of_chart t.isLB (K := Fin 1) (fun _ => (j ≫ w₀).left)
    (fun _ => ((m ^ 2 : ℕ) : ℤ)) (fun _ => j₀) fun z => Set.mem_iInter.2 fun _ => (hin z).2
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap φ ≫ x)).left := inferInstanceAs (IsAffine (Spec _))
  have hpt : ∀ i, (π ≫ t.pt i) ^ (N' ^ 2) = 1 := fun i => by rw [← MonObj.comp_pow, t.torsion, MonObj.comp_one]
  obtain ⟨ze, hze, hp, hexp⟩ := exists_root hG t.pol (pt := fun i => π ≫ t.pt i) hpt hp₀
  obtain ⟨u, hu⟩ := exists_unit_value hG h₂.secBaseChangeAny t.pol (N := m ^ 2) rfl (hr.trans (Nat.mul_comm _ _)) ho
    (pt := fun i => π ≫ t.pt i) hpt hze hp
    (v := fun a => gR (v a)) (by
      have := congrArg (Ideal.map gR) hsp
      rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this) (V := V)
    ((congrArg (IsThetaPtOver t.pol N' · _) (funext fun a => congrArg (overResι V ≫ ·) (el a))).mp hv) (th := th) (t := σ) hth
    ⟨s₁, α, U, hα, hs₁, fun a => (congrArg (SymLift t.A t.L _ _ · _) (congrArg₂ (fun y n => y ^ n ^ 2) (el a) hdiv)).mp (hU a), hσ⟩ k j hk c (j ≫ w₀)
    (congrArg (fun y => j ≫ y ^ N') (el c).symm) τ hτ
  let u' : (Localization.Away f)ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away f))).hom.hom.toMonoidHom u
  have H := secCoord_of_isValueAt (x := spMap φ ≫ x) hτ (t := fun a => pullS t.A _ j (σ a))
    (v := fun a => u' * φ (β (b.ζ ^ thetaCoordExp m r a c : oˣ) * v (thetaCoordIdx m r a c))) fun a => by
      refine (congrArg (IsValueAt t.A t.L _ _ _ τ) (Eq.symm ((map_mul _ _ _).trans ?_))).mp (hu a)
      refine congrArg₂ (· * ·) ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away f))).hom_inv_id_apply _) ?_
      refine (congrArg (fun q => q.hom (β (b.ζ ^ thetaCoordExp m r a c : oˣ) * v (thetaCoordIdx m r a c)))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).trans ?_
      refine congrArg (spMap φ).appTop.hom ((map_mul gR _ _).trans (congrArg (· * _) ?_))
      rw [hexp]
      exact congrArg Units.val ((congrArg unitOn (map_pow (Units.map (β : o →* R)) b.ζ _)).trans (map_pow _ _ _))
  have H' := Coord.scale ((EmbPull.secCoord_pullTo σ _ _ _ _).1 H) u'⁻¹
  simp only [Units.inv_mul_cancel_left] at H'
  refine (congrArg (SecCoord _ σ · _) ?_).mp H'
  rw [hy, ← Over.comp_left, lift_whiskerRight, Category.id_comp]
  exact congrArg CommaMorphism.left (show lift j (j ≫ w₀) = j ≫ lift (𝟙 _) w₀ by rw [comp_lift, Category.comp_id])

end GlobalTheory
end
