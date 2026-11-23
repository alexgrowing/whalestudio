import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleScaleSectionPowEight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombSnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.JetUniq

open GlobalTheory.MBLow.ScaleJet

theorem tr_unique {S : Scheme.{0}} (P : PolAV S) (ρ : LB.Gen (P.L.pull (eSec P.A))) {m : ℕ} (hm : Odd m) {T : Over S}
    {th th' : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)} (hth : ∀ j, th.f j = th'.f j) {x : T ⟶ P.A} {U U' t t'}
    (hU : SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U) (hU' : SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U')
    (H : Tr P ρ m th U t) (H' : Tr P ρ m th' U' t') (j) : t.f j = t'.f j := by
  have hL := P.isLB
  obtain ⟨α, s, hα, hn, h₁, h₂⟩ := H
  obtain ⟨α', s', hα', hn', h₁', h₂'⟩ := H'
  have hc := SymLiftOdd.symLift_unique globalFns_holds P.isAb hL hm.pow _ _ hU hU'
  have ha := gen_unique' hL (fun _ _ _ => rfl) (fst T P.A).left (ptSecT P.A (1 : T ⟶ P.A)).left
    (congrArg (fun q => q.left) (lift_fst _ _ : lift (𝟙 T) (1 : T ⟶ P.A) ≫ _ = _))
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.surj_fst globalFns_holds P.isAb T) hα hα' (fun w I hI => by
      have q := val_corr hI hn (𝟙 _)
      have q' := val_corr hI hn' (𝟙 _)
      rw [val_pull hI, Category.id_comp] at q q'
      exact q.trans q'.symm)
  obtain ⟨p, φ, hφ⟩ := U
  obtain ⟨p', φ', hφ'⟩ := U'
  obtain rfl : p = x := hU.pt_eq
  obtain rfl : p' = p := hU'.pt_eq
  refine sec_ext_val (φ := fun _ : Fin 1 => (snd T P.A).left) hL (fun y J hJ => ?_) j
  refine (twist_val h₂ _ y hJ).trans (Eq.trans ?_ (twist_val h₂' _ y hJ).symm)
  refine congrArg₂ (· * ·) (congrArg Units.val (val_corr hJ hc _)) ?_
  refine (twist_val h₁ _ y hJ).trans (Eq.trans ?_ (twist_val h₁' _ y hJ).symm)
  exact congrArg₂ (· * ·) (congrArg Units.val (ha _ _ y J hJ)) (congrArg (gs _ y _) (hth _))

section Germ

variable {B : Type} [CommRing B] {X : Scheme.{0}}

def germAt (z : Sp B) : B →+* (Sp B).presheaf.stalk z :=
  ((Sp B).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom

theorem germAt_valR (x : Sp B ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (z : Sp B) :
    germAt z (valR x U f) = gs x z U f := by
  rw [valR, dif_pos h, gs_eq x z U (h trivial), germAt, RingHom.comp_apply, Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp B).presheaf (homOfLE h) z trivial _

theorem germAt_ext {a b : B} (h : ∀ z : Sp B, germAt z a = germAt z b) : a = b := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a = (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b :=
    TopCat.Presheaf.section_ext (Sp B).sheaf ⊤ _ _ fun z _ => h z
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1 e

theorem isUnit_valR (x : Sp B ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) : IsUnit (valR x U u.val) := by
  rw [valR, dif_pos h]
  exact (u.isUnit.map _).map _

theorem valR_sec_chart {Y : Scheme.{0}} {L : LB X} (φ : Y ⟶ X) (n : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (n : ℤ)))) (y : Sp B ⟶ Y) {i i' : L.ι}
    (h : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ L.U i) (h' : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ L.U i') :
    valR y (LB.wchart L (fun _ : Fin 1 => φ) fun _ => i') (s.f fun _ => i') =
      valR (y ≫ φ) (L.U i' ⊓ L.U i) (L.g i' i).val ^ n * valR y (LB.wchart L (fun _ : Fin 1 => φ) fun _ => i) (s.f fun _ => i) := by
  have a : ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) fun _ => i := fun z hz => Set.mem_iInter.2 fun _ => h hz
  have a' : ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) fun _ => i' := fun z hz => Set.mem_iInter.2 fun _ => h' hz
  have b : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ (L.U i' ⊓ L.U i) := fun z hz => ⟨h' hz, h hz⟩
  refine germAt_ext fun z => ?_
  have q := sec_trans s y z (a' trivial) (a trivial)
  rw [trF, Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val] at q
  rw [map_mul, map_pow, germAt_valR _ _ b, gs_unit (y ≫ φ) z (L.U i' ⊓ L.U i) (b trivial)]
  exact (germAt_valR _ _ a' _ z).trans (q.trans (congrArg _ (germAt_valR _ _ a _ z).symm))

theorem valR_gen_chart {Y : Scheme.{0}} {L : LB X} (φ : Y ⟶ X) {ρ : LB.Gen (L.pull φ)} (hρ : ρ.IsGen) (y : Sp B ⟶ Y)
    {i i' : L.ι} (h : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ L.U i) (h' : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ L.U i') :
    valR y ((L.pull φ).U fun _ => i') (ρ.s fun _ => i').val =
      valR (y ≫ φ) (L.U i' ⊓ L.U i) (L.g i' i).val * valR y ((L.pull φ).U fun _ => i) (ρ.s fun _ => i).val := by
  have a : ⊤ ≤ y ⁻¹ᵁ (L.pull φ).U fun _ => i := fun z hz => Set.mem_iInter.2 fun _ => h hz
  have a' : ⊤ ≤ y ⁻¹ᵁ (L.pull φ).U fun _ => i' := fun z hz => Set.mem_iInter.2 fun _ => h' hz
  have b : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ (L.U i' ⊓ L.U i) := fun z hz => ⟨h' hz, h hz⟩
  refine germAt_ext fun z => ?_
  have q := congrArg Units.val (gen_trans (φ := fun _ : PUnit => φ) (ε := fun _ => 1) hρ y z (a' trivial) (a trivial))
  rw [trF, Fintype.prod_unique, zpow_one, Units.val_mul] at q
  rw [map_mul, germAt_valR _ _ b, gs_unit (y ≫ φ) z (L.U i' ⊓ L.U i) (b trivial)]
  exact ((germAt_valR _ _ a' _ z).trans (gs_unit y z _ (a' trivial) _)).trans
    (q.trans (congrArg _ ((germAt_valR _ _ a _ z).trans (gs_unit y z _ (a trivial) _)).symm))

end Germ

section Tangent

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

def toProd (A : Over (Sp R)) : A.left ⟶ (baseOver (Sp R) ⊗ A).left :=
  (lift (Over.homMk A.hom (by simp) : A ⟶ baseOver (Sp R)) (𝟙 A)).left

omit [GrpObj A] in
theorem epsLift_eq (v : epsR R ⟶ A) : epsLift v = v.left ≫ toProd A := by
  rw [epsLift, toProd, ← Over.comp_left, comp_lift, Category.comp_id]
  congr 2
  exact Over.OverMorphism.ext (Over.w v).symm

omit [GrpObj A] in
theorem epsLift_snd (v : epsR R ⟶ A) : epsLift v ≫ (snd (baseOver (Sp R)) A).left = v.left := by
  rw [epsLift, ← Over.comp_left, lift_snd]

theorem grpPullback_id : IsGrpPullback A A (𝟙 (Sp R)) (𝟙 A.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 (Sp R)) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul]
  simp [j]

theorem tan_le {v : epsR R ⟶ A} (hv : IsTangent v) {V : A.left.Opens} (hV : ⊤ ≤ eSec A ⁻¹ᵁ V) : ⊤ ≤ v.left ⁻¹ᵁ V := by
  rw [GlobalTheory.ArcLie.le_iff_fst, hv]
  exact hV

theorem fst_valR {v : epsR R ⟶ A} (hv : IsTangent v) {V : A.left.Opens} (hV : ⊤ ≤ eSec A ⁻¹ᵁ V) (f : Γ(A.left, V)) :
    (valR (A := DualNumber R) v.left V f).fst = valR (A := R) (eSec A) V f := by
  have e := GlobalTheory.HolHom.valR_spMap (TrivSqZeroExt.fstHom R R R).toRingHom v.left V (tan_le hv hV) f
  rw [hv] at e
  exact e.symm

theorem snd_valR [IsCommMonObj A] {n : ℕ} {v : Fin n → (epsR R ⟶ A)} (hv : ∀ k, IsTangent (v k)) {c : Fin n → R}
    {w : epsR R ⟶ A} (hc : IsLieComb c v w) {V : A.left.Opens} (hV : ⊤ ≤ eSec A ⁻¹ᵁ V) (f : Γ(A.left, V)) :
    (valR (A := DualNumber R) w.left V f).snd = ∑ k, c k * (valR (A := DualNumber R) (v k).left V f).snd := by
  have e := GlobalTheory.ArcLieCoord.comb_snd grpPullback_id v hv c w hc V (by rw [Category.comp_id]; exact hV) f
  simpa only [Category.comp_id] using e

omit [GrpObj A] in
theorem toProd_snd : toProd A ≫ (snd (baseOver (Sp R)) A).left = 𝟙 A.left := by
  rw [toProd, ← Over.comp_left, lift_snd]; rfl

theorem le_toProd {L : LB A.left} {i : L.ι} (h : ⊤ ≤ eSec A ⁻¹ᵁ L.U i) :
    ⊤ ≤ eSec A ⁻¹ᵁ toProd A ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => (snd (baseOver (Sp R)) A).left) fun _ => i := by
  intro z hz
  refine Set.mem_iInter.2 fun _ => ?_
  have e : (toProd A ≫ (snd (baseOver (Sp R)) A).left) (eSec A z) ∈ L.U i := by
    rw [toProd_snd]; exact h hz
  exact e

end Tangent

local notation "cF" => ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn

theorem thJet_change : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (hp rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → ∀ (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ P.A)) (ϑ ϑ' : I → K) (J J' : I → Fin P.g → K), ThJet ⟨P, hp, rig, hr, th, hth, v, hv⟩ rfl m pt ϑ J → ThJet ⟨P, hp, rig, hr, th', hth', v', hv'⟩ rfl m pt ϑ' J' → (∀ i, ϑ' i = a * ϑ i) ∧ ∃ c : Fin P.g → K, ∀ i j, J' i j = a * ∑ l, M j l * J i l + c j * ϑ i := by
  intro K _ P hp rig hr th hth v hv th' hth' v' hv' a M hs hM m hm _ I pt ϑ ϑ' J J'
  rintro ⟨θ, hθ, U, t, i₀, c, hU, hi, H⟩ ⟨θ', hθ', U', t', i₁, c', hU', hi', H'⟩
  have := P.isAb.comm
  dsimp only at hθ hθ' hU hU' hi hi' H H'
  have k₀ : ⊤ ≤ eSec P.A ⁻¹ᵁ P.L.U i₀ := fun z hz => hi hz
  have k₁ : ⊤ ≤ eSec P.A ⁻¹ᵁ P.L.U i₁ := fun z hz => hi' hz
  have hθ₁ : ∀ j, θ'.f j = (cMul (baseOver (Sp K) ⊗ P.A).hom a θ).f j := fun j => by
    obtain ⟨i, rfl⟩ : ∃ i : P.L.ι, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    have h := LB.wchart_le P.L (fun _ : Fin 1 => (snd (baseOver (Sp K)) P.A).left) (fun _ => i) 0
    exact (hθ' i h).trans ((congrArg _ (hs i)).trans (polAVSectionInverseImage_mulConstant P _ th θ a hθ i h).symm)
  have ht : ∀ i j, (t' i).f j = cF (baseOver (Sp K) ⊗ P.A).hom _ a * (t i).f j := fun i j => by
    obtain ⟨α, s₁, h1, h2, h3, h4⟩ := (hU i).2
    exact tr_unique P rig hm hθ₁ (hU' i).1 (hU i).1 (hU' i).2 (t' := cMul _ a (t i))
      ⟨α, cMul _ a s₁, h1, h2, twist_cMul _ _ _ _ _ _ _ _ _ _ h3, twist_cMul _ _ _ _ _ _ _ _ _ _ h4⟩ j

  let V := LB.wchart P.L (fun _ : Fin 1 => (snd (baseOver (Sp K)) P.A).left) fun _ => i₀
  let D : I → (epsR K ⟶ P.A) → DualNumber K := fun i w => valR (epsLift w) V ((t i).f fun _ => i₀)
  let r : K := valR (𝟙 (Sp K)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (rig.s fun _ => i₀).val
  let G : K := valR (A := K) (eSec P.A) (P.L.U i₁ ⊓ P.L.U i₀) (P.L.g i₁ i₀).val
  let u : Fin P.g → DualNumber K := fun j =>
    valR (A := DualNumber K) (v' j).left (P.L.U i₁ ⊓ P.L.U i₀) (P.L.g i₁ i₀).val ^ (m ^ 2)
  have k₂ : ⊤ ≤ eSec P.A ⁻¹ᵁ (P.L.U i₁ ⊓ P.L.U i₀) := fun z hz => ⟨k₁ hz, k₀ hz⟩
  have hr₀ : r ≠ 0 := (isUnit_valR (𝟙 (Sp K)) ((P.L.pull (eSec P.A)).U fun _ => i₀)
    (fun z hz => Set.mem_iInter.2 fun _ => k₀ hz) _).ne_zero
  have hG₀ : G ≠ 0 := (isUnit_valR (B := K) _ _ k₂ _).ne_zero
  have hu : ∀ j, (u j).fst = G ^ (m ^ 2) := fun j => by
    rw [TrivSqZeroExt.fst_pow, fst_valR (hv'.1 j) k₂]
  have hD : ∀ i l, D i (v l) = TrivSqZeroExt.inl (r ^ (m ^ 2)) *
      (TrivSqZeroExt.inl (ϑ i) + TrivSqZeroExt.inr (J i l + c l * ϑ i)) := H
  have hD' : ∀ i w, D i w = valR (A := DualNumber K) w.left (toProd P.A ⁻¹ᵁ V)
      (((toProd P.A).app V).hom ((t i).f fun _ => i₀)) := fun i w => by
    simp only [D]
    rw [epsLift_eq]
    exact GlobalTheory.HolHom.valR_comp _ _ _ _
  have f₁ : ∀ i j, (D i (v' j)).fst = r ^ (m ^ 2) * ϑ i := fun i j => by
    have e := congrArg TrivSqZeroExt.fst (hD i j)
    rw [hD', fst_valR (hv.1 j) (le_toProd k₀)] at e
    rw [hD', fst_valR (hv'.1 j) (le_toProd k₀), e]
    simp
  have f₂ : ∀ i j, (D i (v' j)).snd = r ^ (m ^ 2) * (∑ l, M j l * J i l + (∑ l, M j l * c l) * ϑ i) := fun i j => by
    rw [hD', snd_valR hv.1 (hM j) (le_toProd k₀), Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hD', hD]
    simp
    ring
  have main : ∀ i j, algebraMap K (DualNumber K) a * (u j * D i (v' j)) = TrivSqZeroExt.inl ((G * r) ^ (m ^ 2)) *
      (TrivSqZeroExt.inl (ϑ' i) + TrivSqZeroExt.inr (J' i j + c' j * ϑ' i)) := fun i j => by
    have e₁ := valR_gen_chart (eSec P.A) hr (𝟙 (Sp K)) hi hi'
    have e₂ := valR_sec_chart (snd (baseOver (Sp K)) P.A).left (m ^ 2) (t i) (epsLift (v' j)) (i := i₀) (i' := i₁)
      (by rw [epsLift_snd]; exact tan_le (hv'.1 j) k₀) (by rw [epsLift_snd]; exact tan_le (hv'.1 j) k₁)
    rw [epsLift_snd] at e₂
    have hx : epsLift (v' j) ≫ (baseOver (Sp K) ⊗ P.A).hom = spMap (algebraMap K (DualNumber K)) := Over.w _
    have e₃ := valR_cMul _ _ _ hx _ a ((t i).f fun _ => i₁)
    have e₄ := H' i j
    rw [e₁] at e₄
    exact (congrArg _ e₂).symm.trans (e₃.symm.trans ((congrArg (valR _ _) (ht i _)).symm.trans e₄))
  have hϑ : ∀ i, ϑ' i = a * ϑ i := fun i => by
    have e := congrArg TrivSqZeroExt.fst (main i ⟨0, hp⟩)
    simp only [TrivSqZeroExt.fst_mul, hu, f₁, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr, add_zero, mul_pow] at e
    refine mul_left_cancel₀ (mul_ne_zero (pow_ne_zero (m ^ 2) hG₀) (pow_ne_zero (m ^ 2) hr₀)) ?_
    linear_combination -e
  refine ⟨hϑ, fun j => a * (∑ l, M j l * c l + (u j).snd / G ^ (m ^ 2) - c' j), fun i j => ?_⟩
  have e := congrArg TrivSqZeroExt.snd (main i j)
  simp only [DualNumber.snd_mul, TrivSqZeroExt.fst_mul, hu, f₁, f₂, hϑ, TrivSqZeroExt.algebraMap_eq_inl,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inr, zero_add, zero_mul,
    add_zero, mul_pow] at e
  have hG₁ := pow_ne_zero (m ^ 2) hG₀
  refine mul_left_cancel₀ (mul_ne_zero hG₁ (pow_ne_zero (m ^ 2) hr₀)) ?_
  linear_combination -e - r ^ (m ^ 2) * a * ϑ i * div_mul_cancel₀ (u j).snd hG₁

end GlobalTheory.MBLow.JetUniq
