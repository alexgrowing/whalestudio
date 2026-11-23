import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmpleStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsHomogeneousXPowMulAddXPowMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfPullSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompatibleSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBAlg

variable {X Y Z : Scheme.{0}}

theorem gm_tw (A H : LB X) (t : ℤ) (r : Z ⟶ X) (z : Z) (p q : A.ι × H.ι)
    (hm : r z ∈ A.U p.1 ⊓ H.U p.2 ⊓ (A.U q.1 ⊓ H.U q.2)) :
    gm r z ((tw A H t).U p ⊓ (tw A H t).U q) ((tw A H t).g p q) =
      gm r z _ (A.g p.1 q.1) * gm r z _ (H.g p.2 q.2) ^ t := by
  refine (gm_div (AbLaw.pw H (-t)) A r z p q hm).trans ?_
  refine congrArg _ ((congrArg (·⁻¹) (map_zpow _ _ _)).trans ?_)
  rw [zpow_neg, inv_inv]
  rfl

theorem lbIso_of_germs {A B : LB X} (s : ∀ p : B.ι × A.ι, Γ(X, B.U p.1 ⊓ A.U p.2)ˣ)
    (h : ∀ (x : X) (p q : B.ι × A.ι), x ∈ B.U p.1 → x ∈ A.U p.2 → x ∈ B.U q.1 → x ∈ A.U q.2 →
      gm (𝟙 X) x _ (s p) = gm (𝟙 X) x _ (B.g p.1 q.1) * (gm (𝟙 X) x _ (A.g p.2 q.2))⁻¹ * gm (𝟙 X) x _ (s q)) :
    LBIso A B := by
  refine ⟨⟨s⟩, fun p q => unit_ext fun x hx => ?_⟩
  exact (gm_res _ x _ hx _).trans ((h x p q hx.1.1 hx.1.2 hx.2.1 hx.2.2).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div A B (𝟙 X) x p q hx) (gm_res _ x _ hx _))).symm)

theorem germs_of_isGen {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (x : X) (p q : B.ι × A.ι)
    (h₁ : x ∈ B.U p.1) (h₂ : x ∈ A.U p.2) (h₃ : x ∈ B.U q.1) (h₄ : x ∈ A.U q.2) :
    gm (𝟙 X) x (B.U p.1 ⊓ A.U p.2) (w.s p) = gm (𝟙 X) x _ (B.g p.1 q.1) * (gm (𝟙 X) x _ (A.g p.2 q.2))⁻¹ *
      gm (𝟙 X) x (B.U q.1 ⊓ A.U q.2) (w.s q) := by
  have hx : (𝟙 X : X ⟶ X) x ∈ B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2) := ⟨⟨h₁, h₂⟩, h₃, h₄⟩
  exact (gm_res _ x _ hx _).symm.trans ((congrArg (gm (𝟙 X) x _) (hw p q)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div A B (𝟙 X) x p q hx) (gm_res _ x _ hx _))))

theorem lbIso_self {A : LB X} (hA : A.IsLB) : LBIso A A := by
  refine lbIso_of_germs (fun p => A.g p.1 p.2) fun x p q h₁ h₂ h₃ h₄ => ?_
  rw [← gm_cocycle hA (𝟙 X) x h₁ h₂ h₃, ← gm_cocycle hA (𝟙 X) x h₂ h₃ h₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

def chartPullTw {A' H' : LB Y} {A H : LB X} {h : Y ⟶ X} (a : ChartPull A' A h) (b : ChartPull H' H h) (t : ℤ) :
    ChartPull (tw A' H' t) (tw A H t) h where
  idx p := (a.idx p.1, b.idx p.2)
  le p y hy := ⟨a.le _ hy.1, b.le _ hy.2⟩
  g y p q hp hq := by
    refine (gm_tw A' H' t (𝟙 Y) y p q ⟨hp, hq⟩).trans (Eq.trans ?_ (gm_tw A H t h y (a.idx p.1, b.idx p.2)
      (a.idx q.1, b.idx q.2) ⟨⟨a.le _ hp.1, b.le _ hp.2⟩, a.le _ hq.1, b.le _ hq.2⟩).symm)
    rw [a.g y _ _ hp.1 hq.1, b.g y _ _ hp.2 hq.2]

theorem lbIso_tw_congr {A B H : LB X} (hH : H.IsLB) (t : ℤ) (h : LBIso A B) : LBIso (tw A H t) (tw B H t) := by
  obtain ⟨w, hw⟩ := h
  have l₁ : ∀ p : (B.ι × H.ι) × (A.ι × H.ι), (tw B H t).U p.1 ⊓ (tw A H t).U p.2 ≤ B.U p.1.1 ⊓ A.U p.2.1 :=
    fun p x hx => ⟨hx.1.1, hx.2.1⟩
  have l₂ : ∀ p : (B.ι × H.ι) × (A.ι × H.ι), (tw B H t).U p.1 ⊓ (tw A H t).U p.2 ≤ H.U p.1.2 ⊓ H.U p.2.2 :=
    fun p x hx => ⟨hx.1.2, hx.2.2⟩
  have v : ∀ (x : X) (p : (B.ι × H.ι) × (A.ι × H.ι)), x ∈ (tw B H t).U p.1 ⊓ (tw A H t).U p.2 →
      gm (𝟙 X) x _ (res (l₁ p) (w.s (p.1.1, p.2.1)) * res (l₂ p) (H.g p.1.2 p.2.2) ^ t) =
        gm (𝟙 X) x (B.U p.1.1 ⊓ A.U p.2.1) (w.s (p.1.1, p.2.1)) * gm (𝟙 X) x _ (H.g p.1.2 p.2.2) ^ t :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x _ hx _)
      ((map_zpow _ _ _).trans (congrArg (· ^ t) (gm_res _ x _ hx _))))
  refine lbIso_of_germs (fun p => res (l₁ p) (w.s (p.1.1, p.2.1)) * res (l₂ p) (H.g p.1.2 p.2.2) ^ t)
    fun x p q h₁ h₂ h₃ h₄ => ?_
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (gm_tw B H t (𝟙 X) x p.1 q.1 ⟨h₁, h₃⟩) (congrArg (·⁻¹) (gm_tw A H t (𝟙 X) x p.2 q.2 ⟨h₂, h₄⟩)))
    (v x q ⟨h₃, h₄⟩)).symm)
  rw [germs_of_isGen hw x (p.1.1, p.2.1) (q.1.1, q.2.1) h₁.1 h₂.1 h₃.1 h₄.1,
    ← gm_cocycle hH (𝟙 X) x h₁.2 h₂.2 h₃.2, ← gm_cocycle hH (𝟙 X) x h₂.2 h₃.2 h₄.2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem lbIso_tw_tw {A H : LB X} (hA : A.IsLB) (hH : H.IsLB) (t : ℤ) : LBIso A (tw (tw A H t) H (-t)) := by
  have l₁ : ∀ p : ((A.ι × H.ι) × H.ι) × A.ι, (tw (tw A H t) H (-t)).U p.1 ⊓ A.U p.2 ≤ A.U p.1.1.1 ⊓ A.U p.2 :=
    fun p x hx => ⟨hx.1.1.1, hx.2⟩
  have l₂ : ∀ p : ((A.ι × H.ι) × H.ι) × A.ι, (tw (tw A H t) H (-t)).U p.1 ⊓ A.U p.2 ≤ H.U p.1.1.2 ⊓ H.U p.1.2 :=
    fun p x hx => ⟨hx.1.1.2, hx.1.2⟩
  have v : ∀ (x : X) (p : ((A.ι × H.ι) × H.ι) × A.ι), x ∈ (tw (tw A H t) H (-t)).U p.1 ⊓ A.U p.2 →
      gm (𝟙 X) x _ (res (l₁ p) (A.g p.1.1.1 p.2) * res (l₂ p) (H.g p.1.1.2 p.1.2) ^ t) =
        gm (𝟙 X) x _ (A.g p.1.1.1 p.2) * gm (𝟙 X) x _ (H.g p.1.1.2 p.1.2) ^ t :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x _ hx _)
      ((map_zpow _ _ _).trans (congrArg (· ^ t) (gm_res _ x _ hx _))))
  refine lbIso_of_germs (fun p => res (l₁ p) (A.g p.1.1.1 p.2) * res (l₂ p) (H.g p.1.1.2 p.1.2) ^ t)
    fun x p q h₁ h₂ h₃ h₄ => ?_
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (· * _)
    ((gm_tw (tw A H t) H (-t) (𝟙 X) x p.1 q.1 ⟨h₁, h₃⟩).trans (congrArg (· * _)
      (gm_tw A H t (𝟙 X) x p.1.1 q.1.1 ⟨h₁.1, h₃.1⟩)))) (v x q ⟨h₃, h₄⟩)).symm)
  rw [← gm_cocycle hA (𝟙 X) x h₁.1.1 h₂ h₃.1.1, ← gm_cocycle hA (𝟙 X) x h₂ h₃.1.1 h₄,
    ← gm_cocycle hH (𝟙 X) x h₁.1.2 h₁.2 h₃.1.2, ← gm_cocycle hH (𝟙 X) x h₁.2 h₃.1.2 h₃.2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem surjective_thickTrans (V : Type) [CommRing V] (I : Ideal V) (e : ℕ) : Surjective (thickTrans V I e) := by
  refine ⟨fun x => ?_⟩
  have h : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1)))) := by
    rw [range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective _)]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : a ∈ I ^ (e + 1) := (GlobalTheory.SecLifts.mk_mem_ker_factor _ a).1 ha
    have h2 : Ideal.Quotient.mk (I ^ (e + 1 + 1)) a ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      have := Ideal.pow_mem_pow ha' 2
      rw [← pow_mul] at this
      exact Ideal.pow_le_pow_right (by omega) this
    exact x.isPrime.mem_of_pow_mem 2 (by rw [h2]; exact Ideal.zero_mem _)
  exact h

open GlobalTheory.MorAlg in

theorem exists_lineBundle_of_thickenings : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∃ M : LB B.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro V _ _ _ _ Y β hβ B b hB hfl hb hc N v hN
  obtain ⟨H, hH, m, σ, hσ⟩ := id hB
  have hL : ∀ e, (H.pull (b e)).IsLB := fun e => pull_isLB hH _
  obtain ⟨σ₀, w₀, hw₀, c₀⟩ := exists_isPull (b 0) hH σ
  have hva : VeryAmpleBy (Y 0).hom (H.pull (b 0)) σ₀ := by
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull V B.left B.hom H m σ hH hσ _
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1))) _ _ (b 0) (hb 0).w ?_ _ w₀ _ (hL 0) hw₀ c₀
    have e : pullback.lift (b 0) (Y 0).hom (hb 0).w = (hb 0).isoPullback.hom := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
      · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
    rw [e]
    infer_instance
  obtain ⟨t₁, ht₁⟩ := GlobalTheory.T.serre_vanishing_very_ample.1 _ _ _ _ _ _ (hL 0) hva (N 0) (hN 0).1
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.TwistGen.twist_generated _ _ _ _ _ _ (hL 0) hva (N 0) (hN 0).1
  obtain ⟨t, h₁, h₂⟩ : ∃ t, t₁ ≤ t ∧ t₂ ≤ t := ⟨max t₁ t₂, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨n, u, hu⟩ := ht₂ t h₂
  have hT : ∀ e, (tw (N e) (H.pull (b e)) t).IsLB := fun e => isLB_tw (hN e).1 (hL e) t
  have hv' : ∀ e, LBIso (tw (N e) (H.pull (b e)) t) ((tw (N (e + 1)) (H.pull (b (e + 1))) t).pull (β e)) :=
    fun e => LBIso.trans (hT e) (isLB_tw (pull_isLB (hN (e + 1)).1 _) (hL e) t) (pull_isLB (hT (e + 1)) _)
      (lbIso_tw_congr (hL e) t ⟨v e, (hN e).2⟩)
      (LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullSame H _ _ _ (β e) fun _ => (hc e).symm) t) (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self (hT (e + 1))))
  choose v' hv' using hv'
  have hflY : ∀ e, Flat (Y e).hom := fun e => MorphismProperty.of_isPullback (P := @Flat) (hb e) hfl
  choose s hs0 hs using fun j => GlobalTheory.SecLifts.exists_compatible_sections V Y β hβ hflY
    (fun e => tw (N e) (H.pull (b e)) t) v' (fun e => ⟨hT e, hv' e⟩) (ht₁ t h₁) (u j)
  have hcov : ∀ e, ⨆ j, nonzeroLocus (s j e) = ⊤ := by
    intro e
    induction e with
    | zero => simpa only [hs0] using hu
    | succ e ih =>
      have hsurj : Surjective (β e) :=
        MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (surjective_thickTrans V _ e)
      refine top_le_iff.1 fun y _ => ?_
      obtain ⟨x, rfl⟩ := hsurj.surj y
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ j, nonzeroLocus (s j e) by rw [ih]; trivial)
      rw [(GlobalTheory.SecPullIso.section_pull _ _ (β e) _ _ (v' e) (hT (e + 1)) (hT e) (hv' e) (s j (e + 1))).2 _
        (hs j e)] at hj
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨P, p, O, x, hO, hx, heq⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal V n ⊥ (by
    intro F hF d
    rw [Ideal.mem_bot] at hF ⊢
    rw [hF, map_zero])
  choose φ w hφ hw cw using fun e => GlobalTheory.exists_hom_of_veryAmpleBy V P p O n x hO hx (Y e).left
    ((Y e).hom ≫ thick V (IsLocalRing.maximalIdeal V) e) _ (fun j => s j e) (hT e) (hcov e) (by
      intro d F hF h0 k
      obtain ⟨i, hi⟩ := (heq d F hF).1 h0 0
      rw [Ideal.mem_bot, mul_eq_zero] at hi
      rw [hi.resolve_left (pow_ne_zero _ (MvPolynomial.X_ne_zero _)), map_zero])
  have hφc : ∀ e, β e ≫ φ (e + 1) = φ e := fun e => by
    obtain ⟨w₁, hw₁, c₁⟩ := IsPull.comp (s := x) (s' := fun j => s j (e + 1)) (s'' := fun j => s j e)
      hO (hT (e + 1)) (hT e) ⟨w (e + 1), hw (e + 1), cw (e + 1)⟩ ⟨v' e, hv' e, fun j => hs j e⟩
    refine GlobalTheory.MapUniq.hom_eq_of_pull_sections V P p O n x hO hx _ _ (fun j => s j e) _ _ w₁ (w e) (hT e) ?_
      hw₁ (hw e) c₁ (cw e)
    rw [Category.assoc, hφ, hφ, ← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  have hi : ∀ e, (hb e).isoPullback.inv ≫ β e =
      thickMap V (IsLocalRing.maximalIdeal V) e B ≫ (hb (e + 1)).isoPullback.inv := fun e => by
    apply (hb (e + 1)).hom_ext
    · rw [Category.assoc, Category.assoc, hc, IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_inv_fst]
      exact ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm
    · rw [Category.assoc, Category.assoc, (hβ e).w, IsPullback.isoPullback_inv_snd_assoc,
        IsPullback.isoPullback_inv_snd]
      exact (pullback.lift_snd _ _ _).symm
  obtain ⟨g, hg⟩ := exists_hom_of_thickenings V B (Over.mk p) hB ⟨O, hO, n, x, hx⟩ hfl
    (fun e => (hb e).isoPullback.inv ≫ φ e) (fun e => by
      refine (Category.assoc _ _ _).trans ((congrArg _ (hφ e)).trans ?_)
      rw [IsPullback.isoPullback_inv_snd_assoc]
      exact pullback.condition.symm) (fun e => by
      rw [← hφc e]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ (e + 1)) (hi e).symm).trans
        (Category.assoc _ _ _)))
  let g' : B.left ⟶ P := g.left
  have hbg : ∀ e, φ e = b e ≫ g' := fun e => by
    have h : pullback.fst B.hom (thick V (IsLocalRing.maximalIdeal V) e) ≫ g' = (hb e).isoPullback.inv ≫ φ e := hg e
    rw [← (hb e).isoPullback_hom_fst, Category.assoc, h, Iso.hom_inv_id_assoc]
  have hM : (tw (O.pull g') H (-t)).IsLB := isLB_tw (pull_isLB hO _) hH _
  refine ⟨tw (O.pull g') H (-t), hM, fun e => ?_⟩
  have hO' : (tw (O.pull (φ e)) (H.pull (b e)) (-t)).IsLB := isLB_tw (pull_isLB hO _) (hL e) _
  exact LBIso.trans (hN e).1 hO' (pull_isLB hM _)
    (LBIso.trans (hN e).1 (isLB_tw (hT e) (hL e) _) hO' (lbIso_tw_tw (hN e).1 (hL e) t)
      (lbIso_tw_congr (hL e) (-t) ⟨w e, hw e⟩))
    (LBIso.chartPull (chartPullTw (chartPullSame O _ _ _ (b e) fun _ => hbg e) (Geo.Tor.chartPullPull _ _ _ rfl) (-t))
      (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self hM))

end GlobalTheory.LBAlg
