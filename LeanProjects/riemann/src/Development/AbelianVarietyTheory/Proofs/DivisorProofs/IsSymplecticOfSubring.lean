import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

open GlobalTheory.EighthPower GlobalTheory.CechPic GlobalTheory.MatrixBundle GlobalTheory.ZM

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SympDescent

theorem translFixed_of_pair {S : Scheme.{0}} {h M : ℕ} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left)
    (H : IsSymmetricPair h A P) (ha : Out.RelAmple A (diagPull A P)) (x : 𝟙_ (Over S) ⟶ A) (hx : x ^ M = 1) :
    (M : ℤ) • cls (diagPull A P) (pull_isLB H.2.2.1 _) =
      (M : ℤ) • pull ((toUnit A ≫ x) * 𝟙 A).left (cls (diagPull A P) (pull_isLB H.2.2.1 _)) := by
  haveI := H.1.comm
  have hP := H.2.2.1
  have hb : IsSymBilin (cls P hP) := isSymBilin_of_gen hP (fun T x x' y =>
    (Biadditive.biadditive_of_triv_axes globalFns_holds S A (diagPull A P) H.1 (pull_isLB hP _) ha P hP
      H.2.2.2.1 H.2.2.2.2.1 T x x' y).1) H.2.2.2.2.2
  have d : ∀ f : A ⟶ A, pull f.left (cls (diagPull A P) (pull_isLB hP _)) = pairCls (cls P hP) f f := fun f =>
    (pull_pairCls (cls P hP) f (𝟙 _) (𝟙 _)).trans (by rw [Category.comp_id])
  have z : ∀ y : A ⟶ A, (M : ℤ) • pairCls (cls P hP) (toUnit A ≫ x) y = 0 := fun y => by
    have e := BilinCalc.map_prod_zpow (fun z => pairCls (cls P hP) z y) (fun a b => hb.mul _ a b y)
      (fun _ : Fin 1 => toUnit A ≫ x) fun _ => (M : ℤ)
    simp only [Finset.univ_unique, Finset.prod_const, Finset.card_singleton, pow_one, Finset.sum_const, one_smul,
      zpow_natCast] at e
    rw [← e, ← MonObj.comp_pow, hx, MonObj.comp_one]
    exact one_left (hb.mul _) y
  rw [d, hb.mul, hb.symm _ (𝟙 A) (_ * _), hb.mul, smul_add, smul_add, z, z, zero_add, zero_add]
  rfl

theorem units_map_comp_appTop {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (u : Γ(Z, ⊤)ˣ) :
    Units.map (f ≫ g).appTop.hom.toMonoidHom u =
      Units.map f.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) :=
  Units.ext (by simp [Scheme.Hom.comp_appTop]; rfl)

theorem isSymplectic_of_subring : ∀ (h M : ℕ) (B R : Type) [CommRing B] [CommRing R] (ζ : Bˣ) (R₁ : Subring R) (s₁ : Sp R₁ ⟶ Sp B) (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over (Sp R)) ⟶ A)) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std h M → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), 0 < M → ζ ^ M = 1 → IsUnit (M : R₁) → IsSymmetricPair h A₁ P₁ → IsPrincipal A₁ P₁ → IsLevel A₁ lv₁ → P.IsLB → IsPullbackTriple A P lv A₁ P₁ lv₁ (spMap R₁.subtype) → IsSymplectic ζ (spMap R₁.subtype ≫ s₁) A P lv → IsSymplectic ζ s₁ A₁ P₁ lv₁ := by
  intro h M B R _ _ ζ R₁ s₁ A _ P lv A₁ _ P₁ lv₁ hM hζ hu H₁ H₂ H₃ hPR Hpb Hs
  haveI := H₁.1.comm
  have hP := H₁.2.2.1
  have hD : (diagPull A₁ P₁).IsLB := pull_isLB hP _
  have z₀ : lv₁ 0 = 1 := by
    have e := H₃.1 0 0
    rw [add_zero] at e
    exact left_eq_mul.1 e
  have tors : ∀ a, lv₁ a ^ M = 1 := fun a => by
    have e : ∀ n : ℕ, lv₁ (n • a) = lv₁ a ^ n := fun n => by
      induction n with
      | zero => rw [zero_smul, pow_zero, z₀]
      | succ n ih => rw [succ_nsmul, H₃.1, ih, pow_succ]
    rw [← e, show M • a = 0 by ext i <;> simp, z₀]
  have th : ∀ a (p : (𝟙_ (Over (Sp R₁))).left), ∃ V : (𝟙_ (Over (Sp R₁))).left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp A₁ (diagPull A₁ P₁) M (Out.overRes V), θ.pt = Out.overResι V ≫ lv₁ a := fun a p => by
    let T := Out.overRes (T := 𝟙_ (Over (Sp R₁))) ⊤
    have hT : (Out.thetaLB A₁ (diagPull A₁ P₁) M (Out.overResι ⊤ ≫ lv₁ a)).IsLB := LB.isLB_linComb hD _ _
    obtain ⟨t, ht⟩ := (cls_eq_zero_iff hT).1 (by
      unfold Out.thetaLB at hT ⊢
      rw [cls_linComb hD, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul]
      have e : Out.translPt A₁ (Out.overResι ⊤ ≫ lv₁ a) = snd T A₁ ≫ ((toUnit A₁ ≫ lv₁ a) * 𝟙 A₁) := by
        rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc, Out.translPt, ← Hom.mul_def, ← Category.assoc,
          toUnit_unique (fst _ _ ≫ _) (toUnit _)]
      rw [e, Over.comp_left, pull_comp, ← map_zsmul, ← map_zsmul,
        ← GlobalTheory.SympDescent.translFixed_of_pair A₁ P₁ H₁ H₂.1 (lv₁ a) (tors a), add_neg_cancel])
    exact ⟨⊤, trivial, ⟨_, t, ht⟩, rfl⟩
  obtain ⟨φ, φ₂, pb, s₁', s₂', iso, hl⟩ := Hpb
  have hdi : LBIso (diagPull A P) ((diagPull A₁ P₁).pull φ) := GlobalTheory.SiegelPull.diag_iso ⟨s₁', s₂'⟩ iso
  have hL : (diagPull A P).IsLB := pull_isLB hPR _

  have inj : Function.Injective ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype).appTop.hom := by
    have u₁ : (𝟙_ (Over (Sp R))).hom = 𝟙 _ := rfl
    rw [u₁, Category.id_comp]
    have k : ∀ z, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((spMap R₁.subtype).appTop.hom z) =
        ((Scheme.ΓSpecIso (CommRingCat.of R₁)).hom.hom z : R) := fun z => by
      have e := congrArg (fun q => q.hom z) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom R₁.subtype))
      first
        | exact e
        | (simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Subring.subtype_apply] at e; exact e)
    intro x y hxy
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hxy
    rw [k, k] at h2
    have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (Subtype.val_injective h2)
    simpa using h3
  intro a b
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_weilIs globalFns_holds H₁.1 hD (th a) (th b)
  let X' : Over (Sp R₁) := Over.mk ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype)
  have ex : ∀ a, (toUnit X' ≫ lv₁ a).left = (lv a).left ≫ φ := fun a => by
    rw [Over.comp_left, Over.toUnit_left, hl a]
    exact Category.assoc _ _ _
  have w := (weilIs_grpPullback_of_comm (Sp R₁) (Sp R) A₁ A (spMap R₁.subtype) φ (diagPull A₁ P₁) (diagPull A P)
    hD hL pb hdi (𝟙_ (Over (Sp R))) M (lv a) (lv b) (toUnit X' ≫ lv₁ a) (toUnit X' ≫ lv₁ b) _ (ex a) (ex b)).1 (Hs a b)
  have w' := CommPairing.weilIs_pull globalFns_holds H₁.1 hD (toUnit X') hc
  have q := CommutatorPairing.weilIs_unique globalFns_holds H₁.1 hD w' w
  have u₂ : (𝟙_ (Over (Sp R₁))).hom = 𝟙 _ := rfl
  have hinj : Function.Injective (Units.map (toUnit X').left.appTop.hom.toMonoidHom) := fun u v huv =>
    Units.ext (inj (by
      have := congrArg Units.val huv
      simp only [Units.coe_map, MonoidHom.coe_coe, Over.toUnit_left] at this
      exact this))
  have q₂ : Units.map (toUnit X').left.appTop.hom.toMonoidHom
      (Units.map ((𝟙_ (Over (Sp R₁))).hom ≫ s₁).appTop.hom.toMonoidHom (unitOn (ζ ^ (2 * stdForm a b).val))) =
      Units.map ((𝟙_ (Over (Sp R))).hom ≫ spMap R₁.subtype ≫ s₁).appTop.hom.toMonoidHom
        (unitOn (ζ ^ (2 * stdForm a b).val)) := by
    rw [← GlobalTheory.SympDescent.units_map_comp_appTop, Over.toUnit_left, u₂, Category.id_comp]
    rfl
  rw [← hinj (q.trans q₂.symm)]
  exact hc

end GlobalTheory.SympDescent
