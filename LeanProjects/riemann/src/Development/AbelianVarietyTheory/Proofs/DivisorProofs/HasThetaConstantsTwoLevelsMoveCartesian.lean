import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstant

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.ThMove
open GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

section Rig
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_unit_rig (hL : L.IsLB) {ρ ρ' : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (hρ' : ρ'.IsGen) :
    ∃ b : Γ(T.left, ⊤)ˣ, ∀ (m : ℕ) (th : LB.Sec (LPow A L ((1 : ℕ) : ℤ) T)) (x : T ⟶ A) (c : Γ(T.left, ⊤)),
      ThG A L ρ m th x c → ThG A L ρ' m th x (b * c) := by
  obtain ⟨a, ha⟩ := GlobalTheory.UU.BiTrivUniq.exists_unit_ratio (M := L) (φ := fun _ : PUnit => eSec A)
    (ε := fun _ => 1) hL hρ hρ'
  refine ⟨Units.map T.hom.appTop.hom.toMonoidHom a, ?_⟩
  rintro m th x c ⟨hx, t, α, s₁, θ, hα, hcorr, htw, hsym, hact, hval⟩
  obtain ⟨α', d, hα', hcorr', hd⟩ := exists_normalised_unit hL hρ' m ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ)
    (((m ^ 2 : ℕ) : ℤ) - 1) (by push_cast; ring) α hα
  obtain ⟨s₁', hs₁'⟩ := GlobalTheory.ThetaPtExist.exists_isTwistPull hL (mulT A _ m) (snd _ A ^ m) (lift_snd _ _)
    ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α' hα' th
  obtain ⟨t', ht'⟩ := GlobalTheory.ThetaNu.exists_isActOf hL θ s₁'
  have e1 : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => ((m ^ 2 : ℕ) : ℤ)) s₁' r z J =
        (gm (r ≫ (fst T A).left) z ⊤ d).val *
          sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => ((m ^ 2 : ℕ) : ℤ)) s₁ r z J := by
    intro Z r z J hJ
    rw [GlobalTheory.ThetaLin.sval_of_isTwistPull A hs₁' r z hJ, GlobalTheory.ThetaLin.sval_of_isTwistPull A htw r z hJ,
      hd Z r z J hJ, Units.val_mul, _root_.mul_assoc]
  have htr : (translT A θ.pt).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left, GlobalTheory.MulSplit.translT_fst']
  have e2 : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
      GlobalTheory.TorsionFixedAut.secVal t' r z J =
        (gm (r ≫ (fst T A).left) z ⊤ d).val * GlobalTheory.TorsionFixedAut.secVal t r z J := by
    intro Z r z J hJ
    rw [GlobalTheory.TorsionFixedAut.sval_isActOf ht' r z hJ, GlobalTheory.TorsionFixedAut.sval_isActOf hact r z hJ]
    simp only [GlobalTheory.TorsionFixedAut.secVal]
    rw [e1 _ z J hJ, Category.assoc, htr]
    ring
  refine ⟨hx, t', α', s₁', θ, hα', hcorr', hs₁', hsym, ht', ?_⟩
  intro z J hJ
  have c1 := val_corr hJ hcorr (𝟙 T.left)
  have c2 := val_corr hJ hcorr' (𝟙 T.left)
  rw [val_pull hJ] at c1 c2
  have c3 := hd _ (𝟙 T.left ≫ (ptSecT A (1 : T ⟶ A)).left) z J hJ
  rw [c2, c1, Category.assoc, GlobalTheory.ThetaReal.NormMul.ptSec_fst, GlobalTheory.OriginFrame.val_rigT ρ _ _ hJ,
    GlobalTheory.OriginFrame.val_rigT ρ' _ _ hJ, ha _ _ z J hJ] at c3
  have hsv : VVRank.sv A t' (ptSecT A (1 : T ⟶ A)).left z J =
      (gm ((ptSecT A (1 : T ⟶ A)).left ≫ (fst T A).left) z ⊤ d).val * VVRank.sv A t (ptSecT A (1 : T ⟶ A)).left z J :=
    e2 _ z J hJ
  have hb : gs (𝟙 T.left) z ⊤ ((Units.map T.hom.appTop.hom.toMonoidHom a : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) =
      (gm (𝟙 T.left ≫ T.hom) z ⊤ a).val := by
    rw [← gs_unit _ z ⊤ trivial a, ← gs_pull (𝟙 T.left) T.hom z ⊤ trivial a.val]
    rfl
  rw [hsv, hval z J hJ, GlobalTheory.ThetaReal.NormMul.ptSec_fst, GlobalTheory.OriginFrame.val_rigT ρ _ _ hJ,
    GlobalTheory.OriginFrame.val_rigT ρ' _ _ hJ, ha _ _ z J hJ, gs_mul (𝟙 T.left) z ⊤ trivial, hb]
  set g := gm (𝟙 T.left ≫ T.hom) z ⊤ a
  set U := val ρ' (𝟙 T.left ≫ T.hom) z J
  set D := gm (𝟙 T.left) z ⊤ d
  rw [Category.id_comp] at c3
  have key : D * g ^ (((m ^ 2 : ℕ) : ℤ) - 1) = 1 := by
    have c5 : U ^ (((m ^ 2 : ℕ) : ℤ) - 1) = D * (g * U) ^ (((m ^ 2 : ℕ) : ℤ) - 1) := c3
    rw [mul_zpow] at c5
    have c6 : D * g ^ (((m ^ 2 : ℕ) : ℤ) - 1) * U ^ (((m ^ 2 : ℕ) : ℤ) - 1) = 1 * U ^ (((m ^ 2 : ℕ) : ℤ) - 1) := by
      rw [_root_.one_mul, _root_.mul_assoc]
      exact c5.symm
    exact mul_right_cancel c6
  have key2 : D * (g * U) ^ ((m ^ 2 : ℕ) : ℤ) = g * U ^ ((m ^ 2 : ℕ) : ℤ) := by
    rw [mul_zpow, ← _root_.mul_assoc]
    congr 1
    rw [zpow_sub_one, ← _root_.mul_assoc] at key
    calc D * g ^ ((m ^ 2 : ℕ) : ℤ) = D * g ^ ((m ^ 2 : ℕ) : ℤ) * g⁻¹ * g := by group
      _ = g := by rw [key, _root_.one_mul]
  have key3 := congrArg Units.val key2
  simp only [Units.val_mul] at key3
  calc (D : _).val * (gs (𝟙 T.left) z ⊤ c * ((g * U) ^ ((m ^ 2 : ℕ) : ℤ)).val)
      = gs (𝟙 T.left) z ⊤ c * ((D : _).val * ((g * U) ^ ((m ^ 2 : ℕ) : ℤ)).val) := by ring
    _ = gs (𝟙 T.left) z ⊤ c * (g.val * (U ^ ((m ^ 2 : ℕ) : ℤ)).val) := by rw [key3]
    _ = g.val * gs (𝟙 T.left) z ⊤ c * (U ^ ((m ^ 2 : ℕ) : ℤ)).val := by ring

theorem exists_sec_rig (hL : L.IsLB) {ρ ρ' : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (hρ' : ρ'.IsGen)
    {th : LB.Sec (LPow A L ((1 : ℕ) : ℤ) T)} (hg : IsGenSec A L _ th) :
    ∃ th', IsGenSec A L _ th' ∧ ∀ (m : ℕ) (x : T ⟶ A) (c : Γ(T.left, ⊤)),
      ThG A L ρ m th x c → ThG A L ρ' m th' x c := by
  obtain ⟨b, hb⟩ := exists_unit_rig hL hρ hρ' (T := T)
  refine ⟨SecM.toSec A (((b⁻¹ : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) • SecM.ofSec A th), isGenSec_smul hg _, ?_⟩
  intro m x c H
  have h1 := ThG.smul (ρ₁ := ρ') hL (th := th)
    (th' := SecM.toSec A (((b⁻¹ : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) • SecM.ofSec A th))
    (a := ((b⁻¹ : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤))) rfl (hb m th x c H)
  rwa [Units.inv_mul_cancel_left] at h1

theorem hasTh₂_rig (hL : L.IsLB) {ρ ρ' : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (hρ' : ρ'.IsGen)
    {m m' N N' : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} {c : Fin N → K} {c' : Fin N' → K}
    (H : HasTh₂ A L ρ m m' x c c') : HasTh₂ A L ρ' m m' x c c' := by
  obtain ⟨θ, pt, pt', hg, h1, h2⟩ := H
  obtain ⟨θ', hg', hθ'⟩ := exists_sec_rig hL hρ hρ' hg
  exact ⟨θ', pt, pt', hg', ⟨h1.1, fun a => hθ' _ _ _ (h1.2.1 a), h1.2.2⟩, ⟨h2.1, fun a => hθ' _ _ _ (h2.2.1 a), h2.2.2⟩⟩

end Rig

section Pts
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
include hp hτ

theorem torsion_up [IsIso τ] {n : ℕ} (x : T ⟶ A) (hx : x ^ n = 1) :
    ∃ x₀ : T₀ ⟶ G, τ ≫ x₀.left = x.left ≫ φ ∧ x₀ ^ n = 1 := by
  have hw : (inv τ ≫ x.left ≫ φ) ≫ G.hom = T₀.hom := by
    rw [Category.assoc, Category.assoc, hp.1.w, ← Category.assoc x.left, Over.w x, ← hτ, IsIso.inv_hom_id_assoc]
  have h1 : τ ≫ (Over.homMk (inv τ ≫ x.left ≫ φ) hw : T₀ ⟶ G).left = x.left ≫ φ := by simp
  refine ⟨Over.homMk (inv τ ≫ x.left ≫ φ) hw, h1, ?_⟩
  apply Over.OverMorphism.ext
  apply (cancel_epi τ).1
  rw [over_pow hp τ hτ h1 n, hx, over_one hp τ hτ]

theorem torsion_down {n : ℕ} (x₀ : T₀ ⟶ G) (hx : x₀ ^ n = 1) :
    ∃ x : T ⟶ A, τ ≫ x₀.left = x.left ≫ φ ∧ x ^ n = 1 := by
  have hc : (τ ≫ x₀.left) ≫ G.hom = T.hom ≫ f := by rw [Category.assoc, Over.w x₀, hτ]
  have h1 : τ ≫ x₀.left = (Over.homMk (hp.1.lift _ _ hc) (hp.1.lift_snd _ _ hc) : T ⟶ A).left ≫ φ := by simp
  refine ⟨Over.homMk (hp.1.lift _ _ hc) (hp.1.lift_snd _ _ hc), h1, ?_⟩
  apply Over.OverMorphism.ext
  apply hp.1.hom_ext
  · rw [← over_pow hp τ hτ h1 n, hx, over_one hp τ hτ]
  · rw [Over.w, Over.w]

theorem isGenSec_down [IsIso τ] {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)} (hw : w.IsGen)
    (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {th : LB.Sec (LPow A L₁ a T)} {th₀ : LB.Sec (LPow G L₀ a T₀)}
    (h : SecRel hp τ hτ w th th₀) (hg : IsGenSec G L₀ a th₀) : IsGenSec A L₁ a th := by
  have hi : CategoryTheory.inv τ ≫ (Over.mk (T.hom ≫ f)).hom = T₀.hom := by
    simp only [Over.mk_hom]; rw [← hτ, IsIso.inv_hom_id_assoc]
  let β : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk τ hτ
  let β' : T₀ ⟶ Over.mk (T.hom ≫ f) := Over.homMk (CategoryTheory.inv τ) hi
  have hβ : β.left = τ := rfl
  have hβ' : β'.left = CategoryTheory.inv τ := rfl
  have hβι : β ≫ β' = 𝟙 _ := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hβ, hβ', IsIso.hom_inv_id, Over.id_left]
  exact isGenSec_move hp τ hτ hw hL₀ hL₁ (B := Over.mk (T.hom ≫ f)) (𝟙 T.left) β (Category.id_comp τ) h
    (GlobalTheory.ThetaCoord.isGenSec_pullS hL₀ β β' hβι hg)

end Pts

section Lists
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
  {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ₁ : LB.Gen (L₁.pull (eSec A))}
  {K : Type} [Field K] (x : Sp K ⟶ S')

abbrev idT (f : S' ⟶ S) {Z : Scheme.{0}} (x : Z ⟶ S') (x₀ : Z ⟶ S) : (Over.mk x).left ⟶ (Over.mk x₀).left := 𝟙 Z

instance {Z : Scheme.{0}} (x : Z ⟶ S') (x₀ : Z ⟶ S) : IsIso (idT f x x₀) := inferInstanceAs (IsIso (𝟙 Z))

theorem idT_w {Z : Scheme.{0}} {x : Z ⟶ S'} {x₀ : Z ⟶ S} (h : x₀ = x ≫ f) :
    idT f x x₀ ≫ (Over.mk x₀).hom = (Over.mk x).hom ≫ f := by
  subst h
  simp [idT]

theorem thList_up (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m N : ℕ}
    {θ : SecAt A L₁ x} {θ₀ : SecAt G L₀ (x ≫ f)} (hθ : SecRel hp (idT f x (x ≫ f)) (idT_w rfl) w θ θ₀)
    {pt : Fin N → (Over.mk x ⟶ A)} {c : Fin N → K} (H : ThList A L₁ ρ₁ m x θ pt c) :
    ∃ pt₀, ThList G L₀ ρ₀ m (x ≫ f) θ₀ pt₀ c := by
  obtain ⟨hinj, hth, hall⟩ := H
  have hx : ∀ a, ∃ p₀ : Over.mk (x ≫ f) ⟶ G, idT f x (x ≫ f) ≫ p₀.left = (pt a).left ≫ φ ∧ p₀ ^ (m ^ 2) = 1 :=
    fun a => torsion_up hp (idT f x (x ≫ f)) (idT_w rfl) (pt a) (hth a).1
  choose pt₀ hpt₀ hpow using hx
  have e : ∀ a, (pt₀ a).left = (pt a).left ≫ φ := fun a => by simpa [idT] using hpt₀ a
  refine ⟨pt₀, ?_, ?_, ?_⟩
  · intro a b hab
    apply hinj
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext
    · rw [← e a, ← e b, hab]
    · rw [Over.w, Over.w]
  · intro a
    have := ThG.up hp (idT f x (x ≫ f)) (idT_w rfl) hw hL₀ hL₁ hr (hpt₀ a) (hpow a) hθ (hth a)
    simpa [idT] using this
  · intro K' _ _ i p hp2
    obtain ⟨q, hq, hqn⟩ := torsion_down hp (idT f (spMap i ≫ x) (spMap i ≫ x ≫ f))
      (idT_w (Category.assoc _ _ _).symm) p hp2
    obtain ⟨a, ha⟩ := hall K' i q hqn
    refine ⟨a, ?_⟩
    have e1 : p.left = q.left ≫ φ := by simpa [idT] using hq
    rw [e1, ha, e a, Category.assoc]

theorem thList_down (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m N : ℕ}
    {θ : SecAt A L₁ x} {θ₀ : SecAt G L₀ (x ≫ f)} (hθ : SecRel hp (idT f x (x ≫ f)) (idT_w rfl) w θ θ₀)
    {pt₀ : Fin N → (Over.mk (x ≫ f) ⟶ G)} {c : Fin N → K} (H : ThList G L₀ ρ₀ m (x ≫ f) θ₀ pt₀ c) :
    ∃ pt, ThList A L₁ ρ₁ m x θ pt c := by
  obtain ⟨hinj, hth, hall⟩ := H
  have hx : ∀ a, ∃ p : Over.mk x ⟶ A, idT f x (x ≫ f) ≫ (pt₀ a).left = p.left ≫ φ ∧ p ^ (m ^ 2) = 1 :=
    fun a => torsion_down hp (idT f x (x ≫ f)) (idT_w rfl) (pt₀ a) (hth a).1
  choose pt hpt hpow using hx
  have e : ∀ a, (pt₀ a).left = (pt a).left ≫ φ := fun a => by simpa [idT] using hpt a
  refine ⟨pt, ?_, ?_, ?_⟩
  · intro a b hab
    apply hinj
    apply Over.OverMorphism.ext
    rw [e a, e b, hab]
  · intro a
    have := ThG.move hp (idT f x (x ≫ f)) (idT_w rfl) hw hL₀ hL₁ hr (hpt a) (hpow a) hθ (hth a)
    simpa [idT] using this
  · intro K' _ _ i p hp2
    obtain ⟨q, hq, hqn⟩ := torsion_up hp (idT f (spMap i ≫ x) (spMap i ≫ x ≫ f))
      (idT_w (Category.assoc _ _ _).symm) p hp2
    obtain ⟨a, ha⟩ := hall K' i q hqn
    refine ⟨a, ?_⟩
    have e1 : q.left = p.left ≫ φ := by simpa [idT] using hq
    apply hp.1.hom_ext
    · rw [← e1, ha, e a, Category.assoc]
    · simp [Over.w]

end Lists

theorem hasTh₂_move : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (S' : Scheme.{0}) (A : Over S') [GrpObj A] [IsCommMonObj A] (L' : LB A.left) (ρ' : LB.Gen (L'.pull (eSec A))) (f : S' ⟶ S) (φ : A.left ⟶ G.left), L'.IsLB → ρ'.IsGen → IsGrpPullback A G f φ → LBIso L' (L.pull φ) → ∀ (m m' N N' : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S') (c : Fin N → K) (c' : Fin N' → K), HasTh₂ A L' ρ' m m' x c c' ↔ HasTh₂ G L ρ m m' (x ≫ f) c c' := by
  intro S G _ _ L ρ hL hρ S' A _ _ L' ρ' f φ hL' hρ' hp hLi m m' N N' K _ x c c'
  obtain ⟨w, hw⟩ := hLi
  obtain ⟨ρ₁, hρ₁, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL' hρ
  constructor
  · intro H
    obtain ⟨θ, pt, pt', hg, h1, h2⟩ := hasTh₂_rig hL' hρ' hρ₁ H
    obtain ⟨θ₀, hθ⟩ := exists_secRel_up hp (idT f x (x ≫ f)) (idT_w rfl) hw hL hL' θ
    obtain ⟨pt₀, l1⟩ := thList_up hp x hw hL hL' hr hθ h1
    obtain ⟨pt₀', l2⟩ := thList_up hp x hw hL hL' hr hθ h2
    exact ⟨θ₀, pt₀, pt₀', GlobalTheory.ThetaPtUp.isGenSec_up hp (idT f x (x ≫ f)) (idT_w rfl) hw hL hL' hθ hg, l1, l2⟩
  · intro H
    obtain ⟨θ₀, pt₀, pt₀', hg₀, l1, l2⟩ := H
    obtain ⟨θ, hθ⟩ := exists_secRel hp (idT f x (x ≫ f)) (idT_w rfl) hw hL hL' θ₀
    obtain ⟨pt, k1⟩ := thList_down hp x hw hL hL' hr hθ l1
    obtain ⟨pt', k2⟩ := thList_down hp x hw hL hL' hr hθ l2
    exact hasTh₂_rig hL' hρ₁ hρ' ⟨θ, pt, pt', isGenSec_down hp _ (idT_w rfl) hw hL hL' hθ hg₀, k1, k2⟩

end GlobalTheory.UMin.ThMove
end
