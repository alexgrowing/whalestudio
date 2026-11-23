import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LiftConnectedOfTrivialUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.GSep.TowerFrames

open GlobalTheory.ConstFam GlobalTheory.FrameMove

section General

variable {S : Scheme.{0}} {P : PolAV S} {T : Over S}

theorem torsFrame_vals {rig : LB.Gen (P.L.pull (eSec P.A))} {n : ℕ} {x : T ⟶ P.A} {τ} (H : IsTorsFrame P rig n x τ) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      ∀ (y : T.left) J, Good P.L y J → val τ (𝟙 _) y J ^ ((n : ℤ) ^ 2) = val α x.left y J * rval rig T.hom y J ∧
        val α (T.hom ≫ eSec P.A) y J = rval rig T.hom y J ^ ((n : ℤ) ^ 2) * (rval rig T.hom y J)⁻¹ := by
  obtain ⟨-, -, α, hα, hN, hc⟩ := H
  refine ⟨α, hα, fun y J hJ => ⟨?_, ?_⟩⟩
  · have a : val τ (𝟙 _) y J ^ ((n : ℤ) ^ 2) = val α (𝟙 _ ≫ x.left) y J * rval rig (𝟙 _ ≫ T.hom) y J ^ (1 : ℤ) :=
      (map_zpow _ _ _).symm.trans ((val_corr hJ hc (𝟙 _)).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_rigT _ _ _ hJ))))
    rwa [Category.id_comp, Category.id_comp, zpow_one] at a
  · exact (val_pull hJ α (eSec P.A) T.hom).symm.trans ((val_corr hJ hN T.hom).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (map_zpow _ _ _) (val_inv _ _))))

theorem torsFrame_ratio_pow [IsLocallyNoetherian S] {rig₁ rig₂ : LB.Gen (P.L.pull (eSec P.A))} {n d : ℕ} {x : T ⟶ P.A}
    {τ₁ τ₂} (H₁ : IsTorsFrame P rig₁ n x τ₁) (H₂ : IsTorsFrame P rig₂ (n * d) x τ₂) (y : T.left) (J)
    (hJ : Good P.L y J) : (val τ₂ (𝟙 _) y J * (val τ₁ (𝟙 _) y J)⁻¹) ^ ((n * d) ^ 2) =
      (rval rig₂ T.hom y J * (rval rig₁ T.hom y J)⁻¹) ^ ((n * d) ^ 2) := by
  obtain ⟨α₁, h₁, v₁⟩ := torsFrame_vals H₁
  obtain ⟨α₂, h₂, v₂⟩ := torsFrame_vals H₂
  obtain ⟨β, hβ⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulPull S P d
  have e : (mulA P.A n).left ≫ (mulA P.A d).left = (mulA P.A (n * d)).left := by
    rw [comp_mulA, ← pow_mul]
  obtain ⟨a, ha⟩ := SymLiftOdd.exists_const P.isLB P.A.hom (eSec P.A) (Over.w η[P.A])
    (GlobalTheory.abelianSchemeLaws_all.1.globalFns S P.A P.isAb).2 (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ h₂) (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.powGen_isGen _ _ _ _ h₁ (d ^ 2)) (DVR.pullGen_isGen _ _ _ _ hβ (mulA P.A n).left)))
  have p : ∀ r : T.left ⟶ P.A.left, val (GeneratorPullback.powGen P.L _ _ α₁ (d ^ 2)) r y J = val α₁ r y J ^ (d ^ 2) :=
    fun r => map_pow _ _ _
  have c₁ := ha _ x.left y J hJ
  have c₂ := ha _ (T.hom ≫ eSec P.A) y J hJ
  have e₀ : (T.hom ≫ eSec P.A) ≫ P.A.hom = T.hom := Over.w (1 : T ⟶ P.A)
  rw [val_mul hJ, val_mul hJ, val_inv, val_pull hJ, p] at c₁ c₂
  rw [comp_mulA, H₁.1, Over.w x] at c₁
  rw [e₀, Category.assoc, eSec_mulA] at c₂
  have c := c₁.trans c₂.symm
  have c' : (val α₂ x.left y J)⁻¹ * val α₁ x.left y J ^ (d ^ 2) =
      (val α₂ (T.hom ≫ eSec P.A) y J)⁻¹ * val α₁ (T.hom ≫ eSec P.A) y J ^ (d ^ 2) := by
    rw [← _root_.mul_assoc, ← _root_.mul_assoc] at c
    exact mul_right_cancel c
  obtain ⟨a₁, b₁⟩ := v₁ y J hJ
  obtain ⟨a₂, b₂⟩ := v₂ y J hJ
  apply Additive.ofMul.injective
  replace a₁ := congrArg Additive.ofMul a₁
  replace a₂ := congrArg Additive.ofMul a₂
  replace b₁ := congrArg Additive.ofMul b₁
  replace b₂ := congrArg Additive.ofMul b₂
  replace c' := congrArg Additive.ofMul c'
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow] at a₁ a₂ b₁ b₂ c' ⊢
  linear_combination (norm := module) a₂ - (d ^ 2) • a₁ - c' + b₂ - (d ^ 2) • b₁

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem transport_ext (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) {x' : Y' ⟶ X'} {x : Y ⟶ X}
    {h : Y' ⟶ Y} (hx : x' ≫ F = h ≫ x) {t : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => x) (fun _ => 1))} (ht : t.IsGen)
    {a : LB.Gen (LB.LinComb L' (K := Fin 1) (fun _ => x') (fun _ => 1))}
    (H : ∀ z J J', Good L z J → Good L' z J' → wVal w z J J' x' * val a (𝟙 _) z J' = val t h z J)
    {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (J J') (hJ : Good L z J) (hJ' : Good L' z J') :
    wVal w z J J' (r ≫ x') * val a r z J' = val t (r ≫ h) z J := by
  obtain ⟨b, -, hb⟩ := exists_gen_through (φ' := fun _ : Fin 1 => x') (h := h) hw hL hL' (fun _ => hx) t ht
  have c : LB.Gen.Corr L' _ _ _ _ a b := corr_of_val hL' fun y I' hI' => by
    obtain ⟨I, hI⟩ := exists_good' hL y
    have e := hb _ (𝟙 _) y I I' hI hI'
    rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp, ← H y I I' hI hI'] at e
    exact mul_left_cancel e
  rw [val_corr hJ' c r, hb _ r z J J' hJ hJ', Fin.prod_univ_one, zpow_one]

theorem exists_square_unit {X₁ X₂ X₃ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {L₃ : LB X₃} {F₁ : X₁ ⟶ X} {F₂ : X₂ ⟶ X}
    {G₁ : X₃ ⟶ X₁} {G₂ : X₃ ⟶ X₂} (e : G₁ ≫ F₁ = G₂ ≫ F₂) (hL : L.IsLB) (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) (h₃ : L₃.IsLB)
    {w₁ : LB.Iso L₁ (L.pull F₁)} {w₂ : LB.Iso L₂ (L.pull F₂)} {v₁ : LB.Iso L₃ (L₁.pull G₁)} {v₂ : LB.Iso L₃ (L₂.pull G₂)}
    (g₁ : w₁.IsGen) (g₂ : w₂.IsGen) (k₁ : v₁.IsGen) (k₂ : v₂.IsGen) :
    ∃ u : Γ(X₃, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X₃) (z : Z) J J₁ J₂ J₃, Good L z J → Good L₁ z J₁ → Good L₂ z J₂ →
      Good L₃ z J₃ → wVal w₁ z J J₁ (r ≫ G₁) * wVal v₁ z J₁ J₃ r =
        gm r z ⊤ u * (wVal w₂ z J J₂ (r ≫ G₂) * wVal v₂ z J₂ J₃ r) := by
  rw [isGen_iff] at g₁ g₂ k₁ k₂
  obtain ⟨s₁, T₁⟩ := exists_comp h₁ w₁ v₁ g₁ k₁ hL h₃
  obtain ⟨s₂, T₂⟩ := exists_comp h₂ w₂ v₂ g₂ k₂ hL h₃
  have key : ∀ (H H' : X₃ ⟶ X) (_ : H = H') (s : LB.Iso L₃ (L.pull H)) (s' : LB.Iso L₃ (L.pull H')), PGen s → PGen s' →
      ∃ u : Γ(X₃, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X₃) (y : Z) (j : L.ι) (k : L₃.ι), H (r y) ∈ L.U j → r y ∈ L₃.U k →
        Geo.Tor.gw s r y j k = gm r y ⊤ u * Geo.Tor.gw s' r y j k := by
    rintro H _ rfl s s' hs hs'
    exact TrivDescentCompare.exists_iso_ratio hL h₃ ((isGen_iff _).2 hs) ((isGen_iff _).2 hs')
  obtain ⟨u, hu⟩ := key _ _ e s₁ s₂ (T₁.pgen_comp h₁ g₁ k₁) (T₂.pgen_comp h₂ g₂ k₂)
  refine ⟨u, fun Z r z J J₁ J₂ J₃ hJ hJ₁ hJ₂ hJ₃ => ?_⟩
  have e' : (r ≫ G₂) ≫ F₂ = (r ≫ G₁) ≫ F₁ := by rw [Category.assoc, Category.assoc, e]
  have a := T₁ Z r z _ _ _ (hJ ((r ≫ G₁) ≫ F₁)) (hJ₁ (r ≫ G₁)) (hJ₃ r)
  have b := T₂ Z r z _ _ _ (hJ ((r ≫ G₂) ≫ F₂)) (hJ₂ (r ≫ G₂)) (hJ₃ r)
  have c := hu Z r z _ _ (hJ ((r ≫ G₁) ≫ F₁)) (hJ₃ r)
  refine a.symm.trans (c.trans (congrArg (_ * ·) (Eq.trans ?_ b)))
  rw [e']

end General

theorem exists_root_ratio {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] [IsDomain R₂] [IsNoetherianRing R₂] {P₁ : PolAV (Sp R₁)}
    {P₂ : PolAV (Sp R₂)} {f : Sp R₂ ⟶ Sp R₁} {φ : P₂.A.left ⟶ P₁.A.left} (gp : IsGrpPullback P₂.A P₁.A f φ)
    {w : LB.Iso P₂.L (P₁.L.pull φ)} (hw : w.IsGen) {rig₁ : LB.Gen (P₁.L.pull (eSec P₁.A))} (h₁ : rig₁.IsGen)
    {rig₂ : LB.Gen (P₂.L.pull (eSec P₂.A))} (h₂ : rig₂.IsGen) {n d : ℕ} (hn : 0 < n * d) {ζ : R₂}
    (hζ : IsPrimitiveRoot ζ ((n * d) ^ 2)) : ∃ u : R₂ˣ,
    ∀ (x₁ : baseOver (Sp R₁) ⟶ P₁.A) (x₂ : baseOver (Sp R₂) ⟶ P₂.A) τ₁ τ₂, x₂.left ≫ φ = f ≫ x₁.left →
      IsTorsFrame P₁ rig₁ n x₁ τ₁ → IsTorsFrame P₂ rig₂ (n * d) x₂ τ₂ → ∃ k : ℕ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (baseOver (Sp R₂)).left) (z : Z) J J', Good P₁.L z J → Good P₂.L z J' →
        (wVal w z J J' (r ≫ x₂.left) * val τ₂ r z J').val =
          gs r z ⊤ (fn (u * ζ ^ k)) * (val τ₁ (r ≫ (f : (baseOver (Sp R₂)).left ⟶ (baseOver (Sp R₁)).left)) z J).val := by
  have : IsLocallyNoetherian (Sp R₂) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R₂)))
  obtain ⟨rig', hrig', Hr⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec P₂.A) (φ := fun _ => eSec P₁.A)
    (ε := fun _ => 1) (h := f) hw P₁.isLB P₂.isLB (fun _ => PolBaseChange.eSec_comm gp) rig₁ h₁
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Sp R₂))).left) (z : Z) J J', Good P₁.L z J → Good P₂.L z J' →
      rval rig₁ (r ≫ f) z J = wVal w z J J' (r ≫ eSec P₂.A) * rval rig' r z J' := fun Z r z J J' hJ hJ' =>
    (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))
  obtain ⟨u, hu⟩ := CommutatorPairing.exists_ratio (K := PUnit) (K' := PUnit) (φ := fun _ => eSec P₂.A)
    (φ' := fun _ => eSec P₂.A) (ε := fun _ => 1) (ε' := fun _ => 1) P₂.isLB (fun _ _ _ => rfl) (𝟙 _) (𝟙 _)
    (Category.id_comp _) (fun a => ⟨a, by simp⟩) h₂ hrig'
  let E : Γ((baseOver (Sp R₂)).left, ⊤) ≃+* R₂ := (Scheme.ΓSpecIso (CommRingCat.of R₂)).commRingCatIsoToRingEquiv
  let E' : Γ((baseOver (Sp R₂)).left, ⊤)ˣ →* R₂ˣ := Units.map E.toRingHom.toMonoidHom
  refine ⟨E' u, fun x₁ x₂ τ₁ τ₂ hx H₁ H₂ => ?_⟩
  obtain ⟨τ', hτ', Hτ⟩ := exists_gen_through (φ' := fun _ : Fin 1 => x₂.left)
    (h := (f : (baseOver (Sp R₂)).left ⟶ (baseOver (Sp R₁)).left)) hw P₁.isLB P₂.isLB (fun _ => hx) τ₁ H₁.2.1
  have H' : IsTorsFrame P₂ rig' n x₂ τ' := isTorsFrame_move gp hw hr hx H₁ hτ' fun z J J' hJ hJ' => by
    have := Hτ _ (𝟙 _) z J J' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this
  obtain ⟨v, hv⟩ := CommutatorPairing.exists_ratio P₂.isLB (fun _ _ _ => rfl) (𝟙 _) (𝟙 _)
    (Category.id_comp _) (fun a => ⟨a, by simp⟩) H₂.2.1 hτ'
  have e : v ^ ((n * d) ^ 2) = (show Γ((baseOver (Sp R₂)).left, ⊤)ˣ from u) ^ ((n * d) ^ 2) := unit_ext fun y _ => by
    obtain ⟨J, hJ⟩ := exists_good' P₂.isLB y
    have a := torsFrame_ratio_pow H' H₂ y J hJ
    have b : rval rig₂ (baseOver (Sp R₂)).hom y J = rval rig' (baseOver (Sp R₂)).hom y J * gm (𝟙 _ ≫ 𝟙 _) y ⊤ u :=
      hu _ (𝟙 _) y J hJ
    rw [hv _ _ y J hJ, b, mul_inv_cancel_comm, mul_inv_cancel_comm, Category.id_comp] at a
    rw [map_pow, map_pow]
    exact a.trans (congrArg (fun q => gm q y ⊤ u ^ ((n * d) ^ 2)) (Category.id_comp (𝟙 (Sp R₂))))
  have e' : ((E' v * (E' u)⁻¹ : R₂ˣ) : R₂) ^ ((n * d) ^ 2) = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, ← map_pow, ← map_pow, e, mul_inv_cancel, Units.val_one]
  have : NeZero ((n * d) ^ 2) := ⟨pow_ne_zero _ hn.ne'⟩
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one e'
  have hv' : fn ((E' u : R₂) * ζ ^ k) = v.val := by
    rw [hk, ← Units.val_mul, mul_comm, inv_mul_cancel_right]
    exact E.symm_apply_apply v.val
  refine ⟨k, fun Z r z J J' hJ hJ' => ?_⟩
  rw [hv', Hτ Z r z J J' hJ hJ', hv Z r z J' hJ', Fin.prod_univ_one, zpow_one, Category.comp_id, gs_unit r z ⊤ trivial,
    ← Units.val_mul, ← _root_.mul_assoc, mul_comm]

theorem tfk_hom (V : Type) [CommRing V] [IsDomain V] : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := Spec.map_id _

end GlobalTheory.GSep.TowerFrames

namespace GlobalTheory.GSep

open TowerFrames GlobalTheory.ConstFam GlobalTheory.FrameMove

theorem exists_frPull_tower : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act), ∃ k : X₁.S.Gam → ℕ,
    ∀ (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ)
      (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (X' : Type) [AddCommGroup X'] (t' : X' → V')
      (δ' : I → X' → X') (𝔪₂ : GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X' t' δ') (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left)
      (w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), w.IsGen → 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ →
    ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∃ c : (FractionRing V')ˣ, ∀ b, FrPull w f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b)
      ((c : FractionRing V') * 𝔪₂.yK ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b) := by
  intro I X₁ act 𝔗
  have := X₁.ar.ded
  have := 𝔗.X₂.ar.ded
  have : IsNoetherianRing 𝔗.X₂.o₁ := by
    have := 𝔗.X₂.ar.ft
    exact Algebra.FiniteType.isNoetherianRing ℤ _
  have : IsNoetherianRing 𝔗.X₂.S.R := isNoetherianRing_of_fg 𝔗.X₂.S.fg
  obtain ⟨w₀, hw₀⟩ := 𝔗.lb
  have hζ : IsPrimitiveRoot (⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ : 𝔗.X₂.S.R)
      ((X₁.S.r * X₁.S.N * 𝔗.d) ^ 2) := by
    rw [← 𝔗.lev]
    exact IsPrimitiveRoot.of_map_of_injective (f := 𝔗.X₂.S.R.val) (𝔗.X₂.S.prim.map_of_injective 𝔗.X₂.ar.inj)
      Subtype.val_injective
  have hn : 0 < X₁.S.r * X₁.S.N * 𝔗.d :=
    Nat.mul_pos (Nat.mul_pos X₁.S.r_pos (lt_of_lt_of_le two_pos X₁.S.N_ge)) 𝔗.d_pos
  obtain ⟨u, hu⟩ := exists_root_ratio 𝔗.cart hw₀ X₁.ρ.rig_gen 𝔗.X₂.ρ.rig_gen hn hζ
  choose k hk using fun b => hu _ _ _ _ (𝔗.lam_pt b) (X₁.ρ.fr_tors b) (by
    rw [← 𝔗.lev]; exact 𝔗.X₂.ρ.fr_tors (𝔗.lam b))
  refine ⟨k, ?_⟩
  intro z₁ z₂ _ V _ _ _ ev X _ t δ 𝔪 V' _ _ _ io f _ ev₂ X' _ t' δ' 𝔪₂ ψ w hw _ hy gp hφ x fr hx hfr x₂ fr₂ hx₂ hfr₂
  obtain ⟨a, ha⟩ := exists_square_unit hφ.symm X₁.ρ.P.isLB 𝔪.A.isLB 𝔗.X₂.ρ.P.isLB 𝔪₂.A.isLB 𝔪.wl_gen hw₀ hw 𝔪₂.wl_gen
  obtain ⟨a₀, ha₀⟩ := (GlobalTheory.abelianSchemeLaws_all.1.globalFns _ 𝔪₂.A.A 𝔪₂.A.isAb).2 a.val
  obtain ⟨c₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V'))).inv).2 a₀
  have hc : ∀ (p : TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A) z,
      (gm p.left z ⊤ a).val = GlobalTheory.UT.cst (R := V') (FractionRing V') z c₀ := fun p z => by
    refine (gs_unit _ z ⊤ trivial a).symm.trans ((congrArg (gs p.left z ⊤) ha₀.symm).trans
      ((gs_pull p.left 𝔪₂.A.A.hom z ⊤ trivial _).trans ?_))
    rw [Over.w p, tfk_hom]
    rfl
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    let z : (TFK (R := V') (FractionRing V')).left := (⊥ : PrimeSpectrum (FractionRing V'))
    refine (gm (1 : TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A).left z ⊤ a).ne_zero ((hc 1 z).trans ?_)
    exact (gs_eq (𝟙 _) z ⊤ trivial _).trans (by simp only [map_zero])
  refine ⟨Units.mk0 c₀ hc₀ * Units.map 𝔪₂.yK.toMonoidHom u, fun b z J J' hJ hJ' => ?_⟩
  obtain ⟨J₁, hJ₁⟩ := exists_good' X₁.ρ.P.isLB z
  obtain ⟨J₂, hJ₂⟩ := exists_good' 𝔗.X₂.ρ.P.isLB z
  have hs : spMap 𝔪₂.yK ≫ spMap 𝔗.om = spMap f ≫ spMap 𝔪.yK := by
    rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, hy]
  have hp : (x₂ (𝔗.lam b)).left ≫ ψ =
      (show (TFK (R := V') (FractionRing V')).left ⟶ (TFK (R := V) (FractionRing V)).left from spMap f) ≫ (x b).left := by
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · have e₁ : ((x₂ (𝔗.lam b)).left ≫ ψ) ≫ 𝔪.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt (𝔗.lam b)).left ≫ 𝔗.φ := by
        rw [Category.assoc, ← hφ, ← Category.assoc, hx₂]
        exact Category.assoc _ _ _
      refine e₁.trans ((congrArg (_ ≫ ·) (𝔗.lam_pt b)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) hs).trans ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hx b).symm).trans
          (Category.assoc _ _ _).symm)))))
    · rw [Category.assoc, Category.assoc, gp.1.w, Over.w (x b), ← Category.assoc, Over.w (x₂ _), tfk_hom, tfk_hom]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have q₁ := transport_ext X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.wl_gen (hx b) (X₁.ρ.fr_tors b).2.1 (hfr b).2
    (show (TFK (R := V') (FractionRing V')).left ⟶ (TFK (R := V) (FractionRing V)).left from spMap f) z J₁ J hJ₁ hJ
  have q₂ : wVal 𝔪₂.wl z J₂ J' (x₂ (𝔗.lam b)).left * _ = _ := (hfr₂ (𝔗.lam b)).2 z J₂ J' hJ₂ hJ'
  have q₃ := hk b _ (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK)
    z J₁ J₂ hJ₁ hJ₂
  have q₄ := ha _ (x₂ (𝔗.lam b)).left z J₁ J J₂ J' hJ₁ hJ hJ₂ hJ'
  rw [← hp] at q₁
  have q₅ := (congrArg (fun q => val (X₁.ρ.fr b) q z J₁) hs).trans q₁.symm
  have q₆ := congrArg (fun q => wVal w₀ z J₁ J₂ q) (hx₂ (𝔗.lam b))
  have q₇ := ((congrArg₂ (fun s t => (s * t).val) q₆ q₂).trans q₃).trans
    (congrArg₂ (fun s t => s * Units.val t) (gs_spMap 𝔪₂.yK z _) q₅)
  have m : ∀ s t, GlobalTheory.UT.cst (R := V') (FractionRing V') z (s * t) =
      GlobalTheory.UT.cst (R := V') (FractionRing V') z s * GlobalTheory.UT.cst (R := V') (FractionRing V') z t := fun s t =>
    (congrArg (gs _ z ⊤) (map_mul _ _ _)).trans (gs_mul _ z ⊤ trivial _ _)
  have m' : GlobalTheory.UT.cst (R := V') (FractionRing V') z (((Units.mk0 c₀ hc₀ * Units.map 𝔪₂.yK.toMonoidHom u :
      (FractionRing V')ˣ) : FractionRing V') *
        𝔪₂.yK ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b) = _ * _ :=
    (congrArg _ (by rw [map_mul, map_pow, Units.val_mul, _root_.mul_assoc]; rfl)).trans (m c₀
      (𝔪₂.yK (u * ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b)))
  have key : ∀ {O : Type} [CommRing O] (Wl W W₀ W₂ A F F₂ : Oˣ) (C U : O), Wl * W = A * (W₀ * W₂) → A.val = C →
      (W₀ * (W₂ * F₂)).val = U * (Wl * F).val → W.val * F₂.val = C * U * F.val := by
    intro O _ Wl W W₀ W₂ A F F₂ C U h₁ h₂ h₃
    refine (Units.mul_right_inj Wl).1 ?_
    replace h₁ := congrArg Units.val h₁
    simp only [Units.val_mul] at h₁ h₃
    rw [← h₂]
    linear_combination F₂.val * h₁ + A.val * h₃
  exact (key _ _ _ _ _ _ _ _ _ q₄ (hc _ z) q₇).trans (congrArg (· * _) m'.symm)

end GlobalTheory.GSep
