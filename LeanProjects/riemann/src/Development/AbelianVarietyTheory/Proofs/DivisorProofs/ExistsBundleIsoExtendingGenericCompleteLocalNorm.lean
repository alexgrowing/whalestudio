import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyPullbackGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompletedPointOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBundleIsoExtendingGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenExtendCompat

open GlobalTheory.GenericExtend

theorem exists_gen_of_compat {X U P : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    [IsDominant j] [QuasiCompact j] (hX : Geo.Tor.IsNormalScheme X) (p : P ⟶ X) [Smooth p]
    [GeometricallyIntegral p] {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {N : LB P} (hN : N.IsLB)
    {eU : U ⟶ pullback p j} (w : eU ≫ pullback.fst p j = j ≫ e) (hπ : eU ≫ pullback.snd p j = 𝟙 U)
    {τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N _ τ)
    {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : N.ι),
      e (j (κ z)) ∈ N.U a → gm (κ ≫ eU) z (pullback.fst p j ⁻¹ᵁ N.U a) (τ a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a)) :
    ∃ σ : ∀ a, Γ(P, N.U a)ˣ, (⟨σ⟩ : LB.Gen N).IsGen ∧ ∀ a, pullU (pullback.fst p j) _ (σ a) = τ a := by
  have := IsNormalScheme.of_pred hX
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  have hJ := (pullback.fst p j).app_injective
  have key : ∀ a, ∀ y ∈ N.U a, Order.coheight y ≤ 1 → y ∉ Set.range (pullback.fst p j) →
      ExtAt (pullback.fst p j) (N.U a) (τ a).val y ∧
        ExtAt (pullback.fst p j) (N.U a) ((τ a)⁻¹).val y := fun a y ha h1 hy ↦ by
    refine extAt_of_coheight_eq_one j p he hN w hπ hτ hρ y
      (le_antisymm (coheight_apply_le_one p h1) (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hy ?_)) a ha
    rw [Scheme.Pullback.range_fst]
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range
      (show p y ⤳ ξ from Order.coheight_eq_zero.1 h0 hξy) hξ
  choose s hs using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).1
  choose s' hs' using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).2
  have hm : ∀ a, s a * s' a = 1 := fun a ↦ hJ _ (by
    change ((pullback.fst p j).app _).hom _ = ((pullback.fst p j).app _).hom _
    rw [map_mul, map_one, hs, hs', Units.mul_inv])
  let σ : ∀ a, Γ(P, N.U a)ˣ := fun a ↦ ⟨s a, s' a, hm a, (mul_comm _ _).trans (hm a)⟩
  have hσ : ∀ a, pullU (pullback.fst p j) _ (σ a) = τ a := fun a ↦ Units.ext (hs a)
  refine ⟨σ, fun a b ↦ Units.map_injective
    (f := ((pullback.fst p j).app (N.U a ⊓ N.U b)).hom.toMonoidHom) (hJ _) ?_, hσ⟩
  change pullU _ _ _ = pullU _ _ _
  refine unit_ext fun q hq ↦ ?_
  have := hτ _ (𝟙 _) q a b hq.1 hq.2
  rw [← hσ, ← hσ, gm_pull _ _ q _ hq.1, gm_pull _ _ q _ hq.2] at this
  rw [gm_pull _ _ q _ hq, gm_pull _ _ q _ hq, map_mul, gm_res _ q _ hq, gm_res _ q _ hq]
  exact this

end GlobalTheory.GenExtendCompat

open GlobalTheory.FormalGeneric GlobalTheory.SectionRingIso in

theorem GlobalTheory.GenericIso.exists_unit_of_genericRel : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j → GlobalTheory.GenericIso.Enough U.toUnifPre U'.toUnifPre hD j → ∀ (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))), GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w → ∀ (B : Type) [CommRing B] [Algebra R B] (g' : Spec (CommRingCat.of B) ⟶ G'.left) (g : Spec (CommRingCat.of B) ⟶ G.left) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), IsAdicComplete (I.map (algebraMap R B)) B → g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) → g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) → ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL' → ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL → (∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left), r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g) → ∃ v : Γ(Spec (CommRingCat.of B), ⊤)ˣ, (∀ (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left), r ≫ pullback.fst G'.hom (jK R) = ρ ≫ g' → ∀ z : Z, Geo.Tor.gw w r z jL (fun _ => jL') = gm ρ z ⊤ v) ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι), r ≫ (fstG I e G').left = ρ ≫ g' → (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) * gm ρ z ⊤ v := by
  intro hL R _ _ I hR D D' A A' G G' _ _ _ _ hG hG' U U' hD j hj hE Φ w hw B _ _ g' g jL jL' hB hg' hg c' c hgg
  haveI := hB
  obtain ⟨v, hv⟩ := exists_isRatio U.toUnifPre U'.toUnifPre hD.w (fun e => (j e).hom.left) g' g jL jL' hD.w_gen
    (fun e => (hj e).2.1) (fun e => (hj e).2.2.1) hg' c' c hgg
  refine ⟨v, fun Z ρ r hr z => ?_, hv⟩
  have hpt := hw.point hL hR hG hG' hE hB hg' hg c' c hgg ρ r hr
  obtain ⟨q₁, e₁, f₁, s₁⟩ : ∃ q₁ : Z ⟶ pullback G.hom (jK R), q₁ = r ≫ Φ.hom.left ∧
      q₁ ≫ pullback.fst G.hom (jK R) = r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R) ∧
      q₁ ≫ pullback.snd G.hom (jK R) = r ≫ pullback.snd G'.hom (jK R) :=
    ⟨_, rfl, Category.assoc _ _ _, (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w Φ.hom))⟩
  have m₂ : pullback.fst G.hom (jK R) (q₁ z) ∈ U.LG.L.U jL :=
    (congrArg (fun q : Z ⟶ _ => q z ∈ U.LG.L.U jL) (f₁.trans hpt)).mpr (c trivial)
  have K : ∀ k : ℕ, 1 ≤ k → ∀ s : U.SecK k, vK s q₁ z jL =
      ((Geo.Tor.gw w r z jL (fun _ => jL') * (gm ρ z ⊤ v)⁻¹) ^ k).val * vK s q₁ z jL := by
    intro k hk s
    obtain ⟨c₀, σ₀, hc₀, h₀⟩ := exists_integral U hk s
    obtain ⟨c₁, σ', σ, hc₁, h₁, hσ⟩ := (hE k hk).1 σ₀
    have val : vl σ (q₁ ≫ pullback.fst G.hom (jK R)) z (fun _ => jL) =
        cst ((r ≫ pullback.snd G'.hom (jK R)) ≫ jK R) z c₁ *
          (cst ((r ≫ pullback.snd G'.hom (jK R)) ≫ jK R) z c₀ * vK s q₁ z jL) := by
      have hm : (q₁ ≫ pullback.fst G.hom (jK R)) z ∈ ch U.LG.L (fun _ => jL) := mem_ch.2 m₂
      have b : (q₁ ≫ pullback.fst G.hom (jK R)) ≫ G.hom = (r ≫ pullback.snd G'.hom (jK R)) ≫ jK R := by
        rw [← s₁, Category.assoc, Category.assoc, pullback.condition]
      refine (congrArg (gs _ z (ch U.LG.L fun _ => jL)) (h₁ _)).trans ((gs_mul _ z _ hm _ _).trans
        (congrArg₂ (· * ·) ((gs_res _ z le_top hm _).trans ((ExpInt.gs_scal _ _ z c₁).trans ?_))
          ((h₀ Z q₁ z jL m₂).trans ?_)))
      · rw [b]
      · rw [s₁]
    have t₁ := hw.2 k hk σ' σ hσ Z r z jL jL' ((congrArg (fun q : Z ⟶ _ => q z ∈ U.LG.L.U jL) f₁).mp m₂)
      ((congrArg (fun q : Z ⟶ _ => q z ∈ U'.LG.L.U jL') hr).mpr (c' trivial))
    have t₂ := hv.vl_eq _ _ _ _ _ _ _ _ hg' c' c hgg σ' σ hσ Z ρ z
    rw [← f₁, hr] at t₁
    rw [← hpt, ← f₁] at t₂
    have key : ∀ {T : Type} [CommRing T] (a b : Tˣ) (d₁ d₀ x y t : T), IsUnit d₁ → IsUnit d₀ →
        d₁ * (d₀ * x) = (a ^ k).val * t → d₁ * (d₀ * y) = (b ^ k).val * t → x = ((a * b⁻¹) ^ k).val * y := by
      intro T _ a b d₁ d₀ x y t u₁ u₀ h₁ h₂
      refine u₀.mul_left_cancel (u₁.mul_left_cancel (h₁.trans ?_))
      rw [mul_left_comm d₀, mul_left_comm d₁, h₂, mul_pow, inv_pow, Units.val_mul, _root_.mul_assoc,
        Units.inv_mul_cancel_left]
    exact key _ _ _ _ _ _ _ (ExpInt.isUnit_cst _ z hc₁) (ExpInt.isUnit_cst _ z hc₀)
      (val.symm.trans t₁) (val.symm.trans t₂)
  exact mul_inv_eq_one.1 (eq_one_of_values hL.ample U.toUnifPre q₁ z jL m₂ _ K)

open GlobalTheory.BundleExt GlobalTheory.GenericExtend in

theorem GlobalTheory.exists_bundleIso_extending_generic_normal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R (maximalIdeal R) e G' ≅ thickObj R (maximalIdeal R) e G), GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j → ∀ (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))), GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w → ∀ ψ : G' ≅ G, IsMonHom ψ.hom → (Over.pullback (jK R)).map ψ.hom = Φ.hom → (∀ e : ℕ, (fstG (maximalIdeal R) e G').left ≫ ψ.hom.left = (j e).hom.left ≫ (fstG (maximalIdeal R) e G).left) → ∃ wL : LB.Iso U'.LG.L (U.LG.L.pull ψ.hom.left), wL.IsGen ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG (maximalIdeal R) e G').left) z jL jL' := by
  have s2 := GlobalTheory.GenericIso.exists_unit_of_genericRel
  intro R _ _ _ hR D D' A A' G G' _ _ _ _ hG hG' U U' hD j hj Φ w hw ψ hψm hψK hψe
  have hR' := hR
  obtain ⟨_, -, _, hRc⟩ := hR'
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hE := hj.enough hL.globalFns U.expand U'.expand
  have := hG'.smooth
  have : GeometricallyIntegral G'.hom := GlobalTheory.geometricallyIntegral_of_isSemiAbelian G'
  have : IsIntegral G'.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G'
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have : IsDominant (jK R) := ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK
  have hX : Geo.Tor.IsNormalScheme (Spec (CommRingCat.of R)) := GlobalTheory.IsNormalScheme.pred _
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : Spec (CommRingCat.of R) ⟶ G'.left, e₀ = eSec G' := ⟨_, rfl⟩
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : Spec (CommRingCat.of R) ⟶ G.left, e₁ = eSec G := ⟨_, rfl⟩
  have he' : e₀ ≫ G'.hom = 𝟙 _ := he₀ ▸ Over.w η[G']
  have he'' : e₁ ≫ G.hom = 𝟙 _ := he₁ ▸ Over.w η[G]
  have hmon : e₀ ≫ ψ.hom.left = e₁ := by
    have := congrArg Over.Hom.left (IsMonHom.one_hom ψ.hom)
    rw [Over.comp_left] at this
    rw [he₀, he₁]
    exact this
  have top : ∀ (W : (Spec (CommRingCat.of R)).Opens), IsLocalRing.closedPoint R ∈ W → ∀ x, x ∈ W :=
    fun W h x => (IsLocalRing.specializes_closedPoint x).mem_open W.isOpen h
  have hF : Φ.hom.left ≫ pullback.fst G.hom (jK R) = (pullback.fst G'.hom (jK R)) ≫ ψ.hom.left := by
    rw [← hψK]
    exact pullback.lift_fst _ _ _
  have hN : (LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).IsLB := LB.isLB_div (LB.isLB_pull U.LG.isLB _) U'.LG.isLB
  have hle : ∀ a : (LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).ι,
      (pullback.fst G'.hom (jK R)) ⁻¹ᵁ (LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).U a ≤
        (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R))).U a.1 ⊓ (U'.LG.L.pull (pullback.fst G'.hom (jK R))).U (fun _ => a.2) := by
    intro a x hx
    refine ⟨mem_pull.2 ?_, mem_pull.2 hx.2⟩
    rw [hF, Scheme.Hom.comp_apply]
    exact mem_pull.1 hx.1
  let τ : ∀ a, Γ(pullback G'.hom (jK R), (pullback.fst G'.hom (jK R)) ⁻¹ᵁ (LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).U a)ˣ :=
    fun a => res (hle a) (w.s (a.1, fun _ => a.2))
  have gτ : ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G'.hom (jK R)) (z : Z) a,
      (pullback.fst G'.hom (jK R)) (r z) ∈ (LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).U a →
      gm r z _ (τ a) = Geo.Tor.gw w r z (a.1 PUnit.unit) (fun _ => a.2) :=
    fun Z r z a h => gm_res r z (hle a) h _
  have hτ : Compat (LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L) (pullback.fst G'.hom (jK R)) τ := by
    intro Z r z a b ha hb
    rw [gτ Z r z a ha, gτ Z r z b hb]
    have ma : (Φ.hom.left ≫ pullback.fst G.hom (jK R)) (r z) ∈ U.LG.L.U (a.1 PUnit.unit) := by
      rw [hF, Scheme.Hom.comp_apply]; exact mem_pull.1 ha.1
    have mb : (Φ.hom.left ≫ pullback.fst G.hom (jK R)) (r z) ∈ U.LG.L.U (b.1 PUnit.unit) := by
      rw [hF, Scheme.Hom.comp_apply]; exact mem_pull.1 hb.1
    rw [(isGen_iff w).1 hw.1 Z r z (a.1 PUnit.unit) (b.1 PUnit.unit) (fun _ => a.2) (fun _ => b.2) ma mb
      (mem_pull.2 ha.2) (mem_pull.2 hb.2)]
    refine congrArg (· * _) ?_
    have e1 := gm_div_g (F := ψ.hom.left) (L := U.LG.L) (L' := U'.LG.L) (r ≫ (pullback.fst G'.hom (jK R))) z (a.1 PUnit.unit)
      (b.1 PUnit.unit) a.2 b.2 (mem_pull.1 ha.1) (mem_pull.1 hb.1) ha.2 hb.2
    have e2 := gm_pull_g U'.LG.L (pullback.fst G'.hom (jK R)) r z (fun _ => a.2) (fun _ => b.2) (mem_pull.2 ha.2) (mem_pull.2 hb.2)
    rw [e2, hF, ← Category.assoc]
    exact e1.symm
  obtain ⟨jL, hjL⟩ := exists_chart U.LG.isLB (e₁ (IsLocalRing.closedPoint R))
  obtain ⟨jL', hjL'⟩ := exists_chart U'.LG.isLB (e₀ (IsLocalRing.closedPoint R))
  have hc : IsAdicComplete ((maximalIdeal R).map (algebraMap R R)) R := by
    rw [show algebraMap R R = RingHom.id R from rfl, Ideal.map_id]; exact hRc
  have hsp : Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 (Spec (CommRingCat.of R)) := by
    rw [show algebraMap R R = RingHom.id R from rfl, CommRingCat.ofHom_id, Spec.map_id]
  obtain ⟨v, hv1, -⟩ := s2 hL R (maximalIdeal R) hR D D' A A' G G' hG hG' U U' hD j hj hE Φ w hw R (e₀)
    (e₁) jL jL' hc (he'.trans hsp.symm) (he''.trans hsp.symm) (fun x _ => top _ hjL' x)
    (fun x _ => top _ hjL x) (fun e Z ρ r hr => by
      rw [← hψe e, ← Category.assoc, hr, Category.assoc, hmon])
  let a₀ : (LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).ι := (fun _ => jL, jL')
  have ha₀ : ∀ x, e₀ x ∈ (LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).U a₀ := fun x =>
    ⟨mem_pull.2 (by rw [← Scheme.Hom.comp_apply, hmon]; exact top (e₁ ⁻¹ᵁ U.LG.L.U jL) hjL x),
      top (e₀ ⁻¹ᵁ U'.LG.L.U jL') hjL' x⟩
  have hle' : ∀ a, e₀ ⁻¹ᵁ (LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).U a ≤
      e₀ ⁻¹ᵁ ((LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).U a ⊓ (LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).U a₀) :=
    fun a x hx => ⟨hx, ha₀ x⟩
  let ρ : ∀ a, Γ(Spec (CommRingCat.of R), e₀ ⁻¹ᵁ (LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).U a)ˣ :=
    fun a => res (hle' a) (pullU (e₀) _ ((LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).g a a₀)) * res le_top v
  let eU : Spec (CommRingCat.of (FractionRing R)) ⟶ pullback G'.hom (jK R) :=
    pullback.lift (jK R ≫ e₀) (𝟙 _) (by rw [Category.assoc, he']; simp)
  have hw0 : eU ≫ (pullback.fst G'.hom (jK R)) = jK R ≫ e₀ := pullback.lift_fst _ _ _
  have hπ : eU ≫ pullback.snd G'.hom (jK R) = 𝟙 _ := pullback.lift_snd _ _ _
  have hq : ∀ y, (pullback.fst G'.hom (jK R)) (eU y) = e₀ (jK R y) := fun y => by
    rw [← Scheme.Hom.comp_apply, hw0, Scheme.Hom.comp_apply]
  obtain ⟨σ, hσg, hσ⟩ := GlobalTheory.GenExtendCompat.exists_gen_of_compat (jK R) hX G'.hom he' hN hw0 hπ hτ (ρ := ρ)
    (fun Z κ z a ha => by
      have h1 : (pullback.fst G'.hom (jK R)) ((κ ≫ eU) z) ∈ (LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).U a := by
        rw [Scheme.Hom.comp_apply, hq]; exact ha
      have h2 : (pullback.fst G'.hom (jK R)) ((κ ≫ eU) z) ∈ (LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).U a₀ := by
        rw [Scheme.Hom.comp_apply, hq]; exact ha₀ _
      rw [hτ Z (κ ≫ eU) z a a₀ h1 h2, gτ Z (κ ≫ eU) z a₀ h2,
        hv1 Z (κ ≫ jK R) (κ ≫ eU) (by rw [Category.assoc, hw0, Category.assoc]) z]
      show _ = gm (κ ≫ jK R) z _ (res (hle' a) (pullU (e₀) _
        ((LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).g a a₀)) * res le_top v)
      rw [map_mul, gm_res_pullU (κ ≫ jK R) (e₀) z (hle' a) ha, gm_res (κ ≫ jK R) z le_top ha,
        Category.assoc, Category.assoc, hw0])
  refine ⟨⟨σ⟩, hσg, fun e Z r z jM jM' jL₁ jL₁' m₁ m₂ m₃ m₄ => ?_⟩
  obtain ⟨t₀⟩ := GlobalTheory.GenericIso.nonempty_pullback_generic (𝟙 G'.left) G'.hom (e₀ (IsLocalRing.closedPoint R))
  have : Nonempty ↥(pullback G'.hom (jK R)) := ⟨(pullback.snd (𝟙 G'.left) (pullback.fst G'.hom (jK R))).base t₀⟩
  have : IsDominant (pullback.fst G'.hom (jK R)) := GlobalTheory.GenericIso.isDominant_of_flat (pullback.fst G'.hom (jK R))
  have : IsSchemeTheoreticallyDominant (pullback.fst G'.hom (jK R)) := .of_isDominant _
  have hsp' : ∀ y : G'.left, G'.hom y ∈ PrimeSpectrum.zeroLocus ((maximalIdeal R : Ideal R) : Set R) →
      ∃ x, (fstG (maximalIdeal R) 0 G').left x = y := fun y hy => by
    rw [← range_thick R (maximalIdeal R) 0] at hy
    exact (Scheme.Pullback.range_fst G'.hom (thick R (maximalIdeal R) 0)).ge hy
  obtain ⟨x, hx⟩ := hsp' ((fstG (maximalIdeal R) e G').left (r z)) (by
    rw [← range_thick R (maximalIdeal R) e]
    exact (Scheme.Pullback.range_fst G'.hom (thick R (maximalIdeal R) e)).le ⟨r z, rfl⟩)
  obtain ⟨j₀, hj₀⟩ := exists_chart U.LG.isLB ((fstG (maximalIdeal R) 0 G).left ((j 0).hom.left x))
  obtain ⟨k₀, hk₀⟩ := exists_chart U'.LG.isLB ((fstG (maximalIdeal R) 0 G').left x)
  obtain ⟨B, _, _, g', g, hB, -, hg', hp, h₁, h₂, h₃, h₄, h₅⟩ :=
    GlobalTheory.CompletedPoint.exists_completed_point (maximalIdeal R) G G' (fun e => (j e).hom) (fun e => (hj e).2.1) x
      _ _ hj₀ hk₀
  obtain ⟨v, hv₁, hv₂⟩ := s2 hL R _ hR D D' A A' G G' hG hG' U U' hD j hj hE Φ w hw B g' g j₀ k₀ hB h₁ h₂ h₃ h₄ h₅
  have hvL : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z), ψ.hom.left (g' (ρ z)) ∈ U.LG.L.U j₀ →
      g' (ρ z) ∈ U'.LG.L.U k₀ →
      Geo.Tor.gw (⟨σ⟩ : LB.Iso U'.LG.L (U.LG.L.pull ψ.hom.left)) (ρ ≫ g') z j₀ k₀ = gm ρ z ⊤ v :=
    fun Z ρ z hj hk => gm_eq_of_dense (pullback.fst G'.hom (jK R)) g' (σ (fun _ => j₀, k₀)) v (fun Z ρ r z hr hz => by
        have hz' : (pullback.fst G'.hom (jK R)) (r z) ∈ (LB.div (U.LG.L.pull ψ.hom.left) U'.LG.L).U (fun _ => j₀, k₀) := by
          rw [← Scheme.Hom.comp_apply, hr]; exact hz
        rw [← hr, ← gm_pull r (pullback.fst G'.hom (jK R)) z _ hz']
        erw [hσ (fun _ => j₀, k₀)]
        rw [gτ Z r z _ hz']
        exact hv₁ Z ρ r hr z) ρ z ⟨mem_pull.2 hj, hk⟩
  exact square_of_flat D.toPre.P.isLB D'.toPre.P.isLB (hψe e) hD.w (U.w_gen e) (U'.w_gen e) hσg (hj e).2.2.1
    g' g j₀ k₀ v h₃ h₄ (h₅ e) hvL (hv₂ e) r z (hx ▸ hp) jM jM' jL₁ jL₁' m₁ m₂ m₃ m₄
