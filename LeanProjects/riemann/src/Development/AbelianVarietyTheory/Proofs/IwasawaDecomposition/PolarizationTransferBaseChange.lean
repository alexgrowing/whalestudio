import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStableOfNoBoundary
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleMapExtendingModelMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferWithFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open scoped CategoryTheory.Obj

namespace GlobalTheory.PolExt

section Det

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.PolFin
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l' : Level H}
  {Xo : Moduli D l} {Xo' : Moduli D l'} {c : Coeff l} {c' : Coeff l'} {O O' : Type} [CommRing O] [CommRing O']
  {β : O →+* c.F} {β' : O' →+* c'.F} {Z : Model Xo c β} {Z' : Model Xo' c' β'} {N : Scheme.{0}} {p' : N ⟶ Z'.X}
  {p : N ⟶ Z.X} {G : Over N} [GrpObj G] [IsCommMonObj G] {ψ' : G.left ⟶ Z'.t.G.left} {ψ : G.left ⟶ Z.t.G.left}
  (h' : IsGrpPullback G Z'.t.G p' ψ') (h : IsGrpPullback G Z.t.G p ψ) {S S' : Type} [CommRing S] [CommRing S']

def pullBasis (M : MChart Z) (x : Sp S ⟶ N) (hx : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U) : Module.Basis (Fin M.n) S (TanM x G) :=
  (lieBasis M (x ≫ p) hx).map (tanEquiv h x).symm

theorem tanPull_pullBasis (M : MChart Z) (φ : S →+* S') {x : Sp S ⟶ N} {x' : Sp S' ⟶ N} (e : spMap φ ≫ x = x')
    (hx : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U) (hx' : ⊤ ≤ (x' ≫ p) ⁻¹ᵁ M.U) (j : Fin M.n) :
    tanPull φ e (pullBasis h M x hx j) = pullBasis h M x' hx' j := by
  have e' : spMap φ ≫ x ≫ p = x' ≫ p := by rw [← Category.assoc, e]
  apply (tanEquiv h x').injective
  rw [← tanPull_tanEquiv h φ e e']
  simp only [pullBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  exact tanPull_lieBasis M φ e' hx hx' j

theorem pullBasis_toMatrix (M M₁ : MChart Z) (x : Sp S ⟶ N) (hx : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U)
    (hx₁ : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M₁.U) : (pullBasis h M x hx).toMatrix (pullBasis h M₁ x hx₁) =
      (lieBasis M (x ≫ p) hx).toMatrix (lieBasis M₁ (x ≫ p) hx₁) := by
  ext i j
  simp [pullBasis, Module.Basis.toMatrix_apply]

def twoDet (M : MChart Z) (M' : MChart Z') (ha : IsAffineOpen (p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)) :
    Γ(N, p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)ˣ :=
  (isUnit_rdet_toMatrix (pullBasis h M (tau ha) (le_preimage_map p inf_le_left (tau_le _ le_rfl)))
    (pullBasis h' M' (tau ha) (le_preimage_map p' inf_le_right (tau_le _ le_rfl)))).unit

theorem ev_twoDet (M : MChart Z) (M' : MChart Z') (ha : IsAffineOpen (p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)) (x : Sp S ⟶ N)
    (h₀ : ⊤ ≤ (x ≫ p) ⁻¹ᵁ M.U) (h₁ : ⊤ ≤ (x ≫ p') ⁻¹ᵁ M'.U) (hh : ⊤ ≤ x ⁻¹ᵁ (p ⁻¹ᵁ M.U ⊓ p' ⁻¹ᵁ M'.U)) :
    ev x _ hh (twoDet h' h M M' ha).val = rdet ((pullBasis h M x h₀).toMatrix (pullBasis h' M' x h₁)) := by
  have e : spMap (ev x _ hh) ≫ tau ha = x := spMap_ev x _ hh
  refine (map_rdet _ _).trans (congrArg rdet ?_)
  ext i j
  have h1 := (pullBasis h M (tau ha) (le_preimage_map p inf_le_left (tau_le _ le_rfl))).sum_toMatrix_smul_self
    (pullBasis h' M' (tau ha) (le_preimage_map p' inf_le_right (tau_le _ le_rfl))) j
  have h2 := congrArg (tanPull (G := G) _ e) h1
  rw [map_sum, tanPull_pullBasis h' M' _ e _ h₁] at h2
  simp only [map_smulₛₗ, tanPull_pullBasis h M _ e _ h₀] at h2
  rw [Module.Basis.toMatrix_apply, ← h2, Module.Basis.repr_sum_self]
  rfl

include h' h in

theorem lbIso_detLie_pull (ha : ∀ (U : Z.X.Opens) (U' : Z'.X.Opens), IsAffineOpen U → IsAffineOpen U' →
    IsAffineOpen (p ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ U')) : LBIso ((detLie Z').pull p') ((detLie Z).pull p) := by
  have le : ∀ J : ((detLie Z).pull p).ι, ((detLie Z).pull p).U J ≤ p ⁻¹ᵁ (J PUnit.unit).U := fun J =>
    LB.wchart_le (detLie Z) (fun _ : PUnit => p) J PUnit.unit
  have le' : ∀ J : ((detLie Z').pull p').ι, ((detLie Z').pull p').U J ≤ p' ⁻¹ᵁ (J PUnit.unit).U := fun J =>
    LB.wchart_le (detLie Z') (fun _ : PUnit => p') J PUnit.unit
  refine ⟨⟨fun a => res (inf_le_inf (le a.1) (le' a.2))
    (twoDet h' h (a.1 PUnit.unit) (a.2 PUnit.unit) (ha _ _ (MChart.hU _) (MChart.hU _)))⟩, fun a b => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z).pull p).U a.1 := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z).pull p).U b.1 := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z').pull p').U a.2 := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ ((detLie Z').pull p').U b.2 := le_preimage_mono inf_le_right hq
  have hp0 := le_preimage_map p (le a.1) hp1
  have hq0 := le_preimage_map p (le b.1) hq1
  have hp3 := le_preimage_map p' (le' a.2) hp2
  have hq3 := le_preimage_map p' (le' b.2) hq2
  have hp4 := le_preimage_mono (inf_le_inf (le a.1) (le' a.2)) hp
  have hq4 := le_preimage_mono (inf_le_inf (le b.1) (le' b.2)) hq
  have g := ev_pull_g (detLie Z) p z a.1 b.1 (le_preimage_inf hp1 hq1) (le_preimage_inf hp0 hq0)
  have g' := ev_pull_g (detLie Z') p' z a.2 b.2 (le_preimage_inf hp2 hq2) (le_preimage_inf hp3 hq3)
  refine (map_mul (ev z _ hz) _ _).trans (Eq.trans ?_ (map_mul (ev z _ hz) _ _).symm)
  refine (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans ((ev_res z _ hp hp4 _).trans
    (ev_twoDet h' h _ _ _ z hp0 hp3 hp4)))
    ((ev_res z _ hz _ _).trans (g'.trans (ev_detChg _ _ _ hp3 hq3 _)))).trans (Eq.trans ?_
    (congrArg₂ (· * ·) ((ev_res z _ hz _ _).trans (g.trans (ev_detChg _ _ _ hp0 hq0 _)))
      ((ev_res z _ hz hq _).trans ((ev_res z _ hq hq4 _).trans (ev_twoDet h' h _ _ _ z hq0 hq3 hq4)))).symm)
  exact (congrArg (_ * rdet ·) (pullBasis_toMatrix h' _ _ z hp3 hq3).symm).trans ((rdet_toMatrix_mul _ _ _).trans
    ((congrArg (rdet · * _) (pullBasis_toMatrix h _ _ z hp0 hq0).symm).trans (rdet_toMatrix_mul _ _ _)).symm)

end Det

theorem isAffineOpen_snd_inf_fst {X Y T : Scheme.{0}} [IsAffine T] (f : X ⟶ T) (g : Y ⟶ T) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (pullback.snd f g ⁻¹ᵁ V ⊓ pullback.fst f g ⁻¹ᵁ U) := by
  let m : pullback (hU.fromSpec ≫ f) (hV.fromSpec ≫ g) ⟶ pullback f g :=
    pullback.map _ _ _ _ hU.fromSpec hV.fromSpec (𝟙 _) (by simp) (by simp)
  have e : m.opensRange = pullback.snd f g ⁻¹ᵁ V ⊓ pullback.fst f g ⁻¹ᵁ U := by
    apply Opens.ext
    rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_map, hU.range_fromSpec, hV.range_fromSpec, Set.inter_comm]
    rfl
  exact e ▸ isAffineOpen_opensRange m

theorem lbIso_pull_of_traits {N U X₁ X₂ : Scheme.{0}} (u : U ⟶ N) (p₁ : N ⟶ X₁) (p₂ : N ⟶ X₂) (D₁ : EffCartierData X₁)
    (D₂ : EffCartierData X₂) (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N) [IsLocallyNoetherian N] [IsPreimmersion u]
    [Flat u] [IsSchemeTheoreticallyDominant u] [QuasiCompact u] [Flat (u ≫ p₁)]
    (hz : ∀ (K : Type) [Field K], (Sp K ⟶ U) → CharZero K)
    (ht : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ N)
      (y : Sp (FractionRing W) ⟶ U), jK W ≫ χ = y ≫ u →
      idlAlong D₁.idealSheaf (χ ≫ p₁) = idlAlong D₂.idealSheaf (χ ≫ p₂)) :
    LBIso (D₁.lb.pull p₁) (D₂.lb.pull p₂) := by
  have lift : ∀ (x : N) (K : Type) [Field K] (g : N.presheaf.stalk x →+* K), Function.Injective g →
      ∃ y : Sp K ⟶ U, y ≫ u = Spec.map (CommRingCat.ofHom g) ≫ N.fromSpecStalk x := by
    intro x K _ g hg
    have := (hN x).1
    refine GlobalTheory.HomExt.exists_lift_of_range_subset u _ ?_
    rintro _ ⟨t, rfl⟩
    obtain ⟨ξ, hξ, hs⟩ := GlobalTheory.exists_mem_genericPoints_specializes x
    have hξ' := GlobalTheory.genericPoints_subset_range_of_isDominant u hξ
    obtain ⟨q, rfl⟩ : ξ ∈ Set.range (N.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]; exact hs
    have ht : Spec.map (CommRingCat.ofHom g) t ⤳ q := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
      change Ideal.comap g t.asIdeal ≤ q.asIdeal
      rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime, Ideal.comap_bot_of_injective _ hg]
      exact bot_le
    have h2 := ht.map (N.fromSpecStalk x).continuous
    have h3 := (hξ : Maximal IsIrreducible _).2 isIrreducible_singleton.closure (specializes_iff_closure_subset.1 h2)
    rw [Scheme.Hom.comp_apply, (h2.antisymm (specializes_iff_closure_subset.2 h3)).eq]
    exact hξ'
  have k₁ : D₁.KeepsRegular p₁ := by
    intro i V hV
    have := D₁.keepsRegular_of_flat (u ≫ p₁) i (u ⁻¹ᵁ V) (fun y hy => hV hy)
    refine mem_nonZeroDivisors_iff_right.2 fun a ha => u.app_injective V ?_
    rw [map_zero]
    refine mem_nonZeroDivisors_iff_right.1 this _ ?_
    have e := congrArg (u.app V).hom ha
    rw [map_mul, map_zero, Cartier.app_resG] at e
    exact e
  have hI : (D₁.pull p₁ k₁).idealSheaf = D₂.idealSheaf.comap p₂ := by
    refine GlobalTheory.Vanishing.eq_comap_of_stalk fun x => ?_
    obtain ⟨hd, hn⟩ := hN x
    obtain ⟨i, hi⟩ := D₂.exists_mem (p₂ x)
    obtain ⟨i', hi'⟩ := D₁.exists_mem (p₁ x)
    have : CharZero (N.presheaf.stalk x) := by
      obtain ⟨y, -⟩ := lift x _ _ (IsFractionRing.injective _ (FractionRing (N.presheaf.stalk x)))
      have := hz _ y
      exact ⟨fun p q e => Nat.cast_injective (R := FractionRing (N.presheaf.stalk x)) (by
        simpa using congrArg (algebraMap _ (FractionRing (N.presheaf.stalk x))) e)⟩
    have e2 : ∀ {X : Scheme.{0}} (π : N ⟶ X) {W : Type} [CommRing W] (g : N.presheaf.stalk x →+* W),
        Spec.map (CommRingCat.ofHom (g.comp (π.stalkMap x).hom)) ≫ X.fromSpecStalk (π x) =
        (Spec.map (CommRingCat.ofHom g) ≫ N.fromSpecStalk x) ≫ π := fun π W _ g => by
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, CommRingCat.ofHom_comp, Spec.map_comp,
        Category.assoc]
      rfl
    have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W →
        ∀ g : N.presheaf.stalk x →+* W, Function.Injective g →
          ((FinalTheorems.stalkId D₁.idealSheaf (p₁ x)).map (p₁.stalkMap x).hom).map g =
          ((FinalTheorems.stalkId D₂.idealSheaf (p₂ x)).map (p₂.stalkMap x).hom).map g := by
      intro W _ _ _ hW g hg
      obtain ⟨y, hy⟩ := lift x _ ((algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W _).comp hg)
      rw [Ideal.map_map, Ideal.map_map, ← PolDiv.idlAlong_fromSpecStalk, ← PolDiv.idlAlong_fromSpecStalk, e2, e2]
      refine ht W hW _ y ?_
      rw [hy, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rw [D₂.stalkId_idealSheaf i _ hi, Ideal.map_span, Set.image_singleton] at key ⊢
    rw [D₁.stalkId_idealSheaf i' _ hi', Ideal.map_span, Set.image_singleton, ← EffCartierData.germ_app] at key
    rw [(D₁.pull p₁ k₁).stalkId_idealSheaf i' _ hi']
    exact PolDiv.span_eq_of_traits (nonZeroDivisors.ne_zero (Cartier.isRegularFn_iff_germ.1 (k₁ i') x hi')) key
  have k₂ : D₂.KeepsRegular p₂ := (D₂.keepsRegular_iff_effCartier p₂).2 (hI ▸ (D₁.pull p₁ k₁).effCartier_idealSheaf)
  exact ((D₁.lbIso_pull p₁ k₁).symm.trans (pull_isLB D₁.isLB_lb _) (D₁.pull p₁ k₁).isLB_lb (D₂.pull p₂ k₂).isLB_lb
    (EffCartierData.lbIso_of_idealSheaf_eq _ _ (hI.trans (D₂.idealSheaf_pull p₂ k₂).symm))).trans
    (pull_isLB D₁.isLB_lb _) (D₂.pull p₂ k₂).isLB_lb (pull_isLB D₂.isLB_lb _) (D₂.lbIso_pull p₂ k₂)

theorem lbIso_pull_tens {N X X' : Scheme.{0}} {p' : N ⟶ X'} {p : N ⟶ X} {A' B' : LB X'} {A B : LB X} (hA' : A'.IsLB)
    (hB' : B'.IsLB) (hA : A.IsLB) (hB : B.IsLB) (m : ℕ) (a : LBIso (A'.pull p') (A.pull p))
    (b : LBIso (B'.pull p') (B.pull p)) :
    LBIso ((CechPic.tens (lbPow (CechPic.dual A') m) (CechPic.dual B')).pull p')
      ((CechPic.tens (lbPow (CechPic.dual A) m) (CechPic.dual B)).pull p) := by
  have key : ∀ {Y : Scheme.{0}} (q : N ⟶ Y) {L M : LB Y} (hL : L.IsLB) (hM : M.IsLB),
      CechPic.cls _ (pull_isLB (CechPic.isLB_tens (isLB_lbPow (CechPic.isLB_dual hL) m) (CechPic.isLB_dual hM)) q) =
        m • -CechPic.cls _ (pull_isLB hL q) + -CechPic.cls _ (pull_isLB hM q) := fun q L M hL hM => by
    rw [CechPic.cls_pull (CechPic.isLB_tens (isLB_lbPow (CechPic.isLB_dual hL) m) (CechPic.isLB_dual hM)),
      CechPic.cls_tens (isLB_lbPow (CechPic.isLB_dual hL) m) (CechPic.isLB_dual hM),
      CechPic.cls_lbPow (CechPic.isLB_dual hL), CechPic.cls_dual hL, CechPic.cls_dual hM, map_add, map_nsmul, map_neg,
      map_neg, CechPic.cls_pull hL, CechPic.cls_pull hM]
  refine (CechPic.cls_eq_iff _ _).1 ((key p' hA' hB').trans (Eq.trans ?_ (key p hA hB).symm))
  rw [(CechPic.cls_eq_iff (pull_isLB hA' p') (pull_isLB hA p)).2 a,
    (CechPic.cls_eq_iff (pull_isLB hB' p') (pull_isLB hB p)).2 b]

theorem exists_hom_of_isPol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F)
    (β' : O' →+* c'.F) (Z : Model Xo c β) (Z' : Model Xo' c' β') (BD : EffCartierData Z.X) (BD' : EffCartierData Z'.X)
    (φ : InvFun (𝓞 E)) (m : ℕ) (b : O →+* O') (σ : 𝓞 E ≃+* 𝓞 E) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : TwMap σ Z'.oF.t Z.oF.t r), IsDedFrac β → IsDedFrac β' → Algebra.FiniteType ℤ O' → IsTwInv H φ → σ H.w0 = H.w0 →
    IsPol φ m Z BD → IsPol φ m Z' BD' → r ≫ Z.j ≫ Z.s = Z'.j ≫ Z'.s ≫ spMap b →
    ∃ π : Z'.X ⟶ Z.X, π ≫ Z.s = Z'.s ≫ spMap b ∧ Z'.j ≫ π = r ≫ Z.j := by
  intro E _ _ _ H D l l' Xo Xo' c c' O O' _ _ β β' Z Z' BD BD' φ m b σ r ν hβ hβ' hO htw hσ hP hP' hr
  obtain ⟨-, h1, h2, h3, h4⟩ := (ofModel Z').arith_and_proOpen hβ' hO
  have h1 : IsPreimmersion Z'.j := h1
  have h2 : Flat Z'.j := h2
  have h3 : IsDominant Z'.j := h3
  have h4 : QuasiCompact Z'.j := h4
  obtain ⟨⟨_, _⟩, _, -⟩ := id hβ'
  have := Z'.flat
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z'.proj
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
  have : IsLocallyNoetherian Z'.X := LocallyOfFiniteType.isLocallyNoetherian Z'.s
  have := GlobalTheory.IsNormalScheme.of_pred Z'.normal
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks Z'.j
  have : GlobalTheory.IsNormalScheme (Xo'.XF c') := GlobalTheory.IsNormalScheme.of_isIso_stalkMap Z'.j
  have : IsLocallyNoetherian (Xo'.XF c') := AmpUniq.isLocallyNoetherian_of_isPreimmersion Z'.j
  let s₁ := Z'.s ≫ spMap b
  have w : Z'.j ≫ s₁ = (r ≫ Z.j) ≫ Z.s := by rw [Category.assoc, hr]
  let f : Xo'.XF c' ⟶ pullback s₁ Z.s := pullback.lift Z'.j (r ≫ Z.j) w
  have hf₁ : f ≫ pullback.fst s₁ Z.s = Z'.j := pullback.lift_fst _ _ _
  have hf₂ : f ≫ pullback.snd s₁ Z.s = r ≫ Z.j := pullback.lift_snd _ _ _
  have : IsPreimmersion (f ≫ pullback.fst s₁ Z.s) := hf₁ ▸ inferInstance
  have : QuasiCompact (f ≫ pullback.fst s₁ Z.s) := hf₁ ▸ inferInstance
  have : IsPreimmersion f := AmpUniq.isPreimmersion_of_comp f (pullback.fst s₁ Z.s)
  have : QuasiCompact f := .of_comp f (pullback.fst s₁ Z.s)
  have : Flat (f ≫ pullback.fst s₁ Z.s ≫ Z'.s) := by
    rw [reassoc_of% hf₁]; infer_instance
  have : IsFinite f.fromNormalization := AmpUniq.isFinite_fromNormalization_graph f (pullback.fst s₁ Z.s ≫ Z'.s)
  let u := f.toNormalization
  let p₁ := f.fromNormalization ≫ pullback.fst s₁ Z.s
  let p₂ := f.fromNormalization ≫ pullback.snd s₁ Z.s
  have hu₁ : u ≫ p₁ = Z'.j := by simp [u, p₁, hf₁]
  have hu₂ : u ≫ p₂ = r ≫ Z.j := by simp [u, p₂, hf₂]
  have : IsPreimmersion (u ≫ p₁) := hu₁ ▸ inferInstance
  have : IsPreimmersion u := AmpUniq.isPreimmersion_of_comp u p₁
  have : Flat u := AmpUniq.flat_of_isPreimmersion u
  have hN := GlobalTheory.IsNormalScheme.pred f.normalization
  have : IsLocallyNoetherian f.normalization := LocallyOfFiniteType.isLocallyNoetherian p₁
  let z₀ : Sp O' ⟶ Sp ℤ := spMap (algebraMap ℤ O')
  have : LocallyOfFiniteType z₀ :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 ‹_›)
  have : Flat z₀ := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Flat (f.toNormalization ≫ p₁ ≫ Z'.s) := by
    rw [reassoc_of% hu₁]; infer_instance
  have : Flat (p₁ ≫ Z'.s) := flat_normalization f (p₁ ≫ Z'.s)
  let t₂ := FiniteStable.twist σ hσ Z.t
  let ν₁ : SABMap Z'.oF.t (FiniteStable.twist σ hσ Z.oF.t) r := ⟨ν.cm, ν.cart, ν.base, ν.act, ν.lin⟩
  let ν₂ : SABMap (FiniteStable.twist σ hσ Z.oF.t) t₂ Z.j :=
    ⟨Z.m.cm, Z.m.cart, Z.m.base, fun a => Z.m.act (σ a), Z.m.lin⟩
  obtain ⟨m₂, -⟩ := ObjMaps.exists_sab_comp ν₂ ν₁
  obtain ⟨_, _, _, _, _, n₁, -⟩ := sabPull Out.CubePf.cubePull p₁ Z'.t
  obtain ⟨_, _, _, _, _, n₂, -⟩ := sabPull Out.CubePf.cubePull p₂ t₂
  obtain ⟨a₁, -⟩ := ObjMaps.exists_sab_cancel n₁ (hu₁ ▸ Z'.m : SABMap Z'.oF.t Z'.t (u ≫ p₁))
  obtain ⟨a₂, -⟩ := ObjMaps.exists_sab_cancel n₂ (hu₂ ▸ m₂ : SABMap Z'.oF.t t₂ (u ≫ p₂))
  obtain ⟨e, -⟩ := GlobalTheory.exists_sabMap_id_of_common_generic GlobalTheory.homExtension_semiAbelian_dvr_unconditional E H _ _ u
    ⟨hN, (p₁ ≫ Z'.s) ≫ z₀, inferInstance, inferInstance⟩ inferInstance inferInstance inferInstance inferInstance
    Z'.oF.t _ _ a₁ a₂ Z'.oF.proper
  obtain ⟨n₂', -⟩ := ObjMaps.exists_sab_comp n₂ e
  rw [Category.id_comp] at n₂'
  have hdet := lbIso_detLie_pull (G := (Over.pullback p₁).obj Z'.t.G) n₁.cart n₂'.cart fun U U' hU hU' =>
    (isAffineOpen_snd_inf_fst s₁ Z.s hU' hU).preimage f.fromNormalization
  have : Flat (u ≫ p₁) := hu₁ ▸ h2
  have hdiv := lbIso_pull_of_traits u p₁ p₂ BD' BD hN (fun K _ y => charZero_of_point (K := .of K) y)
    fun W _ _ _ hW χ y hy =>
      GlobalTheory.TraitOrder.idlAlong_eq E H D l l' Xo Xo' c c' O O' β β' Z Z' BD BD' φ σ r ν hβ hβ' htw hσ hP.1 hP'.1 W hW (χ ≫ p₂) (χ ≫ p₁) y
        (by rw [reassoc_of% hy, hu₁]) (by rw [reassoc_of% hy, hu₂])
  have hA : LBIso ((polOf Z' m BD').pull p₁) ((polOf Z m BD).pull p₂) :=
    lbIso_pull_tens (PolFin.isLB_detLie_of_polOf hP'.2.isLB) BD'.isLB_lb (PolFin.isLB_detLie_of_polOf hP.2.isLB) BD.isLB_lb m hdet hdiv
  have : IsFinite p₁ := AmpUniq.isFinite_fst s₁ Z.s f.fromNormalization hP'.2.isLB hP.2.isLB (PolFin.exists_H0_of_isAmpleLB hP.2) hA
  obtain ⟨h, ⟨k₁, k₂⟩, -⟩ := existsUnique_lift_of_densePart Z'.X _ Z'.X f.normalization Z'.j Z'.normal inferInstance
    inferInstance inferInstance inferInstance p₁ (𝟙 _) u inferInstance (by rw [hu₁, Category.comp_id])
  refine ⟨h ≫ p₂, ?_, by rw [reassoc_of% k₁, hu₂]⟩
  have : p₂ ≫ Z.s = p₁ ≫ s₁ := by simp only [p₁, p₂, Category.assoc, pullback.condition]
  rw [Category.assoc, this, reassoc_of% k₂]

end GlobalTheory.PolExt
