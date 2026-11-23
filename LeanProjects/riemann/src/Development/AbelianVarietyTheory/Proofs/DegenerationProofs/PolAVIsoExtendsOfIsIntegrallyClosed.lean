import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteResidueFieldIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.PolExtend

open GlobalTheory.Algebraise GlobalTheory.SectionRingIso GlobalTheory.GenericExtend TopologicalSpace

theorem exists_normalised_iso {X X' Q U : Scheme.{0}} {L : LB X} {L' : LB X'} {g : Q ⟶ X} {J : Q ⟶ X'}
    (v : LB.Iso (L'.pull J) (L.pull g)) (hv : v.IsGen) {π : Q ⟶ U} {eU : U ⟶ Q} (hπ : eU ≫ π = 𝟙 U)
    {j₀ : L.ι} {j₀' : L'.ι} (h₀ : ∀ t, g (eU t) ∈ L.U j₀) (h₀' : ∀ t, J (eU t) ∈ L'.U j₀') :
    ∃ v' : LB.Iso (L'.pull J) (L.pull g), v'.IsGen ∧
      ∀ (T : Scheme.{0}) (κ : T ⟶ U) (z : T), gw v' (κ ≫ eU) z j₀ (fun _ => j₀') = 1 := by
  have hle : (⊤ : U.Opens) ≤ eU ⁻¹ᵁ ((L.pull g).U (fun _ => j₀) ⊓ (L'.pull J).U (fun _ => j₀')) :=
    fun t _ => ⟨mem_pull.2 (h₀ t), mem_pull.2 (h₀' t)⟩
  let c : Γ(U, ⊤)ˣ := res hle (pullU eU _ (v.s (fun _ => j₀, fun _ => j₀')))
  have ht : ∀ A : Q.Opens, A ≤ π ⁻¹ᵁ ⊤ := fun _ _ _ => trivial
  let v' : LB.Iso (L'.pull J) (L.pull g) := ⟨fun p => v.s p * (res (ht _) (pullU π ⊤ c))⁻¹⟩
  have hv' : ∀ (T : Scheme.{0}) (r : T ⟶ Q) (z : T) (j : L.ι) (k : (L'.pull J).ι), g (r z) ∈ L.U j →
      r z ∈ (L'.pull J).U k → gw v' r z j k = gw v r z j k * (gm (r ≫ π) z ⊤ c)⁻¹ := fun T r z j k hj hk => by
    have hm : r z ∈ (L.pull g).U (fun _ => j) ⊓ (L'.pull J).U k := ⟨mem_pull.2 hj, hk⟩
    refine (map_mul _ _ _).trans (congrArg (_ * ·) ((map_inv _ _).trans (congrArg (·⁻¹) ?_)))
    exact gm_res_pullU r π z (ht _) hm c
  refine ⟨v', (isGen_iff v').2 fun T r z j j' k k' hj hj' hk hk' => ?_, fun T κ z => ?_⟩
  · rw [hv' T r z j k hj hk, hv' T r z j' k' hj' hk', (isGen_iff v).1 hv T r z j j' k k' hj hj' hk hk',
      _root_.mul_assoc]
  · rw [hv' T _ z j₀ _ (h₀ (κ z)) (mem_pull.2 (h₀' (κ z))), Category.assoc, hπ, Category.comp_id,
      gm_res_pullU κ eU z hle trivial]
    exact mul_inv_cancel _

theorem exists_iso_dvr {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] {X X' Q H Z : Scheme.{0}}
    {f : H ⟶ Spec (.of V)} [Smooth f] [GeometricallyIntegral f] {k : Z ⟶ H} {fK : Z ⟶ Spec (.of K)}
    (hK : IsPullback k fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
    {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {G : H ⟶ X} {φ : H ⟶ X'} {g : Q ⟶ X} {J : Q ⟶ X'}
    (v : LB.Iso (L'.pull J) (L.pull g)) (hv : v.IsGen) {ψ : Z ⟶ Q} (hg : ψ ≫ g = k ≫ G) (hJ : ψ ≫ J = k ≫ φ)
    {eV : Spec (.of V) ⟶ H} (heV : eV ≫ f = 𝟙 _) {eK : Spec (.of K) ⟶ Z}
    (heK : eK ≫ k = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ eV)
    {j₀ : L.ι} {j₀' : L'.ι} (h₀ : ∀ t, G (eV t) ∈ L.U j₀) (h₀' : ∀ t, φ (eV t) ∈ L'.U j₀')
    (hn : ∀ z, gw v (eK ≫ ψ) z j₀ (fun _ => j₀') = 1) :
    ∃ u : LB.Iso (L'.pull φ) (L.pull G), u.IsGen ∧ ∀ (T : Scheme.{0}) (r : T ⟶ Z) (z : T) (j : L.ι) (j' : L'.ι),
      G (k (r z)) ∈ L.U j → φ (k (r z)) ∈ L'.U j' →
        gw u (r ≫ k) z j (fun _ => j') = gw v (r ≫ ψ) z j (fun _ => j') := by
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  let N : LB H := LB.div (L.pull G) (L'.pull φ)
  have hN : N.IsLB := LB.isLB_div (LB.isLB_pull hL G) (LB.isLB_pull hL' φ)
  have e₁ : ∀ z, g (ψ z) = G (k z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]
  have e₂ : ∀ z, J (ψ z) = φ (k z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hJ, Scheme.Hom.comp_apply]
  have hW : ∀ a : N.ι, k ⁻¹ᵁ N.U a ≤ ψ ⁻¹ᵁ ((L.pull g).U a.1 ⊓ (L'.pull J).U a.2) := fun a z hz =>
    ⟨mem_pull.2 (e₁ z ▸ mem_pull.1 hz.1), mem_pull.2 (e₂ z ▸ mem_pull.1 hz.2)⟩
  let τ : ∀ a : N.ι, Γ(Z, k ⁻¹ᵁ N.U a)ˣ := fun a => res (hW a) (pullU ψ _ (v.s a))
  have hτ : ∀ (T : Scheme.{0}) (r : T ⟶ Z) (z : T) (a : N.ι), k (r z) ∈ N.U a →
      gm r z _ (τ a) = gw v (r ≫ ψ) z (a.1 PUnit.unit) (fun _ => a.2 PUnit.unit) := fun T r z a ha =>
    gm_res_pullU r ψ z (hW a) ha _
  have hc : ∀ a b : N.ι, res (inf_le_left : k ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ N.U b ≤ _) (τ a) =
      res (le_rfl : k ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ N.U b ≤ k ⁻¹ᵁ (N.U a ⊓ N.U b)) (pullU k _ (N.g a b)) *
        res (inf_le_right : k ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ N.U b ≤ _) (τ b) := fun a b => unit_ext fun z hz => by
    have a₁ := mem_pull.1 hz.1.1
    have a₂ := mem_pull.1 hz.1.2
    have b₁ := mem_pull.1 hz.2.1
    have b₂ := mem_pull.1 hz.2.2
    have h₁ := gm_div_g (L' := L'.pull φ) (F := G) (𝟙 Z ≫ k) z _ _ (fun _ => a.2 PUnit.unit)
      (fun _ => b.2 PUnit.unit) a₁ b₁ hz.1.2 hz.2.2
    have h₂ := (isGen_iff v).1 hv Z (𝟙 Z ≫ ψ) z (a.1 PUnit.unit) (b.1 PUnit.unit) (fun _ => a.2 PUnit.unit)
      (fun _ => b.2 PUnit.unit) ((e₁ z).symm ▸ a₁) ((e₁ z).symm ▸ b₁) (mem_pull.2 ((e₂ z).symm ▸ a₂))
      (mem_pull.2 ((e₂ z).symm ▸ b₂))
    rw [gm_pull_g φ (𝟙 Z ≫ k) z a₂ b₂] at h₁
    rw [gm_pull_g J (𝟙 Z ≫ ψ) z ((e₂ z).symm ▸ a₂) ((e₂ z).symm ▸ b₂), Category.assoc, Category.assoc, hg, hJ,
      ← Category.assoc, ← Category.assoc, ← h₁] at h₂
    rw [map_mul, gm_res _ z inf_le_left hz, gm_res _ z inf_le_right hz, hτ _ (𝟙 Z) z a hz.1, hτ _ (𝟙 Z) z b hz.2]
    exact h₂.trans (congrArg (· * _) (gm_res_pullU (𝟙 Z) k z (V := N.U a ⊓ N.U b)
      (A := k ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ N.U b) le_rfl hz _).symm)
  have hA : (⊤ : (Spec (.of V)).Opens) ≤ eV ⁻¹ᵁ N.U (fun _ => j₀, fun _ => j₀') :=
    fun t _ => ⟨mem_pull.2 (h₀ t), mem_pull.2 (h₀' t)⟩
  have hA' : Spec.map (CommRingCat.ofHom (algebraMap V K)) ⁻¹ᵁ ⊤ ≤
      eK ⁻¹ᵁ k ⁻¹ᵁ N.U (fun _ => j₀, fun _ => j₀') := by
    rw [← Scheme.Hom.comp_preimage eK, heK]
    exact (Spec.map (CommRingCat.ofHom (algebraMap V K))).preimage_mono hA
  have hu : res le_rfl (pullU (Spec.map (CommRingCat.ofHom (algebraMap V K))) ⊤ 1) =
      res hA' (pullU eK _ (τ (fun _ => j₀, fun _ => j₀'))) := by
    refine unit_ext fun z hz => ?_
    rw [map_one, map_one, map_one, gm_res_pullU (𝟙 _) eK z hA' hz, Category.id_comp, hτ _ eK z _ (hA' hz)]
    exact (hn z).symm
  obtain ⟨s, ⟨hsu, hsc, hsr⟩, -⟩ := DvrModel.existsUnique_isUnit_appLE_eq hK hs
    (U := N.U) (g := fun a b => (N.g a b).val) (W := fun a => k ⁻¹ᵁ N.U a) (fun _ => rfl)
    (fun x => exists_chart hN x) (fun a b => Units.isUnit _) (r := fun a => (τ a).val)
    (fun a b => congrArg Units.val (hc a b)) (fun a => Units.isUnit _) heV heK
    (a₀ := (fun _ => j₀, fun _ => j₀')) (A := ⊤) trivial hA rfl hA' isUnit_one (congrArg Units.val hu)
  refine ⟨⟨fun a => (hsu a).unit⟩, fun a b => Units.ext (hsc a b), fun T r z j j' hj hj' => ?_⟩
  have hm : k (r z) ∈ N.U (fun _ => j, fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  have : res le_rfl (pullU k _ (hsu (fun _ => j, fun _ => j')).unit) = τ (fun _ => j, fun _ => j') :=
    Units.ext (hsr _)
  rw [← hτ T r z _ hm, ← this]
  exact (gm_res_pullU r k z (V := N.U (fun _ => j, fun _ => j')) le_rfl hm _).symm

theorem extAt_of_rel {S U P X : Scheme.{0}} [IsLocallyNoetherian S] [GlobalTheory.IsNormalScheme S] (j : U ⟶ S)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (p : P ⟶ S) [Smooth p] [GeometricallyIntegral p]
    {e : S ⟶ P} (he : e ≫ p = 𝟙 S) {L : LB X} {L' : LB P} (hL : L.IsLB) (hL' : L'.IsLB)
    {g : pullback p j ⟶ X} (v : LB.Iso (L'.pull (pullback.fst p j)) (L.pull g)) (hv : v.IsGen) {e₀ : S ⟶ X}
    {eU : U ⟶ pullback p j} (w : eU ≫ pullback.fst p j = j ≫ e) {j₀ : L.ι} {j₀' : L'.ι}
    (h₀ : ∀ s, e₀ s ∈ L.U j₀) (h₀' : ∀ s, e s ∈ L'.U j₀')
    (hn : ∀ (T : Scheme.{0}) (κ : T ⟶ U) (z : T), gw v (κ ≫ eU) z j₀ (fun _ => j₀') = 1)
    (hG : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (l : Sp V ⟶ S)
      (κ : Sp (FractionRing V) ⟶ U), κ ≫ j = jK V ≫ l → ∃ G : pullback p l ⟶ X,
        (∀ ψ : pullback (pullback.snd p l) (jK V) ⟶ pullback p j,
          ψ ≫ pullback.fst p j = pullback.fst _ _ ≫ pullback.fst p l → ψ ≫ g = pullback.fst _ _ ≫ G) ∧
        ∀ eV : Sp V ⟶ pullback p l, eV ≫ pullback.fst p l = l ≫ e → eV ≫ pullback.snd p l = 𝟙 _ →
          eV ≫ G = l ≫ e₀)
    {n : ℕ} (b : H0 L n) (a : L'.ι) (τ : Γ(pullback p j, pullback.fst p j ⁻¹ᵁ L'.U a))
    (hτ : ∀ (T : Scheme.{0}) (r : T ⟶ pullback p j) (z : T) (i : L.ι), g (r z) ∈ L.U i →
      pullback.fst p j (r z) ∈ L'.U a →
      vl b (r ≫ g) z (fun _ => i) = (gw v r z i (fun _ => a)).val ^ n * gs r z _ τ)
    (y : P) (hx : Order.coheight (p y) = 1) (ha : y ∈ L'.U a) : ExtAt (pullback.fst p j) (L'.U a) τ y := by
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst p j)
  have := IsNormalScheme.of_isIso_stalkMap (pullback.fst p j)
  have := IsNormalScheme.isDiscreteValuationRing_stalk hx
  let V : Type := S.presheaf.stalk (p y)
  let K : Type := FractionRing V
  let l : Spec (.of V) ⟶ S := S.fromSpecStalk (p y)
  have : IsPreimmersion l := inferInstanceAs (IsPreimmersion (S.fromSpecStalk (p y)))
  have hl : Set.range l = {ξ | ξ ⤳ p y} := Scheme.range_fromSpecStalk
  let m : Spec (.of K) ⟶ Spec (.of V) := Spec.map (CommRingCat.ofHom (algebraMap V K))
  obtain ⟨κ, hκ⟩ := exists_lift j (m ≫ l) (by
    rintro _ ⟨o, rfl⟩
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    obtain ⟨v, rfl⟩ : ξ ∈ Set.range l := hl ▸ hξy
    have hv : m o ⤳ v := (PrimeSpectrum.le_iff_specializes (m o) v).1 (by
      intro c hc
      have hc' : algebraMap V K c ∈ o.asIdeal := hc
      rw [Ideal.eq_bot_of_prime o.asIdeal, Ideal.mem_bot,
        map_eq_zero_iff _ (IsFractionRing.injective V K)] at hc'
      rw [hc']
      exact Ideal.zero_mem _)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range (hv.map l.continuous) hξ)
  let φ := pullback.fst p l
  let f := pullback.snd p l
  let k := pullback.fst f m
  let fK := pullback.snd f m
  have hK : IsPullback k fK f m := .of_hasPullback f m
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral hK
  have := DvrModel.isOpenImmersion_generic hK
  let ψ : pullback f m ⟶ pullback p j := pullback.lift (k ≫ φ) (fK ≫ κ) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hK.w, Category.assoc, Category.assoc, hκ])
  have hψ : ψ ≫ pullback.fst p j = k ≫ φ := pullback.lift_fst _ _ _
  let eV : Spec (.of V) ⟶ pullback p l := pullback.lift (l ≫ e) (𝟙 _) (by simp [he])
  have heV : eV ≫ φ = l ≫ e := pullback.lift_fst _ _ _
  have heV' : eV ≫ f = 𝟙 _ := pullback.lift_snd _ _ _
  let eK : Spec (.of K) ⟶ pullback f m := pullback.lift (m ≫ eV) (𝟙 _) (by simp [heV'])
  have heK : eK ≫ k = m ≫ eV := pullback.lift_fst _ _ _
  have hek : eK ≫ ψ = κ ≫ eU := by
    rw [← cancel_mono (pullback.fst p j), Category.assoc, hψ, reassoc_of% heK, heV, Category.assoc, w,
      reassoc_of% hκ]
  obtain ⟨G, hG₁, hG₂⟩ := hG V l κ hκ
  have hψg : ψ ≫ g = k ≫ G := hG₁ ψ hψ
  obtain ⟨u, hu, huv⟩ := exists_iso_dvr hK hL hL' v hv hψg hψ heV' heK (j₀ := j₀) (j₀' := j₀')
    (fun t => by rw [← Scheme.Hom.comp_apply, hG₂ eV heV heV']; exact h₀ _)
    (fun t => by rw [← Scheme.Hom.comp_apply, heV]; exact h₀' _) (fun z => by rw [hek]; exact hn _ _ _)
  obtain ⟨s, hs⟩ := Algebraise.exists_down hL hL' G φ u hu b
  have hW : ∀ A : P.Opens, k ⁻¹ᵁ φ ⁻¹ᵁ A ≤ ψ ⁻¹ᵁ pullback.fst p j ⁻¹ᵁ A := fun A => by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hψ]
  have hle : φ ⁻¹ᵁ L'.U a ≤ LB.wchart L' (fun _ : Fin 1 => φ) (fun _ => a) := fun x hx => mem_wc.2 hx
  have hst : (k.appLE _ _ le_rfl).hom (resG _ hle (s.f fun _ => a)) = (ψ.appLE _ _ (hW (L'.U a))).hom τ := by
    refine fn_ext fun z hz => ?_
    obtain ⟨i, hi⟩ := exists_chart hL (G (k z))
    have hi' : g (ψ z) ∈ L.U i := by rwa [← Scheme.Hom.comp_apply, hψg]
    have h₁ := hs _ (𝟙 _ ≫ k) z i a hi hz
    have h₂ := hτ _ (𝟙 _ ≫ ψ) z i hi' (hW _ hz)
    rw [Category.assoc, hψg, ← Category.assoc, h₁, huv _ (𝟙 _) z i a hi hz] at h₂
    refine (gs_res (𝟙 _) z le_rfl hz _).trans ((gs_pull (𝟙 _) k z _ hz _).trans
      ((gs_res _ z hle hz _).trans ((((Units.isUnit _).pow n).mul_left_cancel h₂).trans ?_)))
    exact ((gs_res (𝟙 _) z (hW _) hz _).trans (gs_pull (𝟙 _) ψ z _ (hW _ hz) _)).symm
  obtain ⟨h, hh⟩ : y ∈ Set.range φ := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, hl]
    exact specializes_rfl
  obtain ⟨z, hz⟩ : genericPoint (pullback p l :) ∈ k.opensRange :=
    have : Nonempty k.opensRange := ⟨⟨k (Nonempty.some inferInstance), _, rfl⟩⟩
    genericPoint_mem_opens _
  have hg : ∀ y, y ⤳ φ h → φ (k z) ⤳ y := fun y hy => by
    obtain ⟨h', rfl⟩ : y ∈ Set.range φ := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hl]
      exact (hh ▸ hy).map p.continuous
    rw [hz]
    exact (genericPoint_specializes h').map φ.continuous
  have ha' : φ h ∈ L'.U a := by rw [hh]; exact ha
  have hza : z ∈ k ⁻¹ᵁ φ ⁻¹ᵁ L'.U a := (hg _ specializes_rfl).mem_open (L'.U a).isOpen ha'
  rw [← hh]
  exact extAt_of_generic _ φ k ψ hψ _ _ _ le_rfl (hW _) hst z hza h ha' hg

theorem existsUnique_rel_dense {S U P X : Scheme.{0}} [IsLocallyNoetherian S] [GlobalTheory.IsNormalScheme S] (j : U ⟶ S)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (p : P ⟶ S) [Smooth p] [GeometricallyIntegral p]
    {e : S ⟶ P} (he : e ≫ p = 𝟙 S) {L : LB X} {L' : LB P} (hL : L.IsLB) (hL' : L'.IsLB)
    {g : pullback p j ⟶ X} (v : LB.Iso (L'.pull (pullback.fst p j)) (L.pull g)) (hv : v.IsGen) {e₀ : S ⟶ X}
    {eU : U ⟶ pullback p j} (w : eU ≫ pullback.fst p j = j ≫ e) {j₀ : L.ι} {j₀' : L'.ι}
    (h₀ : ∀ s, e₀ s ∈ L.U j₀) (h₀' : ∀ s, e s ∈ L'.U j₀')
    (hn : ∀ (T : Scheme.{0}) (κ : T ⟶ U) (z : T), gw v (κ ≫ eU) z j₀ (fun _ => j₀') = 1)
    (hG : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (l : Sp V ⟶ S)
      (κ : Sp (FractionRing V) ⟶ U), κ ≫ j = jK V ≫ l → ∃ G : pullback p l ⟶ X,
        (∀ ψ : pullback (pullback.snd p l) (jK V) ⟶ pullback p j,
          ψ ≫ pullback.fst p j = pullback.fst _ _ ≫ pullback.fst p l → ψ ≫ g = pullback.fst _ _ ≫ G) ∧
        ∀ eV : Sp V ⟶ pullback p l, eV ≫ pullback.fst p l = l ≫ e → eV ≫ pullback.snd p l = 𝟙 _ →
          eV ≫ G = l ≫ e₀)
    {n : ℕ} (b : H0 L n) :
    ∃! a : H0 L' n, Rel (T := fun _ => pullback p j) (fun _ => g) (fun _ => pullback.fst p j) (fun _ => v) a b := by
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  have hJ := (pullback.fst p j).app_injective
  let J := pullback.fst p j
  obtain ⟨s, hs⟩ := Algebraise.exists_down hL hL' g J v hv b
  have hle : ∀ a, J ⁻¹ᵁ L'.U a ≤ LB.wchart L' (fun _ : Fin 1 => J) (fun _ => a) := fun a x hx => mem_wc.2 hx
  choose σ hσ using fun a => exists_app_eq J hJ (L'.U a) (resG _ (hle a) (s.f fun _ => a)) fun y ha h1 hy => by
    refine extAt_of_rel j p he hL hL' v hv w h₀ h₀' hn hG b a _ (fun T r z i hi hi' => ?_) y
      (le_antisymm (coheight_apply_le_one p h1) (ENat.one_le_iff_ne_zero.2 fun h0 => hy ?_)) ha
    · exact (hs T r z i a hi hi').trans (congrArg _ (gs_res r z (hle a) hi' _).symm)
    · rw [Scheme.Pullback.range_fst]
      obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
      exact (Flat.generalizingMap j).stableUnderGeneralization_range
        (show p y ⤳ ξ from Order.coheight_eq_zero.1 h0 hξy) hξ
  have inj : ∀ (W : P.Opens) (x x' : Γ(P, W)), (∀ q, J q ∈ W → gs (𝟙 _ ≫ J) q W x = gs (𝟙 _ ≫ J) q W x') → x = x' :=
    fun W x x' h => hJ W (fn_ext fun q hq =>
      (gs_pull (𝟙 _) J q W hq x).trans ((h q hq).trans (gs_pull (𝟙 _) J q W hq x').symm))
  have le : ∀ i : Fin 1 → L'.ι, ch L' i ≤ L'.U (i 0) := fun i y hy => mem_ch.1 hy
  have hv₀ : ∀ (T : Scheme.{0}) (r : T ⟶ pullback p j) (z : T) (i : Fin 1 → L'.ι), J (r z) ∈ L'.U (i 0) →
      gs (r ≫ J) z (ch L' i) (resG _ (le i) (σ (i 0))) =
        gs r z (LB.wchart L' (fun _ : Fin 1 => J) fun _ => i 0) (s.f fun _ => i 0) := fun T r z i hi => by
    refine (gs_res (r ≫ J) z (le i) (mem_ch.2 hi) _).trans ((gs_pull r J z _ hi _).symm.trans ?_)
    rw [hσ]
    exact gs_res r z (hle _) hi _
  let a : H0 L' n := ⟨fun i => resG _ (le i) (σ (i 0)), fun i i' => inj _ _ _ fun q hq => by
    have hi := mem_ch.1 hq.1
    have hi' := mem_ch.1 hq.2
    refine (gs_res (𝟙 _ ≫ J) q inf_le_left hq _).trans ((hv₀ _ (𝟙 _) q i hi).trans
      ((sec_trans s (𝟙 _) q (j := fun _ => i 0) (j' := fun _ => i' 0) (mem_wc.2 hi) (mem_wc.2 hi')).trans (Eq.trans ?_ (gs_mul (𝟙 _ ≫ J) q _ hq _ _).symm)))
    refine congrArg₂ (· * ·) ?_ ((gs_res (𝟙 _ ≫ J) q inf_le_right hq _).trans (hv₀ _ (𝟙 _) q i' hi')).symm
    refine Eq.trans ?_ ((gs_unit (𝟙 _ ≫ J) q _ hq _).trans
      (congrArg Units.val (gm_linComb L' _ _ (𝟙 _ ≫ J) q i i' hq.1 hq.2))).symm
    rw [trF, Fin.prod_univ_one, Fin.prod_univ_one, Category.comp_id]⟩
  have ha : Rel (T := fun _ => pullback p j) (fun _ => g) (fun _ => J) (fun _ => v) a b :=
    fun _ T r z i i' hi hi' => (hs T r z i i' hi hi').trans (congrArg _ (hv₀ T r z (fun _ => i') hi').symm)
  refine ⟨a, ha, fun a' ha' => ?_⟩
  have : a'.f = a.f := funext fun i => by
    obtain ⟨i', rfl⟩ : ∃ i', i = fun _ => i' := ⟨_, fin_one_const i⟩
    refine inj _ _ _ fun q hq => ?_
    obtain ⟨i, hi⟩ := exists_chart hL (g q)
    exact ((Units.isUnit _).pow n).mul_left_cancel
      ((ha' 0 _ (𝟙 _) q i i' hi (mem_ch.1 hq)).symm.trans (ha 0 _ (𝟙 _) q i i' hi (mem_ch.1 hq)))
  cases a'
  exact LB.Sec.mk.injEq _ _ _ _ ▸ this

theorem exists_iso_of_rel (hA : AmpleSt) {R : Type} [CommRing R] [IsNoetherianRing R]
    (P P' : PolAV (Spec (CommRingCat.of R))) {T : Scheme.{0}} (g : T ⟶ P.A.left) (g' : T ⟶ P'.A.left)
    (v : LB.Iso (P'.L.pull g') (P.L.pull g)) (hv : v.IsGen) (hbase : g ≫ P.A.hom = g' ≫ P'.A.hom)
    (E₁ : ∀ (n : ℕ) (b : H0 P.L n), ∃! a : H0 P'.L n,
      Rel (T := fun _ => T) (fun _ => g) (fun _ => g') (fun _ => v) a b)
    (E₂ : ∀ (n : ℕ) (a : H0 P'.L n), ∃! b : H0 P.L n,
      Rel (T := fun _ => T) (fun _ => g) (fun _ => g') (fun _ => v) a b) :
    ∃ Ψ : P'.A ≅ P.A, g = g' ≫ Ψ.hom.left ∧ LBIso P'.L (P.L.pull Ψ.hom.left) := by
  have prop : ∀ Q : PolAV (Spec (CommRingCat.of R)), IsProper Q.A.hom := fun Q => Q.isAb.proper
  have cpt : ∀ Q : PolAV (Spec (CommRingCat.of R)), CompactSpace Q.A.left := fun Q =>
    have := prop Q; QuasiCompact.compactSpace_of_compactSpace Q.A.hom
  have qs : ∀ Q : PolAV (Spec (CommRingCat.of R)), QuasiSeparatedSpace Q.A.left := fun Q =>
    have := prop Q; quasiSeparatedSpace_of_quasiSeparated Q.A.hom
  have := prop P; have := prop P'; have := cpt P; have := cpt P'; have := qs P; have := qs P'
  let Rl : ∀ n : ℕ, H0 P'.L n → H0 P.L n → Prop := fun n a b =>
    Rel (T := fun _ => T) (fun _ => g) (fun _ => g') (fun _ => v) a b
  obtain ⟨θ, hθ⟩ : ∃ θ : ∀ n : ℕ, 1 ≤ n → (H0 P'.L n ≃ H0 P.L n), ∀ n hn a, Rl n a (θ n hn a) := by
    refine ⟨fun n hn => ⟨fun a => (E₂ n a).exists.choose, fun b => (E₁ n b).exists.choose, fun a => ?_,
      fun b => ?_⟩, fun n hn a => (E₂ n a).exists.choose_spec⟩
    · exact (E₁ n _).unique (E₁ n _).exists.choose_spec (E₂ n a).exists.choose_spec
    · exact (E₂ n _).unique (E₂ n _).exists.choose_spec (E₁ n b).exists.choose_spec
  have hlin : ∀ (n : ℕ) (hn : 1 ≤ n) (c : R) (a b d : H0 P'.L n),
      (∀ j, d.f j = a.f j + resTop _ (scal P'.A.hom c) * b.f j) →
      ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal P.A.hom c) * (θ n hn b).f j := by
    intro n hn c a b d h
    have : Rl n d (DVR.SecOps.secAdd (θ n hn a) (DVR.SecOps.secScale (scal P.A.hom c) (θ n hn b))) := by
      intro e Z r z j j' hj hj'
      rw [vl_add_scale (a := θ n hn a) (b := θ n hn b) (c := scal P.A.hom c) (fun _ => rfl) _ z hj,
        vl_add_scale h _ z hj', hθ n hn a e Z r z j j' hj hj', hθ n hn b e Z r z j j' hj hj', gs_scal, gs_scal,
        Category.assoc r, Category.assoc r, hbase]
      ring
    rw [(E₂ n d).unique (hθ n hn d) this]
    exact fun _ => rfl
  have hmul : ∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 P'.L n) (b : H0 P'.L m) (d : H0 P'.L (n + m)),
      (∀ j : Fin 1 → P'.L.ι, (show Γ(P'.A.left, ch P'.L j) from d.f j) =
        (show Γ(P'.A.left, ch P'.L j) from a.f j) * (show Γ(P'.A.left, ch P'.L j) from b.f j)) →
      ∀ j : Fin 1 → P.L.ι, (show Γ(P.A.left, ch P.L j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) =
        (show Γ(P.A.left, ch P.L j) from (θ n hn a).f j) * (show Γ(P.A.left, ch P.L j) from (θ m hm b).f j) := by
    intro n m hn hm a b d h
    obtain ⟨d', hd'⟩ := exists_mul (θ n hn a) (θ m hm b)
    have : Rl (n + m) d d' := by
      intro e Z r z j j' hj hj'
      rw [vl_mul hd' _ z hj, vl_mul h _ z hj', hθ n hn a e Z r z j j' hj hj', hθ m hm b e Z r z j j' hj hj']
      ring
    rw [(E₂ _ d).unique (hθ _ _ d) this]
    exact hd'
  have h4 : 1 ≤ 4 := by norm_num
  obtain ⟨κ, t, ht, hta⟩ := exists_cover hA P 4 le_rfl
  obtain ⟨κ', s, hs, -⟩ := exists_cover hA P' 4 le_rfl
  obtain ⟨κ'', s₅, hs₅, -⟩ := exists_cover hA P' (4 + 1) (by norm_num)
  have ms : ∀ x, ∃ i, x ∈ nonzeroLocus (s i) := fun x => Opens.mem_iSup.1 (by rw [hs]; trivial)
  have ms₅ : ∀ x, ∃ i, x ∈ nonzeroLocus (s₅ i) := fun x => Opens.mem_iSup.1 (by rw [hs₅]; trivial)
  obtain ⟨Ψ, hΨ⟩ := exists_iso_of_sectionRing_equiv R P.A P'.A P.L P'.L P.isLB P'.isLB θ hlin hmul
    ⟨4, h4, H0 P'.L 4, id,
      top_le_iff.1 (hs.ge.trans (iSup_le fun i => le_iSup (fun a : H0 P'.L 4 => nonzeroLocus a) (s i))),
      top_le_iff.1 (ht.ge.trans (iSup_le fun i => le_iSup_of_le ((θ 4 h4).symm (t i))
        (congrArg nonzeroLocus ((θ 4 h4).apply_symm_apply (t i))).ge)),
      fun a => ⟨(isAffineOpen_nonzeroLocus_of_relAmple R P'.A P'.L P'.isLB P'.ample 4 h4).1 _,
        (isAffineOpen_nonzeroLocus_of_relAmple R P.A P.L P.isLB P.ample 4 h4).1 _⟩⟩
  obtain ⟨w, hw, H⟩ := GlobalTheory.exists_iso_of_sectionRing R P.A P'.A P.L P'.L P.isLB P'.isLB θ hlin hmul Ψ.hom.left hΨ
    fun x => by
      obtain ⟨i, hi⟩ := ms x
      obtain ⟨k, hk⟩ := ms₅ x
      exact ⟨4, h4, s i, s₅ k, hi, hk⟩
  have H' : ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 P'.L n) (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) (j : P.L.ι)
      (j' : P'.L.ι), Ψ.hom.left (r z) ∈ P.L.U j → r z ∈ P'.L.U j' →
      vl (θ n hn a) (r ≫ Ψ.hom.left) z (fun _ => j) = (gw w r z j j').val ^ n * vl a r z (fun _ => j') := by
    intro n hn a Z r z j j' hj hj'
    refine (H n hn a Z r z (fun _ => j) (fun _ => j') (fun _ => hj) (fun _ => hj')).trans ?_
    rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast, Units.val_pow_eq_pow_val]
  refine ⟨Ψ, ?_, w, hw⟩
  obtain ⟨y, hy, hy'⟩ := exists_swap _ _ v hv (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _)
  obtain ⟨y', Tr⟩ := Geo.Tor.exists_comp P'.isLB w y ((isGen_iff w).1 hw) ((isGen_iff y).1 hy) P.isLB
    (LB.isLB_pull P.isLB _)
  refine hom_ext_of_sec_pull_eq _ _ P.L P.isLB ⟨4, h4, κ, t, ht, hta⟩ _ _ y'
    ((isGen_iff y').2 (Tr.pgen_comp P'.isLB ((isGen_iff w).1 hw) ((isGen_iff y).1 hy))) fun n hn b z j j' hj hj' => ?_
  obtain ⟨a, rfl⟩ := (θ n hn).surjective b
  obtain ⟨k, hk⟩ := exists_chart P'.isLB (g' z)
  have h₁ := H' n hn a _ g' z j k hj hk
  have h₂ := hθ n hn a 0 _ (𝟙 T) z j' k hj' hk
  have h₃ := Tr _ (𝟙 _) z j k (fun _ => j') hj hk (mem_pull.2 hj')
  rw [hy' _ (𝟙 _) z j' k hj' hk] at h₃
  simp only [Category.id_comp] at h₂ h₃
  refine h₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (fun t => (t ^ n).val) h₃) h₂).symm)
  rw [Units.val_pow_eq_pow_val, ← _root_.mul_assoc, ← mul_pow, ← Units.val_mul, inv_mul_cancel_right]

theorem eSec_fst {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    eSec ((Over.pullback p).obj G) ≫ pullback.fst G.hom p = p ≫ eSec G := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq]
  erw [ExtUnique.pullback_map_left_fst, ← Category.assoc, ← pullback.condition]
  simp

theorem eSec_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f] :
    eSec G ≫ f.left = eSec H := congrArg (·.left) (IsMonHom.one_hom f)

theorem exists_hom_dvr
    (hext : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
        ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    {S U : Scheme.{0}} (j : U ⟶ S) [Mono j] {G G' : Over S} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G)
    (hG' : IsSemiAbelian G') (φ : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') [IsMonHom φ]
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (l : Sp V ⟶ S)
    (κ : Sp (FractionRing V) ⟶ U) (hκ : κ ≫ j = jK V ≫ l) : ∃ F : pullback G.hom l ⟶ G'.left,
      (∀ ψ : pullback (pullback.snd G.hom l) (jK V) ⟶ pullback G.hom j,
        ψ ≫ pullback.fst G.hom j = pullback.fst _ _ ≫ pullback.fst G.hom l →
          ψ ≫ φ.left ≫ pullback.fst G'.hom j = pullback.fst _ _ ≫ F) ∧
      ∀ eV : Sp V ⟶ pullback G.hom l, eV ≫ pullback.fst G.hom l = l ≫ eSec G → eV ≫ pullback.snd G.hom l = 𝟙 _ →
        eV ≫ F = l ≫ eSec G' := by
  obtain ⟨α, hα, hα'⟩ := grpPullback_iso
    ((isGrpPullback_pullback ((Over.pullback l).obj G) (jK V)).comp (isGrpPullback_pullback G l))
    (((isGrpPullback_pullback ((Over.pullback j).obj G) κ).comp
      (isGrpPullback_pullback G j)).congr hκ rfl)
  obtain ⟨β, hβ, hβ'⟩ := grpPullback_iso
    (((isGrpPullback_pullback ((Over.pullback j).obj G') κ).comp
      (isGrpPullback_pullback G' j)).congr hκ rfl)
    ((isGrpPullback_pullback ((Over.pullback l).obj G') (jK V)).comp (isGrpPullback_pullback G' l))
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := hext V (FractionRing V) _ _ (IsSemiAbelian.pullback l G hG)
    (IsSemiAbelian.pullback l G' hG') (α.hom ≫ (Over.pullback κ).map φ ≫ β.hom) inferInstance
  refine ⟨F.left ≫ pullback.fst G'.hom l, fun ψ hψ => ?_, fun eV h₁ h₂ => ?_⟩
  · have h₁ := ExtUnique.pullback_map_left_fst (jK V) F
    have h₂ := ExtUnique.pullback_map_left_fst κ φ
    have h₃ : α.hom.left ≫ pullback.fst (pullback.snd G.hom j) κ = ψ := by
      rw [← cancel_mono (pullback.fst G.hom j), hψ]
      exact (Category.assoc _ _ _).trans hα'
    erw [hF'] at h₁
    rw [Over.comp_left, Over.comp_left] at h₁
    erw [← reassoc_of% h₁, hβ', reassoc_of% h₂, reassoc_of% h₃]
  · have : eV = eSec ((Over.pullback l).obj G) := by
      apply pullback.hom_ext
      · exact h₁.trans (eSec_fst l G).symm
      · exact h₂.trans (Over.w η[(Over.pullback l).obj G]).symm
    rw [this]
    erw [← Category.assoc, eSec_comp F]
    exact eSec_fst l G'

theorem existsUnique_rel_generic
    (hext : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
        ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (P P' : PolAV (Sp R))
    (φ : (Over.pullback (jK R)).obj P'.A ⟶ (Over.pullback (jK R)).obj P.A) [IsMonHom φ]
    {g : pullback P'.A.hom (jK R) ⟶ P.A.left} (hg : g = φ.left ≫ pullback.fst P.A.hom (jK R))
    (v : LB.Iso (P'.L.pull (pullback.fst P'.A.hom (jK R))) (P.L.pull g)) (hv : v.IsGen) {j₀ : P.L.ι} {j₀' : P'.L.ι}
    (h₀ : ∀ s, eSec P.A s ∈ P.L.U j₀) (h₀' : ∀ s, eSec P'.A s ∈ P'.L.U j₀')
    (hn : ∀ (T : Scheme.{0}) (κ : T ⟶ Sp (FractionRing R)) (z : T),
      gw v (κ ≫ eSec ((Over.pullback (jK R)).obj P'.A)) z j₀ (fun _ => j₀') = 1) (n : ℕ) (b : H0 P.L n) :
    ∃! a : H0 P'.L n, Rel (T := fun _ => pullback P'.A.hom (jK R)) (fun _ => g)
      (fun _ => pullback.fst P'.A.hom (jK R)) (fun _ => v) a b := by
  subst hg
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R (FractionRing R)
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have := P'.isAb.smooth
  have := geometricallyIntegral_of_isAbelianScheme P'.A (h := P'.isAb)
  exact existsUnique_rel_dense (jK R) P'.A.hom (e := eSec P'.A) (Over.w η[P'.A]) P.isLB P'.isLB v hv
    (e₀ := eSec P.A) (eSec_fst (jK R) P'.A) h₀ h₀' hn
    (exists_hom_dvr hext (jK R) (isSemiAbelian_of_isAbelianScheme _ P'.isAb)
      (isSemiAbelian_of_isAbelianScheme _ P.isAb) φ) b

end GlobalTheory.PolExtend

open GlobalTheory.PolExtend GlobalTheory.Algebraise in

theorem GlobalTheory.polAV_iso_extends_of_isIntegrallyClosed : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (P P' : PolAV (Sp R)) (ψ : (Over.pullback (jK R)).obj P'.A ≅ (Over.pullback (jK R)).obj P.A), IsMonHom ψ.hom → LBIso (P'.L.pull (pullback.fst P'.A.hom (jK R))) (P.L.pull (ψ.hom.left ≫ pullback.fst P.A.hom (jK R))) → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∃ Ψ : P'.A ≅ P.A, IsMonHom Ψ.hom ∧ (Over.pullback (jK R)).map Ψ.hom = ψ.hom ∧ LBIso P'.L (P.L.pull Ψ.hom.left) := by
  intro hl _ R _ _ _ _ _ P P' ψ hψ ⟨v₀, hv₀⟩ hext
  have chart : ∀ Q : PolAV (Sp R), ∃ j, ∀ s, eSec Q.A s ∈ Q.L.U j := fun Q => by
    obtain ⟨j, hj⟩ := exists_chart Q.isLB (eSec Q.A (IsLocalRing.closedPoint R))
    exact ⟨j, fun s => ((IsLocalRing.specializes_closedPoint s).map (eSec Q.A).continuous).mem_open
      (Q.L.U j).isOpen hj⟩
  obtain ⟨j₀, h₀⟩ := chart P
  obtain ⟨j₀', h₀'⟩ := chart P'
  have e₁ : eSec ((Over.pullback (jK R)).obj P'.A) ≫ ψ.hom.left ≫ pullback.fst P.A.hom (jK R) =
      jK R ≫ eSec P.A := by
    rw [← Category.assoc, eSec_comp ψ.hom, eSec_fst]
  obtain ⟨v, hv, hn⟩ := exists_normalised_iso v₀ hv₀ (π := pullback.snd P'.A.hom (jK R))
    (eU := eSec ((Over.pullback (jK R)).obj P'.A)) (Over.w η[(Over.pullback (jK R)).obj P'.A]) (j₀ := j₀) (j₀' := j₀')
    (fun t => (congrArg (fun q => q t ∈ P.L.U j₀) e₁).mpr (h₀ _))
    (fun t => (congrArg (fun q => q t ∈ P'.L.U j₀') (eSec_fst (jK R) P'.A)).mpr (h₀' _))
  have hi : ψ.hom.left ≫ ψ.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  have ih : ψ.inv.left ≫ ψ.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  have eA : ψ.inv.left ≫ ψ.hom.left ≫ pullback.fst P.A.hom (jK R) = pullback.fst P.A.hom (jK R) := by
    rw [← Category.assoc, ih, Category.id_comp]
  have eB : ψ.hom.left ≫ ψ.inv.left ≫ pullback.fst P'.A.hom (jK R) = pullback.fst P'.A.hom (jK R) := by
    rw [← Category.assoc, hi, Category.id_comp]
  obtain ⟨u, hu, hu'⟩ := exists_swap _ _ v hv ψ.inv.left (pullback.fst P.A.hom (jK R))
    (ψ.inv.left ≫ pullback.fst P'.A.hom (jK R)) eA rfl
  have e₂ : eSec ((Over.pullback (jK R)).obj P.A) ≫ ψ.inv.left ≫ pullback.fst P'.A.hom (jK R) =
      jK R ≫ eSec P'.A := by
    rw [← Category.assoc, eSec_comp ψ.inv, eSec_fst]
  obtain ⟨Ψ, hΨ, hw⟩ := exists_iso_of_rel hl.ample P P' _ _ v hv
    (by
      have : ψ.hom.left ≫ pullback.snd P.A.hom (jK R) = pullback.snd P'.A.hom (jK R) := Over.w ψ.hom
      erw [Category.assoc, pullback.condition, reassoc_of% this, pullback.condition])
    (existsUnique_rel_generic hext P P' ψ.hom rfl v hv h₀ h₀' hn) fun n a => by
      have H := existsUnique_rel_generic hext P' P ψ.inv rfl u hu h₀' h₀ (fun T κ z => by
        rw [hu' T _ z j₀ j₀' ((congrArg (fun q => q (κ z) ∈ P.L.U j₀) (eSec_fst (jK R) P.A)).mpr (h₀ _))
          ((congrArg (fun q => q (κ z) ∈ P'.L.U j₀') e₂).mpr (h₀' _))]
        erw [Category.assoc, eSec_comp ψ.inv, hn, inv_one]) n a
      refine (existsUnique_congr fun b => ⟨fun h e Z r z j j' hj hj' => ?_, fun h e Z r z j' j hj' hj => ?_⟩).1 H
      · have m' := (congrArg (fun q : Z ⟶ P'.A.left => q z ∈ P'.L.U j') (congrArg (r ≫ ·) eB)).mpr hj'
        have := h e Z (r ≫ ψ.hom.left) z j' j m' hj
        rw [hu' Z (r ≫ ψ.hom.left) z j j' hj m'] at this
        simp only [Category.assoc] at this
        rw [eB, hi] at this
        erw [Category.comp_id] at this
        beta_reduce
        rw [this, ← _root_.mul_assoc, ← mul_pow, Units.mul_inv, one_pow, _root_.one_mul]
      · have m := (congrArg (fun q : Z ⟶ P.A.left => q z ∈ P.L.U j) (congrArg (r ≫ ·) eA)).mpr hj
        have := h e Z (r ≫ ψ.inv.left) z j j' m hj'
        simp only [Category.assoc] at this
        rw [eA] at this
        beta_reduce
        rw [hu' Z r z j j' hj hj', this, ← _root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.one_mul]
  have hF : (Over.pullback (jK R)).map Ψ.hom = ψ.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (ExtUnique.pullback_map_left_fst (jK R) Ψ.hom).trans hΨ.symm
    · exact (Over.w _).trans (Over.w _).symm
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R (FractionRing R)
  have := P'.isAb.smooth
  have := P.isAb.proper
  exact ⟨Ψ, ExtUnique.isMonHom_of_pullback (jK R) Ψ.hom (hF ▸ hψ), hF, hw⟩
