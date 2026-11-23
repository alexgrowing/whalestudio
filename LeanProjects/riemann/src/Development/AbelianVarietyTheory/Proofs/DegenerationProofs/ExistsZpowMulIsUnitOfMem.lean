import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValUnitNeZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.ZH.FrameNorm

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc TopologicalSpace

section Points
variable {K C : Type} [Field K] [Field C] [IsAlgClosed C] {Y : Scheme.{0}} {q : Y ⟶ Sp K} [LocallyOfFiniteType q]
  {σ : K →+* C}

variable (q σ) in

theorem exists_point_mem {Z : Set Y} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : Sp C ⟶ Y, x ≫ q = spMap σ ∧ ∀ w, x w ∈ Z := by
  have hs : Surjective (spMap σ) := ⟨fun y ↦ by
    obtain ⟨z⟩ : Nonempty ↥(Sp C) := inferInstance
    exact ⟨z, Subsingleton.elim _ _⟩⟩
  have hJ : JacobsonSpace ↥(pullback q (spMap σ)) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd q (spMap σ))
  obtain ⟨y, hy⟩ := hne
  obtain ⟨z₀, rfl⟩ := (pullback.fst q (spMap σ)).surjective y
  obtain ⟨z, hzZ, hz⟩ := nonempty_inter_closedPoints (Z := pullback.fst q (spMap σ) ⁻¹' Z) ⟨z₀, hy⟩
    (hZ.preimage (pullback.fst q (spMap σ)).continuous)
  replace hz : IsClosed {z} := hz
  refine ⟨pointOfClosedPoint (pullback.snd q (spMap σ)) z hz ≫ pullback.fst _ _,
    by rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc], fun w => ?_⟩
  rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  exact hzZ

theorem eq_of_val_eq [IsReduced Y] {W : Y.Opens} {r s : Γ(Y, W)}
    (h : ∀ x : Sp C ⟶ Y, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → valR x W r = valR x W s) : r = s := by
  rw [← sub_eq_zero]
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => ?_)
  obtain ⟨x, hx, hm⟩ := exists_point_mem q σ (Y.basicOpen (r - s)).isOpen.isLocallyClosed ⟨y, hy⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ W := fun w _ => Y.basicOpen_le _ (hm w)
  have := ((isUnit_valR_iff x W hW (r - s)).2 fun w _ => hm w).ne_zero
  rw [valR_eq x W hW, map_sub, ← valR_eq, ← valR_eq, h x hx hW, sub_self] at this
  exact (this rfl).elim

theorem isUnit_of_val_ne_zero {W : Y.Opens} {r : Γ(Y, W)}
    (h : ∀ x : Sp C ⟶ Y, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → valR x W r ≠ 0) : IsUnit r := by
  refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun y hy => (Scheme.mem_basicOpen _ _ y hy).1 ?_
  by_contra hn
  obtain ⟨x, hx, hm⟩ := exists_point_mem q σ
    (W.isOpen.isLocallyClosed.inter (Y.basicOpen r).isOpen.isClosed_compl.isLocallyClosed) ⟨y, hy, hn⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ W := fun w _ => (hm w).1
  obtain ⟨w⟩ : Nonempty ↥(Sp C) := inferInstance
  exact (hm w).2 ((isUnit_valR_iff x W hW r).1 (h x hx hW).isUnit (show w ∈ (⊤ : (Sp C).Opens) from trivial))

theorem exists_glue [IsReduced Y] {I : Type} (W : Y.Opens) (T : I → Y.Opens) (F : I → (Sp C ⟶ Y) → C)
    (hT : ∀ z, ∃ m, z ∈ T m) (hF : ∀ m, Reg q σ (W ⊓ T m) (F m))
    (h : ∀ m m' x, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ⊤ ≤ x ⁻¹ᵁ T m → ⊤ ≤ x ⁻¹ᵁ T m' → F m x = F m' x) :
    ∃ r : Γ(Y, W), ∀ m x, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ⊤ ≤ x ⁻¹ᵁ T m → F m x = valR x W r := by
  choose u hu using hF
  obtain ⟨r, hr, -⟩ := Y.sheaf.existsUnique_gluing' (fun m => W ⊓ T m) W (fun _ => homOfLE inf_le_left)
    (fun y hy => Opens.mem_iSup.2 ((hT y).imp fun _ hm => ⟨hy, hm⟩)) u
    (fun m m' => eq_of_val_eq (q := q) (σ := σ) (W := W ⊓ T m ⊓ (W ⊓ T m')) fun x hx hW =>
      (valR_res x inf_le_left hW _).trans ((hu m x hx fun _ hz => (hW hz).1).symm.trans
        ((h m m' x hx (fun _ hz => (hW hz).1.1) (fun _ hz => (hW hz).1.2) fun _ hz => (hW hz).2.2).trans
          ((hu m' x hx fun _ hz => (hW hz).2).trans (valR_res x inf_le_right hW _).symm))))
  refine ⟨r, fun m x hx hW hm => ?_⟩
  have hh : ⊤ ≤ x ⁻¹ᵁ (W ⊓ T m) := fun _ hz => ⟨hW hz, hm hz⟩
  rw [hu m x hx hh, ← hr m]
  exact valR_res x inf_le_left hh r

end Points

open GlobalTheory.PrimeSection in

theorem exists_zpow_mul_isUnit_of_mem {X : Scheme.{0}} {t : Γ(X, ⊤)} {ξ : X}
    (hη : ∀ x : X, x ∉ X.basicOpen t ↔ ξ ⤳ x)
    (hp : ∀ U : X.Opens, IsAffineOpen U → ξ ∈ U → Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
    [IsIntegral X] [IsLocallyNoetherian X] {A : Type} {U : A → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
    {a₀ : A} (h₀ : ξ ∈ U a₀) (hg : ∀ a b, IsUnit (g a b)) (τ : Γ(X, X.basicOpen t)ˣ)
    (hτ : (τ : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t)
    {r : ∀ a, Γ(X, U a ⊓ X.basicOpen t)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r b))
    (hru : ∀ a, IsUnit (r a)) :
    ∃ n : ℤ, ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      ∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a := by
  obtain ⟨hdvr, hirr⟩ := isDiscreteValuationRing_stalk hη hp
  have hD : genericPoint X ∈ X.basicOpen t := genericPoint_mem_basicOpen (ne_zero hp)
  have hx₀ : X.presheaf.germ _ _ (genericPoint_mem_inf hp h₀) (r a₀) ≠ 0 := ((hru a₀).map _).ne_zero
  have hτn : ∀ n : ℤ, X.presheaf.germ _ _ hD (↑(τ ^ n) : Γ(X, X.basicOpen t)) =
      algebraMap _ X.functionField (X.presheaf.germ ⊤ ξ trivial t) ^ n := fun n ↦ by
    rw [algebraMap_germ, ← germ_res (le_top : X.basicOpen t ≤ ⊤) hD, ← hτ]
    let φ : Γ(X, X.basicOpen t) →+* X.functionField := (X.presheaf.germ _ _ hD).hom
    change φ _ = φ _ ^ n
    rw [← MonoidHom.coe_coe, ← Units.coe_map, map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  obtain ⟨n, ⟨u, hu, hn⟩, -⟩ :=
    GlobalTheory.PrimeElement.existsUnique_zpow_mul_eq_unit (K := X.functionField) hirr hx₀
  have : ∀ a, ∃ s : Γ(X, U a), X.presheaf.map (homOfLE inf_le_left).op s =
      X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a :=
    fun a ↦ exists_res_eq hη hp _ fun h ↦
      ⟨X.presheaf.germ (U a ⊓ U a₀) ξ ⟨h, h₀⟩ (g a a₀) * u, by
        rw [map_mul, map_mul, hn, germ_res, hτn, algebraMap_germ,
          germ_eq_mul_germ hr (a := a) _ (genericPoint_mem_inf hp h₀)]
        ring⟩
  choose s hs using this
  have hs₀ : ξ ∈ X.basicOpen (s a₀) := by
    rw [X.mem_basicOpen _ ξ h₀]
    convert hu
    apply IsFractionRing.injective _ X.functionField
    have := congrArg (X.presheaf.germ _ _ (genericPoint_mem_inf hp h₀)) (hs a₀)
    rw [map_mul, germ_res, germ_res, hτn] at this
    rw [algebraMap_germ, hn, this]
  refine ⟨n, s, fun b ↦ isUnit_of_isUnit_res hη hp ?_ fun h ↦
    mem_basicOpen_of_compatible hg (compatible_of_res_eq hD hr _ hs) h hs₀, hs⟩
  rw [hs b]
  exact ((Units.isUnit _).map _).mul (hru b)

open GlobalTheory.DvrModel GlobalTheory.PrimeSection in

theorem norm_const : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (A I : Type) (U : A → H.Opens) (T : I → HK.Opens) (F : A → I → (Sp (PadicAlgCl p) ⟶ HK) → PadicAlgCl p), (∀ z, ∃ m, z ∈ T m) → (∀ a m, Reg q σ (j ⁻¹ᵁ U a ⊓ T m) (F a m)) → (∀ a m x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → F a m x ≠ 0) → (∀ a m m' x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → ⊤ ≤ x ⁻¹ᵁ T m' → F a m x = F a m' x) → (∀ a a', ∃ g : Γ(H, U a ⊓ U a')ˣ, ∀ m x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a' → ⊤ ≤ x ⁻¹ᵁ T m → F a m x = valR (x ≫ j) (U a ⊓ U a') g.val * F a' m x) → ∃ κ : ℝ, 0 < κ ∧ ∀ a m (c : Sp (OO p) ⟶ H) x, c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → ‖F a m x‖ = κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hsm hgi hK A I U T F hT hreg hne h₁ h₂
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hK
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hs
  have := isOpenImmersion_generic hK
  have := GlobalTheory.DvrModel.isIntegral hK
  have := GlobalTheory.DvrModel.isLocallyNoetherian f
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hK inferInstance
  have hη := notMem_basicOpen_iff_specializes hϖ hs
  by_cases hA : ∃ a₀, pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))) (genericPoint _) ∈ U a₀
  swap
  · refine ⟨1, one_pos, fun a m c x hc _ _ ha _ => (hA ⟨a, mem_of_notMem_basicOpen hη
      (ha (show IsLocalRing.closedPoint (OO p) ∈ (⊤ : (Sp (OO p)).Opens) from trivial)) ?_⟩).elim⟩
    rw [notMem_basicOpen_iff f hϖ, ← Scheme.Hom.comp_apply, hc]
    exact IsLocalRing.comap_closedPoint jV
  obtain ⟨a₀, h₀⟩ := hA
  choose r hr using fun a => exists_glue (j ⁻¹ᵁ U a) T (F a) hT (hreg a) (h₁ a)
  choose g hg using h₂
  have hpt : ∀ x : Sp (PadicAlgCl p) ⟶ HK, ∃ m, ⊤ ≤ x ⁻¹ᵁ T m := fun x =>
    (hT _).imp fun m hm => (top_le_iff x _).2 hm
  have hru : ∀ a, IsUnit (r a) := fun a => isUnit_of_val_ne_zero (q := q) (σ := σ) fun x hx hW => by
    obtain ⟨m, hm⟩ := hpt x
    rw [← hr a m x hx hW hm]
    exact hne a m x hx hW hm
  have h0 : algebraMap V K ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hϖ.ne_zero
  let φ : K →+* Γ(HK, ⊤) := q.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  obtain ⟨r', τ', hτ', hr', -, hu', E⟩ := exists_transport (opensRange_generic hϖ hK)
    (g := fun a b => (g a b).val) (fun a => rfl) r
    (fun a b => eq_of_val_eq (q := q) (σ := σ) fun x hx hW => by
      obtain ⟨m, hm⟩ := hpt x
      have ha : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U a := fun _ hz => (hW hz).1
      have hb : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U b := fun _ hz => (hW hz).2
      refine (valR_res x inf_le_left hW _).trans (((hr a m x hx ha hm).symm.trans (hg a b m x hx ha hb hm)).trans
        (Eq.symm ((valR_mul x _ hW _ _).trans (congrArg₂ (· * ·) (GlobalTheory.Points.valR_appLE x j _ hW _) ?_))))
      exact (valR_res x inf_le_right hW _).trans (hr b m x hx hb hm).symm)
    (Units.map φ.toMonoidHom (Units.mk0 _ h0)) (appTop_cst hK.w ϖ).symm
  obtain ⟨n, s, hsu, hs'⟩ := exists_zpow_mul_isUnit_of_mem hη (prime_res_generic hϖ hs) h₀
    (fun a b => (g a b).isUnit) τ' hτ' hr' fun a => hu' a (hru a)
  have hpos : 0 < ‖σ (algebraMap V K ϖ)‖ ^ n := zpow_pos (norm_pos_iff.2 ((map_ne_zero σ).2 h0)) n
  refine ⟨(‖σ (algebraMap V K ϖ)‖ ^ n)⁻¹, inv_pos.2 hpos, fun a m c x hc hx hq ha hm => ?_⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U a := by
    show ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a
    rw [hx]
    exact fun _ _ => ha trivial
  have e := congrArg (valR x _) ((E n a (s a)).1 (hs' a))
  have e₁ : valR x ⊤ (Units.map φ.toMonoidHom (Units.mk0 _ h0)).val = σ (algebraMap V K ϖ) :=
    (GlobalTheory.Points.valR_comp x q ⊤ _).symm.trans (by
      rw [hq]
      exact GlobalTheory.Points.valR_specMap (CommRingCat.ofHom σ) _)
  have e₂ : ((valR c (U a) (s a) : OO p) : PadicAlgCl p) = σ (algebraMap V K ϖ) ^ n * F a m x := by
    rw [hr a m x hq hW hm, ← e₁, ← val_zpow x (U := ⊤) (fun _ _ => trivial)]
    refine Eq.trans ?_ ((e.trans (valR_mul x _ hW _ _)).trans (congrArg (· * _) (valR_res x le_top hW _)))
    refine Eq.trans ?_ (GlobalTheory.Points.valR_appLE x j _ hW _).symm
    rw [hx]
    exact ((valR_spMap (OO p).subtype c _ ha).2 _).symm
  have e₃ : ‖((valR c (U a) (s a) : OO p) : PadicAlgCl p)‖ = 1 := by
    have hu : IsUnit (valR c (U a) (s a)) := by
      rw [valR_eq c _ ha]
      exact (hsu a).map _
    obtain ⟨d, hd⟩ := hu.exists_right_inv
    have e' := congrArg (fun z : OO p => ‖(z : PadicAlgCl p)‖) hd
    simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at e'
    exact le_antisymm ((mem_OO_iff _).1 (Subtype.prop _))
      (e'.ge.trans (mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 d.2)))
  rw [e₂, norm_mul, norm_zpow] at e₃
  exact eq_inv_of_mul_eq_one_right e₃

end GlobalTheory.ZH.FrameNorm
end
