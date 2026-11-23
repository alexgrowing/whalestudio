import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCompPG
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMaps
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TwRatio

theorem exists_ratio_gen {X A : Scheme.{0}} {M : LB X} {L₀ : LB A} (hM : M.IsLB) (hL₀ : L₀.IsLB)
    {K : Type} [Fintype K] (φ : K → (A ⟶ X)) (ε : K → ℤ) (F : A ⟶ X)
    (w : LB.Iso L₀ (LB.LinComb M φ ε)) (hw : w.IsGen) (W : LB.Iso L₀ (M.pull F)) (hW : W.IsGen) :
    ∃ τ : LB.Gen (LB.LinComb M (Sum.elim φ (fun _ : PUnit => F)) (Sum.elim ε (fun _ => -1))), τ.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) (J : (Z ⟶ X) → M.ι) (j' : L₀.ι), Good M z J → r z ∈ L₀.U j' →
        val τ r z J = gv w r z (fun k => J (r ≫ φ k)) j' * (gw W r z (J (r ≫ F)) j')⁻¹ := by
  classical
  have pW := (isGen_iff W).1 hW
  have l1 : ∀ (j : K ⊕ PUnit → M.ι) k, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤
      (LB.LinComb M φ ε).U (j ∘ Sum.inl) ⊓ L₀.U k := fun j k y hy =>
    ⟨Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy.1 (Sum.inl i), hy.2⟩
  have l2 : ∀ (j : K ⊕ PUnit → M.ι) k, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤
      (M.pull F).U (fun _ => j (Sum.inr PUnit.unit)) ⊓ L₀.U k := fun j k y hy =>
    ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 (Sum.inr PUnit.unit), hy.2⟩
  let u : ∀ (j : K ⊕ PUnit → M.ι) k, Γ(A, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k)ˣ := fun j k =>
    res (l1 j k) (w.s (j ∘ Sum.inl, k)) * (res (l2 j k) (W.s (fun _ => j (Sum.inr PUnit.unit), k)))⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) j k, r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k →
      gm r z _ (u j k) = gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ :=
    fun Z r z j k hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv _ _).trans (congrArg _ (gm_res r z _ hz _))))
  have rel : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) (j j' : K ⊕ PUnit → M.ι) (k k' : L₀.ι),
      r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j → r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j' →
      r z ∈ L₀.U k → r z ∈ L₀.U k' →
      gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ =
        trF (Sum.elim φ (fun _ : PUnit => F)) (Sum.elim ε (fun _ => -1)) r z j j' *
          (gv w r z (j' ∘ Sum.inl) k' * (gw W r z (j' (Sum.inr PUnit.unit)) k')⁻¹) := by
    intro Z r z j j' k k' hj hj' hk hk'
    have key : ∀ {G : Type} [CommGroup G] (a c d x y : G), a * c⁻¹ * x * (d * c⁻¹ * y)⁻¹ = a * d⁻¹ * (x * y⁻¹) :=
      fun a c d x y => by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
    have a₁ : r z ∈ (LB.LinComb M φ ε).U (j ∘ Sum.inl) := Set.mem_iInter.2 fun i => Set.mem_iInter.1 hj (Sum.inl i)
    have a₂ : r z ∈ (LB.LinComb M φ ε).U (j' ∘ Sum.inl) := Set.mem_iInter.2 fun i => Set.mem_iInter.1 hj' (Sum.inl i)
    have b₁ : F (r z) ∈ M.U (j (Sum.inr PUnit.unit)) := Set.mem_iInter.1 hj (Sum.inr PUnit.unit)
    have b₂ : F (r z) ∈ M.U (j' (Sum.inr PUnit.unit)) := Set.mem_iInter.1 hj' (Sum.inr PUnit.unit)
    have e := gm_linComb M φ ε r z _ _ a₁ a₂
    rw [gm_isGen hw r z _ _ k k' a₁ a₂ hk hk', pW Z r z _ _ k k' b₁ b₂ hk hk']
    erw [e]
    rw [trF, Fintype.prod_sum_type]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, zpow_neg, zpow_one]
    exact key _ _ _ _ _
  have glue : ∀ j : K ⊕ PUnit → M.ι, ∃ s : Γ(A, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j)ˣ,
      ∀ k, res (inf_le_left : LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤ _) s = u j k := fun j =>
    glue_unit _ (fun k => LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k) (fun _ => inf_le_left)
      (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL₀ y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩) (u j)
      (fun k k' y hy => by
        rw [hu _ _ y j k hy.1, hu _ _ y j k' hy.2, rel _ (𝟙 A) y j j k k' hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          trF_self hM _ _ (𝟙 A) y hy.1.1, _root_.one_mul])
  choose s hs using glue
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) j k, r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j →
      r z ∈ L₀.U k → gm r z _ (s j) = gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ :=
    fun Z r z j k hj hk => (gm_res r z _ (show r z ∈ _ ⊓ L₀.U k from ⟨hj, hk⟩) (s j)).symm.trans
      ((congrArg (gm r z _) (hs j k)).trans (hu Z r z j k ⟨hj, hk⟩))
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z J j' hJ hj' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL₀ y
    exact (hv _ (𝟙 A) y j k hj hk).trans ((rel _ (𝟙 A) y j j' k k hj hj' hk hk).trans
      (congrArg _ (hv _ (𝟙 A) y j' k hj' hk).symm))
  · exact hv Z r z _ j' (hJ.mem _ r) hj'

end GlobalTheory.MumCmp.TwRatio

namespace GlobalTheory.MumCmp.TwRatio

theorem exists_twist_ratio : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β b) GlobalTheory.MumCmp.twε)) (hw : w.IsGen)
    (W : LB.Iso D₀.P.L (D.P.L.pull (GlobalTheory.MumCmp.twφ D₀ D β b 0))) (hW : W.IsGen),
    ∃ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D₀.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (j' : D₀.P.L.ι),
        Geo.Tor.Good D.P.L z J → r z ∈ D₀.P.L.U j' →
        Geo.Tor.gv w r z (fun i => J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b i)) j' =
          Geo.Tor.gw W r z (J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b 0)) j' * Geo.Tor.val ν (r ≫ D₀.P.A.hom) z J := by
  intro R _ _ _ D₀ D β b w hw W hW
  classical
  obtain ⟨τ, hτ, vτ⟩ := exists_ratio_gen D.P.isLB D₀.P.isLB (GlobalTheory.MumCmp.twφ D₀ D β b) GlobalTheory.MumCmp.twε
    (GlobalTheory.MumCmp.twφ D₀ D β b 0) w hw W hW
  obtain ⟨t₀, ht₀⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := Fin 2) ![b.left, η[D.P.A].left] ![-1, 1]
  have hF : FormEq (Sum.elim (GlobalTheory.MumCmp.twφ D₀ D β b) (fun _ : PUnit => GlobalTheory.MumCmp.twφ D₀ D β b 0))
      (Sum.elim GlobalTheory.MumCmp.twε (fun _ => -1))
      (fun k => D₀.P.A.hom ≫ (![b.left, η[D.P.A].left] : Fin 2 → ((𝟙_ (Over (Sp R))).left ⟶ D.P.A.left)) k)
      ![-1, 1] := by
    intro U _ h
    have e1 : GlobalTheory.MumCmp.twφ D₀ D β b 1 = D₀.P.A.hom ≫ b.left := rfl
    have e2 : GlobalTheory.MumCmp.twφ D₀ D β b 2 = D₀.P.A.hom ≫ η[D.P.A].left := rfl
    rw [Fintype.prod_sum_type, Fin.prod_univ_three, Fin.prod_univ_two]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, e1, e2, GlobalTheory.MumCmp.twε, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨τ', hτ', vτ'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen D.P.isLB hF τ hτ
  obtain ⟨a, ha⟩ := GlobalTheory.AbPackage.exists_unit_ratio D.P.isLB hτ' (DVR.pullGen_isGen _ _ _ t₀ ht₀ D₀.P.A.hom)
  have hG := GlobalTheory.globalFns_holds _ D₀.P.A D₀.P.isAb
  obtain ⟨c, hc⟩ := hG.2 a.val
  obtain ⟨c', hc'⟩ := hG.2 (a⁻¹).val
  have hcc : c * c' = 1 := hG.1 (by rw [map_mul, hc, hc', Units.mul_inv, map_one])
  let cu : Γ(Sp R, ⊤)ˣ := ⟨c, c', hcc, (mul_comm c' c).trans hcc⟩
  have hcu : pullU D₀.P.A.hom ⊤ cu = a := Units.ext hc
  obtain ⟨ν, hν, vν⟩ := GlobalTheory.TorsionTranslate.exists_scale t₀ ht₀ cu
  refine ⟨ν, hν, fun Z r z J j' hJ hj' => ?_⟩
  have e1 := vτ Z r z J j' hJ hj'
  have e2 := vτ' Z r z J hJ
  have e3 := ha Z r z J hJ
  have e4 := val_pull hJ t₀ D₀.P.A.hom r
  have e5 := vν Z (r ≫ D₀.P.A.hom) z J hJ
  have e6 : gm r z ⊤ a = gm (r ≫ D₀.P.A.hom) z ⊤ cu := by
    rw [← hcu]; exact gm_pull r D₀.P.A.hom z ⊤ trivial cu
  rw [e5, ← e6, ← e4, ← e3, e2, e1, mul_left_comm, mul_inv_cancel, _root_.mul_one]

end GlobalTheory.MumCmp.TwRatio
