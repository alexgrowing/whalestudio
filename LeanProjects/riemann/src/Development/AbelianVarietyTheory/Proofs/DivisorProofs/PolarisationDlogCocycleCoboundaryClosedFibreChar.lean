import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleConditionLogDerivativeTransition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfIsCoboundarySubcover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

namespace GlobalTheory.ChartCob

theorem resG_appLE {Y Z : Scheme.{0}} (f : Y ⟶ Z) {O : Z.Opens} {V V' : Y.Opens} (h : V ≤ f ⁻¹ᵁ O) (h' : V' ≤ V)
    (s : Γ(Z, O)) : resG Y h' ((f.appLE O V h).hom s) = (f.appLE O V' (h'.trans h)).hom s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_resG {Y Z : Scheme.{0}} (f : Y ⟶ Z) {O O' : Z.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ O') (h' : O' ≤ O)
    (s : Γ(Z, O)) :
    (f.appLE O' V h).hom (resG Z h' s) = (f.appLE O V (fun _ hx => h' (h hx))).hom s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem isCoc_pullback {Y Z : Scheme.{0}} (f : Y ⟶ Z) {J : Type} (W : J → Z.Opens)
    (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) (hc : GlobalTheory.CechFin.IsCoc W c) :
    GlobalTheory.CechFin.IsCoc (fun i => f ⁻¹ᵁ W i)
      (fun i i' => (f.appLE (W i ⊓ W i') (f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i')) := by
  intro i i' i''
  have h3 : f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i' ⊓ f ⁻¹ᵁ W i'' ≤ f ⁻¹ᵁ (W i ⊓ W i' ⊓ W i'') := fun _ hx => hx
  have e := congrArg (f.appLE (W i ⊓ W i' ⊓ W i'') (f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i' ⊓ f ⁻¹ᵁ W i'') h3).hom
    (hc i i' i'')
  rw [map_add, appLE_resG, appLE_resG, appLE_resG] at e
  exact (congrArg₂ (· + ·) (resG_appLE f _ _ _) (resG_appLE f _ _ _)).trans (e.trans (resG_appLE f _ _ _).symm)

theorem isCoc_sum {Z X : Scheme.{0}} (p : Z ⟶ X) (U : X.Opens) (L : LB Z) (hL : L.IsLB) {n : ℕ}
    (δ : Fin n → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) (hδ : ∀ a, IsField (p ⁻¹ᵁ U) (δ a))
    {J : Type} (W : J → Z.Opens) (j : J → L.ι) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U) (hj : ∀ i, W i ≤ L.U (j i))
    (r : Fin n → Γ(X, U)) :
    GlobalTheory.CechFin.IsCoc W (fun i i' => ∑ b, (p.appLE U (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) *
      (δ b (W i ⊓ W i') (resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i')).val) *
        resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i'))⁻¹.val)) := by
  intro i i' i''
  simp only [map_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e := GlobalTheory.DlogCocycle.dlog_cocycle Z L hL _ (δ b) (hδ b) J W j hWU hj i i' i''
  rw [map_mul (resG Z _) ((p.appLE _ _ _).hom _), map_mul (resG Z _) ((p.appLE _ _ _).hom _),
    map_mul (resG Z _) ((p.appLE _ _ _).hom _), resG_appLE, resG_appLE, resG_appLE, ← e, mul_add]

theorem isCob_pbT {Y Z : Scheme.{0}} (f : Y ⟶ Z) {I : Type} (V Ω : I → Z.Opens)
    (hle : ∀ a, f ⁻¹ᵁ V a ≤ f ⁻¹ᵁ Ω a) (c : ∀ a b : I, Γ(Z, Ω a ⊓ Ω b)) (h : ∀ a, Γ(Y, f ⁻¹ᵁ Ω a))
    (hh : ∀ a b, (f.appLE (Ω a ⊓ Ω b) (f ⁻¹ᵁ Ω a ⊓ f ⁻¹ᵁ Ω b) (fun _ hx => hx)).hom (c a b) =
      resG Y inf_le_left (h a) - resG Y inf_le_right (h b)) :
    GlobalTheory.KS.IsCob (fun a => f ⁻¹ᵁ V a) (fun a b => GlobalTheory.KS.pbT f (c a b) (f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b)) := by
  refine ⟨fun a => -resG Y (hle a) (h a), fun a b => ?_⟩
  have e := (resG_appLE f _ (inf_le_inf (hle a) (hle b)) _).symm.trans
    (congrArg (resG Y (inf_le_inf (hle a) (hle b))) (hh a b))
  rw [map_sub, GlobalTheory.DlogCocycle.resG_resG, GlobalTheory.DlogCocycle.resG_resG] at e
  have hab : f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b ≤ f ⁻¹ᵁ (Ω a ⊓ Ω b) := fun x hx => ⟨hle a hx.1, hle b hx.2⟩
  simp only [GlobalTheory.KS.pbT, GlobalTheory.KS.rsT]
  rw [dif_pos hab, dif_pos inf_le_left, dif_pos inf_le_right, map_neg, map_neg,
    GlobalTheory.DlogCocycle.resG_resG, GlobalTheory.DlogCocycle.resG_resG]
  refine e.trans ?_
  ring

theorem chart_isCob : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)) (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → GlobalTheory.KS.IsCob (fun a => ι ⁻¹ᵁ t.PP.L.U a) (fun a b => GlobalTheory.KS.pbT ι (∑ c, (t.G.hom.appLE U.1 ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (inf_le_left.trans inf_le_right)).hom (r c) * (δ c ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b).val) * resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b)⁻¹.val)) (ι ⁻¹ᵁ t.PP.L.U a ⊓ ι ⁻¹ᵁ t.PP.L.U b)) := by
  intro E _ _ _ H X t U n δ hδ J W j _ hsup hWU hj m A _ ι hι r h' hh'
  have htop : ∀ x : A.left, x ∈ ι ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    intro x
    have hw := hι.1.w
    have : x ∈ (ι ≫ t.G.hom) ⁻¹ᵁ U.1 := by
      rw [hw]
      show (A.hom ≫ spMap (Ideal.Quotient.mk m) ≫ chart U) x ∈ (U.1 : Set X)
      rw [← U.2.range_fromSpec]
      exact ⟨(A.hom ≫ spMap (Ideal.Quotient.mk m)) x, rfl⟩
    exact this
  let Ω : J ⊕ t.PP.L.ι → t.G.left.Opens := Sum.elim W (fun a => t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1)
  let jj : J ⊕ t.PP.L.ι → t.PP.L.ι := Sum.elim j id
  have hΩU : ∀ q, Ω q ≤ t.G.hom ⁻¹ᵁ U.1 := by
    rintro (i | a)
    · exact hWU i
    · exact inf_le_right
  have hΩj : ∀ q, Ω q ≤ t.PP.L.U (jj q) := by
    rintro (i | a)
    · exact hj i
    · exact inf_le_left
  have hc := isCoc_pullback ι Ω _ (isCoc_sum t.G.hom U.1 t.PP.L t.PP.isLB δ hδ Ω jj hΩU hΩj r)
  obtain ⟨h, hh⟩ := GlobalTheory.CechFin.isCob_of_isCob_subcover A.left (J ⊕ t.PP.L.ι) (fun q => ι ⁻¹ᵁ Ω q)
    (Set.range Sum.inl) (by
      intro q x _
      have hx : ι x ∈ ⨆ i, W i := by rw [hsup]; exact htop x
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨Sum.inl i, TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, rfl⟩, hi⟩⟩)
    _ hc (fun q => match q with | Sum.inl i => h' i | Sum.inr _ => 0) (by
      rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩
      exact hh' i i')
  exact isCob_pbT ι t.PP.L.U (fun a => t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) (fun a x hx => ⟨hx, htop x⟩) _
    (fun a => h (Sum.inr a)) (fun a b => hh (Sum.inr a) (Sum.inr b))

end GlobalTheory.ChartCob
