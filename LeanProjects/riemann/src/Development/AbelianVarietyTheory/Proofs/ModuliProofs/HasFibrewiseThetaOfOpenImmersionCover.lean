import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperRestrictPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ThetaLocal

open GlobalTheory.AbLocusPull

variable {X X' : Scheme.{0}}

theorem fn_ext_of_isOpenImmersion (F : X' ⟶ X) [IsOpenImmersion F] {U : X.Opens} (hU : U ≤ F.opensRange)
    {a b : Γ(X, U)} (h : ∀ x, F x ∈ U → gs F x U a = gs F x U b) : a = b := by
  have := F.isIso_app U hU
  apply (ConcreteCategory.bijective_of_isIso (F.app U)).1
  refine fn_ext fun x hx => ?_
  have e₁ := gs_pull (𝟙 X') F x U hx a
  have e₂ := gs_pull (𝟙 X') F x U hx b
  rw [Category.id_comp] at e₁ e₂
  exact e₁.trans ((h x hx).trans e₂.symm)

theorem exists_fn_of_isOpenImmersion (F : X' ⟶ X) [IsOpenImmersion F] {U : X.Opens} (hU : U ≤ F.opensRange)
    (b : Γ(X', F ⁻¹ᵁ U)) : ∃ a : Γ(X, U), ∀ x, F x ∈ U → gs F x U a = gs (𝟙 X') x _ b := by
  have := F.isIso_app U hU
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (F.app U)).2 b
  refine ⟨a, fun x hx => ?_⟩
  have e₁ := gs_pull (𝟙 X') F x U hx a
  rw [Category.id_comp] at e₁
  exact e₁.symm

theorem exists_secOn_push {F : X' ⟶ X} [IsOpenImmersion F] {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F)) {W : X.Opens} {W' : X'.Opens} (hr : W ≤ F.opensRange) (hW : F ⁻¹ᵁ W ≤ W')
    {θ' : ∀ k, Γ(X', W' ⊓ L'.U k)} (hθ' : θ' ∈ secOn L' W') :
    ∃ θ ∈ secOn L W, ∀ x, F x ∈ W → ∀ j k, F x ∈ L.U j → x ∈ X'.basicOpen (θ' k) → F x ∈ X.basicOpen (θ j) := by
  obtain ⟨w, hw⟩ := hw
  have hw := (isGen_iff w).1 hw
  have rel : ∀ (x : X') j j' k k', F x ∈ W → F x ∈ L.U j → F x ∈ L.U j' → x ∈ L'.U k → x ∈ L'.U k' →
      (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) =
        (gm F x (L.U j ⊓ L.U j') (L.g j j')).val * ((gw w (𝟙 X') x j' k').val * gs (𝟙 X') x _ (θ' k')) := by
    intro x j j' k k' hx hj hj' hk hk'
    have e := hw _ (𝟙 X') x j j' k k' hj hj' hk hk'
    rw [Category.id_comp] at e
    rw [gs_secOn hθ' (𝟙 X') x k k' (hW hx) hk hk', e, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
      ← Units.val_mul]
    congr 2
    rw [mul_right_comm, inv_mul_cancel_right]
  have ex : ∀ j, ∃ a : Γ(X, W ⊓ L.U j), ∀ x k, F x ∈ W → F x ∈ L.U j → x ∈ L'.U k →
      gs F x _ a = (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) := by
    intro j
    let O : L'.ι → X'.Opens := fun k => F ⁻¹ᵁ W ⊓ ((L.pull F).U (fun _ => j) ⊓ L'.U k)
    have le : ∀ k, O k ≤ W' ⊓ L'.U k := fun k x hx => ⟨hW hx.1, hx.2.2⟩
    let u : ∀ k, Γ(X', (L.pull F).U (fun _ => j) ⊓ L'.U k)ˣ := fun k => w.s (fun _ => j, k)
    let a : ∀ k, Γ(X', O k) := fun k => resG X' inf_le_right (u k).val * resG X' (le k) (θ' k)
    have va : ∀ x k, x ∈ O k → gs (𝟙 X') x _ (a k) = (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) := by
      intro x k hx
      refine (gs_mul _ x _ hx _ _).trans ?_
      rw [gs_res _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ hx.2]
      rfl
    obtain ⟨b, hb⟩ := glue_fn (F ⁻¹ᵁ (W ⊓ L.U j)) O (fun k x hx => ⟨hx.1, mem_pull.1 hx.2.1⟩)
      (fun x hx => (exists_chart hL' x).imp fun k hk => ⟨hx.1, mem_pull.2 hx.2, hk⟩) a (fun k k' x hk hk' => by
        rw [va x k hk, va x k' hk', rel x j j k k' hk.1 (mem_pull.1 hk.2.1) (mem_pull.1 hk.2.1) hk.2.2 hk'.2.2,
          gm_self hL F x (mem_pull.1 hk.2.1), Units.val_one, _root_.one_mul])
    obtain ⟨c, hc⟩ := exists_fn_of_isOpenImmersion F (inf_le_left.trans hr) b
    refine ⟨c, fun x k hx hj hk => ?_⟩
    have hm : x ∈ O k := ⟨hx, mem_pull.2 hj, hk⟩
    exact (hc x ⟨hx, hj⟩).trans ((hb x k hm).trans (va x k hm))
  choose θ hθ using ex
  refine ⟨θ, fun j j' => fn_ext_of_isOpenImmersion F (inf_le_left.trans (inf_le_left.trans hr)) fun x hx => ?_,
    fun x hx j k hj hk => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL' x
    rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx,
      gs_unit F x (L.U j ⊓ L.U j') ⟨hx.1.2, hx.2⟩, hθ j x k hx.1.1 hx.1.2 hk, hθ j' x k hx.1.1 hx.2 hk]
    exact rel x j j' k k hx.1.1 hx.1.2 hx.2 hk hk
  · have hm : x ∈ W' ⊓ L'.U k := X'.basicOpen_le _ hk
    refine (isUnit_gs_iff F x (W ⊓ L.U j) ⟨hx, hj⟩ _).1 ?_
    rw [hθ j x k hx hj hm.2]
    exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 X') x _ hm _).2 hk)

theorem hasTheta_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, HasTheta (u i).G (u i).PP.L) → HasTheta t.G t.PP.L := by
  intro E _ _ _ H Z t I Y f u m hf hc hu z
  obtain ⟨i, y, rfl⟩ := hc z
  have := hf i
  have h := (m i).cart.1
  have : IsOpenImmersion (m i).cm.F := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip ‹_›
  obtain ⟨w, g, -⟩ := (m i).lin
  have sq : ∀ x, t.G.hom ((m i).cm.F x) = f i ((u i).G.hom x) := fun x => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  obtain ⟨V, hy, θ', hθ', hne⟩ := hu i y
  have hr : t.G.hom ⁻¹ᵁ (f i ''ᵁ V) ≤ (m i).cm.F.opensRange := by
    rintro x ⟨y', -, e⟩
    obtain ⟨x', h₁, -⟩ := Scheme.exists_preimage_of_isPullback h x y' e.symm
    exact ⟨x', h₁⟩
  have hW : (m i).cm.F ⁻¹ᵁ (t.G.hom ⁻¹ᵁ (f i ''ᵁ V)) ≤ (u i).G.hom ⁻¹ᵁ V := by
    rintro x ⟨y', hy', e⟩
    have e' : y' = (u i).G.hom x := (f i).isOpenEmbedding.injective (e.trans (sq x))
    show (u i).G.hom x ∈ V
    rw [← e']; exact hy'
  obtain ⟨θ, hθ, hb⟩ := exists_secOn_push t.PP.isLB (u i).PP.isLB ⟨w, g⟩ hr hW hθ'
  refine ⟨f i ''ᵁ V, ⟨y, hy, rfl⟩, θ, hθ, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  obtain ⟨x, k, hx, hk⟩ := hne y' hy'
  obtain ⟨j, hj⟩ := exists_chart t.PP.isLB ((m i).cm.F x)
  refine ⟨(m i).cm.F x, j, (sq x).trans (congrArg _ hx), hb x ⟨y', hy', ?_⟩ j k hj hk⟩
  exact ((sq x).trans (congrArg _ hx)).symm

end GlobalTheory.ThetaLocal

end
