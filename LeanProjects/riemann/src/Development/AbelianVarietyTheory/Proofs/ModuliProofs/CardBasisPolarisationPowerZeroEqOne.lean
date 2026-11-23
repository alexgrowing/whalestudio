import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.RankZero

section
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)

theorem top_le_wchart (ψ : Fin 0 → (Y ⟶ X)) (j : Fin 0 → L.ι) : (⊤ : Y.Opens) ≤ LB.wchart L ψ j :=
  fun _ _ => Set.mem_iInter.2 fun k => k.elim0

theorem exists_fn (hL : L.IsLB) (hε : ∀ k, ε k = 0) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ f : Γ(Y, ⊤), ∀ y J, Good L y J → sval s (𝟙 Y) y J = gs (𝟙 Y) y ⊤ f := by
  have hF : FormEq φ ε (Fin.elim0 : Fin 0 → (Y ⟶ X)) (Fin.elim0 : Fin 0 → ℤ) := by
    intro U _ h
    simp [hε]
  obtain ⟨s', hs'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sec hL hF s
  refine ⟨(Y.presheaf.map (homOfLE (top_le_wchart (L := L) Fin.elim0 Fin.elim0)).op).hom (s'.f Fin.elim0),
    fun y J hJ => ?_⟩
  rw [← hs' Y (𝟙 Y) y J hJ, sval_of s' (𝟙 Y) y J Fin.elim0 (fun k => k.elim0)]
  exact (gs_res (𝟙 Y) y (top_le_wchart (L := L) Fin.elim0 Fin.elim0) trivial _).symm

theorem exists_sec_of_fn (hε : ∀ k, ε k = 0) (f : Γ(Y, ⊤)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ y J, Good L y J → sval s (𝟙 Y) y J = gs (𝟙 Y) y ⊤ f := by
  have hle : ∀ j : K → L.ι, LB.wchart L φ j ≤ ⊤ := fun _ => le_top
  have h1 : ∀ y j j', trF (L := L) φ ε (𝟙 Y) y j j' = 1 := fun y j j' => by simp [trF, hε]
  refine ⟨⟨fun j => (Y.presheaf.map (homOfLE (hle j)).op).hom f, fun (j j' : K → L.ι) => fn_ext fun y hy => ?_⟩,
    fun y J hJ => (gs_res (𝟙 Y) y (hle _) (hJ.mem φ (𝟙 Y)) f)⟩
  have hg : gm (𝟙 Y) y ((L.LinComb φ ε).U j ⊓ (L.LinComb φ ε).U j') ((L.LinComb φ ε).g j j') = 1 :=
    (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2).trans (h1 y j j')
  rw [gs_mul (𝟙 Y) y _ hy, gs_unit (𝟙 Y) y _ hy, hg, Units.val_one, _root_.one_mul]
  exact ((gs_res (𝟙 Y) y inf_le_left hy _).trans (gs_res (𝟙 Y) y (hle j) hy.1 f)).trans
    ((gs_res (𝟙 Y) y inf_le_right hy _).trans (gs_res (𝟙 Y) y (hle j') hy.2 f)).symm

end

theorem eq_one_of_existsUnique {Γ : Type} [CommRing Γ] [Nontrivial Γ] {n : ℕ} (β : Fin n → Γ)
    (h : ∀ a : Γ, ∃! c : Fin n → Γ, a = ∑ i, c i * β i) : n = 1 := by
  let F : (Fin n → Γ) →ₗ[Γ] Γ :=
    { toFun := fun c => ∑ i, c i * β i
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by simp [_root_.mul_assoc] }
  have hF : ∀ c, F c = ∑ i, c i * β i := fun _ => rfl
  have hb : Function.Bijective F := by
    refine ⟨fun c c' hcc => ?_, fun a => ?_⟩
    · obtain ⟨d, -, hd⟩ := h (F c)
      exact (hd c (hF c)).trans (hd c' (hcc.trans (hF c'))).symm
    · obtain ⟨c, hc, -⟩ := h a
      exact ⟨c, (hF c).trans hc.symm⟩
  have e := (LinearEquiv.ofBijective F hb).finrank_eq
  simpa using e

theorem eq_one_of_bijective {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (hL : L.IsLB) (T : Over Z)
    [Nontrivial Γ(T.left, ⊤)] (hb : Function.Bijective (fst T G).left.appTop.hom) {n : ℕ}
    (b : Fin n → LB.Sec (Out.LPow G L ((0 : ℕ) : ℤ) T)) (H : GlobalTheory.LN.BasisAlong G L 0 (𝟙 _) b) : n = 1 := by
  have hpull : ∀ (x : Γ(T.left, ⊤)) (y : (T ⊗ G).left),
      gs (fst T G).left y ⊤ x = gs (𝟙 _) y ⊤ ((fst T G).left.appTop.hom x) := fun x y => by
    have e := gs_pull (𝟙 _) (fst T G).left y ⊤ trivial x
    rw [Category.id_comp] at e
    exact e.symm
  have hρ : ∀ y : (T ⊗ G).left, ∃ ρ : Γ((T ⊗ G).left, ⊤) →+* (T ⊗ G).left.presheaf.stalk y,
      ∀ a, gs (𝟙 _) y ⊤ a = ρ a := fun y =>
    ⟨((T ⊗ G).left.presheaf.germ ((𝟙 (T ⊗ G).left) ⁻¹ᵁ ⊤) y trivial).hom.comp (Scheme.Hom.app (𝟙 (T ⊗ G).left) ⊤).hom,
      fun a => gs_eq _ y ⊤ trivial a⟩
  choose β' hβ' using fun i => exists_fn (L := L) (fun _ : Fin 1 => (snd T G).left) (fun _ => ((0 : ℕ) : ℤ)) hL
    (fun _ => rfl) (b i)
  choose β hβ using fun i => hb.2 (β' i)
  have hR : ∀ (c : Fin n → Γ(T.left, ⊤)) (z : (T ⊗ G).left) (J : ((T ⊗ G).left ⟶ G.left) → L.ι), Good L z J →
      ∑ i, gs (fst T G).left z ⊤ (c i) * sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left)
        (ε := fun _ => ((0 : ℕ) : ℤ)) (b i) (𝟙 T ▷ G).left z J
        = gs (𝟙 _) z ⊤ ((fst T G).left.appTop.hom (∑ i, c i * β i)) := by
    intro c z J hJ
    obtain ⟨ρ, hρz⟩ := hρ z
    rw [MonoidalCategory.id_whiskerRight, Over.id_left]
    simp only [hβ' _ z J hJ, hpull, hρz, map_sum, map_mul, hβ]
  have hiff : ∀ (a : Γ(T.left, ⊤)) (c : Fin n → Γ(T.left, ⊤)) (s : LB.Sec (Out.LPow G L ((0 : ℕ) : ℤ) T)),
      (∀ y J, Good L y J → sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => ((0 : ℕ) : ℤ))
        s (𝟙 _) y J = gs (𝟙 _) y ⊤ ((fst T G).left.appTop.hom a)) →
      (GlobalTheory.LN.Lin G L 0 (𝟙 T) b c s ↔ a = ∑ i, c i * β i) := by
    intro a c s hs
    constructor
    · intro hl
      apply hb.1
      apply fn_ext
      intro z _
      obtain ⟨J, hJ, -⟩ := exists_good L hL z (Fin.elim0 : Fin 0 → ((T ⊗ G).left ⟶ G.left)) Fin.elim0
        (fun a => a.elim0) (fun k => k.elim0)
      rw [← hs z J hJ, hl z J hJ, hR c z J hJ]
    · rintro rfl z J hJ
      rw [hs z J hJ, hR c z J hJ]
  refine eq_one_of_existsUnique β (fun a => ?_)
  obtain ⟨s, hs⟩ := exists_sec_of_fn (L := L) (fun _ : Fin 1 => (snd T G).left) (fun _ => ((0 : ℕ) : ℤ))
    (fun _ => rfl) ((fst T G).left.appTop.hom a)
  obtain ⟨c, hc, hcu⟩ := H s
  exact ⟨c, (hiff a c s hs).1 hc, fun c' hc' => hcu c' ((hiff a c' s hs).2 hc')⟩

end GlobalTheory.RankZero

theorem GlobalTheory.basisAlong_zero_card : Out.GlobalFnsSt → ∀ (R : Type) [CommRing R] [Nontrivial R] (P : Out.PolAV (Sp R)) (n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L ((0 : ℕ) : ℤ) (Over.mk (𝟙 (Sp R))))), GlobalTheory.LN.BasisAlong P.A P.L 0 (𝟙 _) b → n = 1 := by
  intro hG R _ _ P n b hB
  have : Nontrivial Γ((Over.mk (𝟙 (Sp R))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  refine GlobalTheory.RankZero.eq_one_of_bijective P.A P.L P.isLB (Over.mk (𝟙 (Sp R))) ?_ b hB
  have : IsIso (snd (Over.mk (𝟙 (Sp R))) P.A) := by
    change IsIso (snd (𝟙_ (Over (Sp R))) P.A)
    rw [← CartesianMonoidalCategory.leftUnitor_hom]
    infer_instance
  have : IsIso (snd (Over.mk (𝟙 (Sp R))) P.A).left :=
    (inferInstance : IsIso ((Over.forget _).map (snd (Over.mk (𝟙 (Sp R))) P.A)))
  have e1 : (fst (Over.mk (𝟙 (Sp R))) P.A).left = (snd (Over.mk (𝟙 (Sp R))) P.A).left ≫ P.A.hom := by
    have h1 : (fst (Over.mk (𝟙 (Sp R))) P.A).left ≫ 𝟙 (Sp R) = _ := Over.w (fst (Over.mk (𝟙 (Sp R))) P.A)
    have h2 := Over.w (snd (Over.mk (𝟙 (Sp R))) P.A)
    exact (Category.comp_id _).symm.trans (h1.trans h2.symm)
  have hc : ((snd (Over.mk (𝟙 (Sp R))) P.A).left ≫ P.A.hom).appTop =
      P.A.hom.appTop ≫ (snd (Over.mk (𝟙 (Sp R))) P.A).left.appTop := by
    simp
  have : IsIso (snd (Over.mk (𝟙 (Sp R))) P.A).left.appTop := by
    exact (inferInstance : IsIso ((snd (Over.mk (𝟙 (Sp R))) P.A).left.app ⊤))
  rw [e1, hc, CommRingCat.hom_comp, RingHom.coe_comp]
  exact Function.Bijective.comp (asIso (snd (Over.mk (𝟙 (Sp R))) P.A).left.appTop).commRingCatIsoToRingEquiv.bijective
    (@hG _ P.A P.grp P.isAb)

end
