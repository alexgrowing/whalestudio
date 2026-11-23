import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.QuotientNorm

open TopologicalSpace

theorem exists_lb_of_cocycle {Y : Scheme.{0}} {K : Type} (V : K → Y.Opens) (hV : ⨆ i, V i = ⊤)
    (a : ∀ i, K → Γ(Y, V i)) (h₁ : ∀ i, a i i = 1) (hle : ∀ i j, Y.basicOpen (a i j) ≤ V j)
    (hc : ∀ i j k, resG Y (inf_le_left : V i ⊓ V j ≤ V i) (a i k) =
      resG Y (inf_le_left : V i ⊓ V j ≤ V i) (a i j) * resG Y (inf_le_right : V i ⊓ V j ≤ V j) (a j k)) :
    ∃ (L : LB Y) (σ : K → LB.Sec L), L.IsLB ∧ ∀ j, Out.nonzeroLocus (σ j) = V j := by
  have hu (i j) : IsUnit (resG Y (inf_le_left : V i ⊓ V j ≤ V i) (a i j)) :=
    IsUnit.of_mul_eq_one _ ((hc i j i).symm.trans (by rw [h₁, map_one]))
  have hg (i j) (y : Y) (hy : y ∈ V i ⊓ V j) :
      gs (𝟙 Y) y (V i ⊓ V j) (hu i j).unit.val = gs (𝟙 Y) y (V i) (a i j) := gs_res _ y _ hy _
  have hc' (i j k) (y : Y) (hy : y ∈ V i ⊓ V j) :
      gs (𝟙 Y) y (V i) (a i k) = gs (𝟙 Y) y (V i) (a i j) * gs (𝟙 Y) y (V j) (a j k) := by
    have e := congrArg (gs (𝟙 Y) y _) (hc i j k)
    rwa [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy] at e
  refine ⟨⟨K, V, fun i j => (hu i j).unit⟩, fun k => ⟨fun i => a i k, fun i j => hc i j k⟩,
    ⟨hV, fun i => Units.ext (fn_ext fun y hy => ?_), fun i j k => Units.ext (fn_ext fun y hy => ?_)⟩, fun j => ?_⟩
  · exact (gs_res (𝟙 Y) y (le_inf le_rfl le_rfl) hy _).trans ((hg i i y ⟨hy, hy⟩).trans (by rw [h₁]; rfl))
  · refine (gs_mul (𝟙 Y) y _ hy _ _).trans ?_
    refine (congrArg₂ (· * ·) ((gs_res (𝟙 Y) y inf_le_left hy _).trans (hg i j y hy.1))
      ((gs_res (𝟙 Y) y (le_inf (inf_le_left.trans inf_le_right) inf_le_right) hy _).trans
        (hg j k y ⟨hy.1.2, hy.2⟩))).trans ((hc' i j k y hy.1).symm.trans ?_)
    exact ((gs_res (𝟙 Y) y (le_inf (inf_le_left.trans inf_le_left) inf_le_right) hy _).trans
      (hg i k y ⟨hy.1.1, hy.2⟩)).symm
  · refine le_antisymm (iSup_le fun i => hle i j) (le_trans ?_ (basicOpen_le_nonzeroLocus _ j))
    exact (Y.basicOpen_of_isUnit (f := a j j) (h₁ j ▸ isUnit_one)).ge

variable {G : Type} [Group G] {X Y : Scheme.{0}} {ρ : G →* Aut X} {π : X ⟶ Y}

theorem eq_of_gs (h : IsAffineQuotient ρ π) {W : Y.Opens} {a b : Γ(Y, W)}
    (e : ∀ x, π x ∈ W → gs π x W a = gs π x W b) : a = b :=
  h.app_injective W (fn_ext fun x hx => (gs_pull (𝟙 X) π x W hx a).trans
    (((Category.id_comp π).symm ▸ e x hx :).trans (gs_pull (𝟙 X) π x W hx b).symm))

theorem exists_norm [Fintype G] (h : IsAffineQuotient ρ π) {W : Y.Opens} {D : X.Opens}
    (hD : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).hom ⁻¹ᵁ D) (r : Γ(X, D)) :
    ∃ a : Γ(Y, W), ∀ x, π x ∈ W → gs π x W a = ∏ g, gs (ρ g).hom x D r := by
  obtain ⟨a, ha⟩ := h.mem_range_app W (∏ g, (ρ g).hom.appLE D _ (hD g) r) fun k => ⟨h.preimage_le W k, by
    rw [map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight k) _ _ fun g => ?_
    have : (ρ (g * k)).hom = (ρ k).hom ≫ (ρ g).hom := by rw [map_mul]; rfl
    simp only [Equiv.coe_mulRight, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, this]⟩
  refine ⟨a, fun x hx => ?_⟩
  have e := gs_pull (𝟙 X) π x W hx a
  rw [Category.id_comp] at e
  rw [← e, show (π.app W).hom a = _ from ha, gs_eq (𝟙 X) x (π ⁻¹ᵁ W) hx, map_prod, map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  exact (gs_eq (𝟙 X) x (π ⁻¹ᵁ W) hx _).symm.trans ((gs_appLE _ D _ (hD g) (𝟙 X) x hx r).trans (by rw [Category.id_comp]))

theorem exists_affine_cover_of_quotient :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → X.IsSeparated → ∀ (L : LB X) (n : ℕ) (σ : Fin n → LB.Sec L), L.IsLB → (∀ i, IsAffineOpen (Out.nonzeroLocus (σ i))) → (∀ x : X, ∃ i, ∀ g, (ρ g).hom x ∈ Out.nonzeroLocus (σ i)) → (∃ (L : LB X') (n : ℕ) (σ : Fin n → LB.Sec L), L.IsLB ∧ (∀ i, IsAffineOpen (Out.nonzeroLocus (σ i))) ∧ ⨆ i, Out.nonzeroLocus (σ i) = ⊤) := by
  rintro G _ _ X Y ρ π H _ L n σ - haff hcov
  classical
  have := Fintype.ofFinite G
  obtain ⟨-, hsurj, -, -, hst⟩ := quotient_isIntegral_surjective_orbits G X Y ρ π H
  have h : IsAffineQuotient ρ π :=
    ⟨H.2.1, H.1, fun W => (H.2.2 W).1, fun W s hs => (H.2.2 W).2 s fun g _ => (hs g).2⟩
  let W : Fin n → X.Opens := fun i => ⨅ g, (ρ g).hom ⁻¹ᵁ Out.nonzeroLocus (σ i)
  have hW (i x) : x ∈ W i ↔ ∀ g, (ρ g).hom x ∈ Out.nonzeroLocus (σ i) := by
    change x ∈ ((W i : X.Opens) : Set X) ↔ _
    simp only [W, Opens.coe_iInf, Set.mem_iInter]
    rfl
  choose V hV using fun i => hst (W i) fun k => by
    ext x
    change (ρ k).hom x ∈ W i ↔ x ∈ W i
    simp only [hW, ← aut_map_mul_apply]
    exact ⟨fun e g => by simpa using e (g * k⁻¹), fun e g => e _⟩
  have hm (i x) : π x ∈ V i ↔ ∀ g, (ρ g).hom x ∈ Out.nonzeroLocus (σ i) := by
    rw [← hW, ← hV]; rfl
  choose r hr using fun i j => AmpleSpan.exists_isRatio (σ j) (σ i)
  choose a ha using fun i j => exists_norm h (W := V i) (D := Out.nonzeroLocus (σ i)) (fun g x hx => (hm i x).1 hx g) (r i j)
  have top : ⨆ i, V i = ⊤ := top_le_iff.1 fun y _ => by
    obtain ⟨x, rfl⟩ := π.surjective y
    obtain ⟨i, hi⟩ := hcov x
    exact Opens.mem_iSup.2 ⟨i, (hm i x).2 hi⟩
  have hc (i j k) (f : X ⟶ X) (x : X) (hi : f x ∈ Out.nonzeroLocus (σ i)) (hj : f x ∈ Out.nonzeroLocus (σ j)) :
      gs f x _ (r i k) = gs f x _ (r i j) * gs f x _ (r j k) := by
    obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus hi
    refine ((mem_nonzeroLocus_iff_pull _ f x hl).1 hi).mul_right_cancel ?_
    rw [← (hr i k).gs f x hi hl, (hr j k).gs f x hj hl, (hr i j).gs f x hi hl]
    ring
  obtain ⟨L', σ', hL', hσ'⟩ := exists_lb_of_cocycle V top a
    (fun i => eq_of_gs h fun x hx => by
      rw [ha i i x hx, AmpleSpan.gs_one' _ _ _ hx]
      refine Finset.prod_eq_one fun g _ => ?_
      have hi := (hm i x).1 hx g
      obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus hi
      refine ((mem_nonzeroLocus_iff_pull _ _ x hl).1 hi).mul_right_cancel ?_
      rw [← (hr i i).gs _ x hi hl, _root_.one_mul])
    (fun i j y hy => by
      obtain ⟨x, rfl⟩ := π.surjective y
      have hx : π x ∈ V i := Y.basicOpen_le _ hy
      have u := (LBGerm.isUnit_gs_iff π x _ hx _).2 hy
      rw [ha i j x hx, IsUnit.prod_univ_iff] at u
      refine (hm j x).2 fun g => ?_
      have := (LBGerm.isUnit_gs_iff _ x _ ((hm i x).1 hx g) _).1 (u g)
      rw [(hr i j).basicOpen] at this
      exact this.2)
    (fun i j k => eq_of_gs h fun x hx => by
      rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, ha i k x hx.1, ha i j x hx.1,
        ha j k x hx.2, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun g _ => hc i j k _ x ((hm i x).1 hx.1 g) ((hm j x).1 hx.2 g))
  refine ⟨L', n, σ', hL', fun i => ?_, by simp only [hσ', top]⟩
  rw [hσ']
  refine h.isAffineOpen_of_preimage ?_
  rw [hV]
  exact IsAffineOpen.iInf fun g => (haff i).preimage (show X ≅ X from ρ g).hom

end GlobalTheory.QuotientNorm
