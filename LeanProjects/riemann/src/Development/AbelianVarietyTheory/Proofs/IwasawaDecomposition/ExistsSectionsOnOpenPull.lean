import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnPowerOfLocalBases
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Reg GlobalTheory.FlagMod

noncomputable section
namespace GlobalTheory.ThetaPullChart

variable {X X' : Scheme.{0}}

theorem gs_piece {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) {V : X.Opens}
    (θ : Γ(X, V)) {W : X'.Opens} (a : L.ι) (i' : L'.ι) (h1 : W ≤ F ⁻¹ᵁ V)
    (h2 : W ≤ (L.pull F).U (fun _ => a) ⊓ L'.U i') (x : X') (hx : x ∈ W) :
    gs (𝟙 X') x W (resG X' h1 ((F.app V).hom θ) * resG X' h2 ((w.s (fun _ => a, i'))⁻¹).val) =
      gs F x V θ * ((gw w (𝟙 X') x a i')⁻¹).val := by
  rw [gs_mul (𝟙 X') x W hx]
  unfold resG
  have e2 := gs_res (𝟙 X') x h2 hx ((w.s (fun _ => a, i'))⁻¹).val
  rw [gs_res (𝟙 X') x h1 hx, gs_pull (𝟙 X') F x V (h1 hx), Category.id_comp]
  refine congrArg _ (e2.trans ?_)
  exact (gs_unit (𝟙 X') x _ (h2 hx) _).trans (congrArg Units.val (map_inv _ _))

theorem gs_secOn {L : LB X} {V : X.Opens} {θ : ∀ i, Γ(X, V ⊓ L.U i)} (hθ : θ ∈ secOn L V)
    {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (a b : L.ι) (hy : f y ∈ V ⊓ L.U a ⊓ L.U b) :
    gs f y _ (θ a) = (gm f y _ (L.g a b)).val * gs f y _ (θ b) := by
  have e := congrArg (gs f y (V ⊓ L.U a ⊓ L.U b)) (hθ a b)
  unfold resG at e
  rw [gs_mul f y _ hy, gs_res f y _ hy, gs_res f y _ hy, gs_res f y _ hy,
    gs_unit f y (L.U a ⊓ L.U b) ⟨hy.1.2, hy.2⟩] at e
  exact e

theorem units_mul_inv_cancel_left {R : Type*} [CommRing R] (u v : Rˣ) (s : R) :
    (u : R) * s * (((u * v)⁻¹ : Rˣ) : R) = s * ((v⁻¹ : Rˣ) : R) := by
  calc (u : R) * s * (((u * v)⁻¹ : Rˣ) : R) = s * ((v⁻¹ : Rˣ) : R) * ((u : R) * ((u⁻¹ : Rˣ) : R)) := by
        rw [mul_inv_rev, Units.val_mul]; ring
    _ = _ := by rw [Units.mul_inv, mul_one]

theorem exists_secOn_pull {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) {V : X.Opens} {V' : X'.Opens} (hV : V' ≤ F ⁻¹ᵁ V)
    {θ : ∀ i, Γ(X, V ⊓ L.U i)} (hθ : θ ∈ secOn L V) :
    ∃ θ' ∈ secOn L' V', ∀ (x : X') (a : L.ι) (i' : L'.ι), x ∈ V' → x ∈ L'.U i' → F x ∈ L.U a →
      gs (𝟙 X') x (V' ⊓ L'.U i') (θ' i') = gs F x (V ⊓ L.U a) (θ a) * ((gw w (𝟙 X') x a i')⁻¹).val := by
  have hP := (isGen_iff w).1 hw
  let T : L.ι → X'.Opens := fun a => V' ⊓ F ⁻¹ᵁ L.U a
  have h1 : ∀ a i', T a ⊓ L'.U i' ≤ F ⁻¹ᵁ (V ⊓ L.U a) := fun a i' x hx => ⟨hV hx.1.1, hx.1.2⟩
  have h2 : ∀ a i', T a ⊓ L'.U i' ≤ (L.pull F).U (fun _ => a) ⊓ L'.U i' :=
    fun a i' x hx => ⟨mem_pull.2 hx.1.2, hx.2⟩
  let σ : ∀ a i', Γ(X', T a ⊓ L'.U i') := fun a i' =>
    resG X' (h1 a i') ((F.app (V ⊓ L.U a)).hom (θ a)) * resG X' (h2 a i') ((w.s (fun _ => a, i'))⁻¹).val
  have hσg : ∀ a i' x (hx : x ∈ T a ⊓ L'.U i'),
      gs (𝟙 X') x _ (σ a i') = gs F x _ (θ a) * ((gw w (𝟙 X') x a i')⁻¹).val :=
    fun a i' x hx => gs_piece w (θ a) a i' (h1 a i') (h2 a i') x hx
  have hσ : ∀ a, σ a ∈ secOn L' (T a) := by
    intro a
    refine fun i' j' => fn_ext fun x hx => ?_
    have hxi : x ∈ T a ⊓ L'.U i' := hx.1
    have hxj : x ∈ T a ⊓ L'.U j' := ⟨hx.1.1, hx.2⟩
    unfold resG
    rw [gs_res (𝟙 X') x _ hx, hσg a i' x hxi, gs_mul (𝟙 X') x _ hx, gs_res (𝟙 X') x _ hx,
      gs_res (𝟙 X') x _ hx, hσg a j' x hxj, gs_unit (𝟙 X') x (L'.U i' ⊓ L'.U j') ⟨hx.1.2, hx.2⟩]
    have ha : (𝟙 X' ≫ F) x ∈ L.U a := hx.1.1.2
    have e := hP X' (𝟙 X') x a a i' j' ha ha hx.1.2 hx.2
    rw [gm_self hL _ x ha, one_mul] at e
    rw [e, mul_inv_rev, inv_inv, Units.val_mul]
    ring
  have hc : ∀ a b i', resG X' (inf_le_inf_right _ inf_le_left : (T a ⊓ T b) ⊓ L'.U i' ≤ T a ⊓ L'.U i') (σ a i') =
      resG X' (inf_le_inf_right _ inf_le_right : (T a ⊓ T b) ⊓ L'.U i' ≤ T b ⊓ L'.U i') (σ b i') := by
    intro a b i'
    refine fn_ext fun x hx => ?_
    unfold resG
    have hxa : x ∈ T a ⊓ L'.U i' := ⟨hx.1.1, hx.2⟩
    have hxb : x ∈ T b ⊓ L'.U i' := ⟨hx.1.2, hx.2⟩
    rw [gs_res (𝟙 X') x _ hx, gs_res (𝟙 X') x _ hx, hσg a i' x hxa, hσg b i' x hxb]
    have ha : (𝟙 X' ≫ F) x ∈ L.U a := hx.1.1.2
    have hb : (𝟙 X' ≫ F) x ∈ L.U b := hx.1.2.2
    have e := hP X' (𝟙 X') x a b i' i' ha hb hx.2 hx.2
    rw [gm_self hL' (𝟙 X') x hx.2, inv_one, mul_one, Category.id_comp] at e
    have eθ := gs_secOn hθ F x a b ⟨⟨hV hx.1.1.1, ha⟩, hb⟩
    rw [e, eθ]
    exact units_mul_inv_cancel_left _ _ _
  obtain ⟨τ, hτ, hτσ⟩ := GlobalTheory.ZH.exists_secOn_glue L' V' T (fun a => inf_le_left)
    (fun x hx => by obtain ⟨a, ha⟩ := exists_chart hL (F x); exact ⟨a, hx, ha⟩) σ hσ hc
  refine ⟨τ, hτ, fun x a i' hx hi' ha => ?_⟩
  have hxa : x ∈ T a ⊓ L'.U i' := ⟨⟨hx, ha⟩, hi'⟩
  rw [← hσg a i' x hxa, ← hτσ a i']
  unfold resG
  exact (gs_res (𝟙 X') x _ hxa _).symm

theorem mem_basicOpen_of_gs {x : X'} {W : X'.Opens} (hx : x ∈ W) (f : Γ(X', W))
    (h : IsUnit (gs (𝟙 X') x W f)) : x ∈ X'.basicOpen f := by
  rw [gs_eq (𝟙 X') x W hx] at h
  exact (X'.mem_basicOpen f x hx).2 h

theorem isUnit_gs_of_mem {F : X' ⟶ X} {V : X.Opens} (θ : Γ(X, V)) (x : X') (hx : F x ∈ X.basicOpen θ) :
    IsUnit (gs F x V θ) := by
  have h2 : x ∈ X'.basicOpen ((F.app V).hom θ) := by
    rw [← Scheme.preimage_basicOpen]; exact hx
  have h3 : x ∈ F ⁻¹ᵁ V := X'.basicOpen_le _ h2
  rw [gs_eq F x V h3]
  exact (X'.mem_basicOpen _ x h3).1 h2

theorem exists_theta_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (v : Y'.X ⟶ Y.X), SABMap Y'.t Y.t v → ∀ (M : MChart Y) (U' : Y'.X.Opens), U' ≤ v ⁻¹ᵁ M.U → ∃ θ : (∀ i, Γ(Y'.t.G.left, Y'.t.G.hom ⁻¹ᵁ U' ⊓ Y'.t.PP.L.U i)), θ ∈ secOn Y'.t.PP.L (Y'.t.G.hom ⁻¹ᵁ U') ∧ ∀ y ∈ U', ∃ (g : Y'.t.G.left) (i : Y'.t.PP.L.ι), Y'.t.G.hom g = y ∧ g ∈ Y'.t.G.left.basicOpen (θ i) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' v n M U' hU'
  obtain ⟨w, hw, -, -⟩ := n.lin
  have hsq : n.φ ≫ Y.t.G.hom = Y'.t.G.hom ≫ v := n.cart.1.w
  have hV : Y'.t.G.hom ⁻¹ᵁ U' ≤ n.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U) := fun x hx => by
    show Y.t.G.hom (n.φ x) ∈ M.U
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
    exact hU' hx
  obtain ⟨θ', hθ', hg⟩ := exists_secOn_pull Y.t.PP.isLB Y'.t.PP.isLB w hw hV M.θ_mem
  refine ⟨θ', hθ', fun y hy => ?_⟩
  obtain ⟨g, i, hgy, hgi⟩ := M.θ_ne (v y) (hU' hy)
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := Y.t.G.hom) (g := v) g y hgy
  let g' : Y'.t.G.left := n.cart.1.isoPullback.inv.base z
  have hg1 : n.φ g' = g := by
    show n.φ (n.cart.1.isoPullback.inv.base z) = g
    rw [← Scheme.Hom.comp_apply, n.cart.1.isoPullback_inv_fst, hz1]
  have hg2 : Y'.t.G.hom g' = y := by
    show Y'.t.G.hom (n.cart.1.isoPullback.inv.base z) = y
    rw [← Scheme.Hom.comp_apply, n.cart.1.isoPullback_inv_snd, hz2]
  obtain ⟨i', hi'⟩ := exists_chart Y'.t.PP.isLB g'
  have hgU : g ∈ Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U i := Y.t.G.left.basicOpen_le _ hgi
  have hx : g' ∈ Y'.t.G.hom ⁻¹ᵁ U' := by
    show Y'.t.G.hom g' ∈ U'
    rw [hg2]; exact hy
  refine ⟨g', i', hg2, mem_basicOpen_of_gs (W := Y'.t.G.hom ⁻¹ᵁ U' ⊓ Y'.t.PP.L.U i') ⟨hx, hi'⟩ _ ?_⟩
  have ha : n.φ g' ∈ Y.t.PP.L.U i := by rw [hg1]; exact hgU.2
  rw [hg g' i i' hx hi' ha]
  refine (isUnit_gs_of_mem _ g' ?_).mul (Units.isUnit _)
  rw [hg1]; exact hgi

end GlobalTheory.ThetaPullChart
