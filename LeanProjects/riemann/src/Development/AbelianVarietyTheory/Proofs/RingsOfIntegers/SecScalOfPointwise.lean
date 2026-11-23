import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxFamScalar

section Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X X' Y Y' W W' Z : Scheme.{0}}

theorem sval_of_secScal {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  unfold GeneratorPullback.SecScal resTop at H
  have hV : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have hW : h (r z) ∈ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hV.2 k
  have hc : LB.Coh L (Sum.elim φ₁ fun k => h ≫ φ₂ k)
      (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := by
    rintro (a | a) (b | b) e <;> simp only [Sum.elim_inl, Sum.elim_inr] at e ⊢ <;> rw [e]
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc]),
    sval_of s₁ r z J (fun k => J (r ≫ φ₁ k)) (fun k => rfl)]
  calc _ = _ := (gs_pull r h z _ hW _).symm
    _ = _ := (gs_res r z _ hV _).symm
    _ = _ := congrArg (gs r z _) (H _ _ hc)
    _ = _ := gs_mul r z _ hV _ _
    _ = _ := congrArg₂ (· * ·) (gs_res r z _ hV _) (gs_res r z _ hV _)

theorem secScal_of_pointwise {L : LB X} (hL : L.IsLB) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : ∀ (y : Y') (J : (Y' ⟶ X) → L.ι), Good L y J →
      sval s₂ (𝟙 Y' ≫ h) y J = gs (𝟙 Y') y ⊤ c * sval s₁ (𝟙 Y') y J) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c := by
  unfold GeneratorPullback.SecScal resTop
  intro j₁ j₂ hc
  apply fn_ext
  intro y hy
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL y (Sum.elim φ₁ fun k => h ≫ φ₂ k) (Sum.elim j₁ j₂) hc (by
    rintro (k | k)
    · exact Set.mem_iInter.1 hy.1 k
    · exact Set.mem_iInter.1 hy.2 k)
  have hW : h y ∈ LB.wchart L φ₂ j₂ := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
  have e := H y J hJ
  rw [sval_of s₂ (𝟙 Y' ≫ h) y J j₂ (fun k => by simpa using hJj (Sum.inr k)),
    sval_of s₁ (𝟙 Y') y J j₁ (fun k => by simpa using hJj (Sum.inl k))] at e
  calc _ = _ := gs_res _ y _ hy _
    _ = _ := gs_pull _ h y _ hW _
    _ = _ := e
    _ = _ := (congrArg₂ (· * ·) (gs_res _ y _ hy _) (gs_res _ y _ hy _)).symm
    _ = _ := (gs_mul _ y _ hy _ _).symm

variable {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem box_sval (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')}
    {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y' ⟶ Y)}
    (hφ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (s' : LB.Sec (LB.LinComb M' φ' ε))
    (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (hle : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι) i,
      LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM ≤
        ρ i ⁻¹ᵁ LB.wchart M (φ i) (fun a => jN a i))
    (H : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι),
      (@id (Γ(Y', LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
        ((LB.linCombIso w φ' ε).s (jN, jM))).val * rs inf_le_right (s'.f jM) =
        ∏ i, rs (hle jN jM i) (((ρ i).app _).hom ((s i).f (fun a => jN a i))))
    (q : Z ⟶ Y') (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (q ≫ φ' a) y (fun i => J ((q ≫ φ' a) ≫ pr i)) (J' (q ≫ φ' a)) ^ ε a).val * sval s' q y J' =
      ∏ i, sval (s i) (q ≫ ρ i) y J := by
  have hq : q y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (q ≫ φ' a)) :=
    ⟨Good.mem (L := LB.LinComb M pr (fun _ => 1)) (J := fun ψ i => J (ψ ≫ pr i)) (fun ψ => hJ.mem pr ψ) φ' q,
      hJ'.mem φ' q⟩
  have key := congrArg (gs q y _) (H (fun a i => J ((q ≫ φ' a) ≫ pr i)) (fun a => J' (q ≫ φ' a)))
  calc _ = _ := congrArg (fun u => (∏ a, bw w (q ≫ φ' a) y (fun i => J ((q ≫ φ' a) ≫ pr i)) (J' (q ≫ φ' a)) ^ ε a).val * u)
          ((sval_of s' q y J' _ (fun a => rfl)).trans (gs_res q y _ hq _).symm)
    _ = _ := congrArg (· * _) (congrArg Units.val (gm_linCombIso w φ' ε q y _ _ hq).symm)
    _ = _ := congrArg (· * _) (gs_unit q y _ hq _).symm
    _ = _ := (gs_mul q y _ hq _ _).symm
    _ = _ := key
    _ = _ := gs_prod q y _ hq Finset.univ _
    _ = _ := Finset.prod_congr rfl fun i _ =>
          ((gs_res q y _ hq _).trans (gs_pull q (ρ i) y _ (hle _ _ i hq) _)).trans
            (sval_of (s i) (q ≫ ρ i) y J _ (fun a => by simp only [Category.assoc, hφ])).symm

theorem gs_scal {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  unfold scal
  have e := gs_pull (𝟙 Z) r z ⊤ trivial ((Scheme.Hom.appTop p).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))
  rw [Category.id_comp] at e
  rw [← e, Scheme.Hom.comp_appTop]
  rfl

theorem gs_scal_prod {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (p' : Y' ⟶ Spec (CommRingCat.of R))
    (ρ : Fin j → (Y' ⟶ Y)) (hρ : ∀ i, ρ i ≫ p = p') (y : Y') (r : Fin j → R) :
    ∏ i, gs (𝟙 _ ≫ ρ i) y ⊤ (scal p (r i)) = gs (𝟙 _) y ⊤ (scal p' (∏ i, r i)) := by
  have hsc : (∏ i, scal p' (r i)) = scal p' (∏ i, r i) := by
    simp only [scal, map_prod]
  rw [← hsc, gs_prod (𝟙 _) y ⊤ trivial Finset.univ]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gs_scal, Category.id_comp, hρ]

theorem secScal_box (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    {K : Type} [Fintype K] {ε : K → ℤ}
    {φ' : K → (Y' ⟶ X')} {φ : Fin j → K → (Y ⟶ X)} {ρ : Fin j → (Y' ⟶ Y)}
    {ψ' : K → (W' ⟶ X')} {ψ : Fin j → K → (W ⟶ X)} {σ : Fin j → (W' ⟶ W)}
    {h' : Y' ⟶ W'} {h : Y ⟶ W} (e' : ∀ a, φ' a = h' ≫ ψ' a) (e : ∀ i, h' ≫ σ i = ρ i ≫ h)
    (s' : LB.Sec (LB.LinComb M' φ' ε)) (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (t' : LB.Sec (LB.LinComb M' ψ' ε)) (t : ∀ i, LB.Sec (LB.LinComb M (ψ i) ε))
    (Hs : ∀ (y : Y') J J', Good M y J → Good M' y J' →
      (∏ a, bw w (𝟙 Y' ≫ φ' a) y (fun i => J ((𝟙 Y' ≫ φ' a) ≫ pr i)) (J' (𝟙 Y' ≫ φ' a)) ^ ε a).val *
        sval s' (𝟙 Y') y J' = ∏ i, sval (s i) (𝟙 Y' ≫ ρ i) y J)
    (Ht : ∀ (y : Y') J J', Good M y J → Good M' y J' →
      (∏ a, bw w (h' ≫ ψ' a) y (fun i => J ((h' ≫ ψ' a) ≫ pr i)) (J' (h' ≫ ψ' a)) ^ ε a).val *
        sval t' h' y J' = ∏ i, sval (t i) (h' ≫ σ i) y J)
    (c : Fin j → Γ(Y, ⊤)) (c' : Γ(Y', ⊤))
    (hc : ∀ y : Y', ∏ i, gs (𝟙 _ ≫ ρ i) y ⊤ (c i) = gs (𝟙 _) y ⊤ c')
    (H : ∀ i, GeneratorPullback.SecScal M (φ i) ε (s i) (ψ i) ε (t i) h (c i)) :
    GeneratorPullback.SecScal M' φ' ε s' ψ' ε t' h' c' := by
  apply secScal_of_pointwise hM'
  intro y J' hJ'
  obtain ⟨J, hJ, -⟩ := exists_good M hM y (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)
  have hs := Hs y J J' hJ hJ'
  have ht := Ht y J J' hJ hJ'
  have hci := hc y
  have hH : ∀ i, sval (t i) (h' ≫ σ i) y J = gs (𝟙 Y' ≫ ρ i) y ⊤ (c i) * sval (s i) (𝟙 Y' ≫ ρ i) y J :=
    fun i => by rw [← sval_of_secScal (H i) (𝟙 Y' ≫ ρ i) y hJ, Category.id_comp, ← e i]
  simp only [Category.id_comp] at hs hH hci ⊢
  simp only [← e'] at ht
  refine (Units.isUnit (∏ a, bw w (φ' a) y (fun i => J (φ' a ≫ pr i)) (J' (φ' a)) ^ ε a)).mul_left_cancel ?_
  rw [ht, Finset.prod_congr rfl (fun i _ => hH i), Finset.prod_mul_distrib, hci, ← hs, mul_left_comm]

end Generic

set_option maxHeartbeats 800000 in

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (pD : IsPowDeg D'.toPre D.toPre j) (k : ℕ) (Fs : Fin j → Fam D.toPre (FractionRing R) k) (f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α) (r : Fin j → R), (∀ i α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((Fs i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom (r i))) → ∀ (F' : Fam D'.toPre (FractionRing R) k), IsBoxFam pD (FractionRing R) k F' Fs → ∀ α' : D'.toPre.X, GeneratorPullback.SecScal D'.toPre.P.L (DegPre.famφ D'.toPre (FractionRing R) α') (DegPre.famε k) (F'.s α') (D'.toPre.famφB α') (DegPre.famε k) (boxFamB pD k f α') (DegPre.prB D'.toPre (FractionRing R)).left (scal (DegPre.BF D'.toPre (FractionRing R)).hom (∏ i, r i)) := by
  intro R _ _ I j D D' pD k Fs f r hF F' hB α'
  have e1 : ∀ i, (D'.toPre.prB (FractionRing R)).left ≫ (pD.pw.pr i).left =
      prB pD (FractionRing R) i ≫ (D.toPre.prB (FractionRing R)).left := by
    intro i
    unfold prB DegPre.prB
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have e2 : ∀ i, prB pD (FractionRing R) i ≫ (D.toPre.BF (FractionRing R)).hom =
      (D'.toPre.BF (FractionRing R)).hom := fun i => Over.w (TF (FractionRing R) ◁ pD.pw.pr i)
  obtain ⟨hφ, hBα⟩ := hB α'
  obtain ⟨hφB, hBB⟩ := isBoxFamB_boxFamB pD k f α'
  exact secScal_box D.toPre.P.isLB D'.toPre.P.isLB pD.w
    (ρ := fun i => prB pD (FractionRing R) i) (σ := fun i => (pD.pw.pr i).left)
    (h' := (D'.toPre.prB (FractionRing R)).left) (h := (D.toPre.prB (FractionRing R)).left)
    (fun a => GC.famφ_eq D'.toPre (FractionRing R) α' a) e1
    (F'.s α') (fun i => (Fs i).s (pD.xe α' i)) (boxFamB pD k f α') (fun i => f i (pD.xe α' i))
    (fun y J J' hJ hJ' => box_sval pD.w hφ (F'.s α') _
      (fun jN _ i => inf_le_left.trans (box_le_of_comp _ _ _ _ _ i (hφ i) jN)) hBα (𝟙 _) y hJ hJ')
    (fun y J J' hJ hJ' => box_sval pD.w hφB (boxFamB pD k f α') _
      (fun jN _ i => inf_le_left.trans (box_le_of_comp _ _ _ _ _ i (hφB i) jN)) hBB _ y hJ hJ')
    (fun i => scal (D.toPre.BF (FractionRing R)).hom (r i)) _
    (fun y => gs_scal_prod _ _ _ e2 y r)
    (fun i => hF i (pD.xe α' i))

end GlobalTheory.BoxFamScalar
