import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowerThickIso

section General

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull gm_div gm_linComb gm_pull_g gm_self mem_pull PGen isGen_iff glue_unit
  exists_chart)

variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'}
  {h : Fin j → (Ge' ⟶ Ge)}

theorem gm_box_g {Z : Scheme.{0}} (ψ : Z ⟶ B') (z : Z) (a b : Fin j → M.ι) (ha : ∀ i, pr i (ψ z) ∈ M.U (a i))
    (hb : ∀ i, pr i (ψ z) ∈ M.U (b i)) :
    gm ψ z (LB.wchart M pr a ⊓ LB.wchart M pr b) ((LB.LinComb M pr (fun _ => 1)).g a b) =
      ∏ i, gm (ψ ≫ pr i) z (M.U (a i) ⊓ M.U (b i)) (M.g (a i) (b i)) :=
  (gm_linComb M pr (fun _ => 1) ψ z a b (Set.mem_iInter.2 ha) (Set.mem_iInter.2 hb)).trans
    (Finset.prod_congr rfl fun _ _ => zpow_one _)

theorem bw_change {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} (hw : w.IsGen) {Z : Scheme.{0}} (ψ : Z ⟶ B') (z : Z)
    (a b : Fin j → M.ι) (k k' : M'.ι) (ha : ∀ i, pr i (ψ z) ∈ M.U (a i)) (hb : ∀ i, pr i (ψ z) ∈ M.U (b i))
    (hk : ψ z ∈ M'.U k) (hk' : ψ z ∈ M'.U k') :
    bw w ψ z a k = (∏ i, gm (ψ ≫ pr i) z (M.U (a i) ⊓ M.U (b i)) (M.g (a i) (b i))) *
      (gm ψ z _ (M'.g k k'))⁻¹ * bw w ψ z b k' := by
  have hm : ψ z ∈ LB.wchart M pr a ⊓ M'.U k ⊓ (LB.wchart M pr b ⊓ M'.U k') :=
    ⟨⟨Set.mem_iInter.2 ha, hk⟩, Set.mem_iInter.2 hb, hk'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr a ⊓ M'.U k ⊓ (LB.wchart M pr b ⊓ M'.U k'))) (hw (a, k) (b, k'))
  have e' := (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div M' (LB.LinComb M pr (fun _ => 1)) ψ z (a, k) (b, k') hm) (gm_res ψ z _ hm _))))
  rw [← gm_box_g ψ z a b ha hb]
  exact e'

def germ (pG' : Ge' ⟶ B') (h : Fin j → (Ge' ⟶ Ge)) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    (we : LB.Iso (L.pull fG) (M.pull pG)) {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι) (jM' : M'.ι)
    (jL : Fin j → L.ι) : (Z.presheaf.stalk z)ˣ :=
  (bw w (r ≫ pG') z jM jM')⁻¹ * ∏ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i)

theorem germ_change (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : w.IsGen) (hwe : PGen we)
    {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM kM : Fin j → M.ι) (jM' kM' : M'.ι) (jL kL : Fin j → L.ι)
    (a₁ : ∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) (a₂ : pG' (r z) ∈ M'.U jM') (a₃ : ∀ i, prG i (fG' (r z)) ∈ L.U (jL i))
    (b₁ : ∀ i, pr i (pG' (r z)) ∈ M.U (kM i)) (b₂ : pG' (r z) ∈ M'.U kM') (b₃ : ∀ i, prG i (fG' (r z)) ∈ L.U (kL i)) :
    germ pG' h w we r z jM jM' jL =
      gm (r ≫ pG') z _ (M'.g jM' kM') *
        (∏ i, gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i)))⁻¹ *
        germ pG' h w we r z kM kM' kL := by
  have p₁ : ∀ i, pG (h i (r z)) = pr i (pG' (r z)) := fun i => congrArg (fun g => g (r z)) (e₁ i).symm
  have p₂ : ∀ i, fG (h i (r z)) = prG i (fG' (r z)) := fun i => congrArg (fun g => g (r z)) (e₂ i)
  have a := bw_change hw (r ≫ pG') z jM kM jM' kM' a₁ b₁ a₂ b₂
  have c : ∀ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i) =
      gm ((r ≫ pG') ≫ pr i) z (M.U (jM i) ⊓ M.U (kM i)) (M.g (jM i) (kM i)) *
        (gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i)))⁻¹ *
        Geo.Tor.gw we (r ≫ h i) z (kM i) (fun _ => kL i) := fun i => by
    have c₃ : fG (h i (r z)) ∈ L.U (jL i) := p₂ i ▸ a₃ i
    have d₃ : fG (h i (r z)) ∈ L.U (kL i) := p₂ i ▸ b₃ i
    have c₁ : pG (h i (r z)) ∈ M.U (jM i) := p₁ i ▸ a₁ i
    have d₁ : pG (h i (r z)) ∈ M.U (kM i) := p₁ i ▸ b₁ i
    have c := hwe Z (r ≫ h i) z (jM i) (kM i) (fun _ => jL i) (fun _ => kL i) c₁ d₁ (mem_pull.2 c₃) (mem_pull.2 d₃)
    rw [gm_pull_g L fG (r ≫ h i) z (fun _ => jL i) (fun _ => kL i) (mem_pull.2 c₃) (mem_pull.2 d₃),
      Category.assoc, Category.assoc, ← e₁, e₂] at c
    rw [Category.assoc, Category.assoc]
    exact c
  unfold germ
  rw [a, Finset.prod_congr rfl fun i _ => c i, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  generalize (∏ i, gm ((r ≫ pG') ≫ pr i) z (M.U (jM i) ⊓ M.U (kM i)) (M.g (jM i) (kM i))) = A
  generalize (∏ i, gm ((r ≫ fG') ≫ prG i) z (L.U (jL i) ⊓ L.U (kL i)) (L.g (jL i) (kL i))) = C
  generalize gm (r ≫ pG') z _ (M'.g jM' kM') = A'
  generalize bw w (r ≫ pG') z kM kM' = P
  generalize (∏ i, Geo.Tor.gw we (r ≫ h i) z (kM i) (fun _ => kL i)) = R
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_unit (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : w.IsGen) (hwe : PGen we)
    (jM' : M'.ι) (jL : Fin j → L.ι) :
    ∃ s : Γ(Ge', (M'.pull pG').U (fun _ => jM') ⊓ ((LB.LinComb L prG (fun _ => 1)).pull fG').U (fun _ => jL))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι), (∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) →
        pG' (r z) ∈ M'.U jM' → (∀ i, prG i (fG' (r z)) ∈ L.U (jL i)) →
        gm r z _ s = germ pG' h w we r z jM jM' jL := by
  have p₁ : ∀ i x, pG (h i x) = pr i (pG' x) := fun i x => congrArg (fun g => g x) (e₁ i).symm
  have p₂ : ∀ i x, fG (h i x) = prG i (fG' x) := fun i x => congrArg (fun g => g x) (e₂ i)
  obtain ⟨W, hW⟩ : ∃ W : (Fin j → M.ι) → Ge'.Opens, ∀ a x, x ∈ W a ↔
      (∀ i, pr i (pG' x) ∈ M.U (a i)) ∧ pG' x ∈ M'.U jM' ∧ ∀ i, prG i (fG' x) ∈ L.U (jL i) :=
    ⟨fun a => pG' ⁻¹ᵁ LB.wchart M pr a ⊓ (pG' ⁻¹ᵁ M'.U jM' ⊓ fG' ⁻¹ᵁ LB.wchart L prG jL),
      fun _ _ => and_congr Set.mem_iInter (and_congr Iff.rfl Set.mem_iInter)⟩
  have l₀ : ∀ a, W a ≤ (M'.pull pG').U (fun _ => jM') ⊓ ((LB.LinComb L prG (fun _ => 1)).pull fG').U (fun _ => jL) :=
    fun a x hx => ⟨mem_pull.2 ((hW a x).1 hx).2.1, mem_pull.2 (Set.mem_iInter.2 ((hW a x).1 hx).2.2)⟩
  have l₁ : ∀ a, W a ≤ pG' ⁻¹ᵁ (LB.wchart M pr a ⊓ M'.U jM') := fun a x hx =>
    ⟨Set.mem_iInter.2 ((hW a x).1 hx).1, ((hW a x).1 hx).2.1⟩
  have l₂ : ∀ a i, W a ≤ h i ⁻¹ᵁ ((M.pull pG).U (fun _ => a i) ⊓ (L.pull fG).U (fun _ => jL i)) := fun a i x hx =>
    ⟨mem_pull.2 ((p₁ i x).symm ▸ ((hW a x).1 hx).1 i), mem_pull.2 ((p₂ i x).symm ▸ ((hW a x).1 hx).2.2 i)⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ a, Γ(Ge', W a)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (a : Fin j → M.ι), r z ∈ W a →
      gm r z (W a) (u a) = germ pG' h w we r z a jM' jL :=
    ⟨fun a => (res (l₁ a) (pullU pG' _ (w.s (a, jM'))))⁻¹ *
        ∏ i, res (l₂ a i) (pullU (h i) _ (we.s (fun _ => a i, fun _ => jL i))),
      fun Z r z a hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z (l₁ a) hz _).trans (gm_pull r pG' z _ (l₁ a hz) _)))) ((map_prod _ _ _).trans
          (Finset.prod_congr rfl fun i _ =>
            (gm_res r z (l₂ a i) hz _).trans (gm_pull r (h i) z _ (l₂ a i hz) _))))⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      choose a ha using fun i => exists_chart hM (pr i (pG' x))
      exact TopologicalSpace.Opens.mem_iSup.2
        ⟨a, (hW a x).2 ⟨ha, mem_pull.1 hx.1, Set.mem_iInter.1 (mem_pull.1 hx.2)⟩⟩) u
    (fun a a' x hx => by
      have h₁ := (hW a x).1 hx.1
      have h₂ := (hW a' x).1 hx.2
      have k := germ_change e₁ e₂ hw hwe (𝟙 Ge') x a a' jM' jM' jL jL h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2
      rw [gm_self hM' (𝟙 Ge' ≫ pG') x h₁.2.1, Finset.prod_eq_one fun i _ =>
        gm_self hL ((𝟙 Ge' ≫ fG') ≫ prG i) x (h₁.2.2 i), inv_one, _root_.one_mul, _root_.one_mul] at k
      exact (hu _ (𝟙 Ge') x a hx.1).trans (k.trans (hu _ (𝟙 Ge') x a' hx.2).symm))
  refine ⟨s, fun Z r z jM a₁ a₂ a₃ => ?_⟩
  have hz := (hW jM (r z)).2 ⟨a₁, a₂, a₃⟩
  exact (gm_res r z (l₀ jM) hz s).symm.trans ((congrArg (gm r z (W jM)) (hs jM)).trans (hu Z r z jM hz))

theorem exists_box_iso (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    (e₁ : ∀ i, pG' ≫ pr i = h i ≫ pG) (e₂ : ∀ i, h i ≫ fG = fG' ≫ prG i)
    (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (we : LB.Iso (L.pull fG) (M.pull pG)) (hw : w.IsGen)
    (hwe : we.IsGen) :
    ∃ we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull fG') (M'.pull pG'), we'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : Fin j → M.ι) (jM' : M'.ι) (jL : Fin j → L.ι),
        (∀ i, pr i (pG' (r z)) ∈ M.U (jM i)) → pG' (r z) ∈ M'.U jM' → (∀ i, prG i (fG' (r z)) ∈ L.U (jL i)) →
        bw w (r ≫ pG') z jM jM' * Geo.Tor.gw we' r z jM' (fun _ => jL) =
          ∏ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i) := by
  rw [isGen_iff] at hwe
  choose s hs using exists_unit hM hM' hL e₁ e₂ hw hwe
  refine ⟨⟨fun p => s (p.1 PUnit.unit) (p.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, fun Z r z jM jM' jL a₁ a₂ a₃ => ?_⟩
  · intro Z r z l l' k k' a₂ b₂ a₄ b₄
    choose a ha using fun i => exists_chart hM (pr i (pG' (r z)))
    have a₄' : ∀ i, prG i (fG' (r z)) ∈ L.U (k PUnit.unit i) := Set.mem_iInter.1 (mem_pull.1 a₄)
    have b₄' : ∀ i, prG i (fG' (r z)) ∈ L.U (k' PUnit.unit i) := Set.mem_iInter.1 (mem_pull.1 b₄)
    have c := germ_change e₁ e₂ hw hwe r z a a l l' _ _ ha a₂ a₄' ha b₂ b₄'
    rw [← hs l _ Z r z a ha a₂ a₄', ← hs l' _ Z r z a ha b₂ b₄', ← gm_box_g (r ≫ fG') z _ _ a₄' b₄'] at c
    rw [gm_pull_g (LB.LinComb L prG (fun _ => 1)) fG' r z k k' a₄ b₄]
    exact c
  · exact (congrArg (bw w (r ≫ pG') z jM jM' * ·) (hs jM' jL Z r z jM a₁ a₂ a₃)).trans
      (mul_inv_cancel_left _ _)

end General

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (e : ℕ) (g : GtCoord I D.toPre e G) (g' : GtCoord I D'.toPre e G'), (∀ i, g'.pG.left ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ g.pG.left) → ∀ (L : LB G.left), L.IsLB → ∀ w : LB.Iso (L.pull (fstG I e G).left) (D.toPre.P.L.pull g.pG.left), w.IsGen → ∃ w' : LB.Iso ((boxLB L pG.pr).pull (fstG I e G').left) (D'.toPre.P.L.pull g'.pG.left), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : Fin j → L.ι), (∀ i, (pD.pw.pr i).left (g'.pG.left (r z)) ∈ D.toPre.P.L.U (jM i)) → g'.pG.left (r z) ∈ D'.toPre.P.L.U jM' → (∀ i, (pG.pr i).left ((fstG I e G').left (r z)) ∈ L.U (jL i)) → bw pD.w (r ≫ g'.pG.left) z jM jM' * Geo.Tor.gw w' r z jM' (fun _ => jL) = ∏ i, Geo.Tor.gw w (r ≫ ((Over.pullback (thick R I e)).map (pG.pr i)).left) z (jM i) (fun _ => jL i) := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG e g g' hq L hL w hw
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  exact exists_box_iso (Ge := (thickObj R I e G).left) (Ge' := (thickObj R I e G').left) (h := rhoE I pG e)
    (pG := g.pG.left) (pG' := g'.pG.left) (fG := fGl I G e) (fG' := fGl I G' e)
    D.toPre.P.isLB D'.toPre.P.isLB hL hq hρ pD.w w pD.w_gen hw

end GlobalTheory.PowerThickIso
