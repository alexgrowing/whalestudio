import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FourthSide

theorem gm_pull_g {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (f : Y ⟶ X') (y : Y) (j j' : L.ι)
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') :
    gm f y ((L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j')) ((L.pull F).g (fun _ => j) (fun _ => j')) =
      gm (f ≫ F) y _ (L.g j j') := by
  have hp : f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)

variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {L' : LB G'}
  {Φ : B' ⟶ B} {Ψ : G' ⟶ G} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'} {h : Ge' ⟶ Ge}

def germ (pG' : Ge' ⟶ B') (fG' : Ge' ⟶ G') (h : Ge' ⟶ Ge) (w : LB.Iso M' (M.pull Φ)) (wL : LB.Iso L' (L.pull Ψ))
    (we : LB.Iso (L.pull fG) (M.pull pG)) {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι)
    (jL' : L'.ι) : (Z.presheaf.stalk z)ˣ :=
  (gw w (r ≫ pG') z jM jM')⁻¹ * (gw we (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ fG') z jL jL')

theorem germ_change (e₁ : pG' ≫ Φ = h ≫ pG) (e₂ : h ≫ fG = fG' ≫ Ψ) {w : LB.Iso M' (M.pull Φ)}
    {wL : LB.Iso L' (L.pull Ψ)} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : PGen w) (hwL : PGen wL) (hwe : PGen we)
    {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM kM : M.ι) (jM' kM' : M'.ι) (jL kL : L.ι) (jL' kL' : L'.ι)
    (a₁ : Φ (pG' (r z)) ∈ M.U jM) (a₂ : pG' (r z) ∈ M'.U jM') (a₃ : Ψ (fG' (r z)) ∈ L.U jL)
    (a₄ : fG' (r z) ∈ L'.U jL') (b₁ : Φ (pG' (r z)) ∈ M.U kM) (b₂ : pG' (r z) ∈ M'.U kM')
    (b₃ : Ψ (fG' (r z)) ∈ L.U kL) (b₄ : fG' (r z) ∈ L'.U kL') :
    germ pG' fG' h w wL we r z jM jM' jL jL' =
      gm (r ≫ pG') z _ (M'.g jM' kM') * (gm (r ≫ fG') z _ (L'.g jL' kL'))⁻¹ *
        germ pG' fG' h w wL we r z kM kM' kL kL' := by
  have p₁ : pG (h (r z)) = Φ (pG' (r z)) := congrArg (fun g => g (r z)) e₁.symm
  have p₂ : fG (h (r z)) = Ψ (fG' (r z)) := congrArg (fun g => g (r z)) e₂
  have c₃ : fG (h (r z)) ∈ L.U jL := p₂ ▸ a₃
  have d₃ : fG (h (r z)) ∈ L.U kL := p₂ ▸ b₃
  have c₁ : pG (h (r z)) ∈ M.U jM := p₁ ▸ a₁
  have d₁ : pG (h (r z)) ∈ M.U kM := p₁ ▸ b₁
  have a := hw Z (r ≫ pG') z jM kM jM' kM' a₁ b₁ a₂ b₂
  have b := hwL Z (r ≫ fG') z jL kL jL' kL' a₃ b₃ a₄ b₄
  have c := hwe Z (r ≫ h) z jM kM (fun _ => jL) (fun _ => kL) c₁ d₁ (mem_pull.2 c₃) (mem_pull.2 d₃)
  rw [gm_pull_g L fG (r ≫ h) z jL kL c₃ d₃, Category.assoc, Category.assoc, ← e₁, e₂] at c
  rw [Category.assoc] at a b
  unfold germ
  rw [a, b, c]
  generalize gm (r ≫ pG' ≫ Φ) z _ (M.g jM kM) = A
  generalize gm (r ≫ fG' ≫ Ψ) z _ (L.g jL kL) = C
  generalize gm (r ≫ pG') z _ (M'.g jM' kM') = A'
  generalize gm (r ≫ fG') z _ (L'.g jL' kL') = C'
  generalize gw w (r ≫ pG') z kM kM' = P
  generalize gw wL (r ≫ fG') z kL kL' = Q
  generalize gw we (r ≫ h) z kM (fun _ => kL) = R
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_unit (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB)
    (e₁ : pG' ≫ Φ = h ≫ pG) (e₂ : h ≫ fG = fG' ≫ Ψ) {w : LB.Iso M' (M.pull Φ)}
    {wL : LB.Iso L' (L.pull Ψ)} {we : LB.Iso (L.pull fG) (M.pull pG)} (hw : PGen w) (hwL : PGen wL) (hwe : PGen we)
    (jM' : M'.ι) (jL' : L'.ι) :
    ∃ s : Γ(Ge', (M'.pull pG').U (fun _ => jM') ⊓ (L'.pull fG').U (fun _ => jL'))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jL : L.ι), Φ (pG' (r z)) ∈ M.U jM →
        pG' (r z) ∈ M'.U jM' → Ψ (fG' (r z)) ∈ L.U jL → fG' (r z) ∈ L'.U jL' →
        gm r z _ s = germ pG' fG' h w wL we r z jM jM' jL jL' := by
  have p₁ : ∀ x, pG (h x) = Φ (pG' x) := fun x => congrArg (fun g => g x) e₁.symm
  have p₂ : ∀ x, fG (h x) = Ψ (fG' x) := fun x => congrArg (fun g => g x) e₂
  obtain ⟨W, hW⟩ : ∃ W : M.ι × L.ι → Ge'.Opens, ∀ i x, x ∈ W i ↔
      Φ (pG' x) ∈ M.U i.1 ∧ pG' x ∈ M'.U jM' ∧ Ψ (fG' x) ∈ L.U i.2 ∧ fG' x ∈ L'.U jL' :=
    ⟨fun i => pG' ⁻¹ᵁ (Φ ⁻¹ᵁ M.U i.1) ⊓ (pG' ⁻¹ᵁ M'.U jM' ⊓ (fG' ⁻¹ᵁ (Ψ ⁻¹ᵁ L.U i.2) ⊓ fG' ⁻¹ᵁ L'.U jL')),
      fun _ _ => Iff.rfl⟩
  have l₀ : ∀ i, W i ≤ (M'.pull pG').U (fun _ => jM') ⊓ (L'.pull fG').U (fun _ => jL') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).2.1, mem_pull.2 ((hW i x).1 hx).2.2.2⟩
  have l₁ : ∀ i, W i ≤ pG' ⁻¹ᵁ ((M.pull Φ).U (fun _ => i.1) ⊓ M'.U jM') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.1⟩
  have l₂ : ∀ i, W i ≤ h ⁻¹ᵁ ((M.pull pG).U (fun _ => i.1) ⊓ (L.pull fG).U (fun _ => i.2)) := fun i x hx =>
    ⟨mem_pull.2 ((p₁ x).symm ▸ ((hW i x).1 hx).1), mem_pull.2 ((p₂ x).symm ▸ ((hW i x).1 hx).2.2.1)⟩
  have l₃ : ∀ i, W i ≤ fG' ⁻¹ᵁ ((L.pull Ψ).U (fun _ => i.2) ⊓ L'.U jL') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).2.2.1, ((hW i x).1 hx).2.2.2⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Ge', W i)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (i : M.ι × L.ι), r z ∈ W i →
      gm r z (W i) (u i) = germ pG' fG' h w wL we r z i.1 jM' i.2 jL' :=
    ⟨fun i => (res (l₁ i) (pullU pG' _ (w.s (fun _ => i.1, jM'))))⁻¹ *
        (res (l₂ i) (pullU h _ (we.s (fun _ => i.1, fun _ => i.2))) *
          res (l₃ i) (pullU fG' _ (wL.s (fun _ => i.2, jL')))),
      fun Z r z i hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹)
        ((gm_res r z (l₁ i) hz _).trans (gm_pull r pG' z _ (l₁ i hz) _)))) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res r z (l₂ i) hz _).trans (gm_pull r h z _ (l₂ i hz) _))
          ((gm_res r z (l₃ i) hz _).trans (gm_pull r fG' z _ (l₃ i hz) _)))))⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hM (Φ (pG' x))
      obtain ⟨j, hj⟩ := exists_chart hL (Ψ (fG' x))
      exact Opens.mem_iSup.2 ⟨(i, j), (hW (i, j) x).2 ⟨hi, mem_pull.1 hx.1, hj, mem_pull.1 hx.2⟩⟩) u
    (fun i i' x hx => by
      have h₁ := (hW i x).1 hx.1
      have h₂ := (hW i' x).1 hx.2
      have k := germ_change e₁ e₂ hw hwL hwe (𝟙 Ge') x i.1 i'.1 jM' jM' i.2 i'.2 jL' jL' h₁.1 h₁.2.1 h₁.2.2.1
        h₁.2.2.2 h₂.1 h₂.2.1 h₂.2.2.1 h₂.2.2.2
      rw [gm_self hM' (𝟙 Ge' ≫ pG') x h₁.2.1, gm_self hL' (𝟙 Ge' ≫ fG') x h₁.2.2.2, inv_one, one_mul, one_mul] at k
      exact (hu _ (𝟙 Ge') x i hx.1).trans (k.trans (hu _ (𝟙 Ge') x i' hx.2).symm))
  refine ⟨s, fun Z r z jM jL a₁ a₂ a₃ a₄ => ?_⟩
  have hz := (hW (jM, jL) (r z)).2 ⟨a₁, a₂, a₃, a₄⟩
  exact (gm_res r z (l₀ (jM, jL)) hz s).symm.trans
    ((congrArg (gm r z (W (jM, jL))) (hs (jM, jL))).trans (hu Z r z (jM, jL) hz))

theorem exists_fourth_side (B B' G G' Ge Ge' : Scheme.{0}) (M : LB B) (M' : LB B') (L : LB G) (L' : LB G')
    (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB) (Φ : B' ⟶ B) (Ψ : G' ⟶ G) (pG : Ge ⟶ B)
    (pG' : Ge' ⟶ B') (fG : Ge ⟶ G) (fG' : Ge' ⟶ G') (h : Ge' ⟶ Ge) (e₁ : pG' ≫ Φ = h ≫ pG)
    (e₂ : h ≫ fG = fG' ≫ Ψ) (w : LB.Iso M' (M.pull Φ)) (wL : LB.Iso L' (L.pull Ψ))
    (we : LB.Iso (L.pull fG) (M.pull pG)) (hw : w.IsGen) (hwL : wL.IsGen) (hwe : we.IsGen) :
    ∃ we' : LB.Iso (L'.pull fG') (M'.pull pG'), we'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
        Φ (pG' (r z)) ∈ M.U jM → pG' (r z) ∈ M'.U jM' → Ψ (fG' (r z)) ∈ L.U jL → fG' (r z) ∈ L'.U jL' →
        gw w (r ≫ pG') z jM jM' * gw we' r z jM' (fun _ => jL') =
          gw we (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ fG') z jL jL' := by
  rw [isGen_iff] at hw hwL hwe
  choose s hs using exists_unit hM hM' hL hL' e₁ e₂ hw hwL hwe
  refine ⟨⟨fun p => s (p.1 PUnit.unit) (p.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  · intro Z r z j j' k k' a₂ b₂ a₄ b₄
    obtain ⟨i, hi⟩ := exists_chart hM (Φ (pG' (r z)))
    obtain ⟨l, hl⟩ := exists_chart hL (Ψ (fG' (r z)))
    have a₄' := mem_pull.1 a₄
    have b₄' := mem_pull.1 b₄
    have c := germ_change e₁ e₂ hw hwL hwe r z i i j j' l l _ _ hi a₂ hl a₄' hi b₂ hl b₄'
    rw [← hs j _ Z r z i l hi a₂ hl a₄', ← hs j' _ Z r z i l hi b₂ hl b₄',
      ← gm_pull_g L' fG' r z _ _ a₄' b₄'] at c
    exact c
  · exact (congrArg (gw w (r ≫ pG') z jM jM' * ·) (hs jM' jL' Z r z jM jL a₁ a₂ a₃ a₄)).trans
      (mul_inv_cancel_left _ _)

end GlobalTheory.FourthSide
