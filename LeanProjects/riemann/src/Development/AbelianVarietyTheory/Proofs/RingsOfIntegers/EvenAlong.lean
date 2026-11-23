import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ChangeChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig

variable {B B' G G' T T' S S₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {p : T ⟶ B} {p' : T' ⟶ B'} {f : T ⟶ G} {f' : T' ⟶ G'}

theorem rig_box (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    (hwe : we.IsGen) (Q : BoxSquare w we we' h)
    (hF : ∀ i, h i ≫ f = f' ≫ prG i) (hE : ∀ i, p' ≫ pr i = h i ≫ p)
    {u : S ⟶ T} {u' : S ⟶ T'} {s : S ⟶ S₀} {eG : S₀ ⟶ G} {eA : S₀ ⟶ B} {eG' : S₀ ⟶ G'} {eA' : S₀ ⟶ B'}
    {rL : LB.Gen (L.pull eG)} (hrL : rL.IsGen) {rM : LB.Gen (M.pull eA)} {rM' : LB.Gen (M'.pull eA')}
    (H : RigAlong we u s rL rM) (hu : ∀ i, u' ≫ h i = u) (hf : u ≫ f = s ≫ eG) (hp : u ≫ p = s ≫ eA)
    (hp' : u' ≫ p' = s ≫ eA') (hG : ∀ (i : Fin j) (_ : PUnit), eG' ≫ prG i = 𝟙 S₀ ≫ eG)
    (b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => eA' ≫ pr i) (fun _ => 1)))
    (b₁ : GeneratorPullback.MapsAt M M' pr w eA' 1 rM' b)
    (b₂ : LB.Gen.Corr M _ _ _ _ b (GeneratorPullback.finProdGen M (J := Fin j) (fun _ _ => eA) (fun _ _ => 1) (fun _ => rM))) :
    RigAlong we' u' s (GeneratorPullback.boxGen L prG (fun _ : PUnit => eG') (fun _ => 1)
      (fun i => GeneratorPullback.pullAlong L (prG i) (𝟙 S₀) (fun _ => eG) (fun _ => 1) (fun _ => eG') (hG i) rL)) rM' := by
  rintro ⟨qM, qL⟩ V a₁ a₂ a₃
  refine unit_ext fun y hy => ?_
  have key := rel_box hM hM' hL hwe Q hF hE (K := PUnit) (ε := fun _ => 1) y (fun _ => u') hrL rM rM' s
    (fun _ => s) (fun _ => s) (fun i _ => by rw [hu, hf]) (fun _ => hp') (fun i _ => by rw [hu, hp])
    (fun J J' hJ hJ' => (congrArg₂ (· * ·) (Fintype.prod_unique _) rfl).trans
      ((mapsAt_val w eA' 1 rM' b b₁ s y hJ hJ').symm.trans ((val_corr hJ b₂ s).trans (val_finProd _ _ _ s y hJ))))
    (fun i J N hJ hN => by
      have e := H.stalk hf hp (𝟙 S) y (J (s ≫ eA)) (N (s ≫ eG)) ((pt_of_eq hp y).symm ▸ hJ (s ≫ eA))
        ((pt_of_eq hf y).symm ▸ hN (s ≫ eG))
      rw [Category.id_comp, Category.id_comp] at e
      rw [Fintype.prod_unique, zpow_one, hu]
      exact e.symm)
    qL qM (fun a b _ => congrArg qM (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 (a₃ hy) k)
    (fun k i => (pt_of_eq (hG i k) (s y)) ▸ Set.mem_iInter.1 (Set.mem_iInter.1 (a₂ hy) k) i)
  rw [Fintype.prod_unique, zpow_one] at key
  have e := gm_box_pull L prG (fun _ => 𝟙 S₀) hG (fun _ => rL) s y qL (a₂ hy)
  rw [Category.comp_id] at e
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res_pull _ u' y a₁ hy _)
    (gm_res_pull _ s y a₂ hy _)).trans (Eq.trans ?_ (gm_res_pull _ s y a₃ hy _).symm))
  rw [Category.id_comp, Category.id_comp]
  exact (congrArg₂ (· * ·) rfl e).trans key.symm

def EvenAlong (we : LB.Iso (L.pull f) (M.pull p)) (iT : T ⟶ T) {iG : G ⟶ G} {iB : B ⟶ B}
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]))
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])) : Prop :=
  ∀ (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι),
    LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS →
    LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT →
    ∀ (V : T.Opens) (h₁ : V ≤ p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT)
      (h₂ : V ≤ (M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1))
      (h₃ : V ≤ iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)))
      (h₄ : V ≤ f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS),
      res h₁ (pullU p _ (σ.s jT)) * res h₂ (we.s (fun _ => jT 1, fun _ => jS 1)) =
        res h₃ (pullU iT _ (we.s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU f _ (s.s jS))

theorem EvenAlong.stalk {we : LB.Iso (L.pull f) (M.pull p)} {iT : T ⟶ T} {iG : G ⟶ G} {iB : B ⟶ B}
    {s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1])}
    {σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])} (ev : EvenAlong we iT s σ)
    (iF : iT ≫ f = f ≫ iG) (iP : iT ≫ p = p ≫ iB) {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z)
    (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι) (cS : LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS)
    (cT : LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT)
    (hS : ∀ k, (![iG, 𝟙 G] : Fin 2 → (G ⟶ G)) k (f (r z)) ∈ L.U (jS k))
    (hT : ∀ k, (![iB, 𝟙 B] : Fin 2 → (B ⟶ B)) k (p (r z)) ∈ M.U (jT k)) :
    gm (r ≫ p) z (LB.wchart M (K := Fin 2) ![iB, 𝟙 B] jT) (σ.s jT) =
      (∏ k, Geo.Tor.gw we ((![r ≫ iT, r] : Fin 2 → _) k) z (jT k) (fun _ => jS k) ^ (![1, -1] : Fin 2 → ℤ) k) *
        gm (r ≫ f) z (LB.wchart L (K := Fin 2) ![iG, 𝟙 G] jS) (s.s jS) := by
  have S0 : f (iT (r z)) ∈ L.U (jS 0) := (pt_of_eq iF (r z)).symm ▸ hS 0
  have T0 : p (iT (r z)) ∈ M.U (jT 0) := (pt_of_eq iP (r z)).symm ▸ hT 0
  have S1 : f (r z) ∈ L.U (jS 1) := hS 1
  have T1 : p (r z) ∈ M.U (jT 1) := hT 1
  let W : T.Opens := p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT ⊓
    ((M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1)) ⊓
    iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)) ⊓
    f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS
  have hW : r z ∈ W := ⟨⟨⟨Set.mem_iInter.2 hT, mem_pull.2 T1, mem_pull.2 S1⟩, mem_pull.2 T0, mem_pull.2 S0⟩,
    Set.mem_iInter.2 hS⟩
  have l₁ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have l₂ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have l₃ : W ≤ _ := inf_le_left.trans inf_le_right
  have l₄ : W ≤ _ := inf_le_right
  obtain ⟨n₁, n₂⟩ := GlobalTheory.EvenPull.even_stalk we s σ jS jT W l₁ l₂ l₃ l₄ r z hW
  have E := n₁.symm.trans ((congrArg (gm r z W) (ev jS jT cS cT W l₁ l₂ l₃ l₄)).trans n₂)
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg]
  rw [← mul_right_comm, ← E, mul_inv_cancel_right]

theorem even_box (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    (hwe : we.IsGen) (Q : BoxSquare w we we' h)
    (hF : ∀ i, h i ≫ f = f' ≫ prG i) (hE : ∀ i, p' ≫ pr i = h i ≫ p)
    {iT : T ⟶ T} {iG : G ⟶ G} {iB : B ⟶ B} {iT' : T' ⟶ T'} {iG' : G' ⟶ G'} {iB' : B' ⟶ B'}
    (ih : ∀ i, iT' ≫ h i = h i ≫ iT) (iF : iT ≫ f = f ≫ iG) (iP : iT ≫ p = p ≫ iB) (iP' : iT' ≫ p' = p' ≫ iB')
    (hG : ∀ i k, (![iG', 𝟙 G'] : Fin 2 → _) k ≫ prG i = prG i ≫ (![iG, 𝟙 G] : Fin 2 → _) k)
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1])) (hs : s.IsGen)
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]))
    (σ' : LB.Gen (LB.LinComb M' (K := Fin 2) ![iB', 𝟙 B'] ![1, -1]))
    (hσ : ∀ (y : T') J J', Good M y J → Good M' y J' →
      om w y J J' (p' ≫ iB') * (om w y J J' p')⁻¹ * val σ' p' y J' = ∏ i, val σ (p' ≫ pr i) y J)
    (ev : EvenAlong we iT s σ) :
    EvenAlong we' iT' (GeneratorPullback.boxGen L prG _ _ (fun i => GeneratorPullback.pullAlong L (prG i) (prG i) _ _ _ (hG i) s)) σ' := by
  intro jS' jT' _ cT V h₁ h₂ h₃ h₄
  refine unit_ext fun z hz => ?_
  obtain ⟨k₁, k₂⟩ := GlobalTheory.EvenPull.even_stalk we'
    (GeneratorPullback.boxGen L prG _ _ (fun i => GeneratorPullback.pullAlong L (prG i) (prG i) _ _ _ (hG i) s)) σ' jS' jT' V h₁ h₂ h₃ h₄
    (𝟙 T') z hz
  refine k₁.trans (Eq.trans ?_ k₂.symm)
  clear k₁ k₂
  have c₀ : ∀ i k, (![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i = (![h i ≫ iT, h i] : Fin 2 → _) k :=
    fun i => Fin.forall_fin_two.2 ⟨ih i, Category.id_comp _⟩
  have c₁ : ∀ i k, ((![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i) ≫ f = (h i ≫ f) ≫ (![iG, 𝟙 G] : Fin 2 → _) k :=
    fun i => Fin.forall_fin_two.2 ⟨by
      show (iT' ≫ h i) ≫ f = (h i ≫ f) ≫ iG
      rw [ih, Category.assoc, iF, Category.assoc], by
      show (𝟙 T' ≫ h i) ≫ f = (h i ≫ f) ≫ 𝟙 G
      rw [Category.id_comp, Category.comp_id]⟩
  have c₃ : ∀ i k, ((![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i) ≫ p = (h i ≫ p) ≫ (![iB, 𝟙 B] : Fin 2 → _) k :=
    fun i => Fin.forall_fin_two.2 ⟨by
      show (iT' ≫ h i) ≫ p = (h i ≫ p) ≫ iB
      rw [ih, Category.assoc, iP, Category.assoc], by
      show (𝟙 T' ≫ h i) ≫ p = (h i ≫ p) ≫ 𝟙 B
      rw [Category.id_comp, Category.comp_id]⟩
  have mL : ∀ k i, (![iG, 𝟙 G] : Fin 2 → (G ⟶ G)) k ((h i ≫ f) z) ∈ L.U (jS' k i) := fun k i => by
    have a : ((f' ≫ (![iG', 𝟙 G'] : Fin 2 → (G' ⟶ G')) k) ≫ prG i) z ∈ L.U (jS' k i) :=
      Set.mem_iInter.1 (Set.mem_iInter.1 (h₄ hz) k) i
    rw [Category.assoc, hG, ← Category.assoc, ← hF] at a
    exact a
  have HM : ∀ J J', Good M z J → Good M' z J' →
      (∏ k, om w z J J' (p' ≫ (![iB', 𝟙 B'] : Fin 2 → _) k) ^ (![1, -1] : Fin 2 → ℤ) k) * val σ' p' z J' =
        ∏ i, val σ (h i ≫ p) z J := fun J J' hJ hJ' => by
    have e := hσ z J J' hJ hJ'
    simp only [hE] at e
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, zpow_one, zpow_neg]
    exact e
  have HU : ∀ i J N, Good M z J → Good L z N → val σ (h i ≫ p) z J =
      (∏ k, Geo.Tor.gw we ((![iT', 𝟙 T'] : Fin 2 → _) k ≫ h i) z (J ((h i ≫ p) ≫ (![iB, 𝟙 B] : Fin 2 → _) k))
        (fun _ => N ((h i ≫ f) ≫ (![iG, 𝟙 G] : Fin 2 → _) k)) ^ (![1, -1] : Fin 2 → ℤ) k) * val s (h i ≫ f) z N :=
    fun i J N hJ hN => by
      simp only [c₀]
      exact ev.stalk iF iP (h i) z _ _
        (fun a b e => congrArg N ((Category.assoc _ _ _).trans ((congrArg (h i ≫ ·) e).trans
          (Category.assoc _ _ _).symm)))
        (fun a b e => congrArg J ((Category.assoc _ _ _).trans ((congrArg (h i ≫ ·) e).trans
          (Category.assoc _ _ _).symm)))
        (fun k => hN ((h i ≫ f) ≫ (![iG, 𝟙 G] : Fin 2 → _) k)) (fun k => hJ ((h i ≫ p) ≫ (![iB, 𝟙 B] : Fin 2 → _) k))
  have key := rel_box hM hM' hL hwe Q hF hE (K := Fin 2) (ε := ![1, -1]) z ![iT', 𝟙 T'] hs σ σ' p'
    (fun i => h i ≫ p) (fun i => h i ≫ f) c₁
    (Fin.forall_fin_two.2 ⟨iP', (Category.id_comp _).trans (Category.comp_id _).symm⟩) c₃ HM HU
    jS' jT' cT (fun k => Set.mem_iInter.1 (h₁ hz) k) mL
  have e := gm_box_pull L prG prG hG (fun _ => s) f' z jS' (h₄ hz)
  rw [Fin.prod_univ_two] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, hF] at key
  rw [Category.id_comp, Category.id_comp, Category.id_comp]
  refine Eq.trans ?_ (congrArg₂ (· * ·) rfl e).symm
  rw [key, mul_right_comm, inv_mul_cancel_right]

end GlobalTheory.PowUnif
