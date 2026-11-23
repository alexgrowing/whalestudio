import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CompatAlongOfSquare
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BoxSymIsSymmetry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig

variable {B B' G G' T T' T₁ T₁' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {p : T ⟶ B} {p' : T' ⟶ B'} {f : T ⟶ G} {f' : T' ⟶ G'}

def BoxSquare (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (we : LB.Iso (L.pull f) (M.pull p))
    (we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')) (h : Fin j → (T' ⟶ T)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ T') (z : Z) (jM : Fin j → M.ι) (jM' : M'.ι) (jL : Fin j → L.ι),
    (∀ i, pr i (p' (r z)) ∈ M.U (jM i)) → p' (r z) ∈ M'.U jM' → (∀ i, prG i (f' (r z)) ∈ L.U (jL i)) →
    bw w (r ≫ p') z jM jM' * Geo.Tor.gw we' r z jM' (fun _ => jL) =
      ∏ i, Geo.Tor.gw we (r ≫ h i) z (jM i) (fun _ => jL i)

theorem compat_box (hM : M.IsLB) {p₁ : T₁ ⟶ B} {p₁' : T₁' ⟶ B'} {f₁ : T₁ ⟶ G} {f₁' : T₁' ⟶ G'}
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    {we₁ : LB.Iso (L.pull f₁) (M.pull p₁)}
    {we₁' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f₁') (M'.pull p₁')} {h₁ : Fin j → (T₁' ⟶ T₁)}
    {m : T ⟶ T₁} {m' : T' ⟶ T₁'} (Q : BoxSquare w we we' h) (Q₁ : BoxSquare w we₁ we₁' h₁)
    (H : CompatAlong we₁ we m) (hf : m ≫ f₁ = f) (hp : m ≫ p₁ = p) (hf' : m' ≫ f₁' = f') (hp' : m' ≫ p₁' = p')
    (hF : ∀ i, h i ≫ f = f' ≫ prG i) (hE : ∀ i, p' ≫ pr i = h i ≫ p) (hm : ∀ i, m' ≫ h₁ i = h i ≫ m) :
    CompatAlong we₁' we' m' := by
  intro q V h₁ h₂
  apply unit_ext
  intro x hx
  refine (gm_rp₁ m' x _ V h₁ hx _).trans (Eq.trans ?_ (gm_res (𝟙 T') x h₂ hx _).symm)
  change Geo.Tor.gw we₁' m' x (q.1 ⟨⟩) (fun _ => q.2 ⟨⟩) = Geo.Tor.gw we' (𝟙 T') x (q.1 ⟨⟩) (fun _ => q.2 ⟨⟩)
  obtain ⟨J, hJ⟩ := exists_good_at hM x
  have x₂ := h₂ hx
  have a₁ : ∀ i, pr i (p' x) ∈ M.U (J (p' ≫ pr i)) := fun i => by simpa using hJ (p' ≫ pr i)
  have b₁ : p' x ∈ M'.U (q.1 ⟨⟩) := mem_pull.mp x₂.1
  have c₀ : f' x ∈ LB.wchart L prG (q.2 ⟨⟩) := by
    have := mem_pull.mp x₂.2
    exact (Scheme.Hom.mem_preimage f').mp this
  have c₁ : ∀ i, prG i (f' x) ∈ L.U (q.2 ⟨⟩ i) := fun i => LB.wchart_le L prG (q.2 ⟨⟩) i c₀
  have ep : p₁' (m' x) = p' x := by rw [← hp']; rfl
  have ef : f₁' (m' x) = f' x := by rw [← hf']; rfl
  have e1 := Q T' (𝟙 T') x (fun i => J (p' ≫ pr i)) (q.1 ⟨⟩) (q.2 ⟨⟩) (fun i => a₁ i) b₁ (fun i => c₁ i)
  have e2 := Q₁ T' m' x (fun i => J (p' ≫ pr i)) (q.1 ⟨⟩) (q.2 ⟨⟩) (fun i => by rw [ep]; exact a₁ i)
    (by rw [ep]; exact b₁) (fun i => by rw [ef]; exact c₁ i)
  have e3 : ∏ i, Geo.Tor.gw we₁ (h i ≫ m) x (J (p' ≫ pr i)) (fun _ => q.2 ⟨⟩ i) =
      ∏ i, Geo.Tor.gw we (h i) x (J (p' ≫ pr i)) (fun _ => q.2 ⟨⟩ i) := by
    refine Finset.prod_congr rfl fun i _ => H.stalk hf hp (h i) x _ _ ?_ ?_
    · rw [← pt_of_eq (hE i) x]; exact a₁ i
    · rw [pt_of_eq (hF i) x]; exact c₁ i
  simp only [Category.id_comp] at e1
  simp only [hp', hm] at e2
  exact _root_.mul_left_cancel (e2.trans (e3.trans e1.symm))

private theorem gm_pull_transition_eq_gm_comp {X T Z : Scheme.{0}} (L : LB X) (f : T ⟶ X) (r : Z ⟶ T) (z : Z) (a b : L.ι)
    (h : r z ∈ (L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b)) :
    gm r z _ ((L.pull f).g (fun _ => a) (fun _ => b)) = gm (r ≫ f) z (L.U a ⊓ L.U b) (L.g a b) :=
  (gm_linComb L (fun _ : PUnit => f) (fun _ => 1) r z (fun _ => a) (fun _ => b) h.1 h.2).trans (by simp)

private theorem gw_mul_gm_transition_eq_gw_of_isGen {B G T Z : Scheme.{0}} {M : LB B} {L : LB G} {p : T ⟶ B} {f : T ⟶ G}
    (hM : M.IsLB) {we : LB.Iso (L.pull f) (M.pull p)} (hwe : we.IsGen) (r : Z ⟶ T) (z : Z) (c : M.ι)
    (a b : L.ι) (h1 : p (r z) ∈ M.U c) (h2 : f (r z) ∈ L.U a) (h3 : f (r z) ∈ L.U b) :
    Geo.Tor.gw we r z c (fun _ => a) * gm (r ≫ f) z (L.U a ⊓ L.U b) (L.g a b) =
      Geo.Tor.gw we r z c (fun _ => b) := by
  have hz : r z ∈ ((M.pull p).div (L.pull f)).U (fun _ => c, fun _ => a) ⊓
      ((M.pull p).div (L.pull f)).U (fun _ => c, fun _ => b) :=
    ⟨⟨mem_pull.mpr h1, mem_pull.mpr h2⟩, ⟨mem_pull.mpr h1, mem_pull.mpr h3⟩⟩
  have hp : (r ≫ p) z ∈ M.U c := h1
  have gM : gm (r ≫ p) z (M.U c ⊓ M.U c) (M.g c c) = 1 := by
    have e0 := congrArg (gm (r ≫ p) z _) (hM.g_self c)
    rw [gm_res (r ≫ p) z _ hp, map_one] at e0
    exact e0
  have e := congrArg (gm r z _) (hwe (fun _ => c, fun _ => a) (fun _ => c, fun _ => b))
  rw [map_mul, gm_res r z _ hz, gm_res r z _ hz] at e
  have eg : gm r z _ (((M.pull p).div (L.pull f)).g (fun _ => c, fun _ => a) (fun _ => c, fun _ => b)) =
      (gm (r ≫ f) z (L.U a ⊓ L.U b) (L.g a b))⁻¹ := by
    refine (map_mul (gm r z _) _ _).trans ?_
    refine (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv (gm r z _) _).trans (congrArg (·⁻¹) (gm_res r z _ hz _)))).trans ?_
    have hzM : r z ∈ (M.pull p).U (fun _ => c) ⊓ (M.pull p).U (fun _ => c) := ⟨mem_pull.mpr h1, mem_pull.mpr h1⟩
    have hzL : r z ∈ (L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b) := ⟨mem_pull.mpr h2, mem_pull.mpr h3⟩
    refine (congrArg₂ (· * ·) (gm_pull_transition_eq_gm_comp M p r z c c hzM)
      (congrArg (·⁻¹) (gm_pull_transition_eq_gm_comp L f r z a b hzL))).trans ?_
    exact (congrArg (· * _) gM).trans (one_mul _)
  rw [eg] at e
  change Geo.Tor.gw we r z c (fun _ => a) = _ * Geo.Tor.gw we r z c (fun _ => b) at e
  rw [e, mul_comm]
  exact mul_inv_cancel_left _ _

theorem change_chart (hM : M.IsLB) {we : LB.Iso (L.pull f) (M.pull p)} (hwe : we.IsGen) {K : Type} [Fintype K]
    {ε : K → ℤ} {Z Y : Scheme.{0}} (z : Z) (P : K → (Z ⟶ T)) {φ : K → (Y ⟶ G)} {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) (m : Z ⟶ Y) (c : ∀ k, P k ≫ f = m ≫ φ k) (jM : K → M.ι) (a b : K → L.ι)
    (hM' : ∀ k, p (P k z) ∈ M.U (jM k)) (ha : ∀ k, φ k (m z) ∈ L.U (a k)) (hb : ∀ k, φ k (m z) ∈ L.U (b k)) :
    (∏ k, Geo.Tor.gw we (P k) z (jM k) (fun _ => a k) ^ ε k) * gm m z (LB.wchart L φ a) (t.s a) =
      (∏ k, Geo.Tor.gw we (P k) z (jM k) (fun _ => b k) ^ ε k) * gm m z (LB.wchart L φ b) (t.s b) := by
  have hf : ∀ k, f (P k z) = φ k (m z) := fun k => pt_of_eq (c k) z
  have ma : m z ∈ LB.wchart L φ a := Set.mem_iInter.2 fun k => ha k
  have mb : m z ∈ LB.wchart L φ b := Set.mem_iInter.2 fun k => hb k
  rw [gen_trans ht m z ma mb]
  unfold trF
  rw [← _root_.mul_assoc, ← Finset.prod_mul_distrib]
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  rw [← mul_zpow]
  refine congrArg (· ^ ε k) ?_
  have e := gw_mul_gm_transition_eq_gw_of_isGen hM hwe (P k) z (jM k) (a k) (b k) (hM' k) (by rw [hf k]; exact ha k)
    (by rw [hf k]; exact hb k)
  rw [c k] at e
  exact e

theorem alg {U K I : Type} [CommGroup U] [Fintype K] [Fintype I] (ε : K → ℤ) (A W' : K → U) (W : K → I → U)
    (h : ∀ k, A k * W' k = ∏ i, W k i) {a' : U} {a b : I → U} (e₁ : (∏ k, A k ^ ε k) * a' = ∏ i, a i)
    (e₂ : ∀ i, a i = (∏ k, W k i ^ ε k) * b i) : a' = (∏ k, W' k ^ ε k) * ∏ i, b i := by
  apply mul_left_cancel (a := ∏ k, A k ^ ε k)
  rw [e₁, Finset.prod_congr rfl (fun i _ => e₂ i), Finset.prod_mul_distrib, Finset.prod_comm,
    ← _root_.mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [← mul_zpow, h, Finset.prod_zpow]

theorem rel_box (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    (hwe : we.IsGen) (Q : BoxSquare w we we' h)
    (hF : ∀ i, h i ≫ f = f' ≫ prG i) (hE : ∀ i, p' ≫ pr i = h i ≫ p)
    {K : Type} [Fintype K] {ε : K → ℤ} {Z YL YM YM' : Scheme.{0}} (z : Z) (P : K → (Z ⟶ T'))
    {φ : K → (YL ⟶ G)} {ψ : K → (YM ⟶ B)} {ψ' : K → (YM' ⟶ B')}
    {tL : LB.Gen (LB.LinComb L φ ε)} (htL : tL.IsGen) (tM : LB.Gen (LB.LinComb M ψ ε))
    (tM' : LB.Gen (LB.LinComb M' ψ' ε)) (mB : Z ⟶ YM') (nB : Fin j → (Z ⟶ YM)) (nG : Fin j → (Z ⟶ YL))
    (c₁ : ∀ i k, (P k ≫ h i) ≫ f = nG i ≫ φ k) (c₂ : ∀ k, P k ≫ p' = mB ≫ ψ' k)
    (c₃ : ∀ i k, (P k ≫ h i) ≫ p = nB i ≫ ψ k)
    (HM : ∀ J J', Good M z J → Good M' z J' →
      (∏ k, om w z J J' (mB ≫ ψ' k) ^ ε k) * val tM' mB z J' = ∏ i, val tM (nB i) z J)
    (HU : ∀ i J N, Good M z J → Good L z N → val tM (nB i) z J =
      (∏ k, Geo.Tor.gw we (P k ≫ h i) z (J (nB i ≫ ψ k)) (fun _ => N (nG i ≫ φ k)) ^ ε k) * val tL (nG i) z N)
    (jL : K → Fin j → L.ι) (jM' : K → M'.ι) (coh : LB.Coh M' (fun k => mB ≫ ψ' k) jM')
    (mM : ∀ k, ψ' k (mB z) ∈ M'.U (jM' k)) (mL : ∀ k i, φ k (nG i z) ∈ L.U (jL k i)) :
    gm mB z (LB.wchart M' ψ' jM') (tM'.s jM') =
      (∏ k, Geo.Tor.gw we' (P k) z (jM' k) (fun _ => jL k) ^ ε k) *
        ∏ i, gm (nG i) z (LB.wchart L φ (fun k => jL k i)) (tL.s (fun k => jL k i)) := by
  obtain ⟨J', hJ', hJ'e⟩ := exists_good M' hM' z (fun k => mB ≫ ψ' k) jM' coh mM
  obtain ⟨J, hJ⟩ := exists_good_at hM z
  obtain ⟨N, hN⟩ := exists_good_at hL z
  have hQ : ∀ k, om w z J J' (mB ≫ ψ' k) * Geo.Tor.gw we' (P k) z (jM' k) (fun _ => jL k) =
      ∏ i, Geo.Tor.gw we (P k ≫ h i) z (J (nB i ≫ ψ k)) (fun _ => jL k i) := by
    intro k
    have hk : ∀ i, (mB ≫ ψ' k) ≫ pr i = nB i ≫ ψ k := fun i => by
      rw [← c₂ k, Category.assoc, hE i, ← Category.assoc, c₃ i k]
    have e := Q Z (P k) z (fun i => J (nB i ≫ ψ k)) (jM' k) (jL k)
      (fun i => by
        have eq : pr i (p' (P k z)) = (nB i ≫ ψ k) z := by
          rw [← hk i, ← c₂ k]
          rfl
        rw [eq]
        exact hJ (nB i ≫ ψ k))
      (by rw [pt_of_eq (c₂ k) z]; exact mM k)
      (fun i => by
        have := mL k i
        rw [← pt_of_eq (c₁ i k) z] at this
        rw [← pt_of_eq (hF i) (P k z)]
        exact this)
    unfold om
    rw [hJ'e k]
    simp only [hk]
    rw [← c₂ k]
    exact e
  have he₂ : ∀ i, val tM (nB i) z J = (∏ k, Geo.Tor.gw we (P k ≫ h i) z (J (nB i ≫ ψ k)) (fun _ => jL k i) ^ ε k) *
      gm (nG i) z (LB.wchart L φ (fun k => jL k i)) (tL.s (fun k => jL k i)) := fun i =>
    (HU i J N hJ hN).trans (change_chart hM hwe z (fun k => P k ≫ h i) htL (nG i) (c₁ i)
      (fun k => J (nB i ≫ ψ k)) (fun k => N (nG i ≫ φ k)) (fun k => jL k i)
      (fun k => by rw [pt_of_eq (c₃ i k) z]; exact hJ _) (fun k => hN _) (fun k => mL k i))
  refine (val_of tM' mB z J' jM' hJ'e).symm.trans ?_
  exact alg ε (fun k => om w z J J' (mB ≫ ψ' k)) (fun k => Geo.Tor.gw we' (P k) z (jM' k) (fun _ => jL k))
    (fun k i => Geo.Tor.gw we (P k ≫ h i) z (J (nB i ≫ ψ k)) (fun _ => jL k i)) hQ (HM J J' hJ hJ') he₂

theorem gm_box_pull {X X' Y Y' Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (F : Fin j → (X' ⟶ X))
    {φ : Fin j → K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {ε : K → ℤ} (ρ : Fin j → (Y' ⟶ Y))
    (hψ : ∀ i k, φ' k ≫ F i = ρ i ≫ φ i k) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) ε)) (r : Z ⟶ Y') (z : Z)
    (jj : K → Fin j → L.ι) (h : r z ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) φ' jj) :
    gm r z (LB.wchart (LB.LinComb L F (fun _ => 1)) φ' jj)
      ((GeneratorPullback.boxGen L F φ' ε (fun i => GeneratorPullback.pullAlong L (F i) (ρ i) (φ i) ε φ' (hψ i) (t i))).s jj) =
      ∏ i, gm (r ≫ ρ i) z (LB.wchart L (φ i) (fun k => jj k i)) ((t i).s (fun k => jj k i)) := by
  refine (GlobalTheory.BoxSymmetry.gm_boxGen L F φ' ε _ r z jj h).trans (Finset.prod_congr rfl fun i _ => ?_)
  have hz : r z ∈ (L.pull (F i)).wchart φ' (fun k _ => jj k i) :=
    Set.mem_iInter.2 fun k => mem_pull.2 (LB.wchart_le L F (jj k) i (Set.mem_iInter.1 h k))
  exact gm_res_pull r (ρ i) z _ hz _

theorem maps_box_val (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {Y Y₀ Z : Scheme.{0}}
    {φ' : K → (Y ⟶ B')} {φ : Fin j → K → (Y₀ ⟶ B)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))))
    (r : Z ⟶ Y) (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, om w y J J' (r ≫ φ' a) ^ ε a) * val t' r y J' = ∏ i, val (t i) (r ≫ ρ i) y J := by
  have m1 : r y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) :=
    Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((r ≫ φ' a) ≫ pr i)
  have m2 : r y ∈ LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) := hJ'.mem φ' r
  have e := congrArg (gm r y _) (H (fun a i => J ((r ≫ φ' a) ≫ pr i), fun a => J' (r ≫ φ' a)))
  dsimp only at e
  have m12 : r y ∈ (((M.LinComb pr fun _ => 1).LinComb φ' ε).U fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓
      (M'.LinComb φ' ε).U fun a => J' (r ≫ φ' a) := ⟨m1, m2⟩
  rw [map_mul, gm_res r y _ m12, gm_res r y _ m12] at e
  have e2 := (gm_box_pull M pr ρ hψ t r y _ m1).symm.trans
    (e.trans (congrArg (· * _) (gm_linCombIso w φ' ε r y _ _ m12)))
  rw [Finset.prod_congr rfl fun i _ => val_of (t i) (r ≫ ρ i) y J (fun k => J ((r ≫ φ' k) ≫ pr i))
    (fun k => congrArg J (by simp only [Category.assoc, hψ]))]
  exact e2.symm

theorem corr_box (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K]
    {ε : K → ℤ} {φ₀ : Fin j → K → (T ⟶ B)} {φ₁ : Fin j → K → (T₁ ⟶ B)} {φ₀' : K → (T' ⟶ B')} {φ₁' : K → (T₁' ⟶ B')}
    {t₀ : ∀ i, LB.Gen (LB.LinComb M (φ₀ i) ε)} {t₁ : ∀ i, LB.Gen (LB.LinComb M (φ₁ i) ε)}
    {t₀' : LB.Gen (LB.LinComb M' φ₀' ε)} {t₁' : LB.Gen (LB.LinComb M' φ₁' ε)}
    {h₀ : Fin j → (T' ⟶ T)} {h₁ : Fin j → (T₁' ⟶ T₁)} {m : T ⟶ T₁} {m' : T' ⟶ T₁'} (hm : ∀ i, m' ≫ h₁ i = h₀ i ≫ m)
    (c₀ : ∀ i k, φ₀' k ≫ pr i = h₀ i ≫ φ₀ i k) (c₁ : ∀ i k, φ₁' k ≫ pr i = h₁ i ≫ φ₁ i k)
    (c' : ∀ k, m' ≫ φ₁' k = φ₀' k)
    (H₀ : LB.Gen.Maps (LB.linCombIso w φ₀' ε) t₀'
      (GeneratorPullback.boxGen M pr φ₀' ε (fun i => GeneratorPullback.pullAlong M (pr i) (h₀ i) (φ₀ i) ε φ₀' (c₀ i) (t₀ i))))
    (H₁ : LB.Gen.Maps (LB.linCombIso w φ₁' ε) t₁'
      (GeneratorPullback.boxGen M pr φ₁' ε (fun i => GeneratorPullback.pullAlong M (pr i) (h₁ i) (φ₁ i) ε φ₁' (c₁ i) (t₁ i))))
    (H : ∀ i, LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ (t₁ i) m) (t₀ i)) :
    LB.Gen.Corr M' _ _ _ _ (LB.pullGen M' _ _ t₁' m') t₀' := by
  refine corr_of_val hM' fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good_at hM y
  have A₁ := maps_box_val w c₁ t₁' t₁ H₁ m' y hJ hJ'
  have A₀ := maps_box_val w c₀ t₀' t₀ H₀ (𝟙 _) y hJ hJ'
  simp only [Category.id_comp, c', hm] at A₁ A₀
  have A₂ : ∏ i, val (t₁ i) (h₀ i ≫ m) y J = ∏ i, val (t₀ i) (h₀ i) y J :=
    Finset.prod_congr rfl fun i _ => (val_pull hJ (t₁ i) m (h₀ i)).symm.trans (val_corr hJ (H i) (h₀ i))
  rw [val_pull hJ' t₁' m' (𝟙 _), Category.id_comp]
  exact _root_.mul_left_cancel (A₁.trans (A₂.trans A₀.symm))

end GlobalTheory.PowUnif
