import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.NormPullExp

section Transport

variable {X₁ X₂ X' Y Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {L' : LB X'} {F₁ : X' ⟶ X₁} {F₂ : X' ⟶ X₂}

theorem exists_transport (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) (h' : L'.IsLB) {w₁ : LB.Iso L' (L₁.pull F₁)}
    {w₂ : LB.Iso L' (L₂.pull F₂)} (hw₁ : PGen w₁) (hw₂ : PGen w₂) {K : Type} [Fintype K] (φ' : K → (Y ⟶ X'))
    {φ₁ : K → (Y ⟶ X₁)} {φ₂ : K → (Y ⟶ X₂)} (e₁ : ∀ k, φ' k ≫ F₁ = φ₁ k) (e₂ : ∀ k, φ' k ≫ F₂ = φ₂ k) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L₁ φ₁ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L₂ φ₂ ε), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L₁.ι) (j : K → L₂.ι)
      (q : K → L'.ι), r z ∈ LB.wchart L₁ φ₁ p → r z ∈ LB.wchart L₂ φ₂ j → r z ∈ LB.wchart L' φ' q →
      gm r z (LB.wchart L₂ φ₂ j) (u.s j) = gm r z (LB.wchart L₁ φ₁ p) (t.s p) *
        ∏ k, (gw w₂ (r ≫ φ' k) z (j k) (q k) / gw w₁ (r ≫ φ' k) z (p k) (q k)) ^ ε k := by
  obtain rfl : (fun k => φ' k ≫ F₁) = φ₁ := funext e₁
  obtain rfl : (fun k => φ' k ≫ F₂) = φ₂ := funext e₂
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p p' : K → L₁.ι) (j j' : K → L₂.ι) (q q' : K → L'.ι),
      r z ∈ LB.wchart L₁ (fun k => φ' k ≫ F₁) p → r z ∈ LB.wchart L₂ (fun k => φ' k ≫ F₂) j →
      r z ∈ LB.wchart L' φ' q →
      r z ∈ LB.wchart L₁ (fun k => φ' k ≫ F₁) p' → r z ∈ LB.wchart L₂ (fun k => φ' k ≫ F₂) j' →
      r z ∈ LB.wchart L' φ' q' →
      gm r z (LB.wchart L₁ (fun k => φ' k ≫ F₁) p) (t.s p) *
        ∏ k, (gw w₂ (r ≫ φ' k) z (j k) (q k) / gw w₁ (r ≫ φ' k) z (p k) (q k)) ^ ε k =
      trF (fun k => φ' k ≫ F₂) ε r z j j' * (gm r z (LB.wchart L₁ (fun k => φ' k ≫ F₁) p') (t.s p') *
        ∏ k, (gw w₂ (r ≫ φ' k) z (j' k) (q' k) / gw w₁ (r ≫ φ' k) z (p' k) (q' k)) ^ ε k) := by
    intro Z r z p p' j j' q q' hp hj hq hp' hj' hq'
    have a₁ := fun k => hw₁ Z (r ≫ φ' k) z (p k) (p' k) (q k) (q' k) (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hp' k)
      (Set.mem_iInter.1 hq k) (Set.mem_iInter.1 hq' k)
    have a₂ := fun k => hw₂ Z (r ≫ φ' k) z (j k) (j' k) (q k) (q' k) (Set.mem_iInter.1 hj k) (Set.mem_iInter.1 hj' k)
      (Set.mem_iInter.1 hq k) (Set.mem_iInter.1 hq' k)
    rw [gen_trans ht r z hp hp']
    simp only [a₁, a₂, trF, Category.assoc, div_eq_mul_inv, mul_inv, inv_inv, mul_zpow, Finset.prod_mul_distrib,
      inv_zpow, Finset.prod_inv_distrib]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ j : K → L₂.ι, ∃ s : Γ(Y, LB.wchart L₂ (fun k => φ' k ≫ F₂) j)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L₁.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L₁ (fun k => φ' k ≫ F₁) p → r z ∈ LB.wchart L₂ (fun k => φ' k ≫ F₂) j →
      r z ∈ LB.wchart L' φ' q →
      gm r z _ s = gm r z (LB.wchart L₁ (fun k => φ' k ≫ F₁) p) (t.s p) *
        ∏ k, (gw w₂ (r ≫ φ' k) z (j k) (q k) / gw w₁ (r ≫ φ' k) z (p k) (q k)) ^ ε k := by
    intro j
    let W : (K → L₁.ι) × (K → L'.ι) → Y.Opens := fun i =>
      LB.wchart L₂ (fun k => φ' k ≫ F₂) j ⊓ (LB.wchart L₁ (fun k => φ' k ≫ F₁) i.1 ⊓ LB.wchart L' φ' i.2)
    have l₁ : ∀ i k, W i ≤ φ' k ⁻¹ᵁ ((L₁.pull F₁).U (fun _ => i.1 k) ⊓ L'.U (i.2 k)) := fun i k x hx =>
      ⟨mem_pull.2 (Set.mem_iInter.1 hx.2.1 k), Set.mem_iInter.1 hx.2.2 k⟩
    have l₂ : ∀ i k, W i ≤ φ' k ⁻¹ᵁ ((L₂.pull F₂).U (fun _ => j k) ⊓ L'.U (i.2 k)) := fun i k x hx =>
      ⟨mem_pull.2 (Set.mem_iInter.1 hx.1 k), Set.mem_iInter.1 hx.2.2 k⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(Y, W i)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i, r z ∈ W i →
        gm r z (W i) (u i) = gm r z (LB.wchart L₁ (fun k => φ' k ≫ F₁) i.1) (t.s i.1) *
        ∏ k, (gw w₂ (r ≫ φ' k) z (j k) (i.2 k) / gw w₁ (r ≫ φ' k) z (i.1 k) (i.2 k)) ^ ε k :=
      ⟨fun i => res (inf_le_right.trans inf_le_left : W i ≤ LB.wchart L₁ (fun k => φ' k ≫ F₁) i.1) (t.s i.1) *
          ∏ k, (res (l₂ i k) (pullU (φ' k) _ (w₂.s (fun _ => j k, i.2 k))) /
            res (l₁ i k) (pullU (φ' k) _ (w₁.s (fun _ => i.1 k, i.2 k)))) ^ ε k, fun Z r z i hz =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _) ((map_prod _ _ _).trans
          (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((map_div _ _ _).trans
            (congrArg₂ (· / ·) ((gm_res r z (l₂ i k) hz _).trans (gm_pull r (φ' k) z _ (l₂ i k hz) _))
              ((gm_res r z (l₁ i k) hz _).trans (gm_pull r (φ' k) z _ (l₁ i k hz) _))))))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W (fun _ => inf_le_left) (fun x hx => by
        choose p hp using fun k => exists_chart h₁ ((φ' k ≫ F₁) x)
        choose q hq using fun k => exists_chart h' (φ' k x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨(p, q), hx, Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩) u
      (fun i i' x hx => by
        rw [hu _ (𝟙 Y) x i hx.1, hu _ (𝟙 Y) x i' hx.2, key _ (𝟙 Y) x i.1 i'.1 j j i.2 i'.2 hx.1.2.1 hx.1.1 hx.1.2.2
          hx.2.2.1 hx.2.1 hx.2.2.2,
          mul_eq_left.1 (trF_trans h₂ (fun k => φ' k ≫ F₂) ε (𝟙 Y) x hx.1.1 hx.1.1 hx.1.1), _root_.one_mul])
    refine ⟨s, fun Z r z p q hp hj hq => ?_⟩
    have hz : r z ∈ W (p, q) := ⟨hj, hp, hq⟩
    exact (gm_res r z inf_le_left hz s).symm.trans ((congrArg (gm r z (W (p, q))) (hs (p, q))).trans (hu Z r z _ hz))
  choose s hs using glue
  refine ⟨⟨s⟩, fun j j' => unit_ext fun x hx => ?_, fun Z r z p j q => hs j Z r z p q⟩
  choose p hp using fun k => exists_chart h₁ ((φ' k ≫ F₁) x)
  choose q hq using fun k => exists_chart h' (φ' k x)
  have mp : (𝟙 Y : Y ⟶ Y) x ∈ LB.wchart L₁ (fun k => φ' k ≫ F₁) p := Set.mem_iInter.2 hp
  have mq : (𝟙 Y : Y ⟶ Y) x ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
  refine (gm_res (𝟙 Y) x _ hx _).trans (((hs j _ _ x p q mp hx.1 mq).trans
    (key _ _ x p p j j' q q mp hx.1 mq mp hx.2 mq)).trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linComb L₂ _ ε (𝟙 Y) x j j' hx.1 hx.2)
    ((gm_res (𝟙 Y) x _ hx _).trans (hs j' _ _ x p q mp hx.2 mq)))

def ratio (w₁ : LB.Iso L' (L₁.pull F₁)) (w₂ : LB.Iso L' (L₂.pull F₂)) (f : Z ⟶ X') (z : Z)
    (J₁ : (Z ⟶ X₁) → L₁.ι) (J₂ : (Z ⟶ X₂) → L₂.ι) (J' : (Z ⟶ X') → L'.ι) : (Z.presheaf.stalk z)ˣ :=
  gw w₂ f z (J₂ (f ≫ F₂)) (J' f) / gw w₁ f z (J₁ (f ≫ F₁)) (J' f)

end Transport

section Norm

variable {S₁ S₂ S' Y : Scheme.{0}} {G₁ : Over S₁} {G₂ : Over S₂} {G' : Over S'} [GrpObj G₁] [IsCommMonObj G₁]
  [GrpObj G₂] [IsCommMonObj G₂] [GrpObj G'] [IsCommMonObj G']

theorem rig_val {L₁ : RigLB G₁} {L' : RigLB G'} {F₁ : G'.left ⟶ G₁.left}
    {e₁ : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S₁)).left} {w₁ : LB.Iso L'.L (L₁.L.pull F₁)}
    (he₁ : eSec G' ≫ F₁ = e₁ ≫ eSec G₁)
    (r₁ : PMaps w₁ (K := PUnit) (fun _ => eSec G') (fun _ => eSec G₁) (fun _ => 1) L'.rig L₁.rig e₁)
    {Z : Scheme.{0}} (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) {J₁ J'} (hJ₁ : Good L₁.L z J₁) (hJ' : Good L'.L z J') :
    val L₁.rig (r ≫ e₁) z J₁ =
      gw w₁ (r ≫ eSec G') z (J₁ ((r ≫ eSec G') ≫ F₁)) (J' (r ≫ eSec G')) * val L'.rig r z J' := by
  have := r₁ Z r z (fun _ => J₁ ((r ≫ eSec G') ≫ F₁)) (fun _ => J' (r ≫ eSec G')) (fun _ => hJ₁ _) (fun _ => hJ' _)
  rw [Fintype.prod_unique, zpow_one] at this
  rw [val_of L₁.rig (r ≫ e₁) z J₁ (fun _ => J₁ ((r ≫ eSec G') ≫ F₁)) (fun _ => by
    rw [Category.assoc, Category.assoc, he₁])]
  exact this

theorem exists_norm (L₁ : RigLB G₁) (L₂ : RigLB G₂) (L' : RigLB G') {F₁ : G'.left ⟶ G₁.left} {F₂ : G'.left ⟶ G₂.left}
    {e₁ : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S₁)).left} {e₂ : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S₂)).left}
    {w₁ : LB.Iso L'.L (L₁.L.pull F₁)} {w₂ : LB.Iso L'.L (L₂.L.pull F₂)} (hw₁ : PGen w₁) (hw₂ : PGen w₂)
    (he₁ : eSec G' ≫ F₁ = e₁ ≫ eSec G₁) (he₂ : eSec G' ≫ F₂ = e₂ ≫ eSec G₂)
    (r₁ : PMaps w₁ (K := PUnit) (fun _ => eSec G') (fun _ => eSec G₁) (fun _ => 1) L'.rig L₁.rig e₁)
    (r₂ : PMaps w₂ (K := PUnit) (fun _ => eSec G') (fun _ => eSec G₂) (fun _ => 1) L'.rig L₂.rig e₂)
    (a' : G'.left ⟶ G'.left) (a₁ : G₁.left ⟶ G₁.left) (ha₁ : a' ≫ F₁ = F₁ ≫ a₁) (h0 : eSec G' ≫ a' = eSec G')
    (ψ : Y ⟶ G'.left) (g₀ g₁ : Y ⟶ G₂.left) (hg₀ : ψ ≫ F₂ = g₀) (hg₁ : (ψ ≫ a') ≫ F₂ = g₁)
    (o : (𝟙_ (Over S')).left ⟶ Y) (ho : o ≫ ψ = eSec G') (a b : ℤ)
    (α₀ : LB.Gen (LB.LinComb L₁.L (K := Fin 2) ![𝟙 G₁.left, a₁] ![a, -b])) (hα : α₀.IsGen)
    (hc : LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ α₀ (eSec G₁))
      (LB.mulGen L₁.L _ _ _ _ (rigPow G₁ L₁.L L₁.rig a) (rigPow G₁ L₁.L L₁.rig (-b)))) :
    ∃ u : LB.Gen (LB.LinComb L₂.L (K := Fin 2) ![g₀, g₁] ![a, -b]), u.IsGen ∧
      (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) (J₂), Good L₂.L z J₂ →
        val u (r ≫ o) z J₂ = val L₂.rig (r ≫ e₂) z J₂ ^ (a - b)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J₁ J₂ J'), Good L₁.L z J₁ → Good L₂.L z J₂ → Good L'.L z J' →
        val u r z J₂ = val α₀ ((r ≫ ψ) ≫ F₁) z J₁ *
          (ratio w₁ w₂ (r ≫ ψ) z J₁ J₂ J' ^ a * ratio w₁ w₂ ((r ≫ ψ) ≫ a') z J₁ J₂ J' ^ (-b)) := by
  have e₁' : ∀ k, (![ψ, ψ ≫ a'] : Fin 2 → _) k ≫ F₁ = (ψ ≫ F₁) ≫ (![𝟙 G₁.left, a₁] : Fin 2 → _) k := fun k => by
    fin_cases k
    · exact (Category.comp_id _).symm
    · show (ψ ≫ a') ≫ F₁ = (ψ ≫ F₁) ≫ a₁
      rw [Category.assoc, Category.assoc, ha₁]
  have e₂' : ∀ k, (![ψ, ψ ≫ a'] : Fin 2 → _) k ≫ F₂ = (![g₀, g₁] : Fin 2 → _) k := fun k => by
    fin_cases k
    · exact hg₀
    · exact hg₁
  obtain ⟨u, hu, hv⟩ := exists_transport L₁.isLB L₂.isLB L'.isLB hw₁ hw₂ (K := Fin 2) ![ψ, ψ ≫ a'] e₁' e₂' ![a, -b]
    (LB.pullGen L₁.L _ _ α₀ (ψ ≫ F₁)) (pullGen_isGen _ _ _ _ hα _)
  have main : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J₁ J₂ J'), Good L₁.L z J₁ → Good L₂.L z J₂ → Good L'.L z J' →
        val u r z J₂ = val α₀ ((r ≫ ψ) ≫ F₁) z J₁ *
          (ratio w₁ w₂ (r ≫ ψ) z J₁ J₂ J' ^ a * ratio w₁ w₂ ((r ≫ ψ) ≫ a') z J₁ J₂ J' ^ (-b)) := by
    intro Z r z J₁ J₂ J' hJ₁ hJ₂ hJ'
    have f₁ := fun k => (congrArg (r ≫ ·) (e₁' k).symm).trans (Category.assoc _ _ _).symm
    have f₂ := fun k => (congrArg (r ≫ ·) (e₂' k).symm).trans (Category.assoc _ _ _).symm
    have := hv Z r z (fun k => J₁ ((r ≫ (![ψ, ψ ≫ a'] : Fin 2 → _) k) ≫ F₁))
      (fun k => J₂ ((r ≫ (![ψ, ψ ≫ a'] : Fin 2 → _) k) ≫ F₂)) (fun k => J' (r ≫ (![ψ, ψ ≫ a'] : Fin 2 → _) k))
      (Set.mem_iInter.2 fun k => (congrArg (fun q => q z ∈ L₁.L.U (J₁ ((r ≫ (![ψ, ψ ≫ a'] : Fin 2 → _) k) ≫ F₁))) (f₁ k)).mpr (hJ₁ _))
      (Set.mem_iInter.2 fun k => (congrArg (fun q => q z ∈ L₂.L.U (J₂ ((r ≫ (![ψ, ψ ≫ a'] : Fin 2 → _) k) ≫ F₂))) (f₂ k)).mpr (hJ₂ _)) (hJ'.mem _ r)
    rw [← val_of u r z J₂ _ (fun k => congrArg J₂ (f₂ k)), ← val_of _ r z J₁ _ (fun k => congrArg J₁ (f₁ k)),
      val_pull hJ₁, Fin.prod_univ_two] at this
    rw [Category.assoc r ψ F₁, Category.assoc r ψ a']
    exact this
  refine ⟨u, hu, fun Z r z J₂ hJ₂ => ?_, main⟩
  choose J₁ hJ₁ using fun χ : Z ⟶ G₁.left => exists_chart L₁.isLB (χ z)
  choose J' hJ' using fun χ : Z ⟶ G'.left => exists_chart L'.isLB (χ z)
  have c := val_corr hJ₁ hc (r ≫ e₁)
  rw [val_pull hJ₁, val_mul hJ₁] at c
  have p : ∀ k : ℤ, val (rigPow G₁ L₁.L L₁.rig k) (r ≫ e₁) z J₁ = val L₁.rig (r ≫ e₁) z J₁ ^ k := fun k =>
    map_zpow _ _ _
  rw [main Z _ z J₁ J₂ J' hJ₁ hJ₂ hJ', Category.assoc r o ψ, ho, Category.assoc r _ a', h0, Category.assoc r _ F₁,
    he₁, ← Category.assoc, c, p, p, rig_val he₁ r₁ r z hJ₁ hJ', rig_val he₂ r₂ r z hJ₂ hJ', ratio, sub_eq_add_neg,
    zpow_add, _root_.mul_mul_mul_comm, ← mul_zpow, ← mul_zpow, mul_right_comm, mul_div_cancel]

theorem pgen_cast {LG PP : RigLB G₂} (h : LG = PP) {L' : LB G'.left} {F : G'.left ⟶ G₂.left}
    {w : LB.Iso L' (PP.L.pull F)} (hw : PGen w) : PGen (isoCast (congrArg RigLB.L h).symm F w) := by
  subst h
  exact hw

theorem pmaps_cast {LG PP : RigLB G₂} (h : LG = PP) {L' : RigLB G'} {F : G'.left ⟶ G₂.left}
    {w : LB.Iso L'.L (PP.L.pull F)} {e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S₂)).left}
    (hw : PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G₂) (fun _ => 1) L'.rig PP.rig e) :
    PMaps (isoCast (congrArg RigLB.L h).symm F w) (K := PUnit) (fun _ => eSec G') (fun _ => eSec G₂) (fun _ => 1)
      L'.rig LG.rig e := by
  subst h
  exact hw

end Norm

theorem twist_val {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A}
    {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    {s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd T A).left) (fun _ => b))}
    {s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd T A).left) (fun _ => a))}
    (h : IsTwistPull A L ψ m hm a b α s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    sval s' r z J = (val α r z J).val * sval s (r ≫ ψ.left) z J := by
  have hz := hJ.mem (K := Fin 2) ![(snd T A).left, m.left] r
  have e := congrArg (gs r z _) (h (fun a => J (r ≫ ![(snd T A).left, m.left] a)))
  have l := chart_le_pull A L ψ m hm (fun a => J (r ≫ ![(snd T A).left, m.left] a))
  rw [sval_of s (r ≫ ψ.left) z J (fun _ => J (r ≫ m.left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, hm])]
  exact (gs_res r z _ hz _).symm.trans (e.trans ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _)
    ((gs_res r z l hz _).trans (gs_pull r ψ.left z
      (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (r ≫ m.left))) (l hz) _)))))

theorem final_alg {R : Type} [CommRing R] (x₁ x y₁ y : R) (a u v₁ v₂ w₁ w₂ : Rˣ) (q k : ℕ)
    (t₁ : x₁ * v₁.val ^ q = y₁ * v₂.val ^ q) (t₂ : x * w₁.val ^ k = y * w₂.val ^ k) (t₃ : y₁ = a.val * y)
    (h : u = a * ((v₂ / v₁) ^ (q : ℤ) * (w₂ / w₁) ^ (-(k : ℤ)))) : x₁ = x * u.val := by
  have e : u * (v₁ ^ q * w₂ ^ k) = a * v₂ ^ q * w₁ ^ k := by
    rw [h, zpow_neg, zpow_natCast, zpow_natCast, div_pow, div_pow]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_div]
    abel
  have e' := congrArg Units.val e
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at e'
  refine (Units.mul_left_inj (v₁ ^ q * w₂ ^ k)).1 ?_
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  rw [_root_.mul_assoc x, e']
  linear_combination (w₂.val ^ k) * t₁ + (v₂.val ^ q * w₂.val ^ k) * t₃ - (a.val * v₂.val ^ q) * t₂

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∀ (α : 𝓞 E) (N k q : ℕ) (e : k * N = q), α * star α = (N : 𝓞 E) → 0 < N → (k = 1 ∨ 4 ≤ k) → ∀ (σ : P.U.toUnifPre.SecGF F k) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo xF))) (θ : Fam P.D.toPre F k) (σ₁ : P.U.toUnifPre.SecGF F q) (s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))) (θα : Fam P.D.toPre F (k * N)), SecTieF I P F xF k σ s → P.U.toUnifPre.ExpandsG F k σ θ → IsNormPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) (q : ℤ) (k : ℤ) s s₁ → SecTieF I P F xF q σ₁ s₁ → PullAl P.D F P.oD α k N θ θα → P.U.toUnifPre.ExpandsG F q σ₁ (PowGerm.famCast (Dp := P.D.toPre) (F := F) e θα) := by
  intro E _ _ _ H Dw l Xo c T io y I P F _ _ xF hx α N k q e hN hN0 hk σ s θ σ₁ s₁ θα ht hθ hn ht₁ hP
  letI := H.starRing
  letI := io.toAlgebra
  subst e
  obtain ⟨α₀, β, hα₀, hc, hβ, htw⟩ := hn
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have c₁ := I.m1.cart.1
  have c₂ := I.m2.cart.1
  obtain ⟨ψ, ψ₁, ψ₂⟩ : ∃ ψ : pullback I.G.G.hom (jK T.V) ⟶ I.t'.G.left, ψ ≫ I.m2.φ = gK ∧
      ψ ≫ I.t'.G.hom = pullback.snd I.G.G.hom (jK T.V) :=
    ⟨c₂.lift _ _ pullback.condition, c₂.lift_fst _ _ _, c₂.lift_snd _ _ _⟩
  have h0 : eSec I.t'.G ≫ (I.t'.act.act α).left = eSec I.t'.G := by
    unfold eSec
    rw [← Over.comp_left, (I.t'.act.hom α).one_hom]
  have g₁ : endK (I.G.act.act α) ≫ gK = gK ≫ (I.G.act.act α).left := pullback.lift_fst _ _ _
  have hg₁ : (ψ ≫ (I.t'.act.act α).left) ≫ I.m2.φ = endK (I.G.act.act α) ≫ gK := by
    rw [g₁, ← ψ₁, Category.assoc, Category.assoc]
    exact congrArg (ψ ≫ ·) (I.m2.act α)
  have ho : unitK ≫ ψ = eSec I.t'.G := by
    refine c₂.hom_ext ?_ ?_
    · refine (Category.assoc _ _ _).trans ((congrArg (unitK ≫ ·) ψ₁).trans ((pullback.lift_fst _ _ _).trans ?_))
      rw [I.m2.cm.e_comm, I.m2.base]
    · refine (Category.assoc _ _ _).trans ((congrArg (unitK ≫ ·) ψ₂).trans ((pullback.lift_snd _ _ _).trans ?_))
      exact (Over.w η[I.t'.G]).symm
  obtain ⟨u, hu, hu₀, hu₁⟩ := exists_norm Xo.univ.t.PP P.U.LG I.t'.PP ((isGen_iff _).1 I.rig1.1)
    (pgen_cast P.bundle ((isGen_iff _).1 I.rig2.1)) I.m1.cm.e_comm I.m2.cm.e_comm
    ((maps_iff I.w1 _ _ _ _ _ _ _ (rigPull_le _ _ I.m1.cm.e_comm _) (fun _ => rfl)).1 I.rig1.2)
    (pmaps_cast P.bundle ((maps_iff I.w2 _ _ _ _ _ _ _ (rigPull_le _ _ I.m2.cm.e_comm _) (fun _ => rfl)).1 I.rig2.2))
    (I.t'.act.act α).left (Xo.univ.t.act.act α).left (I.m1.act α) h0 ψ gK (endK (I.G.act.act α) ≫ gK) ψ₁ hg₁
    unitK ho ((k * N : ℕ) : ℤ) (k : ℤ) α₀ hα₀ hc
  obtain ⟨s'', hs₁, hs₂⟩ := GlobalTheory.PullExpField.main hL T.V E H I.G P α N hN hN0 k hk u hu
    (corr_of_val P.U.LG.isLB fun z J hJ => by
      rw [val_pull hJ, val_pull hJ, hu₀ _ _ z J hJ, I.m2.base]
      refine Eq.trans ?_ (map_pow _ _ _).symm
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN0.ne'
      rw [← zpow_natCast, show ((k * n.succ : ℕ) : ℤ) - k = ((k * (n.succ - 1) : ℕ) : ℤ) by
        rw [Nat.succ_sub_one]; push_cast; ring]
      rfl) F σ θ hθ σ₁ (fun z J₂ hJ₂ => by
      choose J₁ hJ₁ using fun χ : (UnifPre.GF (G := I.G.G) F).left ⟶ _ => exists_chart Xo.univ.t.PP.isLB (χ z)
      choose J' hJ' using fun χ : (UnifPre.GF (G := I.G.G) F).left ⟶ _ => exists_chart I.t'.PP.isLB (χ z)
      have u₁ := hu₁ _ (snd (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left z J₁ J₂ J' hJ₁ hJ₂ hJ'
      have r₂ : ((snd (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left ≫ ψ) ≫ I.m2.φ =
          UnifPre.gFK (G := I.G.G) F := (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ψ₁)
      have r₃ : (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left ≫ spMap (algebraMap T.Fr F) =
          ((snd (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left ≫ ψ) ≫ I.t'.G.hom :=
        ((Over.w (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G))).trans
          (Over.w (snd (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G))).symm).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ψ₂)).symm
      have b₁ : ((TFK (R := T.V) F) ◁ (Over.pullback (jK T.V)).map (I.G.act.act α)).left ≫
          (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left =
          (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left := by
        rw [← Over.comp_left, whiskerLeft_fst]
      have b₂ : ((TFK (R := T.V) F) ◁ (Over.pullback (jK T.V)).map (I.G.act.act α)).left ≫ UnifPre.gFK (G := I.G.G) F =
          (((snd (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left ≫ ψ) ≫ (I.t'.act.act α).left) ≫
            I.m2.φ := by
        rw [UnifPre.gFK, ← Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left, Category.assoc,
          Category.assoc _ ψ, Category.assoc _ _ I.m2.φ]
        exact congrArg (_ ≫ ·) hg₁.symm
      generalize (snd (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left ≫ ψ = r at u₁ r₂ r₃ b₂
      obtain ⟨zU, z₁, z₂⟩ : ∃ zU : (UnifPre.GF (G := I.G.G) F).left ⟶ (ptO Xo xF ⊗ Xo.univ.t.G).left,
          zU ≫ (fst (ptO Xo xF) Xo.univ.t.G).left =
            (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left ∧
          zU ≫ (snd (ptO Xo xF) Xo.univ.t.G).left = r ≫ I.m1.φ :=
        ⟨pullback.lift (f := xF) (g := Xo.univ.t.G.hom) _ _ (by
          rw [hx, ← Category.assoc, r₃, Category.assoc, Category.assoc, c₁.w]), pullback.lift_fst _ _ _,
          pullback.lift_snd _ _ _⟩
      have z₃ : zU ≫ (fst (ptO Xo xF) Xo.univ.t.G).left ≫ spMap (algebraMap T.Fr F) = r ≫ I.t'.G.hom := by
        rw [← Category.assoc, z₁, r₃]
      have d₁ : (lift (fst (ptO Xo xF) Xo.univ.t.G) (snd (ptO Xo xF) Xo.univ.t.G ≫ Xo.univ.t.act.act α)).left ≫
          (fst (ptO Xo xF) Xo.univ.t.G).left = (fst (ptO Xo xF) Xo.univ.t.G).left := by
        rw [← Over.comp_left, lift_fst]
      have d₂ : (zU ≫ (lift (fst (ptO Xo xF) Xo.univ.t.G) (snd (ptO Xo xF) Xo.univ.t.G ≫ Xo.univ.t.act.act α)).left) ≫
          (snd (ptO Xo xF) Xo.univ.t.G).left = (r ≫ (I.t'.act.act α).left) ≫ I.m1.φ := by
        rw [Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, ← Category.assoc, z₂, Category.assoc,
          Category.assoc]
        exact congrArg (r ≫ ·) (I.m1.act α).symm
      have t₁ := ht₁.2 _ r (𝟙 _) zU ((Category.id_comp _).trans r₂.symm) z₂ ((Category.id_comp _).trans z₁.symm) z₃
        z J₁ J₂ (J' r) hJ₁ hJ₂ (hJ' r)
      have t₂ := ht.2 _ (r ≫ (I.t'.act.act α).left) _ _ b₂ d₂ (by rw [b₁, Category.assoc, d₁, z₁])
        (by rw [Category.assoc, ← Category.assoc _ (fst (ptO Xo xF) Xo.univ.t.G).left, d₁, z₃, Category.assoc, Over.w])
        z J₁ J₂ (J' _) hJ₁ hJ₂ (hJ' _)
      have t₃ := twist_val htw zU z hJ₁
      rw [val_corr hJ₁ hβ zU, val_pull hJ₁, z₂] at t₃
      exact final_alg _ _ _ _ _ _ _ _ _ _ _ _ t₁ t₂ t₃ u₁)
  obtain ⟨π, -, hπ⟩ := GlobalTheory.PullLin.exists_pull_linearMap hL T.V P.D F (𝓞 E) P.oD H.w0 P.w0 α N k hN0 (by omega) hN
  rw [(hπ _ _).1 hP, ← (hπ _ _).1 hs₁]
  exact hs₂

end GlobalTheory.NormPullExp
