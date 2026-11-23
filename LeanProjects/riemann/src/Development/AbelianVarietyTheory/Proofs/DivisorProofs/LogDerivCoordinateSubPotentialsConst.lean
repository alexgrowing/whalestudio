import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudCoordinateInChartsHasCharacterWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartFunctionOfWeightUnitLogDerivStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub)

theorem exists_const_of_glue : ∀ {K : Type} [Field K] (A₀ : Over (Sp K)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ {I : Type} (U : I → A₀.left.Opens) (f : ∀ i, Γ(A₀.left, U i)), ⨆ i, U i = ⊤ → (∀ i i', resG A₀.left (inf_le_left : U i ⊓ U i' ≤ U i) (f i) = resG A₀.left (inf_le_right : U i ⊓ U i' ≤ U i') (f i')) → ∃ c : K, ∀ (Z : Scheme.{0}) (b : Z ⟶ A₀.left) (z : Z) (i : I), b z ∈ U i → gs b z (U i) (f i) = cst (b ≫ A₀.hom) z c := by
  intro K _ A₀ _ hab I U f hcov hcomp
  obtain ⟨F, hF, -⟩ := A₀.left.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) (by rw [hcov]) f hcomp
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨s, hs⟩ := (hG (Sp K) A₀ hab).2 F
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom s, fun Z b z i hz => ?_⟩
  rw [cst, Iso.hom_inv_id_apply, ← gs_pull b A₀.hom z ⊤ trivial s, ← hF i]
  refine (gs_res b z (le_top : U i ≤ ⊤) hz F).trans ?_
  rw [← hs]
  rfl

theorem exists_coordEq : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → ∀ α : Q.X, ChartFree Y h ν m₀ V pb α → ∃ c : K, CoordEq Y h ν m₀ V pb α c := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hC hD α hfree
  obtain ⟨T, hT₁, hT₂⟩ := hF.exists_strictHenselian_absolutely_closed_local_ring α
  have hT0 : T 0 = 𝟙 _ := hF.T_zero (hT₁ 0) (hT₂ 0)
  have hab : IsAbelianScheme A₀ := PolPull.isAbelianScheme_of_isGrpPullback Q.P.isAb hF.pull
  have hV : ∀ i, V i ≤ Q.P.L.U (h.j i) := hC.2.2.1
  let U : (Fin 4 → h.J) → Q.P.A.left.Opens := fun i =>
    V (i 0) ⊓ LB.wchart Q.P.L (Q.famφB α) (fun j => h.j (i j))
  have hU : ∀ i, Y.q.left ⁻¹ᵁ U i ≤ h.W (i 0) ⊓ xU Y α (fun j => h.j (i j)) := by
    intro i y hy
    refine ⟨?_, Set.mem_iInter.2 fun k => ?_⟩
    · rw [hD.1]; exact hy.1
    · have := Set.mem_iInter.1 hy.2 (![1, 2, 0, 3] k)
      show y ∈ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k ⁻¹ᵁ Q.P.L.U (h.j (i (![1, 2, 0, 3] k)))
      rw [gtφT_eq, Scheme.Hom.comp_preimage]
      exact this
  have exA : ∀ i : Fin 4 → h.J, ∃ A : Γ(Q.P.A.left, U i), (Y.q.left.app (U i)).hom A *
      rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i) =
      dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i)) := fun i =>
    GlobalTheory.T.exists_abelianPart_function_of_weight_unit_logDeriv Y h ν hF.wt hF.basic (i 0) α (U i) ((hU i).trans inf_le_left) _
      (by rw [GlobalTheory.KS.GlueDer.rsT_eq ((hU i).trans inf_le_right)]; exact (Units.isUnit _).map _)
      (GlobalTheory.T.raynaud_coordinate_in_charts_has_character_weight Y α _ _ ((hU i).trans inf_le_right))
  choose A hA using exA
  let Oi : (Fin 4 → h.J) → A₀.left.Opens := fun i =>
    T 0 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 0)) ⊓ T 1 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 1)) ⊓ T 2 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 2)) ⊓ T 3 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 3))
  have memO : ∀ i (p : A₀.left), p ∈ Oi i ↔ ∀ j, m₀ (T j p) ∈ V (i j) := by
    intro i p
    constructor
    · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ j
      fin_cases j
      exacts [h0, h1, h2, h3]
    · intro H
      exact ⟨⟨⟨H 0, H 1⟩, H 2⟩, H 3⟩
  have hOU : ∀ i, Oi i ≤ m₀ ⁻¹ᵁ U i := by
    intro i p hp
    have H := (memO i p).1 hp
    refine ⟨?_, Set.mem_iInter.2 fun k => ?_⟩
    · have := H 0
      rw [hT0] at this
      exact this
    · have := hV _ (H k)
      rw [← Scheme.Hom.comp_apply, hT₁ k, Scheme.Hom.comp_apply] at this
      exact this
  have hOT : ∀ i j, Oi i ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j)) := fun i j p hp => (memO i p).1 hp j
  let f : ∀ i, Γ(A₀.left, Oi i) := fun i =>
    pbT m₀ (A i) (Oi i) + pbT (T 0) (pb (i 0)) (Oi i) - pbT (T 1) (pb (i 1)) (Oi i) +
      pbT (T 2) (pb (i 2)) (Oi i) - pbT (T 3) (pb (i 3)) (Oi i)
  have hCA : ∀ i (Z : Scheme.{0}) (a : Z ⟶ Y.H.left) (b : Z ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ z, b z ∈ Oi i →
      CoordAt Y h ν m₀ V pb α i T a b z (gs b z (Oi i) (f i)) := by
    intro i Z a b w z hz
    have hza : a z ∈ Y.q.left ⁻¹ᵁ U i := by
      show Y.q.left (a z) ∈ U i
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
      exact hOU i hz
    have e1 : rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i) =
        resG _ (hU i) (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))) := by
      rw [← GlobalTheory.KS.GlueDer.rsT_eq (hU i)]
      refine fn_ext fun y hy => ?_
      rw [gs_rsT (𝟙 _) y ((hU i).trans inf_le_right) hy, gs_rsT (𝟙 _) y (hU i) hy,
        gs_rsT (𝟙 _) y inf_le_right (hU i hy)]
    have e2 : dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i)) =
        resG _ (hU i) (dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j)))) := by
      rw [e1]
      exact (isField_dE h ν hF.field (i 0)).2.2 _ _ (hU i) inf_le_left _
    have lhs : gs a z (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))
        (dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j)))) =
        gs (b ≫ m₀) z (U i) (A i) * gs a z (xU Y α fun j => h.j (i j)) (xc Y α fun j => h.j (i j)).val := by
      rw [← gs_res a z (hU i) hza, ← e2, ← hA i, gs_mul a z _ hza, gs_rsT a z ((hU i).trans inf_le_right) hza,
        gs_pull a Y.q.left z (U i) hza, w]
    have rhs : gs b z (Oi i) (f i) = gs (b ≫ m₀) z (U i) (A i) +
        gs (b ≫ T 0) z (m₀ ⁻¹ᵁ V (i 0)) (pb (i 0)) - gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V (i 1)) (pb (i 1)) +
        gs (b ≫ T 2) z (m₀ ⁻¹ᵁ V (i 2)) (pb (i 2)) - gs (b ≫ T 3) z (m₀ ⁻¹ᵁ V (i 3)) (pb (i 3)) := by
      simp only [f, gs_add b z _ hz, gs_sub b z _ hz, gs_pbT b m₀ z (hOU i) hz, gs_pbT b (T _) z (hOT i _) hz]
    unfold CoordAt
    rw [lhs, rhs]
    ring
  have uniq : ∀ i (Z : Scheme.{0}) (a : Z ⟶ Y.H.left) (b : Z ⟶ A₀.left) (z : Z) (w₁ w₂ : Z.presheaf.stalk z),
      a z ∈ xU Y α (fun j => h.j (i j)) → CoordAt Y h ν m₀ V pb α i T a b z w₁ →
      CoordAt Y h ν m₀ V pb α i T a b z w₂ → w₁ = w₂ := by
    intro i Z a b z w₁ w₂ hm h₁ h₂
    unfold CoordAt at h₁ h₂
    rw [h₁, gs_unit a z _ hm] at h₂
    exact add_left_cancel ((Units.isUnit _).mul_left_cancel h₂)
  have hover : ∀ i i', resG A₀.left (inf_le_left : Oi i ⊓ Oi i' ≤ Oi i) (f i) =
      resG A₀.left (inf_le_right : Oi i ⊓ Oi i' ≤ Oi i') (f i') := by
    intro i i'
    refine ext_lift Y m₀ fun Z a b w z hz => ?_
    rw [gs_res b z inf_le_left hz, gs_res b z inf_le_right hz]
    have hi : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j) := fun j => (memO i (b z)).1 hz.1 j
    have hi' : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i' j) := fun j => (memO i' (b z)).1 hz.2 j
    have h₁ := hfree T hT₁ hT₂ Z a b w z i i' hi hi' _ (hCA i Z a b w z hz.1)
    exact uniq i' Z a b z _ _ (hF.mem_chart hD hV hT₁ w hi').2 h₁ (hCA i' Z a b w z hz.2)
  have hcov : ⨆ i, Oi i = ⊤ := by
    refine eq_top_iff.2 fun p _ => ?_
    have ex : ∀ j, ∃ k, m₀ (T j p) ∈ V k := fun j => by
      have : m₀ (T j p) ∈ (⨆ k, V k) := by rw [hC.2.1]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    choose i hi using ex
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (memO i p).2 hi⟩
  obtain ⟨c, hc⟩ := exists_const_of_glue A₀ hab Oi f hcov hover
  refine ⟨c, fun T' hT'₁ hT'₂ Z a b w z i hi => ?_⟩
  obtain rfl : T' = T := funext fun j =>
    hF.pull.1.hom_ext ((hT'₁ j).trans (hT₁ j).symm) ((hT'₂ j).trans (hT₂ j).symm)
  have hz : b z ∈ Oi i := (memO i (b z)).2 hi
  rw [← hc Z b z i hz]
  exact hCA i Z a b w z hz

end GlobalTheory.HeatConn
