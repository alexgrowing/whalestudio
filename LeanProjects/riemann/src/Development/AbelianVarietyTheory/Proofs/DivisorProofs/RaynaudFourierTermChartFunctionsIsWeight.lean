import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.TermWt

theorem isWt_term : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Fin 1 → Q.P.L.ι) (V : Y.H.left.Opens), V ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j → IsWt Y α V (rsT (τ.f j) V) := by
  intro R _ _ Q O _ _ _ oa Y k α σ τ hT j V hV
  intro S _ φ x x' c a a' ha ha' hV₁ hV₂ hq hc
  subst ha ha'
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hV' : V ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)).U j := hV
  have germ : ∀ (b : Sp S ⟶ Y.H.left), ⊤ ≤ b ⁻¹ᵁ V → ∀ z,
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (valR b V (rsT (τ.f j) V))) =
        gs b z (LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j) (τ.f j) := by
    intro b hb z
    rw [valR, dif_pos hb, Iso.hom_inv_id_apply, rsT, dif_pos hV']
    refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z V (hb trivial) _).trans ?_)
    rw [Category.id_comp]
    exact gs_res b z hV (hb trivial) _
  have hqq : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := congrArg CommaMorphism.left hq
  apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
  refine fn_ext fun z _ => ?_
  obtain ⟨J, hJ, hJj⟩ := exists_good Q.P.L hL z (fun _ : Fin 1 => x.left ≫ Y.q.left) j
    (fun a b _ => congrArg j (Subsingleton.elim a b))
    (fun i => Set.mem_iInter.1 (hV (hV₁ (show z ∈ (⊤ : (Sp S).Opens) from trivial))) i)
  have e₁ : ∀ i, J (x.left ≫ (fun _ : Fin 1 => Y.q.left) i) = j i := hJj
  have e₂ : ∀ i, J (x'.left ≫ (fun _ : Fin 1 => Y.q.left) i) = j i := fun i => by rw [hqq]; exact hJj i
  have t₁ := hT (Over.mk (spMap φ)) x z J hJ
  have t₂ := hT (Over.mk (spMap φ)) x' z J hJ
  rw [sval_of τ _ z J j e₁] at t₁
  rw [sval_of τ _ z J j e₂, hq, hc α z J hJ, Units.val_mul] at t₂
  show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
  rw [germ _ hV₂ z, t₂, map_mul, gs_mul (𝟙 _) z ⊤ trivial, germ _ hV₁ z, t₁,
    show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c α : S) = (unitOn (c α)).val from rfl,
    gs_unit (𝟙 _) z ⊤ trivial]
  exact _root_.mul_left_comm _ _ _

end GlobalTheory.Heat.TermWt
