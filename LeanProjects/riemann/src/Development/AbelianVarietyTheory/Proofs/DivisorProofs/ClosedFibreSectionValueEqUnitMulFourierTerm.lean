import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibreVal

variable {X Y Z : Scheme.{0}}

theorem gs_pow (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by simp only [gs_eq f y U h, map_pow]

theorem gs_sum (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (S : Finset κ) (a : κ → Γ(X, U)) :
    gs f y U (S.sum a) = S.sum (fun i => gs f y U (a i)) := by simp only [gs_eq f y U h, map_sum]

theorem gs_zero (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem mem_finset_inf {κ : Type} (S : Finset κ) (V : κ → X.Opens) (x : X) (h : ∀ i ∈ S, x ∈ V i) : x ∈ S.inf V :=
  Finset.inf_induction (p := fun W : X.Opens => x ∈ W) trivial (fun _ h₁ _ h₂ => ⟨h₁, h₂⟩) h

end GlobalTheory.Mum.FibreVal

theorem GlobalTheory.Mum.FibreVal.pG_app_eq_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) {V : D.P.A.left.Opens} (x : Γ(D.P.A.left, V))
    (h : ((pullback.fst D.P.A.hom (thick R I e)).app V).hom x = 0) : (g.pG.left.app V).hom x = 0 := by
  have h' := congrArg (g.q.left.app (pullback.fst D.P.A.hom (thick R I e) ⁻¹ᵁ V)).hom h
  rw [map_zero] at h'
  exact h'

theorem GlobalTheory.Mum.FibreVal.sval_comp_eq_zero {X W Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (g : Z ⟶ W) (p : W ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J)
    (h : (p.app (LB.wchart L φ (fun k => J ((g ≫ p) ≫ φ k)))).hom (s.f (fun k => J ((g ≫ p) ≫ φ k))) = 0) :
    sval s (g ≫ p) z J = 0 := by
  have e1 := gs_pull g p z (LB.wchart L φ (fun k => J ((g ≫ p) ≫ φ k))) (hJ.mem φ (g ≫ p)) (s.f (fun k => J ((g ≫ p) ≫ φ k)))
  rw [h, gs_zero] at e1
  exact e1.symm

set_option maxHeartbeats 1000000 in
open GlobalTheory.Mum.FibreVal in

theorem GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (T : Over (Sp R)) (g : T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) (y : T ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) g (Y.Φ T y) → ∀ (k : ℕ) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι) (J' : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good U.LG.L z J → Good D.toPre.P.L z J' → ∃ c : (T.left.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (s : H0 U.LG.L k), IsTermOf Y b τ → F.Lead α b → U.ExpandsAt 0 k s F.f → sval s (g ≫ (fstG (maximalIdeal R) 0 G).left) z J = c.val * sval τ y.left z J' := by
  intro R _ _ _ D A G _ _ U Y T g y hP k z J J' hJ hJ'
  let pp : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) := (fun _ => J' (g ≫ (U.gt 0).pG.left), fun _ => J (g ≫ (fstG (maximalIdeal R) 0 G).left))
  have hpp : g z ∈ (LB.div (D.toPre.P.L.pull (U.gt 0).pG.left) (U.LG.L.pull (fstG (maximalIdeal R) 0 G).left)).U pp :=
    ⟨Set.mem_iInter.2 fun _ => hJ' (g ≫ (U.gt 0).pG.left), Set.mem_iInter.2 fun _ => hJ (g ≫ (fstG (maximalIdeal R) 0 G).left)⟩
  refine ⟨(gm g z _ ((U.w 0).s pp) ^ k)⁻¹, ?_⟩
  intro α b τ F s hT hL hE
  obtain ⟨S, h0, hS⟩ := hE
  let j₁ : Fin 1 → U.LG.L.ι := fun _ => J (g ≫ (fstG (maximalIdeal R) 0 G).left)
  let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β i => J' ((g ≫ (U.gt 0).pG.left) ≫ D.toPre.famφB β i)
  let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β i => J' (g ≫ D.toPre.Oφ (U.gt 0).pG β i)
  have hcoh : CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2)))
        (Sum.elim (fun _ => pp.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
    have key : ∀ c, (Sum.elim (fun _ => pp.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) c =
        J' (g ≫ (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2))) c) := by
      rintro (a | a | a) <;> simp [jf, jt, pp]
    intro a c e
    rw [key, key, e]
  have e := hS pp j₁ jf jt rfl hcoh
  have hz : g z ∈ U.expW 0 pp j₁ S jf jt :=
    ⟨⟨hpp, hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (g ≫ (fstG (maximalIdeal R) 0 G).left)⟩, mem_finset_inf _ _ _ fun β _ =>
      ⟨hJ'.mem (D.toPre.famφB β) (g ≫ (U.gt 0).pG.left), hJ'.mem (D.toPre.Oφ (U.gt 0).pG β) g⟩⟩
  have e' := congrArg (gs g z (U.expW 0 pp j₁ S jf jt)) e
  rw [gs_mul g z _ hz, gs_pow g z _ hz, gs_unit g z _ hz, gm_res g z _ hz, gs_res g z _ hz] at e'
  erw [gs_pull g (fstG (maximalIdeal R) 0 G).left z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁) (Set.mem_iInter.2 fun _ => hJ (g ≫ (fstG (maximalIdeal R) 0 G).left))] at e'
  rw [gs_sum g z _ hz] at e'
  have hterm : ∀ (β : D.toPre.X) (hβ : β ∈ S),
      gs g z (U.expW 0 pp j₁ S jf jt)
        (((thickObj R (maximalIdeal R) 0 G).left.presheaf.map (homOfLE (U.expW_le_f 0 pp j₁ jf jt hβ)).op).hom
            (((U.gt 0).pG.left.app _).hom ((F.f β).f (jf β))) *
          (Semi.res (U.expWeight_le_chart_weight 0 pp j₁ jf jt hβ) (((U.gt 0).t β).s (jt β))).val) =
      sval (F.f β) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t β) g z J').val := by
    intro β hβ
    rw [gs_mul g z _ hz, gs_res g z _ hz, gs_unit g z _ hz]
    erw [gm_res g z _ hz]
    erw [gs_pull g (U.gt 0).pG.left z _ (hJ'.mem (D.toPre.famφB β) (g ≫ (U.gt 0).pG.left))]
    rfl
  replace e' := (e'.trans (Finset.sum_congr rfl fun (β : S) _ => hterm β.1 β.2)).trans
    (Finset.sum_attach S (fun β => sval (F.f β) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t β) g z J').val))
  have hsum : ∑ β ∈ S, sval (F.f β) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t β) g z J').val =
      sval (F.f α) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t α) g z J').val := by
    apply Finset.sum_eq_single α
    · intro β _ hne
      rw [sval_comp_eq_zero (F.f β) g (U.gt 0).pG.left z hJ' (pG_app_eq_zero (U.gt 0) _ (hL.2 β hne _)), zero_mul]
    · intro hα
      rw [sval_comp_eq_zero (F.f α) g (U.gt 0).pG.left z hJ' (h0 α hα _), zero_mul]
  rw [hsum] at e'
  have hq : (y ≫ Y.q).left = g ≫ (U.gt 0).pG.left := by
    have h1 := (Y.rep.1 T Y.H y (𝟙 Y.H)).1
    rw [Category.comp_id] at h1
    rw [Over.comp_left]
    exact h1.symm.trans hP.1
  have ht : val ((Y.Φ T y).s α) (𝟙 _) z J' = val ((U.gt 0).t α) g z J' :=
    (val_corr hJ' (hP.2 α) (𝟙 _)).trans ((val_pull hJ' _ g (𝟙 _)).trans (by rw [Category.id_comp]))
  rw [hT T y z J' hJ', hq, ht, ← hL.1, ← e',
    sval_of s (g ≫ (fstG (maximalIdeal R) 0 G).left) z J j₁ (fun _ => by rw [Category.comp_id]),
    ← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.one_mul]
