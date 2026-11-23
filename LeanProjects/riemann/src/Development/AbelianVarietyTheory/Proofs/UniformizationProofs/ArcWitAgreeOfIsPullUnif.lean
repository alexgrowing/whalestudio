import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

set_option maxHeartbeats 6400000 in

theorem arcWit_agree_of_isPullUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) → ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left), g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) → W.Agree W' ψ := by
  intro E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' hD₂ ⟨hφe, hee, w₂, hwe, T₂⟩ ψ bc hψ _ hbc hPU₂
    hact h3
  have he : eSec W.t.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec W'.t.G := by
    rw [Category.id_comp]
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ψ.hom)
  obtain ⟨wL₂, g₂, he₂, m₂, lev₂⟩ := hPU₂.lg
  have pg₂ := (isGen_iff wL₂).1 g₂
  refine ⟨hψ, hact, h3, he, pullCongr hbc wL₂,
    (isGen_iff _).2 (pgen_pullCongr hbc pg₂), ?_, fun n ψn hψn => ?_⟩
  · have HA := (maps_iff wL₂ _ (fun _ => eSec W'.t.G) _ W.P.U.LG.rig W'.P.U.LG.rig
      (Out.specOf (RingHom.id (PowerSeries k))) _ (rigPull_le _ _ he₂ W'.P.U.LG.L) (fun _ => rfl)).1 m₂
    have e0 : Out.specOf (RingHom.id (PowerSeries k)) = 𝟙 (𝟙_ (Over (Sp (PowerSeries k)))).left := by
      simp [Out.specOf]
    have HB : PMaps wL₂ (fun _ : PUnit => eSec W.t.G) (fun _ => eSec W'.t.G) (fun _ => 1) W.P.U.LG.rig W'.P.U.LG.rig
        (𝟙 _) := e0 ▸ HA
    exact (maps_iff (pullCongr hbc wL₂) _ (fun _ => eSec W'.t.G) _ W.P.U.LG.rig W'.P.U.LG.rig (𝟙 _) _
      (rigPull_le _ _ he W'.P.U.LG.L) (fun _ => rfl)).2 (pmaps_pullCongr hbc HB)
  · obtain ⟨h₂, hh₁, hh₂, ht₂, hw₂⟩ := lev₂ n
    have hfst : h₂ ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left =
        (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left ≫ ψ.hom.left := by
      rw [hh₁, hbc]
    obtain rfl : h₂ = ψn := by rw [hψn]; exact thick_map_eq ψ.hom h₂ hfst
    refine ⟨?_, fun A _ _ v => ⟨fun x pt₀ t₀ _ hg => ?_, fun j₀ jM jM' jL jL' H1 H2 H3 => ?_⟩⟩
    · exact (congrArg (fun f => (W.P.U.gt n).pG.left ≫ f) hφe.symm).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ W'.φ) hh₂)).trans (Category.assoc _ _ _))
    · obtain ⟨hψ₂, hm₂⟩ := ht₂ (W.e x)
      have P₂ := (maps_iff hD₂.w _ _ _ ((W.P.U.gt n).t (W.e x)) ((W'.P.U.gt n).t (hD₂.xe (W.e x))) h₂ _
        (Out.GeneratorPullback.pullAlong_le _ _ _ _ _ hψ₂) (fun _ => rfl)).1 hm₂
      have Q₂ := genRelR_transfer T₂ W'.P.D.toPre.P.isLB W.P.D.toPre.P.isLB
        (fun k => by rw [Category.assoc, hψ₂ k, Category.id_comp, Category.assoc])
        (pmaps_pullGen P₂ v (v ≫ h₂) rfl) t₀
      have Q₃ := genRelR_heq hφe hwe (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) v) t₀
      rw [← hee x]
      exact Q₂.2 (Q₃.2 hg)
    · have m1 := (top_le_iff_cpt _ _).1 H1
      have m2 := (top_le_iff_cpt _ _).1 H2
      have m3 := (top_le_iff_cpt _ _).1 H3
      have p2 : (v ≫ (W.P.U.gt n).pG.left) ≫ hD₂.e.hom.left ≫
          pullback.fst W'.P.D.toPre.P.A.hom (Out.specOf (RingHom.id (PowerSeries k))) =
          v ≫ h₂ ≫ (W'.P.U.gt n).pG.left := by rw [Category.assoc, hh₂]
      have p3 : (v ≫ h₂) ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left =
          (v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) ≫ ψ.hom.left := by
        rw [Category.assoc, hfst, Category.assoc]
      have e2 := congrArg (fun g => g (cpt A)) p2
      have e3 := congrArg (fun g => g (cpt A)) p3
      simp only at e2 e3
      have hjM := m1.2
      have mB1 : W'.φ ((hD₂.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom
          (Out.specOf (RingHom.id (PowerSeries k)))) ((v ≫ (W.P.U.gt n).pG.left) (cpt A))) ∈ a.D₀.P.L.U j₀ := by
        have := mem_pull.1 m2.1; rw [← e2] at this; exact this
      have mB2 : (hD₂.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (Out.specOf (RingHom.id (PowerSeries k))))
          ((v ≫ (W.P.U.gt n).pG.left) (cpt A)) ∈ W'.P.D.toPre.P.L.U jM' := by
        have := m2.2; rw [← e2] at this; exact this
      have mC1 := mem_pull.1 m3.1
      have mC2 := m3.2
      have mC3 : (bc.hom.left ≫ pullback.fst W'.t.G.hom (Out.specOf (RingHom.id (PowerSeries k))))
          ((v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) (cpt A)) ∈ W'.P.U.LG.L.U jL' := by
        rw [hbc]; exact mC1
      have mD : (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left ((v ≫ h₂) (cpt A)) ∈ W'.P.U.LG.L.U jL' := by
        have e3' : (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left ((v ≫ h₂) (cpt A)) =
            ψ.hom.left ((v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) (cpt A)) := e3
        rw [e3']; exact mC1
      have R2 := T₂ _ (v ≫ (W.P.U.gt n).pG.left) (cpt A) j₀ jM' jM mB1 mB2 hjM
      rw [p2] at R2
      have RE := gw_heq hφe hwe (v ≫ (W.P.U.gt n).pG.left) (cpt A) j₀ jM
      have RU2 : gw hD₂.w (v ≫ (W.P.U.gt n).pG.left) (cpt A) jM' jM *
          gm v (cpt A) _ ((W.P.U.w n).s (fun _ => jM, fun _ => jL)) =
          gm (v ≫ h₂) (cpt A) _ ((W'.P.U.w n).s (fun _ => jM', fun _ => jL')) *
          gw wL₂ (v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) (cpt A) jL' jL := by
        have := gm_of_res_eq' (hw₂ (fun _ => jM') jM jL (fun _ => jL')) v (y := cpt A)
          ⟨⟨⟨⟨mem_pull.2 mB2, hjM⟩, ⟨mem_pull.2 hjM, mem_pull.2 mC2⟩⟩, ⟨mem_pull.2 m2.2, mem_pull.2 mD⟩⟩,
            ⟨mem_pull.2 mC3, mC2⟩⟩
        rw [gm_pull, gm_pull, gm_pull] at this
        · exact this
        · exact ⟨mem_pull.2 mC3, mC2⟩
        · exact ⟨mem_pull.2 m2.2, mem_pull.2 mD⟩
        · exact ⟨mem_pull.2 mB2, hjM⟩
      have EU := congrArg (· * gm v (cpt A) _ ((W.P.U.w n).s (fun _ => jM, fun _ => jL))) (RE.symm.trans R2)
      beta_reduce at EU
      rw [_root_.mul_assoc, RU2, ← _root_.mul_assoc, ← gw_pullCongr hbc wL₂] at EU
      apply toStkA_injective
      rw [map_mul, map_mul, map_mul, toStkA_valR, toStkA_valR, toStkA_valR, toStkA_valR, toStkA_valR]
      · have EU' := congrArg Units.val EU
        simp only [Units.val_mul] at EU'
        exact EU'
      all_goals first
        | exact H1
        | exact H2
        | exact H3
        | exact (top_le_iff_cpt _ _).2 ⟨mem_pull.2 m2.2, mem_pull.2 mD⟩
        | exact (top_le_iff_cpt _ _).2 ⟨mem_pull.2 m1.2, mem_pull.2 mC2⟩

end GlobalTheory
