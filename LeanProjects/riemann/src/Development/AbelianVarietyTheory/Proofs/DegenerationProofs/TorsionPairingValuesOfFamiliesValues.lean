import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FeOfPhiTriv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.WeilValues

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem top_le_chart {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (φ : K → (Y ⟶ X))
    (r : Sp F ⟶ Y) : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ (fun k => J (r ≫ φ k)) := fun z _ =>
  Good.mem (L := L) (z := z) (J := J) (fun ψ => hJ ψ trivial) φ r

theorem vF_ne_zero {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) : vF t r J ≠ 0 := by
  refine fun h => ?_
  exact (((Units.isUnit _).map _).map _).ne_zero ((dif_pos (top_le_chart hJ φ r)).symm.trans h)

theorem valF_const_mul (r : Sp F ⟶ Y) (π : Y ⟶ Sp F) (h : r ≫ π = 𝟙 _) (U : Y.Opens) (hU : ⊤ ≤ r ⁻¹ᵁ U) (z : F)
    (a : Γ(Y, U)) : valF r U (resTop U (π.appTop.hom (fnOf z)) * a) = z * valF r U a := by
  rw [valF, valF, dif_pos hU, dif_pos hU, map_mul, map_mul]
  congr 1
  have e : (r.appLE U ⊤ hU).hom (resTop U (π.appTop.hom (fnOf z))) = (r ≫ π).appTop.hom (fnOf z) := by
    simp only [resTop]
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp, RingHom.comp_apply]
    exact congrArg (fun g : Γ(Y, ⊤) ⟶ Γ(Sp F, ⊤) => g.hom (π.appTop.hom (fnOf z))) (Scheme.Hom.appLE_eq_app r (U := ⊤))
  rw [e, h]
  exact (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply z
end Val

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F}

theorem famV_smul (ν : NumOf D F N) {k : ℕ} {s : Fam D F k} {f : N.X → N.A → F} (h : ν.FamV s f) (z : F) :
    ν.FamV (z • s) (z • f) := by
  intro α x
  have e : (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst, Over.id_left]
  refine Eq.trans ?_ (valF_const_mul _ _ e _ (top_le_chart ν.good _ _) z _).symm
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, h α x]
  rfl

theorem exists_phiRel (hB : D.TauBimult) {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen) (s : Fam D F k) :
    ∃ t, PhiRel D F k p w s t := by
  obtain ⟨t, ht⟩ := DVR.exists_phi GlobalTheory.globalFns_holds p w hw hB s
  exact ⟨t, (DVR.phiRel_iff GlobalTheory.globalFns_holds p w hw s t).2 ht⟩

theorem phi_ne_zero {k : ℕ} (q : N.QT k) (w : Fˣ) {f : N.X → N.A → F} (hf : f ≠ 0) : N.phi q w f ≠ 0 := by
  intro h
  refine hf (funext fun α => funext fun x => ?_)
  have := congrFun (congrFun h (α + q.1.1.toAdd)) (x * q.1.2.b⁻¹)
  simp only [NumD.phi, add_sub_cancel_right, inv_mul_cancel_right, Pi.zero_apply, Units.mul_right_eq_zero] at this
  exact this

theorem weil_eq_values : BrGtSt → BrFamSt → BrWpSt := by
  intro _ hF R _ _ D hE hB F _ _ _ N ν k hk p p' q q' z hq hq'
  obtain ⟨h1, h2, -, ⟨s₀, f₀, hs₀, hf₀⟩, -, h6⟩ := hF R D hE hB F N ν k hk
  have key : ∀ w w', w.IsGen → w'.IsGen → ∀ s s₁ s₂ s₃ s₄ : Fam D F k,
      PhiRel D F k p' w' s s₁ → PhiRel D F k p w s₁ s₂ → PhiRel D F k p w s s₃ → PhiRel D F k p' w' s₃ s₄ →
      ∀ f, ν.FamV s f → ∃ f₄, ν.FamV s₄ f₄ ∧ ν.FamV s₂ ((N.wp q q' : F) • f₄) ∧ (f ≠ 0 → f₄ ≠ 0) := by
    intro w w' hw hw' s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄ f hf
    obtain ⟨f₁, a₁, -⟩ := h1 s₁
    obtain ⟨f₂, a₂, -⟩ := h1 s₂
    obtain ⟨f₃, a₃, -⟩ := h1 s₃
    obtain ⟨f₄, a₄, -⟩ := h1 s₄
    let u : Fˣ := Units.mk0 _ (vF_ne_zero ν.good w (𝟙 (Sp F)))
    let u' : Fˣ := Units.mk0 _ (vF_ne_zero ν.good w' (𝟙 (Sp F)))
    have e₁ := (h6 p' q' w' u' s s₁ f f₁ hq' hw' rfl hf a₁).1 r₁
    have e₂ := (h6 p q w u s₁ s₂ f₁ f₂ hq hw rfl a₁ a₂).1 r₂
    have e₃ := (h6 p q w u s s₃ f f₃ hq hw rfl hf a₃).1 r₃
    have e₄ := (h6 p' q' w' u' s₃ s₄ f₃ f₄ hq' hw' rfl a₃ a₄).1 r₄
    refine ⟨f₄, a₄, ?_, fun h => ?_⟩
    · rw [e₄, e₃, ← (GlobalTheory.Ex.PhiOp.phi_main F N k q q' u u' f).2.2.1, ← e₁, ← e₂]
      exact a₂
    · rw [e₄, e₃]
      exact phi_ne_zero _ _ (phi_ne_zero _ _ h)
  constructor
  · intro H
    obtain ⟨w, hw⟩ := DVR.exists_gen_of_local (V := F) D.P.L D.P.isLB (DegPre.lineφ D F p.g.b) (DegPre.lineε k)
    obtain ⟨w', hw'⟩ := DVR.exists_gen_of_local (V := F) D.P.L D.P.isLB (DegPre.lineφ D F p'.g.b) (DegPre.lineε k)
    obtain ⟨s₁, r₁⟩ := exists_phiRel hB p' w' hw' s₀
    obtain ⟨s₂, r₂⟩ := exists_phiRel hB p w hw s₁
    obtain ⟨s₃, r₃⟩ := exists_phiRel hB p w hw s₀
    obtain ⟨s₄, r₄⟩ := exists_phiRel hB p' w' hw' s₃
    obtain ⟨f₄, a₄, a₂, hne⟩ := key w w' hw hw' s₀ s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄ f₀ hs₀
    have e := (DVR.isSmul_iff z s₄ s₂).1 (H w w' hw hw' s₀ s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄)
    have b := famV_smul ν a₄ z
    rw [← e] at b
    exact smul_left_injective F (hne hf₀) ((h1 s₂).unique b a₂)
  · rintro rfl w w' hw hw' s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄
    obtain ⟨f, hf, -⟩ := h1 s
    obtain ⟨f₄, a₄, a₂, -⟩ := key w w' hw hw' s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄ f hf
    exact (DVR.isSmul_iff _ s₄ s₂).2 (h2 _ _ _ a₂ (famV_smul ν a₄ _))

end GlobalTheory.WeilValues
