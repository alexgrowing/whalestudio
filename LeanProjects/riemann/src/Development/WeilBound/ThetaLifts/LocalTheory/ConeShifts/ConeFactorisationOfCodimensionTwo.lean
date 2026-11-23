import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PureIte
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.ConeIntegralFactorisation

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem unr_div {χ χ' : Chr F E} {S : Set (Pl F)} (h : UnrOff χ S) (h' : UnrOff χ' S) : UnrOff (χ / χ') S := fun w hw x hx => by
  have a := h w hw x hx
  have b := h' w hw x hx
  have : locChar (χ / χ') w x = locChar χ w x / locChar χ' w x := map_div Circle.toUnits _ _
  rw [this, a, b, div_one]

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem nu_cont (t : IsTriple B G X om om') : Continuous X.ν := (isHecke_div t.chars.heckeα t.chars.heckeβ).1

theorem nu_res (t : IsTriple B G X om om') : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.ν 0 := fun x => by
  have h := resEtaPow_div t.chars.resα t.chars.resβ x
  rw [(add_comm a a' ▸ t.geo.even : Even (a' + a)).neg_one_pow] at h
  rw [pow_zero]
  exact h

theorem coneIntegralFactorisation_of (hA : ActsEx) (hI : IdeleFub) (hKF : KFub) (hV : VacFixX) (hS : VacShift) (hAr : ArchCone) (hF : FinM)
    (hP : PureFac) (hSp : SchSpan) (hId : IdealM) : PositivityTheory.ThKEnd.Comp.ConeIntegralFactorisation := by
  obtain ⟨a₁, a₂, b₁, b₂, hId⟩ := hId
  refine ⟨a₁, a₂, ?_⟩
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' c e ei ev he hE K μK μ m hK h1 h2 hm
  by_cases ex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' t t₁ => (ex ⟨X, om, om', om₁, om₁', t, t₁⟩).elim⟩
  obtain ⟨X₀, o, o', o₁, o₁', t₀, t₀₁⟩ := ex
  have hC : Cfg B G.M G₁.M H H' e (shiftA H H') :=
    ⟨t₀.base, ⟨_, _, t₀.geo.hV⟩, ⟨_, _, t₀.geo.hW⟩, ⟨_, _, t₀₁.geo.hV⟩, ⟨_, _, t₀₁.geo.hW⟩, t₀.geo.hM, t₀₁.geo.hM,
      ⟨_, _, c.hH⟩, ⟨_, _, c.hH'⟩, .inl ⟨he, rfl⟩⟩
  obtain ⟨𝔞, h0, hlat, hcnt, hval⟩ := hId F E σ B _ _ _ _ _ _ _ _ H H' _ _ _ _ _ _ _ _ t₀.base t₀.geo.hV t₀.geo.hW c.hH c.hH'
    (by omega) (by omega) (by omega) (by omega) _ _ _ (.inl ⟨rfl, rfl, rfl⟩)
  have hz : 2 ≤ (b + 2 - a') / 2 := by
    have := t₀.geo.eBig
    omega
  obtain ⟨κ, hκ, HG⟩ := gen hA hI hKF hV hS hAr hF hP hSp hC hE hK h1 h2 hm h0 hlat hz
  refine ⟨κ, hκ, fun X om om' om₁ om₁' t _ => ?_⟩
  have := HG _ _ _ _ _ _ _ (pairV t) X.ν X.S₀ X.T (nu_cont t) (by classical exact Finset.subset_union_left)
    (unr_div t.chars.unrα t.chars.unrβ) t.chars.unrβ (unr_div t.chars.unrβ t.chars.unrα)
    fun w hw => ⟨t.chars.ram w hw, hcnt w (t.chars.sub hw)⟩
  rw [hval X.ν (nu_cont t) (nu_res t) fun w hw => unr_div t.chars.unrα t.chars.unrβ w fun h => hw (t.chars.sub h)] at this
  exact this

theorem coneFacB_of (hA : ActsEx) (hI : IdeleFub) (hKF : KFub) (hV : VacFixX) (hS : VacShift) (hAr : ArchCone) (hF : FinM)
    (hP : PureFac) (hSp : SchSpan) (hId : IdealM) : ConeFacB := by
  obtain ⟨a₁, a₂, b₁, b₂, hId⟩ := hId
  refine ⟨b₁, b₂, ?_⟩
  intro F E _ _ _ _ _ σ B a b G G₁ H H' c e ei ev he hE K μK μ m hK h1 h2 hm
  by_cases ex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' t t₁ => (ex ⟨X, om, om', om₁, om₁', t, t₁⟩).elim⟩
  obtain ⟨X₀, o, o', o₁, o₁', t₀, t₀₁⟩ := ex
  have hC : Cfg B G.M' G₁.M' H H' e (shiftB σ H H') :=
    ⟨t₀.base, ⟨_, _, t₀.geo.hV'⟩, ⟨_, _, t₀.geo.hW⟩, ⟨_, _, t₀₁.geo.hV'⟩, ⟨_, _, t₀₁.geo.hW⟩, t₀.geo.hM', t₀₁.geo.hM',
      ⟨_, _, c.hH⟩, ⟨_, _, c.hH'⟩, .inr ⟨he, rfl⟩⟩
  obtain ⟨𝔞, h0, hlat, hcnt, hval⟩ := hId F E σ B _ _ _ _ _ _ _ _ H H' _ _ _ _ _ _ _ _ t₀.base t₀.geo.hV' t₀.geo.hW c.hH c.hH'
    (by omega) (by omega) (by omega) (by omega) _ _ _ (.inr ⟨rfl, rfl, rfl⟩)
  have hz : 2 ≤ (a - (b + 2)) / 2 + 1 := by
    have := t₀.geo.eBig
    omega
  obtain ⟨κ, hκ, HG⟩ := gen hA hI hKF hV hS hAr hF hP hSp hC hE hK h1 h2 hm h0 hlat hz
  refine ⟨κ, hκ, fun X om om' om₁ om₁' t _ => ?_⟩
  have := HG _ _ _ _ _ _ _ (pairV' t) X.ν X.S₀ X.T (nu_cont t) (by classical exact Finset.subset_union_left)
    (unr_div t.chars.unrα t.chars.unrβ) t.chars.unrα (unr_div t.chars.unrα t.chars.unrβ)
    fun w hw => ⟨t.chars.ram w hw, hcnt w (t.chars.sub hw)⟩
  rw [hval X.ν (nu_cont t) (nu_res t) fun w hw => unr_div t.chars.unrα t.chars.unrβ w fun h => hw (t.chars.sub h)] at this
  exact this

theorem coneFactorisation_of_codimension_two (h : PositivityTheory.ThKEnd.Comp.ConeIntegralFactorisation) : ConeFacA := by
  obtain ⟨e₁, e₂, h⟩ := h
  exact ⟨e₁, e₂, fun F E _ _ _ _ _ σ B b a' G G₁ H H' c => h F E σ B b a' G G₁ H H' ⟨c.eV, c.q1.trans c.q0.symm, c.ep, c.hH, c.hH'⟩⟩

end PositivityTheory.ThKG.Loc.Cone

end
