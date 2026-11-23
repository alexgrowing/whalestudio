import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedPre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineForgetFormsBijectiveSiteAndPairsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem compatibleForms_cocycles_differ_by_coboundary : ∀ (R R' : Type) [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') (κ : DividedPowers I) (κ' : DividedPowers I') (X X' : Scheme.{0}) (t : X ⟶ Sp R) (t' : X' ⟶ Sp R') (σ : R →+* R') (φ₀ : X' ⟶ X) (m : IsMor κ t κ' t' σ φ₀) (k : (KK κ t).Z1) (k' : (KK κ' t').Z1) (f : Z1 (O κ t)) (f' : Z1 (O κ' t')), k.1.1 = f.1 → k'.1.1 = f'.1 → H1.mk _ f' = m.pull1 (H1.mk _ f) → ∃ g, (KK κ' t').D0 g = (morMap m).p1 k.1 - k'.1 := by
  intro R R' _ _ I I' κ κ' X X' t t' σ φ₀ m k k' f f' hk hk' h
  have h' : H1.mk _ (m.coef.pullbackOneCocycle f) = H1.mk _ f' := h.symm
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 h'
  have hinj := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R' I' κ' X' t' X' (𝟙 X')).1.1.injective
  have hz : (morMap m).p1 k.1 - k'.1 ∈ (KK κ' t').Z1 :=
    sub_mem ((morMap m).z1 k).2 k'.2
  have h0 : (KK κ' t').fnMap.h1 (QuotientAddGroup.mk ⟨_, hz⟩ : (KK κ' t').H1) = 0 := by
    change (QuotientAddGroup.mk ((KK κ' t').fnMap.z1 ⟨_, hz⟩) : Cx.H1 _) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    refine ⟨g, ?_⟩
    refine Prod.ext ?_ ?_
    · funext T T' φ
      have e := congrFun (congrFun (congrFun hg T) T') φ
      have e1 := congrFun (congrFun (congrFun hk (m.obj T)) (m.obj T')) (m.functor.map φ)
      have e2 := congrFun (congrFun (congrFun hk' T) T') φ
      refine e.trans ?_
      exact congrArg₂ (fun u v : T'.B ↦ u - v) e1.symm e2.symm
    · funext T
      rfl
  have h1 := hinj (h0.trans (map_zero (KK κ' t').fnMap.h1).symm)
  rw [QuotientAddGroup.eq_zero_iff] at h1
  exact h1

end GlobalTheory.PDForm
