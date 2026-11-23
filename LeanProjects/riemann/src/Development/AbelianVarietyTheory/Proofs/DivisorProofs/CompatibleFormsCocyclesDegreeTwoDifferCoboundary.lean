import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedPre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineForgetFormsBijectiveSiteAndPairsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.ClsTwo

universe u

theorem cob_of_fn_cob {C : Type u} [Category.{0} C] (K : Cx C) (h : Function.Injective K.fnMap.h2)
    (z : K.T2) (hz : z ∈ K.Z2) (e : K.M0.c1)
    (he : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
      K.M0.map ψ (e T T' φ) - e T T'' (φ ≫ ψ) + e T' T'' ψ = z.1 T T' T'' φ ψ) :
    ∃ g, K.D1 g = z := by
  have h0 : K.fnMap.h2 (QuotientAddGroup.mk ⟨z, hz⟩) = 0 := by
    change (QuotientAddGroup.mk (K.fnMap.z2 ⟨z, hz⟩) : (Cx.single K.M0).H2) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    refine ⟨(e, 0), ?_⟩
    refine Prod.ext ?_ rfl
    funext T T' T'' φ ψ
    exact he T T' T'' φ ψ
  have h1 : (QuotientAddGroup.mk ⟨z, hz⟩ : K.H2) = 0 := h (h0.trans (map_zero _).symm)
  rw [QuotientAddGroup.eq_zero_iff] at h1
  exact h1

theorem cob_of_class_eq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') (κ : DividedPowers I) (κ' : DividedPowers I') (X X' : Scheme.{0}) (t : X ⟶ Sp R) (t' : X' ⟶ Sp R') (σ : R →+* R') (φ₀ : X' ⟶ X) (m : IsMor κ t κ' t' σ φ₀) (k : (KK κ t).Z2) (k' : (KK κ' t').Z2) (f : Z2 (O κ t)) (f' : Z2 (O κ' t')), k.1.1 = f.1 → k'.1.1 = f'.1 → H2.mk _ f' = m.pull2 (H2.mk _ f) → ∃ g, (KK κ' t').D1 g = (morMap m).p2 k.1 - k'.1 := by
  intro R R' _ _ I I' κ κ' X X' t t' σ φ₀ m k k' f f' hk hk' h
  have h' : H2.mk _ (m.coef.pullbackTwoCocycle f) = H2.mk _ f' := h.symm
  obtain ⟨e, he⟩ := H2.mk_eq_mk.1 h'
  refine cob_of_fn_cob (KK κ' t') (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R' I' κ' X' t' X' (𝟙 X')).1.2.injective _
    (AddSubgroup.sub_mem _ ((morMap m).p2_mem_Z2_of_mem_Z2 k.2) k'.2) e ?_
  intro T T' T'' φ ψ
  have h1 := congrFun (congrFun (congrFun (congrFun (congrFun he T) T') T'') φ) ψ
  refine h1.trans ?_
  have h2 : (m.coef.pullbackTwoCocycle f).1 T T' T'' φ ψ = ((morMap m).p2 k.1).1 T T' T'' φ ψ :=
    (congrFun (congrFun (congrFun (congrFun (congrFun hk _) _) _) (m.functor.map φ)) (m.functor.map ψ)).symm
  have h3 := congrFun (congrFun (congrFun (congrFun (congrFun hk' T) T') T'') φ) ψ
  exact congrArg₂ (fun a b : (O κ' t').obj T'' ↦ a - b) h2 h3.symm

end GlobalTheory.PDForm.ClsTwo
