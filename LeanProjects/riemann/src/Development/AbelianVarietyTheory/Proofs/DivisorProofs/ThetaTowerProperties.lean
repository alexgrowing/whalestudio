import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPlaneSplitHermitianLatticeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianSelfDualLatticeHyperbolicPlaneSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta

noncomputable section

namespace GlobalTheory.ThK

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem resEtaPow_of_add_two {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ : Eˣ →* Circle} {n : ℕ} (h : ResEtaPow K χ (n + 2)) : ResEtaPow K χ n := by
  intro a
  rw [h a]
  simp [pow_add]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) :
    ResEtaPow K (χ / χ') (n + m) := by
  intro a
  rw [MonoidHom.div_apply, Circle.coe_div, h a, h' a]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg, inv_one, ← pow_add]

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem towerB_of (hP : GlobalTheory.FunPr.Hypotheses₂) : TowerB := by
  intro F E _ _ _ _ _ σ B a b G X om om' hT hq
  have g := hT.geo
  have c := hT.chars
  have hb := g.aBig
  have hl := g.lt
  obtain ⟨Y', V₁, H, hY', hV₁, hH⟩ := GlobalTheory.KTowerPlane.exists_hyperbolic_split F E σ B hT.base (b + 2) b rfl (by omega) G.V' G.q (b + 2 - G.q)
    hq (by omega) g.hV' 0 (b + 1) (by omega) (by omega)
  obtain ⟨W', W₁, H', hW', hW₁, hH'⟩ := GlobalTheory.PlaneSkew.plane_skew F E σ B hT.base (a + (b + 2)) (a + b) (by omega) (by omega) G.W
    (a + (b + 2) - (G.p + G.q)) (G.p + G.q) (by omega) (by omega) g.hW a (a + b + 1) (by omega) (by omega)
  have hV0 : (reS G.V G.V).IsHerm σ B (a - G.p) G.p := g.hV
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.ModelEx.model_exists F E σ B hT.base a (a + b) (reS G.V G.V) W₁ _ _ _ _ hV0 hW₁
  obtain ⟨M₁', hM₁'⟩ := GlobalTheory.ModelEx.model_exists F E σ B hT.base b (a + b) V₁ W₁ _ _ _ _ hV₁ hW₁
  have rα : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.α b := resEtaPow_of_add_two c.resα
  obtain ⟨om₁, hom₁⟩ := GlobalTheory.WeilExGen.exists_isWeil hP F E σ B hT.base a (a + b) (reS G.V G.V) W₁ _ _ _ _ hV0 hW₁ M₁ hM₁ X.β (X.β / X.α)
    c.heckeβ (isHecke_div c.heckeβ c.heckeα) c.resβ (resEtaPow_div c.resβ rα)
  obtain ⟨om₁', hom₁'⟩ := GlobalTheory.WeilExGen.exists_isWeil hP F E σ B hT.base b (a + b) V₁ W₁ _ _ _ _ hV₁ hW₁ M₁' hM₁' X.α (X.α / X.β)
    c.heckeα (isHecke_div c.heckeα c.heckeβ) rα (by rw [Nat.add_comm]; exact resEtaPow_div rα c.resβ)
  refine ⟨G.V, Y', W', ⟨hT.base, ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hV0, hY', hW', ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩,
      ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩, c, hT.weil, hT.weil'⟩,
    ⟨G.p, G.q - 1, reS G.V G.V, V₁, W₁, M₁, M₁'⟩, H, H', ⟨rfl, rfl, ?_, hH, hH'⟩, om₁, om₁', ⟨hT.base, ?_, ?_, hom₁, hom₁'⟩⟩
  · show G.q - 1 + 1 = G.q
    omega
  · have he := g.eBig
    refine ⟨by omega, ?_, fun w => ?_, ?_, ?_, hV0, ?_, ?_, hM₁, hM₁'⟩
    · obtain ⟨k, hk⟩ := g.even
      exact ⟨k - 1, by omega⟩
    · have := g.kappa w
      push_cast at this ⊢
      omega
    · show 2 * (G.p + (G.q - 1)) + 1 < (a - b) / 2
      omega
    · show 2 * (G.p + (G.q - 1)) + 1 < b
      omega
    · show V₁.IsHerm σ B (G.q - 1) (b - (G.q - 1))
      rw [show b - (G.q - 1) = b + 2 - G.q - 1 by omega]
      exact hV₁
    · show W₁.IsSkew σ B (a + b - (G.p + (G.q - 1))) (G.p + (G.q - 1))
      rw [show a + b - (G.p + (G.q - 1)) = a + (b + 2) - (G.p + G.q) - 1 by omega,
        show G.p + (G.q - 1) = G.p + G.q - 1 by omega]
      exact hW₁
  · exact ⟨c.heckeα, c.heckeβ, rα, c.resβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩

theorem towerA_of (hP : GlobalTheory.FunPr.Hypotheses₂) : TowerA := by
  intro F E _ _ _ _ _ σ B b a' G X om om' hT hq0 hp
  have g := hT.geo
  have c := hT.chars
  have hb := g.aBig
  have hl := g.lt
  have he := g.eBig
  rw [hq0] at hb he
  obtain ⟨Y', V₁, H, hY', hV₁, hH⟩ := GlobalTheory.KTowerPlane.exists_hyperbolic_split F E σ B hT.base (b + 2) b rfl (by omega) G.V (b + 2 - G.p) G.p
    (by omega) hp g.hV 0 (b + 1) (by omega) (by omega)
  have hW0 := g.hW
  rw [hq0] at hW0
  obtain ⟨W', W₁, H', hW', hW₁, hH'⟩ := GlobalTheory.PlaneSkew.plane_skew F E σ B hT.base (b + 2 + a') (b + a') (by omega) (by omega) G.W
    (b + 2 + a' - (G.p + 0)) (G.p + 0) (by omega) (by omega) hW0 0 (b + 1) (by omega) (by omega)
  have hV0' : (reS G.V' G.V').IsHerm σ B 0 (a' - 0) := by
    have := g.hV'
    rw [hq0] at this
    exact this
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.ModelEx.model_exists F E σ B hT.base b (b + a') V₁ W₁ _ _ _ _ hV₁ hW₁
  obtain ⟨M₁', hM₁'⟩ := GlobalTheory.ModelEx.model_exists F E σ B hT.base a' (b + a') (reS G.V' G.V') W₁ _ _ _ _ hV0' hW₁
  have rβ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.β b := resEtaPow_of_add_two c.resβ
  obtain ⟨om₁, hom₁⟩ := GlobalTheory.WeilExGen.exists_isWeil hP F E σ B hT.base b (b + a') V₁ W₁ _ _ _ _ hV₁ hW₁ M₁ hM₁ X.β (X.β / X.α)
    c.heckeβ (isHecke_div c.heckeβ c.heckeα) rβ (resEtaPow_div rβ c.resα)
  obtain ⟨om₁', hom₁'⟩ := GlobalTheory.WeilExGen.exists_isWeil hP F E σ B hT.base a' (b + a') (reS G.V' G.V') W₁ _ _ _ _ hV0' hW₁ M₁' hM₁' X.α (X.α / X.β)
    c.heckeα (isHecke_div c.heckeα c.heckeβ) c.resα (by rw [Nat.add_comm]; exact resEtaPow_div c.resα rβ)
  refine ⟨Y', G.V', W', ⟨hT.base, ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hY', g.hV',
      (by show (reS G.W W').IsSkew σ B (b + 2 + a' - (G.p + G.q)) (G.p + G.q); rw [hq0]; exact hW'),
      ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩, ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩,
      c, hT.weil, hT.weil'⟩,
    ⟨G.p - 1, 0, V₁, reS G.V' G.V', W₁, M₁, M₁'⟩, H, H', ⟨rfl, hq0, rfl, ?_, hH, hH'⟩, om₁, om₁', ⟨hT.base, ?_, ?_, hom₁, hom₁'⟩⟩
  · show G.p - 1 + 1 = G.p
    omega
  · refine ⟨?_, ?_, fun w => ?_, ?_, ?_, ?_, hV0', ?_, hM₁, hM₁'⟩
    · show a' < b
      omega
    · obtain ⟨k, hk⟩ := g.even
      exact ⟨k - 1, by omega⟩
    · have := g.kappa w
      push_cast at this ⊢
      omega
    · show 2 * (G.p - 1 + 0) + 1 < (b - a') / 2
      omega
    · show 2 * (G.p - 1 + 0) + 1 < a'
      omega
    · show V₁.IsHerm σ B (b - (G.p - 1)) (G.p - 1)
      rw [show b - (G.p - 1) = b + 2 - G.p - 1 by omega]
      exact hV₁
    · show W₁.IsSkew σ B (b + a' - (G.p - 1 + 0)) (G.p - 1 + 0)
      rw [show b + a' - (G.p - 1 + 0) = b + 2 + a' - (G.p + 0) - 1 by omega,
        show G.p - 1 + 0 = G.p + 0 - 1 by omega]
      exact hW₁
  · exact ⟨c.heckeα, c.heckeβ, c.resα, rβ, c.expα, c.expβ, c.disj, c.sub, c.ram, c.unrα, c.unrβ, c.good⟩

theorem towerA_and_towerB (hP : GlobalTheory.FunPr.Hypotheses₂) : TowerA ∧ TowerB := ⟨towerA_of hP, towerB_of hP⟩

end GlobalTheory.ThK
