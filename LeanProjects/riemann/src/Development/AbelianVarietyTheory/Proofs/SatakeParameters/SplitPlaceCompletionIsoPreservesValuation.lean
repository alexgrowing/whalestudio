import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjSPV
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitConjVal

theorem eq_of_isEquiv {F : Type} [Field F] (v1 v2 : Valuation F (WithZero (Multiplicative ℤ)))
    (h : v1.IsEquiv v2) (a b : F) (ha : v1 a = WithZero.exp (-1)) (hb : v2 b = WithZero.exp (-1))
    (x : F) : v1 x = v2 x := by
  have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact WithZero.exp_ne_zero ha.symm
  have hb0 : b ≠ 0 := by rintro rfl; rw [map_zero] at hb; exact WithZero.exp_ne_zero hb.symm
  have hlt : ∀ r s : F, v1 r < v1 s ↔ v2 r < v2 s := fun r s => by
    rw [← not_le, ← not_le, h s r]
  have hval : ∀ y : F, y ≠ 0 → v2 y = WithZero.exp (WithZero.log (v2 y)) := fun y hy =>
    (WithZero.exp_log (by simpa using hy)).symm
  have hval1 : ∀ y : F, y ≠ 0 → v1 y = WithZero.exp (WithZero.log (v1 y)) := fun y hy =>
    (WithZero.exp_log (by simpa using hy)).symm
  have ha2 : v2 a = WithZero.exp (-1) := by
    have h1 : v2 a < 1 := by
      rw [← map_one v2, ← hlt, map_one, ha, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have h2 : v1 b < 1 := by
      rw [← map_one v1, hlt, map_one, hb, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have h3 : ¬ v1 b < v1 a := by
      intro h3
      rw [hlt, hb] at h3
      rw [hval a ha0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [hval a ha0, WithZero.exp_lt_exp] at h3
      omega
    have h4 : v1 b = v1 a := by
      rw [hval1 b hb0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
      rw [hval1 b hb0, ha, WithZero.exp_lt_exp] at h3
      rw [hval1 b hb0, ha, WithZero.exp_inj]
      omega
    rw [← hb]
    exact ((h.eq_iff).1 h4).symm
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  set k := WithZero.log (v1 x)
  have e1 : v1 x = v1 (a ^ (-k)) := by
    rw [map_zpow₀, ha, ← WithZero.exp_zsmul, hval1 x hx]
    congr 1; simp [k]
  rw [e1, (h.eq_iff).1 e1, map_zpow₀, map_zpow₀, ha, ha2]

theorem valuation_eq : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ x : s.v.adicCompletion (maximalRealSubfield L), Valued.v (c x) = Valued.v x := by
  intro L _ _ _ s c hc hci x
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion (maximalRealSubfield L) s.v
  have ho : IsOpenMap c :=
    AddMonoidHom.isOpenMap_of_sigmaCompact c.toAddEquiv.toAddMonoidHom c.surjective hc
  have hc' : Continuous c.symm := c.toEquiv.continuous_symm_iff.2 ho
  let v' : Valuation (s.v.adicCompletion (maximalRealSubfield L)) (WithZero (Multiplicative ℤ)) :=
    (Valued.v : Valuation (s.w.adicCompletion L) (WithZero (Multiplicative ℤ))).comap c.toRingHom
  have hE : v'.IsEquiv Valued.v := by
    rw [Valuation.isEquiv_iff_val_lt_one]
    intro y
    refine ⟨fun h => ?_, fun h => GlobalTheory.ConjParahoric.val_lt_one_map c.toRingHom hc h⟩
    simpa using GlobalTheory.ConjParahoric.val_lt_one_map c.symm.toRingHom hc' h
  obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
  obtain ⟨ϖ, hϖ⟩ := s.w.valuation_exists_uniformizer L
  have h1 : v' (s.i ϖ) = WithZero.exp (-1) := by
    show Valued.v (c (s.i ϖ)) = _
    rw [hci, ReciprocityTheory.Aut.adic_valued_algebraMap, hϖ]
  have h2 : Valued.v (algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) π) =
      WithZero.exp (-1) := by
    rw [ReciprocityTheory.Aut.adic_valued_algebraMap, hπ]
  exact eq_of_isEquiv v' Valued.v hE _ _ h1 h2 x

end GlobalTheory.SplitConjVal
