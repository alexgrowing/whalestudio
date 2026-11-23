import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzTwFin
import Development.DiscreteGroups.GlobalIrreducibility.DzTwChar

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands
  GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem lTw : LTw := by
  intro E _ _ w g _ i hi n K _ _ hK hn χ₀
  obtain ⟨χ, hχs, hχl⟩ := DzTw.exists_liftsChar i hi χ₀
  have hdet : ∀ k : GL (Fin n) ℤ_[g],
      χ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k))) =
        χ₀ (Matrix.GeneralLinearGroup.det (red g n k)) := by
    intro k
    rw [hχl.1 (Matrix.GeneralLinearGroup.det k) _ ?_]
    · congr 1
      refine Units.ext ?_
      show PadicInt.toZMod ((k : Matrix (Fin n) (Fin n) ℤ_[g]).det) =
        ((red g n k : Matrix (Fin n) (Fin n) (ZMod g))).det
      exact RingHom.map_det _ _
    · show (i.toRingHom.mapMatrix ((algebraMap ℤ_[g] ℚ_[g]).mapMatrix (k : Matrix (Fin n) (Fin n) ℤ_[g]))).det =
        i.toRingHom ((algebraMap ℤ_[g] ℚ_[g]) (k : Matrix (Fin n) (Fin n) ℤ_[g]).det)
      rw [RingHom.map_det, RingHom.map_det]
  refine ⟨χ, hχs, hχl, fun θ hθ τ hτ hθτ σ hσ => ?_⟩
  refine ⟨DzTw.twFD τ χ₀, irrTwist σ (detChar (Fin n) χ) (hχs.detChar (n := Fin n)),
    DzTw.isRegularChar_mul K χ₀ hθ, DzTw.isCusp_twFD τ χ₀ hτ, DzTw.char_twFD K hK hn χ₀ θ τ hθτ, ?_,
    Sigma.ext rfl (heq_of_eq (clTwist_cl σ _ _).symm)⟩
  obtain ⟨φ, hφ0, hφ⟩ := hσ
  refine ⟨φ, hφ0, fun k v => ?_⟩
  show φ ((((detChar (Fin n) χ₀ (red g n k)) : ℂˣ) : ℂ) • τ.ρ (red g n k) v) =
    (((detChar (Fin n) χ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k))) : ℂˣ) : ℂ) •
      σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k)) (φ v)
  rw [map_smul, hφ k v, detChar_apply, detChar_apply, hdet k, MonoidHom.comp_apply]

end DiscreteGroups.sglob.DzType
