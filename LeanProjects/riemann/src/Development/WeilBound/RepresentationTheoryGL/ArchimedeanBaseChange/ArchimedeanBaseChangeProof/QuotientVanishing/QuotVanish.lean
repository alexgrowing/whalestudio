import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.D4

open PositivityTheory.Rg.BcB

def NormEq : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G)
  (μH : Measure H) [SFinite μH] [μH.IsInvInvariant] (F : G → ℂ) (ρ₁ ρ₂ : G → ENNReal), Measurable F →
  (∀ h ∈ H, ∀ g, F (h * g) = F g) → IsQuotNormaliser H μH ρ₁ → IsQuotNormaliser H μH ρ₂ →
  ∫ g, F g * ((ρ₁ g).toReal : ℂ) ∂μ = ∫ g, F g * ((ρ₂ g).toReal : ℂ) ∂μ

def flagStab {K : Type} [Field K] {n : ℕ} (W₁ W₂ : Submodule K (Fin n → K)) : Subgroup (GL (Fin n) K) where
  carrier := {g | W₁.map (Matrix.toLin' g.val) = W₁ ∧ W₂.map (Matrix.toLin' g.val) = W₂}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp] at *
    rw [hb.1, ha.1, hb.2, ha.2]; exact ⟨rfl, rfl⟩
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at *
    have e : ∀ W : Submodule K (Fin n → K), W.map (Matrix.toLin' a.val) = W →
        W.map (Matrix.toLin' (a⁻¹ : GL (Fin n) K).val) = W := fun W hW => by
      conv_lhs => rw [← hW]
      rw [← Submodule.map_comp, ← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one,
        Submodule.map_id]
    exact ⟨e _ ha.1, e _ ha.2⟩

def IwaFlag : Prop := ∀ (n : ℕ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ → ∀ g : GL (Fin n) ℂ,
  ∃ q ∈ flagStab W₁ W₂, ∃ k : GL (Fin n) ℂ, thetaR (starRingEnd ℂ) n k = k ∧ g = q * k

def uOf {K : Type} [Field K] {n : ℕ} {W₁ W₂ : Submodule K (Fin n → K)} (hW : W₁ ≤ W₂) (X : nilrad W₁ W₂) :
    GL (Fin n) K where
  val := 1 + X.1
  inv := 1 - X.1 + X.1 * X.1
  val_inv := by
    have h3 : X.1 * (X.1 * X.1) = 0 := by
      ext i j
      have := congrFun (X.2.2.2 _ (X.2.2.1 _ (X.2.1 (Pi.single j 1)))) i
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
      simpa [Matrix.mul_assoc] using this
    noncomm_ring
    rw [h3]; simp
  inv_val := by
    have h3 : X.1 * (X.1 * X.1) = 0 := by
      ext i j
      have := congrFun (X.2.2.2 _ (X.2.2.1 _ (X.2.1 (Pi.single j 1)))) i
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
      simpa [Matrix.mul_assoc] using this
    noncomm_ring
    rw [h3]; simp

def NilChange : Prop := ∀ (n : ℕ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) (e : GL (Fin n) ℂ),
  (e * thetaR (starRingEnd ℂ) n e).val.charpoly.Separable → perpD (starRingEnd ℂ) e W₁ = W₂ →
  perpD (starRingEnd ℂ) e W₂ = W₁ → ∀ [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)]
  (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure],
  ∃ (Φ : nilrad W₁ W₂ ≃ᵐ nilrad W₁ W₂) (c : NNReal), 0 < c ∧ ν.map Φ = c • ν ∧
    ∀ X, uOf hW (Φ X) * e = twConj (thetaR (starRingEnd ℂ) n) (uOf hW X) e

def CentFlag : Prop := ∀ (n : ℕ) (d : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)),
  (d * thetaR (starRingEnd ℂ) n d).val.charpoly.Separable → perpD (starRingEnd ℂ) d W₁ = W₂ →
  perpD (starRingEnd ℂ) d W₂ = W₁ → twCent (thetaR (starRingEnd ℂ) n) d ≤ flagStab W₁ W₂ ∧
  ∀ q ∈ flagStab W₁ W₂, perpD (starRingEnd ℂ) (twConj (thetaR (starRingEnd ℂ) n) q d) W₁ = W₂ ∧
    perpD (starRingEnd ℂ) (twConj (thetaR (starRingEnd ℂ) n) q d) W₂ = W₁

def QuotVanish : Prop := ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
  (μ : Measure (GL (Fin n) ℂ)) [μ.IsHaarMeasure] (d : GL (Fin n) ℂ) (μT : Measure (twCent (thetaR (starRingEnd ℂ) n) d))
  [μT.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) [MeasurableSpace (nilrad W₁ W₂)]
  [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure] (F : GL (Fin n) ℂ → ℂ),
  (d * thetaR (starRingEnd ℂ) n d).val.charpoly.Separable → perpD (starRingEnd ℂ) d W₁ = W₂ →
  perpD (starRingEnd ℂ) d W₂ = W₁ → Measurable F → (∀ t ∈ twCent (thetaR (starRingEnd ℂ) n) d, ∀ x, F (t * x) = F x) →
  (∀ x k, thetaR (starRingEnd ℂ) n k = k → F (x * k) = F x) →
  (∀ q ∈ flagStab W₁ W₂, ∫ X, F (uOf hW X * q) ∂ν = 0) → quotIntegral μ (twCent (thetaR (starRingEnd ℂ) n) d) μT F = 0

def KerFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : GA E n → ℂ), IsTest φ →
  ∀ C : Set (GA E n), IsCompact C → Set.Finite {d : GL (Fin n) E | ∃ x ∈ C, φ (twConj (thetaA E n) x (ratGL E n d)) ≠ 0}

def AbsUnfold : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (Γ Γ₀ : Subgroup G)
  (Fd : Set G) (F : G → ℂ), Countable Γ → DiscreteTopology Γ → Γ₀ ≤ Γ → IsFundamentalDomain Γ Fd μ → Measurable F →
  (∀ g ∈ Γ₀, ∀ x, F (g * x) = F x) → Integrable (fun x => ∑' q : Γ ⧸ Γ₀.subgroupOf Γ, ‖F ((q.out : G)⁻¹ * x)‖) (μ.restrict Fd) →
  ∫ x in Fd, ∑' q : Γ ⧸ Γ₀.subgroupOf Γ, F ((q.out : G)⁻¹ * x) ∂μ = quotIntegral μ Γ₀ Measure.count F

end PositivityTheory.Rg.BcB.D4

end
