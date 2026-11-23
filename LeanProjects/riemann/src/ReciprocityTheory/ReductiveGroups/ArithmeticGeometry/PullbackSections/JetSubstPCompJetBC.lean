import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')

theorem jetBC_mk {κ : Type} {m : ℕ} (P : MvPolynomial κ S) :
    jetBC ψ κ m (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ (MvPolynomial.map ψ P) := rfl

theorem jetAug_comp_jetBC (κ : Type) (m : ℕ) :
    (jetAug : Jet S' κ m →ₐ[S'] S').toRingHom.comp (jetBC ψ κ m) = ψ.comp (jetAug : Jet S κ m →ₐ[S] S).toRingHom := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)) <;>
    simp [jetBC, jetAug, liftJet]

theorem jetTrunc_comp_jetBC (κ : Type) (m : ℕ) :
    (jetTrunc : Jet S' κ (m + 1) →ₐ[S'] Jet S' κ m).toRingHom.comp (jetBC ψ κ (m + 1)) =
      (jetBC ψ κ m).comp (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m).toRingHom := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)) <;>
    simp [jetBC, jetTrunc]

theorem jetTan_comp_jetBC {κ : Type} [DecidableEq κ] (ℓ : κ) (m : ℕ) :
    (jetTan ℓ : Jet S' κ (m + 1) →ₐ[S'] DualNumber S').toRingHom.comp (jetBC ψ κ (m + 1)) =
      (dualMap ψ).comp (jetTan ℓ : Jet S κ (m + 1) →ₐ[S] DualNumber S).toRingHom := by
  have e : ∀ (T : Type) [CommRing T] (P : MvPolynomial κ T),
      (jetTan ℓ : Jet T κ (m + 1) →ₐ[T] DualNumber T) (Ideal.Quotient.mk (orig T κ ^ (m + 1 + 1)) P) =
        aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber T) else 0) P := fun _ _ _ => rfl
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, jetBC_mk, e, aeval_C,
      MvPolynomial.map_C]
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, jetBC_mk, e, aeval_X,
      MvPolynomial.map_X]
    split_ifs <;> ext <;> simp [dualMap]

theorem jetMap_comp_jetBC {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (hφ : ∀ i, φ i ∈ orig S κ')
    (hφ' : ∀ i, MvPolynomial.map ψ (φ i) ∈ orig S' κ') :
    (jetMap (m := m) (fun i => MvPolynomial.map ψ (φ i)) hφ').toRingHom.comp (jetBC ψ κ m) =
      (jetBC ψ κ' m).comp (jetMap (m := m) φ hφ).toRingHom := by
  have e : ∀ (T : Type) [CommRing T] (χ : κ → MvPolynomial κ' T) (hχ : ∀ i, χ i ∈ orig T κ')
      (P : MvPolynomial κ T), (jetMap (m := m) χ hχ) (Ideal.Quotient.mk (orig T κ ^ (m + 1)) P) =
        Ideal.Quotient.mk (orig T κ' ^ (m + 1)) (aeval χ P) := fun _ _ _ _ _ => rfl
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)) <;>
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, jetBC_mk, e, aeval_C, aeval_X,
      MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.algebraMap_eq]

theorem map_sub_const {κ : Type} (P : MvPolynomial κ S) :
    MvPolynomial.map ψ (P - C (MvPolynomial.constantCoeff P)) =
      MvPolynomial.map ψ P - C (MvPolynomial.constantCoeff (MvPolynomial.map ψ P)) := by
  simp [MvPolynomial.constantCoeff_map]

theorem jetSubstP_comp_jetBC {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) :
    (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) : Jet S' κ m →ₐ[S'] Jet S' κ' m).toRingHom.comp (jetBC ψ κ m) =
      (jetBC ψ κ' m).comp (jetSubstP m φ : Jet S κ m →ₐ[S] Jet S κ' m).toRingHom := by
  have e : ∀ (T : Type) [CommRing T] (χ : κ → MvPolynomial κ' T) (hχ : ∀ i, χ i ∈ orig T κ')
      (P : MvPolynomial κ T), (jetMap (m := m) χ hχ) (Ideal.Quotient.mk (orig T κ ^ (m + 1)) P) =
        Ideal.Quotient.mk (orig T κ' ^ (m + 1)) (aeval χ P) := fun _ _ _ _ _ => rfl
  unfold jetSubstP
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)) <;>
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, jetBC_mk, e, aeval_C, aeval_X,
      MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.algebraMap_eq, map_sub_const]

theorem jetBC_psJet {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S) :
    jetBC ψ κ m (psJet m f) = psJet m (MvPowerSeries.map ψ f) := by
  simp [jetBC, psJet, psTrunc, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
