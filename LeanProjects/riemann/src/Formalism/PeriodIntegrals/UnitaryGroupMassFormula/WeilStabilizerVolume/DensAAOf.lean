import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensHSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensFF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensTop

noncomputable section

namespace PI.VolStabW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

def ResAA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → SWc1W F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → 2 * a < M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ ψ, IsCharAF F ψ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    ∀ᶠ v in cofinite,
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∃ (L : AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E))
      (Λ : ℕ → AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E))
      (H : ℕ → AddSubgroup (HermR (Fv F v) σ a)),
      (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) = latV b v ∧
      IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∧
      IsCompact (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∧ Λ 0 ≤ L ∧
      (∀ n, IsOpen (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
      (∀ n, IsCompact (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧ Antitone Λ ∧
      (∀ n, IsOpen (H n : Set (HermR (Fv F v) σ a))) ∧
      (∀ n, IsCompact (H n : Set (HermR (Fv F v) σ a))) ∧
      (∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ n, (H n : Set (HermR (Fv F v) σ a)) ⊆ N') ∧
      (∀ y ∈ L, gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 y - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ H 0 →
        ∃ D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a,
          (∀ n, (Λ n).map D = H n) ∧ ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n,
            gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z + W) - gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 (y + Z) - D W ∈
              H (n + 1)) ∧
      ∃ (k K : Type) (_ : Field k) (_ : Finite k) (_ : CommRing K) (_ : Algebra k K)
        (σ' : K ≃ₐ[k] K) (J' : Matrix (Fin M) (Fin M) K) (T' : Matrix (Fin a) (Fin a) K),
        IsQuadInv k K σ' ∧ (2 : k) ≠ 0 ∧ (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧
        (∀ i j, σ' (T' j i) = T' i j) ∧ IsUnit T'.det ∧ (Nat.card k : ℝ) = qV v ∧
        ((μv ((L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ∩
            gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1 ⁻¹' {z | z - hermOf (Fv F v) σ (gramE σ J X0) hT ∈ H 0})) /
            νv (H 0)).toReal =
          (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ℝ) /
            (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2)

theorem densAA_of (hFL : FibLat) (hFF : FFCount) (hR : ResAA) : DensAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  obtain ⟨C, hC⟩ := hFF M
  refine ⟨C, ?_⟩
  filter_upwards [hR F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet ψ hψ d b] with v hv
  intro μv hμv νv hνv fibV hfib
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have := hμv.1
  have := hνv.1
  obtain ⟨L, Λ, H, hL, hLo, hLc, hΛL, hΛo, hΛc, hΛa, hHo, hHc, hHb, hyp, k, K, _, _, _, _, σ', J',
    T', hQ, h2, hJ', hJu, hT', hTu, hq, hcnt⟩ := hv μv hμv νv hνv
  have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hN := isOpen_unitHerm (Fv F v) (isOpen_units_Fv F v) σ a
  have e := hFL _ _ _ μv νv hμv.1 hνv.1 (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective
    (gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1) (continuous_gramH (Fv F v) σ (sigma_invol σ hCM.2.2.2) J hJ.1) (fun _ => rfl) _ _ fibV hfib
    (hermOf (Fv F v) σ (gramE σ J X0) hT) Filter.univ_mem _
    (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet))
    (fun X hX => linIndep_of_isUnit_det (Fv F v) σ J X hX) L hLo hLc Λ H hΛL hΛo hΛc hΛa hHo hHc
    hHb hyp
  rw [hcnt, hL] at e
  rw [e]
  have hb := hC k K σ' hQ h2 J' hJ' hJu a (by omega) T' hT' hTu
  rw [← hq]
  have : ((((Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ℝ) /
      (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) : ℝ) : ℂ) - 1) =
      (((Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ℝ) /
      (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact hb

end PI.VolStabW
