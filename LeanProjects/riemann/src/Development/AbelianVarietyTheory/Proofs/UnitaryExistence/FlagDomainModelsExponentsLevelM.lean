import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEqNsmulOfDvdPairing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCuspPseudoBasisAdaptedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentMatchingIndependentOfCuspBasisStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemPrincipalCongruenceInterCuspCentreIffStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemDualCuspCharacterLatticeIffAdaptedBasisStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspPairingIntIffHermitianExponentIntegralStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ExpoModels

theorem exists_equiv_of_stab {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (h : IsUStab G Λ γ) :
    ∃ e : Λ ≃ₗ[𝓞 E] Λ, ∀ v : Λ, (e v : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) := by
  have hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨{ toFun := fun v => ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E), (h.2 _).1 v.2⟩
            invFun := fun v => ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E),
              (h.2 _).2 (by rw [hri]; exact v.2)⟩
            map_add' := fun x y => Subtype.ext (by simp [Matrix.mulVec_add])
            map_smul' := fun a x => Subtype.ext (by simp [Matrix.mulVec_smul])
            left_inv := fun v => Subtype.ext (hli _)
            right_inv := fun v => Subtype.ext (hri _) }, fun v => rfl⟩

theorem mem_gamma_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    {F : FamilyUnif Xo σ' ty} {r : ℕ} {M : ModelsOf F r} (hM : ModelBase M) (hA : l.A = 1) (k : Fin F.n)
    (γ : GL (Fin r) E) :
    γ ∈ (M.X k).Γ ↔ IsUStab (M.X k).Gm (M.X k).Λ γ ∧ ∀ v ∈ (M.X k).Λ, ∃ w ∈ (M.X k).Λ,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + l.M • w := by
  rw [hM.gam k γ]
  refine and_congr_right fun hs => ?_
  obtain ⟨e, he⟩ := exists_equiv_of_stab _ _ γ hs
  constructor
  · rintro ⟨h1, -⟩ v hv
    let gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La := (M.φ k).trans (e.trans (M.φ k).symm)
    have hg : ∀ a, (M.φ k (gam a) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := by
      intro a
      simp only [gam, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, he]
    have key := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (F.Di k) l gam
      (fun a b => by
        have h2 := hM.ef k (gam a) (gam b)
        rw [hg, hg, hs.1, ← hM.ef k a b] at h2
        exact_mod_cast h2)
      (fun a ha => by
        obtain ⟨b, hb⟩ := h1 a ha
        refine ⟨b, (M.φ k).injective (Subtype.ext ?_)⟩
        rw [hg, hb, map_add, map_nsmul]
        rfl)
    obtain ⟨b, hb⟩ := key ((M.φ k).symm ⟨v, hv⟩)
    refine ⟨M.φ k b, (M.φ k b).2, ?_⟩
    have h3 := hg ((M.φ k).symm ⟨v, hv⟩)
    rw [hb, map_add, map_nsmul, LinearEquiv.apply_symm_apply] at h3
    exact h3.symm
  · intro h
    refine ⟨fun a _ => ?_, fun a => ?_⟩
    · obtain ⟨w, hw, h2⟩ := h _ (M.φ k a).2
      refine ⟨(M.φ k).symm ⟨w, hw⟩, ?_⟩
      rw [LinearEquiv.apply_symm_apply]
      exact h2
    · refine ⟨(M.φ k).symm (e (M.φ k a) - M.φ k a), ?_⟩
      rw [LinearEquiv.apply_symm_apply, hA, one_smul, ← he]
      simp

theorem expoMatch_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (M : ModelsOf F r) (ρ : ℕ), ModelBase M → l.A = 1 → FJ.ExpoMatch M.X 1 ρ l.M := by
  intro E _ _ _ H Dw l Xo σ' g ty F r M ρ hM hA cu₀
  obtain ⟨k, cu₀⟩ := cu₀
  obtain ⟨cu, P, cc', hP, hPe, hne, hΛ⟩ := GlobalTheory.T.exists_cusp_pseudoBasis_adapted_lattice E r ρ (M.X k) cu₀
  refine GlobalTheory.T.exponentMatching_independent_of_cuspBasis E r ρ l.M (M.X k) cu₀ cu P hP hPe ?_
  intro χ hχ
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hr : LinearMap.range φ = (M.X k).Λ := by
    simp only [φ, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have hz := GlobalTheory.T.mem_principalCongruence_inter_cuspCentre_iff E H r ρ (M.X k) l.M (F.Di k) φ cu cc' hr
    ⟨Subtype.val_injective.comp (M.φ k).injective,
      by rw [← LinearMap.coe_range, hr]; exact (M.X k).Λ_span,
      (M.X k).Gm_herm, (M.X k).Gm_det, hM.ef k⟩ (mem_gamma_iff hM hA k) hΛ
  have hd := GlobalTheory.T.mem_dual_cuspCharacterLattice_iff_adapted_basis E r ρ (M.X k) cu cc' hΛ
  have ht := GlobalTheory.T.cuspPairing_int_iff_hermitianExponent_integral E H r ρ (M.X k) l.M cc' χ (by have := l.three_le; omega) hne hχ
  constructor
  · intro h u hu m hm
    exact ht.1 (fun β h1 h2 => h β ((hz β).2 ⟨h1, h2⟩)) u m ((hd u).1 hu) ((hd m).1 hm)
  · intro h β hβ
    exact ht.2 (fun u m hu hm => h u ((hd u).2 hu) m ((hd m).2 hm)) β ((hz β).1 hβ).1 ((hz β).1 hβ).2

end GlobalTheory.ExpoModels
