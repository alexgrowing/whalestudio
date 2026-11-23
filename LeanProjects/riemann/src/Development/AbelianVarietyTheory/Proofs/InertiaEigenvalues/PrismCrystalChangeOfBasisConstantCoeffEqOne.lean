import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalBasisTransportFreeOverPrismStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.CrysDiag.eps_constantCoeff_eq_one : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (κ : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (κ₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, κ₀ τ (δ.f y) = PowerSeries.constantCoeff (κ τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), κ τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ τ, (Matrix.of fun i j => ∑ q, c i j q • κ τ (y i j q)).map PowerSeries.constantCoeff = 1 := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  intro E jA hR hM oE hoE b hb PP S₀ p₀ p₁ δ κ κ₀ hδ hκ₀ hκ Q _ c y hy τ
  obtain ⟨h1, h2⟩ := GlobalTheory.T.crystal_basis_transport_free_over_prism l a e O K t ϖ ι P T I E jA hR hM oE hoE b hb
  have key : ∀ j, ∑ i, ∑ q, δ.f (y i j q) • (oE (c i j q)).u S₀ (E.tr (δ.comp p₀) (b i)) =
      ∑ i, ∑ _q : Unit, (if i = j then (1 : S₀.A) else 0) • (oE 1).u S₀ (E.tr (δ.comp p₀) (b i)) := by
    intro j
    have hfix : ∀ i, (oE 1).u S₀ (E.tr (δ.comp p₀) (b i)) = E.tr (δ.comp p₀) (b i) := fun i => by
      rw [(oE 1).u_tr, h1]
    simp only [hfix, ite_smul, one_smul, zero_smul, Finset.sum_const, Finset.card_univ, Fintype.card_unit]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    conv_rhs => rw [hδ, E.tr_comp, hy j]
    simp only [E.tr_comp, map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => ?_
    rw [(oE (c i j q)).u_tr]
    exact ((E.tr δ).map_smulₛₗ _ _).symm
  have hC : ∀ w : Wq l a, (toAc t K (PowerSeries.C w) τ : K⟦X⟧) = PowerSeries.C (algebraMap O K (emb t τ w)) := by
    intro w
    ext n
    rw [coeff_toAc, PowerSeries.coeff_C, PowerSeries.coeff_C]
    split_ifs <;> simp
  have hψ : ∀ z : ℤ_[l], κ₀ τ ((δ.comp p₀).f (algebraMap ℤ_[l] (Wq l a)⟦X⟧ z)) =
      algebraMap O K⟦X⟧ (algebraMap ℤ_[l] O z) := by
    intro z
    change κ₀ τ (δ.f (p₀.f _)) = _
    rw [hκ₀, hκ, PowerSeries.algebraMap_apply, frobS_C, PowerSeries.constantCoeff_C, hC,
      AlgEquiv.commutes, AlgHom.commutes, PowerSeries.algebraMap_apply]
  refine Matrix.ext fun i j => ?_
  have hij := h2 S₀ (δ.comp p₀) Q Unit (fun i q => c i j q) (fun i q => δ.f (y i j q)) (fun _ _ => 1)
    (fun i _ => if i = j then (1 : S₀.A) else 0) (by simpa only [one_smul] using key j) K⟦X⟧ (κ₀ τ) hψ i
  simp only [hκ₀, Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul, apply_ite (κ₀ τ),
    map_one, map_zero] at hij
  rw [Matrix.map_apply, Matrix.of_apply, map_sum, Matrix.one_apply, ← hij]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, PowerSeries.algebraMap_apply,
    PowerSeries.constantCoeff_C, PowerSeries.algebraMap_apply]
