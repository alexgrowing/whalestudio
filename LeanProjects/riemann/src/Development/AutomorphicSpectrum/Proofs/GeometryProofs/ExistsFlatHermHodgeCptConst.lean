import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalLatticeHeightFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionsTwoComponents
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceOfNotMemGenFibre

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_flatHerm_hodgeCpt_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (τ : CMType H) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (A : HermLine J) (c₀ : Ω) (r : HeightOneSpectrum (𝓞 F') →₀ ℚ) (cinf : (F' →+* ℂ) → ℝ), Fl.RootLines xdeg e → A.a = ∑ i, xdeg (τ, i) → Birational y → IsConjInvariantH A → c₀ ≠ 0 → (∀ p ∈ genFibre ℤ 𝔐.ξ, (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsGenAt p (c₀ * ∏ i, e (τ, i))) → (∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt 𝔐.ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt 𝔐.ξ p) → OrderAt (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (c₀ * ∏ i, e (τ, i)) (ψ π) m k p) → (∀ σ, 0 < cinf σ) → (∀ (σ : F' →+* ℂ) z (g h : MRing J) (dg dh : K → ℕ), PtOver y ψ σ z → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖) → OverInt y ψ ∧ ∃ Sf : FlatHerm y ψ A, Sf.ht = ((r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ σ : F' →+* ℂ, Real.log (cinf σ)) / (Module.finrank ℚ F' : ℝ) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl xdeg e τ F' _ _ ψ A c₀ r cinf hR hA hB hC hc₀ hgen hZ hcinf hnorm
  have hN : NormalCpt 𝔐.ξ := XR.normalCpt_of_isCptGen 𝔐.tie.gen 𝔐.normal
  have hO : OverInt y ψ := overInt_of_normalCpt 𝔐.tie hN ψ
  have hD := GlobalTheory.T.hodge_cpt_flag_degree E H D l Xo c O β Y S Ω K J y 𝔐 Fl xdeg e τ hR
  rw [← hA] at hD
  refine ⟨hO, GlobalTheory.T.birational_lattice_height_formula K J Ω F' y ψ 𝔐.X 𝔐.ξ Ω _ (∏ i, e (τ, i)) c₀ A r cinf hO hB hC 𝔐.tie hN hD hc₀
    (fun p => ?_) hcinf hnorm⟩
  by_cases hp : p ∈ genFibre ℤ 𝔐.ξ
  · exact Or.inl ⟨cst_mem_regAt_of_genFibre hN ψ hp, orderAt_one_zero.2 (hgen p hp)⟩
  · obtain ⟨v, hv⟩ := exists_place_of_notMem_genFibre hN ψ hp
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F'
    obtain ⟨m, n, hm, hn, h⟩ := hZ v π hπ
    exact Or.inr ⟨v, π, m, n, hv, hπ, hm, hn, h p hv⟩

end GlobalTheory.CompanionTheory.Ar.Flat
