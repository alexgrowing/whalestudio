import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem mulVec_le {p : ℕ} [Fact p.Prime] {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ_[p]} (hT : ∀ i k, ‖T i k‖ ≤ 1)
    {a : Fin n → ℂ_[p]} (ha : ∀ i, ‖a i‖ ≤ 1) (i : Fin n) : ‖(T *ᵥ a) i‖ ≤ 1 := by
  change ‖∑ k, T i k * a k‖ ≤ 1
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hT i k) (norm_nonneg _) (ha k)

private theorem mulVec_le_iff {p : ℕ} [Fact p.Prime] {n : ℕ} {R : Type} [CommRing R] (χ : R →+* ℂ_[p])
    (hχ : ∀ r, ‖χ r‖ ≤ 1) {T : Matrix (Fin n) (Fin n) R} (hT : IsUnit T.det) (a : Fin n → ℂ_[p]) :
    (∀ i, ‖(T.map χ *ᵥ a) i‖ ≤ 1) ↔ ∀ i, ‖a i‖ ≤ 1 := by
  refine ⟨fun h i => ?_, fun h => mulVec_le (fun _ _ => hχ _) h⟩
  have := mulVec_le (T := T⁻¹.map χ) (fun _ _ => hχ _) h i
  rwa [mulVec_mulVec, ← Matrix.map_mul, nonsing_inv_mul _ hT, Matrix.map_one _ (map_zero _) (map_one _),
    one_mulVec] at this

theorem UpperTheory.frame_generic_valuation :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : Var F) (ρ : Y.X ⟶ gen Z) (_ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) (g₀ : GenFrame e ρ) (τ : E →+* ℂ) (X : Scheme.{0}) (j : Y.X ⟶ X) (M : X.Modules) (hM : IsVB M (Dw.mult τ)) (dual : Bool) (A : Chart M (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn), IsLie g₀ τ j dual A → (∀ z : X, ∃ ch : Chart M (Dw.mult τ), z ∈ ch.U ∧ LatOn g₀ τ j ch.U (lieMat dual (A ch))) → IsLat g₀ τ j dual A := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y ρ _ g₀ τ X j M _ dual A hA h ch v _ ε y yt hyt hin φ f hf a w hw
  obtain ⟨ch₀, hz, h₀⟩ := h (yt (IsLocalRing.closedPoint ε.O))
  have hin₀ : ⊤ ≤ yt ⁻¹ᵁ ch₀.U := (Scheme.preimage_eq_top_of_closedPoint_mem yt hz).ge
  have up : ∀ {U : X.Opens}, ⊤ ≤ yt ⁻¹ᵁ U → j (below y.1) ∈ U := fun {U} hU => by
    have : (spMap ε.O.subtype ≫ yt) (IsLocalRing.closedPoint _) ∈ U := hU (Set.mem_univ _)
    rwa [hyt] at this
  obtain ⟨f₀, hco, hf₀⟩ := hf.change hA.1 (up hin) (up hin₀)
  obtain ⟨g, hg⟩ := f.exists_isMap (valP ε y) rfl rfl
  obtain ⟨g', hg'⟩ := f₀.exists_isMap (valP ε y) rfl rfl
  have hsp : spMap (valP ε y) ≫ stalkPt Y (below y.1) ≫ j = spMap ((ioOf (resP v) ε).comp ε.O.subtype) ≫ yt := by
    have h₁ : spMap (valP ε y) = spMap (ioOf (resP v) ε) ≫ spMap (Scheme.stalkClosedPointTo y.1).hom := by
      rw [← Spec.map_comp]; rfl
    have h₂ : spMap ((ioOf (resP v) ε).comp ε.O.subtype) = spMap (ioOf (resP v) ε) ≫ spMap ε.O.subtype := by
      rw [← Spec.map_comp]; rfl
    rw [h₁, h₂, Category.assoc, Category.assoc, hyt, ← Category.assoc _ _ j]
    exact congrArg (_ ≫ · ≫ j) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y.1)
  have hu := isUnit_det_trAt ch ch₀ hin hin₀
  have hT : g.co g' τ = (lieMat dual (trAt yt ch ch₀)).map ((ioOf (resP v) ε).comp ε.O.subtype) := by
    rw [hg.co τ hg' rfl, hco, ← lieMat_map _ _ (isUnit_det_trAt _ _ (stalk_le j (up hin)) (stalk_le j (up hin₀))),
      ← trAt_spMap _ _ _ (stalk_le j (up hin)) (stalk_le j (up hin₀)), hsp, trAt_spMap _ _ _ hin hin₀,
      lieMat_map _ _ hu]
  rw [← funext (hg τ)] at hw
  have hw' := GlobalTheory.LineNorm.Chart.comb_comb (g'.tan τ) (g'.co_spec g τ) hw
  have ha : a = g.co g' τ *ᵥ ∑ k, a k • fun b => g'.co g τ b k := by
    have : (∑ k, a k • fun b => g'.co g τ b k) = g'.co g τ *ᵥ a := by
      funext b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, mul_comm]
    rw [this, mulVec_mulVec, EigFrame.co_mul, EigFrame.co_self, one_mulVec]
  rw [funext (hg' τ)] at hw'
  rw [h₀ v ε y yt hyt hin₀ φ f₀ hf₀ _ w hw',
    ← mulVec_le_iff ((ioOf (resP v) ε).comp ε.O.subtype)
      (fun r => (ioOf_le_one_iff _ (residueCharacteristic_mem v) ε _).2 r.2) (isUnit_det_lieMat dual hu), ← hT, ← ha]
