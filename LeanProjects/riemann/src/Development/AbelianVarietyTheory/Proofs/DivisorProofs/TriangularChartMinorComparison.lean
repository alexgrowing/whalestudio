import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorsTriangularChangeInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularMatricesValueMultiplicative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionEquivRegularUnitValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CramerTriBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstLat.CramerFrame

theorem regAt_minorAt {Z : Scheme.{0}} [IsIntegral Z] {x : Z} {n g : ℕ} (P : Matrix (Fin n) (Fin g) Z.functionField)
    (hP : ∀ a b, RegAt x (P a b)) (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin n) : RegAt x (minorAt P k hk τ) := by
  obtain ⟨A, rfl⟩ := CramerValues.exists_germ_matrix P hP
  rw [CramerValues.minorAt_map_ringHom]
  exact ⟨_, rfl⟩

theorem det_rowSel_mul_map {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {g : ℕ} (τ : Fin g → Fin (g + g))
    (M : Matrix (Fin (g + g)) (Fin g) R) :
    Matrix.det ((rowSel τ : Matrix (Fin g) (Fin (g + g)) S) * M.map ψ) =
      ψ (Matrix.det ((rowSel τ : Matrix (Fin g) (Fin (g + g)) R) * M)) := by
  rw [RingHom.map_det]
  congr 1
  ext l k
  simp [Matrix.mul_apply, rowSel]

theorem frameUm_det_regAt : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (W : Y.X.Opens) (p : ℕ), p.Prime → genericPoint Y.X ∈ W → ∀ {g : ℕ} (U' : V.X.Opens) (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (σ : ∀ k : ℕ, Fin k → Fin (g + g)), (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) → ChartReg V U' H T → (∀ (k : ℕ) (hk : k ≤ g), minorAt H k hk (σ k) ≠ 0) → (∀ z : V.G, V.j z ∈ U' → ∀ (k : ℕ) (hk : k ≤ g), UnitAt z (minorAt (H * ((T (V.π z)).map V.φ)⁻¹) k hk (σ k))) → (AtTest V W p fun _ e y z yt => ⊤ ≤ yt ⁻¹ᵁ U' → ∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)), e.w (minorAt (valMat V H (T (below y.1)) z) k hk τ) ≤ e.w (minorAt (valMat V H (T (below y.1)) z) k hk (σ k))) → (rowSel (σ g) * frameUm V H σ).det = 1 ∧ ∀ x ∈ U', ¬ IsUnit (p : V.X.presheaf.stalk x) → ∀ r k, RegAt x (frameUm V H σ r k) := by
  intro F _ _ Y V W p hp hW g U' H d T σ hT hreg hne hunit hmax
  have htri : ∀ y, cramerCol H σ = cramerCol (H * ((T y).map V.φ)⁻¹) σ := fun y =>
    (triChange H ((T y).map V.φ) (fun i j hij => by
      rw [Matrix.map_apply, (hT y).1 hij, map_zero]) (fun i => by
      rw [Matrix.map_apply, (hT y).2 i]
      exact (map_ne_zero _).2 (d y i).ne_zero) σ).2.1
  have hfn : ∀ r k, fnEquiv V (frameUm V H σ r k) = cramerCol H σ r k := fun r k =>
    (fnEquiv V).apply_symm_apply _
  have hgen : ∀ r k, ∀ z : V.G, V.j z ∈ U' → RegAt (V.j z) (frameUm V H σ r k) := by
    intro r k z hz
    rw [← ((fnEquiv_transport V).1 z _).1, hfn, htri (V.π z)]
    simp only [cramerCol, Matrix.of_apply]
    rw [div_eq_mul_inv]
    exact (regAt_minorAt _ (hreg z hz) _ _ _).mul (hunit z hz _ _).inv.regAt
  refine ⟨?_, fun x hx hpx r k => ?_⟩
  · obtain ⟨B, -, -, -, hdet⟩ := cramerCol_tri_det H σ hne
    have h := det_rowSel_mul_map ((fnEquiv V).symm : V.G.functionField →+* V.X.functionField) (σ g) (cramerCol H σ)
    exact h.trans ((congrArg _ hdet).trans (map_one _))
  · refine GlobalTheory.Mean4O.Cover.RegOverP.regAt_of_values_over F Y V p hp W hW U' _ (hgen r k) ?_ x hx hpx
    intro v hv e y hy z yt hz hyt hU
    have hj : V.j (below z) ∈ U' := by
      change (z ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ U'
      rw [← hyt]
      exact hU (x := spMap e.O.subtype (IsLocalRing.closedPoint (AlgebraicClosure F))) trivial
    have hb : below y.1 = V.π (below z) := by
      rw [← hz]
      rfl
    have hm := hmax v hv e y hy z yt hz hyt hU ((k : ℕ) + 1) k.2 (Fin.snoc (σ k) r)
    rw [hb] at hm
    obtain ⟨-, hv2, hv3⟩ := CramerValues.values_regular z
    have hu := hunit (below z) hj ((k : ℕ) + 1) k.2
    have hne' := GlobalTheory.TrueGeo.SmallSec.valAt_ne_zero hu
    rw [← (fnEquiv_transport V).2 z _ (hgen r k _ hj), hfn, htri (V.π (below z))]
    simp only [cramerCol, Matrix.of_apply]
    rw [(hv3 _ _ (regAt_minorAt _ (hreg _ hj) _ _ _) hu).2, map_div₀, div_le_one (e.w.pos hne'),
      (hv2 _ (hreg _ hj) _ _ _).2, (hv2 _ (hreg _ hj) _ _ _).2]
    exact hm

end GlobalTheory.ConstLat.CramerFrame

end
