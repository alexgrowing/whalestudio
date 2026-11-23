import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt
open ReciprocityTheory.ChartRestriction.G.PullbackSections

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieFilt

attribute [local instance] Over.cartesianMonoidalCategory

theorem bijective_sum_of_eigBases {E F K M : Type} [Field E] [NumberField E] [Field F] [CharZero F] [CommRing K]
    [Algebra F K] [AddCommGroup M] [Module K M] (j : F →+* ℂ) (χ : (E →+* ℂ) → (𝓞 E →+* F))
    (hχ : ∀ τ a, j (χ τ a) = τ (a : E)) (ρ : 𝓞 E →+* Module.End K M) {r : (E →+* ℂ) → ℕ}
    (U : ∀ τ, Fin (r τ) → M) (hU : ∀ τ i, IsEigV ρ (χ τ) (U τ i))
    (hb : ∀ τ w, IsEigV ρ (χ τ) w → ∃! a : Fin (r τ) → K, w = ∑ i, a i • U τ i) :
    Function.Bijective fun a : (Σ τ, Fin (r τ)) → K => ∑ s, a s • U s.1 s.2 := by
  obtain ⟨α, hα, ⟨f, hf, hfs⟩, hN⟩ := exists_sepElt j χ hχ
  have he : ∀ τ (a : Fin (r τ) → K), IsEigV ρ (χ τ) (∑ i, a i • U τ i) := fun τ a b => by
    simp only [map_sum, map_smul, hU τ _ b, Finset.smul_sum]
    exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _
  refine ⟨fun a a' h => ?_, fun w => ?_⟩
  · simp only [Fintype.sum_sigma] at h
    funext ⟨τ, i⟩
    have h1 := proj_sum_eig ρ χ α hα _ (fun τ => he τ fun i => a ⟨τ, i⟩) τ
    have h2 := proj_sum_eig ρ χ α hα _ (fun τ => he τ fun i => a' ⟨τ, i⟩) τ
    rw [h, h2] at h1
    exact congrFun ((hb τ _ (he τ fun i => a' ⟨τ, i⟩)).unique h1 rfl) i
  · choose a ha _ using fun τ => hb τ _ (eig_of_alpha ρ χ α hN τ (proj_eig_alpha ρ χ α hα f hf hfs τ w))
    refine ⟨fun s => a s.1 s.2, ?_⟩
    simp only [Fintype.sum_sigma, ← ha]
    rw [← LinearMap.sum_apply, sum_proj ρ χ α hα]
    rfl

open scoped CategoryTheory.MonObj in

theorem bijective_mulVec_of_eigBases : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {K : Type} [CommRing K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X)
    {g : ℕ} (ch : VB.Chart (omega Z.t.G) g), ⊤ ≤ x ⁻¹ᵁ ch.U →
    ∀ {r : (E →+* ℂ) → ℕ} (u : ∀ τ, Fin (r τ) → (Sp (DualNumber K) ⟶ Z.t.G.left)), (∀ τ, IsEigBasis Z φ x τ (u τ)) →
    ∀ P : Matrix (Fin g) (Σ τ, Fin (r τ)) K, IsTanMat Z x ch (fun s : Σ τ, Fin (r τ) => u s.1 s.2) P →
    Function.Bijective P.mulVec := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z K _ φ x g ch hV r u hu P hP
  letI : Algebra c.F K := φ.toAlgebra
  let U : ∀ τ, Fin (r τ) → TanM x Z.t.G := fun τ i => LieMet.tanOf ((hu τ).1 i).1
  have hU : ∀ τ i a, actR Z.t.act a (U τ i) = φ (embK c τ a) • U τ i := fun τ i a =>
    LieMet.tan_ext (((hu τ).1 i).2 a)
  have hW : ∀ τ (w : TanM x Z.t.G), (∀ a, actR Z.t.act a w = φ (embK c τ a) • w) →
      ∃! a : Fin (r τ) → K, w = ∑ i, a i • U τ i := fun τ w hw =>
    (existsUnique_congr fun a => LieMet.isComb_iff (U τ) a w).1
      ((hu τ).2 _ ⟨LieMet.isTan_tv w, fun a => congrArg (fun v => (tv v).left) (hw a)⟩)
  have hb := bijective_sum_of_eigBases (K := K) (M := TanM x Z.t.G) c.F.val.toRingHom (embK c) (embK_coe c)
    (actR Z.t.act) U hU hW
  obtain ⟨Φ, hΦ⟩ := LocM.TanPair.exists_tanM_equiv E H Z.X Z.t K x ch.U hV g ch.e ch.isFrame
  have e : P.mulVec = Φ ∘ fun a : (Σ τ, Fin (r τ)) → K => ∑ s, a s • U s.1 s.2 := by
    funext a b
    simp only [Function.comp_apply, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun s _ => (mul_comm _ _).trans (congrArg _ ((hP s _ hV b).trans (hΦ (U s.1 s.2) b).symm))
  rw [e]
  exact Φ.bijective.comp hb

end GlobalTheory.LieFilt

end
