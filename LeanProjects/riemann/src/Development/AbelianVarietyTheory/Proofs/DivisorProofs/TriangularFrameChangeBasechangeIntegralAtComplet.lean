import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIntegralEigenbasisOfFrameAtLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUnitIntegralGeneratorPrincipalLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieBasisLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTriplePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SabMapCancelAndCompOver
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnimodularMulLowerTriangularOfDetNStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

namespace GlobalTheory.PtDegInt

open GlobalTheory.LamT

private theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

private theorem sab_comp' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} (n : SABMap t₂ t₁ g)
    (m₁ : SABMap t₁ t f₁) (f₂ : S₂ ⟶ S) (h : f₂ = g ≫ f₁) : ∃ m : SABMap t₂ t f₂, m.φ = n.φ ≫ m₁.φ := by
  subst h
  exact sabComp pullCubComp E H _ _ _ t t₁ t₂ f₁ g m₁ n

private theorem sab_cancel' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S} (m₁ : SABMap t₁ t f₁)
    (m₂ : SABMap t₂ t f₂) (g : S₂ ⟶ S₁) (h : f₂ = g ≫ f₁) : ∃ n : SABMap t₂ t₁ g, n.φ ≫ m₁.φ = m₂.φ :=
  (GlobalTheory.sabMap_cancel_and_comp_over E H S S₁ S₂ t t₁ t₂ f₁ f₂ g m₁ m₂ h).1

private theorem integral_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : CDVR) (io : c.F →+* T.Fr)
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} {x : Sp T.Fr ⟶ Xo.X} :
    letI := io.toAlgebra
    ∀ (y : FrPt Xo c T.Fr) (_ : y.x = x) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
    LieInt T io m1 m2 y.u → SecInt T m1 m2 y.s → Integral T io y := by
  intro y hx
  subst hx
  exact integral_of T io y

theorem intPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∃ (ρV : 𝓞 K →+* T.V) (_ : (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K)) (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))) (_ : m1'.φ = n'.φ ≫ m1.φ) (_ : m2'.φ ≫ n.φ = n'.φ ≫ m2.φ) (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (td : Ix Dw → T.Frˣ) (y' : FrPt Xo c T.Fr), (∀ σ i j, i < j → C σ i j = 0) ∧ (∀ σ i, C σ i i = (td (some ⟨σ, i⟩) : T.Fr)) ∧ FrChg C (td none : T.Fr) yT y' ∧ GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u ∧ Integral T (iK.comp (algebraMap c.F K)) y' := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 𝔓 T iK hiK yT hyT
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  obtain ⟨ρV, hρV⟩ := exists_restrict_ringHom (algebraMap (𝓞 K) K) (algebraMap T.V T.Fr) hinj iK
    (fun r => (hiK _).2 (HeightOneSpectrum.valuation_le_one 𝔓 r))
  obtain ⟨G, n, -⟩ := (GlobalTheory.LamT.pat_pullback E H _ _ ρV B).1
  obtain ⟨_, _, _, _, _, n', -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap iK) t₀
  have hx : yT.x = spMap iK ≫ y.x := hyT.1
  obtain ⟨m1', h1⟩ := sab_comp' n' m1 yT.x hx
  obtain ⟨k2, hk2⟩ := sab_comp' n' m2 _ rfl
  obtain ⟨m2', h2⟩ := sab_cancel' n k2 (spMap (algebraMap T.V T.Fr))
    (by rw [← spMap_comp', ← spMap_comp', hρV])
  obtain ⟨⟨g0, hg0u, hg0⟩, -⟩ := GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T (iK.comp (algebraMap c.F K)) G.t _ yT.x m1' m2' yT rfl
  obtain ⟨a0, ha0⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T (iK.comp (algebraMap c.F K)) G _ yT.x m1' m2' yT rfl
  choose k hk using fun σ => GlobalTheory.T.exists_integral_unimodular_mul_lowerTriangular_of_det_ne_zero T.V T.Fr (Dw.mult σ) (g0 σ) (hg0u σ).ne_zero
  have hkdet : ∀ σ, IsUnit (((k σ).map (algebraMap T.V T.Fr))).det := fun σ => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hk σ).1.map _
  let C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr :=
    fun σ => (k σ).map (algebraMap T.V T.Fr) * g0 σ
  have hCdet : ∀ σ, IsUnit (C σ).det := fun σ => by
    simp only [C, Matrix.det_mul]
    exact (hkdet σ).mul (hg0u σ)
  have hlow : ∀ σ i j, i < j → C σ i j = 0 := fun σ i j hij => (hk σ).2 i j hij
  have hdiag : ∀ σ i, C σ i i ≠ 0 := fun σ i => by
    have hd : (C σ).det = ∏ j, C σ j j :=
      Matrix.det_of_lowerTriangular _ (fun a b hab => hlow σ a b hab)
    have hne : (C σ).det ≠ 0 := (hCdet σ).ne_zero
    rw [hd] at hne
    exact Finset.prod_ne_zero_iff.1 hne i (Finset.mem_univ _)
  let td : Ix Dw → T.Frˣ := fun o => o.elim a0 (fun p => Units.mk0 (C p.1 p.2 p.2) (hdiag p.1 p.2))
  obtain ⟨y', hy', hyu⟩ := existsUnique_frChg E H Dw l Xo c T.Fr yT C a0 hCdet
  obtain ⟨y0, hy0, -⟩ := existsUnique_frChg E H Dw l Xo c T.Fr yT g0 a0 hg0u
  obtain ⟨y1, hy1, -⟩ := existsUnique_frChg E H Dw l Xo c T.Fr y0 (fun σ => (k σ).map (algebraMap T.V T.Fr)) 1 hkdet
  have hc := (frChg_refl_and_comp E H Dw l Xo c T.Fr yT y0 y1).2 g0 _ (a0 : T.Fr) _ hy0 hy1
  have h1y : y1 = y' := hyu y1 (by simpa [C] using hc)
  have hL0 : LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y0.u := hg0 a0 y0 hy0
  have hL1 : LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y1.u :=
    (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T (iK.comp (algebraMap c.F K)) G.t _ yT.x m1' m2' y0 hy0.1).2 hL0 k _ y1
      (fun σ => (hk σ).1) hy1
  rw [h1y] at hL1
  refine ⟨ρV, hρV, G, _, n, n', m1', m2', h1, h2.trans hk2, C, td, y', hlow, fun σ i => rfl, hy', hL1, ?_⟩
  exact integral_of_eq T (iK.comp (algebraMap c.F K)) y' hy'.1 m1' m2' hL1 (ha0 C y' hy')

end GlobalTheory.PtDegInt
