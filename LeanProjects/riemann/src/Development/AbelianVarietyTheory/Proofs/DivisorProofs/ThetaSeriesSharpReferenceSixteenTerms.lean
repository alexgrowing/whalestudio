import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DescendToThetaConstantFieldStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreEighthPowerThetaObjectSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePrimeToCharTorsionRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibrePointTransferFixedModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistFibreIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharp_fibre_iso_exists : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∃ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f ∧ LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) ∧ (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) := by
  intro g l hl hodd W hW
  have LL := GlobalTheory.abelianSchemeLaws_all
  choose J hJ Mat κ w w' hTf using GlobalTheory.T.fibre_eighth_power_theta_object_subfield W hW
  have hD := fun gQ : ℕ => @GlobalTheory.T.descend_to_thetaConstant_field LL.1 LL.2 (8 * gQ) (J gQ) (hJ gQ) (Mat gQ) (κ gQ) l (w gQ) (w' gQ) hl hodd
  choose j₀f hj₀f using hD
  refine ⟨(Finset.range (g + 1)).sup j₀f + 1, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hCN hlu Q hQg ρ hρ D e hS C u mo hmo hTh K _ _ ev k₀ hk₀ hrat σ hσ
  have hj1 : 1 ≤ j := by omega
  obtain ⟨bT, t, v, ψ, hSh, hPr, hHT, hψ, hL, htor⟩ :=
    hTf Q.g l hl hodd j hj1 V V₁ hCN hlu Q rfl ρ hρ D e hS C u mo hmo hTh K ev k₀ hk₀ hrat
  have hle : j₀f Q.g ≤ j := by
    have := Finset.le_sup (f := j₀f) (Finset.mem_range.2 (by omega : Q.g < g + 1))
    omega
  have hs : spMap k₀.subtype = spMap k₀.subtype ≫ spMap (RingHom.id k₀) := by
    simp [spMap]
  obtain ⟨t₀, ⟨φ, hφ, hLφ, hpts, -⟩, -⟩ :=
    hj₀f Q.g j hle k₀ bT k₀ K (RingHom.id k₀) k₀.subtype (spMap k₀.subtype) t v hs hSh hPr hHT
  have hσe : σ.toRingHom.comp k₀.subtype = k₀.subtype := RingHom.ext fun r => hσ r r.2
  obtain ⟨f, hf, hfL, hfq⟩ := GlobalTheory.Poinc.Sep.Twist.twist_fibre_iso V₁ D.P.A D.P.L D.P.isLB K ev σ k₀ k₀.subtype hσe t.A t.L t.isLB ψ hψ hL t₀.A t₀.L t₀.isLB φ hφ hLφ
  refine ⟨f, hf, hfL, ?_⟩
  intro y hy q hq1 hq2
  obtain ⟨k, hk⟩ := hy
  obtain ⟨y', hy'1, hy'2⟩ := GlobalTheory.T.torsion_fibre_point_transfer_fixed_model V₁ D.P.A K ev t.A ψ hψ k₀ k₀.subtype t₀.A φ hφ (l ^ k) y hk q hq1 hq2
  haveI : IsAlgClosed k₀ := hk₀
  have hlk : IsUnit ((l ^ k : ℕ) : k₀) := by
    have h1 : IsUnit (ev (l : V₁)) := hlu.map ev
    have h2 : IsUnit ((l : k₀) : K) := by simpa using h1
    have h3 : IsUnit (l : k₀) := by
      rcases h2.exists_left_inv with ⟨x, hx⟩
      exact isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hx
    simpa using h3.pow k
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.abelianScheme_primeToChar_torsion_rational k₀ K k₀.subtype t₀.A t₀.ab (l ^ k) hlk y' hy'1
  rw [hfq q y₀ (by rw [← hy'2, hy₀]) hq2, hq1]

end GlobalTheory.Poinc.Sep
