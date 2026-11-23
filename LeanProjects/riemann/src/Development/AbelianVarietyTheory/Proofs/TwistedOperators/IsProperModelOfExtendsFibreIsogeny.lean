import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeOfGenericallySurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem isProper_of_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (F : G.G ⟶ G'.G) (N : ℕ), Ext m₁ m₂ n₁ n₂ f F → f' ≫ f = 𝟙 _ ^ N → 0 < N → IsProper G.G.hom → IsProper G'.G.hom := by
  intro E _ _ _ H Dw l Xo T x x' G G' t t' m₁ m₂ n₁ n₂ f f' F N ⟨ψ, _, hψ, hc⟩ hN hpos hG
  have hU : IsAbelianScheme Xo.univ.t.G :=
    ⟨Xo.univ.t.semi.comm, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩
  have hA : IsAbelianScheme (Fib Xo x') := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback x' _ hU
  have hB : IsAbelianScheme G.G := ⟨G.semi.comm, G.semi.smooth, hG, G.semi.geomConnected⟩
  have hch : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have hu : IsUnit (N : Γ(Sp T.Fr, ⊤)) := by
    have h0 : IsUnit (N : T.Fr) := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hpos.ne')
    have := h0.map (Scheme.ΓSpecIso (CommRingCat.of T.Fr)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, -, -, hs⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective _ (Fib Xo x') N hA hu
  have hl : f'.left ≫ f.left = (𝟙 (Fib Xo x') ^ N).left := congrArg (·.left) hN
  have hf : Function.Surjective f.left := by
    intro y
    obtain ⟨z, hz⟩ := hs.1 y
    refine ⟨f'.left z, ?_⟩
    rw [← Scheme.Hom.comp_apply, hl, hz]
  have p₁ : IsPullback m₁.φ t.G.hom Xo.univ.t.G.hom x := m₁.cart.1
  have q₁ : IsPullback n₁.φ t'.G.hom Xo.univ.t.G.hom x' := n₁.cart.1
  have q₂ : IsPullback n₂.φ t'.G.hom G'.G.hom (spMap (algebraMap T.V T.Fr)) := n₂.cart.1
  have hsq := hc p₁.isoPullback.hom q₁.isoPullback.hom (by simp) (by simp) (by simp) (by simp)
  have hψs : Function.Surjective ψ.left := by
    intro y
    obtain ⟨z, hz⟩ := hf (q₁.isoPullback.hom y)
    obtain ⟨w, rfl⟩ := (inferInstance : Surjective p₁.isoPullback.hom).1 z
    refine ⟨w, q₁.isoPullback.hom.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
    exact hz
  refine (GlobalTheory.isAbelianScheme_of_generically_surjective T.V T.Fr G.G G'.G hB G'.semi F ?_).proper
  rintro y ⟨s, hs⟩
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback q₂ y s hs.symm
  obtain ⟨w, rfl⟩ := hψs z
  refine ⟨m₂.φ w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hψ, Scheme.Hom.comp_apply, hz]

end GlobalTheory.HkIntegral
