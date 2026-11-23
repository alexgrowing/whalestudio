import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CurveRootGeometry.FrobFin

theorem isIntegralHom_frob (q : ℕ) [Fact q.Prime] (C : Scheme.{0}) (h : (q : Γ(C, ⊤)) = 0) :
    IsIntegralHom (frob C q h) where
  isAffine_preimage U hU := hU
  isIntegral_app U hU := by
    intro x
    refine ⟨Polynomial.X ^ q - Polynomial.C (show Γ(C, U) from x),
      Polynomial.monic_X_pow_sub_C _ (Fact.out : q.Prime).ne_zero, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero]
    exact (frob_app q h U x).symm

theorem isIso_frob_spec (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [PerfectField k] [CharP k q]
    (h : (q : Γ(Spec (.of k), ⊤)) = 0) : IsIso (frob (Spec (.of k)) q h) := by
  have e : frob (Spec (.of k)) q h = Spec.map (CommRingCat.ofHom (frobenius k q)) :=
    SS.FrobField.absFrob_spec k q 1 Fact.out h (frobenius k q)
      (fun c => by rw [pow_one, frobenius_def])
  rw [e]
  have : IsIso (CommRingCat.ofHom (frobenius k q)) :=
    (frobeniusEquiv k q).toCommRingCatIso.isIso_hom
  infer_instance

theorem isFinite_frob : ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [PerfectField k] [CharP k q]
    (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], LocallyOfFiniteType (strHom k C) →
    IsFinite (frob C q (natCast_eq_zero C q k)) ∧
      ∀ x : C, frob C q (natCast_eq_zero C q k) x = x := by
  intro q _ k _ _ _ C _ hC
  refine ⟨?_, fun x => rfl⟩
  have hk : (q : Γ(Spec (.of k), ⊤)) = 0 :=
    SS.FrobField.cast_zero_sp k (CharP.cast_eq_zero k q)
  have := isIso_frob_spec q k hk
  have e := frob_naturality q hk (strHom k C) (natCast_eq_zero C q k)
  have : LocallyOfFiniteType (frob C q (natCast_eq_zero C q k) ≫ strHom k C) := by
    rw [e]; infer_instance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).2
    ⟨isIntegralHom_frob q C _, locallyOfFiniteType_of_comp _ (strHom k C)⟩

end GlobalTheory.CurveRootGeometry.FrobFin
end
