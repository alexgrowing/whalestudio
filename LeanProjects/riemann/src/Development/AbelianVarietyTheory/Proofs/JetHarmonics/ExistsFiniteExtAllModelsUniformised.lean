import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GCorSt
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionAllModelsUniformized

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.IntegralPull

theorem exists_finite_ext_all_models_uniformised {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr)
    (y : IntFr Xo c T io) (e : ℕ) (la : HeightOneSpectrum (𝓞 c.F)) (ho : OverLa la T.V io e) (hy : y.IsAlg) :
    ∃ (T' : CDVR) (φ : T.V →+* T'.V) (φF : T.Fr →+* T'.Fr) (e₁ : ℕ) (z' : IntFr Xo c T' (φF.comp io)),
      Function.Injective φ ∧ IsLocalHom φ ∧ φ.Finite ∧
      φF.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp φ ∧
      0 < e₁ ∧ OverLa la T'.V (φF.comp io) (e * e₁) ∧ z'.IsAlg ∧
      (letI := io.toAlgebra; letI := (φF.comp io).toAlgebra
        FrMap ({ φF with commutes' := fun _ => rfl } : T.Fr →ₐ[c.F] T'.Fr) y.1 z'.1) ∧
      ∀ I : IntData Xo c T' (φF.comp io) z'.1, ∃ P : PELUnif (maximalIdeal T'.V) I.G, P.TorsionIso := by
  have : Finite (ResidueField T.V) := hy
  obtain ⟨G, t, m1, m2, -⟩ := y.2.2
  obtain ⟨W, _, _, _, hc, _, hf, hi, hr, hS⟩ := GlobalTheory.UnifAfterExt.exists_split_baseChange T.V G.G G.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  let T' : Formalism.L2.Pj.CDVR := { V := W }
  have : FaithfulSMul T.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hl : IsLocalHom (algebraMap T.V W) := inferInstance
  have hj : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T.V W)) :=
    (IsFractionRing.injective W _).comp hi
  obtain ⟨φ, hφ⟩ : ∃ φ : T.Fr →+* T'.Fr, ∀ v, φ (algebraMap T.V T.Fr v) = algebraMap T'.V T'.Fr (algebraMap T.V W v) :=
    ⟨IsFractionRing.lift hj, IsFractionRing.lift_algebraMap hj⟩
  obtain ⟨r, hr0, hv⟩ := exists_index (V' := T'.V) (algebraMap T.V W) φ hφ
  letI := io.toAlgebra
  letI := (φ.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { φ with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c _ _ ψ y.1
  obtain ⟨p, χ, y₀, hy₀⟩ := y.2.1
  let y' : IntFr Xo c T' (φ.comp io) :=
    ⟨z, ⟨p, ψ.comp χ, y₀, Formalism.L2.Pj.frMap_trans (Xo := Xo) (c := c) _ _ _ χ ψ y₀ y.1 z hy₀ hz⟩,
      integral_baseChange T T' io (φ.comp io) _ hi ψ hφ y.1 z hz y.2.2⟩
  refine ⟨T', algebraMap T.V W, φ, r, y', hi, hl, RingHom.finite_algebraMap.2 hf, RingHom.ext hφ, hr0, ?_, hr, hz,
    fun I => exists_unif_of_split T T' _ φ hφ m1 m2 hz.1 I.m1 I.m2 hS⟩
  rw [Nat.mul_comm]
  exact ho.bc φ hr0 hv

end GlobalTheory.IntegralPull
