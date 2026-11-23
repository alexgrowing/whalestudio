import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicMapLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyBaseChangeModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelFiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalModelProjectiveFlatStatement

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory

namespace GlobalTheory.SiegLoc

theorem exists_siegel_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (n : ℕ) (R : Type) [CommRing R] (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (φ : InvFun ℤ) (F : SFam (Module.finrank ℚ E / 2 * (D.p + D.q)) n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ), 1 ≤ D.p + D.q → 3 ≤ n → Odd n → n ∣ l.M → IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ (n : 𝓞 c.F) R _ b.toAlgebra → SiegData (Module.finrank ℚ E / 2 * (D.p + D.q)) φ n F S s j G e BD d N → ∃ (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S), (∀ x, ((ω (κ x) : c.F) : ℂ) = (x : ℂ)) ∧ IsSiegPull s j G e κ C π := by
  intro E _ _ _ H D l Xo c n R _ b ω φ F S s j _ G _ e BD d N hpq hn hodd hnM hω hωb hloc hSD
  obtain ⟨o, ⟨m0⟩⟩ := GlobalTheory.obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) Xo.X (Xo.XF c) Xo.s
    (pullback.fst _ _ ≫ Xo.s) (pullback.fst _ _) rfl rfl
    (by rw [show spMap (RingHom.id (KA l)) = 𝟙 _ from Spec.map_id _, Category.comp_id]) Xo.univ
  obtain ⟨κ, hκ, hκfin⟩ := GlobalTheory.T.exists_cyclotomic_map_localization E H l c n R b ω hn hnM hω hωb hloc
  obtain ⟨y, α, α₂, hy, hα, hsq, hΛ, hfin⟩ := GlobalTheory.T.siegel_family_base_change_model E H D l Xo c n (ω.comp κ) o m0 F hpq hn hodd hnM hκ
  have hnormF : Geo.Tor.IsNormalScheme (Xo.XF c) := by
    have := Xo.smooth
    have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
      (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance).2.1
  obtain ⟨Y, π, sY, jQ, hπ, hπs, hYn, hYp, hYf, hjQs, hjQπ, hjQo, hjQd, hrange⟩ :=
    GlobalTheory.T.exists_normal_model_finite (cycAway n) R c.F κ ω S F.X (Xo.XF c) s j F.s _ y hy hω hκfin hSD.1 hSD.2.2.1 hnormF hfin
  obtain ⟨t, m, μ, hμ, hmμ, hab⟩ := GlobalTheory.T.normal_model_projective_flat E H _ φ n F S s j G e BD d N R c.F ω (Xo.XF c) Y sY jQ π o.t y α α₂
    hn hSD hω hYn hYp hYf hjQo hjQd hπ o.proper hjQπ hα hsq hΛ
  have hab' : pullback.fst sY (spMap ω) ⁻¹' abLocus t.G = Set.range jQ := by
    ext x
    rw [Set.mem_preimage, hab, Set.mem_preimage, hSD.2.2.2.2.2.2.2.1, hrange]
  exact ⟨κ, ⟨Y, sY, hYn, hYp, hYf, jQ, hjQs, hjQo, hjQd, t, o, m0, m, hab'⟩, π, hκ, μ, y, α, α₂, hπ, hπs, hμ,
    hjQπ.symm, hα, hsq, hΛ, hmμ⟩

end GlobalTheory.SiegLoc
