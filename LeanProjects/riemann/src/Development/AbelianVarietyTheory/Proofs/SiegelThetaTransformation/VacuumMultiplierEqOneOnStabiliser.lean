import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetFrameNeZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierTrivialPrincipalCongruenceStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem GlobalTheory.Dict.conjI_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (l : Geo.Tor.Level H) : conjI (Mfr l) = l.Mb := by
  have hb : ∀ a : 𝓞 E, Lev.bar a = H.bar a := fun a => by
    apply IsFractionRing.injective (𝓞 E) E
    exact (H.bar_eq a).symm
  ext a
  rw [Lev.mem_conjI, hb, Mfr,
    Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective]
  exact ⟨fun ⟨y, hy, e⟩ => H.bar.injective e ▸ hy, fun h => ⟨a, h, rfl⟩⟩

theorem GlobalTheory.Dict.mult_eq_one_on_stab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (D : SW.Level X) (hn : r ≤ n) (ph : (Fin n → LaJ Xo c d) → c.F), IsSympl X bas → Even n → LevTie d σ ph D hn → ∀ (D' : Datum H) (φ : D'.La →ₗ[𝓞 E] (Fin r → E)), r = D'.p + D'.q → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a b, ((D'.EF a b : ℤ) : ℚ) = EF X (φ a) (φ b)) → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → ∀ L ∈ D.lats, ∀ ga ∈ D.grp, mapL ga L = L → mu ga L = 1 ∧ ∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + l.M • u' := by
  intro E _ _ _ H Dw l Xo c n d σ r g X bas idx D hn ph hs hev hT D' φ hr hinj hsp hEF v₀ hv mu hmu L hL ga
    hga hfix
  have hle : D.𝔪 ≤ Mfr l := by rw [hT.prod]; exact Ideal.mul_le.2 fun a ha b _ => Ideal.mul_mem_right b _ ha
  have hN : Mfr l * conjI (Mfr l) = Ideal.span {(l.M : 𝓞 E)} := by
    rw [conjI_half, mul_comm]; exact l.prod
  obtain ⟨h1, h2, h3⟩ := (stab_trivial_mod E r X g bas idx n hs hev D (Mfr l) l.M hle hN
    (fun k hk => (hT.grp k).1 hk) ga hga).2 L hL hfix
  refine ⟨?_, h1⟩
  obtain ⟨-, -, hgrp, hlat, -⟩ := GlobalTheory.SW.level_laws E r X g bas idx n hs hev D hn
  obtain ⟨hu, k, hk, hred⟩ := (hgrp ga).1 hga
  obtain ⟨hsd, -, -, hsh⟩ := hlat L hL
  have hfix' : mapL ga (D.sh L) = D.sh L := by rw [← (hsh ga hga).2, hfix]
  have hvac := hv L hL
  have hw := GlobalTheory.T.vacuumMultiplier_trivial_principalCongruence E r X g bas idx n hs hev H D' φ hr hinj hsp hEF (D.sh L) hsd l.M l.three_le ga hu
    hfix' h2 (v₀ L) (hT.w ▸ hvac)
  have hlam : D.lam ⟨k, hk⟩ = 1 := hT.det _ (h3 ⟨k, hk⟩ hred l.three_le)
  have e := hmu ga hga L hL ⟨k, hk⟩ hred
  rw [hw, hlam, hfix, Units.val_one, _root_.mul_one] at e
  have hne : v₀ L ≠ 0 := fun h0 => by
    have := hvac.2.1
    rw [h0] at this
    simp [ip, haar, haarAt] at this
  have : (mu ga L - 1) • v₀ L = 0 := by rw [sub_smul, one_smul, ← e, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hne)
