import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeformationBaseRingLocalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFamilyLocalDomainOfTwoFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValueTwoFibresLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtOfThetaConstantsAndFirstJetsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.KeyTop

theorem levelPoint_cast {S : Scheme.{0}} {P : PolAV S} {M : ℕ} {u₁ u₂ : Γ(S, ⊤)ˣ} (h : u₁ = u₂)
    (l : Out.Level P M u₁) {g : ℕ} (hg : P.g = g) : levelPoint (h ▸ l) hg = levelPoint l hg := by
  subst h; rfl

theorem exhaust {K : Type} [Field K] [IsAlgClosed K] {P : PolAV (Sp K)} {M : ℕ} {ze : Γ(Sp K, ⊤)ˣ}
    (lev : Out.Level P M ze) {g : ℕ} (hg : P.g = g) (z : baseOver (Sp K) ⟶ P.A) (hz : z ^ M = 1) :
    ∃ a, levelPoint lev hg a = z := by
  subst hg
  obtain ⟨c, hc⟩ := lev.span K (𝟙 _) z hz
  refine ⟨fun i => ((c i : ℕ) : ZMod M), ?_⟩
  rw [levelPoint_rfl, Out.Level.toPt, ← hc]
  congr 1
  funext i; exact ZMod.val_cast_of_lt (c i).isLt

end GlobalTheory.MBLow.KeyTop

namespace GlobalTheory.MBLow.KeyTop

theorem transfer_of_rule4 : ∀ κ : Rule, Rule4 κ → Transfer κ := by
  intro κ hκ g n hn hodd
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_family_localDomain_of_twoFibres g n hn hodd
  refine ⟨max j₁ 1, fun j hj C _ _ _ _ _ e x hg ζ lev k hD => ?_⟩
  have hj1 : j₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj2 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hmodd : Odd (n ^ j) := hodd.pow
  have hm3 : 3 ≤ n ^ j := by
    have h2 := hn.two_le
    have hne : n ≠ 2 := fun h => by subst h; exact (Nat.not_even_iff_odd.mpr hodd) even_two
    have := Nat.le_self_pow (show j ≠ 0 by omega) n
    omega
  obtain ⟨Θ, Γ, π, b, hπ, hb, hJ, ε, hε, hD'⟩ := hD
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  let Φ : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) ⊕ (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) × Fin g → PowerSeries C :=
    Sum.elim Θ (fun p => Γ p.1 p.2)
  let c : Fin 2 → C := ![(ζ : C), k]
  have hbΦ : ∀ a n, ‖PowerSeries.coeff n (Φ a)‖ ≤ b := by
    rintro (a | ⟨a, i⟩) n
    · exact (hb a n).1
    · exact (hb a n).2 i
  have hsΦ : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → ∀ a, Summable fun n => ‖e (PowerSeries.coeff n (Φ a)) * u ^ n‖ := by
    intro u hu hu'
    obtain ⟨hs, -⟩ := hD' u hu hu'
    rintro (a | ⟨a, i⟩)
    · exact (hs a).1
    · exact (hs a).2 i
  obtain ⟨u, o, _, _, jo, c₀, hu0, huε, hc₀, W, _, _, _, _, _, _, β, i₀, i₁, φ, hinj, h0, h1, hunit, hprime, hφ⟩ :=
    GlobalTheory.T.exists_deformation_base_ring_local_domain C e _ (Fin 2) Φ c π b ε hπ hε hbΦ hsΦ
  obtain ⟨-, x₀, hg₀, lev₀, hJ₀, hκ₀⟩ := hD' u hu0 huε
  have hc0 : jo (c₀ 0) = ζ := hc₀ 0
  have hc1 : jo (c₀ 1) = k := hc₀ 1
  have hζ0 : c₀ 0 ≠ 0 := fun h => ζ.ne_zero (by rw [← hc0, h, map_zero])
  let ζ₀ : oˣ := Units.mk0 (c₀ 0) hζ0
  have hu₁ : Units.map (i₁.comp β).toMonoidHom ζ₀ = ζ := Units.ext (by
    show (i₁.comp β) (c₀ 0) = ζ
    rw [h1, hc0])
  have hu₀ : Units.map (i₀.comp β).toMonoidHom ζ₀ = Units.map e.toMonoidHom ζ := Units.ext (by
    show (i₀.comp β) (c₀ 0) = e ζ
    rw [h0, RingHom.comp_apply, hc0])
  have hl₀ := (congrArg unitOn hu₀).symm
  have hl₁ := (congrArg unitOn hu₁).symm
  let l₀ := hl₀ ▸ lev₀
  let l₁ := hl₁ ▸ lev
  have eϑ₀ : (fun a => ∑' n, e (PowerSeries.coeff n (Θ a)) * u ^ n) = fun a => i₀ (φ (Sum.inl a)) :=
    funext fun a => ((hφ (Sum.inl a)).1).symm
  have eJ₀ : (fun a i => ∑' n, e (PowerSeries.coeff n (Γ a i)) * u ^ n) = fun a i => i₀ (φ (Sum.inr (a, i))) :=
    funext fun a => funext fun i => ((hφ (Sum.inr (a, i))).1).symm
  have eϑ₁ : (fun a => ∑' n, PowerSeries.coeff n (Θ a) * π ^ n) = fun a => i₁ (φ (Sum.inl a)) :=
    funext fun a => ((hφ (Sum.inl a)).2).symm
  have eJ₁ : (fun a i => ∑' n, PowerSeries.coeff n (Γ a i) * π ^ n) = fun a i => i₁ (φ (Sum.inr (a, i))) :=
    funext fun a => funext fun i => ((hφ (Sum.inr (a, i))).2).symm
  rw [eϑ₀, eJ₀, ← levelPoint_cast hl₀ lev₀ hg₀] at hJ₀
  rw [eϑ₁, eJ₁, ← levelPoint_cast hl₁ lev hg] at hJ
  have hθ₀ := GlobalTheory.T.isThetaPt_of_thetaConstantsAndFirstJets ℂ x₀ g hg₀ (n ^ j) hmodd (by exact_mod_cast pow_ne_zero _ hn.ne_zero) _ _ _ _ hJ₀
  have hθ₁ := GlobalTheory.T.isThetaPt_of_thetaConstantsAndFirstJets C x g hg (n ^ j) hmodd (by exact_mod_cast pow_ne_zero _ hn.ne_zero) _ _ _ _ hJ
  obtain ⟨P, pt, φ₀, φ₁, hPg, hpt, hpb₀, hpb₁, hL₀, hL₁, hc₀', hc₁'⟩ :=
    hj₁ j hj1 o ζ₀ W β (fun a => φ (Sum.inl a)) ℂ C i₀ i₁ hprime x₀.P x.P hg₀ hg l₀ l₁ hθ₀ hθ₁
  have hk₀ : (κ ℂ x₀ : ℂ) = i₀ (β (c₀ 1)) := by
    rw [hκ₀, ← RingHom.comp_apply i₀ β, h0, RingHom.comp_apply, hc1]
  have := GlobalTheory.T.thetaKeyValue_two_fibres_local_ring κ hκ W ℂ C i₀ i₁ hinj hunit P x₀ x g hg₀ hg (n ^ j) hPg hmodd hm3 _ pt
    (levelPoint l₀ hg₀) (levelPoint l₁ hg) φ₀ φ₁ hpt hpb₀ hpb₁ hL₀ hL₁ hc₀' hc₁'
    (fun z hz => exhaust l₁ hg z hz) _ _ (β (c₀ 1)) hJ₀ hJ hk₀
  rw [this, ← RingHom.comp_apply i₁ β, h1, hc1]

end GlobalTheory.MBLow.KeyTop
