import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor.VExist

theorem cube_corr {G U : Type} [CommGroup G] [CommGroup U] {θ : G → G → G → U} (h : IsCub θ) (a a' b b' p q : G) :
    θ b q a * θ b q p * θ a p (b * q) * (θ b' q a' * θ b' q p * θ a' p (b' * q)) * θ (a * b) (a' * b') (p * q) =
      θ a a' p * θ b b' q * θ a a' q * θ b b' p *
        (θ (b * b') q (a * a') * θ (b * b') q p * θ (a * a') p (b * b' * q)) := by
  have E := fun {x y : U} (e : x = y) => congrArg Additive.ofMul e
  have k0 := E (h.compat a b (a' * b') (p * q))
  have k1 := E (h.compat b b' q (a * a'))
  have k2 := E (h.compat a a' p (b * b' * q))
  have k3 := E (h.compat a' b' a (p * q))
  have k4 := E (h.compat a' b' b (p * q))
  have k5 := E (h.coc b b' q p)
  have k6 := E (h.coc b' q p b)
  have k7 := E (h.coc a' (b' * p * q) b a)
  have k8 := E (h.coc a a' q b)
  have k9 := E (h.coc a a' q b')
  have k10 := E (h.coc a' q b' a)
  have k11 := E (h.coc a (a' * q) b' b)
  have k12 := E (h.coc a a' b' b)
  have k13 := E (h.coc a' (b' * q) b a)
  have k14 := E (h.coc a' q b' b)
  have k15 := E (h.coc b (b' * q) p a)
  have k16 := E (h.coc b q p a)
  have k17 := E (h.coc b' q p a)
  have k18 := E (h.coc b (b' * q) p a')
  have k19 := E (h.coc a (p * q) b' a')
  have k20 := E (h.coc b (p * q) b' a')
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at *
  simp only [mul_comm, mul_assoc, mul_left_comm, h.s01, h.s12] at *
  linear_combination (norm := abel) k0 - k1 - k2 + k3 + k4 - k5 - k6 + k7 - k8 - k9 - k10 - k11 + k12 - k13 - k14 - k15 + k16 - k17 - k18 + k19 + k20

end GlobalTheory.Mum.TensTor.VExist

namespace GlobalTheory.Mum.TensTor.VExist

theorem pair_mult {F : Type} [Field F] (N : NumD F) (gi gj : N.Gt) (ai aj ai' aj' : N.X) :
    gj.s (ai + ai') * gi.s (aj + aj') /
        (N.θ (N.c (aj + aj')) gj.b (N.c (ai + ai')) * N.θ (N.c (aj + aj')) gj.b gi.b *
          N.θ (N.c (ai + ai')) gi.b (N.c (aj + aj') * gj.b)) *
      (N.θ (N.c ai * N.c aj) (N.c ai' * N.c aj') (gi.b * gj.b) /
        (N.θ (N.c ai) (N.c ai') gi.b * N.θ (N.c aj) (N.c aj') gj.b)) =
    gj.s ai * gi.s aj / (N.θ (N.c aj) gj.b (N.c ai) * N.θ (N.c aj) gj.b gi.b * N.θ (N.c ai) gi.b (N.c aj * gj.b)) *
      (gj.s ai' * gi.s aj' /
        (N.θ (N.c aj') gj.b (N.c ai') * N.θ (N.c aj') gj.b gi.b * N.θ (N.c ai') gi.b (N.c aj' * gj.b))) := by
  have m₁ := congrArg Additive.ofMul (gj.mult ai ai')
  have m₂ := congrArg Additive.ofMul (gi.mult aj aj')
  have k := congrArg Additive.ofMul (cube_corr N.cub (N.c ai) (N.c ai') (N.c aj) (N.c aj') gi.b gj.b)
  rw [N.c_add, N.c_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at m₁ m₂ k ⊢
  linear_combination (norm := abel) m₁ + m₂ + k

theorem gtRelV_exists : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F),
    TensFacts W φ e wv → ∀ vs : Fin r → N.Gt, ∃ v' : N'.Gt, GtRelV W φ e wv v' vs := by
  intro F _ N N' r W φ e wv hT vs
  obtain ⟨-, hφb, he_add, -, hc, hw0, hθ, -⟩ := hT
  set b' := Function.surjInv hφb.2 (fun j => (vs j).b) with hb'def
  have hb' : ∀ j, φ b' j = (vs j).b := fun j => congrFun (Function.surjInv_eq hφb.2 _) j
  let U : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hw0 x)
  let R : N'.X → Fˣ := fun χ' => ∏ i, ∏ j, ((vs j).s (e χ' i) * (vs i).s (e χ' j) /
          (N.θ (N.c (e χ' j)) (vs j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (vs j).b (vs i).b *
            N.θ (N.c (e χ' i)) (vs i).b (N.c (e χ' j) * (vs j).b))) ^ W i j
  let s' : N'.X → Fˣ := fun χ' => R χ' * U (N'.c χ' * b') * U 1 / (U (N'.c χ') * U b')
  have hmult : ∀ χ χ' : N'.X, s' (χ + χ') * N'.θ (N'.c χ) (N'.c χ') b' = s' χ * s' χ' := by
    intro χ χ'
    let P : Fˣ := ∏ i, ∏ j, (N.θ (N.c (e χ i) * N.c (e χ j)) (N.c (e χ' i) * N.c (e χ' j)) ((vs i).b * (vs j).b) /
        (N.θ (N.c (e χ i)) (N.c (e χ' i)) (vs i).b * N.θ (N.c (e χ j)) (N.c (e χ' j)) (vs j).b)) ^ W i j
    have hθu : N'.θ (N'.c χ) (N'.c χ') b' * U (N'.c χ * N'.c χ' * b') * U (N'.c χ) * U (N'.c χ') * U b' =
        P * U (N'.c χ * N'.c χ') * U (N'.c χ * b') * U (N'.c χ' * b') * U 1 := by
      have h := hθ (N'.c χ) (N'.c χ') b'
      simp only [hc, hb'] at h
      exact Units.ext (by simpa [U, P] using h)
    have hR : R (χ + χ') * P = R χ * R χ' := by
      simp only [R, P, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
      rw [← mul_zpow, ← mul_zpow, he_add, he_add, pair_mult]
    have a := congrArg Additive.ofMul hθu
    have b := congrArg Additive.ofMul hR
    simp only [s', N'.c_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at a b ⊢
    linear_combination (norm := abel) a + b
  refine ⟨⟨b', s', hmult⟩, hb', fun χ' => ?_⟩
  have h1 := hw0 (N'.c χ')
  have h2 := hw0 b'
  simp only [s', U, Units.val_div_eq_div_val, Units.val_mul, Units.val_mk0]
  field_simp
  simp only [R]
  ring

end GlobalTheory.Mum.TensTor.VExist
