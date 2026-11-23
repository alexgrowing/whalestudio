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

namespace GlobalTheory.Mum.TensTor

theorem cube_corr {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (xi xj yi yj ui uj : A) (sji sij tji tij : U) :
    sji * tji / θ xi yj uj * (sij * tij / θ xj yi ui) /
        (θ xj (yj * uj) xi * θ xj (yj * uj) (yi * ui) * θ xi (yi * ui) (xj * (yj * uj))) *
      (θ (xi * xj) (yi * yj) (ui * uj) / (θ xi yi ui * θ xj yj uj)) =
    sji * sij / (θ xj yj xi * θ xj yj yi * θ xi yi (xj * yj)) *
      (tji * tij / (θ xj uj xi * θ xj uj ui * θ xi ui (xj * uj))) := by
  have hp : ∀ x y z, θ x y z = θ y x z ∧ θ x y z = θ x z y ∧ θ x y z = θ z x y ∧ θ x y z = θ y z x ∧
      θ x y z = θ z y x := fun x y z =>
    ⟨h.s01 x y z, h.s12 x y z, (h.s12 x y z).trans (h.s01 x z y), (h.s01 x y z).trans (h.s12 y x z),
      ((h.s01 x y z).trans (h.s12 y x z)).trans (h.s01 y z x)⟩
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have c0 := E (show θ (xi * xj) (yi * yj) (ui * uj) * θ xi xj (ui * uj) = θ xi (xj * yi * yj) (ui * uj) * θ xj (yi * yj) (ui * uj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * yj) (ui * uj))
  have c1 := E (show θ (xj * ui) uj (yi * yj) * θ xj ui (yi * yj) = θ xj (ui * uj) (yi * yj) * θ ui uj (yi * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj ui uj (yi * yj))
  have c2 := E (show θ (xj * ui) (yi * yj) uj * θ xj ui uj = θ xj (yi * yj * ui) uj * θ ui (yi * yj) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj ui (yi * yj) uj)
  have c3 := E (show θ (xj * yj) uj (yi * ui) * θ xj yj (yi * ui) = θ xj (yj * uj) (yi * ui) * θ yj uj (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yj uj (yi * ui))
  have c4 := E (show θ (xj * yj) (yi * ui) uj * θ xj yj uj = θ xj (yi * yj * ui) uj * θ yj (yi * ui) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yj (yi * ui) uj)
  have c5 := E (show θ (xj * yi) ui yj * θ xj yi yj = θ xj (yi * ui) yj * θ yi ui yj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yi ui yj)
  have c6 := E (show θ (xj * yi) yj ui * θ xj yi ui = θ xj (yi * yj) ui * θ yi yj ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yi yj ui)
  have c7 := E (show θ (xi * xj) (yj * uj) (yi * ui) * θ xi xj (yi * ui) = θ xi (xj * yj * uj) (yi * ui) * θ xj (yj * uj) (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yj * uj) (yi * ui))
  have c8 := E (show θ (xi * xj) (yi * ui) (yj * uj) * θ xi xj (yj * uj) = θ xi (xj * yi * ui) (yj * uj) * θ xj (yi * ui) (yj * uj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * ui) (yj * uj))
  have c9 := E (show θ (xi * ui) uj (xj * yi * yj) * θ xi ui (xj * yi * yj) = θ xi (ui * uj) (xj * yi * yj) * θ ui uj (xj * yi * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui uj (xj * yi * yj))
  have c10 := E (show θ (xi * ui) (xj * yi * yj) uj * θ xi ui uj = θ xi (xj * yi * yj * ui) uj * θ ui (xj * yi * yj) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui (xj * yi * yj) uj)
  have c11 := E (show θ (xi * yj) uj (xj * yi * ui) * θ xi yj (xj * yi * ui) = θ xi (yj * uj) (xj * yi * ui) * θ yj uj (xj * yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yj uj (xj * yi * ui))
  have c12 := E (show θ (xi * yj) (xj * yi * ui) uj * θ xi yj uj = θ xi (xj * yi * yj * ui) uj * θ yj (xj * yi * ui) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yj (xj * yi * ui) uj)
  have c13 := E (show θ (xi * ui) uj xj * θ xi ui xj = θ xi (ui * uj) xj * θ ui uj xj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui uj xj)
  have c14 := E (show θ (xi * ui) xj uj * θ xi ui uj = θ xi (xj * ui) uj * θ ui xj uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui xj uj)
  have c15 := E (show θ (xi * xj) uj ui * θ xi xj ui = θ xi (xj * uj) ui * θ xj uj ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj uj ui)
  have c16 := E (show θ (xi * xj) ui uj * θ xi xj uj = θ xi (xj * ui) uj * θ xj ui uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj ui uj)
  have c17 := E (show θ (xi * yi) ui (xj * yj) * θ xi yi (xj * yj) = θ xi (yi * ui) (xj * yj) * θ yi ui (xj * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yi ui (xj * yj))
  have c18 := E (show θ (xi * yi) (xj * yj) ui * θ xi yi ui = θ xi (xj * yi * yj) ui * θ yi (xj * yj) ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yi (xj * yj) ui)
  have c19 := E (show θ (xi * xj) (yi * ui) yj * θ xi xj yj = θ xi (xj * yi * ui) yj * θ xj (yi * ui) yj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * ui) yj)
  have c20 := E (show θ (xi * xj) yj (yi * ui) * θ xi xj (yi * ui) = θ xi (xj * yj) (yi * ui) * θ xj yj (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj yj (yi * ui))
  have p0 := E (hp xj (yj * uj) xi).2.2.1
  have p1 := E (hp xj yj xi).2.2.1
  have p2 := E (hp xj yj yi).2.1
  have p3 := E (hp xj uj xi).2.2.1
  have p4 := E (hp (xj * ui) uj (yi * yj)).2.2.1
  have p5 := E (hp xj ui (yi * yj)).2.1
  have p6 := E (hp xj (ui * uj) (yi * yj)).2.1
  have p7 := E (hp ui uj (yi * yj)).2.2.1
  have p8 := E (hp (xj * ui) (yi * yj) uj).1
  have p9 := E (hp ui (yi * yj) uj).1
  have p10 := E (hp (xj * yj) uj (yi * ui)).2.1
  have p11 := E (hp yj uj (yi * ui)).2.1
  have p12 := E (hp (xj * yi) ui yj).2.1
  have p13 := E (hp xj (yi * ui) yj).2.1
  have p14 := E (hp yi ui yj).2.1
  have p15 := E (hp (xi * xj) (yj * uj) (yi * ui)).2.1
  have p16 := E (hp xi (xj * yj * uj) (yi * ui)).2.1
  have p17 := E (hp xj (yj * uj) (yi * ui)).2.1
  have p18 := E (hp (xi * ui) uj (xj * yi * yj)).2.2.1
  have p19 := E (hp xi ui (xj * yi * yj)).2.1
  have p20 := E (hp xi (ui * uj) (xj * yi * yj)).2.1
  have p21 := E (hp ui uj (xj * yi * yj)).2.2.1
  have p22 := E (hp (xi * ui) (xj * yi * yj) uj).1
  have p23 := E (hp ui (xj * yi * yj) uj).1
  have p24 := E (hp (xi * yj) uj (xj * yi * ui)).2.1
  have p25 := E (hp xi (yj * uj) (xj * yi * ui)).2.1
  have p26 := E (hp yj uj (xj * yi * ui)).2.1
  have p27 := E (hp (xi * ui) uj xj).2.2.1
  have p28 := E (hp xi ui xj).2.1
  have p29 := E (hp xi (ui * uj) xj).2.1
  have p30 := E (hp ui uj xj).2.2.1
  have p31 := E (hp (xi * ui) xj uj).1
  have p32 := E (hp ui xj uj).1
  have p33 := E (hp (xi * xj) uj ui).2.1
  have p34 := E (hp xi (xj * uj) ui).2.1
  have p35 := E (hp (xi * yi) ui (xj * yj)).2.1
  have p36 := E (hp xi (yi * ui) (xj * yj)).2.1
  have p37 := E (hp yi ui (xj * yj)).2.1
  have p38 := E (hp (xi * xj) (yi * ui) yj).2.1
  have p39 := E (hp xi (xj * yi * ui) yj).2.1
  rw [← mul_assoc xj yj uj]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at *
  linear_combination (norm := abel) c0 - c1 + c2 + c3 - c4 + c5 - c6 + c7 - c8 - c9 + c10 + c11 - c12 + c13 - c14 - c15 + c16 + c17 - c18 + c19 - c20 - p0 + p1 + p2 + p3 + p4 + p5 - p6 - p7 - p8 + p9 - p10 + p11 - p12 + 2 • p13 + p14 - p15 + p16 + p17 + p18 + p19 - p20 - p21 - p22 + p23 - p24 + p25 + p26 - p27 - p28 + p29 + p30 + p31 - p32 + p33 - p34 - p35 + p36 + p37 - p38 + p39

end GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem vmul_comb {U : Type} [CommGroup U] (s1 s2 t P1 P2 P Q wc wb wb' wcb wcb' wbb' wcbb' w1 : U)
    (h1 : s1 * wc * wb = P1 * wcb * w1) (h2 : s2 * wc * wb' = P2 * wcb' * w1)
    (h3 : t * wcbb' * wc * wb * wb' = Q * wcb * wcb' * wbb' * w1) (h4 : P * Q = P1 * P2) :
    s1 * s2 / t * wc * wbb' = P * wcbb' * w1 := by
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a1 := E h1; have a2 := E h2; have a3 := E h3; have a4 := E h4
  simp only [ofMul_mul, ofMul_div] at *
  linear_combination (norm := abel) a1 + a2 - a3 - a4

theorem gtRelV_mul : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv →
    ∀ (v' u' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' us →
      GtRelV W φ e wv (v' * u') (vs * us) := by
  intro F _ N N' r W φ e wv hT v' u' vs us hv hu
  obtain ⟨hφ, -, -, -, hφc, hw0, hcub, -⟩ := hT
  refine ⟨fun j => ?_, fun χ' => ?_⟩
  · show φ (v'.b * u'.b) j = (vs j).b * (us j).b
    rw [hφ, hv.1, hu.1]
  · let w : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hw0 x)
    let Pf : (Fin r → N.Gt) → Fˣ := fun g => ∏ i, ∏ j, ((g j).s (e χ' i) * (g i).s (e χ' j) /
      (N.θ (N.c (e χ' j)) (g j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (g j).b (g i).b *
        N.θ (N.c (e χ' i)) (g i).b (N.c (e χ' j) * (g j).b))) ^ W i j
    let Qf : Fˣ := ∏ i, ∏ j, (N.θ (N.c (e χ' i) * N.c (e χ' j)) ((vs i).b * (vs j).b) ((us i).b * (us j).b) /
      (N.θ (N.c (e χ' i)) (vs i).b (us i).b * N.θ (N.c (e χ' j)) (vs j).b (us j).b)) ^ W i j
    have h1 : v'.s χ' * w (N'.c χ') * w v'.b = Pf vs * w (N'.c χ' * v'.b) * w 1 := Units.ext (hv.2 χ')
    have h2 : u'.s χ' * w (N'.c χ') * w u'.b = Pf us * w (N'.c χ' * u'.b) * w 1 := Units.ext (hu.2 χ')
    have h3 := hcub (N'.c χ') v'.b u'.b
    rw [mul_assoc (N'.c χ') v'.b u'.b] at h3
    simp only [hφc, hv.1, hu.1] at h3
    have h3' : N'.θ (N'.c χ') v'.b u'.b * w (N'.c χ' * (v'.b * u'.b)) * w (N'.c χ') * w v'.b * w u'.b =
        Qf * w (N'.c χ' * v'.b) * w (N'.c χ' * u'.b) * w (v'.b * u'.b) * w 1 := Units.ext h3
    have h4 : Pf (vs * us) * Qf = Pf vs * Pf us := by
      simp only [Pf, Qf]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← mul_zpow, ← mul_zpow]
      exact congrArg (· ^ W i j) (cube_corr N.cub (N.c (e χ' i)) (N.c (e χ' j)) (vs i).b (vs j).b (us i).b (us j).b
        ((vs j).s (e χ' i)) ((vs i).s (e χ' j)) ((us j).s (e χ' i)) ((us i).s (e χ' j)))
    exact congrArg Units.val (vmul_comb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3' h4)

end GlobalTheory.Mum.TensTor
