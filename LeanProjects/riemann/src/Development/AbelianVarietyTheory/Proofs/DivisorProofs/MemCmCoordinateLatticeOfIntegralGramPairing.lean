import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearHomPowEqOfKillsComplexTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearHomKillsTorsionOfWeilPairingDivisibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingLinearHomSpanGramFormStatement

set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

theorem mem_lat_of_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ d : Fin p → E, (∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) →
        d ∈ GlobalTheory.FlatCM.HomLat.lat X := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X gP gQ hG barE hbar d hd
  classical
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image d)
  have hsq : ((y.natAbs ^ 2 : ℕ) : ℤ) = y * y := by rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs, sq]
  have hint : ∀ a, IsIntegral ℤ (((y.natAbs ^ 2 : ℕ) : E) * d a) := fun a => by
    have h1 := hyi (d a) (Finset.mem_image_of_mem d (Finset.mem_univ a))
    have e : ((y.natAbs ^ 2 : ℕ) : E) * d a = (algebraMap ℤ E y) * (y • d a) := by
      rw [zsmul_eq_mul, algebraMap_int_eq, eq_intCast, ← _root_.mul_assoc]
      congr 1
      rw [← Int.cast_natCast (R := E), hsq]
      try push_cast
      try ring
    rw [e]
    exact isIntegral_algebraMap.mul h1
  set n : ℕ := y.natAbs ^ 2 with hn_def
  have hn : 0 < n := pow_pos (Int.natAbs_pos.2 hy0) 2
  let x : Fin p → 𝓞 E := fun a => ⟨(n : E) * d a, hint a⟩
  have hx : ∀ a, (x a : E) = n * d a := fun a => rfl
  have hψ := GlobalTheory.FlatCM.HomLat.isLinearHom_prod X x
  have hk := GlobalTheory.T.linearHom_kills_torsion_of_weilPairing_divisible E H hH K ρ σ₁ p X _ hψ n hn (fun f hf ⟨m, hm, z, hfz⟩ => by
    have hm' : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
    have hc : (fun a => (z a : E) / m) ∈ GlobalTheory.FlatCM.HomLat.lat X := Submodule.subset_span
      ⟨m, hm, z, fun a => by field_simp, f, hf, hfz⟩
    obtain ⟨w, hw⟩ := hd _ hc
    refine ⟨w, GlobalTheory.T.weilPairing_linearHom_span_gramForm E H hH K ρ σ₁ p X gP gQ hG m hm z f hf hfz x _ ?_⟩
    have hb : ∀ b, ((H.bar (x b) : 𝓞 E) : E) = n * barE (d b) := fun b => by
      rw [← hbar, hx, map_mul, map_natCast]
    have key : (m : E) * ((n : E) * (w : E)) =
        ∑ a, ∑ b, (z a : E) * (gP a b : E) * ((H.bar (x b) : 𝓞 E) : E) := by
      simp_rw [hb]
      rw [hw]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      field_simp
    apply RingOfIntegers.coe_injective
    push_cast
    exact key)
  obtain ⟨χ, hχ, hχn⟩ := GlobalTheory.T.exists_linearHom_pow_eq_of_kills_complex_torsion E H K σ₁ (X.A true) X.B _ hψ n hn hk
  exact Submodule.subset_span ⟨n, hn, x, hx, χ, hχ, hχn⟩

end GlobalTheory.FlatCM.HomLat
