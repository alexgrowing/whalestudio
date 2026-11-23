import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentBundlePowerHeckeQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedBundleOfDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiInvolutionOfGaloisIsogenyDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendedBundleGaloisCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledByIntegerPrimeToPStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke

theorem exists_pol_translate : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso P' (P'.pull (lift (snd A' A') (fst A' A')).left) ∧ Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) ∧ (∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1) ∧ (∀ c' : D.O, LBIso (P'.pull (lift (fst A' A' ≫ act'.act c') (snd A' A')).left) (P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c').unop)).left)) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o A' _ _ act' ψ hA' hψ hG hact
  obtain ⟨P₀, hP₀, w₀⟩ := GlobalTheory.T.exists_descent_bundle_power_hecke_quotient' p D R b g c k N hc hk hN hNp hEF hg hck S s o A' ψ hA' hψ hG
  obtain ⟨P', hP', r1, r2, w⟩ := GlobalTheory.T.exists_birigidified_bundle_of_descent p D R b (N * k) S s o A' ψ hψ _ P₀ hP₀ w₀
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left _ |>.1 hk)
  have hk2 : 0 < k ^ 2 := by positivity
  have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_dvd_iff] at hck; omega)
  have hm1 : 1 ≤ k ^ 2 / c := Nat.div_pos (Nat.le_of_dvd hk2 hck) hc0
  have hmp : (k ^ 2 / c).Coprime p :=
    Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hck) (hk.pow_left 2)
  exact ⟨P', hP', r1, r2,
    GlobalTheory.T.descended_birigidified_bundle_symmetric p D R b (N * k) S s o A' ψ _ hA' hψ hG _ P' hP' w r1 r2,
    GlobalTheory.T.relAmple_diagonal_descended_bundle_galois_cover p D R b (N * k) S s o A' ψ _ hA' hψ hG _ hm1 P' hP' w,
    GlobalTheory.T.descendedBundle_kernel_killed_by_integer_prime_to_p p D R b (N * k) S s o A' ψ _ hA' hψ hG _ hmp P' hP' w,
    GlobalTheory.T.rosati_involution_of_galois_isogeny_descent p D R b (N * k) S s o A' act' ψ _ hA' hψ hG hact _ P' hP' w r1 r2, w⟩

end GlobalTheory.UPel.HT.Hecke
