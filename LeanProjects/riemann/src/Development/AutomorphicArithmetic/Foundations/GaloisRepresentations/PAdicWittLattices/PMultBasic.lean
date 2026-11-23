import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedIntCastLeIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem dvd_of_mult {p : ℕ} [Fact p.Prime] {m n : ℕ} (hm : m.Coprime p) {s t t' : AfP p}
    (hs : IsIntAf s) (ht' : IsIntAf t') (e : t * t' = 1) (h : (n : AfP p) * t = (m : AfP p) * s) : m ∣ n := by
  have hpos : 0 < m := by
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.1 hm)
  refine Int.natCast_dvd_natCast.1 (GlobalTheory.IntDvdAdele.dvd_of_eq_mul_int p m hpos hm (n : ℤ) (s * t')
    (GlobalTheory.HeckeApprox.isInt_mul hs ht') ?_)
  rw [Int.cast_natCast, ← _root_.mul_assoc, ← h, _root_.mul_assoc, e, _root_.mul_one]

theorem UpperTheory.Gal.G3.pMultBasic :
    NuInt → MultBasic := by
  intro hNu p _
  refine ⟨?_, ?_, ?_⟩
  · rintro a c c' hc hc' ⟨t, t', ht, ht', e, ha⟩ ⟨s, s', hs, hs', e', ha'⟩
    have h : (c : AfP p) * t = (c' : AfP p) * s := ha.symm.trans ha'
    exact Nat.dvd_antisymm (dvd_of_mult hc ht hs' e' h.symm) (dvd_of_mult hc' hs ht' e h)
  · rintro a a' c c' ⟨t, t', ht, ht', e, ha⟩ ⟨s, s', hs, hs', e', ha'⟩
    refine ⟨t * s, t' * s', GlobalTheory.HeckeApprox.isInt_mul ht hs, GlobalTheory.HeckeApprox.isInt_mul ht' hs', ?_, ?_⟩
    · rw [_root_.mul_mul_mul_comm, e, e', _root_.one_mul]
    · rw [ha, ha', Nat.cast_mul, _root_.mul_mul_mul_comm]
  · intro D G L u hu
    refine ⟨UpperTheory.Gal.G3.mul u, UpperTheory.Gal.G3.mul u⁻¹, hNu p D G L u (UpperTheory.Gal.Int.Geo.integ_of_mem hu),
      hNu p D G L u⁻¹ (UpperTheory.Gal.Int.Geo.integ_of_mem (inv_mem hu)),
      Units.mul_inv ((u : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2), ?_⟩
    rw [Nat.cast_one, _root_.one_mul]
