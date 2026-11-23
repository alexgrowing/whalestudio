import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

private theorem conj_core {V : Type*} [AddCommGroup V] [Module ℚ V] (H U Hi : V →+ V) {k N : ℕ} (hk : 0 < k) {v w : V}
    (hv : H (Hi v) = v) (e : U (k • Hi v) = k • Hi v + (N * k) • w) : H (U (Hi v)) = v + N • H w := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have h1 := congrArg H e
  simp only [map_nsmul, map_add, hv] at h1
  have h2 : k • H (U (Hi v)) = k • (v + N • H w) := by
    rw [h1, smul_add, mul_comm N k, mul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℚ k, ← Nat.cast_smul_eq_nsmul ℚ k] at h2
  exact MulAction.injective₀ hk' h2

private theorem congOne_conj {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {h u : G.GAf} {k N : ℕ}
    (hI : Integ L h) (hk : 0 < k) (hinv : ∀ v ∈ LaHat D, k • L.actG h⁻¹ v ∈ LaHat D) (hu : L.CongOne (N * k) u) :
    L.CongOne N (h * u * h⁻¹) := by
  intro v hv
  obtain ⟨w, hw, e⟩ := hu _ (hinv v hv)
  refine ⟨L.actG h w, hI w hw, ?_⟩
  have hhv : L.actG h (L.actG h⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have := conj_core (L.actG h).toAddMonoidHom (L.actG u).toAddMonoidHom (L.actG h⁻¹).toAddMonoidHom hk (v := v) (w := w) hhv e
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  exact this

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pAdmOf :
    AdmOf := by
  intro p _ D G L h k N hI hk hinv u hu
  refine ⟨congOne_conj L hI hk hinv hu.1, ?_⟩
  have e : (h * u * h⁻¹)⁻¹ = h * u⁻¹ * h⁻¹ := by group
  rw [e]
  exact congOne_conj L hI hk hinv hu.2
