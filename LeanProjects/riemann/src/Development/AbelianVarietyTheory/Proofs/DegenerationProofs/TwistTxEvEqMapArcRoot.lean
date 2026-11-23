import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxEvEqMapArcStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex.RootSum

def scaleForm {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) : N.Form n where
  be := (n : ℤ) • β.be
  symm y z := congrArg ((n : ℤ) * ·) (β.symm y z)
  pos y hy := mul_pos (Int.natCast_pos.2 hn) (β.pos y hy)
  dvd y z := by
    obtain ⟨a, ha⟩ := β.dvd y z
    exact ⟨k * a, by change (n : ℤ) * β.be y z = _; rw [ha]; ring⟩

def pullForm {O O' : Type} [CommRing O] [CommRing O'] {N₀ : NumD O} {N : NumD O'} {k : ℕ} (β : N.Form k)
    (e : N₀.X ≃+ N.X) (be₀ : LinearMap.BilinForm ℤ N₀.X) (h : ∀ y z, β.be (e y) (e z) = be₀ y z) : N₀.Form k where
  be := be₀
  symm y z := by rw [← h, ← h, β.symm]
  pos y hy := by rw [← h]; exact β.pos _ (fun h0 => hy (e.map_eq_zero_iff.1 h0))
  dvd y z := h y z ▸ β.dvd _ _

def idHom {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) (t u : Oˣ)
    (h : t ^ n = u) : NumD.Hom (RingHom.id O) (N.twist (scaleForm β n hn) t) (N.twist β u) where
  φ := MonoidHom.id _
  h _ := 1
  h_one := rfl
  θ_eq _ _ _ := by simp only [mul_one]; rfl
  σ_eq _ := by simp only [mul_one]; rfl
  lam := 1
  th_eq _ := by simp only [mul_one, Units.val_one, one_mul]; rfl
  e := AddEquiv.refl N.X
  c_eq _ := rfl
  ψ_eq (χ : N.X) := by
    rw [mul_one]
    change N.ψ χ * u ^ (β.be χ χ / 2) = N.ψ χ * t ^ ((n : ℤ) * β.be χ χ / 2)
    rw [Int.mul_ediv_assoc _ ((Dvd.intro _ rfl : (2 : ℤ) ∣ 2 * k).trans (β.dvd χ χ)), zpow_mul, zpow_natCast, h]

theorem idHom_rel {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) (t u r : Oˣ)
    (h : t ^ n = u) {i : ℕ} (a : ℕ) (hi : i * a = n) (hd : i ∣ n) (hr : t ^ a = r) (p₁ : N.QT i)
    (p : (N.twist β u).QT i) (hp : TwRel β u r p₁ p) :
    p.1.1.toAdd = (idHom β n hn t u h).e (N.twQ (scaleForm β n hn) t hd p₁).1.1.toAdd ∧
      (idHom β n hn t u h).Rel (N.twQ (scaleForm β n hn) t hd p₁).1.2 p.1.2 := by
  refine ⟨congrArg Multiplicative.toAdd hp.1, hp.2.1, fun (χ : N.X) => ?_⟩
  change p.1.2.s χ * 1 = p₁.1.2.s χ * t ^ ((n : ℤ) * β.be p₁.1.1.toAdd χ / i) * 1 * 1
  have hi0 : (i : ℤ) ≠ 0 := by
    rintro h0
    rw [Int.natCast_eq_zero.1 h0, zero_mul] at hi
    omega
  rw [hp.2.2, ← hi, Nat.cast_mul, mul_assoc (i : ℤ), Int.mul_ediv_cancel_left _ hi0, zpow_mul, zpow_natCast, hr,
    mul_one, mul_one]

theorem twist_tx_ev_eq_map_arc_root : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (t u rm rj : Cˣ) (m j : ℕ), Odd m → 0 < j → (t : C) = φ PowerSeries.X → t ^ j = rm → t ^ (m ^ 2) = rj → rm ^ (m ^ 2) = u → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (be₀ : LinearMap.BilinForm ℤ N₀.X) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = be₀ y z) → ∀ (p₀ : N₀.QT (m ^ 2)) (p₁ : N.QT (m ^ 2)) (p : (N.twist β u).QT (m ^ 2)), p₁.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p₁.1.2 → TwRel β u rm p₁ p → (N.twist β u).tx m p = I.lam * φ (N₀.arcTx (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀) ∧ ∀ (q₀ : N₀.QT j) (q₁ : N.QT j) (q : (N.twist β u).QT j), q₁.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q₁.1.2 → TwRel β u rj q₁ q → ∀ s : ℕ, (m : ℤ) ^ 2 * (((m ^ 2 * j : ℕ) : ℤ) * be₀ q₀.1.1.toAdd q₀.1.1.toAdd) ≤ s → (t : C) ^ s * (N.twist β u).ev m p q.1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀ q₀ s) := by
  intro O C _ _ _ _ φ h1 h2 t u rm rj m j hm hj ht hrm hrj hu N₀ N I k be₀ β hβ p₀ p₁ p hp1 hp2 hp
  have hn : 0 < m ^ 2 * j := Nat.mul_pos (pow_pos hm.pos 2) hj
  have htu : t ^ (m ^ 2 * j) = u := by rw [mul_comm, pow_mul, hrm, hu]
  have hd : m ^ 2 ∣ m ^ 2 * j := Dvd.intro _ rfl
  have key := GlobalTheory.T.twist_tx_ev_eq_map_arc_alt O C φ h1 h2 t ht N₀ N I (m ^ 2 * j) (scaleForm (pullForm β I.e be₀ hβ) _ hn)
    (scaleForm β _ hn) (fun y z => congrArg (((m ^ 2 * j : ℕ) : ℤ) * ·) (hβ y z)) m hd hm p₀ p₁ hp1 hp2
  have hr := idHom_rel β _ hn t u rm htu j rfl hd hrm p₁ p hp
  have tr := (NumD.hom_transport C C _ _ _ (idHom β _ hn t u htu)).2.2.2.2 m hm _ p hr.1 hr.2
  refine ⟨Eq.trans (tsum_congr fun χ => ?_) key.1, fun q₀ q₁ q hq1 hq2 hq s hs => ?_⟩
  · exact (tr χ).1.trans (one_mul _)
  · have hd' : j ∣ m ^ 2 * j := Dvd.intro_left _ rfl
    have hr' := idHom_rel β _ hn t u rj htu (m ^ 2) (mul_comm _ _) hd' hrj q₁ q hq
    refine Eq.trans (congrArg _ (tsum_congr fun χ => ?_)) (key.2 j hd' q₀ q₁ hj.ne' hq1 hq2 s hs)
    refine ((tr χ).2 _ _ hr'.2).trans ?_
    change ((1 * 1 ^ (m ^ 2) : Cˣ) : C) * _ = _
    rw [one_pow, mul_one, Units.val_one, one_mul]
    rfl

end GlobalTheory.Ex.RootSum
end
