import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem nsmul_cancel' {V : Type} [AddCommGroup V] [Module ℚ V] {c : ℕ} (hc : c ≠ 0) {a b : V}
    (h : c • a = c • b) : a = b := by
  have h' : (c : ℚ) • a = (c : ℚ) • b := by
    rw [Nat.cast_smul_eq_nsmul ℚ, Nat.cast_smul_eq_nsmul ℚ]
    exact h
  exact smul_right_injective V (Nat.cast_ne_zero.mpr hc) h'

private theorem rel_core {p : ℕ} [Fact p.Prime] {D : Datum p} (F : D.La →+ AfP p ⊗[ℚ] VQ D)
    (hFmem : ∀ z, F z ∈ LaHat D) {Q Q' : Type} [Group Q] [Group Q'] (Φ : Q →* Q')
    (eI : ℕ → D.La → Q) (eJ : ℕ → D.La → Q')
    (addI : ∀ n a b, eI n (a + b) = eI n a * eI n b) (addJ : ∀ n a b, eJ n (a + b) = eJ n a * eJ n b)
    (kerI : ∀ n, 0 < n → ∀ x, eI n x = 1 ↔ ∃ y, x = n • y)
    (kerJ : ∀ n, 0 < n → ∀ x, eJ n x = 1 ↔ ∃ y, x = n • y)
    (towerI : ∀ n m, 0 < n → 0 < m → ∀ x, eI (n * m) x ^ m = eI n x)
    (f : ℕ → D.La →+ D.La) (k : ℕ) (hk0 : 0 < k) (hk : k.Coprime p)
    (honto : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, f n y = k • x + n • z)
    (hrel : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, F (f n x) = k • inAf D x + n • w)
    (hev : ∀ n, 0 < n → n.Coprime p → ∀ x, eJ n x = Φ (eI (n * k) (f (n * k) x)))
    (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (x y : D.La) :
    Φ (eI n x) = eJ n y ↔ ∃ v ∈ LaHat D, F x = inAf D y + n • v := by
  have hpowI : ∀ N, 0 < N → ∀ (m : ℕ) a, eI N (m • a) = eI N a ^ m := by
    intro N hN m a
    induction m with
    | zero =>
      rw [zero_nsmul, pow_zero]
      exact (kerI N hN 0).mpr ⟨0, by simp⟩
    | succ m ih => rw [succ_nsmul, addI, ih, pow_succ]
  have hinAf : ∀ a : D.La, inAf D (n • a) = n • inAf D a := fun a =>
    map_nsmul (GlobalTheory.HeckeApprox.inAfH D) n a
  have hNpos : 0 < n * k := Nat.mul_pos hn hk0
  have hNp : (n * k).Coprime p := Nat.Coprime.mul hnp hk
  obtain ⟨y', z, hy'⟩ := honto (n * k) hNpos hNp x
  have hL : Φ (eI n x) = eJ n y' := by
    rw [← towerI n k hn hk0 x, hev n hn hnp y', hy', addI, (kerI (n * k) hNpos ((n * k) • z)).mpr ⟨z, rfl⟩,
      _root_.mul_one, hpowI (n * k) hNpos]
  obtain ⟨v0, hv0, hv0eq⟩ : ∃ v0 ∈ LaHat D, F x = inAf D y' + n • v0 := by
    obtain ⟨w, hw, hFw⟩ := hrel (n * k) hNpos hNp y'
    rw [hy', map_add, map_nsmul, map_nsmul] at hFw
    refine ⟨w - F z, (LaHat D).sub_mem hw (hFmem z), ?_⟩
    apply nsmul_cancel' (c := k) (Nat.pos_iff_ne_zero.mp hk0)
    have e : k • F x = k • inAf D y' + (n * k) • w - (n * k) • F z := by
      rw [← hFw]
      abel
    rw [e, smul_add, smul_smul, mul_comm k n, smul_sub, add_sub_assoc]
  have hdiff : eJ n y' = eJ n y ↔ eJ n (y' - y) = 1 := by
    have hsplit : eJ n y' = eJ n (y' - y) * eJ n y := by rw [← addJ, sub_add_cancel]
    constructor
    · intro h
      rw [hsplit] at h
      exact mul_right_cancel (h.trans (_root_.one_mul _).symm)
    · intro h
      rw [hsplit, h, _root_.one_mul]
  rw [hL, hdiff, kerJ n hn (y' - y)]
  constructor
  · rintro ⟨z', hz'⟩
    refine ⟨v0 + inAf D z', (LaHat D).add_mem hv0 (GlobalTheory.HeckeApprox.inAf_mem D z'), ?_⟩
    have h1 : inAf D y' - inAf D y = n • inAf D z' := by
      rw [← GlobalTheory.HeckeApprox.inAf_sub, hz', hinAf]
    rw [hv0eq, smul_add, ← h1]
    abel
  · rintro ⟨v, hv, hFv⟩
    apply GlobalTheory.LKGeo.LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (y' - y) n hn hnp (v - v0) ((LaHat D).sub_mem hv hv0)
    have h2 := hv0eq.symm.trans hFv
    rw [GlobalTheory.HeckeApprox.inAf_sub, smul_sub, sub_eq_sub_iff_add_eq_add, h2, add_comm]

theorem UpperTheory.Gal.G3.pRelArith :
    RelArith := by
  unfold UpperTheory.Gal.G3.RelArith UpperTheory.Gal.G3.Rel
  intro p _ D G L R _ _ gb S s N N' o' o K _ t I J ψ h f u c k hψ hint hsys hrel hev n hn hnp x y
  haveI := hψ
  have hk : k.Coprime p := hsys.2.1
  have hk0 : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hk0
    rw [hk0, Nat.coprime_zero_left] at hk
    exact (Fact.out : p.Prime).one_lt.ne' hk
  let Φ : (Over.mk t ⟶ o'.A) →* (Over.mk t ⟶ o.A) :=
    MonoidHom.mk' (fun g => g ≫ ψ) (fun a b => MonObj.mul_comp a b ψ)
  exact rel_core ((L.actG h).toAddMonoidHom.comp (GlobalTheory.HeckeApprox.inAfH D))
    (fun z => hint _ (GlobalTheory.HeckeApprox.inAf_mem D z)) Φ I.ev J.ev I.add J.add I.ker J.ker I.tower f k hk0 hk
    hsys.2.2.2.2.2.2 hrel hev n hn hnp x y
