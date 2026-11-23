import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmulStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem ev_eq {Λ Q : Type} [AddCommGroup Λ] [Group Q] (E : ℕ → Λ → Q)
    (add : ∀ n x y, E n (x + y) = E n x * E n y) (ker : ∀ n, 0 < n → ∀ x, E n x = 1 ↔ ∃ y, x = n • y)
    (tower : ∀ n m, 0 < n → 0 < m → ∀ x, E (n * m) x ^ m = E n x) {κ m N : ℕ} (hN : N = κ * m) (hκ : 0 < κ)
    (hm : 0 < m) {a b c : Λ} (h : a = b + κ • c) : E κ a = E N (m • b) := by
  have hz : ∀ n, E n 0 = 1 := by
    intro n
    have h0 := add n 0 0
    rw [_root_.add_zero] at h0
    exact (_root_.mul_eq_left.mp h0.symm)
  have hpow : ∀ n (k : ℕ) x, E n (k • x) = E n x ^ k := by
    intro n k x
    induction k with
    | zero => simp [hz]
    | succ k ih => rw [succ_nsmul, add, ih, _root_.pow_succ]
  have hc : E κ (κ • c) = 1 := (ker κ hκ _).mpr ⟨c, rfl⟩
  rw [h, add, hc, _root_.mul_one, hN, hpow, tower κ m hκ hm]

theorem UpperTheory.Gal.FiniteEtaleModels.trKer_holds :
    TrKer := by
  intro p _ D G L R _ _ gb h X s M₁ M₂ o' o ψ hT n κ c₁ hM hsurj f hf Ω _ _ z g hg hgk
  obtain ⟨hM3, hMc⟩ := M₁.2
  have hne : (M₁ : ℕ) ≠ 0 := by omega
  rw [hM] at hne hMc
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  have hκ0 : 0 < κ := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  have hc0 : 0 < c₁ := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  have hκc : κ.Coprime p := Nat.Coprime.coprime_dvd_left ⟨n * c₁, by ring⟩ hMc
  have hnκc : (n * κ).Coprime p := Nat.Coprime.coprime_dvd_left ⟨c₁, rfl⟩ hMc
  obtain ⟨β, hβ⟩ := GlobalTheory.UPel.HT.GenCmp.exists_spMap (z ≫ s)
  obtain ⟨I', I'', h1, h2, hev⟩ := hT.2.2.2.2 Ω z β hβ
  obtain ⟨a, ha⟩ := (I'.onto κ hκ0 g).mp hgk
  have h0 : I''.ev κ 0 = 1 := (I''.ker κ hκ0 0).mpr ⟨0, by simp⟩
  have hψ : I'.ev κ a ≫ ψ = I''.ev κ 0 := by rw [ha, hg, h0]
  obtain ⟨v, hv, hav⟩ := (hev κ hκ0 hκc a 0).mp hψ
  have hin0 : inAf D 0 = 0 := by
    have := GlobalTheory.HeckeApprox.inAf_sub D 0 0
    rw [_root_.sub_zero, _root_.sub_self] at this
    exact this
  rw [hin0, _root_.zero_add] at hav
  have hinv : ∀ y, L.actG h⁻¹ (L.actG h y) = y := by
    intro y
    rw [← Module.End.mul_apply, ← map_mul, _root_.inv_mul_cancel, map_one, Module.End.one_apply]
  obtain ⟨x, w, hw, hvx⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D (n * κ) (Nat.mul_pos hn0 hκ0) hnκc v hv
  obtain ⟨w', hw', hfx⟩ := hf x
  obtain ⟨w'', hw'', hw''e⟩ := hsurj w hw
  have e2 : κ • L.actG h⁻¹ w = w'' := by rw [← map_nsmul, ← hw''e, hinv]
  have key : inAf D ((show D.La from a) - f x) = κ • (n • (w' + w'')) := by
    have e1 : inAf D a = L.actG h⁻¹ (κ • v) := by rw [← hav, hinv]
    rw [GlobalTheory.HeckeApprox.inAf_sub, e1, hvx, map_nsmul, map_add, map_nsmul, _root_.smul_add, hfx,
      smul_comm κ (n * κ), e2, smul_smul κ n, mul_comm κ n, _root_.smul_add]
    abel
  have hmem : n • (w' + w'') ∈ LaHat D := AddSubgroup.nsmul_mem _ (AddSubgroup.add_mem _ hw' hw'') n
  obtain ⟨y, hy⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ κ hκ0 hκc _ hmem key
  have hay : (show D.La from a) = f x + κ • y := by rw [← hy]; abel
  refine ⟨x, ?_⟩
  calc g = I'.ev κ a := ha.symm
    _ = I'.ev (M₁ : ℕ) ((n * c₁) • f x) :=
        ev_eq I'.ev I'.add I'.ker I'.tower (by rw [hM]; ring) hκ0 (Nat.mul_pos hn0 hc0) hay
    _ = I'.ev (M₁ : ℕ) (c₁ • n • f x) := by rw [smul_smul, mul_comm n c₁]
    _ = _ := (h1 _).symm
