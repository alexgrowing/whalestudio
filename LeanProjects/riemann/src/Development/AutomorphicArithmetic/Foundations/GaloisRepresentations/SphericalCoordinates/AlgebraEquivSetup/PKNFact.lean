import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem cong_conj_iff (hG : CongGrpEx) {E : Type} [Field E] [NumberField E] [IsCMField E] (n N : ℕ) (hN : 0 < N)
    (u : Plc E) (a : GLw n u) (ha : a ∈ GlobalTheory.LFun.KGL u n) (y : GLw n u) :
    (Cong1 N u (a * y * a⁻¹) ∧ Cong1 N u (a * y * a⁻¹)⁻¹) ↔ Cong1 N u y ∧ Cong1 N u y⁻¹ := by
  obtain ⟨K, hc, -, -, -, hn, -, -⟩ := hG E n N hN u
  rw [← hc, ← hc]
  exact hn a ha y

private theorem principalCongruence_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (N : ℕ) (u : Plc E) :
    Cong1 N u (1 : GLw n u) := by
  intro i k
  simp

theorem UpperTheory.Gal.W2.Seed.pKNFact :
    KNIff → FacEq → AtApart → CongGrpEx → CongConj → UpperTheory.Gal.W2.Seed.LocComm → UpperTheory.Gal.CertificateRingHomMap.LocComm → KNFact := by
  intro hK _ _ hG hC _ hL E _ _ _ A n p _ S F w L hF q hq hgood hqw N hN K hKc
  have e : ∀ (u : Plc E) (g : GUf E n), GeneralLinearGroup.map (pLoc E u) (F.tr.a * mat g * F.tr.a⁻¹) =
      F.a u * comp u g * (F.a u)⁻¹ := by
    intro u g
    rw [F.a_tr]
    simp only [map_mul, map_inv]
    rfl
  have hCong : ∀ g : GUf E n, S.L.CongOne N (F.j g) ↔ ∀ u : Plc E, (p : 𝓞 E) ∉ u.asIdeal →
      Cong1 N u (F.a u * comp u g * (F.a u)⁻¹) := by
    intro g
    rw [F.j_tr, ((hK E A n p S F.tr g).2 N hN)]
    simp only [e]
  have einv : ∀ (u : Plc E) (g : GUf E n), F.a u * comp u g⁻¹ * (F.a u)⁻¹ = (F.a u * comp u g * (F.a u)⁻¹)⁻¹ := by
    intro u g
    rw [map_inv]
    group
  have hw := (hL E n w.1 w.2.1)
  have hcs : IsSplitAt (CertificateRingHomMap.cj w.1) := hw.2.2.2.1
  have hqc : (q : 𝓞 E) ∈ (CertificateRingHomMap.cj w.1).asIdeal := by
    by_contra hc
    haveI : Fact q.Prime := ⟨hq⟩
    have h1 : GlobalTheory.Cong.Apart w.1 (CertificateRingHomMap.cj w.1) := apart_of_not_mem (p := q) hc hqw
    exact (((hL E n (CertificateRingHomMap.cj w.1) hcs).2.1 w.1).1 h1).2 hw.2.2.2.2.1.symm
  have hcw := F.a_int w.1 q hq hgood hqw
  have hcc := F.a_int _ q hq hgood hqc
  have main : ∀ y : GLw n w.1, Cong1 N w.1 y → Cong1 N w.1 y⁻¹ → S.L.CongOne N (L.loc y) := by
    intro y h1 h2
    rw [hF.2, hCong]
    intro u _
    by_cases huw : u = w.1
    · subst huw
      rw [CertificateRingHomMap.comp_loc]
      exact ((cong_conj_iff hG n N hN _ _ hcw y).2 ⟨h1, h2⟩).1
    by_cases huc : u = CertificateRingHomMap.cj w.1
    · subst huc
      have c1 : Cong1 N (CertificateRingHomMap.cj w.1) (comp (CertificateRingHomMap.cj w.1) (CertificateRingHomMap.loc w.2.1 y)) :=
        hC E n N w.1 _ (CertificateRingHomMap.sim_loc _ _) (by rwa [CertificateRingHomMap.comp_loc])
      have c2 : Cong1 N (CertificateRingHomMap.cj w.1) (comp (CertificateRingHomMap.cj w.1) (CertificateRingHomMap.loc w.2.1 y))⁻¹ := by
        rw [← map_inv]
        exact hC E n N w.1 _ (by rw [map_inv, CertificateRingHomMap.sim_loc, inv_one]) (by rwa [map_inv, CertificateRingHomMap.comp_loc, inv_inv])
      exact ((cong_conj_iff hG n N hN _ _ hcc _).2 ⟨c1, c2⟩).1
    · rw [CertificateRingHomMap.comp_loc_of_apart w.2.1 (((hw.2.1 u).2 ⟨huw, huc⟩)) y]
      simpa using principalCongruence_one N u
  refine ⟨fun y hy => ?_, fun k hk => ?_⟩
  · obtain ⟨h1, h2⟩ := (hKc y).1 hy
    refine ⟨main y h1 h2, ?_⟩
    rw [← map_inv]
    exact main y⁻¹ h2 (by rwa [inv_inv])
  · obtain ⟨g, rfl⟩ := F.surj k
    rw [hF.1, hKc]
    have h1 := (hCong g).1 hk.1 w.1 w.2.2
    have h2 := (hCong g⁻¹).1 (by rw [map_inv]; exact hk.2) w.1 w.2.2
    rw [einv] at h2
    exact (cong_conj_iff hG n N hN _ _ hcw _).1 ⟨h1, h2⟩
