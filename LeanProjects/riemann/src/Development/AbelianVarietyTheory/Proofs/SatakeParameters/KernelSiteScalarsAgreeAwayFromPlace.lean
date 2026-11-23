import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiAlgUnitInert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GidxFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetLatticeTuplesAgreeingAwayFromPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeDetIdealCharacterEqConstMulDetStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointsAgreeAwayOfLatticeTuplesAgreeAwayStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersCharOnNormOneIdelesMulUnramifiedClassValueStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReaderLevelBadPrimesCoprimeResidueCharStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePointDetNormOneOrderEqNegLengthStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc.AwayId

theorem key {K : Type} [Field K] {P M C : K} (hP : P ≠ 0) (hM : M ≠ 0) (hC : C ≠ 0) (V A A' n n' : ℤ) :
    P ^ (V * (n - n')) * (M ^ n' * (M ^ n)⁻¹ * (C ^ n) ^ (-A) * (C ^ n') ^ A') * (P ^ (-V) * (M * C ^ A)) ^ n *
      (P ^ V * (M⁻¹ * C ^ (-A'))) ^ n' = 1 := by
  simp only [mul_zpow, ← zpow_mul, inv_zpow', mul_sub, zpow_sub₀ hP, neg_mul, zpow_neg]
  rw [mul_comm A n, mul_comm A' n', mul_comm V n, mul_comm V n']
  field_simp

theorem map_zpow_of {G M : Type*} [Group G] [DivisionMonoid M] (f : G → M) (U : Subgroup G) (h1 : f 1 = 1)
    (hm : ∀ x ∈ U, ∀ y ∈ U, f (x * y) = f x * f y) {x : G} (hx : x ∈ U) (n : ℤ) : f (x ^ n) = f x ^ n := by
  let φ : U →* M := { toFun := fun y => f y, map_one' := h1, map_mul' := fun y z => hm _ y.2 _ z.2 }
  have := map_zpow φ ⟨x, hx⟩ n
  simpa [φ] using this

theorem lamC_mul' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  rw [lamC_eq_of_mem lam hx, lamC_eq_of_mem lam hy, lamC_eq_of_mem lam (mul_mem hx hy), ← map_mul]
  rfl

theorem lamC_zpow' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (n : ℤ) :
    TaylorLogMetric.lamC lam (x ^ n) = TaylorLogMetric.lamC lam x ^ n := by
  rw [lamC_eq_of_mem lam hx, lamC_eq_of_mem lam (zpow_mem hx n), ← map_zpow₀]
  rfl

theorem lamC_inv' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x⁻¹ = (TaylorLogMetric.lamC lam x)⁻¹ := by
  rw [lamC_eq_of_mem lam hx, lamC_eq_of_mem lam (inv_mem hx), ← map_inv₀]
  rfl

theorem lamC_ne_zero' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (h0 : x ≠ 0) :
    TaylorLogMetric.lamC lam x ≠ 0 := by
  rw [lamC_eq_of_mem lam hx]
  exact (map_ne_zero lam).2 fun h => h0 (congrArg Subtype.val h)

theorem final {K : Type} [Field K] {P M C Q s : K} (hP : P ≠ 0) (hM : M ≠ 0) (hC : C ≠ 0) (V A A' la la' n n' : ℤ) :
    Q * P ^ (V * (n - n')) * (s * (M ^ n' * (M ^ n)⁻¹ * (C ^ n) ^ (-A) * (C ^ n') ^ A')) *
        ((P ^ (-V) * (M * C ^ A)) ^ (la + n) * (P ^ V * (M⁻¹ * C ^ (-A'))) ^ (la' + n')) =
      Q * s * ((P ^ (-V) * (M * C ^ A)) ^ la * (P ^ V * (M⁻¹ * C ^ (-A'))) ^ la') := by
  have hXa : P ^ (-V) * (M * C ^ A) ≠ 0 := mul_ne_zero (zpow_ne_zero _ hP) (mul_ne_zero hM (zpow_ne_zero _ hC))
  have hXb : P ^ V * (M⁻¹ * C ^ (-A')) ≠ 0 := mul_ne_zero (zpow_ne_zero _ hP) (mul_ne_zero (inv_ne_zero hM) (zpow_ne_zero _ hC))
  have hk := key hP hM hC V A A' n n'
  rw [zpow_add₀ hXa, zpow_add₀ hXb]
  calc _ = Q * s * ((P ^ (-V) * (M * C ^ A)) ^ la * (P ^ V * (M⁻¹ * C ^ (-A'))) ^ la') *
        (P ^ (V * (n - n')) * (M ^ n' * (M ^ n)⁻¹ * (C ^ n) ^ (-A) * (C ^ n') ^ A') * (P ^ (-V) * (M * C ^ A)) ^ n *
          (P ^ V * (M⁻¹ * C ^ (-A'))) ^ n') := by ring
    _ = _ := by rw [hk, mul_one]

set_option maxHeartbeats 4000000 in

theorem scal_away : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pair → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, ∀ a b : (sysS H X std).G.Kf, S.E.iK a = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (-((sysS H X std).vm v (j + 1))) * TaylorLogMetric.lamC S.lam (S.muT (j + 1) π * chiI J π ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) → S.E.iK b = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1)) * TaylorLogMetric.lamC S.lam ((S.muT (j + 1) π)⁻¹ * chiI J π ^ (-((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)))) → ∀ (La Lb : (sysS H X std).Lt j) (La' Lb' : (sysS H X std).Lt (j + 1)), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' → GlobalTheory.TwU.pPow (sysS H X std) j La La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La') * S.E.iK (a ^ len (sysS H X std) v j Lb.2 * b ^ len (sysS H X std) v (j + 1) Lb'.2) = GlobalTheory.TwU.pPow (sysS H X std) j Lb Lb' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j Lb Lb') * S.E.iK (a ^ len (sysS H X std) v j La.2 * b ^ len (sysS H X std) v (j + 1) La'.2)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hSpl hP v π hπ j hj a b ha hb La Lb La' Lb' hab hab'
  have hR := GlobalTheory.TwV.DelB.sysS_ranks S
  have hjle : j ≤ D.R.m := hj.le
  have hj1 : j + 1 ≤ D.R.m := hj
  have hjm : j < (sysS H X std).mm := hR.1 ▸ hj
  have hPa := hP j hjm La La' hab.1 hab'.1
  have hPb := hP j hjm Lb Lb' hab.2.1 hab'.2.1
  obtain ⟨k, hkU, hkI, hkO, hk⟩ := GlobalTheory.T.det_latticeTuples_agreeing_away_from_place S hD hSpl v π hπ j hjle La Lb hab
  obtain ⟨k', hkU', hkI', hkO', hk'⟩ := GlobalTheory.T.det_latticeTuples_agreeing_away_from_place S hD hSpl v π hπ (j + 1) hj1 La' Lb' hab'
  obtain ⟨c0, hc0⟩ := GlobalTheory.T.kernelLattice_detIdeal_character_eq_const_mul_det S hD hSpl j hjle
  obtain ⟨c0', hc0'⟩ := GlobalTheory.T.kernelLattice_detIdeal_character_eq_const_mul_det S hD hSpl (j + 1) hj1
  obtain ⟨-, hsl⟩ := GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hSpl v j hjle La Lb hab
  obtain ⟨-, hsl'⟩ := GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hSpl v (j + 1) hj1 La' Lb' hab'
  obtain ⟨hχm, hχ1, -, hχN⟩ := GlobalTheory.T.charOnNormOneIdeles_mul_unramified_classValue S hD hSpl
  have hbad := (GlobalTheory.T.level_badPrimes_coprime_residueChar S hD hSpl).2.2.2
  have hdtb := (GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hSpl j hjle Lb hab.2.1).1
  have hdtb' := (GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hSpl (j + 1) hj1 Lb' hab'.2.1).1
  have law := S.law
  have hmuk : ∀ κ ∈ U1 (sigD D), κ ∈ intU D.host.F D.host.E → OneOff ((A0 J).pl v).1 κ → S.muT (j + 1) κ = 1 := by
    intro κ hκ hκI hκO
    refine law.mu_unr j hj κ hκ hκI fun v' hv' => hκO v' fun h => hbad v' hv' ?_
    rw [h]
    exact ((A0 J).pl v).2

  have hmuF : ∀ x ∈ U1 (sigD D), ∀ (e : ℤ) (κ : (AfE D.host.F D.host.E)ˣ), κ ∈ U1 (sigD D) → S.muT (j + 1) κ = 1 →
      S.muT (j + 1) (x * π ^ e * κ) = S.muT (j + 1) x * S.muT (j + 1) π ^ e := by
    intro x hx e κ hκ h1
    have hpe : π ^ e ∈ U1 (sigD D) := zpow_mem hπ.1 e
    rw [(law.mu_mul j hj).2 _ (mul_mem hx hpe) _ hκ, h1, mul_one, (law.mu_mul j hj).2 _ hx _ hpe,
      map_zpow_of (S.muT (j + 1)) (U1 (sigD D)) (law.mu_mul j hj).1 (law.mu_mul j hj).2 hπ.1 e]
  have hchi1 : chiI J 1 = 1 := hχ1 1 (one_mem _) (one_mem _)
  have hchF : ∀ x ∈ U1 (sigD D), ∀ (e : ℤ) (κ : (AfE D.host.F D.host.E)ˣ), κ ∈ U1 (sigD D) → κ ∈ intU D.host.F D.host.E →
      chiI J (x * π ^ e * κ) = chiI J x * chiI J π ^ e := by
    intro x hx e κ hκ hκI
    have hpe : π ^ e ∈ U1 (sigD D) := zpow_mem hπ.1 e
    rw [hχm _ (mul_mem hx hpe) _ hκ, hχ1 κ hκ hκI, mul_one, hχm _ hx _ hpe, map_zpow_of (chiI J) (U1 (sigD D)) hchi1 hχm hπ.1 e]
  have hscal : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La' =
      GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j Lb Lb' *
        (S.muT (j + 1) π ^ (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2) *
          (S.muT (j + 1) π ^ (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2))⁻¹ *
          (chiI J π ^ (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2)) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) *
          (chiI J π ^ (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2)) ^ ((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) := by
    unfold GlobalTheory.TwU.scal0
    rw [hc0 La hab.1 hPa.1.2.2.1, hc0 Lb hab.2.1 hPb.1.2.2.1, hc0' La' hab'.1 hPa.1.2.2.2, hc0' Lb' hab'.2.1 hPb.1.2.2.2, hk, hk',
      hmuF _ hdtb _ k hkU (hmuk k hkU hkI hkO), hmuF _ hdtb' _ k' hkU' (hmuk k' hkU' hkI' hkO'),
      hchF _ hdtb _ k hkU hkI, hchF _ hdtb' _ k' hkU' hkI']
    simp only [mul_zpow, mul_inv]
    ring

  have hp0 : ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ≠ 0 :=
    Nat.cast_ne_zero.2 (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero
  have hpp : GlobalTheory.TwU.pPow (sysS H X std) j La La' = GlobalTheory.TwU.pPow (sysS H X std) j Lb Lb' *
      ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1) *
        ((len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2) -
          (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2))) := by
    unfold GlobalTheory.TwU.pPow
    rw [← zpow_add₀ hp0]
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    have he : ∀ v' ∈ Finset.univ.erase v, (sysS H X std).vm v' (j + 1) * (len (sysS H X std) v' (j + 1) La'.2 - len (sysS H X std) v' j La.2) =
        (sysS H X std).vm v' (j + 1) * (len (sysS H X std) v' (j + 1) Lb'.2 - len (sysS H X std) v' j Lb.2) := by
      intro v' hv'
      rw [hsl v' (Finset.ne_of_mem_erase hv'), hsl' v' (Finset.ne_of_mem_erase hv')]
    rw [Finset.sum_congr rfl he]
    ring

  have hm_alg : S.muT (j + 1) π ∈ TaylorLogMetric.Qbar := law.mu_alg j hj π hπ.1
  have hm_ne : S.muT (j + 1) π ≠ 0 := law.mu_ne hj hπ.1
  obtain ⟨𝔞, hN1, hc𝔞⟩ := hχN π hπ.1
  have hgx := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  have hcu := GlobalTheory.TwV.Xc.chi_alg_unit_inert D _ S.lam t.χ t.χ_ok (by omega) hgx.2.1 𝔞 hN1
  have hc_alg : chiI J π ∈ TaylorLogMetric.Qbar := hc𝔞 ▸ hcu.1
  have hc_ne : chiI J π ≠ 0 := hc𝔞 ▸ hcu.2.1
  have hsb : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j Lb Lb' ∈ TaylorLogMetric.Qbar := hPb.2.2.2.2.1
  have hLm := lamC_ne_zero' S.lam hm_alg hm_ne
  have hLc := lamC_ne_zero' S.lam hc_alg hc_ne
  have hma := fun (e : ℤ) => zpow_mem hm_alg e
  have hca := fun (e : ℤ) => zpow_mem hc_alg e
  rw [lamC_mul' S.lam hm_alg (hca _), lamC_zpow' S.lam hc_alg] at ha
  rw [lamC_mul' S.lam (inv_mem hm_alg) (hca _), lamC_inv' S.lam hm_alg, lamC_zpow' S.lam hc_alg] at hb
  rw [hpp, hscal, lamC_mul' S.lam hsb (mul_mem (mul_mem (mul_mem (hma _) (inv_mem (hma _))) (zpow_mem (hca _) _)) (zpow_mem (hca _) _)),
    lamC_mul' S.lam (mul_mem (mul_mem (hma _) (inv_mem (hma _))) (zpow_mem (hca _) _)) (zpow_mem (hca _) _),
    lamC_mul' S.lam (mul_mem (hma _) (inv_mem (hma _))) (zpow_mem (hca _) _),
    lamC_mul' S.lam (hma _) (inv_mem (hma _)), lamC_inv' S.lam (hma _),
    lamC_zpow' S.lam (hca _), lamC_zpow' S.lam (hca _), lamC_zpow' S.lam hm_alg, lamC_zpow' S.lam hm_alg,
    lamC_zpow' S.lam hc_alg, lamC_zpow' S.lam hc_alg,
    map_mul, map_mul, map_zpow₀, map_zpow₀, map_zpow₀, map_zpow₀, ha, hb]
  have e1 : len (sysS H X std) v j Lb.2 = len (sysS H X std) v j La.2 + (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2) := by ring
  have e2 : len (sysS H X std) v (j + 1) Lb'.2 = len (sysS H X std) v (j + 1) La'.2 +
      (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2) := by ring
  generalize len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2 = n at e1 ⊢
  generalize len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2 = n' at e2 ⊢
  rw [e1, e2]
  exact final hp0 hLm hLc _ _ _ _ _ _ _
end GlobalTheory.TwV.Xc.AwayId

end
