import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCongr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal GlobalTheory.ConjPeriod
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ConjPeriod

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

abbrev plusR (l : ℕ) [Fact l.Prime] : Subring (Per.BdR l) := (algebraMap (Per.BdRp l) (Per.BdR l)).range

theorem eD_uj_mem (T : LocTied l P AI) (j : ℕ) (a : Per.Acris l) : T.eD (uj T j a) ∈ plusR l := by
  obtain ⟨i, hi, -⟩ := GlobalTheory.CrisIncl.exists_restrict l _ T.incl
  exact ⟨_, (hi ((GlobalTheory.MemLoc.phiA l ^ j) a)).symm⟩

theorem eD_om_mem (T : LocTied l P AI) (x : Om l) : T.eD (algebraMap (Om l) P.R.BdR x) ∈ plusR l := by
  obtain ⟨y, hy, -⟩ := T.om x
  exact ⟨y, hy.symm⟩

theorem l_inv_mem (l : ℕ) [Fact l.Prime] : ∃ u ∈ plusR l, (l : Per.BdR l) * u = 1 := by
  obtain ⟨v, hv⟩ := (GlobalTheory.RingBasics.isUnit_l l).exists_right_inv
  refine ⟨algebraMap (Per.BdRp l) (Per.BdR l) (algebraMap (Per.AinfP l) (Per.BdRp l) v), ⟨_, rfl⟩, ?_⟩
  have h := congrArg ((algebraMap (Per.BdRp l) (Per.BdR l)).comp (algebraMap (Per.AinfP l) (Per.BdRp l))) hv
  rwa [map_mul, map_natCast, map_one] at h

theorem conj_mem_Fil_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (j : ℕ) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) (h : Compat T K j s) (b : BK K),
    conj T K j s h b ∈ (P.PD K).Fil 0 := by
  intro l _ P AI T K j s h b
  let f : BK K →+* Per.BdR l := T.eD.toRingHom.comp (conj T K j s h)
  have hz : ∀ z : CK K, f (toB K z) ∈ plusR l := fun z => by
    induction z using GlobalTheory.AcrisK.induction_on with
    | mul a c =>
      rw [map_mul, map_mul]
      refine mul_mem ?_ ?_
      · exact eD_uj_mem T j a |> fun h' => by
          simpa only [f, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, conj_inC] using h'
      · rw [← inK_oK]
        simpa only [f, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, conj_inK] using
          eD_om_mem T (s (oK K c))
    | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
  obtain ⟨D, z, hD⟩ := exists_pow_mul b
  obtain ⟨u, hu, hlu⟩ := l_inv_mem l
  have e : f b = u ^ D * f (toB K z) := by
    rw [← hD, map_mul, map_pow, map_natCast, ← mul_assoc, ← mul_pow, mul_comm u, hlu, one_pow, one_mul]
  have hm : f b ∈ plusR l := e ▸ mul_mem (pow_mem hu D) (hz z)
  obtain ⟨y, hy⟩ := hm
  rw [T.fil]
  change f b ∈ Per.FilD l 0
  rw [← hy]
  exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero y

end GlobalTheory.ConjPeriod

end
