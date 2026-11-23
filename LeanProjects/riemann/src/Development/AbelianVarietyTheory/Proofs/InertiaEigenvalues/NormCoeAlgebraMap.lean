import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbOfFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGamGamKTorsion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocPrimeVNormalised
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.GroupLayer

variable {l : ℕ} [Fact l.Prime]

theorem v_le_iff (P : LocPrime l) (LL : FinExt l) (x y : ↥LL.1) :
    P.v LL y ≤ P.v LL x ↔ ‖(x : Om l)‖ ≤ ‖(y : Om l)‖ := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.HWL.NormVal.locPrime_v_normalised l P LL
  by_cases hy : y = 0
  · subst hy
    simp only [AddValuation.map_zero, top_le_iff, AddValuation.top_iff, ZeroMemClass.coe_zero,
      norm_zero, norm_le_zero_iff, ZeroMemClass.coe_eq_zero]
  · have hne : P.v LL y ≠ ⊤ := fun h => hy ((AddValuation.top_iff _).1 h)
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← hq, h2, (h1 y q).1 hq.symm]

theorem norm_coe_algebraMap (LL : FinExt l) (a : ℤ_[l]) :
    ‖((algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) a) : ↥LL.1) : Om l)‖ = ‖a‖ := by
  change ‖algebraMap ℚ_[l] (Om l) (a : ℚ_[l])‖ = ‖(a : ℚ_[l])‖
  simp

theorem norm_pow_sub_one (LL : FinExt l) (a : ℤ_[l]) (k : ℕ) :
    ‖((algebraMap ↥(OL LL) ↥LL.1 ((algebraMap ℤ_[l] ↥(OL LL) a) ^ k) - 1 : ↥LL.1) : Om l)‖
      = ‖a ^ k - 1‖ := by
  rw [← norm_coe_algebraMap LL (a ^ k - 1), map_sub, map_sub, map_one, map_one, map_pow (algebraMap ℤ_[l] ↥(OL LL))]

theorem norm_sub_one (LL : FinExt l) (a : ℤ_[l]) :
    ‖((algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) a) - 1 : ↥LL.1) : Om l)‖
      = ‖a - 1‖ := by
  simpa only [pow_one] using norm_pow_sub_one LL a 1

noncomputable def congSub (l : ℕ) [Fact l.Prime] (s : ℕ) : Subgroup ℤ_[l]ˣ :=
  (Units.map (Ideal.Quotient.mk (Ideal.span {(l : ℤ_[l]) ^ s})).toMonoidHom).ker

theorem mem_congSub (s : ℕ) (u : ℤ_[l]ˣ) :
    u ∈ congSub l s ↔ ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← Ideal.Quotient.eq, congSub, MonoidHom.mem_ker,
    Units.ext_iff]
  simp

theorem nonempty_gamS : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l),
    Good K s LL → Nonempty (GamS P K s LL) := by
  intro l _ P K s LL hG
  obtain ⟨emb, hbij, hσ⟩ := GlobalTheory.HWL.exists_letters l P K s LL hG
  obtain ⟨hs1, hs2, hKs, -⟩ := hG
  obtain ⟨χ, hχ, -, honto⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  obtain ⟨one, hone1, hone2⟩ := GlobalTheory.HWL.exists_unitLat l K LL
  obtain ⟨h1, h2, -⟩ := GlobalTheory.HWL.NormVal.locPrime_v_normalised l P LL
  let χK : ↥(GK K) →* ℤ_[l]ˣ := χ.comp (GK K).subtype
  obtain ⟨gam, gamK, D, hgam, hD, hK, hKeq, hK1⟩ := GlobalTheory.PadicUnitSub.exists_gam_gamK_torsion l s χK.range hs1 hs2 (fun u hu => by
    obtain ⟨g, hg, hgu⟩ := honto K s hKs u hu
    exact ⟨⟨g, hg⟩, hgu⟩)
  let χΓ : ↥χK.range →* (↥(OL LL))ˣ :=
    (Units.map (algebraMap ℤ_[l] ↥(OL LL)).toMonoidHom).comp χK.range.subtype
  have hχΓ : ∀ g : ↥χK.range, (χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) ((g : ℤ_[l]ˣ) : ℤ_[l]) :=
    fun _ => rfl
  have hres : ∀ g : ↥(GK K), algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g : ℚ_[l]) =
      algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) ((χK g : ℤ_[l]ˣ) : ℤ_[l])) := fun g => by
    rw [P.PD_χ, ← hχ]; rfl
  have hs : ((s : ℚ) : WithTop ℚ) = (s : WithTop ℚ) := by norm_cast
  have hz : (l : ℝ) ^ (-((s : ℚ) : ℝ)) = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [← Real.rpow_intCast]; push_cast; rfl
  refine ⟨{ emb := emb, emb_bij := hbij, emb_σ := hσ, n_eq := rfl, v_l := ?_, s_pos := hs1,
            s_two := fun h => hs2 (by rwa [P.PD_p] at h), Gam := ↥χK.range,
            resΓ := χK.rangeRestrict, resΓ_onto := χK.rangeRestrict_surjective, χΓ := χΓ,
            χΓ_res := fun g => (hres g).symm, χΓ_inj := ?_, gam := gam, gam_gen := ?_, DelF := D,
            DelF_def := hD, gamK := gamK, gamK_gen := ?_, gamK_eq := ?_,
            gamK_eq_one := fun h h' => hK1 h (by rwa [P.PD_p] at h'),
            GKs := (congSub l s).comap χK, GKs_def := ?_, one := one, one_triv := hone1,
            one_line := hone2 }⟩
  · rw [P.PD_p]
    have := (h1 (l : ↥LL.1) 1).2 (by
      have h := norm_coe_algebraMap LL (l : ℤ_[l])
      rw [map_natCast, map_natCast] at h
      rw [h, PadicInt.norm_p]; simp [Real.rpow_neg_one])
    simpa using this
  · intro a b hab
    have h := congrArg (fun u : (↥(OL LL))ˣ => (u : ↥(OL LL))) hab
    simp only [hχΓ] at h
    have h0 := norm_coe_algebraMap LL (((a : ℤ_[l]ˣ) : ℤ_[l]) - ((b : ℤ_[l]ˣ) : ℤ_[l]))
    rw [map_sub, h, sub_self, map_zero, ZeroMemClass.coe_zero, norm_zero, eq_comm, norm_eq_zero,
      sub_eq_zero] at h0
    exact Subtype.ext (Units.ext h0)
  · rw [← hs, h1, hχΓ, norm_sub_one, hgam, hz]
  · intro g
    rw [v_le_iff, hχΓ, hχΓ, norm_pow_sub_one, norm_pow_sub_one]
    exact hK g
  · intro h
    refine hKeq fun g => ?_
    have := h g
    rwa [v_le_iff, hχΓ, hχΓ, norm_pow_sub_one, norm_pow_sub_one] at this
  · intro g
    rw [Subgroup.mem_comap, mem_congSub, ← hs, h2, hres, norm_sub_one, hz]

end GlobalTheory.HWL.GroupLayer
