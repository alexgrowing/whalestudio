import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.JTranslate
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.Imports
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.BlockIndexOfWeylShuffle
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.Bridge
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellBlockShapes.OpenJ
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellBlockShapes.ValuationOneApplyLe
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.MemUnipUTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier GlobalTheory.SplitWeil GroundTheory.Automorphic.Whittaker
open GroundTheory.Automorphic.GLnLocal ValuativeRel

namespace PositivityTheory.RgUd.CellA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_le_one_of_nabs_lt (z : kˣ) (hz : nabs k z < 1) : valuation k (z : k) ≤ 1 := by
  have h := (nabs_le_iff z 1).1 (by rw [nabs_one]; exact hz.le)
  simpa using h

theorem scalar_id (t : ℝ) (ht : 0 < t) (i m r : ℕ) :
    (t ^ i) ^ (m * r) * (t ^ i) ^ (-((m * r : ℕ) : ℝ) / 2) = Real.sqrt t ^ (i * m * r) := by
  have hti : 0 < t ^ i := pow_pos ht i
  rw [← Real.rpow_natCast (t ^ i) (m * r), ← Real.rpow_add hti, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast (t ^ (1 / 2 : ℝ)), ← Real.rpow_mul ht.le, ← Real.rpow_natCast t i,
    ← Real.rpow_mul ht.le]
  congr 1
  push_cast
  ring

variable {r m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

set_option maxHeartbeats 2000000 in

theorem openCellPar (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (ρ : Representation ℂ (Levi k fun a => Fin (dd r m a)) W) (hρ : IsSmooth ρ) (ω : kˣ →* ℂˣ)
    (hcent : ∀ (z : kˣ) (t : W), ρ (levZ k r m z) t = (ω z : ℂ) • t)
    (hv : ∃ v, v ∉ twKer ρ (unipM k (dd r m)) (whitM (dd r m) ψ)) (z : kˣ) (hz : nabs k z < 1) :
    ∃ F : IndSp (stdBlocks (dd r m) (hdd r m)) ρ,
      F ∉ twKer (parInd (stdBlocks (dd r m) (hdd r m)) ρ) (unipB k (Fin (r + m))) (whitChar ψ (r + m)) ∧
      ∀ i : ℕ, parInd (stdBlocks (dd r m) (hdd r m)) ρ (aDiag k (r + m) m (z ^ i)) F -
        (((Real.sqrt (nabs k z) : ℝ) : ℂ) ^ (i * m * r) * (ω z : ℂ) ^ i) • F ∈
          twKer (parInd (stdBlocks (dd r m) (hdd r m)) ρ) (unipB k (Fin (r + m))) (whitChar ψ (r + m)) := by
  obtain ⟨v, hv⟩ := hv
  have hv0 : v ≠ 0 := fun h => hv (h ▸ Submodule.zero_mem _)
  obtain ⟨J, vol, _, hJker, hJU, _, hJvol⟩ :=
    CellB.openJ k ψ hψ 2 (r + m) (dd r m) (hdd r m) ρ hρ
  obtain ⟨n, _, hwhit, hcpt, hopen, f, hf, hfv, hf0⟩ :=
    exists_bump k ψ hψ 2 (r + m) (dd r m) (hdd r m) ρ hρ v
  have hle : CellB.congrL k r m n ≤ unipU k (dd r m) (hdd r m) := inf_le_left
  have hwL : ∀ (u : GL (Fin (r + m)) k) (hb : u ∈ unipB k (Fin (r + m))),
      u ∈ CellB.congrL k r m n → whitChar ψ (r + m) ⟨u, hb⟩ = 1 :=
    fun u hb hu => hwhit u hb (CellB.mem_congrL.1 hu).2
  obtain ⟨hpos, hJf⟩ := hJvol _ hle hcpt hopen
  have hJ0 := hJf ⟨f, hf⟩ v (fun u hb hu => by
    rw [hwL u hb hu, Units.val_one, one_smul]; exact hfv u hu) hf0
  have hz1 := valuation_le_one_of_nabs_lt z hz
  refine ⟨f, ?_, fun i => ?_⟩
  · intro h
    have h2 := (hJker ⟨f, hf⟩).2 h
    rw [hJ0] at h2
    exact hv ((Submodule.smul_mem_iff _ (Complex.ofReal_ne_zero.2 hpos.ne')).1 h2)
  · have hval : valuation k ((z ^ i : kˣ) : k) ≤ 1 := by
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_one₀ zero_le' hz1
    set a := aDiag k (r + m) m (z ^ i) with ha
    have hconj := conj_aDiag (r := r) (m := m) k (z ^ i)
    have hB : ∀ u ∈ unipB k (Fin (r + m)), a * u * a⁻¹ ∈ unipB k (Fin (r + m)) :=
      fun u hu => aDiag_conj_mem_unipB k _ m (z ^ i) hu
    have hU : ∀ u ∈ unipU k (dd r m) (hdd r m), a * u * a⁻¹ ∈ unipU k (dd r m) (hdd r m) :=
      fun u hu => aDiag_conj_mem_unipU k (z ^ i) hu
    have hUi : ∀ u ∈ unipU k (dd r m) (hdd r m), a⁻¹ * u * a ∈ unipU k (dd r m) (hdd r m) := by
      intro u hu
      have h := aDiag_conj_mem_unipU (r := r) (m := m) k (z ^ i)⁻¹ hu
      rwa [← aDiag_inv, inv_inv] at h
    have hLc : ∀ u ∈ CellB.congrL k r m n, a * u * a⁻¹ ∈ CellB.congrL k r m n := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := CellB.mem_congrL.1 hu
      exact CellB.mem_congrL.2 ⟨hU u hu1,
        aDiag_conj_mem_congr k _ m (z ^ i) hval n ((mem_unipU_two k).1 hu1).1 hu2⟩
    obtain ⟨_, hm, hJa⟩ := J_translate ψ J vol hJvol _ hle hcpt hopen hwL f hf v hfv hf0
      a (levZ k r m (z ^ i)) hconj hB hU hUi hLc
    set δ : ℂ := ((deltaHalf k (fun a : Fin 2 => Fin (dd r m a)) (levZ k r m (z ^ i)) : ℂˣ) : ℂ)
      with hδ
    have hvol := CellB.vol_conj_aDiag ψ ρ J vol hJU hJvol (fun u => mem_unipU_two k) n (z ^ i) hval
      hwL ⟨_, hm⟩ (δ • ρ (levZ k r m (z ^ i)) v)
      (by rw [hcent]; exact smul_ne_zero (Units.ne_zero _) (smul_ne_zero (Units.ne_zero _) hv0))
      (fun u hu => by
        obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
        show _ = _
        rw [translate_apply (dd r m) (hdd r m) ρ a _ hconj f]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show a⁻¹ * (a * u' * a⁻¹) * a = u' by group, hfv u' hu'])
      (fun u hu hnu => by
        show _ = _
        rw [translate_apply (dd r m) (hdd r m) ρ a _ hconj f]
        rw [hf0 _ (hUi u hu) (fun h => hnu (Subgroup.mem_map.2 ⟨a⁻¹ * u * a, h, by
          show a * (a⁻¹ * u * a) * a⁻¹ = u
          group⟩)), map_zero, smul_zero])
    have hmem : parInd (stdBlocks (dd r m) (hdd r m)) ρ a f -
        (((Real.sqrt (nabs k z) : ℝ) : ℂ) ^ (i * m * r) * (ω z : ℂ) ^ i) • f ∈
          openFns (dd r m) (hdd r m) ρ := sub_mem hm (Submodule.smul_mem _ _ hf)
    apply (hJker ⟨_, hmem⟩).1
    have hsplit : J ⟨_, hmem⟩ = J ⟨_, hm⟩ -
        (((Real.sqrt (nabs k z) : ℝ) : ℂ) ^ (i * m * r) * (ω z : ℂ) ^ i) • J ⟨f, hf⟩ := by
      rw [← map_smul, ← map_sub]
      rfl
    rw [hsplit, hJa, hJ0, hvol, hcent, hδ, deltaHalf_levZ, nabs_pow]
    convert Submodule.zero_mem _
    rw [smul_smul, smul_smul, smul_smul, ← sub_smul]
    convert zero_smul ℂ v
    rw [sub_eq_zero, map_pow, Units.val_pow_eq_pow_val, ← Complex.ofReal_pow,
      ← scalar_id (nabs k z) (GlobalTheory.SplitWeil.nabs_pos k z) i m r]
    push_cast
    ring

end PositivityTheory.RgUd.CellA
