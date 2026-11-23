import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock

noncomputable section

namespace GlobalTheory.IndJacBlock.Fwd

open GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem place_zero_val (b : Fin 2 → ℕ) (i : Fin (b 0)) :
    ((pairPlace b (rfl : b 0 + b 1 = _) ⟨0, i⟩ : Fin _) : ℕ) = i := by
  simp [pairPlace]

theorem place_one_val (b : Fin 2 → ℕ) (i : Fin (b 1)) :
    ((pairPlace b (rfl : b 0 + b 1 = _) ⟨1, i⟩ : Fin _) : ℕ) = b 0 + i := by
  simp [pairPlace]

theorem Y0_mul_pair (b : Fin 2 → ℕ) (p : parab k (pairPlace b (rfl : b 0 + b 1 = _))) :
    Y0 k (b 1) (b 0 + b 1) * (p : GL (Fin (b 0 + b 1)) k).1 =
      (leviProj k (pairPlace b rfl) p 1 : GL (Fin (b 1)) k).1 * Y0 k (b 1) (b 0 + b 1) := by
  ext i j
  rw [Y0_mul_apply, mul_Y0_apply]
  have e1 : pairPlace b (rfl : b 0 + b 1 = _) ⟨1, i⟩ = Fin.natAdd (b 0) i :=
    Fin.ext (by rw [place_one_val]; simp)
  split_ifs with h
  · rw [leviProj_apply]
    have e2 : pairPlace b (rfl : b 0 + b 1 = _) ⟨1, (⟨j - b 0, by omega⟩ : Fin (b 1))⟩ = j :=
      Fin.ext (by rw [place_one_val]; simp; omega)
    rw [e1, e2]
  · have hp := mem_parab_iff.1 p.2 1 0 i ⟨j, by omega⟩ (by decide)
    have e3 : pairPlace b (rfl : b 0 + b 1 = _) ⟨0, (⟨j, by omega⟩ : Fin (b 0))⟩ = j :=
      Fin.ext (by rw [place_zero_val])
    rwa [e1, e3] at hp

theorem deltaHalf_two_blocks (b : Fin 2 → ℕ) (g : Levi k (fun j : Fin 2 => Fin (b j))) :
    ((deltaHalf k (fun j : Fin 2 => Fin (b j)) g : ℂˣ) : ℂ) =
      apow (gdet (g 0)) ((b 1 : ℂ) / 2) * apow (gdet (g 1)) (-(b 0 : ℂ) / 2) := by
  have h0 : modExp (fun j : Fin 2 => Fin (b j)) 0 = b 1 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  have h1 : modExp (fun j : Fin 2 => Fin (b j)) 1 = -(b 0 : ℤ) := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_two]
  rw [deltaHalf_apply, Fin.prod_univ_two, h0, h1]
  push_cast
  rfl

theorem pairChar_two_blocks (b : Fin 2 → ℕ) (μ : Fin 2 → kˣ →* ℂˣ) (g : Levi k (fun j : Fin 2 => Fin (b j))) :
    pairChar k b μ g = μ 0 (gdet (g 0)) * μ 1 (gdet (g 1)) := by
  simp [pairChar, MonoidHom.finsetProd_apply, Fin.prod_univ_two]

theorem exists_detTw_pair (b : Fin 2 → ℕ) (d : ℕ) (h : b 0 + b 1 = d) (ν : kˣ →* ℂˣ) (χ : Fin 2 → kˣ →* ℂˣ)
    (h0 : χ 0 = 1) (h1 : χ 1 = ν⁻¹) (f : GL (Fin d) k → ℂ) (hf : f ∈ indSp k (b 1) d ν) :
    ∃ F : IndSp (pairPlace b h) (ofChar (pairChar k b χ)), F.1.1 = detTw d ((b 1 : ℂ) / 2) f := by
  subst h
  obtain ⟨⟨U, hU, hfU⟩, hfl⟩ := hf
  have hK : IsSmoothChar (detChar (Fin (b 0 + b 1)) (absPow k ((b 1 : ℂ) / 2))) :=
    (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar
  have hK1 : ((detChar (Fin (b 0 + b 1)) (absPow k ((b 1 : ℂ) / 2))).ker : Set (GL (Fin (b 0 + b 1)) k)) ∈ nhds 1 :=
    hK.mem_nhds (by simp)
  refine ⟨⟨⟨detTw (b 0 + b 1) ((b 1 : ℂ) / 2) f, fun p x => ?_⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (Filter.inter_mem hU hK1) fun g hg => ?_)⟩, rfl⟩
  · have hl := hfl p x (leviProj k (pairPlace b rfl) p 1) (Y0_mul_pair b p)
    set A := leviProj k (pairPlace b rfl) p 0 with hA
    set D := leviProj k (pairPlace b rfl) p 1 with hD
    have hdet : gdet (p : GL (Fin (b 0 + b 1)) k) = gdet A * gdet D := by
      rw [gdet, det_parab, Fin.prod_univ_two]
    have e : apow (gdet D) (-(b 0 : ℂ) / 2) =
        apow (gdet D) ((b 1 : ℂ) / 2) * apow (gdet D) (-((b 0 + b 1 : ℕ) : ℂ) / 2) := by
      rw [← apow_add]; congr 1; push_cast; ring
    simp only [MonoidHom.comp_apply, twist_apply, ofChar_apply, detTw_apply, gdet_mul, apow_mul, hl, hdet,
      smul_eq_mul, deltaHalf_two_blocks, pairChar_two_blocks, h0, h1, ← hA, ← hD, e,
      MonoidHom.one_apply, one_mul, MonoidHom.inv_apply]
    ring
  · have hg2 : apow (gdet g) ((b 1 : ℂ) / 2) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.1 hg.2)
      exact this
    apply Subtype.ext
    show (fun x => detTw (b 0 + b 1) ((b 1 : ℂ) / 2) f (x * g)) = detTw (b 0 + b 1) ((b 1 : ℂ) / 2) f
    funext x
    simp only [detTw_apply, gdet_mul, apow_mul, hg2, mul_one, hfU x g hg.1]

end GlobalTheory.IndJacBlock.Fwd

namespace GlobalTheory.IndJacBlock

theorem exists_indSp_detTw : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (hnd : n ≤ d) (ν : kˣ →* ℂˣ), ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν,
    ∃ F : IndSp (pairPlace (b2 n d) (block_size_pair_sum hnd)) (ofChar (pairChar k (b2 n d) (chi2 k ν))),
      F.1.1 = GlobalTheory.FullRankCoinv.IndTwist.detTw d ((n : ℂ) / 2) f := by
  intro k _ _ _ _ n d hnd ν f hf
  exact Fwd.exists_detTw_pair (b2 n d) d (block_size_pair_sum hnd) ν (chi2 k ν) rfl rfl f hf

end GlobalTheory.IndJacBlock
