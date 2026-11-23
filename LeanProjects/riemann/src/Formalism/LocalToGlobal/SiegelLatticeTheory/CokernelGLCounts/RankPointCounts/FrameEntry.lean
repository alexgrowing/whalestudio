import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolLat

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem sum_fvec {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (w : Fin (D.R.rS + 1) → D.host.E) :
    ∑ c, w c • F0.fvec c = ∑ a : Fin D.R.rS, w (Fin.castSucc a) • F0.e a + w (Fin.last _) • F0.z := by
  rw [Fin.sum_univ_castSucc]
  simp [FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last]

theorem frame_entry {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hX : XLam Λ F = XS D F.fl) (hz : F.fl.z ∈ Λ) (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hs : ∀ v ∈ Λ, s v ∈ Λ)
    (uu : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu)
    (hfr : ∀ b, s (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (c b : Fin (D.R.rS + 1)) (hcb : c < b) :
    uu c b ∈ ddS D ^ (-((((b : ℕ) - (c : ℕ) : ℕ)) : ℤ)) := by
  have hne := Formalism.L2.SG.Pf.StabIntSh.lg_ddS_ne (D := D)
  have hXS_le : XS D F.fl ≤ Λ := by rw [← hX]; exact inf_le_left
  have hXmem : ∀ y : Fin D.R.rS → D.host.E, (∑ a, y a • F.fl.e a) ∈ Λ → (∑ a, y a • F.fl.e a) ∈ XS D F.fl := by
    intro y hy
    rw [← hX]
    refine Submodule.mem_inf.2 ⟨hy, ?_⟩
    show (∑ a, y a • F.fl.e a) ∈ F.fl.X
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hc : (c : ℕ) < D.R.rS := lt_of_lt_of_le hcb (Nat.lt_succ_iff.1 b.2)
  obtain ⟨a, rfl⟩ : ∃ a : Fin D.R.rS, c = Fin.castSucc a := ⟨⟨c, hc⟩, rfl⟩
  induction b using Fin.lastCases with
  | last =>
    have hv : s F.fl.z - F.fl.z = ∑ a', uu (Fin.castSucc a') (Fin.last _) • F.fl.e a' := by
      have h := hfr (Fin.last _)
      rw [sum_fvec] at h
      simp only [FlagG.fvec, Fin.snoc_last] at h
      rw [h, (huu _ _).2 rfl, one_smul, add_sub_cancel_right]
    have hmem : s F.fl.z - F.fl.z ∈ XS D F.fl := by
      rw [hv]
      apply hXmem
      rw [← hv]
      exact Λ.sub_mem (hs _ hz) hz
    have h := coef_XS F.fl hmem _ hv a
    have e : (-((((Fin.last D.R.rS : Fin (D.R.rS + 1)) : ℕ) - ((Fin.castSucc a : Fin (D.R.rS + 1)) : ℕ) : ℕ)) : ℤ) =
        -((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) := by
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [Nat.cast_sub a.2.le]
    rw [e]
    exact h
  | cast b' =>
    have hab : (a : ℕ) < b' := hcb
    have key : ∀ x ∈ ddS D ^ (-((D.R.rS : ℤ) - ((b' : ℕ) : ℤ))),
        x * uu (Fin.castSucc a) (Fin.castSucc b') ∈ ddS D ^ (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))) := by
      intro x hx
      have hgen : x • F.fl.e b' ∈ XS D F.fl := Submodule.subset_span ⟨b', x, hx, rfl⟩
      have hv : s (x • F.fl.e b') = ∑ a', (x * uu (Fin.castSucc a') (Fin.castSucc b')) • F.fl.e a' := by
        have h := hfr (Fin.castSucc b')
        rw [sum_fvec] at h
        simp only [FlagG.fvec, Fin.snoc_castSucc] at h
        rw [LinearEquiv.map_smul, h, (huu _ _).1 (Fin.castSucc_lt_last b'), zero_smul, add_zero, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [smul_smul]
      have hmem : s (x • F.fl.e b') ∈ XS D F.fl := by
        rw [hv]
        apply hXmem
        rw [← hv]
        exact hs _ (hXS_le hgen)
      exact coef_XS F.fl hmem _ hv a
    have h := mem_of_mul (ddS D) hne _ _ _ key
    have e : (-((((Fin.castSucc b' : Fin (D.R.rS + 1)) : ℕ) - ((Fin.castSucc a : Fin (D.R.rS + 1)) : ℕ) : ℕ)) : ℤ) =
        -((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) - -((D.R.rS : ℤ) - ((b' : ℕ) : ℤ)) := by
      simp only [Fin.val_castSucc]
      rw [Nat.cast_sub hab.le]
      ring
    rw [e]
    exact h

end Formalism.L2.SG.Pf.ZsVolLat

end
