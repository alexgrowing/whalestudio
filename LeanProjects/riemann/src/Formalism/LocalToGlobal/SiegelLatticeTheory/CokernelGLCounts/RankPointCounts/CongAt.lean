import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolCong

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix IsDedekindDomain
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem cong_at {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hc : IsFixedConv Λ (Lat.gS D) F) (hc' : IsFixedConv Λ (Lat.gS D) F')
    (hz' : F'.fl.z ∈ Λ) (hadm : ∀ b, ModG (VS D) Λ (Lat.gS D) (F'.fl.fvec b - F.fl.fvec b))
    (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hs : ∀ v ∈ Λ, s v ∈ Λ)
    (uu uu' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu) (huu' : IsUpUni uu')
    (hfr : ∀ b, s (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (hfr' : ∀ b, s (F'.fl.fvec b) = ∑ c, uu' c b • F'.fl.fvec c)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (j i : Fin (D.R.rS + 1)) (hji : j < i) :
    ∃ t : 𝓞 D.host.E, t ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E,
      (t : D.host.E) * (uu j i - uu' j i) = ((Lat.gS D : ℕ) : D.host.E) * o := by
  have hP := P.isPrime
  set g : 𝓞 D.host.E := ((Lat.gS D : ℕ) : 𝓞 D.host.E) with hg
  set M := Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {g} • Λ) with hM
  have hg0 : ((Lat.gS D : ℕ) : D.host.E) ≠ 0 := by
    have h2 : (Lat.gS D : ℕ) ≠ 0 := by
      unfold Lat.gS
      exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
    exact_mod_cast h2

  have hgs : ∀ x : (VS D).V, x ∈ Ideal.span {g} • Λ ↔ ∃ l ∈ Λ, g • l = x := by
    intro x
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  have hd : ∀ c, F'.fl.fvec c - F.fl.fvec c ∈ M := fun c => hadm c P hgP
  have hsd : s (F'.fl.fvec i - F.fl.fvec i) ∈ M := by
    obtain ⟨t, ht, htd⟩ := (mem_locP P.asIdeal _ _).1 (hd i)
    obtain ⟨l, hl, hlg⟩ := (hgs _).1 htd
    refine (mem_locP P.asIdeal _ _).2 ⟨t, ht, ?_⟩
    rw [← smul_O, ← hlg, smul_O]
    exact (hgs _).2 ⟨s l, hs l hl, rfl⟩
  have hud : ∀ c, uu' c i • (F'.fl.fvec c - F.fl.fvec c) ∈ M := by
    intro c
    obtain ⟨t1, ht1, o, ho⟩ := int_at F' Λ hc' hz' s hs uu' huu' hfr' P hgP c i
    obtain ⟨t2, ht2, htd⟩ := (mem_locP P.asIdeal _ _).1 (hd c)
    obtain ⟨l, hl, hlg⟩ := (hgs _).1 htd
    refine (mem_locP P.asIdeal _ _).2 ⟨t1 * t2, fun h => (hP.mem_or_mem h).elim ht1 ht2, ?_⟩
    have e : (t1 * t2) • (uu' c i • (F'.fl.fvec c - F.fl.fvec c)) = o • (t2 • (F'.fl.fvec c - F.fl.fvec c)) := by
      rw [← algebraMap_smul D.host.E (t1 * t2), ← algebraMap_smul D.host.E o, ← algebraMap_smul D.host.E t2, smul_smul,
        smul_smul]
      have ho' : algebraMap (𝓞 D.host.E) D.host.E t1 * uu' c i = algebraMap (𝓞 D.host.E) D.host.E o := ho
      rw [map_mul, mul_right_comm, ho']
    rw [e, ← hlg]
    exact (hgs _).2 ⟨o • l, Λ.smul_mem o hl, smul_comm g o l⟩

  set y : Fin D.R.rS → D.host.E := fun a => uu' (Fin.castSucc a) i - uu (Fin.castSucc a) i with hy
  have hlast : uu' (Fin.last _) i - uu (Fin.last _) i = 0 := by
    by_cases h : i = Fin.last _
    · subst h
      rw [(huu' _ _).2 rfl, (huu _ _).2 rfl, sub_self]
    · have hlt : i < Fin.last _ := lt_of_le_of_ne (Fin.le_last i) h
      rw [(huu' _ _).1 hlt, (huu _ _).1 hlt, sub_self]
  have hw : ∑ a, y a • F.fl.e a = s (F'.fl.fvec i - F.fl.fvec i) - ∑ c, uu' c i • (F'.fl.fvec c - F.fl.fvec c) := by
    rw [map_sub, hfr i, hfr' i]
    simp only [smul_sub, Finset.sum_sub_distrib]
    have h2 : ∑ c, (uu' c i - uu c i) • F.fl.fvec c = ∑ a, y a • F.fl.e a := by
      rw [sum_fvec]
      simp only [hy, hlast, zero_smul, add_zero]
    rw [← h2]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  have hwM : ∑ a, y a • F.fl.e a ∈ M := by
    rw [hw]
    exact M.sub_mem hsd (M.sum_mem fun c _ => hud c)
  obtain ⟨t, ht, htw⟩ := (mem_locP P.asIdeal _ _).1 hwM
  obtain ⟨l, hl, hlg⟩ := (hgs _).1 htw

  have hl_eq : l = ∑ a, (((Lat.gS D : ℕ) : D.host.E)⁻¹ * ((t : D.host.E) * y a)) • F.fl.e a := by
    have h1 : ((Lat.gS D : ℕ) : D.host.E) • l = t • ∑ a, y a • F.fl.e a := by
      rw [← hlg, ← algebraMap_smul D.host.E g]
      rfl
    have h2 := congrArg (fun v => ((Lat.gS D : ℕ) : D.host.E)⁻¹ • v) h1
    simp only [smul_smul, inv_mul_cancel₀ hg0, one_smul] at h2
    rw [h2, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul D.host.E t, smul_smul, smul_smul, mul_assoc]
  have hlX : l ∈ XLam Λ F := by
    refine Submodule.mem_inf.2 ⟨hl, ?_⟩
    show l ∈ F.fl.X
    rw [hl_eq]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hloc : l ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
    rw [← conv_at F Λ hc P hgP]
    exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hlX⟩
  obtain ⟨t', ht', ht'l⟩ := (mem_locP P.asIdeal _ _).1 hloc
  have hv2 : t' • l = ∑ a, ((t' : D.host.E) * (((Lat.gS D : ℕ) : D.host.E)⁻¹ * ((t : D.host.E) * y a))) • F.fl.e a := by
    rw [hl_eq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul D.host.E t', smul_smul]
  have hjr : (j : ℕ) < D.R.rS := lt_of_lt_of_le hji (Nat.lt_succ_iff.1 i.2)
  obtain ⟨o, ho⟩ := coef_spanO F.fl ht'l _ hv2 ⟨j, hjr⟩
  refine ⟨t' * t, fun h => (hP.mem_or_mem h).elim ht' ht, -o, ?_⟩
  have hyj : y ⟨j, hjr⟩ = uu' j i - uu j i := rfl
  rw [hyj] at ho
  have hgi : ((Lat.gS D : ℕ) : D.host.E) * ((Lat.gS D : ℕ) : D.host.E)⁻¹ = 1 := mul_inv_cancel₀ hg0
  push_cast
  linear_combination ((Lat.gS D : ℕ) : D.host.E) * ho + ((t' : D.host.E) * (t : D.host.E) * (uu' j i - uu j i)) * hgi

end Formalism.L2.SG.Pf.ZsVolLat

end
