import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OneMemDdPow

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix IsDedekindDomain
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_locP {W : Type*} [AddCommGroup W] [Module (𝓞 D.host.E) W] (p : Ideal (𝓞 D.host.E)) [p.IsPrime]
    (L : Submodule (𝓞 D.host.E) W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ t : 𝓞 D.host.E, t ∉ p ∧ t • x ∈ L := Iff.rfl

theorem smul_O (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (t : 𝓞 D.host.E) (x : (VS D).V) : s (t • x) = t • s x := by
  rw [← algebraMap_smul D.host.E t x, LinearEquiv.map_smul, algebraMap_smul]

theorem conv_at {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hc : IsFixedConv Λ (Lat.gS D) F) (P : HeightOneSpectrum (𝓞 D.host.E)) (hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
  obtain ⟨c, -, hc1, heq⟩ := hc.1 P
  rw [heq]
  congr 2
  ext v
  simp [hc1 hgP]

theorem int_at {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hc : IsFixedConv Λ (Lat.gS D) F) (hz : F.fl.z ∈ Λ) (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hs : ∀ v ∈ Λ, s v ∈ Λ)
    (uu : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu)
    (hfr : ∀ b, s (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (c i : Fin (D.R.rS + 1)) :
    ∃ t : 𝓞 D.host.E, t ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (t : D.host.E) * uu c i = o := by
  have hP := P.isPrime
  have hconv := conv_at F Λ hc P hgP
  rcases lt_trichotomy c i with hci | hci | hci
  · have hcr : (c : ℕ) < D.R.rS := lt_of_lt_of_le hci (Nat.lt_succ_iff.1 i.2)
    obtain ⟨a, rfl⟩ : ∃ a : Fin D.R.rS, c = Fin.castSucc a := ⟨⟨c, hcr⟩, rfl⟩
    have hXmem : ∀ y : Fin D.R.rS → D.host.E, (∑ a, y a • F.fl.e a) ∈ Λ → (∑ a, y a • F.fl.e a) ∈ XLam Λ F := by
      intro y hy
      refine Submodule.mem_inf.2 ⟨hy, ?_⟩
      show (∑ a, y a • F.fl.e a) ∈ F.fl.X
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    induction i using Fin.lastCases with
    | last =>
      have hv : s F.fl.z - F.fl.z = ∑ a', uu (Fin.castSucc a') (Fin.last _) • F.fl.e a' := by
        have h := hfr (Fin.last _)
        rw [sum_fvec] at h
        simp only [FlagG.fvec, Fin.snoc_last] at h
        rw [h, (huu _ _).2 rfl, one_smul, add_sub_cancel_right]
      have hmem : s F.fl.z - F.fl.z ∈ XLam Λ F := by
        rw [hv]
        apply hXmem
        rw [← hv]
        exact Λ.sub_mem (hs _ hz) hz
      have hloc : s F.fl.z - F.fl.z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
        rw [← hconv]
        exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hmem⟩
      obtain ⟨t, ht, htv⟩ := (mem_locP P.asIdeal _ _).1 hloc
      have hv2 : t • (s F.fl.z - F.fl.z) = ∑ a', ((t : D.host.E) * uu (Fin.castSucc a') (Fin.last _)) • F.fl.e a' := by
        rw [hv, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← algebraMap_smul D.host.E t, smul_smul]
      obtain ⟨o, ho⟩ := coef_spanO F.fl htv _ hv2 a
      exact ⟨t, ht, o, ho.symm⟩
    | cast i' =>
      have he : F.fl.e i' ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) := by
        rw [hconv]
        exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact Submodule.subset_span ⟨i', rfl⟩⟩
      obtain ⟨t1, ht1, ht1e⟩ := (mem_locP P.asIdeal _ _).1 he
      have hv : s (t1 • F.fl.e i') = ∑ a', ((t1 : D.host.E) * uu (Fin.castSucc a') (Fin.castSucc i')) • F.fl.e a' := by
        have h := hfr (Fin.castSucc i')
        rw [sum_fvec] at h
        simp only [FlagG.fvec, Fin.snoc_castSucc] at h
        rw [smul_O, h, (huu _ _).1 (Fin.castSucc_lt_last i'), zero_smul, add_zero, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← algebraMap_smul D.host.E t1, smul_smul]
      have hmem : s (t1 • F.fl.e i') ∈ XLam Λ F := by
        rw [hv]
        apply hXmem
        rw [← hv]
        exact hs _ (Submodule.mem_inf.1 ht1e).1
      have hloc : s (t1 • F.fl.e i') ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
        rw [← hconv]
        exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hmem⟩
      obtain ⟨t2, ht2, ht2v⟩ := (mem_locP P.asIdeal _ _).1 hloc
      have hv2 : t2 • s (t1 • F.fl.e i') =
          ∑ a', ((t2 : D.host.E) * ((t1 : D.host.E) * uu (Fin.castSucc a') (Fin.castSucc i'))) • F.fl.e a' := by
        rw [hv, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← algebraMap_smul D.host.E t2, smul_smul]
      obtain ⟨o, ho⟩ := coef_spanO F.fl ht2v _ hv2 a
      refine ⟨t2 * t1, fun h => (hP.mem_or_mem h).elim ht2 ht1, o, ?_⟩
      rw [ho]
      push_cast
      ring
  · subst hci
    exact ⟨1, P.asIdeal.primeCompl.one_mem, 1, by rw [(huu c c).2 rfl]; simp⟩
  · exact ⟨1, P.asIdeal.primeCompl.one_mem, 0, by rw [(huu c i).1 hci]; simp⟩

end Formalism.L2.SG.Pf.ZsVolLat

end
