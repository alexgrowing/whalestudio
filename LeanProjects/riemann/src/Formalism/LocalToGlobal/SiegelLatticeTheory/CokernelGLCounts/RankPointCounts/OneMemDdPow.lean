import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameEntry

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix IsDedekindDomain
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_of_loc (I : Submodule (𝓞 D.host.E) D.host.E) (x : D.host.E)
    (h : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ t : 𝓞 D.host.E, t ∉ P.asIdeal ∧ (t : D.host.E) * x ∈ I) : x ∈ I := by
  let J : Ideal (𝓞 D.host.E) :=
    { carrier := {t | (t : D.host.E) * x ∈ I}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at *
        push_cast
        rw [add_mul]
        exact I.add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        push_cast
        rw [zero_mul]
        exact I.zero_mem
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq] at *
        have e : (((c • a : 𝓞 D.host.E)) : D.host.E) * x = c • ((a : D.host.E) * x) := by
          rw [smul_eq_mul, Algebra.smul_def]
          push_cast
          ring
        rw [e]
        exact I.smul_mem c ha }
  by_contra hx
  have hJ : J ≠ ⊤ := by
    intro h1
    have h2 : (1 : 𝓞 D.host.E) ∈ J := h1 ▸ Submodule.mem_top
    apply hx
    have h3 : ((1 : 𝓞 D.host.E) : D.host.E) * x ∈ I := h2
    simpa using h3
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJ
  have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.E)
  obtain ⟨t, htP, ht⟩ := h ⟨M, hM.isPrime, hM0⟩
  exact htP (hJM ht)

theorem one_mem_ddPow (k : ℕ) : (1 : D.host.E) ∈ ddS D ^ (-(k : ℤ)) := by
  have hne := Formalism.L2.SG.Pf.StabIntSh.lg_ddS_ne (D := D)
  have h1 : ddS D ^ k ≤ 1 := pow_le_one' FractionalIdeal.coeIdeal_le_one k
  have h2 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ ≤ (ddS D ^ k)⁻¹ :=
    FractionalIdeal.inv_anti_mono (pow_ne_zero k hne) one_ne_zero h1
  rw [inv_one] at h2
  rw [_root_.zpow_neg, zpow_natCast]
  exact h2 (FractionalIdeal.mem_one_iff _ |>.2 ⟨1, map_one _⟩)

theorem coef_spanO {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {v : (VS D).V}
    (hv : v ∈ Submodule.span (𝓞 D.host.E) (Set.range F0.e))
    (y : Fin D.R.rS → D.host.E) (hy : v = ∑ a, y a • F0.e a) (a : Fin D.R.rS) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = y a := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  have hyy : y = fun b => (c b : D.host.E) := by
    have h := F0.e_indep
    rw [Fintype.linearIndependent_iff] at h
    funext b
    have := h (fun b => y b - (c b : D.host.E)) (by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hy]
      rw [← hc]
      simp only [sub_eq_zero]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [algebraMap_smul]) b
    exact sub_eq_zero.1 this
  exact ⟨c a, by rw [hyy]⟩

end Formalism.L2.SG.Pf.ZsVolLat

end
