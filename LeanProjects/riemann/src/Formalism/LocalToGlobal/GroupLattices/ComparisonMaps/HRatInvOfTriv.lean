import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOfWeak

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} (G : GAtP p) {LL : Type} [Field LL] (e : LL →+* G.Kf)

def InvAt (i : G.comp) (L0 : G.P.Tup) (ξ : G.P.Xsp) : Prop :=
  ∀ γ : (G.lev i).Γ, (G.lev i).smul γ L0 = L0 → ((G.lev i).χ γ : G.O) • (G.lev i).actX γ ξ = ξ

def HRatInv : Prop :=
  ∀ (i : G.comp) (L0 : G.P.Tup), G.P.IsLatTup L0 →
    {ξ | ξ ∈ G.P.HtupW L0 ∧ InvAt G i L0 ξ} ⊆
      Submodule.span G.O {ξ | ξ ∈ G.P.HtupW L0 ∧ InvAt G i L0 ξ ∧ RatX G e ξ}

theorem chiAct_mul (i : G.comp) (a b : (G.lev i).Γ) (ξ : G.P.Xsp) :
    ((G.lev i).χ (a * b) : G.O) • (G.lev i).actX (a * b) ξ =
      ((G.lev i).χ a : G.O) • (G.lev i).actX a (((G.lev i).χ b : G.O) • (G.lev i).actX b ξ) := by
  rw [map_mul, Units.val_mul, Formalism.MainNotions.G.LatticeSystems.jd_actX_mul, LinearMap.comp_apply, LinearMap.map_smul_of_tower, smul_smul]

theorem jdI_apply (i : G.comp) (L0 : G.P.Tup) (γ : (G.lev i).Γ) (ξ : G.P.Xsp) (hξ : InvAt G i L0 ξ) :
    delta G i L0 ξ i ((G.lev i).smul γ L0) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ ξ := by
  classical
  unfold Formalism.MainNotions.G.LatticeSystems.delta
  have hex : ∃ γ' : (G.lev i).Γ, (G.lev i).smul γ L0 = (G.lev i).smul γ' L0 := ⟨γ, rfl⟩
  rw [dif_pos hex, if_pos rfl]
  have hspec : (G.lev i).smul γ L0 = (G.lev i).smul hex.choose L0 := hex.choose_spec
  have hstab : (G.lev i).smul (γ⁻¹ * hex.choose) L0 = L0 := by
    rw [Formalism.MainNotions.G.LatticeSystems.jd_smul_mul, ← hspec, ← Formalism.MainNotions.G.LatticeSystems.jd_smul_mul, inv_mul_cancel,
      Formalism.MainNotions.G.LatticeSystems.jd_smul_one]
  have h1 := hξ (γ⁻¹ * hex.choose) hstab
  calc ((G.lev i).χ hex.choose : G.O) • (G.lev i).actX hex.choose ξ
      = ((G.lev i).χ (γ * (γ⁻¹ * hex.choose)) : G.O) • (G.lev i).actX (γ * (γ⁻¹ * hex.choose)) ξ := by
        rw [mul_inv_cancel_left]
    _ = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (((G.lev i).χ (γ⁻¹ * hex.choose) : G.O) •
          (G.lev i).actX (γ⁻¹ * hex.choose) ξ) := chiAct_mul G i _ _ ξ
    _ = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ ξ := by rw [h1]

theorem jdI_mem (Hv : G.P.Tup → Submodule G.O G.P.Xsp) (hE : EquivSys G Hv)
    (i : G.comp) (L0 : G.P.Tup) (hL0 : G.P.IsLatTup L0) (ξ : G.P.Xsp) (hξ : ξ ∈ Hv L0) (hI : InvAt G i L0 ξ) :
    delta G i L0 ξ ∈ G.funMod Hv := by
  classical
  rw [Formalism.MainNotions.G.GAtP.funMod, Submodule.mem_pi]
  intro i' _
  unfold Formalism.MainNotions.G.Level.funMod
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [Submodule.mem_iInf]
    intro L
    rw [Submodule.mem_iInf]
    intro hL
    rw [Submodule.mem_comap, LinearMap.proj_apply]
    unfold Formalism.MainNotions.G.LatticeSystems.delta
    split_ifs with h1 h2
    · have h3 := hE i h1.choose L0 hL0 ξ hξ
      rwa [← h1.choose_spec] at h3
    · exact Submodule.zero_mem _
    · exact Submodule.zero_mem _
  · rw [Submodule.mem_iInf]
    intro L
    rw [Submodule.mem_iInf]
    intro hL
    rw [LinearMap.mem_ker, LinearMap.proj_apply]
    apply Formalism.MainNotions.G.LatticeSystems.jd_zero
    right
    rintro ⟨γ, rfl⟩
    exact hL (Formalism.MainNotions.G.LatticeSystems.jd_lat _ γ L0 hL0)
  · rw [Submodule.mem_iInf]
    intro γ
    rw [Submodule.mem_iInf]
    intro L
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    simp only [LinearMap.proj_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.restrictScalars_apply]
    by_cases hi : i' = i
    · subst hi
      by_cases hL : ∃ h : (G.lev i').Γ, L = (G.lev i').smul h L0
      · obtain ⟨h, rfl⟩ := hL
        rw [← Formalism.MainNotions.G.LatticeSystems.jd_smul_mul, jdI_apply G i' L0 _ ξ hI, jdI_apply G i' L0 h ξ hI, chiAct_mul]
      · have hL' : ¬ ∃ h : (G.lev i').Γ, (G.lev i').smul γ L = (G.lev i').smul h L0 := by
          rintro ⟨h, hh⟩
          apply hL
          refine ⟨γ⁻¹ * h, ?_⟩
          rw [Formalism.MainNotions.G.LatticeSystems.jd_smul_mul, ← hh, ← Formalism.MainNotions.G.LatticeSystems.jd_smul_mul, inv_mul_cancel,
            Formalism.MainNotions.G.LatticeSystems.jd_smul_one]
        rw [Formalism.MainNotions.G.LatticeSystems.jd_zero G i' L0 ξ i' _ (Or.inr hL'),
          Formalism.MainNotions.G.LatticeSystems.jd_zero G i' L0 ξ i' _ (Or.inr hL), map_zero, smul_zero]
    · rw [Formalism.MainNotions.G.LatticeSystems.jd_zero G i L0 ξ i' _ (Or.inl hi), Formalism.MainNotions.G.LatticeSystems.jd_zero G i L0 ξ i' _ (Or.inl hi),
        map_zero, smul_zero]

theorem inv_of_mem (Hv : G.P.Tup → Submodule G.O G.P.Xsp) (F : G.Fn) (hF : F ∈ G.funMod Hv) (i : G.comp)
    (L0 : G.P.Tup) : InvAt G i L0 (F i L0) := by
  intro γ hγ
  have hFi : F i ∈ (G.lev i).funMod Hv := (Submodule.mem_pi.mp hF) i (Set.mem_univ i)
  unfold Formalism.MainNotions.G.Level.funMod at hFi
  rw [Submodule.mem_inf, Submodule.mem_inf] at hFi
  have h3 := hFi.2
  rw [Submodule.mem_iInf] at h3
  have h4 := h3 γ
  rw [Submodule.mem_iInf] at h4
  have h5 := h4 L0
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h5
  simp only [LinearMap.proj_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.restrictScalars_apply] at h5
  rw [hγ] at h5
  exact h5.symm

theorem jdI_decomp (reps : Finset (G.comp × G.P.Tup)) (hR : IsReps G reps)
    (Hv : G.P.Tup → Submodule G.O G.P.Xsp) (F : G.Fn) (hF : F ∈ G.funMod Hv) :
    F = ∑ r ∈ reps, delta G r.1 r.2 (F r.1 r.2) := by
  classical
  have hcomp : ∀ i, F i ∈ (G.lev i).funMod Hv := fun i => (Submodule.mem_pi.mp hF) i (Set.mem_univ i)
  have heqv : ∀ (i : G.comp) (γ : (G.lev i).Γ) (L : G.P.Tup),
      F i ((G.lev i).smul γ L) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (F i L) := by
    intro i γ L
    have hFi := hcomp i
    unfold Formalism.MainNotions.G.Level.funMod at hFi
    rw [Submodule.mem_inf, Submodule.mem_inf] at hFi
    have h3 := hFi.2
    rw [Submodule.mem_iInf] at h3
    have h4 := h3 γ
    rw [Submodule.mem_iInf] at h4
    have h5 := h4 L
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h5
    simpa only [LinearMap.proj_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.restrictScalars_apply] using h5
  have hzero : ∀ (i : G.comp) (L : G.P.Tup), ¬ G.P.IsLatTup L → F i L = 0 := by
    intro i L hL
    have hFi := hcomp i
    unfold Formalism.MainNotions.G.Level.funMod at hFi
    rw [Submodule.mem_inf, Submodule.mem_inf] at hFi
    have h3 := hFi.1.2
    rw [Submodule.mem_iInf] at h3
    have h4 := h3 L
    rw [Submodule.mem_iInf] at h4
    have h5 := h4 hL
    rwa [LinearMap.mem_ker, LinearMap.proj_apply] at h5
  funext i' L
  rw [Finset.sum_apply, Finset.sum_apply]
  by_cases hL : G.P.IsLatTup L
  · obtain ⟨⟨i0, L0⟩, hr0, hi0, γ, hγ⟩ := hR.2.2 i' L hL
    dsimp only at hi0 hγ
    subst hi0
    rw [Finset.sum_eq_single ⟨i0, L0⟩]
    · dsimp only
      rw [hγ, jdI_apply G i0 L0 γ _ (inv_of_mem G Hv F hF i0 L0), heqv]
    · rintro ⟨i1, L1⟩ hr1 hne
      apply Formalism.MainNotions.G.LatticeSystems.jd_zero
      by_cases h1 : i0 = i1
      · subst h1
        right
        rintro ⟨g, hg⟩
        refine hne (hR.2.1 ⟨i0, L0⟩ hr0 ⟨i0, L1⟩ hr1 rfl ⟨g⁻¹ * γ, ?_⟩).symm
        dsimp only
        rw [Formalism.MainNotions.G.LatticeSystems.jd_smul_mul, ← hγ, hg, ← Formalism.MainNotions.G.LatticeSystems.jd_smul_mul, inv_mul_cancel,
          Formalism.MainNotions.G.LatticeSystems.jd_smul_one]
      · left
        exact fun h => h1 (by simpa using h)
    · intro h
      exact absurd hr0 h
  · rw [hzero i' L hL]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨i1, L1⟩ hr1
    apply Formalism.MainNotions.G.LatticeSystems.jd_zero
    right
    rintro ⟨g, rfl⟩
    exact hL (Formalism.MainNotions.G.LatticeSystems.jd_lat _ g L1 (hR.1 _ hr1))

theorem deltaI_rat (hA : RatActG G e) (i : G.comp) (L0 : G.P.Tup) (ξ : G.P.Xsp) (hξ : RatX G e ξ) :
    RatFn G e (delta G i L0 ξ) := by
  intro i' L
  classical
  unfold Formalism.MainNotions.G.LatticeSystems.delta
  split_ifs with h1 h2
  · exact hA i h1.choose ξ hξ
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩

theorem mRatSpan_inv (h2 : G.FinClasses) (hE : EquivSys G G.P.HtupW) (hA : RatActG G e) (hH : HRatInv G e) :
    MRatSpan G.P G.comp e G.M := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro F hF
    obtain ⟨reps, hR⟩ := jd_reps G h2
    rw [jdI_decomp G reps hR G.P.HtupW F hF]
    refine Submodule.sum_mem _ fun r hr => ?_
    have hlat : G.P.IsLatTup r.2 := hR.1 r hr
    have hval : F r.1 r.2 ∈ G.P.HtupW r.2 := ((jd_fmem G G.P.HtupW F).1 hF r.1).1 r.2 hlat
    have hsp : F r.1 r.2 ∈ Submodule.span G.O {ξ | ξ ∈ G.P.HtupW r.2 ∧ InvAt G r.1 r.2 ξ ∧ RatX G e ξ} :=
      hH r.1 r.2 hlat ⟨hval, inv_of_mem G G.P.HtupW F hF r.1 r.2⟩
    generalize F r.1 r.2 = x at hsp
    induction hsp using Submodule.span_induction with
    | mem ξ hξ =>
      have hm : delta G r.1 r.2 ξ ∈ G.M := jdI_mem G G.P.HtupW hE r.1 r.2 hlat ξ hξ.1 hξ.2.1
      exact Submodule.subset_span
        ⟨⟨delta G r.1 r.2 ξ, Submodule.subset_span hm, deltaI_rat G e hA r.1 r.2 ξ hξ.2.2⟩, hm, rfl⟩
    | zero =>
      have : delta G r.1 r.2 (0 : G.P.Xsp) = 0 := by
        have := jd_smul G r.1 r.2 0 0
        simpa using this
      rw [this]; exact Submodule.zero_mem _
    | add y z _ _ h1' h2' => rw [jd_add]; exact Submodule.add_mem _ h1' h2'
    | smul a y _ h1' => rw [jd_smul]; exact Submodule.smul_mem _ _ h1'

end Formalism.L2.G.Cmp
