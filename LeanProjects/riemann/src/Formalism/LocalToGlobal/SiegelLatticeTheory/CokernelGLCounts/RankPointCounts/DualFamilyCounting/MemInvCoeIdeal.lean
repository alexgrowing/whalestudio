import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.SharpRestriction.CuspSpanNormBounds.RowsOneGenusOfLocalDiscriminant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SplitPrimeCounts.LsSetresInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDet

noncomputable section

open NumberField Module IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Frac

variable {K : Type} [Field K] [NumberField K]

theorem mem_inv_coeIdeal {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) (x : K) :
    x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))⁻¹ ↔
      ∀ y ∈ J, ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = x * algebraMap (𝓞 K) K y := by
  have hJ' : (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  rw [FractionalIdeal.mem_inv_iff hJ']
  constructor
  · intro h y hy
    exact (FractionalIdeal.mem_one_iff _).1
      (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨y, hy, rfl⟩))
  · intro h y hy
    obtain ⟨y0, hy0, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_one_iff _).2 (h y0 hy0)

theorem exists_loc_gen {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) (P : Ideal (𝓞 K)) [hP : P.IsPrime] :
    ∃ c : K, c ≠ 0 ∧
      (∀ x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))⁻¹,
        ∃ o : 𝓞 K, x = algebraMap (𝓞 K) K o * c) ∧
      ∃ s : 𝓞 K, s ∉ P ∧
        algebraMap (𝓞 K) K s * c ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))⁻¹ := by
  have hlt : J * P < J := by
    refine lt_of_le_of_ne Ideal.mul_le_left ?_
    intro h
    have h2 : J * P = J * ⊤ := by rw [Ideal.mul_top]; exact h
    exact hP.ne_top (mul_left_cancel₀ hJ h2)
  obtain ⟨a, haJ, haP⟩ := SetLike.exists_of_lt hlt
  have ha0 : a ≠ 0 := fun h => haP (h ▸ Submodule.zero_mem _)
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h; exact ha0 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).1 h)
  obtain ⟨Q, hQ⟩ : J ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 haJ)
  have hQP : ¬ Q ≤ P := by
    intro hle
    apply haP
    have h1 : a ∈ Ideal.span {a} := Ideal.mem_span_singleton_self a
    rw [hQ] at h1
    exact Ideal.mul_mono_right hle h1
  obtain ⟨s, hsQ, hsP⟩ := Set.not_subset.1 hQP
  refine ⟨(algebraMap (𝓞 K) K a)⁻¹, inv_ne_zero haK, ?_, s, hsP, ?_⟩
  · intro x hx
    obtain ⟨o, ho⟩ := (mem_inv_coeIdeal hJ x).1 hx a haJ
    refine ⟨o, ?_⟩
    rw [ho]
    field_simp
  · rw [mem_inv_coeIdeal hJ]
    intro y hy
    have hsy : y * s ∈ J * Q := Ideal.mul_mem_mul hy hsQ
    rw [← hQ] at hsy
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hsy
    refine ⟨t, ?_⟩
    have h3 := congrArg (algebraMap (𝓞 K) K) ht
    rw [map_mul, map_mul] at h3
    field_simp
    linear_combination h3

end Frac

section Diff

variable (D : Formalism.BasicNotions.D7)

abbrev ddI : Ideal (𝓞 D.host.E) :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))

abbrev Nd : ℕ := Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F))

theorem Nd_mem : ((Nd D : ℕ) : 𝓞 D.host.E) ∈ ddI D := by
  have h := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
    (Ideal.absNorm_mem (differentIdeal ℤ (𝓞 D.host.F)))
  simpa using h

theorem Nd_ne : (Nd D : ℕ) ≠ 0 := by
  intro h
  rw [Nd, Ideal.absNorm_eq_zero_iff] at h
  exact differentIdeal_ne_bot h

theorem ddI_ne : ddI D ^ 0 ≠ ⊥ ∧ ∀ k : ℕ, ddI D ^ k ≠ ⊥ := by
  have h1 : ddI D ≠ ⊥ := by
    intro h
    have := Nd_mem D
    rw [h, Ideal.mem_bot] at this
    exact Nd_ne D (by exact_mod_cast this)
  exact ⟨by simp, fun k => pow_ne_zero k h1⟩

theorem g_ne : ((gS D : ℕ) : D.host.E) ≠ 0 := by
  rw [gS, Nat.cast_mul]
  exact mul_ne_zero (Nat.cast_ne_zero.2 (D.host.g_prime 0).ne_zero)
    (Nat.cast_ne_zero.2 (D.host.g_prime 1).ne_zero)

theorem Nd_not_mem {P : Ideal (𝓞 D.host.E)} [hP : P.IsPrime] (hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P) (k : ℕ) :
    ((Nd D ^ k : ℕ) : 𝓞 D.host.E) ∉ P := by
  intro hN
  have key : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∉ P := by
    intro i hi
    have hc : Nat.Coprime (Nd D ^ k) (D.host.g i) :=
      Nat.Coprime.pow_left k (Formalism.L2.SG.SplitPrimeNormLemmas.IntG.coprime_gi i)
    have hb := Nat.gcd_eq_gcd_ab (Nd D ^ k) (D.host.g i)
    rw [hc] at hb
    have hb' := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hb
    push_cast at hb'
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one, hb']
    exact P.add_mem (P.mul_mem_right _ (by exact_mod_cast hN)) (P.mul_mem_right _ hi)
  have hg' : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ P := by
    simpa [gS, Nat.cast_mul] using hg
  rcases hP.mem_or_mem hg' with h | h
  · exact key 0 h
  · exact key 1 h

theorem ddS_zpow (a : Fin D.R.rS) :
    ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) =
      ((ddI D ^ (D.R.rS - a) : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
  have ha : (a : ℕ) ≤ D.R.rS := a.2.le
  rw [show -((D.R.rS : ℤ) - (a : ℕ)) = -(((D.R.rS - a : ℕ) : ℕ) : ℤ) by push_cast [Nat.cast_sub ha]; ring,
    zpow_neg, zpow_natCast, FractionalIdeal.coeIdeal_pow]
  rfl

theorem one_mem_ddS (a : Fin D.R.rS) : (1 : D.host.E) ∈ ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) := by
  rw [ddS_zpow, mem_inv_coeIdeal ((ddI_ne D).2 _)]
  intro y _
  exact ⟨y, by simp⟩

theorem Nd_mul_mem (a : Fin D.R.rS) {x : D.host.E} (hx : x ∈ ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o =
      algebraMap (𝓞 D.host.E) D.host.E ((Nd D ^ (D.R.rS - a) : ℕ) : 𝓞 D.host.E) * x := by
  rw [ddS_zpow, mem_inv_coeIdeal ((ddI_ne D).2 _)] at hx
  obtain ⟨o, ho⟩ := hx _ (by exact Ideal.pow_mem_pow (Nd_mem D) _)
  exact ⟨o, by rw [ho, mul_comm, Nat.cast_pow]⟩

end Diff

section XS

variable (D : Formalism.BasicNotions.D7) {T : D.host.E} (F : FlagG (VS D) D.R.rS T)

theorem smulO (s : 𝓞 D.host.E) (x : (VS D).V) :
    s • x = (algebraMap (𝓞 D.host.E) D.host.E s) • x := (algebraMap_smul D.host.E s x).symm

theorem xs_gen {y : (VS D).V} (hy : y ∈ XS D F) (P : Submodule (𝓞 D.host.E) (VS D).V)
    (h : ∀ (a : Fin D.R.rS) (x : D.host.E), x ∈ ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) → x • F.e a ∈ P) : y ∈ P := by
  refine (Submodule.span_le.2 ?_) hy
  rintro _ ⟨a, x, hx, rfl⟩
  exact h a x hx

theorem e_mem_XS (a : Fin D.R.rS) : F.e a ∈ XS D F :=
  Submodule.subset_span ⟨a, 1, one_mem_ddS D a, by simp⟩

theorem XS_le_X : XS D F ≤ F.X.restrictScalars (𝓞 D.host.E) := by
  intro y hy
  refine xs_gen D F hy _ fun a x _ => ?_
  exact F.X.smul_mem x (Submodule.subset_span ⟨a, rfl⟩)

theorem XS_le_locP_e (P : Ideal (𝓞 D.host.E)) [P.IsPrime] (hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P) :
    XS D F ≤ Formalism.HermitianLatticesTheory.localization₂ P (Submodule.span (𝓞 D.host.E) (Set.range F.e)) := by
  intro y hy
  refine xs_gen D F hy _ fun a x hx => ?_
  obtain ⟨o, ho⟩ := Nd_mul_mem D a hx
  refine ⟨((Nd D ^ (D.R.rS - a) : ℕ) : 𝓞 D.host.E), Nd_not_mem D hg _, ?_⟩
  rw [smulO, smul_smul, ← ho, ← smulO]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem xs_locGen (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ c : Fin D.R.rS → D.host.E, (∀ a, c a ≠ 0) ∧
      (((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ a, c a = 1) ∧
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XS D F) =
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F.e a))) := by
  have := P.isPrime
  by_cases hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · refine ⟨fun _ => 1, fun _ => one_ne_zero, fun _ _ => rfl, ?_⟩
    simp only [one_smul]
    refine le_antisymm (Formalism.L2.SG.Pf.locP_le_locP' (XS_le_locP_e D F P.asIdeal hg)) ?_
    refine Formalism.L2.SG.Pf.localization_mono' (Submodule.span_le.2 ?_)
    rintro _ ⟨a, rfl⟩
    exact e_mem_XS D F a
  · choose c hc0 hc1 hc2 using fun a : Fin D.R.rS =>
      exists_loc_gen ((ddI_ne D).2 (D.R.rS - a)) P.asIdeal
    refine ⟨c, hc0, fun h => absurd h hg, le_antisymm ?_ ?_⟩
    · refine Formalism.L2.SG.Pf.locP_le_locP' ?_
      intro y hy
      refine xs_gen D F hy _ fun a x hx => ?_
      rw [ddS_zpow] at hx
      obtain ⟨o, rfl⟩ := hc1 a x hx
      refine Formalism.L2.SG.Pf.le_locP' _ _ ?_
      rw [mul_smul, ← smulO]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · refine Formalism.L2.SG.Pf.locP_le_locP' (Submodule.span_le.2 ?_)
      rintro _ ⟨a, rfl⟩
      obtain ⟨s, hs, hsc⟩ := hc2 a
      refine ⟨s, hs, ?_⟩
      rw [smulO, smul_smul]
      exact Submodule.subset_span ⟨a, _, by rw [ddS_zpow]; exact hsc, rfl⟩

theorem XS_fg : (XS D F).FG := by
  refine Submodule.FG.of_le (Submodule.fg_span (Set.finite_range fun a : Fin D.R.rS =>
    (algebraMap (𝓞 D.host.E) D.host.E ((Nd D ^ (D.R.rS - a) : ℕ) : 𝓞 D.host.E))⁻¹ • F.e a)) ?_
  intro y hy
  refine xs_gen D F hy _ fun a x hx => ?_
  obtain ⟨o, ho⟩ := Nd_mul_mem D a hx
  have hN : algebraMap (𝓞 D.host.E) D.host.E ((Nd D ^ (D.R.rS - a) : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    rw [map_natCast]; exact_mod_cast pow_ne_zero _ (Nd_ne D)
  have : x • F.e a = o • ((algebraMap (𝓞 D.host.E) D.host.E ((Nd D ^ (D.R.rS - a) : ℕ) : 𝓞 D.host.E))⁻¹ • F.e a) := by
    rw [smulO, smul_smul, ho, mul_comm, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end XS

section Frames

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem sum_fvec {T : E} (F : FlagG S r T) (c : Fin r → E) (a : E) :
    ∑ i, (Fin.snoc (α := fun _ => E) c a : Fin (r + 1) → E) i • F.fvec i = ∑ i, c i • F.e i + a • F.z := by
  rw [Fin.sum_univ_castSucc]
  simp [FlagG.fvec]

theorem fvec_last {T : E} (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp [FlagG.fvec]

theorem fvec_cast {T : E} (F : FlagG S r T) (a : Fin r) : F.fvec (Fin.castSucc a) = F.e a := by
  simp [FlagG.fvec]

theorem mem_X_iff {T : E} (F : FlagG S r T) {x : S.V} : x ∈ F.X ↔ ∃ c : Fin r → E, ∑ i, c i • F.e i = x :=
  Submodule.mem_span_range_iff_exists_fun E

end Frames

section Indep

variable (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F1 : FlagG (VS D) D.R.rS T')

theorem totPos_ne {x : D.host.E} (hx : Formalism.MainNotions.S.LocalSplitGroups.TotPos x) : x ≠ 0 := by
  have : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n; positivity)
  obtain ⟨τ⟩ := this
  intro h
  have := hx τ
  rw [h, map_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem indep (hG : GZ T T' (Zhat F0 F1) ≠ 0) : LinearIndependent D.host.E (Sum.elim F0.fvec F1.fvec) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hdet := PI.UnitaryGroupMassFormula.CntFormula.gram_determinant_ne_zero D T T' (Zhat F0 F1) hG
  have hmv : (Ga T T' (Zhat F0 F1)).mulVec c = 0 := by
    funext a
    have h1 : (VS D).hT (Sum.elim F0.fvec F1.fvec a) (∑ i, c i • Sum.elim F0.fvec F1.fvec i) = 0 := by
      rw [hc, map_zero]
    rw [map_sum] at h1
    simp only [map_smul, smul_eq_mul] at h1
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ga_gram D F0 F1 a i, brS, mul_comm]
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hmv)

end Indep

end Formalism.L2.SG.Pf.Cnt.R3
