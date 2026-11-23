import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GpMfixLeU

noncomputable section

open scoped Classical

set_option linter.style.haveILetI false

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula
  IsDedekindDomain

section GP3

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V}

theorem gp_div (g : ℕ) : ∀ v ∈ Ideal.span {(g : 𝓞 E)} • Λ, ((g : E))⁻¹ • v ∈ Λ := by
  intro v hv
  refine Submodule.smul_induction_on hv ?_ ?_
  · intro a ha w hw
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    by_cases hg : (g : E) = 0
    · rw [hg, inv_zero, zero_smul]
      exact zero_mem _
    · have : ((g : E))⁻¹ • ((t * (g : 𝓞 E)) • w) = t • w := by
        rw [gp_osmul, gp_osmul, map_mul, map_natCast, smul_smul, mul_comm (algebraMap (𝓞 E) E t),
          ← mul_assoc, inv_mul_cancel₀ hg, one_mul]
      rw [this]
      exact Submodule.smul_mem _ t hw
  · intro a b ha hb
    rw [smul_add]
    exact add_mem ha hb

theorem gp_locΛ_map (p : Ideal (𝓞 E)) [p.IsPrime] {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {v : S.V}
    (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ) : n v ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ := by
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff p Λ v).1 hv
  exact (mem_localization_iff p Λ _).2 ⟨s, hs, by rw [← gp_map_osmul]; exact autLam_maps hn hv⟩

theorem gp_gen_mem (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) {F : LFlag S r T} {F' : LFlag S r T'}
    {ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)} (hξ : AdmWit Λ g F F' ξ) (hP : (g : 𝓞 E) ∈ P.asIdeal)
    (b : Fin (r + 1)) : (haveI := P.isPrime; gpGen g F F' ξ b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  haveI := P.isPrime
  have h := hξ.2.2 b P hP
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff P.asIdeal _ _).1 h
  refine (mem_localization_iff P.asIdeal Λ _).2 ⟨s, hs, ?_⟩
  unfold gpGen
  rw [gp_smul_comm]
  exact gp_div g _ hv

theorem gp_Mfix_map {F : LFlag S r T} (hl : IsLift Λ F) {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    ∀ v ∈ gpMfix Λ F, n v ∈ gpMfix Λ F := by
  have h : gpMfix Λ F ≤ (gpMfix Λ F).comap (fO n) := by
    refine Submodule.span_le.2 ?_
    rintro w (hw | hw)
    · obtain ⟨h1, h2⟩ := mem_XLam.1 hw
      exact Submodule.subset_span (Set.mem_union_left _ (mem_XLam.2 ⟨autLam_maps hn.1 h1, nlam_maps_X hn _ h2⟩))
    · rw [Set.mem_singleton_iff] at hw
      rw [hw, hl.2]
      show n F.fl.z ∈ gpMfix Λ F
      have h1 : F.fl.z ∈ gpMfix Λ F := by
        refine Submodule.subset_span (Set.mem_union_right _ ?_)
        rw [Set.mem_singleton_iff, hl.2]
      have h2 : n F.fl.z - F.fl.z ∈ gpMfix Λ F :=
        Submodule.subset_span (Set.mem_union_left _ (nlam_z_sub hn hl.1))
      have := Submodule.add_mem _ h2 h1
      rwa [sub_add_cancel] at this
  exact fun v hv => h hv

theorem gp_Mfix_map_loc (p : Ideal (𝓞 E)) [p.IsPrime] {F : LFlag S r T} (hl : IsLift Λ F)
    {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) {v : S.V} (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p (gpMfix Λ F)) :
    n v ∈ Formalism.HermitianLatticesTheory.localization₂ p (gpMfix Λ F) := by
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff p _ v).1 hv
  exact (mem_localization_iff p _ _).2 ⟨s, hs, by rw [← gp_map_osmul]; exact gp_Mfix_map hl hn _ hv⟩

theorem gp_e_mem (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) {F' : LFlag S r T'} (hc : IsFixedConv Λ g F')
    (hP : (g : 𝓞 E) ∈ P.asIdeal) (a : Fin r) :
    (haveI := P.isPrime; F'.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F')) := by
  haveI := P.isPrime
  obtain ⟨c, -, hc1, heq⟩ := hc.1 P
  rw [heq]
  have : c a • F'.fl.e a ∈ Submodule.span (𝓞 E) (Set.range fun a => c a • F'.fl.e a) :=
    Submodule.subset_span ⟨a, rfl⟩
  rw [hc1 hP a, one_smul] at this
  exact gp_le_locP _ _ this

theorem gp_XLam_le (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) {F' : LFlag S r T'} (hc : IsFixedConv Λ g F')
    (hP : (g : 𝓞 E) ∈ P.asIdeal) (K : Submodule (𝓞 E) S.V)
    (hK : ∀ s ∈ P.asIdeal.primeCompl, ∀ k : S.V, s • k ∈ K → k ∈ K) (he : ∀ a, F'.fl.e a ∈ K) :
    (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F') ≤ K) := by
  haveI := P.isPrime
  obtain ⟨c, -, hc1, heq⟩ := hc.1 P
  rw [heq]
  intro v hv
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff P.asIdeal _ v).1 hv
  refine hK s hs v ((Submodule.span_le.2 ?_) hv)
  rintro _ ⟨a, rfl⟩
  show c a • F'.fl.e a ∈ K
  rw [hc1 hP a, one_smul]
  exact he a

theorem gp_frame_loc (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) {F' : LFlag S r T'} (hl : IsLift Λ F')
    (hc : IsFixedConv Λ g F') (hP : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin (r + 1)) :
    (haveI := P.isPrime; frame F' b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  haveI := P.isPrime
  induction b using Fin.lastCases with
  | last =>
    rw [frame_last]
    exact gp_le_locP _ _ hl.1
  | cast i =>
    rw [frame_castSucc]
    refine locP_mono _ (fun v hv => (mem_XLam.1 hv).1) (gp_e_mem P g hc hP i)

theorem gp_frameAct_mem (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) {F : LFlag S r T} (hl : IsLift Λ F)
    (hc : IsFixedConv Λ g F) (hP : (g : 𝓞 E) ∈ P.asIdeal)
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (b : Fin (r + 1)) :
    (haveI := P.isPrime; frameAct (frame F) ξ b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (gpMfix Λ F)) := by
  haveI := P.isPrime
  unfold frameAct
  refine Submodule.sum_mem _ fun a _ => ?_
  have e : ((ξ a b : 𝓞 E) : E) • frame F a = ξ a b • frame F a := (gp_osmul _ _).symm
  rw [e]
  refine Submodule.smul_mem _ _ ?_
  induction a using Fin.lastCases with
  | last =>
    rw [frame_last]
    refine gp_le_locP _ _ (Submodule.subset_span (Set.mem_union_right _ ?_))
    rw [Set.mem_singleton_iff, hl.2]
  | cast i =>
    rw [frame_castSucc]
    exact locP_mono _ (show XLam Λ F ≤ gpMfix Λ F from fun v hv => Submodule.subset_span
      (Set.mem_union_left _ hv)) (gp_e_mem P g hc hP i)

theorem gp_nlam_sub_X {F' : LFlag S r T'} {m : S.V ≃ₗ[E] S.V} (hm : m ∈ NLam Λ F') (b : Fin (r + 1)) :
    m (frame F' b) - frame F' b ∈ Xsp F' := by
  induction b using Fin.lastCases with
  | last =>
    rw [frame_last]
    exact hm.2.2 _ (z_mem_orth F')
  | cast i =>
    rw [frame_castSucc]
    exact Xflag_le_X F' i.1 (hm.2.1 i.1 _ (e_mem_Xflag F' i))

theorem gp_loc_X (p : Ideal (𝓞 E)) [p.IsPrime] {F' : LFlag S r T'} {v : S.V} (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ)
    (hX : v ∈ Xsp F') : v ∈ Formalism.HermitianLatticesTheory.localization₂ p (XLam Λ F') := by
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff p Λ v).1 hv
  refine (mem_localization_iff p _ v).2 ⟨s, hs, mem_XLam.2 ⟨hv, ?_⟩⟩
  rw [gp_osmul]
  exact Submodule.smul_mem _ _ hX

end GP3

end PI.TermAttrConst.UnitaryGroupMassFormula
