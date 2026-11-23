import Formalism.SharpRestriction.LevelLetterCocycles.CocyclesToWachVectorsBoundOfExtTool
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.MemZeroSubCoe
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Pass

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem finiteDimensional_filLev (c : ZMod n) (hfd : FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb c))) (u : ℤ) :
    FiniteDimensional LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 u) := by
  have hc : c - ((0 : ℕ) : ZMod n) = c := by simp
  haveI : FiniteDimensional LL
      ↥(Formalism.WeaklyAdmissibleFiltrations.FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb (c - ((0 : ℕ) : ZMod n)))) := by
    rw [hc]
    exact Submodule.finiteDimensional_of_le inf_le_right
  unfold Formalism.MainNotions.WachCoordinates.FilLev
  infer_instance

theorem multV_nonneg' [NeZero n] (hFD : Sh.FilDim W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hT : IsCrys PD T.ρ) (c : ZMod n) (τ : K →ₐ[Qp] LL) (hτ : Formalism.MainNotions.LiftingTheory.Over W τ c)
    (hfd : FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb c))) (k : ℤ) : 0 ≤ multV PD T.ρ τ k := by
  obtain ⟨-, hdim⟩ := hFD hA T hT c τ hτ
  have h1 := hdim k (k + 1) (by omega)
  have hI : Finset.Ico k (k + 1) = {k} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [hI, Finset.sum_singleton] at h1

  have hle : Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (k + 1) ≤ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 k := by
    unfold Formalism.MainNotions.WachCoordinates.FilLev
    apply Submodule.map_mono
    apply Submodule.map_mono
    apply inf_le_inf_right
    unfold Formalism.WeaklyAdmissibleFiltrations.FilCris
    apply inf_le_inf_left
    apply Submodule.comap_mono
    unfold Formalism.WeaklyAdmissibleFiltrations.FilV
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    clear hx
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      exact LinearMap.mem_range.mpr ⟨v ⊗ₜ ⟨(w : BdR), PD.Fil_anti k w.2⟩, by simp⟩
    | add y z hy hz =>
      rw [map_add]
      exact add_mem hy hz
  haveI := finiteDimensional_filLev W T c hfd k
  have h2 : Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (k + 1)) ≤
      Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 k) :=
    LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
  have h3 : ((Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (k + 1)) : ℕ) : ℤ) ≤
      Module.finrank LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T c 0 k) := by exact_mod_cast h2
  linarith

theorem sum_multV_le [NeZero n] (hFD : Sh.FilDim W) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ} (hS : SetCS W d T₁ T₂ F b S η m)
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (c : ZMod n) (hc : c ∈ evens n d) (τ : K →ₐ[Qp] LL)
    (hτ : Formalism.MainNotions.LiftingTheory.Over W τ c) (a : ℕ) (ha : a < b c) :
    ∑ k ∈ Finset.Ico (-(a : ℤ)) 0, multV PD T₂.ρ τ k ≤ (m : ℤ) := by
  have hjump := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS c τ hτ
  have hfd := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fd_letter₂ W hS c
  have hT₂ : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hev : (c.val + d) % 2 = 0 := by simpa [evens] using hc
  rw [← Finset.sum_filter_of_ne (p := fun k => k ∈ Finset.Icc (-(η : ℤ)) η)]
  · calc ∑ k ∈ (Finset.Ico (-(a : ℤ)) 0).filter (fun k => k ∈ Finset.Icc (-(η : ℤ)) η), multV PD T₂.ρ τ k
        ≤ ∑ k ∈ Finset.Icc (-(η : ℤ)) η, multV PD T₂.ρ τ k :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => (Finset.mem_filter.1 hk).2)
            (fun k _ _ => multV_nonneg' W T₂ hFD hS.1 hT₂ c τ hτ hfd k)
      _ ≤ (m : ℤ) := hS.2.2.2.2.2.2.2.1 c τ hτ
  · intro k hk hne
    have hj : IsJumpV PD T₂.ρ τ k := by
      by_contra hnj
      exact hne (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_multV_of_not_jump PD T₂.ρ τ k hnj)
    have hw := hjump k hj
    simp only [Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS, hev, if_true, Set.mem_union, Set.mem_Icc] at hw
    have hk' := Finset.mem_Ico.1 hk
    simp only [Finset.mem_Icc]
    omega

theorem step1Pass_pass [NeZero n] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ) (ζ : LL)
    (hζ : IsPrimitiveRoot ζ PD.p) (hEx : Sh.ExpRules W) (hER : Sh.ExpRing W) (hK : Sh.LemK W)
    (hFD : Sh.FilDim W) (c : ZMod n) (τ : K →ₐ[Qp] LL) (hτ : Formalism.MainNotions.LiftingTheory.Over W τ c)
    (hfd : FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb c))) [IsDomain O] [IsPrincipalIdealRing O]
    [IsFractionRing O LL] {FF : Type} [AddCommGroup FF] [Module O FF] [Module.Finite O FF]
    (u : FF →ₗ[O] W.DD T) (a m : ℕ)
    (hu : ∀ f, Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (u f) ∧ Formalism.MainNotions.LiftingTheory.qp W ^ a • u f ∈ W.N T ∧
      Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (W.γ T (u f) - u f))
    (hdim : ∑ k ∈ Finset.Ico (-(a : ℤ)) 0, multV PD T.ρ τ k ≤ (m : ℤ)) :
    (∀ (lenO : ℕ∞) (cc : ℝ) (A : Submodule O FF),
      ∃ B, PChain lenO m cc A B 1 0 ∧ ∀ f ∈ B, u f ∈ W.N T) ∧ (m = 0 → ∀ f, u f ∈ W.N T) := by
  have hlev : W.lev c ζ (Formalism.MainNotions.LiftingTheory.qp W ^ a) ≠ 0 := by
    obtain ⟨⟨w, hw, hq⟩, -, -⟩ := hER hA c ζ hζ
    rw [map_pow, hq, mul_pow]
    exact mul_ne_zero (pow_ne_zero _ hw.ne_zero) (pow_ne_zero _ PowerSeries.X_ne_zero)
  have R := hEx hA T hT c ζ hζ
  have hex : ∀ f, ∃! d, Sh.IsExp W T c ζ (u f) d := fun f => R.1 (u f) _ (hu f).2.1 hlev
  choose ex hexs huniq using hex
  have ex_add : ∀ f g, ex (f + g) = ex f + ex g := fun f g =>
    (huniq (f + g) _ (by rw [map_add]; exact R.2.2.1 _ _ _ _ (hexs f) (hexs g))).symm
  have ex_smul : ∀ (r : O) f, ex (r • f) = fun k => algebraMap O LL r • ex f k := fun r f =>
    (huniq (r • f) _ (by rw [map_smul]; exact R.2.2.2.1 r _ _ (hexs f))).symm
  set F0 := Formalism.MainNotions.WachCoordinates.FilLev W T c 0 0 with hF0
  set Fa := Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-(a : ℤ)) with hFa
  let φ : FF →+ (T.V ⊗[Qp] BdR) ⧸ F0 :=
    AddMonoidHom.mk' (fun f => Submodule.Quotient.mk (ex f 0)) (fun f g => by
      simp only [ex_add, Pi.add_apply, Submodule.Quotient.mk_add])
  have hφ : ∀ (r : O) f, φ (r • f) = algebraMap O LL r • φ f := by
    intro r f
    simp only [φ, AddMonoidHom.mk'_apply, ex_smul, Submodule.Quotient.mk_smul]
  have hLK : ∀ f, ex f 0 ∈ Fa ∧ (u f ∈ W.N T ↔ ex f 0 ∈ F0) := by
    intro f
    have hj : ∃ j : ℕ, ((PD.p : ℕ) : O) ^ j • (W.γ T (u f) - u f) ∈ W.N T := by
      obtain ⟨y, hy, -, he⟩ := (hu f).2.2
      exact ⟨0, by rw [pow_zero, one_smul, he]; exact (W.N T).smul_mem _ hy⟩
    exact (hK hA T hT c ζ hζ (u f) (ex f) (hu f).1 (hexs f) hj).2 a (hu f).2.1
  have hker : ∀ f, φ f = 0 ↔ u f ∈ W.N T := by
    intro f
    rw [(hLK f).2]
    exact Submodule.Quotient.mk_eq_zero _
  have := finiteDimensional_filLev W T c hfd (-(a : ℤ))
  have := finiteDimensional_filLev W T c hfd 0
  let Aq := Fa.map F0.mkQ
  have hle : F0 ≤ Fa := Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T c 0 (by omega : -(a : ℤ) ≤ 0)
  have hAq : finrank LL ↥Aq ≤ m := by
    let g := F0.mkQ ∘ₗ Fa.subtype
    have hr : LinearMap.range g = Aq := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hk : LinearMap.ker g = F0.comap Fa.subtype := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    have h1 := LinearMap.finrank_range_add_finrank_ker g
    rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h1
    have h2 := (hFD hA T hT c τ hτ).2 (-(a : ℤ)) 0 (by omega)
    rw [← hF0, ← hFa] at h2
    omega
  have hrange : ∀ f, φ f ∈ Aq := fun f => Submodule.mem_map_of_mem (hLK f).1
  refine ⟨fun lenO cc A => ?_, fun hm0 f => ?_⟩
  · let φA : ↥A →+ (T.V ⊗[Qp] BdR) ⧸ F0 := φ.comp A.subtype.toAddMonoidHom
    have hφA : ∀ (r : O) (x : ↥A), φA (r • x) = algebraMap O LL r • φA x := fun r x => hφ r x
    have hm : finrank LL ↥(Submodule.span LL (Set.range φA)) ≤ m := by
      have : FiniteDimensional LL ↥Aq := inferInstance
      refine le_trans (Submodule.finrank_mono ?_) hAq
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hrange x
    refine ⟨Formalism.MainNotions.N.Pv.LocalLengthBound.zeroSub A φA hφA,
      Formalism.MainNotions.N.Pv.LocalLengthBound.pchain_of_gen (Formalism.MainNotions.N.Pv.LocalLengthBound.pstep_rank A φA hφA hm), ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (hker _).1 hy
  · subst hm0
    have h0 : Aq = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have := hrange f
    rw [h0, Submodule.mem_bot] at this
    exact (hker f).1 this

end Pass

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
