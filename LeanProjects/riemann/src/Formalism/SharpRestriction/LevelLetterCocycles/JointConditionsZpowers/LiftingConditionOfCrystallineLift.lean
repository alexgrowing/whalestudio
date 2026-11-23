import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

open NumberField IsDedekindDomain

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'}

theorem LiftF_mono (F : LatHom L L') {e e' : ℕ} (he : e ≤ e') (h : F.LiftF PD e) : F.LiftF PD e' := by
  intro c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact (F.ImF PD).smul_mem _ (h c hc)

end Gen

section Fields

variable {l : ℕ} [Fact l.Prime]

theorem Ks_mono (K : FinExt l) {s s' : ℕ} (h : s ≤ s') : Ks K s ≤ Ks K s' := by
  unfold Formalism.BasicNotions.Loc.Ks
  refine sup_le_sup_left ?_ _
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  apply IntermediateField.subset_adjoin
  simp only [Set.mem_setOf_eq] at hx ⊢
  obtain ⟨c, hc⟩ := pow_dvd_pow l h
  rw [hc, pow_mul, hx, one_pow]

theorem caseA_of_unram (P : LocPrime l) (H : LocHW l P) {K : FinExt l} {LL : FinExt l} (h : Good K 1 LL)
    (hK : K.1 ≤ MaximalUnramifiedExtension l) (hl : l ≠ 2) : Formalism.MainNotions.LiftingTheory.CaseA (H.W K 1 LL h) := by
  refine ⟨⟨RingHom.injective (algebraMap ↥(K0 K) ↥K.1), fun y =>
    ⟨⟨(y : Om l), IntermediateField.mem_inf.mpr ⟨y.2, hK y.2⟩⟩, by ext; rfl⟩⟩, H.W_s K 1 LL h, ?_⟩
  rw [P.PD_p K]
  exact hl

end Fields

theorem Hmax_const_le (n M h : ℕ) : Formalism.MainNotions.LiftingTheory.Hmax n (fun _ => M) (fun _ => h) ≤ M + h := by
  unfold Formalism.MainNotions.LiftingTheory.Hmax
  exact Finset.sup_le fun _ _ => le_rfl

def LiftWin (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (M h : ℕ) : Prop :=
  ∀ T : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL),
    IsSubquotOfSums T.ρ (fun x : D.nd.X i => ⇑(Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) →
    IsCrys (Br.PD D.loc D.nbr i w hw) T.ρ ∧
      ∀ τ, JumpsInV (Br.PD D.loc D.nbr i w hw) T.ρ τ (Set.Icc (-(M : ℤ)) h)

theorem lifting_condition_of_crystalline_lift (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (M h : ℕ) (CA CB CK : ℝ) (hCA : 0 ≤ CA)
    (h54 : Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK) (hl : D.nd.l i ≠ 2)
    (hur : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
      (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i))
    (hwin : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
      ∀ C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw, C.IsGood → LiftWin D i r w hw C M h)
    (he : ∀ w ∈ dc.col, CA * (1 + ((M + h : ℕ) : ℝ) / (D.nd.l i : ℝ) +
      (1 + Real.logb (D.nd.l i) (((M + h : ℕ) : ℝ) + 1))) ≤ (e' w : ℝ)) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.LiftExponentAtPlaces (D := D) i r dc e' := by
  intro w hw hcol C hC

  have hgood : Good (D.nbr i w hw).Kw 1 C.LL := by
    refine ⟨le_rfl, fun h2 => absurd h2 hl, ?_, ?_⟩
    · unfold Formalism.BasicNotions.Loc.Ks Formalism.BasicNotions.Loc.K0
      exact le_sup_of_le_left (le_inf le_rfl (hur w hw hcol))
    · intro τ x
      obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits' τ (fun (y : Om (D.nd.l i)) =>
        ⟨(Algebra.IsIntegral.isIntegral (R := ℚ_[D.nd.l i]) (A := Om (D.nd.l i)) y).tower_top,
          by first | exact IsAlgClosed.splits _ | exact IsAlgClosed.splits_codomain' _ | exact IsAlgClosed.splits_of_splits _ | simp⟩)
      have e : φ x = τ x := by
        rw [← hφ]
        rfl
      rw [← e]
      have hle : Ks (D.nbr i w hw).Kw 1 ≤ C.LL.1.comap φ := by
        unfold Formalism.BasicNotions.Loc.Ks Formalism.BasicNotions.Loc.K0
        refine sup_le ?_ ?_
        · intro y hy
          show φ y ∈ C.LL.1
          exact C.le ((D.nbr i w hw).LL_split (φ.comp (D.nbr i w hw).Kw.1.val)
            ⟨y, (IntermediateField.mem_inf.mp hy).1⟩)
        · rw [IntermediateField.adjoin_le_iff]
          intro y hy
          show φ y ∈ C.LL.1
          apply hC
          have hy1 : y ^ D.nd.l i = 1 := by simpa using hy
          obtain ⟨c, hc⟩ := Nat.dvd_lcm_left (D.nd.l i) D.host.condN
          rw [← map_pow, hc, pow_mul, hy1, one_pow, map_one]
      exact hle x.2
  have hA : Formalism.MainNotions.LiftingTheory.CaseA ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hgood) :=
    caseA_of_unram (D.loc (D.nd.l i)) (HW (D.nd.l i)) hgood (hur w hw hcol) hl
  unfold LiftAt
  intro V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 L1 hc1 hs1 V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 L2 hc2 hs2 Fm hFm
  let T1 : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) := ⟨V1, ρ1, hc1, L1⟩
  let T2 : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) := ⟨V2, ρ2, hc2, L2⟩
  have hw1 := hwin w hw hcol C hC T1 hs1
  have hw2 := hwin w hw hcol C hC T2 hs2
  have hJ : Formalism.MainNotions.LiftingTheory.JumpsLet ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hgood) T1 (fun _ => M) (fun _ => h) :=
    fun _ τ _ => hw1.2 τ
  have hSur : Formalism.MainNotions.LiftingTheory.Sur ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hgood) (T₁ := T1) (T₂ := T2) Fm :=
    ⟨hw1.1, hw2.1, hFm⟩

  have hlift := h54.1 (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hgood hA T1 T2 Fm (fun _ => M) (fun _ => h) hSur hJ
  have hbound := (h54.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hgood T1 (fun _ => M) (fun _ => h) hw1.1 hJ).1 hA
  rw [(D.loc (D.nd.l i)).PD_p] at hbound
  have hH := Hmax_const_le (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) M h
  have hl1 : (1 : ℝ) < D.nd.l i := by exact_mod_cast (D.nd.lPrime i).out.one_lt
  have hHr : (Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M) (fun _ => h) : ℝ) ≤
      ((M + h : ℕ) : ℝ) := by exact_mod_cast hH
  have hlog : Real.logb (D.nd.l i)
      ((Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M) (fun _ => h) : ℝ) + 1) ≤
      Real.logb (D.nd.l i) (((M + h : ℕ) : ℝ) + 1) :=
    Real.logb_le_logb_of_le hl1 (by positivity) (by linarith)
  have hdiv : (Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M) (fun _ => h) : ℝ) /
      (D.nd.l i : ℝ) ≤ ((M + h : ℕ) : ℝ) / (D.nd.l i : ℝ) := by
    gcongr
  have hmono := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (le_refl (1 : ℝ)) hdiv) (add_le_add (le_refl (1 : ℝ)) hlog)) hCA
  have hle : Formalism.MainNotions.LiftingTheory.ePA (D.nd.l i)
      (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M))
      (Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M) (fun _ => h))
      (Formalism.MainNotions.LiftingTheory.jumpSet ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hgood) T1
        (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M))
        (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => h))) ≤ e' w := by
    exact_mod_cast hbound.trans (hmono.trans (he w hcol))
  rw [(D.loc (D.nd.l i)).PD_p] at hlift
  exact LiftF_mono _ _ hle hlift

end Formalism.MainNotions.N
