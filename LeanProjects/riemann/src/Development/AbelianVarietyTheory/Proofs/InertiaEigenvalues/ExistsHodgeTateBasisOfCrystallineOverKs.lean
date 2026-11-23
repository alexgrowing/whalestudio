import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateInvariantsCyclotomicTwistStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodDataStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineCyclotomicLevelOfFinrankInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteJumpsInfFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFamilyAdaptedToSeparatedFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerreTateLinearIndependentOfWeightwiseStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwistStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilInvariantJumpDescendsFinExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicBasisGaloisLatticeSameMatricesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamTensorCoordinatesOfBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamInvariantsCoordinatesFinrankEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKsOfFinExt
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.HTBasisEx

variable {l : ℕ} [Fact l.Prime]

theorem basis_of_invariants (P : LocPrime l) (AI : LocAinf l P) (Θ : ThetaL P AI) (K : FinExt l)
    (s : ℕ) (hs : Lev l s) (E : FinExt l) (hE : E.1 = Ks K s) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l]) (D : Submodule ↥E.1 (Fin d → P.R.BdR))
    (hD : ∀ y ∈ D, ∀ g ∈ GK E,
      ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y)
    (hfin : Module.Finite ↥E.1 ↥D) (hd : Module.finrank ↥E.1 ↥D = d) :
    ∃ (e : Fin d → Fin d → PadicComplex l) (u : Fin d → ℤ), LinearIndependent (PadicComplex l) e ∧
      (∀ k, ∃ y ∈ D, (∀ i, y i ∈ (P.PD E).Fil (u k)) ∧ ¬ ∀ i, y i ∈ (P.PD E).Fil (u k + 1)) ∧
      ∀ σ ∈ GK E, ∀ k, twAct AI.actC P.χQ (u k)
        (fun g => (M g).map (algebraMap ℚ_[l] (PadicComplex l))) σ (e k) = e k := by
  classical
  obtain ⟨sy, hsy⟩ := GlobalTheory.T.exists_deRhamFil_graded_symbol_to_tate_twist l P AI Θ E
  have hsum : ∀ (a : ℤ) (t : Finset (Fin d)) (f : Fin d → P.R.BdR),
      (∀ j ∈ t, f j ∈ (P.PD E).Fil a) → sy a (∑ j ∈ t, f j) = ∑ j ∈ t, sy a (f j) := by
    intro a t f
    induction t using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.sum_empty]
      exact ((hsy a).2.2.1 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)
    | insert j t hj ih =>
      intro hf
      have ht : ∀ j ∈ t, f j ∈ (P.PD E).Fil a := fun j h => hf j (Finset.mem_insert_of_mem h)
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        (hsy a).1 _ (hf j (Finset.mem_insert_self _ _)) _ (Submodule.sum_mem _ ht), ih ht]
  obtain ⟨x, u, hx, hind⟩ := GlobalTheory.T.exists_family_adapted_to_separated_filtration ↥E.1 (Fin d → P.R.BdR) D
    (fun a => Submodule.pi Set.univ fun _ => (P.PD E).Fil a) d hfin hd
    (fun a y hy i hi => (P.PD E).Fil_anti a (hy i hi))
    (by
      intro y
      choose n hn using fun i => (P.PD E).Fil_exh (y i)
      have hanti : Antitone (P.PD E).Fil := antitone_int_of_succ_le (P.PD E).Fil_anti
      obtain ⟨b, hb⟩ := (Set.finite_range n).bddBelow
      exact ⟨b, fun i _ => hanti (hb ⟨i, rfl⟩) (hn i)⟩)
    (fun y hy => funext fun i => (P.PD E).Fil_sep _ fun a => hy a i (Set.mem_univ i))
  have hxF : ∀ k i, x k i ∈ (P.PD E).Fil (u k) := fun k i => (hx k).2 i (Set.mem_univ i)
  have hact : ∀ σ ∈ GK E, ∀ k, twAct AI.actC P.χQ (u k)
      (fun g => (M g).map (algebraMap ℚ_[l] (PadicComplex l))) σ (fun i => sy (u k) (x k i)) =
        fun i => sy (u k) (x k i) := by
    intro σ hσ k
    funext i
    have hg : ∀ j, P.actQdR σ (x k j) ∈ (P.PD E).Fil (u k) := fun j => by
      rw [← P.PD_actdR E ⟨σ, hσ⟩]
      exact (P.PD E).Fil_G _ _ _ (hxF k j)
    have h1 := congrFun (hD _ (hx k).1 σ hσ) i
    conv_rhs => rw [← h1]
    simp only [twAct, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum _ _ _ (fun j _ => by
      rw [← Algebra.smul_def]
      exact ((P.PD E).Fil (u k)).smul_of_tower_mem _ (hg j)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, (hsy _).2.1 _ _ (hg j),
      (hsy _).2.2.2 σ _ (hxF k j), IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l)]
    have hc : ∀ c : Om l, (c : PadicComplex l) = algebraMap (Om l) (PadicComplex l) c :=
      fun _ => rfl
    rw [hc]
    exact mul_left_comm _ _ _
  refine ⟨fun k i => sy (u k) (x k i), u, ?_, fun k => ⟨x k, (hx k).1, hxF k, fun h => ?_⟩, hact⟩
  · refine GlobalTheory.T.serreTate_linearIndependent_of_weightwise l AI.actC P.χQ (GK E) E.1 ?_ d d _ _ u hact ?_
    · intro i y hy
      have := GlobalTheory.T.tate_invariants_cyclotomic_twist l AI.actC P.χQ ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K s hs i y
        (by intro g hg; apply hy; unfold GK; rw [hE]; exact hg)
      rwa [hE]
    · intro a c hc h0
      refine hind a c hc fun i _ => ?_
      have hm : ∀ k, c k • x k i ∈ (P.PD E).Fil a := by
        intro k
        by_cases hk : u k = a
        · exact Submodule.smul_mem _ _ (hk ▸ hxF k i)
        · rw [hc k hk, zero_smul]; exact Submodule.zero_mem _
      rw [Finset.sum_apply]
      refine ((hsy a).2.2.1 _ (Submodule.sum_mem _ fun k _ => hm k)).1 ?_
      rw [hsum a _ _ fun k _ => hm k]
      have h1 := congrFun h0 i
      rw [Finset.sum_apply, Pi.zero_apply] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : u k = a
      · subst hk
        exact (by rw [Pi.smul_apply, Algebra.smul_def]; exact (hsy _).2.1 _ _ (hxF k i))
      · simp only [Pi.smul_apply, hc k hk, zero_smul, ZeroMemClass.coe_zero, smul_eq_mul]
        rw [((hsy a).2.2.1 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)]
        simp
  · have := hind (u k) (Pi.single k 1) (fun j hj => Pi.single_eq_of_ne (fun e => hj (by rw [e])) _)
      (by
        intro i _
        simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        exact h i) k
    simp at this

set_option maxHeartbeats 1600000 in

theorem htBasis_of_isCrys (P : LocPrime l) (AI : LocAinf l P) (Θ : ThetaL P AI) (K : FinExt l)
    (s : ℕ) (hs : Lev l s) (E : FinExt l) (hEs : E.1 = Ks K s) (hle : K.1 ≤ E.1) (LL : FinExt l)
    (h7K : fontCore (P.PD K)) (h7E : fontCore (P.PD E))
    (T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hcrys : IsCrys (P.PD E) (T'.ρ.comp (Subgroup.inclusion (GK_le hle))))
    {d : ℕ} (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (hM : IsMat K LL T' M A)
    (m : ℕ) (hm : s ≤ m) :
    {a : ℤ | DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≠
      DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) a}.Finite ∧
    HTBasis AI.actC P.χQ (Gj K m) M
      {a : ℤ | DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≠
        DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) a} := by
  have hLL : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨bV, hbV⟩ := GlobalTheory.T.exists_padic_basis_galoisLattice_same_matrices l K LL T' d M A hM
  let ρ' : Representation ↥LL.1 ↥(GK E) T'.V := T'.ρ.comp (Subgroup.inclusion (GK_le hle))
  let AK : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := { V := T'.V, ρ := T'.ρ, cont := T'.cont }
  let AE : GRep ↥(GK E) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := T'.V, ρ := ρ'
      cont := fun x => (T'.cont x).comp (continuous_inclusion (GK_le hle)) }
  have hK := h7K _ _ (GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt l LL) AK
  have hE := h7E _ _ (GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt l LL) AE
  have hanti : ∀ a, FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≤ FilV (P.PD K) a := by
    obtain ⟨Φ, h1, -⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD K) T'.ρ bV
    intro a z hz
    exact (h1 a z).2 fun i => (P.PD K).Fil_anti a ((h1 _ z).1 hz i)
  refine ⟨GlobalTheory.T.finite_setOf_inf_filtration_ne_succ _ _ (DdR (P.PD K) T'.ρ) (fun a => FilV (P.PD K) a) hK.2.1.1 hanti, ?_⟩
  classical
  let M0 : GQ l → Matrix (Fin d) (Fin d) ℚ_[l] := fun g =>
    if hg : g ∈ GK K then Matrix.of fun i j => bV.repr (T'.ρ ⟨g, hg⟩ (bV j)) i else 0
  have hM0 : ∀ g (hg : g ∈ GK K), M0 g = Matrix.of fun i j => bV.repr (T'.ρ ⟨g, hg⟩ (bV j)) i :=
    fun g hg => dif_pos hg
  have hmul : ∀ g ∈ GK K, ∀ g' ∈ GK K, M0 (g * g') = M0 g * M0 g' := by
    intro g hg g' hg'
    rw [hM0 g hg, hM0 g' hg', hM0 _ (mul_mem hg hg')]
    have key : ∀ γ : ↥(GK K), (Matrix.of fun i j => bV.repr (T'.ρ γ (bV j)) i) =
        LinearMap.toMatrix bV bV ((T'.ρ γ).restrictScalars ℚ_[l]) := fun γ => by
      ext i j
      rw [LinearMap.toMatrix_apply]; rfl
    have hcomp : (T'.ρ ⟨g * g', mul_mem hg hg'⟩).restrictScalars ℚ_[l] =
        (T'.ρ ⟨g, hg⟩).restrictScalars ℚ_[l] ∘ₗ (T'.ρ ⟨g', hg'⟩).restrictScalars ℚ_[l] := by
      refine LinearMap.ext fun v => ?_
      exact LinearMap.congr_fun (map_mul T'.ρ ⟨g, hg⟩ ⟨g', hg'⟩) v
    rw [key, key, key, hcomp]
    exact LinearMap.toMatrix_comp bV bV bV _ _
  obtain ⟨ΦE, -, hΦE⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD E) ρ' bV
  obtain ⟨DE, hDE, hfin, hdim⟩ := GlobalTheory.T.deRham_invariants_coordinates_finrank_eq (P.PD E) ρ' bV hLL hE.2.1.1 (hE.2.2 hcrys) ΦE hΦE
  have hinv : ∀ y ∈ DE, ∀ g ∈ GK E,
      ((M0 g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y := by
    intro y hy g hg
    have := (hDE y).1 hy ⟨g, hg⟩
    simp only [P.PD_actdR] at this
    rw [hM0 g (GK_le hle hg)]
    exact this
  obtain ⟨e, u, hli, hu, hact⟩ := basis_of_invariants P AI Θ K s hs E hEs M0 DE
    hinv hfin hdim
  have hFil : ∀ a x, x ∈ (P.PD E).Fil a ↔ x ∈ (P.PD K).Fil a := fun a x =>
    Set.ext_iff.1 (P.PD_Fil E K a) x
  refine ⟨e, u, hli, fun k => ?_, fun σ hσ k => ?_⟩
  · obtain ⟨y, hy, hy1, hy2⟩ := hu k
    simp only [hFil] at hy1 hy2
    obtain ⟨z, hz, hz1, hz2⟩ := GlobalTheory.T.deRhamFil_invariant_jump_descends_finExt l P K E hle d M0 hmul (u k) y (hinv y hy) hy1 hy2
    obtain ⟨Φ, h1, h2⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD K) T'.ρ bV
    intro heq
    have hmem : Φ.symm z ∈ DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k) := by
      refine ⟨?_, (h1 _ _).2 (by simpa using hz1)⟩
      simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      apply Φ.injective
      rw [h2, Φ.apply_symm_apply]
      have := hz g g.2
      rw [hM0 g g.2] at this
      simp only [P.PD_actdR]
      exact this
    have hmem' : Φ.symm z ∈ DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k + 1) := by
      have heq' : DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k + 1) =
        DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k) := heq
      rw [heq']; exact hmem
    exact hz2 (by simpa using (h1 _ _).1 hmem'.2)
  · have hσE : σ ∈ GK E := by
      refine IntermediateField.fixingSubgroup_le (?_ : E.1 ≤ Ks K m) hσ
      rw [hEs]
      refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun x hx => ?_) _
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
      change x ^ (l ^ (s + n)) = 1
      rw [pow_add, pow_mul, show x ^ l ^ s = 1 from hx, one_pow]
    have hσK : σ ∈ GK K := GK_le hle hσE
    have hMσ : M σ = (M0 σ).map (algebraMap ℚ_[l] (PadicComplex l)) := by
      rw [hM0 σ hσK]
      ext i j
      exact hbV ⟨σ, hσK⟩ i j
    have := hact σ hσE k
    unfold twAct at this ⊢
    rw [hMσ]
    exact this

theorem exists_htBasis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O), IsCrysOn S S.W.GKs T → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∀ m : ℕ, s ≤ m → (Jset S T).Finite ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K m) M (Jset S T) := by
  intro D HW F h7 l _ K s LL h S E' T hcr d M A hM m hm
  obtain ⟨Θ⟩ := GlobalTheory.T.nonempty_thetaOnBdRPlus_periodData D l
  obtain ⟨E, hEs⟩ : ∃ E : FinExt l, E.1 = Ks K s :=
    ⟨⟨Ks K s, GlobalTheory.MemLoc.finiteDimensional_Ks_of_finExt K s⟩, rfl⟩
  have hle : K.1 ≤ E.1 := hEs ▸ h.2.2.1
  exact htBasis_of_isCrys (D.loc l) (D.locA l) Θ K s ⟨h.1, h.2.1⟩ E hEs hle LL (h7 l K) (h7 l E) T
    (GlobalTheory.T.isCrystalline_cyclotomicLevel_of_finrank_invariants l (D.loc l) K s LL _ ((HW l).W K s LL h) ((HW l).W_s K s LL h) E hEs hle T hcr)
    M A hM m hm

end GlobalTheory.HTBasisEx
