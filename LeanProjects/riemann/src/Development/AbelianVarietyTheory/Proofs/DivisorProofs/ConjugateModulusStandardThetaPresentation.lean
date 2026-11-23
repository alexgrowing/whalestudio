import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorIntegralPointVacuumRootOfUnitySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIntegralPointSkewLatticeUnitVectorSameEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionCosetVectorEqTranslateUnitVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeTranslateUnitVectorVacuumExpansioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexStandardInfSkewThetaLatticeEqAbsNormPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewIdealLatticePointRationalNormKillsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddCharThetaCommutatorPhaseSkewLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCongruentOfCommutatorPhaseEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardPrincipalCongruenceTransversalLeAbsNormPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormSqLeOfRootOfUnityAddCharCombinationStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatIn

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BotPairSmall.LastRows

theorem la_perm (D : D7) (T : Tor D) {a d : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (S : Submodule (𝓞 D.host.E) D.host.E) (σ : Fin d ≃ Fin d) (y : VC D a d)
    (hy : y ∈ La D T L (Submodule.pi Set.univ fun _ => S)) :
    (fun τ i j => y τ (σ i) j : VC D a d) ∈ La D T L (Submodule.pi Set.univ fun _ => S) := by
  have hH : ∀ A ∈ homL D L (Submodule.pi Set.univ fun _ : Fin d => S),
      A.submatrix σ id ∈ homL D L (Submodule.pi Set.univ fun _ : Fin d => S) := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA => exact Submodule.subset_span fun x hx i _ => hA x hx (σ i) trivial
    | zero => exact zero_mem _
    | add A B _ _ hA hB => exact add_mem hA hB
    | smul c A _ hA => exact Submodule.smul_mem _ c hA
  have hY : ∀ A ∈ YYl D L (Submodule.pi Set.univ fun _ : Fin d => S),
      A.submatrix σ id ∈ YYl D L (Submodule.pi Set.univ fun _ : Fin d => S) := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨b, hb, B, hB, rfl⟩ := hA
      exact Submodule.subset_span ⟨b, hb, _, hH B hB, rfl⟩
    | zero => exact zero_mem _
    | add A B _ _ hA hB => exact add_mem hA hB
    | smul c A _ hA => exact Submodule.smul_mem _ c hA
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨w, hw, _, hY A hA, rfl⟩
  | zero => exact zero_mem _
  | add x z _ _ hx hz => exact add_mem hx hz
  | neg x _ hx => exact neg_mem hx

theorem kap_perm (D : D7) (T : Tor D) {a d : ℕ} (σ : Fin d ≃ Fin d) (x y : VC D a d) :
    Formalism.MainNotions.TaylorLogMetric.kap D T (fun τ i j => x τ (σ i) j) y = Formalism.MainNotions.TaylorLogMetric.kap D T x (fun τ i j => y τ (σ.symm i) j) := by
  have : Hf D T (fun τ i j => x τ (σ i) j) y = Hf D T x (fun τ i j => y τ (σ.symm i) j) := by
    unfold Hf
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← σ.sum_comp (fun i => ∑ j, x τ i j * (starRingEnd ℂ) (y τ (σ.symm i) j))]
    simp
  unfold Formalism.MainNotions.TaylorLogMetric.kap
  rw [this]

theorem exists_perm (D : D7) {o a d : ℕ} (h : o + a = d) :
    ∃ σ : Fin d ≃ Fin d, ∀ i j, unitBlock D o a d (σ i) j = unitBlock D 0 a d i j := by
  refine ⟨⟨fun i => ⟨if i.1 < a then o + i.1 else i.1 - a, by have := i.2; split_ifs <;> omega⟩,
    fun i => ⟨if i.1 < o then a + i.1 else i.1 - o, by have := i.2; split_ifs <;> omega⟩, fun i => ?_, fun i => ?_⟩,
    fun i j => ?_⟩
  · have := i.2
    apply Fin.ext; dsimp only; split_ifs <;> omega
  · have := i.2
    apply Fin.ext; dsimp only; split_ifs <;> omega
  · have := i.2
    have := j.2
    simp only [unitBlock, Matrix.of_apply, Equiv.coe_fn_mk]
    refine if_congr ?_ rfl rfl
    split_ifs <;> omega

theorem distinct (D : D7) (δ : ℂ) (hc : Crv D ⊤ δ) (𝔪 : Ideal (𝓞 D.host.E)) (h𝔪 : 𝔪 ≠ ⊥)
    (hco : IsCoprime 𝔪 (D.host.conj • 𝔪)) (hb : IsCoprime 𝔪 D.host.𝔟) {o a d : ℕ} (ho : o + a = d) (r r' : GA D a)
    (hr : r ∈ intG D a) (hr' : r' ∈ intG D a) (x x' : Matrix (Fin d) (Fin a) D.host.E)
    (hx : pt D (tor0 D ⊤ δ) δ x ∈ La0 D (tor0 D ⊤ δ) a d) (hx' : pt D (tor0 D ⊤ δ) δ x' ∈ La0 D (tor0 D ⊤ δ) a d)
    (h1 : ∀ i j, (x.map (inc D) - (unitBlock D o a d).map (inc D) *
      (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪)
    (h2 : ∀ i j, (x'.map (inc D) - (unitBlock D o a d).map (inc D) *
      (((r'⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪)
    (hk : ∀ y ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d),
      Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x) y = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x') y) :
    CongOne D 𝔪 (r⁻¹ * r') := by
  obtain ⟨σ, hσ⟩ := exists_perm D ho
  have key : ∀ (z : Matrix (Fin d) (Fin a) D.host.E) (M : Matrix (Fin a) (Fin a) (AE D)) i j,
      ((z.submatrix σ id).map (inc D) - (unitBlock D 0 a d).map (inc D) * M) i j =
        (z.map (inc D) - (unitBlock D o a d).map (inc D) * M) (σ i) j := by
    intro z M i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.submatrix_apply, id, hσ]
  refine GlobalTheory.T.stabilizer_congruent_of_commutatorPhase_eq D δ hc 𝔪 h𝔪 hco hb (by omega) r r' hr hr' (x.submatrix σ id) (x'.submatrix σ id)
    (la_perm D _ _ _ σ _ hx) (la_perm D _ _ _ σ _ hx') (fun i j => by rw [key]; exact h1 _ _)
    (fun i j => by rw [key]; exact h2 _ _) fun y hy => ?_
  exact (kap_perm D _ σ (pt D (tor0 D ⊤ δ) δ x) y).trans
    ((hk _ (la_perm D _ _ _ σ.symm _ hy)).trans (kap_perm D _ σ (pt D (tor0 D ⊤ δ) δ x') y).symm)

theorem unitBlock_mul_int (D : D7) (o : ℕ) {a d : ℕ} (r : GA D a) (hr : r ∈ intG D a) (i : Fin d) (j : Fin a) :
    ((unitBlock D o a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈
      OhE D := by
  rw [Matrix.mul_apply]
  refine sum_mem fun l _ => mul_mem ?_ ?_
  · rw [Matrix.map_apply]
    by_cases h : i.1 = o + l.1
    · simp only [unitBlock, Matrix.of_apply, h, if_true, map_one]; exact one_mem _
    · simp only [unitBlock, Matrix.of_apply, h, if_false, map_zero]; exact zero_mem _
  · rw [Subgroup.coe_inv]
    exact ((mem_intG r).1 hr l j).2

theorem om_cosetV_eq (o : ℕ) : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (r : GA D a), r ∈ intG D a → ∃ x : Matrix (Fin d) (Fin a) D.host.E, pt D (tor0 D ⊤ δ) δ x ∈ (La0 D (tor0 D ⊤ δ) a d) ∧ (∀ i j, (x.map (inc D) - (unitBlock D o a d).map (inc D) * (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j ∈ hatId D 𝔪) ∧ W.Om r 1 (cosetV D δ 𝔪 o a d e0) = ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x) (W.Om r 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) := by
  intro D δ hc a d e0 he W 𝔪 h𝔪 r hr
  set T := tor0 D ⊤ δ
  set G := Iop D T (La0 D T a d) (La D T (stdL D a) (skewLat D 𝔪 d)) e0 with hGdef
  set x₀ := unitBlock D o a d with hx₀
  have hT := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have he' : e0 ∈ TT D T a d := hT.1 _ _ (GlobalTheory.FunObj.CosetTT.sd_stdL a) (GlobalTheory.FunObj.CosetTT.sd_stdL d) e0 he
  obtain ⟨M, hM, hMx⟩ := GlobalTheory.FunObj.CosetTT.la_skew_nsmul (D := D) ⊤ δ 𝔪 a d
  have hG : G ∈ TT D T a d :=
    GlobalTheory.FunObj.CosetTT.iop_mem_TT hc _ (fun y hy => ⟨M, hM, hMx y hy⟩) he'
  have hF : Wd D T (pt D T δ x₀) G ∈ TT D T a d := hT.2.1 _ _ hG
  obtain ⟨m, hm, hlift⟩ := W.lift r 1 x₀ G hG
  have hN : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  set R : Matrix (Fin a) (Fin a) (AE D) := (((r⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hR
  set Tm : Matrix (Fin d) (Fin a) (AE D) := x₀.map (inc D) * R with hTm
  have hTint : ∀ i j, Tm i j ∈ OhE D := fun i j => unitBlock_mul_int D o r hr i j
  choose b w hw hbw using fun i j =>
    GlobalTheory.CongApprox.exists_int_approx D (m * Ideal.absNorm 𝔪) (Nat.mul_pos hm hN) (Tm i j) (hTint i j)
  set x : Matrix (Fin d) (Fin a) D.host.E := Matrix.of fun i j => (b i j : D.host.E) with hxdef
  have hdiff : ∀ i j, (x.map (inc D) - Tm) i j = -(((m * Ideal.absNorm 𝔪 : ℕ) : AE D) * w i j) := by
    intro i j
    rw [Matrix.sub_apply, Matrix.map_apply, hbw i j]
    simp [hxdef]
  have hnat : ∀ k : ℕ, ((k : ℕ) : AE D) ∈ OhE D := fun k => natCast_mem _ k
  refine ⟨x, LiftCoset.globalIntegralMatrix_mem_stdThetaLattice D δ x (fun i j => ⟨b i j, rfl⟩), fun i j => ?_, ?_⟩
  · rw [hdiff i j, Nat.cast_mul, mul_comm ((m : ℕ) : AE D), mul_assoc]
    exact neg_mem (GlobalTheory.BotPairSmall.BlockIdx.absNorm_mul_mem_hatId D 𝔪 (mul_mem (hnat m) (hw i j)))
  · have hclose : CloseTo D ⊤ m (r : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) x₀ x := by
      intro i j
      refine ⟨-(((Ideal.absNorm 𝔪 : ℕ) : AE D) * w i j),
        GlobalTheory.CongApprox.OhE_le_IhE_top D _ (neg_mem (mul_mem (hnat _) (hw i j))), ?_⟩
      have e1 : (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1 := by simp
      have e2 : (((r : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = R := by
        rw [hR, Subgroup.coe_inv]
      rw [e1, Matrix.one_mul, e2, ← hTm, hdiff i j, Nat.cast_mul]
      ring
    have hl := hlift x hclose
    show W.Om r 1 (((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ • Wd D T (pt D T δ x₀) G) = _
    rw [W.smul r 1 _ _ hF, hl]

theorem pres_stdSum_last (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) {o a d : ℕ} (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0)
    (ho : o + a = d) (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)) (h𝔪 : 𝔪 ≠ ⊥) (hco : IsCoprime 𝔪 (D.host.conj • 𝔪))
    (hb : IsCoprime 𝔪 D.host.𝔟) (R : Finset (GA D a)) (hR : ∀ r ∈ R, r ∈ intG D a)
    (huniq : ∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) :
    Pres D ⊤ δ (Ideal.absNorm 𝔪) e0 (stdSum W 𝔪 o R) := by
  have had : a ≤ d := by omega
  have he : e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) := hv.1
  have hN0 : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  have hidx := GlobalTheory.T.index_standard_inf_skewThetaLattice_eq_absNorm_pow D δ hc 𝔪 h𝔪 hco a d
  haveI hfin : Finite (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) :=
    AddSubgroup.index_ne_zero_iff_finite.1 (by rw [hidx]; positivity)
  letI : Fintype (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) := Fintype.ofFinite _
  have wsm : ∀ (x : VC D a d) (c : ℂ) (G : VC D a d → ℂ), Wd D (tor0 D ⊤ δ) x (c • G) = c • Wd D (tor0 D ⊤ δ) x G := by
    intro x c G; funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring
  have hr : ∀ i : R, ∃ (c : ℂ) (x : Matrix (Fin d) (Fin a) D.host.E), (∃ m : ℕ, 0 < m ∧ c ^ m = 1) ∧
      pt D (tor0 D ⊤ δ) δ x ∈ La0 D (tor0 D ⊤ δ) a d ∧
      (∀ i' j, (x.map (inc D) - (unitBlock D o a d).map (inc D) *
        ((((i : GA D a)⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i' j ∈ hatId D 𝔪) ∧
      W.Om i 1 (cosetV D δ 𝔪 o a d e0) = ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
        (c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x)
          (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)) := by
    intro i
    obtain ⟨c, hcm, hce⟩ := GlobalTheory.FunObj.StdDatum.vacuum_int_root_of_unity D δ hc e0 he W i (hR i i.2)
    obtain ⟨x, hx, hxc, hom⟩ := om_cosetV_eq o D δ hc e0 he W 𝔪 h𝔪 i (hR i i.2)
    refine ⟨c, x, hcm, hx, hxc, ?_⟩
    rw [hom, GlobalTheory.T.weil_integralPoint_skewLatticeUnitVector_same_eigen D δ hc e0 he W 𝔪 h𝔪 i (hR i i.2) c hce, wsm]
  choose c x hcm hx hxc hom using hr
  choose χ hχ using fun i : R => GlobalTheory.T.exists_addChar_thetaCommutatorPhase_skewLattice D δ hc 𝔪 (pt D (tor0 D ⊤ δ) δ (x i)) (hx i)
  have hone : ∀ k : GA D a, CongOne D 𝔪 (k⁻¹ * k) := by
    intro k i' j
    rw [inv_mul_cancel]
    simp
  have hinj : Function.Injective χ := by
    intro i j hij
    have hk : ∀ y ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d),
        Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x i)) y =
          Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x j)) y := by
      intro y hy
      rw [← hχ i ⟨y, hy⟩, ← hχ j ⟨y, hy⟩, hij]
    have h1 := distinct D δ hc 𝔪 h𝔪 hco hb ho i j (hR i i.2) (hR j j.2) (x i) (x j) (hx i) (hx j) (hxc i) (hxc j) hk
    exact Subtype.ext ((huniq j (hR j j.2)).unique ⟨i.2, h1⟩ ⟨j.2, hone j⟩)
  have hcard : Fintype.card R ≤ Ideal.absNorm 𝔪 ^ (a * d) := by
    rw [Fintype.card_coe]
    refine (GlobalTheory.T.card_principalCongruence_transversal_le_absNorm_pow D 𝔪 h𝔪 a R hR huniq).trans (Nat.pow_le_pow_right hN0 ?_)
    rw [pow_two]; exact Nat.mul_le_mul_left a had
  obtain ⟨rr, hrr, hint, hρ⟩ := GlobalTheory.T.sum_norm_sq_le_of_rootOfUnity_addChar_combination (Ideal.absNorm 𝔪) (a * d) c χ hN0 hcm hinj
    (by rw [← hidx, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]) hcard
  choose z hz hzN using fun q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) =>
    GlobalTheory.T.skewIdealLattice_point_rational_normKills D δ hc 𝔪 h𝔪 _ (Quotient.out q).2
  set e := Fintype.equivFin (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ⧸
      (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)))
  refine ⟨_, fun i => rr (e.symm i), fun i => z (e.symm i), fun i => hzN _, fun i => hint _, fun ρ => ?_, ?_⟩
  · rw [e.symm.sum_comp (fun q => ‖ρ (rr q)‖)]; exact hρ ρ
  funext y
  rw [e.symm.sum_comp (fun q => ((rr q : Qbar) : ℂ) * Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) e0 y)]
  simp only [stdSum, Finset.sum_apply]
  rw [← Finset.sum_coe_sort R]
  simp only [hom, Pi.smul_apply, smul_eq_mul, GlobalTheory.T.standardLattice_translate_unitVector_vacuum_expansion D δ hc 𝔪 h𝔪 e0 he _ (hx _), hidx,
    finsum_eq_sum_of_fintype, hrr, ← hz]
  have hs : ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ *
      ((Real.sqrt (((Ideal.absNorm 𝔪 ^ (a * d) : ℕ) : ℝ)) : ℂ))⁻¹ = (((Ideal.absNorm 𝔪 : ℂ)) ^ (a * d))⁻¹ := by
    have h1 : (((Ideal.absNorm 𝔪 ^ (a * d) : ℕ) : ℝ)) = (Ideal.absNorm 𝔪 : ℝ) ^ (a * d) := by push_cast; rfl
    rw [h1, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; rfl
  have hχq : ∀ (i : R) q, χ i q = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (x i))
      ((Quotient.out q : La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) : VC D a d) := by
    intro i q
    rw [← hχ i, QuotientAddGroup.out_eq']
  simp only [hχq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
  rw [← hs]; ring

end GlobalTheory.BotPairSmall.LastRows

namespace GlobalTheory.BotPairSmall

theorem pres_conj_std : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hb : IsCoprime (D.host.conj • 𝔪) D.host.𝔟) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ Q : ℕ, Ideal.absNorm 𝔪 = Q → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D (D.host.conj • 𝔪) (r⁻¹ * k)) → Pres D ⊤ δ Q e0 (∑ r ∈ R, W.Om r 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0)) := by
  intro D δ t0 hc _ a d _ e0 hv W _ _ 𝔪 hm hcop hb _ o ho Q hQ R hR huniq
  have hcc : D.host.conj • (D.host.conj • 𝔪) = 𝔪 := by
    have h2 : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => D.host.φ₀.injective (by
      show D.host.φ₀ (D.host.conj (D.host.conj x)) = D.host.φ₀ x
      rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])
    rw [← mul_smul, h2, one_smul]
  have hco : IsCoprime (D.host.conj • 𝔪) (D.host.conj • (D.host.conj • 𝔪)) := by
    rw [hcc, Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hcop
  have h := LastRows.pres_stdSum_last D δ t0 hc e0 hv ho W _ (conj_smul_ne_bot D hm) hco hb R hR huniq
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.absNorm_smul_eq, hQ] at h
  exact h

end GlobalTheory.BotPairSmall

end
