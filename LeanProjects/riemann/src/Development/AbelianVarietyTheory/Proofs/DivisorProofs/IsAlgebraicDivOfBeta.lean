import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeIsIntegralOverStandardLatticeStabilisStatement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTop.SqField

theorem gBig_and {Q Q' : GP} (h : GBig @Q) (h' : GBig @Q') :
    GBig fun {_ _ _ _} G μ C x b => Q G μ C x b ∧ Q' G μ C x b := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨a', ha'⟩ := h'
  refine ⟨max a a', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h1⟩ := ha ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h2⟩ := ha' ε CF (le_of_max_le_right hCF)
  refine ⟨max C0 C1, max x0 x1, fun C hC D large₂ he hx hR T Lc μ hμ G => ⟨?_, ?_⟩⟩
  · exact h1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hμ G
  · exact h2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hμ G

theorem isAlgebraic_norm {D : D7} {δ t0 : ℂ} {Q N : ℕ} {B : ℝ} {del : ℕ → ℝ} (hC : GlobalTheory.NormSum.CoordInt D N B Q del)
    (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (hP : P.Small N B) : IsAlgebraic ℚ ((P.norm : ℝ) : ℂ) := by
  have hco : ∀ h T, P.coord h T ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun h T => by
    obtain ⟨p, hp, hi⟩ := GlobalTheory.T.exists_prime_isIntegralOverStandardLatticeStabiliser D P.d h
    haveI : Fact p.Prime := ⟨hp⟩
    exact ((hC δ t0 p Q le_rfl P hP).2.2 h hi T).1
  have hsq : ∀ g, ((P.sq g : ℝ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun g => by
    unfold GlobalTheory.NormSum.Pair.sq
    rw [Complex.ofReal_sum]
    refine sum_mem fun T _ => ?_
    have e : ((‖P.coord g T‖ ^ 2 : ℝ) : ℂ) = P.coord g T * (starRingEnd ℂ) (P.coord g T) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e]
    exact mul_mem (hco g T)
      (mem_algebraicClosure_iff.2 ((mem_algebraicClosure_iff.1 (hco g T)).algHom (starRingEnd ℂ).toRatAlgHom))
  have hterm : ∀ h : GlobalTheory.NormSum.Cls D P.d P.J,
      (((((GlobalTheory.NormSum.gam D P.J h.out : ℝ))⁻¹ * P.sq h.out : ℝ)) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun h => by
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    exact mul_mem (inv_mem (natCast_mem _ _)) (hsq _)
  refine mem_algebraicClosure_iff.1 ?_
  unfold GlobalTheory.NormSum.Pair.norm
  by_cases hs : (Function.support fun h : GlobalTheory.NormSum.Cls D P.d P.J =>
      ((GlobalTheory.NormSum.gam D P.J h.out : ℝ))⁻¹ * P.sq h.out).Finite
  · rw [finsum_eq_sum _ hs, Complex.ofReal_sum]
    exact sum_mem fun h _ => hterm h
  · rw [finsum_of_infinite_support hs, Complex.ofReal_zero]
    exact zero_mem _

theorem isAlgebraic_div_of_beta {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {d s : ℕ} (hd : 0 < d)
    (hs : 1 ≤ s) (κ : I → ℕ) (Λ : PeriodPair) {x y : ℂ} (hx : x ≠ 0)
    (ha : IsAlgebraic ℚ (GlobalTheory.CMVal.beta E d s κ Λ x)) (hb : IsAlgebraic ℚ (GlobalTheory.CMVal.beta E d s κ Λ y)) :
    IsAlgebraic ℚ (y / x) := by
  have hC : (GlobalTheory.CMVal.C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (GlobalTheory.CMVal.cmValueConst_pos E hd (by omega) κ).ne'
  have hΔ : GlobalTheory.CMVal.latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ ≠ 0 := pow_ne_zero _ (GlobalTheory.CMVal.latDisc_ne_zero Λ)
  have e : (y / x) ^ 12 = GlobalTheory.CMVal.beta E d s κ Λ y / GlobalTheory.CMVal.beta E d s κ Λ x := by
    unfold GlobalTheory.CMVal.beta
    field_simp
  refine IsAlgebraic.of_pow (n := 12) (by norm_num) ?_
  rw [e]
  exact mem_algebraicClosure_iff.1 (div_mem (mem_algebraicClosure_iff.2 hb) (mem_algebraicClosure_iff.2 ha))

theorem sqIn_of {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T)
    (hI : GlobalTheory.NormSum.IntSt) (hΛ : ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ)
    (hT : ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c, ∃ x, IsTor G i j s (fam G μ₀ i j c) x ∧ x ≠ 0 ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ →
        IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D sc.cGap i j s) Λ x))
    (hQ : GlobalTheory.NormSum.GoodLevel D (levQ G.pl))
    (hS : ∀ (δ t0 : ℂ) (Q : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) t (i j : Fin D.R.m) 𝔪, IsBottom G t i j 𝔪 P P' →
      P.Small (bigN D) (maxWt D sc.cGap) ∧ P'.Small (bigN D) (maxWt D sc.cGap)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ GlobalTheory.BigTop.Fun.SqIn G μ₀ (algebraMap M ℂ) := by
  obtain ⟨C, -, hI⟩ := hI
  have hN : 1 ≤ bigN D := by have := D.R.m_add_three_le_k; unfold bigN; omega
  obtain ⟨-, del, -, hco, -⟩ := hI D (levQ G.pl) (bigN D) (maxWt D sc.cGap) (max 1 (Real.log D.host.rdE)) hQ hN
    (by exact_mod_cast le_max_left _ _) (le_max_left _ _) (le_max_right _ _)

  obtain ⟨Sn, hSn, hSa, hSb⟩ : ∃ Sn : Set ℂ, Sn.Finite ∧ (∀ z ∈ Sn, IsAlgebraic ℚ z) ∧
      (GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (fun _ => True) → GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (· ∈ Sn)) := by
    by_cases hb : GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (fun _ => True)
    · obtain ⟨δ, t0, hb⟩ := hb
      choose P P' hP using hb
      refine ⟨Set.range (fun ij => ((P ij).norm : ℂ)) ∪ Set.range (fun ij => ((P' ij).norm : ℂ)),
        (Set.finite_range _).union (Set.finite_range _), ?_,
        fun _ => ⟨δ, t0, fun ij => ⟨P ij, P' ij, (hP ij).1, Or.inl ⟨ij, rfl⟩, Or.inr ⟨ij, rfl⟩⟩⟩⟩
      rintro z (⟨ij, rfl⟩ | ⟨ij, rfl⟩)
      · exact isAlgebraic_norm hco _ (hS δ t0 _ _ _ _ _ _ _ (hP ij).1).1
      · exact isAlgebraic_norm hco _ (hS δ t0 _ _ _ _ _ _ _ (hP ij).1).2
    · exact ⟨∅, Set.finite_empty, fun z hz => absurd hz (Set.notMem_empty z), fun h => absurd h hb⟩

  let St : Set ℂ := ⋃ (i : Fin D.R.m) (j : Fin D.R.m) (s ∈ Set.Icc 1 (halfRank D i j)) (c : Bool),
    {z | ∃ x y, IsTor G i j s (nuH G μ₀ i j) x ∧ IsTor G i j s (nuH G μ₀ i j * delOf Lc c) y ∧ z = y / x}
  have hSt : St.Finite := by
    refine Set.finite_iUnion fun i => Set.finite_iUnion fun j => (Set.finite_Icc _ _).biUnion fun s _ =>
      Set.finite_iUnion fun c => Set.Subsingleton.finite ?_
    rintro _ ⟨x, y, hx, hy, rfl⟩ _ ⟨x', y', hx', hy', rfl⟩
    rw [hx.2.unique hx'.2, hy.2.unique hy'.2]
  have hd : 0 < D.host.d := D.host.hypOdd.2.1.pos
  obtain ⟨Λ, hΛ⟩ := hΛ
  have hSta : ∀ z ∈ St, IsAlgebraic ℚ z := by
    intro z hz
    simp only [St, Set.mem_iUnion, Set.mem_setOf_eq] at hz
    obtain ⟨i, j, s, ⟨h1, h2⟩, c, x, y, hx, hy, rfl⟩ := hz
    obtain ⟨x0, hx0, hx00, ha⟩ := hT i j s h1 h2 none
    obtain ⟨x1, hx1, -, hb⟩ := hT i j s h1 h2 (some c)
    rw [hx.2.unique hx0.2, hy.2.unique hx1.2]
    exact isAlgebraic_div_of_beta hd h1 _ Λ hx00 (ha Λ hΛ) (hb Λ hΛ)
  let S : Set ℂ := Sn ∪ St
  haveI : Finite S := (hSn.union hSt).to_subtype
  have hmem : ∀ z ∈ S, z ∈ Set.range (algebraMap (IntermediateField.adjoin ℚ S) ℂ) := fun z hz =>
    ⟨⟨z, IntermediateField.subset_adjoin ℚ S hz⟩, rfl⟩
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin fun z hz =>
    (Or.elim hz (hSa z) (hSta z)).isIntegral, ⟨fun h => ?_, fun i j s c x y h1 h2 hx hy => ?_⟩⟩
  · obtain ⟨δ, t0, b⟩ := hSb h
    exact ⟨δ, t0, fun ij => let ⟨P, P', a, b1, b2⟩ := b ij; ⟨P, P', a, hmem _ (Or.inl b1), hmem _ (Or.inl b2)⟩⟩
  · refine hmem _ (Or.inr ?_)
    simp only [St, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨i, j, s, ⟨h1, h2⟩, c, x, y, hx, hy, rfl⟩

end GlobalTheory.SqTop.SqField

namespace GlobalTheory.BigTop.Fun

end GlobalTheory.BigTop.Fun

end
