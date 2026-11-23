import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem satT_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (a : G) (hf : (MulAction.orbit K (a : G ⧸ K)).Finite) (S : Set G)
    (hS : ∀ g, g ∈ S ↔ ∃ x ∈ K, ∃ y ∈ K, g = x * a * y) (v : V) :
    dc ρ K K a v = GlobalTheory.LFun.heckeVec ρ K (Set.indicator S 1) v := by
  classical
  haveI := hf.to_subtype
  have h1 : dc ρ K K a v = ∑ᶠ q : MulAction.orbit K (a : G ⧸ K), ρ (q : G ⧸ K).out v :=
    (LinearMap.applyₗ (R := ℂ) (M₂ := V) v).toAddMonoidHom.map_finsum (Set.toFinite _)
  rw [h1, finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out v), finsum_mem_def, GlobalTheory.LFun.heckeVec]
  refine finsum_congr fun c => ?_
  have h2 : c ∈ MulAction.orbit K (a : G ⧸ K) ↔ c.out ∈ S := by
    rw [hS]
    constructor
    · rintro ⟨x, hx⟩
      have hx' : ((x.1 * a : G) : G ⧸ K) = (c.out : G ⧸ K) := hx.trans c.out_eq'.symm
      exact ⟨x, x.2, _, QuotientGroup.eq.1 hx', by group⟩
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      change ((x * a : G) : G ⧸ K) = c
      rw [← c.out_eq', e]
      exact (QuotientGroup.mk_mul_of_mem _ hy).symm
  by_cases hc : c.out ∈ S
  · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (h2.2 hc)]; simp
  · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (mt h2.1 hc)]; simp

private theorem satT_unif (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    Formalism.UG.IsUnifV L w (unif (w.adicCompletion L) : w.adicCompletion L) := by
  haveI : (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (valuation (w.adicCompletion L))
    (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ)))
  have hu : valuation (w.adicCompletion L) (unif (w.adicCompletion L) : w.adicCompletion L) =
      uniformizer (w.adicCompletion L) := by
    refine Classical.epsilon_spec (p := fun x : (w.adicCompletion L)ˣ =>
      valuation (w.adicCompletion L) (x : w.adicCompletion L) = uniformizer (w.adicCompletion L)) ?_
    obtain ⟨x, hx⟩ := valuation_surjective (uniformizer (w.adicCompletion L))
    refine ⟨Units.mk0 x ?_, hx⟩
    rintro rfl
    exact (zero_lt_iff.2 (by simp) : 0 < uniformizer (w.adicCompletion L)).ne ((map_zero _).symm.trans hx)
  obtain ⟨p, hp⟩ := GlobalTheory.LFun.exists_isUnifV w
  unfold Formalism.UG.IsUnifV at hp ⊢
  have h1 : Valued.v (unif (w.adicCompletion L) : w.adicCompletion L) < (1 : WithZero (Multiplicative ℤ)) :=
    he.lt_one_iff_lt_one.1 (hu.trans_lt uniformizer_lt_one)
  have h2 : valuation (w.adicCompletion L) p < 1 := he.lt_one_iff_lt_one.2 (by rw [hp]; decide)
  have h3 := (he _ _).1 ((le_uniformizer_iff.2 h2).trans_eq hu.symm)
  rw [hp] at h3
  refine le_antisymm ?_ h3
  change _ ≤ WithZero.exp (-1 : ℤ)
  rw [← WithZero.lt_mul_exp_iff_le (by simp), ← WithZero.exp_add]
  simpa using h1

private theorem satT_num (q n j : ℕ) (hq : q ≠ 0) :
    ((((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ^ j =
      (q : ℂ) ^ (j * (j - 1) / 2) * (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have h2 : ((j * (j - 1) / 2 : ℕ) : ℂ) = (j : ℂ) * ((j : ℂ) - 1) / 2 := by
    rw [← Nat.choose_two_right, Nat.cast_choose_two]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg q), ← Complex.cpow_nat_mul, ← Complex.cpow_natCast, h2]
  push_cast
  rw [← Complex.cpow_add _ _ hq']
  congr 1
  ring

private theorem satT_pol (q n : ℕ) (hq : q ≠ 0) (B : Multiset ℂˣ) (hB : B.card = n) (a : ℕ → ℂ)
    (ha : ∀ j ≤ n, a j = GlobalTheory.LFun.satEig q n B j) :
    ((UpperTheory.V.Af.algSat n q B).map fun b => X - C b).prod = heckePol n q a := by
  have hc : (UpperTheory.V.Af.algSat n q B).card = n := by simp [UpperTheory.V.Af.algSat, hB]
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, hc, UpperTheory.V.Hi.heckePol]
  refine Finset.sum_congr rfl fun j hj => ?_
  have e : (UpperTheory.V.Af.algSat n q B).esymm j =
      ((((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ^ j * (B.map fun b : ℂˣ => (b : ℂ)).esymm j := by
    rw [← smul_eq_mul, Multiset.pow_smul_esymm, UpperTheory.V.Af.algSat]
    congr 2
    simp
  rw [ha j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)), e, satT_num q n j hq, GlobalTheory.LFun.satEig]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

theorem UpperTheory.V.Hi.satT :
    ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → GlobalTheory.LFun.KGL w n = KO (w.adicCompletion L) (Fin n) ∧ ∃ a : ℕ → ℂ, a 0 = 1 ∧ (∀ j, ∀ v ∈ fixd σ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp σ.ρ j v = a j • v) ∧ ((UpperTheory.V.Af.algSat n (normV w) B).map fun b => X - C b).prod = heckePol n (normV w) a := by
  intro L _ _ n w σ B hB
  have hK : KO (w.adicCompletion L) (Fin n) = GlobalTheory.LFun.KGL w n := GlobalTheory.SmGL.SphCompletion.KO_completion w n
  refine ⟨hK.symm, fun j => GlobalTheory.LFun.satEig (normV w) n B (min j n), by simp [GlobalTheory.LFun.satEig, Multiset.esymm], ?_,
    satT_pol _ n (GlobalTheory.LFun.qV_ne_zero w) B hB.card _ fun j hj => by rw [min_eq_left hj]; rfl⟩
  intro j v hv
  by_cases h0 : v = 0
  · simp [h0]
  rw [hK] at hv
  have h1 := (hB.2 v (GlobalTheory.LGrp.mem_fixed.2 hv) h0).2.2.2 _ (satT_unif L w) (min j n) (min_le_right _ _)
  refine Eq.trans ?_ h1
  rw [sphOp, hK]
  refine satT_dc σ.ρ _ _ (Formalism.UG.P.orbit_coset_finite _ (Formalism.UG.Final.GLintComm L w n) _) _ (fun g => ?_) v
  have hal : (al (w.adicCompletion L) n j).val =
      Formalism.UG.diagJ n (unif (w.adicCompletion L) : w.adicCompletion L) (min j n) := by
    rw [UpperTheory.V.Hi.al, upow, val_diagT, Formalism.UG.diagJ]
    congr 1
    funext i
    have := i.2
    by_cases h : (i : ℕ) < j
    · simp [h]
    · simp [h]
  simp only [Set.mem_setOf_eq, ← hal, ← Units.val_mul, Units.val_inj]
