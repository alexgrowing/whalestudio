import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.IdxProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocIdx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.GlobMeasureEqRelIndexMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.HelpSng
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MeasBAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GOfPrime
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.HaarIdx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StKHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CardNuGZmod
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLq
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRed

noncomputable section

namespace Formalism.L2.SG.Pf.DstarIdxPf

open MeasureTheory Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets PI.MassDataKppVolLemmas
open scoped ENNReal

section Glob

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)

theorem lIdx_ne (p : TypX X) : lIdx X hb p ≠ 0 := by
  obtain ⟨K, hKe, -, -, -, hfin⟩ := LocIdx_main X hb (Formalism.L2.SG.Closed.level_subgroup_is_group X)
    (Formalism.L2.SG.Closed.level_subgroup_properties X) p
  have hcl : KvS X p = K := by rw [KvS, ← hKe, Subgroup.closure_eq]
  rw [lIdx, LocIdx_KppvS X hb (Formalism.L2.SG.Closed.level_subgroup_is_group X) p, hcl]
  exact hfin

theorem g_pos : 1 ≤ X.B.g := Nat.one_le_iff_ne_zero.mpr (Formalism.L2.SG.Pf.modulus_g_ne_zero X)

theorem isOpen_Kg : IsOpen (X.B.I.Kg X.B.g) := X.B.I.topf_open X.B.g (g_pos X)

theorem one_mem_Kg : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g :=
  ⟨Formalism.L2.SG.Pf.unitaryCongruence.K_one _, fun y _ => ⟨0, zero_mem _, by rw [show X.B.I.fmat 1 = 1 from rfl, sub_self, Matrix.zero_mulVec, smul_zero]⟩⟩

theorem isOpen_levelSubgroup' : IsOpen ((levelSubgroupOfCharacter X (Formalism.L2.SG.Closed.level_subgroup_is_group X) : Subgroup X.B.I.Gf) : Set X.B.I.Gf) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  refine Filter.mem_of_superset ((isOpen_Kg X).mem_nhds (one_mem_Kg X)) ?_
  intro x hx
  exact ((Formalism.L2.SG.Closed.level_subgroup_properties X).1 x hx).1

theorem relIdx_eq : ((levelSubgroupOfCharacter X (Formalism.L2.SG.Closed.level_subgroup_is_group X)).relIndex (KsetSub X.B.I)) =
    ∏ p : TypX X, lIdx X hb p := by
  rw [← PI.MassDataKppVolLemmas.IP_gIdx X hb (Formalism.L2.SG.Closed.level_subgroup_is_group X)]
  exact PI.MassDataKppVolLemmas.IP_idxProd X hb PI.MassDataKppVolLemmas.single_component_surjective
    (Formalism.L2.SG.Closed.level_subgroup_is_group X) (Formalism.L2.SG.Closed.level_subgroup_properties X)

theorem muK_eq : X.B.μf X.B.I.Kset =
    ((∏ p : TypX X, lIdx X hb p : ℕ) : ℝ≥0∞) * X.B.μf X.K2 := by
  have hle : levelSubgroupOfCharacter X (Formalism.L2.SG.Closed.level_subgroup_is_group X) ≤ KsetSub X.B.I :=
    fun x hx => (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 x hx
  have hi : (levelSubgroupOfCharacter X (Formalism.L2.SG.Closed.level_subgroup_is_group X)).relIndex (KsetSub X.B.I) ≠ 0 := by
    rw [relIdx_eq X hb]
    exact Finset.prod_ne_zero_iff.2 fun p _ => lIdx_ne X hb p
  have := Glob_measure_eq_relIndex_mul X.B.μf (KsetSub X.B.I) (levelSubgroupOfCharacter X (Formalism.L2.SG.Closed.level_subgroup_is_group X)) hle
    (isOpen_levelSubgroup' X) hi
  rw [relIdx_eq X hb] at this
  exact this

theorem ratio_eq : (X.B.μf X.B.I.Kset).toReal / X.volK2 = ∏ p : TypX X, (lIdx X hb p : ℝ) := by
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hv2 : 0 < X.volK2 := ENNReal.toReal_pos hL.2.2.1.ne' hL.2.2.2.ne
  rw [muK_eq X hb, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  unfold HidaSetting.volK2 at hv2 ⊢
  rw [mul_div_assoc, div_self hv2.ne', mul_one]
  push_cast
  rfl

end Glob

theorem rowLev_arith (k m c : ℕ) (hm : Even m) (h2 : 2 ≤ m) (h : c + k = (k + m - 1) * (k + m - 1 - 1) / 2) :
    c = (m / 2 - 1) * (m / 2 - 1 - 1) + 2 * (m / 2 - 1) * (k + 1) + (m / 2 - 1) ^ 2 + k * (k - 1) / 2 := by
  obtain ⟨t, rfl⟩ := hm
  have ht : (t + t) / 2 = t := by omega
  rw [ht]
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have e1 : k + (s + 1 + (s + 1)) - 1 = k + 2 * s + 1 := by omega
  have e2 : k + 2 * s + 1 - 1 = k + 2 * s := by omega
  rw [e1, e2] at h
  simp only [Nat.add_sub_cancel]
  have hA : s * (s - 1) + 2 * s * (k + 1) + s ^ 2 = 2 * s * s + s + 2 * s * k := by
    cases s with
    | zero => simp
    | succ r =>
      simp only [Nat.add_sub_cancel]
      ring
  have hK : (k + 1) * k / 2 = k * (k - 1) / 2 + k := by
    cases k with
    | zero => simp
    | succ j =>
      simp only [Nat.add_sub_cancel]
      rw [show (j + 1 + 1) * (j + 1) = (j + 1) * j + 2 * (j + 1) by ring,
        Nat.add_mul_div_left _ _ (by norm_num)]
  have hB : (k + 2 * s + 1) * (k + 2 * s) / 2 = (2 * s * s + s + 2 * s * k) + (k + 1) * k / 2 := by
    rw [show (k + 2 * s + 1) * (k + 2 * s) = (k + 1) * k + 2 * (2 * s * s + s + 2 * s * k) by ring,
      Nat.add_mul_div_left _ _ (by norm_num)]
    ring
  rw [hA]
  rw [hB, hK] at h
  omega

theorem card_rowLev (R : Formalism.BasicNotions.Ranks) (g : ℕ) [Fact g.Prime] :
    Nat.card {A : GL (Fin (R.k + R.m - 1)) (ZMod g) //
      Formalism.MainNotions.StandardLattice.IsRowLev R.k (R.m / 2 - 1) (A : Matrix (Fin (R.k + R.m - 1)) (Fin (R.k + R.m - 1)) (ZMod g))} =
      nnC R.rS R.k g * ukC R.k g := by
  have h2 := R.two_le_m
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun A : GL (Fin (R.k + R.m - 1)) (ZMod g) =>
      Formalism.MainNotions.J.isRowLev_iff R.k (R.m / 2 - 1) (A : Matrix (Fin (R.k + R.m - 1)) (Fin (R.k + R.m - 1)) (ZMod g))),
    Formalism.MainNotions.J.card_pat _ (by
      simp only [Formalism.MainNotions.J.rowS, Formalism.MainNotions.J.upS, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun p hp => hp.1), Nat.card_zmod]
  unfold nnC ukC
  rw [MassDataIdxStIm.card_isN, Nat.card_congr (MassDataIdxStIm.upUniGEquiv R.k), MassDataIdxStIm.card_uni, ZMod.card,
    ← pow_add]
  congr 1
  have h := Formalism.MainNotions.J.card_rowS R.k (R.m / 2 - 1) (R.k + R.m - 1) (by omega)
  rw [rowLev_arith R.k R.m _ R.m_even h2 h]
  rfl

theorem ggC_eq (R : Formalism.BasicNotions.Ranks) (g : ℕ) :
    ggC R.rS R.k g = Nat.card (GL (Fin (R.k + R.m - 1)) (ZMod g)) := by
  have hc0 : Nat.card (Formalism.FourierDecayAlt.S3.Idx R.rS R.k) = Nat.card (Fin (R.k + R.m - 1)) := by
    obtain ⟨t, ht⟩ := R.m_even
    have h2 := R.two_le_m
    simp only [Formalism.FourierDecayAlt.S3.Idx, Formalism.FourierDecayAlt.S3.Mid, Nat.card_sum, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit, Formalism.BasicNotions.Ranks.rS]
    omega
  have hc : Fintype.card (Formalism.FourierDecayAlt.S3.Idx R.rS R.k) = Fintype.card (Fin (R.k + R.m - 1)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hc0
  unfold ggC
  exact Nat.card_congr (Units.mapEquiv
    (Matrix.reindexAlgEquiv (ZMod g) (ZMod g) (Fintype.equivOfCardEq hc)).toMulEquiv).toEquiv

section Loc

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)

theorem lIdx_mul (p : TypX X) (hR : MassDataIdxSteps.StRed X p) (hI : MassDataIdxSteps.StImA X hb p) :
    lIdx X hb p * (nnC D.R.rS D.R.k (gOf p) * ukC D.R.k (gOf p)) = ggC D.R.rS D.R.k (gOf p) := by
  obtain ⟨K, hKs, -, -, -⟩ := MassDataIdxSteps.stK_holds X p
  obtain ⟨ρ, hρ, hker⟩ := hR K hKs
  obtain ⟨A, hAs, hAk, hcard⟩ := hI K hKs ρ hρ hker
  have := MassDataIdxSteps.finite_GL X p
  have key := MassDataIdxSteps.redIdx K _ ρ hρ A hAk
  have hKv : KvS X p = K := by
    have e : (K : Set _) = Formalism.L2.SG.TypedSets.Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1 := hKs
    rw [KvS, ← e, Subgroup.closure_eq]
  have hKpp : KppvS X hb p = A.map K.subtype := by
    rw [KppvS]
    have e : Formalism.L2.SG.TypedSets.compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1 =
        ((A.map K.subtype : Subgroup (MassDataIdxSteps.HAp X p)) : Set (MassDataIdxSteps.HAp X p)) := by
      rw [Subgroup.coe_map]
      exact hAs.symm
    rw [e, Subgroup.closure_eq]
  have hidx : lIdx X hb p = A.index := by
    rw [lIdx, hKv, hKpp, Subgroup.relIndex, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  rw [hidx, ← hcard]
  exact key

theorem lIdx_eq (p : TypX X) (hR : MassDataIdxSteps.StRed X p) (hI : MassDataIdxSteps.StImA X hb p) :
    (lIdx X hb p : ℝ) = Formalism.MainNotions.StandardLattice.idxRowLoc (gOf p) D.R.k D.R.m := by
  haveI : Fact (gOf p).Prime := by
    unfold gOf
    split_ifs
    · exact ⟨D.host.g_prime 0⟩
    · exact ⟨D.host.g_prime 1⟩
  have hm := lIdx_mul X hb p hR hI
  have hpos : 0 < ggC D.R.rS D.R.k (gOf p) := by
    rw [ggC_eq D.R (gOf p)]
    exact Nat.card_pos
  have hne : nnC D.R.rS D.R.k (gOf p) * ukC D.R.k (gOf p) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hm
    omega
  unfold Formalism.MainNotions.StandardLattice.idxRowLoc Formalism.MainNotions.StandardLattice.idxLoc
  rw [card_rowLev D.R (gOf p), ← ggC_eq D.R (gOf p), ← hm]
  have hne' : ((nnC D.R.rS D.R.k (gOf p) * ukC D.R.k (gOf p) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hne
  rw [Nat.cast_mul (lIdx X hb p), mul_div_assoc, div_self hne', mul_one]

end Loc

section Typ

open IsDedekindDomain NumberField

def hosMap {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S] (e : R ≃+* S)
    (v : HeightOneSpectrum R) : HeightOneSpectrum S where
  asIdeal := v.asIdeal.comap e.symm.toRingHom
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    refine (Submodule.ne_bot_iff _).2 ⟨e x, ?_, ?_⟩
    · show e.symm (e x) ∈ v.asIdeal
      rw [RingEquiv.symm_apply_apply]; exact hx
    · exact (map_ne_zero_iff e e.injective).2 hx0

theorem hosMap_symm {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S] (e : R ≃+* S)
    (v : HeightOneSpectrum R) : hosMap e.symm (hosMap e v) = v := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  ext x
  simp [hosMap]

def overEquiv {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S] (e : R ≃+* S) (g : ℕ) :
    {v : HeightOneSpectrum R // (g : R) ∈ v.asIdeal} ≃ {w : HeightOneSpectrum S // (g : S) ∈ w.asIdeal} where
  toFun v := ⟨hosMap e v.1, by show e.symm (g : S) ∈ v.1.asIdeal; rw [map_natCast]; exact v.2⟩
  invFun w := ⟨hosMap e.symm w.1, by show e.symm.symm (g : R) ∈ w.1.asIdeal; rw [map_natCast]; exact w.2⟩
  left_inv v := Subtype.ext (hosMap_symm e v.1)
  right_inv w := Subtype.ext (by simpa using hosMap_symm e.symm w.1)

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

def iF : X.B.I.F ≃+* D.host.F :=
  RingEquiv.ofBijective
    ((X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).codRestrict D.host.F (fun a => (X.ιE_F _).2 ⟨a, rfl⟩))
    ⟨fun a b h => by
      have h' := congrArg Subtype.val h
      simp only [RingHom.codRestrict_apply, RingHom.coe_comp, Function.comp_apply] at h'
      exact (algebraMap X.B.I.F X.B.I.E).injective (X.ιE.injective h'),
     fun y => by
      obtain ⟨a, ha⟩ := (X.ιE_F y.1).1 y.2
      exact ⟨a, Subtype.ext ha⟩⟩

theorem card_over (i : Fin 2) :
    Nat.card {v : HeightOneSpectrum (𝓞 X.B.I.F) // ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal} = D.R.f := by
  rw [Nat.card_congr (overEquiv (RingOfIntegers.mapRingEquiv (iF X)) (D.host.g i))]
  exact (Formalism.MainNotions.J.splitsF_g D i).1

theorem not_both (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h0 : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal)
    (h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) : False := by
  have hne : D.host.g 0 ≠ D.host.g 1 := D.host.g_ne
  have hcop : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).mpr hne)
  obtain ⟨a, b, hab⟩ := hcop
  have h2 : (a : 𝓞 X.B.I.F) * ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) +
      (b : 𝓞 X.B.I.F) * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 X.B.I.F) hab
    push_cast at this
    exact this
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h2]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)

theorem gOf_iff (i : Fin 2) (p : TypX X) : gOf p = D.host.g i ↔ ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
  have hne : D.host.g 0 ≠ D.host.g 1 := D.host.g_ne
  have htyp : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal :=
    (Formalism.L2.SG.TypedSets.mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
      (D.host.g_prime 1).ne_zero p.1).1 p.2
  unfold Formalism.L2.SG.TypedSets.gOf
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · by_cases h0 : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal
    · simp [h0]
    · simp [h0, Ne.symm hne]
  · by_cases h0 : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal
    · simp only [h0, if_true]
      constructor
      · intro h
        exact absurd h hne
      · intro h1
        exact (not_both X p.1 h0 h1).elim
    · simp only [h0, if_false]
      exact ⟨fun _ => htyp.resolve_left h0, fun _ => trivial⟩

def typEquiv (i : Fin 2) :
    {p : TypX X // gOf p = D.host.g i} ≃ {v : HeightOneSpectrum (𝓞 X.B.I.F) // ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal} where
  toFun p := ⟨p.1.1, (gOf_iff X i p.1).1 p.2⟩
  invFun v := ⟨⟨v.1, (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
      (D.host.g_prime 1).ne_zero v.1).2 (by fin_cases i; exacts [Or.inl v.2, Or.inr v.2])⟩,
    (gOf_iff X i _).2 v.2⟩
  left_inv p := rfl
  right_inv v := rfl

theorem prod_typ (φ : ℕ → ℝ) :
    ∏ p : TypX X, φ (gOf p) = φ (D.host.g 0) ^ D.R.f * φ (D.host.g 1) ^ D.R.f := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun p : TypX X => gOf p = D.host.g 0)]
  have hiff : ∀ p : TypX X, ¬ gOf p = D.host.g 0 ↔ gOf p = D.host.g 1 := by
    intro p
    constructor
    · intro h
      have hp := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
        (D.host.g_prime 1).ne_zero p.1).1 p.2
      rcases hp with h0 | h1
      · exact absurd ((gOf_iff X 0 p).2 h0) h
      · exact (gOf_iff X 1 p).2 h1
    · intro h h'
      exact not_both X p.1 ((gOf_iff X 0 p).1 h') ((gOf_iff X 1 p).1 h)
  have h1 : ∀ p : {p : TypX X // gOf p = D.host.g 0}, φ (gOf p.1) = φ (D.host.g 0) := fun p => by
    rw [p.2]
  have h2 : ∀ p : {p : TypX X // ¬ gOf p = D.host.g 0}, φ (gOf p.1) = φ (D.host.g 1) := fun p => by
    rw [(hiff p.1).1 p.2]
  rw [Fintype.prod_congr _ _ h1, Fintype.prod_congr _ _ h2, Finset.prod_const, Finset.prod_const,
    Finset.card_univ, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    Nat.card_congr (typEquiv X 0), card_over X 0,
    Nat.card_congr ((Equiv.subtypeEquivRight hiff).trans (typEquiv X 1)), card_over X 1]

end Typ

section Main

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem dstarIdx_of (hR : ∀ p : TypX X, MassDataIdxSteps.StRed X p)
    (hI : ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (p : TypX X), MassDataIdxSteps.StImA X hb p) :
    Formalism.L2.SG.Pf.RowDictPf.DstarIdx X := by
  let hb := (Formalism.L2.SG.Closed.adelic_isomorphism_statement X.B.I).1
  unfold Formalism.L2.SG.Pf.RowDictPf.DstarIdx
  rw [ratio_eq X hb]
  rw [Finset.prod_congr rfl (fun p _ => lIdx_eq X hb p (hR p) (hI hb p))]
  rw [prod_typ X (fun g => Formalism.MainNotions.StandardLattice.idxRowLoc g D.R.k D.R.m)]
  rfl

theorem dstarIdx_holds : Formalism.L2.SG.Pf.RowDictPf.DstarIdx X :=
  dstarIdx_of X (fun p => Formalism.L2.SG.Pf.MassDataX.stRed_holds X p) (fun hb p => Formalism.L2.SG.Pf.MassDataX.stImA_holds X hb p)

end Main

end Formalism.L2.SG.Pf.DstarIdxPf
