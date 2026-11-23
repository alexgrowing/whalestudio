import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfC

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MQ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

theorem dvd_pow_of_dvr {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : O) (hp0 : p ≠ 0)
    (hpu : ¬ IsUnit p) : ∀ a : O, a ≠ 0 → ∃ (k : ℕ) (b : O), p ^ k = b * a := by
  intro a ha
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hpu (associated_one_iff_isUnit.1 (by simpa using hk))
  have h1 : ϖ ^ m ∣ ϖ ^ (k * m) := pow_dvd_pow ϖ (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hk1))
  have hdvd : a ∣ p ^ m :=
    hm.dvd.trans (h1.trans (by rw [pow_mul]; exact (hk.symm.pow_pow).dvd))
  obtain ⟨b, hb⟩ := hdvd
  exact ⟨m, b, by rw [hb, mul_comm]⟩

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem mem_DelS' {x : W.DD T} : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  simp [DelS, Submodule.mem_iInf, sub_eq_zero]

theorem mem_letS' {c : ZMod n} {x : W.DD T} : x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  simp [letS, sub_eq_zero]

theorem γD_smulA' (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem expand_at (π' a : LetA O n) (i : ZMod n) (hπ0 : PowerSeries.constantCoeff (π' i) = 0)
    (F : PowerSeries O) (hF : a i = PowerSeries.subst (π' i) F) :
    a i = π' i * PowerSeries.subst (π' i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) F) +
      PowerSeries.C (PowerSeries.constantCoeff F) := by
  have hS : PowerSeries.HasSubst (π' i) := PowerSeries.HasSubst.of_constantCoeff_zero' hπ0
  conv_lhs => rw [hF, PowerSeries.eq_X_mul_shift_add_const F]
  rw [PowerSeries.subst_add hS, PowerSeries.subst_mul hS, PowerSeries.subst_X hS, PowerSeries.subst_C]
  rfl

set_option maxHeartbeats 1000000 in

theorem basis_L [IsDomain O] (π' : LetA O n) (s' : ℕ) (hs : 1 ≤ s') (w₁ : (LetA O n)ˣ)
    (hπ : π' = w₁ * (letπ : LetA O n) ^ s')
    (huniq : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O, ∀ i, a i = PowerSeries.subst (π' i) (f i))
    {r : ℕ} (b : Fin r → W.DD T) (hbΔ : ∀ j, b j ∈ W.NΔ T)
    (hbu : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (hbe : ∀ x ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W (a j)) ∧ x = ∑ j, a j • b j)
    (c : ZMod n) : Nonempty (Module.Basis (Fin r) O (LcQ W T π' c)) := by
  classical
  set d : ZMod n := c - 1 with hd
  have hπd : ∀ i, π' i = (w₁ : LetA O n) i * PowerSeries.X ^ s' := fun i => π_at s' π' w₁ hπ i
  have hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0 := by
    intro i
    rw [hπd i, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
  have hmem : ∀ j, (letE d : LetA O n) • b j ∈ NcS W T d := by
    intro j
    obtain ⟨hN, hΔ⟩ := hbΔ j
    refine ⟨⟨(W.N T).smul_mem _ hN, (mem_DelS' W T).2 fun δ hδ => ?_⟩, (mem_letS' W T).2 ?_⟩
    · rw [γD_smulA', hΔ δ hδ, (show ∀ δ ∈ W.DelF, W.γA δ (letE d : LetA O n) = letE d from letE_mem W d) δ hδ]
    · rw [smul_smul, letE_mul_self']
  let v : Fin r → LcQ W T π' c := fun j => Submodule.Quotient.mk ⟨_, hmem j⟩
  have hli : LinearIndependent O v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h0 : (∑ j, g j • (⟨_, hmem j⟩ : ↥(NcS W T d))) ∈
        (PiNS W T π' 1).comap (NcS W T d).subtype := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
      simpa only [map_smul, Submodule.mkQ_apply] using hg
    rw [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sum] at h0
    simp only [Submodule.coe_smul] at h0
    obtain ⟨⟨y, hyN, hy⟩, -⟩ := h0
    obtain ⟨a', ha'⟩ := (hbu y hyN).exists
    have hxN : π' • y ∈ W.N T := (W.N T).smul_mem _ hyN
    have hrep1 : π' • y = ∑ j, (π' * a' j) • b j := by
      rw [ha', Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    have hrep2 : π' • y = ∑ j, (algebraMap O (LetA O n) (g j) * (letE d : LetA O n)) • b j := by
      have hy' : π' • y = ∑ j, g j • ((letE d : LetA O n) • b j) := by
        rw [← hy]
        show π' • y = ((π' ^ 1 : LetA O n) • LinearMap.id : W.DD T →ₗ[LetA O n] W.DD T) y
        rw [pow_one]
        rfl
      rw [hy']
      exact Finset.sum_congr rfl fun j _ => by rw [← smul_smul, algebraMap_smul]
    have huq := (hbu _ hxN).unique hrep1 hrep2
    have hj := congrFun (congrFun huq j) d
    simp only [Pi.mul_apply, letE, Pi.single_eq_same, mul_one] at hj
    have hcc := congrArg PowerSeries.constantCoeff hj
    rw [map_mul, hπ0 d, zero_mul] at hcc
    have : PowerSeries.constantCoeff ((algebraMap O (LetA O n) (g j)) d) = g j := by
      show PowerSeries.constantCoeff (algebraMap O (PowerSeries O) (g j)) = g j
      rw [PowerSeries.algebraMap_apply]
      simp
    rw [this] at hcc
    exact hcc.symm
  have hsp : ⊤ ≤ Submodule.span O (Set.range v) := by
    rintro q -
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨⟨hxN, hxΔ⟩, hxl⟩ := hx
    have hxΔ' := (mem_DelS' W T).1 hxΔ
    have hxl' := (mem_letS' W T).1 hxl
    obtain ⟨a, haΔ, hxa⟩ := hbe x ⟨hxN, hxΔ'⟩
    choose F hF using fun j => (huniq (a j) (haΔ j)).exists
    let κ : Fin r → O := fun j => PowerSeries.constantCoeff (F j d)
    let t : Fin r → LetA O n := fun j _ => PowerSeries.subst (π' d) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F j d))
    have hkey : ∀ j, (letE d : LetA O n) * a j = algebraMap O (LetA O n) (κ j) * letE d + π' * ((letE d : LetA O n) * t j) := by
      intro j
      funext i
      by_cases hi : i = d
      · subst hi
        simp only [Pi.mul_apply, Pi.add_apply, letE, Pi.single_eq_same, one_mul, mul_one]
        rw [expand_at π' (a j) _ (hπ0 _) (F j _) (hF j _)]
        show _ = algebraMap O (PowerSeries O) (κ j) + _
        rw [PowerSeries.algebraMap_apply]
        simp only [Algebra.algebraMap_self, RingHom.id_apply, t, κ]
        ring
      · simp [letE, Pi.single_apply, hi]
    set y : W.DD T := ∑ j, ((letE d : LetA O n) * t j) • b j with hydef
    have hyN : y ∈ W.N T := Submodule.sum_mem _ fun j _ => (W.N T).smul_mem _ (hbΔ j).1
    have hxe : x = ∑ j, κ j • ((letE d : LetA O n) • b j) + π' • y := by
      conv_lhs => rw [← hxl', hxa, Finset.smul_sum]
      rw [hydef, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, hkey j, add_smul, smul_smul, ← algebraMap_smul (LetA O n) (κ j), smul_smul]
    have hdiff : (⟨x, ⟨⟨hxN, hxΔ⟩, hxl⟩⟩ : ↥(NcS W T d)) - ∑ j, κ j • ⟨_, hmem j⟩ ∈
        (PiNS W T π' 1).comap (NcS W T d).subtype := by
      rw [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      have he : x - ∑ j, κ j • ((letE d : LetA O n) • b j) = π' • y := by rw [hxe]; abel
      rw [he]
      refine ⟨⟨y, hyN, ?_⟩, ?_⟩
      · show ((π' ^ 1 : LetA O n) • LinearMap.id : W.DD T →ₗ[LetA O n] W.DD T) y = π' • y
        rw [pow_one]; rfl
      · rw [← he]
        refine sub_mem hxΔ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem j).1.2)
    have hq : (Submodule.Quotient.mk (⟨x, ⟨⟨hxN, hxΔ⟩, hxl⟩⟩ : ↥(NcS W T d)) : LcQ W T π' c) = ∑ j, κ j • v j := by
      rw [(Submodule.Quotient.eq _).2 hdiff, ← Submodule.mkQ_apply, map_sum]
      simp only [map_smul, Submodule.mkQ_apply]
      rfl
    rw [hq]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp⟩

theorem finite_L [IsDomain O] (π' : LetA O n) (s' : ℕ) (hs : 1 ≤ s') (w₁ : (LetA O n)ˣ)
    (hπ : π' = w₁ * (letπ : LetA O n) ^ s')
    (huniq : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O, ∀ i, a i = PowerSeries.subst (π' i) (f i))
    {r : ℕ} (b : Fin r → W.DD T) (hbΔ : ∀ j, b j ∈ W.NΔ T)
    (hbu : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (hbe : ∀ x ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W (a j)) ∧ x = ∑ j, a j • b j)
    (c : ZMod n) : Module.Finite O (LcQ W T π' c) := by
  exact Module.Finite.of_basis (basis_L W T π' s' hs w₁ hπ huniq b hbΔ hbu hbe c).some

end Formalism.MainNotions.N.Ln34.MQ
