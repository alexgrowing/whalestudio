import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer
import Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobPiNPf
import Formalism.PadicSubsetSums.StableGradedCounts.ARCReuse

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem w_div {R : Type*} [CommRing R] (c L : R) (hc : IsUnit c) (l : ℕ) [Fact l.Prime]
    (hP : ∀ N : ℕ, ∃ b : R, L ^ (N + padicValNat l N.factorial) =
      b * ∏ y ∈ Finset.Ico 1 (N + 1), (c ^ y - 1))
    (a k : ℕ) (hk : k < 2 * a) :
    (∏ m ∈ (Finset.range (2 * a)).erase k, (c ^ k - c ^ m)) ∣
      L ^ (2 * a - 1 + padicValNat l (2 * a - 1).factorial) := by
  have hsplit : (Finset.range (2 * a)).erase k = Finset.range k ∪ Finset.Ico (k + 1) (2 * a) := by
    ext m; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range k) (Finset.Ico (k + 1) (2 * a)) := by
    rw [Finset.disjoint_left]; intro m h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
  have hA : ∏ m ∈ Finset.range k, (c ^ k - c ^ m) =
      (∏ m ∈ Finset.range k, c ^ m) * ∏ y ∈ Finset.Ico 1 (k + 1), (c ^ y - 1) := by
    have e1 : ∀ m ∈ Finset.range k, c ^ k - c ^ m = c ^ m * (c ^ (k - m) - 1) := by
      intro m hm
      have hm' := Finset.mem_range.1 hm
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hm'.le]
    rw [Finset.prod_congr rfl e1, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_Ico_eq_prod_range, show k + 1 - 1 = k by omega,
      ← Finset.prod_range_reflect (fun j => c ^ (1 + j) - 1) k]
    refine Finset.prod_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.1 hm
    show c ^ (k - m) - 1 = c ^ (1 + (k - 1 - m)) - 1
    rw [show 1 + (k - 1 - m) = k - m by omega]
  have hB : ∏ m ∈ Finset.Ico (k + 1) (2 * a), (c ^ k - c ^ m) =
      (∏ m ∈ Finset.Ico (k + 1) (2 * a), -(c ^ k)) *
        ∏ y ∈ Finset.Ico 1 (2 * a - 1 - k + 1), (c ^ y - 1) := by
    have e2 : ∀ m ∈ Finset.Ico (k + 1) (2 * a), c ^ k - c ^ m = -(c ^ k) * (c ^ (m - k) - 1) := by
      intro m hm
      have hm' := (Finset.mem_Ico.1 hm).1
      have e : c ^ m = c ^ k * c ^ (m - k) := by rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      rw [e]; ring
    rw [Finset.prod_congr rfl e2, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range,
      show 2 * a - 1 - k + 1 - 1 = 2 * a - (k + 1) by omega]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [show k + 1 + j - k = 1 + j by omega]
  have hU₁ : IsUnit (∏ m ∈ Finset.range k, c ^ m) := by
    rw [Finset.prod_pow_eq_pow_sum]; exact hc.pow _
  have hU₂ : IsUnit (∏ m ∈ Finset.Ico (k + 1) (2 * a), -(c ^ k)) := by
    rw [Finset.prod_const]; exact (hc.pow k).neg.pow _
  obtain ⟨b₁, hb₁⟩ := hP k
  obtain ⟨b₂, hb₂⟩ := hP (2 * a - 1 - k)
  have h1 : (∏ m ∈ Finset.range k, c ^ m) * ∏ y ∈ Finset.Ico 1 (k + 1), (c ^ y - 1) ∣
      L ^ (k + padicValNat l k.factorial) :=
    hU₁.mul_left_dvd.2 (Dvd.intro_left _ hb₁.symm)
  have h2 : (∏ m ∈ Finset.Ico (k + 1) (2 * a), -(c ^ k)) *
      ∏ y ∈ Finset.Ico 1 (2 * a - 1 - k + 1), (c ^ y - 1) ∣
      L ^ (2 * a - 1 - k + padicValNat l (2 * a - 1 - k).factorial) :=
    hU₂.mul_left_dvd.2 (Dvd.intro_left _ hb₂.symm)
  have hv : padicValNat l k.factorial + padicValNat l (2 * a - 1 - k).factorial ≤
      padicValNat l (2 * a - 1).factorial := by
    have hkN : k ≤ 2 * a - 1 := by omega
    have hd := Nat.factorial_mul_factorial_dvd_factorial hkN
    rw [← padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
    exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).1 (dvd_trans pow_padicValNat_dvd hd)
  rw [hsplit, Finset.prod_union hdisj, hA, hB]
  refine dvd_trans ?_ (pow_dvd_pow L (show k + padicValNat l k.factorial +
    (2 * a - 1 - k + padicValNat l (2 * a - 1 - k).factorial) ≤
      2 * a - 1 + padicValNat l (2 * a - 1).factorial by omega))
  rw [pow_add]
  exact mul_dvd_mul h1 h2

theorem w_coker {R V : Type} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V]
    (γ ϖ : Module.End R V) (V₂ N' : Submodule R V) (a : ℕ) (c d : R)
    (hinj : Function.Injective ϖ) (hst : ∀ x ∈ N', ϖ x ∈ N') (hin : ∀ x ∈ V₂, (ϖ ^ a) x ∈ N')
    (hV : ∀ (i : ℕ), ∀ x ∈ V₂, ∃ y ∈ V₂, γ ((ϖ ^ i) x) - c ^ i • (ϖ ^ i) x = (ϖ ^ (i + 1)) y)
    (hN : ∀ (i : ℕ), ∀ x ∈ N', ∃ y ∈ N', γ ((ϖ ^ i) x) - c ^ i • (ϖ ^ i) x = (ϖ ^ (i + 1)) y)
    (hd : ∀ k ∈ Finset.range (2 * a), (∏ m ∈ (Finset.range (2 * a)).erase k, (c ^ k - c ^ m)) ∣ d)
    (hd0 : d ≠ 0) : ∀ x ∈ V₂, d • x ∈ N' := by
  intro x hx
  set W : Submodule R V := N'.map (ϖ ^ a) with hWdef
  have hW : W ≤ W.comap γ := by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨y, hy, hyy⟩ := hN a z hz
    have e : γ ((ϖ ^ a) z) = (ϖ ^ a) (c ^ a • z + ϖ y) := by
      have e0 : (ϖ ^ a) (ϖ y) = (ϖ ^ (a + 1)) y := by rw [pow_succ, Module.End.mul_apply]
      rw [map_add, map_smul, e0, ← hyy]; abel
    show γ ((ϖ ^ a) z) ∈ W
    rw [e]
    exact ⟨_, N'.add_mem (N'.smul_mem _ hz) (hst y hy), rfl⟩
  have h1 : Polynomial.aeval γ (∏ i ∈ Finset.range a, (Polynomial.X - Polynomial.C (c ^ i)))
      ((ϖ ^ a) x) ∈ W := by
    have := Formalism.IrreducibleCountingLemmas.WindowSums.filtered_product R V γ (fun i => N'.map (ϖ ^ i)) (fun i => c ^ i) 0 a
      (by
        rintro i _ _ w ⟨z, hz, rfl⟩
        obtain ⟨y, hy, hyy⟩ := hN i z hz
        exact ⟨y, hy, hyy.symm⟩)
      ((ϖ ^ a) x) ⟨(ϖ ^ a) x, hin x hx, by simp⟩
    rw [Finset.range_eq_Ico]
    rw [zero_add] at this
    exact this
  have h2 : Polynomial.aeval γ (∏ i ∈ Finset.Ico a (2 * a), (Polynomial.X - Polynomial.C (c ^ i)))
      ((ϖ ^ a) x) ∈ W := by
    have := Formalism.IrreducibleCountingLemmas.WindowSums.filtered_product R V γ (fun i => V₂.map (ϖ ^ i)) (fun i => c ^ i) a a
      (by
        rintro i _ _ w ⟨z, hz, rfl⟩
        obtain ⟨y, hy, hyy⟩ := hV i z hz
        exact ⟨y, hy, hyy.symm⟩)
      ((ϖ ^ a) x) ⟨x, hx, rfl⟩
    rw [two_mul]
    obtain ⟨t, ht, hte⟩ := this
    rw [← hte, pow_add, Module.End.mul_apply]
    exact ⟨_, hin t ht, rfl⟩
  have hinjOn : Set.InjOn (fun k => c ^ k) (↑(Finset.range (2 * a)) : Set ℕ) := by
    intro k hk m hm hkm
    by_contra hne
    have hkm' : c ^ k = c ^ m := hkm
    have hdk := hd k (Finset.mem_coe.1 hk)
    have hz : ∏ j ∈ (Finset.range (2 * a)).erase k, (c ^ k - c ^ j) = 0 :=
      Finset.prod_eq_zero (i := m) (Finset.mem_erase.2 ⟨Ne.symm hne, Finset.mem_coe.1 hm⟩)
        (by rw [hkm', sub_self])
    rw [hz, zero_dvd_iff] at hdk
    exact hd0 hdk
  have hL := Formalism.WindowSums.arc_Lagrange R (V ⧸ W) (W.mapQ W γ hW) (Finset.range (2 * a)) (Finset.range a)
    (fun k => c ^ k) d (W.mkQ ((ϖ ^ a) x)) (by intro k hk; simp only [Finset.mem_range] at hk ⊢; omega) hinjOn
    (by rw [Formalism.IrreducibleCountingLemmas.WindowSums.aeval_mapQ]; exact (Submodule.Quotient.mk_eq_zero W).mpr h1)
    (by
      rw [Formalism.ZetaNonvanishing.ARCV.range_sdiff_range, Formalism.IrreducibleCountingLemmas.WindowSums.aeval_mapQ]
      exact (Submodule.Quotient.mk_eq_zero W).mpr h2)
    hd
  rw [← map_smul] at hL
  obtain ⟨x', hx', hxx⟩ := (Submodule.Quotient.mk_eq_zero W).mp hL
  rw [← map_smul] at hxx
  have hinja : Function.Injective (ϖ ^ a) := by
    rw [Module.End.coe_pow]; exact hinj.iterate a
  rw [← hinja hxx]
  exact hx'

section WLocal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem w_lin {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (p C T : A) (i : ℕ) (u v : M) :
    (p ^ i * (C + p * T)) • (u + p • v) - C • (p ^ i • u) = p ^ (i + 1) • (C • v + T • (u + p • v)) := by
  module

theorem w_grad (T : LocLat G Qp LL O) (π' f : LetA O n) (c₀ : O) (hf : W.γA W.gam π' = π' * f)
    (htf : ∀ i : ℕ, ∃ ti ∈ W.AΔ, f ^ i = algebraMap O (LetA O n) c₀ ^ i + π' * ti)
    (X : Submodule O (W.DD T)) (hXγ : ∀ z ∈ X, W.γD T W.gam z ∈ X)
    (hXA : ∀ b ∈ W.AΔ, ∀ z ∈ X, b • z ∈ X)
    (hX1 : ∀ z ∈ X, ∃ z' ∈ X, W.γD T W.gam z - z = π' • z') (i : ℕ) (z : W.DD T) (hz : z ∈ X) :
    ∃ y ∈ X, W.γD T W.gam (π' ^ i • z) - c₀ ^ i • (π' ^ i • z) = π' ^ (i + 1) • y := by
  obtain ⟨ti, hti, hfi⟩ := htf i
  obtain ⟨z', hz', hzz⟩ := hX1 z hz
  refine ⟨algebraMap O (LetA O n) c₀ ^ i • z' + ti • W.γD T W.gam z,
    X.add_mem (hXA _ (W.AΔ.pow_mem (W.AΔ.algebraMap_mem _) _) z' hz') (hXA ti hti _ (hXγ z hz)), ?_⟩
  have hγz : W.γD T W.gam z = z + π' • z' := by rw [← hzz]; abel
  have hc : c₀ ^ i • (π' ^ i • z) = (algebraMap O (LetA O n) c₀ ^ i) • (π' ^ i • z) := by
    rw [← map_pow, algebraMap_smul]
  rw [hc, gradNPf_γD_smul, map_pow, hf, mul_pow, hfi, hγz]
  exact w_lin π' _ ti i z z'

theorem w_local [IsDomain O] (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (π' f t : LetA O n)
    (c₀ d : O) (s' : ℕ) (w : (LetA O n)ˣ) (hw : π' = (w : LetA O n) * letπ ^ s') (hπA : π' ∈ W.AΔ)
    (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π') (hEE : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hf : W.γA W.gam π' = π' * f) (ht : f - algebraMap O (LetA O n) c₀ = π' * t)
    (hγ₁ : ∀ y ∈ W.NΔ T₁, ∃ e ∈ W.N T₁, W.γD T₁ W.gam y - y = π' • e)
    (hγ₂ : ∀ y ∈ W.NΔ T₂, ∃ e ∈ W.N T₂, W.γD T₂ W.gam y - y = π' • e)
    (a : ℕ) (hW1 : ∀ c : ZMod n, ∀ y ∈ NcS W T₂ c, ∃ x ∈ NcS W T₁ c, W.map F x = π' ^ a • y)
    (hd : ∀ k ∈ Finset.range (2 * a),
      (∏ m ∈ (Finset.range (2 * a)).erase k, (c₀ ^ k - c₀ ^ m)) ∣ d) (hd0 : d ≠ 0) :
    ∀ c : ZMod n, ∀ y ∈ NcS W T₂ c, ∃ x ∈ NcS W T₁ c, W.map F x = d • y := by
  intro c y hy
  have hfΔ : f ∈ W.AΔ := gradNPf_fΔ W s' w π' f hw hπΔ hf
  have htΔ : t ∈ W.AΔ := fun δ hδ => by
    apply Formalism.MainNotions.LiftingTheory.unit_mul_pi_pow_left_cancel w s'
    rw [← hw]
    have h := congrArg (W.γA δ) ht
    rw [map_sub, map_mul, hfΔ δ hδ, AlgHom.commutes, hπΔ δ hδ] at h
    rw [← h, ht]
  have htf : ∀ i : ℕ, ∃ ti ∈ W.AΔ, f ^ i = algebraMap O (LetA O n) c₀ ^ i + π' * ti := by
    intro i
    induction i with
    | zero => exact ⟨0, W.AΔ.zero_mem, by simp⟩
    | succ i ih =>
      obtain ⟨ti, hti, e⟩ := ih
      refine ⟨algebraMap O (LetA O n) c₀ ^ i * t + ti * algebraMap O (LetA O n) c₀ + π' * ti * t,
        W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (W.AΔ.algebraMap_mem _) _) htΔ)
          (W.AΔ.mul_mem hti (W.AΔ.algebraMap_mem _))) (W.AΔ.mul_mem (W.AΔ.mul_mem hπA hti) htΔ), ?_⟩
      have hf' : f = algebraMap O (LetA O n) c₀ + π' * t := by linear_combination ht
      rw [pow_succ, e, hf']
      ring
  have hNcγ : ∀ (T : LocLat G Qp LL O), ∀ z ∈ NcS W T c, W.γD T W.gam z ∈ NcS W T c := by
    intro T z hz
    obtain ⟨hzN, hzΔ, hzl⟩ := (mem_NcS W T c z).1 hz
    exact (mem_NcS W T c _).2 ⟨W.N_Γ T _ z hzN,
      fun δ hδ => by rw [← W.γD_mul, mul_comm, W.γD_mul, hzΔ δ hδ], by rw [← γD_letE, hzl]⟩
  have hNcA : ∀ (T : LocLat G Qp LL O), ∀ b ∈ W.AΔ, ∀ z ∈ NcS W T c, b • z ∈ NcS W T c := by
    intro T b hb z hz
    obtain ⟨hzN, hzΔ, hzl⟩ := (mem_NcS W T c z).1 hz
    exact (mem_NcS W T c _).2 ⟨(W.N T).smul_mem b hzN,
      fun δ hδ => by rw [gradNPf_γD_smul, hb δ hδ, hzΔ δ hδ], by rw [smul_comm, hzl]⟩
  have hNc1 : ∀ (T : LocLat G Qp LL O),
      (∀ y ∈ W.NΔ T, ∃ e ∈ W.N T, W.γD T W.gam y - y = π' • e) →
      ∀ z ∈ NcS W T c, ∃ z' ∈ NcS W T c, W.γD T W.gam z - z = π' • z' := by
    intro T hγT z hz
    obtain ⟨hzN, hzΔ, hzl⟩ := (mem_NcS W T c z).1 hz
    obtain ⟨e, he, hee⟩ := hγT z ⟨hzN, hzΔ⟩
    refine ⟨e, (mem_NcS W T c e).2 ⟨he, fun δ hδ => ?_, ?_⟩, hee⟩
    · rw [← sub_eq_zero]
      apply gradNPf_tf W T π' hEE
      have h1 : W.γD T δ (π' • e) = π' • W.γD T δ e := by rw [gradNPf_γD_smul, hπΔ δ hδ]
      have h2 : W.γD T δ (W.γD T W.gam z - z) = W.γD T W.gam z - z := by
        rw [map_sub, ← W.γD_mul, mul_comm, W.γD_mul, hzΔ δ hδ]
      rw [smul_sub, ← h1, ← hee, h2, sub_self]
    · rw [← sub_eq_zero]
      apply gradNPf_tf W T π' hEE
      have h3 : (letE c : LetA O n) • (W.γD T W.gam z - z) = W.γD T W.gam z - z := by
        rw [smul_sub, ← γD_letE, hzl]
      rw [smul_sub, smul_comm, ← hee, h3, sub_self]
  let ϖ : Module.End O (W.DD T₂) := (Formalism.MainNotions.DeltaInvariantLattices.smulA W T₂ π').restrictScalars O
  have hϖ1 : ∀ z, ϖ z = π' • z := fun z => rfl
  have hϖ : ∀ (i : ℕ) (z : W.DD T₂), (ϖ ^ i) z = π' ^ i • z := by
    intro i
    induction i with
    | zero => intro z; simp
    | succ i ih => intro z; rw [pow_succ', Module.End.mul_apply, ih, hϖ1, smul_smul, ← pow_succ']
  set N' : Submodule O (W.DD T₂) := (NcS W T₁ c).map ((W.map F).restrictScalars O) with hN'
  have hmem : ∀ z, z ∈ N' ↔ ∃ x ∈ NcS W T₁ c, W.map F x = z := fun z => by
    rw [hN', Submodule.mem_map]; rfl
  have hXγ : ∀ z ∈ N', W.γD T₂ W.gam z ∈ N' := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (hmem z).1 hz
    exact (hmem _).2 ⟨_, hNcγ T₁ x hx, W.map_γ F _ x⟩
  have hXA : ∀ b ∈ W.AΔ, ∀ z ∈ N', b • z ∈ N' := by
    intro b hb z hz
    obtain ⟨x, hx, rfl⟩ := (hmem z).1 hz
    exact (hmem _).2 ⟨_, hNcA T₁ b hb x hx, map_letA_smul W T₁ F b x⟩
  have hX1 : ∀ z ∈ N', ∃ z' ∈ N', W.γD T₂ W.gam z - z = π' • z' := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (hmem z).1 hz
    obtain ⟨x', hx', hxe⟩ := hNc1 T₁ hγ₁ x hx
    refine ⟨W.map F x', (hmem _).2 ⟨x', hx', rfl⟩, ?_⟩
    rw [← W.map_γ, ← map_sub, hxe, map_letA_smul]
  have hinj : Function.Injective ϖ := by
    intro z z' h
    have h0 : π' • z = π' • z' := h
    have h' : π' • (z - z') = 0 := by rw [smul_sub, h0, sub_self]
    exact sub_eq_zero.1 (gradNPf_tf W T₂ π' hEE _ h')
  have hst : ∀ z ∈ N', ϖ z ∈ N' := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (hmem z).1 hz
    exact (hmem _).2 ⟨π' • x, hNcA T₁ π' hπA x hx, map_letA_smul W T₁ F π' x⟩
  have hin : ∀ z ∈ NcS W T₂ c, (ϖ ^ a) z ∈ N' := by
    intro z hz
    rw [hϖ]
    obtain ⟨x, hx, e⟩ := hW1 c z hz
    exact (hmem _).2 ⟨x, hx, e⟩
  have hV : ∀ (i : ℕ), ∀ z ∈ NcS W T₂ c, ∃ y ∈ NcS W T₂ c,
      W.γD T₂ W.gam ((ϖ ^ i) z) - c₀ ^ i • (ϖ ^ i) z = (ϖ ^ (i + 1)) y := by
    intro i z hz
    obtain ⟨y, hy, e⟩ := w_grad W T₂ π' f c₀ hf htf (NcS W T₂ c) (hNcγ T₂) (hNcA T₂) (hNc1 T₂ hγ₂) i z hz
    exact ⟨y, hy, by rw [hϖ, hϖ]; exact e⟩
  have hN : ∀ (i : ℕ), ∀ z ∈ N', ∃ y ∈ N',
      W.γD T₂ W.gam ((ϖ ^ i) z) - c₀ ^ i • (ϖ ^ i) z = (ϖ ^ (i + 1)) y := by
    intro i z hz
    obtain ⟨y, hy, e⟩ := w_grad W T₂ π' f c₀ hf htf N' hXγ hXA hX1 i z hz
    exact ⟨y, hy, by rw [hϖ, hϖ]; exact e⟩
  exact (hmem _).1 (w_coker (W.γD T₂ W.gam) ϖ (NcS W T₂ c) N' a c₀ d hinj hst hin hV hN hd hd0 y hy)

theorem w_avg (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (π' : LetA O n)
    (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π') (a : ℕ) (d₀ : O) (hd₀ : d₀ * (W.DelF.card : O) = 1)
    (h3 : ∀ c : ZMod n, ∀ y ∈ NcS W T₂ c, π' ^ a • y ∈ (W.Nl T₁ c).map (Formalism.MainNotions.DeltaInvariantLattices.mapA W F)) :
    ∀ c : ZMod n, ∀ y ∈ NcS W T₂ c, ∃ z ∈ NcS W T₁ c, W.map F z = π' ^ a • y := by
  intro c y hy
  obtain ⟨-, hyΔ, -⟩ := (mem_NcS W T₂ c y).1 hy
  obtain ⟨z, hz, hze⟩ := Submodule.mem_map.1 (h3 c y hy)
  obtain ⟨z₀, hz₀, hz₀e⟩ := Submodule.mem_map.1 hz
  have hidem : (letE c : LetA O n) * letE c = letE c := by
    funext i
    simp only [letE, Pi.mul_apply, Pi.single_apply]
    split_ifs <;> simp
  have hzz : z = (letE c : LetA O n) • z₀ := by rw [← hz₀e]; rfl
  have hzN : z ∈ W.N T₁ := by rw [hzz]; exact Submodule.smul_mem _ _ hz₀
  have hzl : (letE c : LetA O n) • z = z := by rw [hzz, smul_smul, hidem]
  have hze' : W.map F z = π' ^ a • y := hze
  have hlet : (letE c : LetA O n) ∈ W.AΔ := fun δ _ => Formalism.MainNotions.LiftingTheory.wmap_γA_letE W δ c
  refine ⟨Formalism.MainNotions.LiftingTheory.lifta_avg W T₁ d₀ z, (mem_NcS W T₁ c _).2
    ⟨(Formalism.MainNotions.LiftingTheory.lifta_avg_N W T₁ d₀ z hzN).1, Formalism.MainNotions.LiftingTheory.lifta_avg_inv W T₁ d₀ z, ?_⟩, ?_⟩
  · rw [← Formalism.MainNotions.LiftingTheory.lifta_avg_smul W T₁ d₀ _ hlet z, hzl]
  · have hΔ' : ∀ δ ∈ W.DelF, W.γD T₂ δ (π' ^ a • y) = π' ^ a • y := by
      intro δ hδ
      rw [gradNPf_γD_smul, map_pow, hπΔ δ hδ, hyΔ δ hδ]
    rw [Formalism.MainNotions.LiftingTheory.lifta_avg_map, hze', Formalism.MainNotions.LiftingTheory.lifta_avg_fix W T₂ d₀ hd₀ _ hΔ']

end WLocal

set_option maxHeartbeats 1000000 in
theorem w_pf : Formalism.MainNotions.N.Ln34.WStep := by
  intro D HW F Cm CA CB CK hA l hlp hl K LL hG π' E hR T₁ T₂ Fm h' hT₁ hT₂ hOnto hJ
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs : 1 ≤ sK l K := frobpin_sK_pos hl K LL hG
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hl2 : 2 ≤ l := hlp.out.two_le
  obtain ⟨f, t, x, u, hu, hxu, hf, ht, hEE, hπΔ, hγ₂, -, hP⟩ :=
    gradNPf_hyps D HW F Cm hA.1 l hl K LL hG π' E hR T₂ hT₂ hs
  obtain ⟨_, _, _, _, -, -, -, -, -, -, hγ₁, -, -⟩ :=
    gradNPf_hyps D HW F Cm hA.1 l hl K LL hG π' E hR T₁ hT₁ hs
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hlv : (D.loc l).v LL (l : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hlO : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL))) = 1 := by
    rw [map_natCast]
    exact hlv
  have hxU : IsUnit x := by
    have h1 := gradNPf_unit_one_add ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv
      (l : ↥(OL LL)) u hlO
    rwa [show 1 + (l : ↥(OL LL)) * u = x by linear_combination -hxu] at h1
  have hl0 : (l : ↥(OL LL)) ≠ 0 := by
    intro h0
    rw [h0, map_zero, AddValuation.map_zero] at hlO
    exact WithTop.top_ne_one hlO
  obtain ⟨w, hw⟩ := hR.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := hA.1 l K 1 LL hG
  have hcard : ((HW l).W K 1 LL hG).DelF.card = sK l K := by
    rw [(h9W T₂ hT₂ hs1 hp).1, hpl]
  have hsl : ¬ l ∣ sK l K :=
    Nat.not_dvd_of_pos_of_lt hs (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
  have hunit : IsUnit ((sK l K : ℕ) : ↥(OL LL)) :=
    gradNPf_unit_nat ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv l hlp.out hlv (sK l K) hsl
  set d₀ : ↥(OL LL) := ((hunit.unit⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)) with hd₀def
  have hd₀ : d₀ * (((HW l).W K 1 LL hG).DelF.card : ↥(OL LL)) = 1 := by
    rw [hcard, hd₀def]; exact hunit.val_inv_mul
  set a' : ℕ := ⌈(((finrank ↥(K0 K) ↥K.1 * ⨆ _j : ZMod (finrank ℚ_[l] ↥(K0 K)), (h' + h') : ℕ)) : ℚ) /
      ((((D.loc l).PD K).p : ℚ) - 1)⌉₊ with ha'
  set r : ℝ := (2 * eK K * h' : ℝ) / ((l : ℝ) - 1) with hr
  have hae : a' = ⌈r⌉₊ := by
    rw [ha', ciSup_const, hpl]
    set q : ℚ := (((eK K * (h' + h') : ℕ)) : ℚ) / ((l : ℚ) - 1) with hq
    have hqr : ((q : ℚ) : ℝ) = r := by rw [hq, hr]; push_cast; ring
    apply le_antisymm
    · rw [Nat.ceil_le]
      have h1 : ((q : ℚ) : ℝ) ≤ ((⌈r⌉₊ : ℕ) : ℝ) := by rw [hqr]; exact Nat.le_ceil r
      exact_mod_cast h1
    · rw [Nat.ceil_le, ← hqr]
      exact_mod_cast Nat.le_ceil q
  have hL := hA.2.2.2.2.2.1 l K 1 LL hG T₁ T₂ Fm (fun _ => h') (fun _ => h') hT₁ hT₂
  have h3 : ∀ c, ∀ y ∈ NcS ((HW l).W K 1 LL hG) T₂ c,
      π' ^ a' • y ∈ (((HW l).W K 1 LL hG).Nl T₁ c).map (Formalism.MainNotions.DeltaInvariantLattices.mapA _ Fm) := by
    intro c y hy
    obtain ⟨hyN, hyΔ, hyl⟩ := (mem_NcS _ T₂ c y).1 hy
    exact (hL hOnto (fun τ i _ => hJ τ)).2 hs1 π' hR.1 ⟨w, by rw [hw, hpl]⟩ c y
      (Submodule.mem_map.2 ⟨y, hyN, by rw [LinearMap.smul_apply, LinearMap.id_apply, hyl]⟩)
      (fun δ hδ => by rw [hyΔ δ hδ, sub_self]; exact Submodule.zero_mem _)
  have hW1 := w_avg _ T₁ T₂ Fm π' hπΔ a' d₀ hd₀ h3
  have hd : ∀ k ∈ Finset.range (2 * a'),
      (∏ m ∈ (Finset.range (2 * a')).erase k, ((x ^ sK l K) ^ k - (x ^ sK l K) ^ m)) ∣
        (l : ↥(OL LL)) ^ rhoA l (eK K) h' := by
    intro k hk
    have e : rhoA l (eK K) h' = 2 * a' - 1 + padicValNat l (2 * a' - 1).factorial := by
      rw [hae]; rfl
    rw [e]
    exact w_div (x ^ sK l K) (l : ↥(OL LL)) (hxU.pow _) l hP a' k (Finset.mem_range.1 hk)
  intro c y hy
  rw [hpl]
  exact w_local _ T₁ T₂ Fm π' f t (x ^ sK l K) ((l : ↥(OL LL)) ^ rhoA l (eK K) h') (sK l K) w hw hR.1
    hπΔ hEE hf ht hγ₁ hγ₂ a' hW1 hd (pow_ne_zero _ hl0) c y hy

end Formalism.MainNotions.N.Ln34
