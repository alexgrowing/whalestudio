import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorCmDifferentIdealScaled
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise nonZeroDivisors

noncomputable section

namespace GlobalTheory.ThetaLatIndex

theorem relIndex_pi_const {ι G : Type} [Fintype ι] [AddCommGroup G] (L L' : AddSubgroup G) :
    (AddSubgroup.pi Set.univ fun _ : ι => L').relIndex (AddSubgroup.pi Set.univ fun _ : ι => L) =
      L'.relIndex L ^ Fintype.card ι := by
  let f : (AddSubgroup.pi Set.univ fun _ : ι => L) →+ (ι → L) :=
    { toFun := fun x i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y => ⟨⟨fun i => y i, fun i _ => (y i).2⟩, rfl⟩
  have hc : (AddSubgroup.pi Set.univ fun _ : ι => L').addSubgroupOf
      (AddSubgroup.pi Set.univ fun _ : ι => L) =
      (AddSubgroup.pi Set.univ fun _ : ι => L'.addSubgroupOf L).comap f := by
    ext x
    simp [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi, f]
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_comap_of_surjective _ hf, AddSubgroup.index_pi]
  simp [AddSubgroup.relIndex]

section General

variable {R K M : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower R K M]

def mulL (I : Submodule R K) (L : Submodule R M) : Submodule R M :=
  Submodule.span R {v | ∃ t ∈ I, ∃ y ∈ L, v = t • y}

theorem exists_gen_inv (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) {n : R} (hn : n ≠ 0) :
    ∃ t ∈ I, (∀ s ∈ I, ∃ a : R, ∃ s' ∈ I, s = a • t + n • s') ∧
      ∃ t' : K, ∃ a : R, (∀ s ∈ I, ∃ b : R, algebraMap R K b = t' * s) ∧ t' * t + algebraMap R K (a * n) = 1 := by
  have hn' : (FractionalIdeal.spanSingleton R⁰ (algebraMap R K n)) ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hn
  have hle : FractionalIdeal.spanSingleton R⁰ (algebraMap R K n) * I ≤ I :=
    FractionalIdeal.spanSingleton_mul_le_iff.2 fun z hz => by
      rw [← Algebra.smul_def]; exact (I : Submodule R K).smul_mem n hz
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_add_spanSingleton_mul_eq hle (mul_ne_zero hn' hI) one_ne_zero
  rw [mul_one] at ht
  refine ⟨t, ?_, fun s hs => ?_, ?_⟩
  · rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← ht, ← FractionalIdeal.sup_eq_add]
    exact le_sup_right
  · rw [← ht, FractionalIdeal.mem_add] at hs
    obtain ⟨i, hi, j, hj, rfl⟩ := hs
    obtain ⟨s', hs', rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hi
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hj
    exact ⟨a, s', hs', by rw [add_comm, Algebra.smul_def n]⟩
  · have h1 : FractionalIdeal.spanSingleton R⁰ (algebraMap R K n) + FractionalIdeal.spanSingleton R⁰ t * I⁻¹ = 1 := by
      have := congrArg (· * I⁻¹) ht
      simpa only [add_mul, mul_assoc, mul_inv_cancel₀ hI, mul_one] using this
    have h2 : (1 : K) ∈ FractionalIdeal.spanSingleton R⁰ (algebraMap R K n) + FractionalIdeal.spanSingleton R⁰ t * I⁻¹ := by
      rw [h1]; exact FractionalIdeal.one_mem_one _
    rw [FractionalIdeal.mem_add] at h2
    obtain ⟨i, hi, j, hj, e⟩ := h2
    obtain ⟨t', ht', rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hj
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    refine ⟨t', a, fun s hs => ?_, ?_⟩
    · have := FractionalIdeal.mul_mem_mul ht' hs
      rw [inv_mul_cancel₀ hI] at this
      exact (FractionalIdeal.mem_one_iff _).1 this
    · rw [← e, map_mul, Algebra.smul_def]; ring

theorem relIndex_mulL (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) {n : R} (hn : n ≠ 0) (L L₀ : Submodule R M)
    (h : ∀ x ∈ L₀, n • x ∈ L) :
    (mulL (I : Submodule R K) L).toAddSubgroup.relIndex (mulL (I : Submodule R K) L₀).toAddSubgroup =
      L.toAddSubgroup.relIndex L₀.toAddSubgroup := by
  obtain ⟨t, ht, hg, t', a, hi, e⟩ := exists_gen_inv I hI hn
  let f : M →+ M := DistribSMul.toAddMonoidHom M t
  have hf : ∀ x, f x = t • x := fun _ => rfl
  set H := (mulL (I : Submodule R K) L).toAddSubgroup ⊓ (mulL (I : Submodule R K) L₀).toAddSubgroup with hH
  have h1 : (mulL (I : Submodule R K) L₀).toAddSubgroup = L₀.toAddSubgroup.map f ⊔ H := by
    apply le_antisymm
    · have key : ∀ v ∈ mulL (I : Submodule R K) L₀, ∀ o : R, o • v ∈ L₀.toAddSubgroup.map f ⊔ H := by
        intro v hv
        induction hv using Submodule.span_induction with
        | mem v hv =>
          intro o
          obtain ⟨s, hs, y, hy, rfl⟩ := hv
          obtain ⟨b, s', hs', rfl⟩ := hg s hs
          rw [add_smul, smul_add]
          refine AddSubgroup.add_mem_sup ⟨(o * b) • y, L₀.smul_mem _ hy, ?_⟩ ⟨?_, ?_⟩
          · rw [hf, smul_comm, mul_smul, smul_assoc]
          · refine Submodule.smul_mem _ o (Submodule.subset_span ⟨s', hs', n • y, h y hy, ?_⟩)
            rw [smul_assoc, smul_comm]
          · exact Submodule.smul_mem _ o (Submodule.subset_span ⟨_, (I : Submodule R K).smul_mem n hs', y, hy, rfl⟩)
        | zero => intro o; rw [smul_zero]; exact zero_mem _
        | add x y _ _ hx hy => intro o; rw [smul_add]; exact add_mem (hx o) (hy o)
        | smul b x _ hx => intro o; rw [smul_smul]; exact hx _
      intro v hv
      simpa using key v hv 1
    · refine sup_le ?_ inf_le_right
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨t, ht, y, hy, rfl⟩
  have h2 : ∀ v ∈ mulL (I : Submodule R K) L, t' • v ∈ L := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨s, hs, y, hy, rfl⟩ := hv
      obtain ⟨b, hb⟩ := hi s hs
      rw [smul_smul, ← hb, algebraMap_smul]
      exact L.smul_mem b hy
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul b x _ hx => rw [smul_comm]; exact L.smul_mem b hx
  have h3 : H.comap f ⊓ L₀.toAddSubgroup = L.toAddSubgroup ⊓ L₀.toAddSubgroup := by
    ext x
    refine and_congr_left fun hx => ⟨fun hx' => ?_, fun hx' => ⟨?_, ?_⟩⟩
    · have e2 : x = t' • (t • x) + a • (n • x) := by
        rw [smul_smul, smul_smul, ← algebraMap_smul K (a * n) x, ← add_smul, e, one_smul]
      change x ∈ L
      rw [e2]
      exact add_mem (h2 _ hx'.1) (L.smul_mem a (h x hx))
    · exact Submodule.subset_span ⟨t, ht, x, hx', rfl⟩
    · exact Submodule.subset_span ⟨t, ht, x, hx, rfl⟩
  rw [← AddSubgroup.inf_relIndex_right, ← hH, h1, AddSubgroup.relIndex_sup_right, ← AddSubgroup.relIndex_comap,
    ← AddSubgroup.inf_relIndex_right, h3, AddSubgroup.inf_relIndex_right]

end General

open GlobalTheory.InertSign GlobalTheory.ThetaLatImage

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem exists_int_smul {L : Lat D N} (hL : Submodule.span D.host.E (L : Set (Fin N → D.host.E)) = ⊤)
    (x : Fin N → D.host.E) : ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ L := by
  have hx : x ∈ Submodule.span D.host.E (L : Set (Fin N → D.host.E)) := by rw [hL]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hx b
    · rw [mul_smul]; exact zsmul_mem hy a
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    have hc : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ _).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨b, hb, hbc⟩ := hc.exists_integral_multiple
    refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
    have e : (b * a) • c • x = (⟨b • c, hbc⟩ : 𝓞 D.host.E) • (a • x) := by
      change _ = (b • c) • (a • x)
      rw [mul_smul, smul_comm a, smul_assoc]
    rw [e]
    exact L.smul_mem _ hx

theorem exists_common {L : Lat D N} (hL : Submodule.span D.host.E (L : Set (Fin N → D.host.E)) = ⊤) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ stdL D N, n • x ∈ L := by
  choose m hm hm' using fun i : Fin N => exists_int_smul hL (Pi.single i 1)
  refine ⟨∏ i, m i, Finset.prod_ne_zero_iff.2 fun i _ => hm i, fun x hx => ?_⟩
  choose o ho using mem_stdL.1 hx
  have e : x = ∑ i, o i • (Pi.single i 1 : Fin N → D.host.E) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, ← ho, Algebra.smul_def]
  rw [e, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_comm, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
  exact L.smul_mem _ (zsmul_mem (hm' i) _)

theorem idx_ne_zero {L : Lat D N} (hL : SD D L) : idx D L ≠ 0 := by
  obtain ⟨n, hn, h⟩ := exists_common ((sd_iff D L).1 hL).2.1
  have hfg : (stdL D N).FG := Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  haveI : Module.Finite (𝓞 D.host.E) (stdL D N) := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ (stdL D N ⧸ Submodule.comap (stdL D N).subtype L) :=
    Module.Finite.trans (𝓞 D.host.E) _
  haveI : Finite (stdL D N ⧸ Submodule.comap (stdL D N).subtype L) := by
    refine Module.finite_of_fg_torsion _ fun q => ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change n • (Submodule.mkQ (Submodule.comap (stdL D N).subtype L) x) = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h x x.2
  exact Nat.card_pos.ne'

theorem relIndex_Iid (hcc : cc ≠ ⊥) {L : Lat D N} {n : ℤ} (hn : n ≠ 0) (h : ∀ x ∈ stdL D N, n • x ∈ L) :
    (mulL (Iid D cc) L).toAddSubgroup.relIndex (mulL (Iid D cc) (stdL D N)).toAddSubgroup = idx D L :=
  relIndex_mulL (⟨Iid D cc, IdealGenerator.isFractional_Iid D cc⟩ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (fun h => IdealGenerator.Iid_ne_bot D cc hcc (FractionalIdeal.coeToSubmodule_eq_bot.2 h))
    (n := (n : 𝓞 D.host.E)) (Int.cast_ne_zero.2 hn) L (stdL D N)
    fun x hx => by rw [Int.cast_smul_eq_zsmul]; exact h x hx

def cj (D : D7) (N : ℕ) : (Fin N → D.host.E) →+ (Fin N → D.host.E) where
  toFun y j := D.host.conj (y j)
  map_zero' := by funext j; simp
  map_add' x y := by funext j; simp

theorem cj_cj (y : Fin N → D.host.E) : cj D N (cj D N y) = y := funext fun j => conj_conj D (y j)

theorem cj_mem_std {y : Fin N → D.host.E} : cj D N y ∈ stdL D N ↔ y ∈ stdL D N := by
  have : ∀ y, y ∈ stdL D N → cj D N y ∈ stdL D N := fun y hy => mem_stdL.2 fun i => (mem_stdL.1 hy i).conj
  exact ⟨fun h => cj_cj y ▸ this _ h, this y⟩

def cjL (L : Lat D N) : Lat D N where
  carrier := {y | cj D N y ∈ L}
  add_mem' := fun {a b} ha hb => by
    change cj D N (a + b) ∈ L
    rw [map_add]; exact L.add_mem ha hb
  zero_mem' := by
    change cj D N 0 ∈ L
    rw [map_zero]; exact L.zero_mem
  smul_mem' := fun c a ha => by
    have e : cj D N (c • a) = sgO D c • cj D N a := by
      funext j
      change D.host.conj ((c : D.host.E) * a j) = D.host.conj (c : D.host.E) * D.host.conj (a j)
      rw [map_mul]
    change cj D N (c • a) ∈ L
    rw [e]; exact L.smul_mem _ ha

theorem idx_cjL (L : Lat D N) : idx D (cjL L) = idx D L := by
  have e : (stdL D N).toAddSubgroup.map (cj D N) = (stdL D N).toAddSubgroup := by
    ext y
    refine ⟨?_, fun hy => ⟨cj D N y, cj_mem_std.2 hy, cj_cj y⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact cj_mem_std.2 hx
  rw [idx_eq_relIndex, idx_eq_relIndex]
  change (L.toAddSubgroup.comap (cj D N)).relIndex _ = _
  rw [AddSubgroup.relIndex_comap, e]

theorem cjL_std : cjL (stdL D N) = stdL D N := Submodule.ext fun _ => cj_mem_std

theorem span_conj_eq (L : Lat D N) : Submodule.span (𝓞 D.host.E)
    {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)} = mulL (Iid D cc) (cjL L) := by
  unfold mulL
  congr 1
  ext v
  constructor
  · rintro ⟨t, ht, y, hy, rfl⟩
    exact ⟨t, ht, cj D N y, by change cj D N (cj D N y) ∈ L; rwa [cj_cj], rfl⟩
  · rintro ⟨t, ht, y, hy, rfl⟩
    exact ⟨t, ht, cj D N y, hy, congrArg _ (cj_cj y).symm⟩

theorem sd_std : SD D (stdL D N) := by
  refine (sd_iff D _).2 ⟨Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    refine mem_stdL.2 fun i => ?_
    rw [Pi.basisFun_apply, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact sum_mem fun i _ => mul_mem (mem_stdL.1 hy i) (mem_stdL.1 hx i).conj
  · refine mem_stdL.2 fun j => ?_
    have := h (Pi.single j 1) (mem_stdL.2 fun i => by
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _)
    simpa [hE, Pi.single_apply, apply_ite] using this

def ptH (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →+ VC D N N' where
  toFun := pt D (tor0 D cc δ) δ
  map_zero' := pt_zero
  map_add' := pt_add

theorem relIndex_La (hδ : δ ≠ 0) (L L₁ : Lat D N) (L' L₁' : Lat D N') :
    (La D (tor0 D cc δ) L L').relIndex (La D (tor0 D cc δ) L₁ L₁') =
      (RL D cc L L').toAddSubgroup.relIndex (RL D cc L₁ L₁').toAddSubgroup := by
  have e : ∀ (L : Lat D N) (L' : Lat D N'),
      La D (tor0 D cc δ) L L' = (RL D cc L L').toAddSubgroup.map (ptH D cc δ N N') := fun L L' => by
    ext x
    rw [(theta_lattice_image D cc δ hδ N N').2.1]
    exact exists_congr fun z => and_congr_right fun _ => eq_comm
  rw [e, e, AddSubgroup.relIndex_map_map_of_injective _ _ (pt_injective hδ)]

theorem theta_lattice_index : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E), SD D L' → idx D L' ≠ 0 ∧ (La D (tor0 D cc δ) (stdL D N) L').relIndex (La0 D (tor0 D cc δ) N N') = idx D L' ^ N) ∧ ∀ L : Submodule (𝓞 D.host.E) (Fin N → D.host.E), SD D L → idx D L ≠ 0 ∧ (La D (tor0 D cc δ) L (stdL D N')).relIndex (La0 D (tor0 D cc δ) N N') = idx D L ^ N' := by
  intro D cc δ hc N N'
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ hc).2.1
  refine ⟨fun L' hL => ⟨idx_ne_zero hL, ?_⟩, fun L hL => ⟨idx_ne_zero hL, ?_⟩⟩
  · obtain ⟨n, hn, h⟩ := exists_common ((sd_iff D L').1 hL).2.1
    let f : (Fin N → Fin N' → D.host.E) →+ Matrix (Fin N') (Fin N) D.host.E :=
      { toFun := fun w i j => w j i, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have hf : Function.Injective f := fun w w' e => funext fun j => funext fun i => congrFun (congrFun e i) j
    have e : ∀ L' : Lat D N', (RL D cc (stdL D N) L').toAddSubgroup =
        (AddSubgroup.pi Set.univ fun _ : Fin N => (mulL (Iid D cc) L').toAddSubgroup).map f := fun L' => by
      ext z
      refine (mem_RL_cols L' z).trans ⟨fun h => ⟨fun j i => z i j, fun j _ => h j, rfl⟩, ?_⟩
      rintro ⟨w, hw, rfl⟩ j
      exact hw j trivial
    rw [La0, relIndex_La hδ, e, e, AddSubgroup.relIndex_map_map_of_injective _ _ hf, relIndex_pi_const,
      relIndex_Iid hc.1.1 hn h, Fintype.card_fin]
  · obtain ⟨n, hn, h⟩ := exists_common ((sd_iff D L).1 hL).2.1
    have h' : ∀ x ∈ stdL D N, n • x ∈ cjL L := fun x hx => by
      change cj D N (n • x) ∈ L
      rw [map_zsmul]; exact h _ (cj_mem_std.2 hx)
    have e : ∀ L : Lat D N, SD D L → (RL D cc L (stdL D N')).toAddSubgroup =
        (AddSubgroup.pi Set.univ fun _ : Fin N' => (mulL (Iid D cc) (cjL L)).toAddSubgroup) := fun L hL => by
      ext z
      refine (mem_RL_rows L hL z).trans ?_
      rw [span_conj_eq]
      exact ⟨fun h i _ => h i, fun h i => h i trivial⟩
    rw [La0, relIndex_La hδ, e L hL, e _ sd_std, cjL_std]
    refine (relIndex_pi_const _ _).trans ?_
    rw [relIndex_Iid hc.1.1 hn h', idx_cjL, Fintype.card_fin]

end GlobalTheory.ThetaLatIndex
