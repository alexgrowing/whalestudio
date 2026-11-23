import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamLine

variable {D : D7}

def intRing (D : D7) : Subring (AE D) := (GlobalTheory.CharFin.hatRing D.host.F D.host.E).comap (finPart D)

theorem mem_intRing (z : AE D) : z ∈ intRing D ↔ finPart D z ∈ intAE D := by
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact Iff.rfl

theorem finPart_cA (z : AE D) : finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem cA_cA' (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem cA_mem {z : AE D} (hz : z ∈ intRing D) : cA D z ∈ intRing D := by
  rw [mem_intRing] at hz ⊢
  rw [finPart_cA]
  have : intAE D ≤ (intAE D).comap (sigR (Af D.host.F) D.sp.cm.sig).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, rfl⟩
    exact AddSubgroup.subset_closure
      ⟨a, ha, RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E) x, rfl⟩
  exact this hz

def Dvd (N : ℕ) (z : AE D) : Prop :=
  ∃ w ∈ GlobalTheory.CharFin.hatRing D.host.F D.host.E, finPart D z = (N : Af D.host.F ⊗[D.host.F] D.host.E) * w

theorem Dvd.add {N : ℕ} {y z : AE D} (hy : Dvd N y) (hz : Dvd N z) : Dvd N (y + z) := by
  obtain ⟨a, ha, e⟩ := hy
  obtain ⟨b, hb, e'⟩ := hz
  exact ⟨a + b, add_mem ha hb, by rw [RingHom.map_add, e, e', mul_add]⟩

theorem Dvd.mul {N : ℕ} {y z : AE D} (hy : Dvd N y) (hz : z ∈ intRing D) : Dvd N (y * z) := by
  obtain ⟨a, ha, e⟩ := hy
  exact ⟨a * finPart D z, mul_mem ha hz, by rw [map_mul, e, mul_assoc]⟩

theorem dvd_mul {N : ℕ} {z : AE D} (hz : z ∈ intRing D) : Dvd N ((N : AE D) * z) :=
  ⟨finPart D z, hz, by rw [map_mul, map_natCast]⟩

theorem isOpen_dvd {N : ℕ} (hN : 0 < N) : IsOpen {z : AE D | Dvd N z} := by
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, -⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hfc : Continuous (finPart D) := by
    have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
    rw [this]
    exact continuous_snd.comp hec
  have h := (GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E N hN).preimage hfc
  convert h using 1
  ext z
  simp only [Dvd, Set.mem_setOf_eq, Set.mem_preimage, nsmul_eq_mul]
  exact Iff.rfl

theorem isOpen_intRing : IsOpen {z : AE D | z ∈ intRing D} := by
  convert isOpen_dvd (D := D) one_pos using 1
  ext z
  simp only [Dvd, Set.mem_setOf_eq, Nat.cast_one, one_mul, exists_eq_right']
  exact Iff.rfl

theorem eq_one_of_dvd {N : ℕ} (hN : 2 < N) {a : D.host.E} (ha : star a * a = 1) (h : Dvd N (incA D a - 1)) :
    a = 1 := by
  have hc : ∀ (φ : D.host.E →+* ℂ) (y : D.host.E), φ (star y) = starRingEnd ℂ (φ y) :=
    fun φ y => @IsCMField.complexEmbedding_complexConj D.host.E _ _
      (D.host.isCMField_hostE) _ φ y
  obtain ⟨w, hw, e⟩ := h
  refine sub_eq_zero.1 (GlobalTheory.NormOneChar.eq_zero_of_small D.host.F D.host.E hN _ w hw ?_ fun φ => ?_)
  · rw [← e, RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one]
    rfl
  · have h4 := congrArg (fun z => ‖φ z‖) ha
    simp only [map_mul, hc, norm_mul, Complex.norm_conj, map_one, norm_one] at h4
    have h5 : ‖φ a‖ = 1 := by nlinarith [norm_nonneg (φ a)]
    rw [map_sub, map_one]
    refine (norm_sub_le _ _).trans ?_
    rw [h5, norm_one]; norm_num

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unit_nat (k : Type) [Field k] [ValuativeRel k] : ∃ N : ℕ, 2 < N ∧ valuation k (N : k) = 1 := by
  by_contra h
  push_neg at h
  have hle : ∀ n : ℕ, valuation k (n : k) ≤ 1 := fun n => natCast_mem (valuation k).integer n
  have h3 := lt_of_le_of_ne (hle 3) (h 3 (by norm_num))
  have h4 := lt_of_le_of_ne (hle 4) (h 4 (by norm_num))
  have := Valuation.map_sub_lt (valuation k) h4 h3
  norm_num at this

theorem exists_unit_ne_one (h : 2 < Nat.card (IsLocalRing.ResidueField 𝒪[k])) :
    ∃ u : k, valuation k u = 1 ∧ ¬ valuation k (u - 1) < 1 := by
  have : Finite (IsLocalRing.ResidueField 𝒪[k]) := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨r, h0, h1⟩ : ∃ r : IsLocalRing.ResidueField 𝒪[k], r ≠ 0 ∧ r ≠ 1 := by
    have := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[k])
    rw [Nat.card_eq_fintype_card] at h
    classical
    by_contra hh
    push_neg at hh
    have : (Finset.univ : Finset (IsLocalRing.ResidueField 𝒪[k])) ⊆ {0, 1} := fun r _ => by
      by_cases h0 : r = 0
      · simp [h0]
      · simp [hh r h0]
    have h2 := (Finset.card_le_card this).trans Finset.card_le_two
    rw [Finset.card_univ] at h2
    omega
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective r
  have key : ∀ x : 𝒪[k], IsLocalRing.residue 𝒪[k] x ≠ 0 → valuation k (x : k) = 1 := fun x hx =>
    (Valuation.Integers.one_of_isUnit (Valuation.integer.integers (valuation k))
      ((IsLocalRing.residue_ne_zero_iff_isUnit x).1 hx))
  refine ⟨u, key u h0, ?_⟩
  have := key (u - 1) (by rw [map_sub, map_one]; exact sub_ne_zero.2 h1)
  exact (le_of_eq this.symm).not_gt

variable (p : SplitPt D k)

def Near (N : ℕ) (y : AE D) : Prop :=
  cA D y * y = 1 ∧ y ∈ intRing D ∧ Dvd N ((1 - (p.e + cA D p.e)) * (y - 1)) ∧ valuation k (p.pr y - 1) < 1

variable {p} {N : ℕ}

theorem near_one : Near p N 1 :=
  ⟨by simp, one_mem _, ⟨0, zero_mem _, by simp⟩, by simp⟩

theorem Near.val {y : AE D} (h : Near p N y) : valuation k (p.pr y) = 1 := by
  have := Valuation.map_one_add_of_lt (valuation k) h.2.2.2
  rwa [add_sub_cancel] at this

theorem Near.mul {y z : AE D} (hy : Near p N y) (hz : Near p N z) : Near p N (y * z) := by
  refine ⟨?_, mul_mem hy.2.1 hz.2.1, ?_, ?_⟩
  · rw [map_mul, mul_mul_mul_comm, hy.1, hz.1, mul_one]
  · convert (hy.2.2.1.mul hz.2.1).add hz.2.2.1 using 1
    ring
  · have : p.pr (y * z) - 1 = (p.pr y - 1) * p.pr z + (p.pr z - 1) := by rw [map_mul]; ring
    rw [this]
    refine Valuation.map_add_lt _ ?_ hz.2.2.2
    rw [map_mul, hz.val, mul_one]
    exact hy.2.2.2

theorem Near.conj {y : AE D} (hy : Near p N y) : Near p N (cA D y) := by
  refine ⟨by rw [cA_cA', mul_comm, hy.1], cA_mem hy.2.1, ?_, ?_⟩
  · convert hy.2.2.1.mul (neg_mem (cA_mem hy.2.1)) using 1
    linear_combination (1 - (p.e + cA D p.e)) * hy.1
  · have h1 : p.pr (cA D y) * p.pr y = 1 := by rw [← map_mul, hy.1, map_one]
    have h2 : valuation k (p.pr (cA D y)) = 1 := by
      have := congrArg (valuation k) h1
      rwa [map_mul, hy.val, mul_one, map_one] at this
    have : p.pr (cA D y) - 1 = -((p.pr y - 1) * p.pr (cA D y)) := by linear_combination h1
    rw [this, Valuation.map_neg, map_mul, h2, mul_one]
    exact hy.2.2.2

theorem sec_mem {a : k} (ha : valuation k a ≤ 1) : p.sec a ∈ intRing D :=
  (mem_intRing _).2 ((p.int_iff a).1 ha)

theorem e_mem : p.e ∈ intRing D := by
  have := p.sec_pr 1
  rw [map_one, mul_one] at this
  rw [← this]
  exact sec_mem (by simp)

theorem mem_of_supp {y : AE D} (h1 : cA D y * y = 1) (h2 : (p.e + cA D p.e) * (y - 1) = y - 1)
    (h3 : valuation k (p.pr y) = 1) : y ∈ intRing D := by
  have h4 : p.pr (cA D y) * p.pr y = 1 := by rw [← map_mul, h1, map_one]
  have h5 : valuation k (p.pr (cA D y)) = 1 := by
    have := congrArg (valuation k) h4
    rwa [map_mul, h3, mul_one, map_one] at this
  have h6 : y = 1 - (p.e + cA D p.e) + p.sec (p.pr y) + cA D (p.sec (p.pr (cA D y))) := by
    rw [p.sec_pr, p.sec_pr, map_mul, cA_cA']
    linear_combination -h2
  rw [h6]
  exact add_mem (add_mem (sub_mem (one_mem _) (add_mem e_mem (cA_mem e_mem))) (sec_mem h3.le))
    (cA_mem (sec_mem h5.le))

theorem dvd_idem (hN : valuation k (N : k) = 1) : Dvd N (p.e + cA D p.e) := by
  have h0 : (N : k) ≠ 0 := fun h => by simp [h] at hN
  have h1 : p.e = N * p.sec (N : k)⁻¹ := by
    rw [← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul, mul_inv_cancel₀ h0, ← mul_one p.e, ← p.sec_pr, map_one]
  have h2 : p.sec (N : k)⁻¹ ∈ intRing D := sec_mem (by rw [map_inv₀, hN, inv_one])
  have h3 : cA D p.e = N * cA D (p.sec (N : k)⁻¹) := by
    conv_lhs => rw [h1, map_mul, map_natCast]
  rw [h3]
  nth_rewrite 1 [h1]
  exact (dvd_mul h2).add (dvd_mul (cA_mem h2))

theorem lt_one_of_near (hN2 : 2 < N) (hN : valuation k (N : k) = 1) {y : AE D} (h1 : cA D y * y = 1)
    (h2 : (p.e + cA D p.e) * (y - 1) = y - 1) (h3 : valuation k (p.pr y) = 1) {a : D.host.E}
    (ha : star a * a = 1) (h : Near p N (y * incA D a)) : valuation k (p.pr y - 1) < 1 := by
  have hy := mem_of_supp h1 h2 h3
  have h4 : incA D a = y * incA D a * cA D y := by linear_combination (-incA D a) * h1
  have h5 : incA D a ∈ intRing D := h4 ▸ mul_mem h.2.1 (cA_mem hy)
  have h6 : Dvd N (incA D a - 1) := by
    convert h.2.2.1.add ((dvd_idem (p := p) hN).mul (sub_mem h5 (one_mem _))) using 1
    linear_combination (incA D a) * h2
  have h7 := h.2.2.2
  rwa [eq_one_of_dvd hN2 ha h6, map_one, mul_one] at h7

theorem isOpen_near (hN : 0 < N) :
    IsOpen {y : AE D | y ∈ intRing D ∧ Dvd N ((1 - (p.e + cA D p.e)) * (y - 1)) ∧ valuation k (p.pr y - 1) < 1} := by
  have h1 : IsOpen {a : k | valuation k a < 1} := by
    refine isOpen_iff_mem_nhds.2 fun a ha => ?_
    refine (IsValuativeTopology.mem_nhds_iff).2 ⟨1, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    exact Valuation.map_add_lt (valuation k) ha hb
  haveI : IsTopologicalRing (AE D) := inferInstance
  have h2 : Continuous fun y : AE D => (1 - (p.e + cA D p.e)) * (y - 1) := by
    simp only [sub_eq_add_neg]
    exact (continuous_const_mul _).comp (continuous_add_const _)
  exact isOpen_intRing.inter (((isOpen_dvd hN).preimage
    h2).inter
    (h1.preimage (p.cont_pr.sub continuous_const)))

section Line

variable {S : HSp D} [Subsingleton (Fin S.rank)] (i : Fin S.rank)

theorem ent_mul (g h : GA D S) : mt S (g * h) i i = mt S g i i * mt S h i i := by
  rw [mt_mul, Matrix.mul_apply, Fintype.sum_subsingleton _ i]

theorem ent_norm (g : GA D S) : cA D (mt S g i i) * mt S g i i = 1 := by
  have h1 := congrFun (congrFun (mt_unitary S g) i) i
  have h2 := congrFun (congrFun (giA_mul_gA S) i) i
  simp only [Matrix.mul_apply, Fintype.sum_subsingleton _ i, Matrix.one_apply_eq] at h1 h2
  change cA D (mt S g i i) * _ = _ at h1
  linear_combination (giA S i i) * h1 - (cA D (mt S g i i) * mt S g i i - 1) * h2

theorem ent_inv (g : GA D S) : mt S g⁻¹ i i = cA D (mt S g i i) := by
  have h1 := ent_mul i g g⁻¹
  rw [mul_inv_cancel, mt_one, Matrix.one_apply_eq] at h1
  linear_combination (-cA D (mt S g i i)) * h1 - (mt S g⁻¹ i i) * ent_norm i g

variable (p N) in

def ratNear : Subgroup (GA D S) where
  carrier := {g | ∃ a : D.host.E, star a * a = 1 ∧ Near p N (mt S g i i * incA D a)}
  one_mem' := ⟨1, by simp, by simpa using near_one⟩
  mul_mem' := by
    rintro g h ⟨a, ha, hg⟩ ⟨b, hb, hh⟩
    refine ⟨a * b, by rw [star_mul, mul_comm (star b), mul_mul_mul_comm, ha, hb, mul_one], ?_⟩
    rw [ent_mul, RingHom.map_mul, mul_mul_mul_comm]
    exact hg.mul hh
  inv_mem' := by
    rintro g ⟨a, ha, hg⟩
    refine ⟨star a, by rw [star_star, mul_comm, ha], ?_⟩
    have := hg.conj
    rw [RingHom.map_mul] at this
    rw [ent_inv]
    exact this

theorem isOpen_ratNear (hN : 0 < N) : IsOpen (ratNear p N i : Set (GA D S)) := by
  have hc : Continuous fun g : GA D S => mt S g i i :=
    (continuous_apply i).comp ((continuous_apply i).comp (continuous_mt S))
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (mem_of_superset
    (((isOpen_near (p := p) hN).preimage hc).mem_nhds ?_) fun g hg => ⟨1, by simp, ?_⟩)
  · have := (near_one (p := p) (N := N)).2
    simpa using this
  · rw [RingHom.map_one, mul_one]
    exact ⟨ent_norm i g, hg⟩

theorem GQ_le_ratNear : GQ S ≤ ratNear p N i := by
  intro g hg
  obtain ⟨γ, hγ⟩ := mem_ratMx.1 ((mem_GQ_iff S g).1 hg)
  have h1 : mt S g i i = incA D (γ i i) := by rw [← hγ]; rfl
  have h2 : incA D (star (γ i i) * γ i i) = 1 := by
    rw [RingHom.map_mul, ← ent_norm i g, h1]; rfl
  refine ⟨star (γ i i), ?_, ?_⟩
  · rw [star_star, mul_comm]
    exact incA_injective (h2.trans (RingHom.map_one _).symm)
  · rw [h1, ← RingHom.map_mul, mul_comm, h2]
    exact near_one

theorem pr_ent (β : Frame p S (Fin 1)) (g : GL (Fin 1) k) : p.pr (mt S (β.gl g) i i) = g.val 0 0 := by
  have h1 := congrFun (congrFun (β.gl_mat g) i) i
  have h2 := congrFun (congrFun β.bb' i) i
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply_eq, Matrix.map_apply] at h1 h2
  rw [h1]
  linear_combination (g.val 0 0) * h2

theorem supp_ent (β : Frame p S (Fin 1)) (g : GL (Fin 1) k) :
    (p.e + cA D p.e) * (mt S (β.gl g) i i - 1) = mt S (β.gl g) i i - 1 := by
  have := β.gl_supp g i i
  rwa [Matrix.sub_apply, Matrix.one_apply_eq] at this

end Line

theorem exists_tame_ramified : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D), S.rank = 1 → ∀ β : Frame p S (Fin 1), 2 < Nat.card (IsLocalRing.ResidueField 𝒪[k]) → ∃ f : GA D S → ℂ, IsContAut S f ∧ (∀ g : GL (Fin 1) k, valuation k (g.val 0 0 - 1) < 1 → β.rep g f = f) ∧ ∃ g : GL (Fin 1) k, valuation k (g.val 0 0) = 1 ∧ β.rep g f ≠ f := by
  intro D k _ _ _ _ p S hS β hk
  classical
  haveI : Subsingleton (Fin S.rank) := by rw [hS]; infer_instance
  let i : Fin S.rank := ⟨0, by omega⟩
  obtain ⟨N, hN2, hN⟩ := exists_unit_nat k
  obtain ⟨u, hu, hu1⟩ := exists_unit_ne_one hk
  let H := ratNear p N i
  have hopen : IsOpen (H : Set (GA D S)) := isOpen_ratNear i (by omega)
  have hcl : IsClopen (H : Set (GA D S)) := ⟨H.isClosed_of_isOpen hopen, hopen⟩
  refine ⟨fun g => if g ∈ H then 1 else 0, ⟨fun γ hγ g => ?_, ?_⟩, fun g hg => ?_, ?_⟩
  · simp only [H.mul_mem_cancel_left (GQ_le_ratNear i hγ)]
  · exact continuous_if (by
      have : frontier {g | g ∈ H} = ∅ := hcl.frontier_eq
      intro a ha
      rw [this] at ha
      exact ha.elim) continuousOn_const continuousOn_const
  · have hv : valuation k (g.val 0 0) = 1 := by
      have := Valuation.map_one_add_of_lt (valuation k) hg
      rwa [add_sub_cancel] at this
    have hm : β.gl g ∈ H := by
      refine ⟨1, by simp, ?_⟩
      rw [RingHom.map_one, mul_one]
      refine ⟨ent_norm i _, mem_of_supp (ent_norm i _) (supp_ent i β g) (by rw [pr_ent, hv]), ?_, by rwa [pr_ent]⟩
      rw [sub_mul, supp_ent, one_mul, sub_self]
      exact ⟨0, zero_mem _, by rw [RingHom.map_zero, mul_zero]⟩
    funext x
    change (if x * β.gl g ∈ H then (1 : ℂ) else 0) = _
    simp only [H.mul_mem_cancel_right hm]
  · have hu0 : u ≠ 0 := fun h => by simp [h] at hu
    let g : GL (Fin 1) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![u] (by simpa using hu0)
    have hg : g.val 0 0 = u := rfl
    refine ⟨g, hu, fun h => ?_⟩
    have h1 := congrFun h 1
    change (if 1 * β.gl g ∈ H then (1 : ℂ) else 0) = if (1 : GA D S) ∈ H then 1 else 0 at h1
    rw [if_pos H.one_mem, one_mul] at h1
    have hm : β.gl g ∈ H := by
      by_contra hh
      rw [if_neg hh] at h1
      exact zero_ne_one h1
    obtain ⟨a, ha, hn⟩ := hm
    have := lt_one_of_near hN2 hN (ent_norm i _) (supp_ent i β g) (by rw [pr_ent, hg, hu]) ha hn
    rw [pr_ent, hg] at this
    exact hu1 this

end GlobalTheory.RamLine
