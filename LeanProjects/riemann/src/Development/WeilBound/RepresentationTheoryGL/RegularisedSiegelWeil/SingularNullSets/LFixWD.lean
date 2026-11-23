import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixW_C

noncomputable section

set_option synthInstance.maxHeartbeats 200000

open scoped Matrix TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU
  GlobalTheory.MixModel GlobalTheory.StdUnn Filter

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {D : D7}

theorem exists_fin {p : Pl D → Prop} (h : ∀ᶠ v in cofinite, p v) : ∃ S₀ : Finset (Pl D), ∀ v ∉ S₀, p v :=
  ⟨(Filter.eventually_cofinite.1 h).toFinset, fun v hv => by
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv; exact hv⟩

def IntS (S : Finset (Pl D)) (a : AE D) : Prop := ∀ v ∉ S, cv D v a ∈ intLoc D.host.F D.host.E v

def OffS (S : Finset (Pl D)) (a : AE D) : Prop :=
  (∀ w, compInf D.host.F D.host.E w a = 0) ∧ (∀ v ∈ S, cv D v a = 0) ∧ IntS S a

variable {S : Finset (Pl D)}

theorem IntS.add {a b : AE D} (ha : IntS S a) (hb : IntS S b) : IntS S (a + b) := fun v hv => by
  rw [map_add]; exact add_mem (ha v hv) (hb v hv)

theorem IntS.mul {a b : AE D} (ha : IntS S a) (hb : IntS S b) : IntS S (a * b) := fun v hv => by
  rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)

theorem IntS.neg {a : AE D} (ha : IntS S a) : IntS S (-a) := fun v hv => by
  rw [map_neg]; exact neg_mem (ha v hv)

theorem intS_zero : IntS S (0 : AE D) := fun v _ => by rw [map_zero]; exact zero_mem _

theorem intS_sum {ι : Type} (s : Finset ι) (f : ι → AE D) (h : ∀ i ∈ s, IntS S (f i)) : IntS S (∑ i ∈ s, f i) :=
  fun v hv => by rw [map_sum]; exact sum_mem fun i hi => h i hi v hv

theorem IntS.cA {a : AE D} (ha : IntS S a) : IntS S (cA D a) := fun v hv => by
  rw [LIdemEx.cv_cA]; exact sigR_mem_intLoc _ (ha v hv)

theorem OffS.add {a b : AE D} (ha : OffS S a) (hb : OffS S b) : OffS S (a + b) :=
  ⟨fun w => by rw [map_add, ha.1 w, hb.1 w, add_zero], fun v hv => by rw [map_add, ha.2.1 v hv, hb.2.1 v hv, add_zero],
    ha.2.2.add hb.2.2⟩

theorem offS_zero : OffS S (0 : AE D) := ⟨fun w => map_zero _, fun v _ => map_zero _, intS_zero⟩

theorem OffS.neg {a : AE D} (ha : OffS S a) : OffS S (-a) :=
  ⟨fun w => by rw [map_neg, ha.1 w, neg_zero], fun v hv => by rw [map_neg, ha.2.1 v hv, neg_zero], ha.2.2.neg⟩

theorem OffS.mul_left {a b : AE D} (ha : IntS S a) (hb : OffS S b) : OffS S (a * b) :=
  ⟨fun w => by rw [map_mul, hb.1 w, mul_zero], fun v hv => by rw [map_mul, hb.2.1 v hv, mul_zero], ha.mul hb.2.2⟩

theorem OffS.mul_right {a b : AE D} (ha : OffS S a) (hb : IntS S b) : OffS S (a * b) :=
  ⟨fun w => by rw [map_mul, ha.1 w, zero_mul], fun v hv => by rw [map_mul, ha.2.1 v hv, zero_mul], ha.2.2.mul hb⟩

theorem offS_sum {ι : Type} (s : Finset ι) (f : ι → AE D) (h : ∀ i ∈ s, OffS S (f i)) : OffS S (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact offS_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem OffS.cA {a : AE D} (ha : OffS S a) : OffS S (cA D a) :=
  ⟨fun w => by rw [LIdemEx.compInf_cA, ha.1 w, map_zero], fun v hv => by rw [LIdemEx.cv_cA, ha.2.1 v hv, map_zero],
    ha.2.2.cA⟩

theorem OffS.intS {a : AE D} (ha : OffS S a) : IntS S a := ha.2.2

theorem intOff_iff {a b : ℕ} (x : Mx D a b) : IntOff S x ↔ ∀ i j, IntS S (x i j) :=
  ⟨fun h i j v hv => h v hv i j, fun h v hv i j => h i j v hv⟩

theorem offS_mul_left {a b c : ℕ} {x : Mx D a b} {y : Mx D b c} (hx : ∀ i j, IntS S (x i j)) (hy : ∀ i j, OffS S (y i j))
    (i : Fin a) (j : Fin c) : OffS S ((x * y) i j) := by
  rw [Matrix.mul_apply]; exact offS_sum _ _ fun k _ => (hy k j).mul_left (hx i k)

theorem offS_mul_right {a b c : ℕ} {x : Mx D a b} {y : Mx D b c} (hx : ∀ i j, OffS S (x i j)) (hy : ∀ i j, IntS S (y i j))
    (i : Fin a) (j : Fin c) : OffS S ((x * y) i j) := by
  rw [Matrix.mul_apply]; exact offS_sum _ _ fun k _ => (hx i k).mul_right (hy k j)

theorem intS_mul {a b c : ℕ} {x : Mx D a b} {y : Mx D b c} (hx : ∀ i j, IntS S (x i j)) (hy : ∀ i j, IntS S (y i j))
    (i : Fin a) (j : Fin c) : IntS S ((x * y) i j) := by
  rw [Matrix.mul_apply]; exact intS_sum _ _ fun k _ => (hx i k).mul (hy k j)

theorem offS_trace {a : ℕ} {x : Mx D a a} (hx : ∀ i j, OffS S (x i j)) : OffS S (Matrix.trace x) :=
  offS_sum _ _ fun i _ => hx i i

theorem adj_intS {a b : ℕ} {x : Mx D a b} (hx : ∀ i j, IntS S (x i j)) (i : Fin b) (j : Fin a) : IntS S (adj x i j) :=
  (hx j i).cA

theorem adj_offS {a b : ℕ} {x : Mx D a b} (hx : ∀ i j, OffS S (x i j)) (i : Fin b) (j : Fin a) : OffS S (adj x i j) :=
  (hx j i).cA

theorem exists_rat_int {a b : ℕ} (Q : Matrix (Fin a) (Fin b) D.host.E) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ i j, IntS S (rat Q i j) := by
  have h : ∀ᶠ v : Pl D in cofinite, IsGood D.host.F D.host.E v ∧ ∀ i j k,
      algebraMap D.host.F (Fv D.host.F v) ((bE D.host.F D.host.E).repr (Q i j) k) ∈ v.adicCompletionIntegers D.host.F :=
    eventually_good.and (eventually_all.2 fun i => eventually_all.2 fun j => eventually_coord (Q i j))
  obtain ⟨S₀, hS₀⟩ := exists_fin h
  refine ⟨S₀, fun S hS i j v hv => ?_⟩
  obtain ⟨hg, hc⟩ := hS₀ v (fun h => hv (hS h))
  show (1 : Fv D.host.F v) ⊗ₜ[D.host.F] Q i j ∈ _
  refine (mem_intLoc_iff hg _).2 fun k => ?_
  rw [crd_tmul, one_mul]
  exact hc i j k

theorem psi_off {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ z : AE D, OffS S z → ψ (trA z) = 1 ∧ ψ (halfTr z) = 1 := by
  classical
  obtain ⟨S₁, hS₁⟩ := psi_kernel hψ
  obtain ⟨S₂, hS₂⟩ := exists_fin (eventually_good (F := D.host.F) (E := D.host.E))
  refine ⟨S₁ ∪ S₂, fun S hS z hz => ?_⟩
  have h1 : (trA z).1 = 0 := funext fun w => by rw [trA_fst, hz.1 w, map_zero]; rfl
  have hg : ∀ v ∉ S, IsGood D.host.F D.host.E v := fun v hv =>
    hS₂ v fun h => hv (hS (Finset.mem_union_right _ h))
  have h2 : ∀ v ∈ S, (trA z).2 v = 0 := fun v hv => by rw [trA_snd, hz.2.1 v hv, map_zero]
  have h3 : ∀ v ∉ S, (trA z).2 v ∈ v.adicCompletionIntegers D.host.F := fun v hv => by
    rw [trA_snd]; exact trace_mem (hg v hv) (hz.2.2 v hv)
  have hS1 : S₁ ⊆ S := fun v h => hS (Finset.mem_union_left _ h)
  refine ⟨hS₁ S hS1 _ h1 h2 h3, hS₁ S hS1 _ ?_ ?_ ?_⟩
  · show (algebraMap D.host.F (AF D.host.F) (1 / 2)).1 * (trA z).1 = 0
    rw [h1, mul_zero]
  · intro v hv
    show (algebraMap D.host.F (AF D.host.F) (1 / 2)).2 v * (trA z).2 v = 0
    rw [h2 v hv, mul_zero]
  · intro v hv
    show (algebraMap D.host.F (AF D.host.F) (1 / 2)).2 v * (trA z).2 v ∈ _
    refine mul_mem ?_ (h3 v hv)
    have := (hg v hv).half
    rwa [one_div]

theorem dual_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ v ∉ S₀, ∀ c : Fv D.host.F v ⊗[D.host.F] D.host.E,
      (∀ t ∈ intLoc D.host.F D.host.E v,
        psiV D.host.F ψ v (Algebra.trace (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) (c * t)) = 1) →
      c ∈ intLoc D.host.F D.host.E v := by
  obtain ⟨S₀, hS₀⟩ := exists_fin ((eventually_good (F := D.host.F) (E := D.host.E)).and
    (GlobalTheory.CompanionTheory.PsiCondLoc.psiCond D.host.F ψ hψ))
  refine ⟨S₀, fun v hv c hc => ?_⟩
  obtain ⟨hg, hp⟩ := hS₀ v hv
  refine mem_of_trace hg c fun t ht => (hp _).1 fun s hs => ?_
  have hst : algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) s * t ∈ intLoc D.host.F D.host.E v := by
    refine mul_mem ?_ ht
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact tmul_one_mem hs
  have := hc _ hst
  have e : c * (algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) s * t) = s • (c * t) := by
    rw [Algebra.smul_def]; ring
  rw [e, LinearMap.map_smul, smul_eq_mul, mul_comm] at this
  exact this

end PositivityTheory.Rg.Rsw.L.LFixW

end
