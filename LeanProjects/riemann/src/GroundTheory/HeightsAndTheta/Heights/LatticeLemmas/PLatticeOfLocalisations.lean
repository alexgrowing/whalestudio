import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.WeilPolarization.AlgebraMapFMemLocIntegers
import GroundTheory.GlobalFields.Adele.Discrete
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField TensorProduct IsDedekindDomain Submodule
open GroundTheory.Heights₂.Heights

noncomputable section

namespace LatticeOfLocalisations

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

set_option linter.unusedSectionVars false

section Place

variable (v : HeightOneSpectrum (𝓞 K))

theorem smul_mem_of_mem_integers
    (P : Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V))
    {k : v.adicCompletion K} (hk : k ∈ v.adicCompletionIntegers K)
    {w : v.adicCompletion K ⊗[K] V} (hw : w ∈ P) : k • w ∈ P := by
  have h := P.smul_mem (⟨k, hk⟩ : v.adicCompletionIntegers K) hw
  rwa [← algebraMap_smul (v.adicCompletion K)] at h

theorem toLocal_smul' (d : 𝓞 K) (x : V) :
    toLocal v (d • x) = algebraMap K (v.adicCompletion K) (d : K) • toLocal v x := by
  rw [toLocal_smul, ← algebraMap_smul (v.adicCompletion K)]
  rfl

theorem smul_mem_of_dvd
    (P : Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V))
    {d D : 𝓞 K} (h : d ∣ D) {y : v.adicCompletion K ⊗[K] V}
    (hy : algebraMap K (v.adicCompletion K) (d : K) • y ∈ P) :
    algebraMap K (v.adicCompletion K) (D : K) • y ∈ P := by
  obtain ⟨k, rfl⟩ := h
  rw [show ((d * k : 𝓞 K) : K) = (k : K) * (d : K) by push_cast; ring, map_mul, mul_smul]
  exact smul_mem_of_mem_integers v P (Theta.Ex1GL.algebraMap_integer_mem v k) hy

theorem smul_mem_of_mem_span
    (P : Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V))
    (k : v.adicCompletion K) {s : Set (v.adicCompletion K ⊗[K] V)} (hs : ∀ y ∈ s, k • y ∈ P)
    {y : v.adicCompletion K ⊗[K] V} (hy : y ∈ span (v.adicCompletionIntegers K) s) : k • y ∈ P := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [smul_add]; exact add_mem hx hz
  | smul o x _ hx =>
    rw [← algebraMap_smul (v.adicCompletion K) o x, smul_smul, mul_comm, ← smul_smul,
      algebraMap_smul]
    exact P.smul_mem o hx

theorem exists_smul_mem_of_mem_span_field
    (P : Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V))
    {y : v.adicCompletion K ⊗[K] V} (hy : y ∈ span (v.adicCompletion K) (P : Set _)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ algebraMap K (v.adicCompletion K) (d : K) • y ∈ P := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    exact add_mem (smul_mem_of_dvd v P (dvd_mul_right d₁ d₂) h₁)
      (smul_mem_of_dvd v P (dvd_mul_left d₂ d₁) h₂)
  | smul a x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨b, hb, hab⟩ :=
      HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
    refine ⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero hb) hd, ?_⟩
    have e : algebraMap K (v.adicCompletion K) ((b * d : 𝓞 K) : K) • a • x =
        (a * algebraMap (𝓞 K) (v.adicCompletion K) b) •
          algebraMap K (v.adicCompletion K) (d : K) • x := by
      rw [smul_smul, smul_smul]
      congr 1
      rw [IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K),
        ← RingOfIntegers.coe_eq_algebraMap,
        show ((b * d : 𝓞 K) : K) = (b : K) * (d : K) by push_cast; ring, map_mul]
      ring
    rw [e]
    exact smul_mem_of_mem_integers v P hab h

theorem exists_smul_le
    (P Q : Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V)) (hP : P.FG)
    (hQ : span (v.adicCompletion K) (Q : Set (v.adicCompletion K ⊗[K] V)) = ⊤) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ y ∈ P, algebraMap K (v.adicCompletion K) (d : K) • y ∈ Q := by
  classical
  obtain ⟨s, rfl⟩ := hP
  have hs : ∀ t : Finset (v.adicCompletion K ⊗[K] V),
      ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ y ∈ t, algebraMap K (v.adicCompletion K) (d : K) • y ∈ Q := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert a t _ ih =>
      obtain ⟨d, hd, h⟩ := ih
      obtain ⟨e, he, h'⟩ := exists_smul_mem_of_mem_span_field v Q (y := a) (by rw [hQ]; trivial)
      refine ⟨d * e, mul_ne_zero hd he, fun y hy => ?_⟩
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact smul_mem_of_dvd v Q (dvd_mul_left e d) h'
      · exact smul_mem_of_dvd v Q (dvd_mul_right d e) (h y hy)
  obtain ⟨d, hd, h⟩ := hs s
  exact ⟨d, hd, fun y hy => smul_mem_of_mem_span v Q _ (fun z hz => h z hz) hy⟩

theorem localLattice_span (s : Set V) :
    localLattice v (span (𝓞 K) s) = span (v.adicCompletionIntegers K) (toLocal v '' s) := by
  refine le_antisymm (span_le.mpr ?_) (span_mono (Set.image_mono subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul a x _ hx => rw [toLocal_smul]; exact smul_mem _ _ hx

theorem span_localLattice_eq_top (L : Submodule (𝓞 K) V) (hL : span K (L : Set V) = ⊤) :
    span (v.adicCompletion K) (localLattice v L : Set (v.adicCompletion K ⊗[K] V)) = ⊤ := by
  rw [eq_top_iff]
  rintro w -
  induction w using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a x =>
    have hx : toLocal v x ∈
        (span (v.adicCompletion K) (localLattice v L : Set (v.adicCompletion K ⊗[K] V))).restrictScalars K := by
      refine span_le_restrictScalars K (v.adicCompletion K) _ ?_
      refine span_mono (subset_span (R := v.adicCompletionIntegers K)) ?_
      rw [← Submodule.map_span]
      exact mem_map_of_mem (by rw [hL]; trivial)
    have e : a ⊗ₜ[K] x = a • toLocal v x := by
      simp [toLocal, TensorProduct.smul_tmul']
    rw [e]
    exact smul_mem _ a hx
  | add w z hw hz => exact add_mem hw hz

def intCoords {ι : Type*} (e : Module.Basis ι K V) :
    Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V) where
  carrier := {w | ∀ i, (Algebra.TensorProduct.basis (v.adicCompletion K) e).repr w i ∈
    v.adicCompletionIntegers K}
  add_mem' hw hz i := by rw [map_add, Finsupp.add_apply]; exact add_mem (hw i) (hz i)
  zero_mem' i := by rw [map_zero, Finsupp.zero_apply]; exact zero_mem _
  smul_mem' o w hw i := by
    rw [← algebraMap_smul (v.adicCompletion K) o w, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem o.2 (hw i)

theorem repr_toLocal {ι : Type*} (e : Module.Basis ι K V) (x : V) (i : ι) :
    (Algebra.TensorProduct.basis (v.adicCompletion K) e).repr (toLocal v x) i =
      algebraMap K (v.adicCompletion K) (e.repr x i) := by
  simp [toLocal, Algebra.TensorProduct.basis_repr_tmul]

theorem localLattice_le_intCoords {ι : Type*} (e : Module.Basis ι K V) :
    localLattice v (span (𝓞 K) (Set.range e)) ≤ intCoords v e := by
  classical
  rw [localLattice_span, span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩ j
  show _ ∈ _
  rw [repr_toLocal, e.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

end Place

theorem mem_span_of_forall_toLocal_mem {ι : Type*} (e : Module.Basis ι K V) {x : V}
    (hx : ∀ v, toLocal v x ∈ localLattice v (span (𝓞 K) (Set.range e))) :
    x ∈ span (𝓞 K) (Set.range e) := by
  rw [e.mem_span_iff_repr_mem (𝓞 K)]
  intro i
  obtain ⟨z, hz⟩ := GroundTheory.Global.exists_eq_of_forall_mem_adicCompletionIntegers K (e.repr x i)
    fun v => by
      have h := localLattice_le_intCoords v e (hx v) i
      rw [repr_toLocal] at h
      exact h
  exact ⟨z, hz⟩

theorem exists_smul_mem_span_basis {ι : Type*} [Fintype ι] (e : Module.Basis ι K V) {n : ℕ}
    (g : Fin n → V) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ m ∈ span (𝓞 K) (Set.range g), c • m ∈ span (𝓞 K) (Set.range e) := by
  classical
  obtain ⟨⟨c, hc⟩, hcint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K))
    (Finset.univ : Finset (ι × Fin n)) (fun p => e.repr (g p.2) p.1)
  refine ⟨c, nonZeroDivisors.ne_zero hc, fun m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [e.mem_span_iff_repr_mem (𝓞 K)]
    intro i
    obtain ⟨r, hr⟩ := hcint (i, j) (Finset.mem_univ _)
    refine ⟨r, ?_⟩
    rw [hr, ← algebraMap_smul K c (g j), map_smul, Finsupp.smul_apply]
    simp [Algebra.smul_def]
  | zero => simp
  | add x z _ _ hx hz => rw [smul_add]; exact add_mem hx hz
  | smul a x _ hx => rw [smul_comm]; exact smul_mem _ a hx

theorem exists_common_scale (M₁ : FullLattice K V)
    (N : ∀ v : HeightOneSpectrum (𝓞 K),
      Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V))
    (hN : ∀ v, IsLocalLattice v (N v)) (hfin : {v | N v ≠ localLattice v M₁.carrier}.Finite) :
    ∃ D : 𝓞 K, D ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K),
      (∀ y ∈ N v, algebraMap K (v.adicCompletion K) (D : K) • y ∈ localLattice v M₁.carrier) ∧
      (∀ y ∈ localLattice v M₁.carrier, algebraMap K (v.adicCompletion K) (D : K) • y ∈ N v) := by
  classical
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp M₁.fg
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ d : 𝓞 K, d ≠ 0 ∧
      (∀ y ∈ N v, algebraMap K (v.adicCompletion K) (d : K) • y ∈ localLattice v M₁.carrier) ∧
      (∀ y ∈ localLattice v M₁.carrier, algebraMap K (v.adicCompletion K) (d : K) • y ∈ N v) := by
    intro v
    obtain ⟨d₁, hd₁, h₁⟩ := exists_smul_le v (N v) (localLattice v M₁.carrier) (hN v).1
      (span_localLattice_eq_top v M₁.carrier M₁.span_eq)
    obtain ⟨d₂, hd₂, h₂⟩ := exists_smul_le v (localLattice v M₁.carrier) (N v)
      (by rw [← hg, localLattice_span]; exact fg_span ((Set.finite_range g).image _)) (hN v).2
    exact ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂,
      fun y hy => smul_mem_of_dvd v _ (dvd_mul_right _ _) (h₁ y hy),
      fun y hy => smul_mem_of_dvd v _ (dvd_mul_left _ _) (h₂ y hy)⟩
  choose d hd hdN hdM using hloc
  refine ⟨∏ v ∈ hfin.toFinset, d v, Finset.prod_ne_zero_iff.mpr fun v _ => hd v, fun v => ?_⟩
  by_cases hv : v ∈ hfin.toFinset
  · exact ⟨fun y hy => smul_mem_of_dvd v _ (Finset.dvd_prod_of_mem d hv) (hdN v y hy),
      fun y hy => smul_mem_of_dvd v _ (Finset.dvd_prod_of_mem d hv) (hdM v y hy)⟩
  · have hNv : N v = localLattice v M₁.carrier := by simpa using hv
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rw [← hNv]
      exact smul_mem_of_mem_integers v _ (Theta.Ex1GL.algebraMap_integer_mem v _) hy
    · rw [hNv]
      exact smul_mem_of_mem_integers v _ (Theta.Ex1GL.algebraMap_integer_mem v _) hy

theorem smul_localLattice_mem (v : HeightOneSpectrum (𝓞 K)) {L L' : Submodule (𝓞 K) V} (D : 𝓞 K)
    (h : ∀ m ∈ L, D • m ∈ L') {y : v.adicCompletion K ⊗[K] V} (hy : y ∈ localLattice v L) :
    algebraMap K (v.adicCompletion K) (D : K) • y ∈ localLattice v L' := by
  refine smul_mem_of_mem_span v _ _ ?_ hy
  rintro _ ⟨m, hm, rfl⟩
  rw [← toLocal_smul']
  exact subset_span ⟨_, h m hm, rfl⟩

theorem mem_localLattice_latticeOfLocal (M₁ : FullLattice K V)
    (N : ∀ v : HeightOneSpectrum (𝓞 K),
      Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V))
    (hfin : {v | N v ≠ localLattice v M₁.carrier}.Finite) {D : 𝓞 K} (hD : D ≠ 0)
    (hDN : ∀ v : HeightOneSpectrum (𝓞 K),
      ∀ y ∈ N v, algebraMap K (v.adicCompletion K) (D : K) • y ∈ localLattice v M₁.carrier)
    (hDM : ∀ v : HeightOneSpectrum (𝓞 K),
      ∀ y ∈ localLattice v M₁.carrier, algebraMap K (v.adicCompletion K) (D : K) • y ∈ N v)
    (v : HeightOneSpectrum (𝓞 K)) {y : v.adicCompletion K ⊗[K] V} (hy : y ∈ N v) :
    y ∈ localLattice v (latticeOfLocal N) := by
  classical
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp M₁.fg
  have hMv : ∀ u : HeightOneSpectrum (𝓞 K), localLattice u M₁.carrier =
      span (u.adicCompletionIntegers K) (Set.range fun i => toLocal u (g i)) := fun u => by
    rw [← hg, localLattice_span, ← Set.range_comp]
    rfl
  have hDK : (D : K) ≠ 0 := by exact_mod_cast hD
  have ha : ∀ u : HeightOneSpectrum (𝓞 K), algebraMap K (u.adicCompletion K) (D : K) ≠ 0 :=
    fun u => (map_ne_zero _).mpr hDK
  have hDy := hDN v y hy
  rw [hMv v] at hDy
  obtain ⟨cc, hcc⟩ := (mem_span_range_iff_exists_fun (v.adicCompletionIntegers K)).mp hDy
  have hT₀ : {u : HeightOneSpectrum (𝓞 K) | D ∈ u.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {D})
      (by simpa [Ideal.span_singleton_eq_bot] using hD)).subset fun u hu => ?_
    exact Ideal.dvd_span_singleton.mpr hu
  set T : Finset (HeightOneSpectrum (𝓞 K)) := hfin.toFinset ∪ hT₀.toFinset
  have happ := fun i => Theta.Ex1GL.exists_approx v T (D * D) (mul_ne_zero hD hD) (cc i).2
  choose b hbv hbT using happ
  choose o ho hov using hbv
  set x : V := (D : K)⁻¹ • ∑ i, b i • g i with hx_def
  have hx : ∀ u : HeightOneSpectrum (𝓞 K), toLocal u x =
      (algebraMap K (u.adicCompletion K) (D : K))⁻¹ •
        ∑ i, algebraMap K (u.adicCompletion K) (b i : K) • toLocal u (g i) := by
    intro u
    rw [hx_def, map_smul, map_sum, ← algebraMap_smul (u.adicCompletion K) (D : K)⁻¹, map_inv₀]
    simp only [toLocal_smul']
  set m : v.adicCompletion K ⊗[K] V := ∑ i, o i • toLocal v (g i) with hm_def
  have hm : m ∈ localLattice v M₁.carrier := by
    rw [hMv v]
    exact sum_mem fun i _ => smul_mem_of_mem_integers v _ (ho i) (subset_span ⟨i, rfl⟩)
  have hxv : toLocal v x = y + algebraMap K (v.adicCompletion K) (D : K) • m := by
    set a := algebraMap K (v.adicCompletion K) (D : K) with ha_def
    have hterm : ∀ i, algebraMap K (v.adicCompletion K) (b i : K) • toLocal v (g i) =
        ((cc i : v.adicCompletion K) • toLocal v (g i)) + a • a • (o i • toLocal v (g i)) := by
      intro i
      rw [smul_smul, smul_smul, ← add_smul]
      congr 1
      have h := hov i
      rw [show ((D * D : 𝓞 K) : K) = (D : K) * (D : K) by push_cast; ring, map_mul] at h
      linear_combination h
    have hcc' : ∑ i, (cc i : v.adicCompletion K) • toLocal v (g i) = a • y := by
      rw [← hcc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul (v.adicCompletion K) (cc i)]
      rfl
    rw [hx v, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, hcc',
      ← Finset.smul_sum, ← Finset.smul_sum, ← hm_def, smul_add, smul_smul, inv_mul_cancel₀ (ha v),
      one_smul, smul_smul, inv_mul_cancel₀ (ha v), one_smul]
  have hxM : x ∈ latticeOfLocal N := by
    intro u
    by_cases huv : u = v
    · subst huv
      rw [hxv]
      exact add_mem hy (hDM u _ hm)
    by_cases huT : u ∈ T
    · choose o' ho' hou' using fun i => hbT i u huT huv
      have e : toLocal u x = algebraMap K (u.adicCompletion K) (D : K) •
          ∑ i, o' i • toLocal u (g i) := by
        rw [hx u, Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, smul_smul, hou' i]
        congr 1
        rw [show ((D * D : 𝓞 K) : K) = (D : K) * (D : K) by push_cast; ring, map_mul]
        field_simp [ha u]
      rw [e]
      refine hDM u _ ?_
      rw [hMv u]
      exact sum_mem fun i _ => smul_mem_of_mem_integers u _ (ho' i) (subset_span ⟨i, rfl⟩)
    · have hDu : D ∉ u.asIdeal := fun h =>
        huT (Finset.mem_union_right _ (hT₀.mem_toFinset.mpr h))
      have hNu : N u = localLattice u M₁.carrier := by
        by_contra h
        exact huT (Finset.mem_union_left _ (hfin.mem_toFinset.mpr h))
      rw [hx u, hNu, Finset.smul_sum]
      refine sum_mem fun i _ => ?_
      rw [smul_smul]
      refine smul_mem_of_mem_integers u _ (mul_mem (Theta.Ex1GL.inv_mem_of_notMem u hDu)
        (Theta.Ex1GL.algebraMap_integer_mem u (b i))) ?_
      rw [hMv u]
      exact subset_span ⟨i, rfl⟩
  have h1 : toLocal v x ∈ localLattice v (latticeOfLocal N) := subset_span ⟨x, hxM, rfl⟩
  have h2 : algebraMap K (v.adicCompletion K) (D : K) • m ∈ localLattice v (latticeOfLocal N) :=
    smul_localLattice_mem v D (fun m' hm' u => by
      rw [toLocal_smul']
      exact hDM u _ (subset_span ⟨m', hm', rfl⟩)) hm
  have e : y = toLocal v x - algebraMap K (v.adicCompletion K) (D : K) • m := by
    rw [hxv]; abel
  rw [e]
  exact sub_mem h1 h2

theorem latticeOfLocal_spec (M₁ : FullLattice K V)
    (N : ∀ v : HeightOneSpectrum (𝓞 K),
      Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V))
    (hN : ∀ v, IsLocalLattice v (N v)) (hfin : {v | N v ≠ localLattice v M₁.carrier}.Finite) :
    (latticeOfLocal N).FG ∧ span K (latticeOfLocal N : Set V) = ⊤ ∧
      ∀ v, localLattice v (latticeOfLocal N) = N v := by
  classical
  obtain ⟨D, hD, hDNM⟩ := exists_common_scale M₁ N hN hfin
  have hDN := fun v => (hDNM v).1
  have hDM := fun v => (hDNM v).2
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp M₁.fg
  have hP3 : ∀ m ∈ M₁.carrier, D • m ∈ latticeOfLocal N := fun m hm u => by
    rw [toLocal_smul']
    exact hDM u _ (subset_span ⟨m, hm, rfl⟩)

  have hgK : span K (Set.range g) = ⊤ := by
    rw [eq_top_iff, ← M₁.span_eq, span_le, ← hg]
    exact fun x hx => span_le_restrictScalars (𝓞 K) K (Set.range g) hx
  have : Module.Finite K V :=
    ⟨⟨Finset.univ.image g, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hgK]⟩⟩
  let e := Module.finBasis K V
  obtain ⟨c, hc, hcF⟩ := exists_smul_mem_span_basis e g
  have hM'F : ∀ x ∈ latticeOfLocal N, (c * D) • x ∈ span (𝓞 K) (Set.range e) := by
    intro x hx
    refine mem_span_of_forall_toLocal_mem e fun u => ?_
    rw [mul_smul, toLocal_smul', toLocal_smul']
    refine smul_mem_of_mem_span u _ _ ?_ (hDN u _ (hx u))
    rintro _ ⟨m, hm, rfl⟩
    rw [← toLocal_smul']
    exact subset_span ⟨_, hcF m (by rw [hg]; exact hm), rfl⟩
  refine ⟨?_, ?_, fun v => le_antisymm ?_ fun y hy =>
    mem_localLattice_latticeOfLocal M₁ N hfin hD hDN hDM v hy⟩
  · let f : V →ₗ[𝓞 K] V := (c * D) • LinearMap.id
    have hf : Function.Injective f := by
      intro x z h
      change (c * D) • x = (c * D) • z at h
      rw [← algebraMap_smul K (c * D) x, ← algebraMap_smul K (c * D) z] at h
      exact smul_right_injective V ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr
        (mul_ne_zero hc hD)) h
    refine fg_of_fg_map_injective f hf (FG.of_le (fg_span (Set.finite_range e)) ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact hM'F x hx
  · rw [eq_top_iff, ← M₁.span_eq, span_le]
    intro m hm
    have e' : m = (D : K)⁻¹ • (D • m) := by
      rw [← algebraMap_smul K D m, smul_smul, ← RingOfIntegers.coe_eq_algebraMap,
        inv_mul_cancel₀ (by exact_mod_cast hD), one_smul]
    rw [e']
    exact smul_mem _ _ (subset_span (hP3 m hm))
  · rw [localLattice, span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx v

end LatticeOfLocalisations

theorem LatticeOfLocalisations.proof : LatticeOfLocalisations.Statement := by
  intro K _ _ V _ _ _ _ M₁ N N'' hN hNfin hN'' hN''fin
  obtain ⟨hfg, hspan, hloc⟩ := LatticeOfLocalisations.latticeOfLocal_spec M₁ N hN hNfin
  obtain ⟨-, -, hloc''⟩ := LatticeOfLocalisations.latticeOfLocal_spec M₁ N'' hN'' hN''fin
  refine ⟨hfg, hspan, hloc, fun h v => ?_, fun h x hx v => h v (hx v)⟩
  rw [← hloc v, ← hloc'' v]
  exact span_mono (Set.image_mono h)

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
