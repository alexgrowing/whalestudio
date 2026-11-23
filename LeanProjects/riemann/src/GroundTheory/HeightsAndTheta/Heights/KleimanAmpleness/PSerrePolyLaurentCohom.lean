import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSerrePoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u

namespace LaurentCohomProof

variable {S : Type u} [CommRing S] {N : ℕ}

def negSet (a : Fin (N + 1) → ℤ) : Finset (Fin (N + 1)) := Finset.univ.filter fun j => a j < 0

theorem mem_negSet {a : Fin (N + 1) → ℤ} {j : Fin (N + 1)} : j ∈ negSet a ↔ a j < 0 := by
  simp [negSet]

variable (S) in

def part (J : Finset (Fin (N + 1))) : Laurent S N →ₗ[S] Laurent S N where
  toFun f := f.filter fun a => negSet a = J
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

theorem part_apply (J : Finset (Fin (N + 1))) (f : Laurent S N) (a : Fin (N + 1) → ℤ) :
    part S J f a = if negSet a = J then f a else 0 :=
  Finsupp.filter_apply _ _ _

theorem sum_part (f : Laurent S N) : ∑ J, part S J f = f := by
  ext a
  rw [Finsupp.finsetSum_apply]
  simp only [part_apply]
  rw [Finset.sum_ite_eq]
  simp

variable (S N) in

def wPart (c : ℤ) (J : Finset (Fin (N + 1))) : Submodule S (Laurent S N) :=
  Finsupp.supported S S {a | negSet a = J ∧ ∑ j, a j = c}

theorem mem_exps {c : ℤ} {I : StdCell N} {f : Laurent S N} (hf : f ∈ laurentDeg S N c I)
    {a : Fin (N + 1) → ℤ} (ha : f a ≠ 0) : a ∈ laurentExps N c I.1 := by
  by_contra h
  exact ha ((Finsupp.mem_supported' S f).mp hf a h)

theorem part_mem_w {c : ℤ} {J : Finset (Fin (N + 1))} {I : StdCell N} {f : Laurent S N}
    (hf : f ∈ laurentDeg S N c I) : part S J f ∈ wPart S N c J := by
  refine (Finsupp.mem_supported' S _).mpr fun a ha => ?_
  rw [part_apply]
  split_ifs with h
  · by_contra h'
    exact ha ⟨h, (mem_exps hf h').1⟩
  · rfl

theorem part_eq_zero {c : ℤ} {J : Finset (Fin (N + 1))} {I : StdCell N} {f : Laurent S N}
    (hf : f ∈ laurentDeg S N c I) (hJ : ¬ J ⊆ I.1) : part S J f = 0 := by
  ext a
  rw [part_apply, Finsupp.zero_apply]
  split_ifs with h
  · by_contra h'
    apply hJ
    intro j hj
    by_contra hjI
    have h1 := (mem_exps hf h').2 j hjI
    rw [← h, mem_negSet] at hj
    omega
  · rfl

theorem mem_deg_of_w {c : ℤ} {J : Finset (Fin (N + 1))} {I : StdCell N} {y : Laurent S N}
    (hy : y ∈ wPart S N c J) (hJ : ¬ J ⊆ I.1 → y = 0) : y ∈ laurentDeg S N c I := by
  by_cases h : J ⊆ I.1
  · refine (Finsupp.mem_supported' S _).mpr fun a ha => ?_
    refine (Finsupp.mem_supported' S _).mp hy a fun ⟨hJa, hc⟩ => ha ⟨hc, fun j hj => ?_⟩
    by_contra hneg
    have : j ∈ negSet a := mem_negSet.mpr (by omega)
    rw [hJa] at this
    exact hj (h this)
  · rw [hJ h]; exact Submodule.zero_mem _

theorem part_mem_deg {c : ℤ} {J : Finset (Fin (N + 1))} {I : StdCell N} {f : Laurent S N}
    (hf : f ∈ laurentDeg S N c I) : part S J f ∈ laurentDeg S N c I :=
  mem_deg_of_w (part_mem_w hf) (part_eq_zero hf)

variable (S N) in

abbrev G : StdCell N → Type u := fun _ => Laurent S N

variable (S N) in

abbrev ρ := Cech.idRes S (Laurent S N) (Finset.univ : Finset (Fin (N + 1)))

variable (S) in

def partC (J : Finset (Fin (N + 1))) (i : ℕ) : Cech.Cochain (G S N) i →ₗ[S] Cech.Cochain (G S N) i :=
  Cech.mapC (fun _ => part S J) i

theorem partC_d (J : Finset (Fin (N + 1))) (i : ℕ) (z : Cech.Cochain (G S N) i) :
    Cech.d (G S N) (ρ S N) i (partC S J i z) = partC S J (i + 1) (Cech.d (G S N) (ρ S N) i z) :=
  (Cech.mapC_d (ρ := ρ S N) (ρ' := ρ S N) (fun _ => part S J) (fun _ _ _ _ => rfl) i z).symm

theorem sum_partC (i : ℕ) (z : Cech.Cochain (G S N) i) : ∑ J, partC S J i z = z := by
  funext I
  rw [Finset.sum_apply]
  exact sum_part (z I)

theorem partC_mem_cocy {c : ℤ} {i : ℕ} (J : Finset (Fin (N + 1))) {z : Cech.Cochain (G S N) i}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i) :
    partC S J i z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i :=
  ⟨LinearMap.mem_ker.mpr (by rw [partC_d, LinearMap.mem_ker.mp hz.1, map_zero]),
    fun I _ => part_mem_deg (hz.2 I (Set.mem_univ _))⟩

theorem partC_mem_bdry (hC : Cech.Cone.Statement.{u, u}) {c : ℤ} {i : ℕ}
    {J : Finset (Fin (N + 1))} (hJ : J ≠ Finset.univ) {z : Cech.Cochain (G S N) (i + 1)}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) (i + 1)) :
    partC S J (i + 1) z ∈ Cech.bdryDeg (G S N) (laurentDeg S N c) (ρ S N) (i + 1) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∉ J := by
    by_contra h
    exact hJ (Finset.eq_univ_iff_forall.mpr fun x => by by_contra hx; exact h ⟨x, hx⟩)
  have hzI : ∀ I, z I ∈ laurentDeg S N c I.1 := fun I => hz.2 I (Set.mem_univ _)
  obtain ⟨y, hyW, hy0, hyd⟩ := (hC S (Laurent S N) N J).1 (wPart S N c J) i₀ hi₀ i (partC S J (i + 1) z)
    (by rw [partC_d, LinearMap.mem_ker.mp hz.1, map_zero]) (fun I => part_mem_w (hzI I))
    (fun I h => part_eq_zero (hzI I) h)
  exact Submodule.mem_map.mpr ⟨y, fun I _ => mem_deg_of_w (hyW I) (hy0 I), hyd⟩

theorem partC_zero (hC : Cech.Cone.Statement.{u, u}) {c : ℤ} {J : Finset (Fin (N + 1))}
    (hJ0 : J ≠ ∅) (hJ : J ≠ Finset.univ) {z : Cech.Cochain (G S N) 0}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) 0) : partC S J 0 z = 0 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∉ J := by
    by_contra h
    exact hJ (Finset.eq_univ_iff_forall.mpr fun x => by by_contra hx; exact h ⟨x, hx⟩)
  exact (hC S (Laurent S N) N J).2.1 (Finset.nonempty_iff_ne_empty.mpr hJ0) i₀ hi₀ _
    (by rw [partC_d, LinearMap.mem_ker.mp hz.1, map_zero])
    (fun I h => part_eq_zero (hz.2 I (Set.mem_univ _)) h)

theorem part_univ_eq_zero {c : ℤ} (hc : 0 ≤ c) {I : StdCell N} {f : Laurent S N}
    (hf : f ∈ laurentDeg S N c I) : part S Finset.univ f = 0 := by
  ext a
  rw [part_apply, Finsupp.zero_apply]
  split_ifs with h
  · by_contra h'
    have hneg : ∀ j ∈ Finset.univ, a j < 0 := fun j _ => mem_negSet.mp (h ▸ Finset.mem_univ j)
    have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hneg
    rw [Finset.sum_const_zero, (mem_exps hf h').1] at this
    omega
  · rfl

def bnd (c : ℤ) : Set (Fin (N + 1) → ℤ) :=
  {a | ∑ j, a j = c ∧ (negSet a = ∅ ∨ negSet a = Finset.univ)}

theorem bnd_finite (c : ℤ) : (bnd (N := N) c).Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin (N + 1) => Set.Icc (-|c|) |c|)
    fun _ => Set.finite_Icc _ _).subset ?_
  rintro a ⟨hc, h | h⟩ j -
  · have hnn : ∀ k ∈ Finset.univ, 0 ≤ a k := fun k _ => by
      by_contra hk
      have : k ∈ negSet a := mem_negSet.mpr (by omega)
      rw [h] at this
      exact Finset.notMem_empty _ this
    have h1 := Finset.single_le_sum hnn (Finset.mem_univ j)
    rw [hc] at h1
    have := hnn j (Finset.mem_univ j)
    exact ⟨by linarith [abs_nonneg c], h1.trans (le_abs_self c)⟩
  · have hng : ∀ k ∈ Finset.univ, 0 ≤ -a k := fun k _ => by
      have := mem_negSet.mp (h ▸ Finset.mem_univ k)
      omega
    have h1 := Finset.single_le_sum hng (Finset.mem_univ j)
    rw [Finset.sum_neg_distrib, hc] at h1
    have := mem_negSet.mp (h ▸ Finset.mem_univ j)
    exact ⟨by linarith [neg_abs_le c], by linarith [abs_nonneg c]⟩

theorem reduce (hC : Cech.Cone.Statement.{u, u}) {c : ℤ} {i : ℕ} {z : Cech.Cochain (G S N) i}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i) :
    ∃ w ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i,
      (∀ I, w I ∈ Finsupp.supported S S (bnd c)) ∧
      z - w ∈ Cech.bdryDeg (G S N) (laurentDeg S N c) (ρ S N) i := by
  classical
  let K : Finset (Finset (Fin (N + 1))) := Finset.univ.filter fun J => J ≠ ∅ ∧ J ≠ Finset.univ
  refine ⟨z - ∑ J ∈ K, partC S J i z,
    Submodule.sub_mem _ hz (Submodule.sum_mem _ fun J _ => partC_mem_cocy J hz), fun I => ?_, ?_⟩
  · refine (Finsupp.mem_supported' S _).mpr fun a ha => ?_
    change z I a - (∑ J ∈ K, partC S J i z) I a = 0
    rw [Finset.sum_apply, Finsupp.finsetSum_apply]
    change z I a - ∑ J ∈ K, part S J (z I) a = 0
    simp only [part_apply]
    rw [Finset.sum_ite_eq]
    split_ifs with hK
    · exact sub_self _
    · rw [sub_zero]
      by_contra h'
      have hc := (mem_exps (hz.2 I (Set.mem_univ _)) h').1
      apply ha
      refine ⟨hc, ?_⟩
      by_contra hb
      exact hK (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h0 => hb (Or.inl h0),
        fun h1 => hb (Or.inr h1)⟩)
  · rw [sub_sub_cancel]
    cases i with
    | zero =>
      have h0 : ∑ J ∈ K, partC S J 0 z = 0 := Finset.sum_eq_zero fun J hJ =>
        partC_zero hC (Finset.mem_filter.mp hJ).2.1 (Finset.mem_filter.mp hJ).2.2 hz
      rw [h0]
      exact Submodule.zero_mem _
    | succ i =>
      exact Submodule.sum_mem _ fun J hJ => partC_mem_bdry hC (Finset.mem_filter.mp hJ).2.2 hz

theorem mk_eq {c : ℤ} {i : ℕ} {z w : Cech.Cochain (G S N) i}
    (hz : z ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i)
    (hw : w ∈ Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i)
    (h : z - w ∈ Cech.bdryDeg (G S N) (laurentDeg S N c) (ρ S N) i) :
    (Submodule.Quotient.mk ⟨z, hz⟩ : laurentCohom S N i c) = Submodule.Quotient.mk ⟨w, hw⟩ :=
  (Submodule.Quotient.eq _).mpr h

end LaurentCohomProof

open LaurentCohomProof in

theorem SerrePoly.LaurentCohom.proof (hC : Cech.Cone.Statement.{u, u}) :
    SerrePoly.LaurentCohom.Statement.{u} := by
  intro S _ _ N
  refine ⟨fun i c => ?_, fun c hc i hi => ?_, fun c hc z hz => ?_⟩
  ·
    let B := Finsupp.supported S S (bnd (N := N) c)
    have : Finite (bnd (N := N) c) := (bnd_finite c).to_subtype
    have : Module.Finite S B := Module.Finite.equiv (Finsupp.supportedEquivFinsupp _).symm
    let T := ∀ _ : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i, B
    let ψ : T →ₗ[S] Cech.Cochain (G S N) i :=
      LinearMap.pi fun I => B.subtype.comp (LinearMap.proj I)
    let C := Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i
    let P := C.comap ψ
    have : IsNoetherian S T := isNoetherian_of_linearEquiv
      (LinearEquiv.piCongrRight fun _ => Finsupp.supportedEquivFinsupp (M := S) (R := S) (bnd c)).symm
    have : Module.Finite S P := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian P)
    let g : P →ₗ[S] laurentCohom S N i c :=
      (Submodule.mkQ _).comp (ψ.restrict (p := P) (q := C) fun _ hx => hx)
    refine Module.Finite.of_surjective g fun x => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨w, hw, hwB, hzw⟩ := reduce hC hz
    have hP : (fun I => (⟨w I, hwB I⟩ : B)) ∈ P := Submodule.mem_comap.mpr hw
    refine ⟨⟨_, hP⟩, ?_⟩
    exact (mk_eq hz hw hzw).symm
  ·
    obtain ⟨i, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    refine (Submodule.Quotient.subsingleton_iff).mpr (eq_top_iff.mpr fun ⟨z, hz⟩ _ => ?_)
    change z ∈ Cech.bdryDeg _ _ _ _
    have hu : partC S Finset.univ (i + 1) z = 0 := by
      funext I
      exact part_univ_eq_zero hc (hz.2 I (Set.mem_univ _))
    rw [← sum_partC (S := S) (i + 1) z, ← Finset.sum_erase_add _ _ (Finset.mem_univ Finset.univ), hu,
      add_zero]
    exact Submodule.sum_mem _ fun J hJ => partC_mem_bdry hC (Finset.ne_of_mem_erase hJ) hz
  ·
    let sg : Fin (N + 1) → Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 := fun k =>
      ⟨⟨{k}, Finset.singleton_nonempty k, Finset.subset_univ _⟩, Finset.card_singleton k⟩
    have hconst := (hC S (Laurent S N) N ∅).2.2 z (LinearMap.mem_ker.mp hz.1)
    refine ⟨z (sg 0), (Finsupp.mem_supported' S _).mpr fun a ha => ?_, fun I => hconst I (sg 0)⟩
    by_contra h'
    apply ha
    refine ⟨(mem_exps (hz.2 (sg 0) (Set.mem_univ _)) h').1, fun j _ => ?_⟩
    by_cases hk : ∃ k, k ≠ j
    · obtain ⟨k, hk⟩ := hk
      have h'' : z (sg k) a ≠ 0 := by rwa [hconst (sg k) (sg 0)]
      exact (mem_exps (hz.2 (sg k) (Set.mem_univ _)) h'').2 j (by simpa [sg] using hk.symm)
    · replace hk : ∀ k, k = j := fun k => by by_contra h; exact hk ⟨k, h⟩
      have hs := (mem_exps (hz.2 (sg 0) (Set.mem_univ _)) h').1
      rw [Finset.sum_eq_single j (fun k _ hkj => absurd (hk k) hkj) (by simp)] at hs
      omega

end

end GroundTheory.Heights₂.Heights.Kleiman
