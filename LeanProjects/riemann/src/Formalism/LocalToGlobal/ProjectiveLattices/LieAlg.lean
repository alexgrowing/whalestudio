import Mathlib

noncomputable section

namespace Formalism.L2.Pj.LieAlg

open Submodule

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem exists_divisor (s : Finset K) : ∃ t : K, (t = 0 → ∀ x ∈ s, x = 0) ∧ (t = 0 ∨ t ∈ s) ∧
    ∀ x ∈ s, ∃ r : V, x = algebraMap V K r * t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, Or.inl rfl, by simp⟩
  | insert a s ha ih =>
    obtain ⟨t, h0, hts, hdiv⟩ := ih
    by_cases ht : t = 0
    · have hs := h0 ht
      refine ⟨a, fun hz x hx => ?_, Or.inr (Finset.mem_insert_self a s), fun x hx => ?_⟩
      · rcases Finset.mem_insert.1 hx with hx | hx
        · rw [hx]; exact hz
        · exact hs x hx
      · rcases Finset.mem_insert.1 hx with hx | hx
        · exact ⟨1, by simp [hx]⟩
        · exact ⟨0, by simp [hs x hx]⟩
    · have hts' : t = 0 ∨ t ∈ insert a s := by
        rcases hts with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_insert_of_mem h)
      by_cases haz : a = 0
      · refine ⟨t, fun h => absurd h ht, hts', fun x hx => ?_⟩
        rcases Finset.mem_insert.1 hx with hx | hx
        · exact ⟨0, by simp [hx, haz]⟩
        · exact hdiv x hx
      · rcases (ValuationRing.iff_isInteger_or_isInteger V K).1 inferInstance (a / t) with ⟨r, hr⟩ | ⟨r, hr⟩
        · refine ⟨t, fun h => absurd h ht, hts', fun x hx => ?_⟩
          rcases Finset.mem_insert.1 hx with hx | hx
          · exact ⟨r, by rw [hx, hr]; field_simp⟩
          · exact hdiv x hx
        · refine ⟨a, fun h => absurd h haz, Or.inr (Finset.mem_insert_self a s), fun x hx => ?_⟩
          rcases Finset.mem_insert.1 hx with hx | hx
          · exact ⟨1, by simp [hx]⟩
          · obtain ⟨q, hq⟩ := hdiv x hx
            refine ⟨q * r, ?_⟩
            rw [hq, map_mul, hr]
            field_simp

theorem fg_eq_span_singleton (S : Submodule V K) (hS : S.FG) : ∃ t : K, S = span V {t} := by
  classical
  obtain ⟨s, rfl⟩ := hS
  obtain ⟨t, -, hts, hdiv⟩ := exists_divisor (V := V) s
  refine ⟨t, le_antisymm ?_ ?_⟩
  · rw [span_le]
    intro x hx
    obtain ⟨r, hr⟩ := hdiv x hx
    rw [SetLike.mem_coe, mem_span_singleton]
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  · rw [span_le, Set.singleton_subset_iff]
    rcases hts with h | h
    · rw [h]; exact zero_mem _
    · exact subset_span h

def tailZero (m : ℕ) (i : Fin m) : Submodule V (Fin m → K) where
  carrier := {α | ∀ j, i < j → α j = 0}
  add_mem' {a b} ha hb j hj := by simp [ha j hj, hb j hj]
  zero_mem' j _ := rfl
  smul_mem' r α ha j hj := by simp [ha j hj]

theorem herm (m : ℕ) (Λ : Submodule V (Fin m → K)) (hfg : Λ.FG)
    (hne : ∀ i : Fin m, ∃ α ∈ Λ, (∀ j, i < j → α j = 0) ∧ α i ≠ 0) :
    ∃ β : Fin m → (Fin m → K), (∀ i, β i ∈ Λ) ∧ (∀ i j, i < j → β i j = 0) ∧ (∀ i, β i i ≠ 0) ∧
      ∀ α ∈ Λ, ∃! r : Fin m → V, α = ∑ i, r i • β i := by
  classical
  haveI : IsNoetherian V Λ := isNoetherian_of_fg_of_noetherian Λ hfg
  have key : ∀ i : Fin m, ∃ b : Fin m → K, b ∈ Λ ∧ (∀ j, i < j → b j = 0) ∧ b i ≠ 0 ∧
      ∀ α ∈ Λ, (∀ j, i < j → α j = 0) → ∃ c : V, α i = c • b i := by
    intro i
    let I : Submodule V K := (Λ ⊓ tailZero (V := V) (K := K) m i).map (LinearMap.proj i)
    have hIfg : I.FG := by
      have h1 : ((tailZero (V := V) (K := K) m i).comap Λ.subtype).FG := IsNoetherian.noetherian _
      have h2 := h1.map Λ.subtype
      rw [Submodule.map_comap_subtype] at h2
      exact h2.map _
    obtain ⟨t, ht⟩ := fg_eq_span_singleton I hIfg
    have tI : t ∈ I := ht ▸ mem_span_singleton_self t
    obtain ⟨b, ⟨hbΛ, hbz⟩, hbt⟩ := Submodule.mem_map.1 tI
    have hbt' : b i = t := hbt
    have hmem : ∀ α ∈ Λ, (∀ j, i < j → α j = 0) → ∃ c : V, α i = c • b i := by
      intro α hα hz
      have h3 : α i ∈ I := Submodule.mem_map.2 ⟨α, ⟨hα, hz⟩, rfl⟩
      rw [ht, mem_span_singleton] at h3
      obtain ⟨c, hc⟩ := h3
      exact ⟨c, by rw [hbt', hc]⟩
    refine ⟨b, hbΛ, hbz, ?_, hmem⟩
    obtain ⟨α, hα, hz, hne'⟩ := hne i
    obtain ⟨c, hc⟩ := hmem α hα hz
    intro h0
    exact hne' (by rw [hc, h0, smul_zero])
  choose β hβΛ hβz hβd hβc using key
  have indep : ∀ r : Fin m → V, ∑ i, r i • β i = 0 → r = 0 := by
    intro r hr
    by_contra hne0
    have hS : (Finset.univ.filter fun i => r i ≠ 0).Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hne0
      exact ⟨i, by simpa using hi⟩
    have hi : r ((Finset.univ.filter fun i => r i ≠ 0).max' hS) ≠ 0 := by
      have h4 := Finset.max'_mem _ hS
      simpa using h4
    set i := (Finset.univ.filter fun i => r i ≠ 0).max' hS with hidef
    have hgt : ∀ j, i < j → r j = 0 := by
      intro j hj
      by_contra h
      have h5 : j ≤ i := Finset.le_max' _ j (by simpa using h)
      exact absurd hj (not_lt.2 h5)
    have hcoord := congrFun hr i
    rw [Finset.sum_apply, Finset.sum_eq_single i] at hcoord
    · rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, mul_eq_zero] at hcoord
      rcases hcoord with h | h
      · exact hi ((IsFractionRing.injective V K) (by rw [h, map_zero]))
      · exact hβd i h
    · intro j _ hji
      rw [Pi.smul_apply]
      rcases lt_or_gt_of_ne hji with h | h
      · rw [hβz j i h, smul_zero]
      · rw [hgt j h, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have exist : ∀ k : ℕ, ∀ α ∈ Λ, (∀ j : Fin m, k ≤ j.val → α j = 0) →
      ∃ r : Fin m → V, α = ∑ i, r i • β i := by
    intro k
    induction k with
    | zero =>
      intro α _ hz
      refine ⟨0, ?_⟩
      funext j
      simp [hz j (Nat.zero_le _)]
    | succ k ih =>
      intro α hα hz
      by_cases hk : k < m
      · let i : Fin m := ⟨k, hk⟩
        obtain ⟨c, hc⟩ := hβc i α hα (fun j hj => hz j (by have h6 : k < j.val := hj; omega))
        obtain ⟨r, hr⟩ := ih (α - c • β i) (Λ.sub_mem hα (Λ.smul_mem c (hβΛ i))) (by
          intro j hj
          simp only [Pi.sub_apply, Pi.smul_apply]
          rcases Nat.eq_or_lt_of_le hj with h | h
          · have h7 : j = i := Fin.ext h.symm
            rw [h7, hc, sub_self]
          · rw [hz j h, hβz i j (show i < j from h), smul_zero, sub_zero])
        have hs : ∑ j, (Pi.single i c : Fin m → V) j • β j = c • β i := by
          rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp),
            Pi.single_eq_same]
        refine ⟨r + Pi.single i c, ?_⟩
        rw [sub_eq_iff_eq_add] at hr
        rw [hr]
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hs]
      · exact ih α hα (fun j hj => hz j (by have := j.isLt; omega))
  refine ⟨β, hβΛ, hβz, hβd, ?_⟩
  intro α hα
  obtain ⟨r, hr⟩ := exist m α hα (fun j hj => absurd j.isLt (not_lt.2 hj))
  refine ⟨r, hr, fun r' hr' => ?_⟩
  have h8 := indep (r' - r) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    rw [← hr, ← hr', sub_self])
  exact sub_eq_zero.1 h8

theorem eig_basis {n m : ℕ} {ι : Type} (L : ι → (Fin n → V) →ₗ[V] (Fin n → V)) (χ : ι → V)
    (M : ι → (Fin n → K) →ₗ[K] (Fin n → K))
    (hM : ∀ a c, M a (fun j => algebraMap V K (c j)) = fun j => algebraMap V K (L a c j))
    (v : Fin m → (Fin n → K)) (hv : ∀ a i, M a (v i) = algebraMap V K (χ a) • v i)
    (hb : ∀ w, (∀ a, M a w = algebraMap V K (χ a) • w) → ∃! cf : Fin m → K, w = ∑ i, cf i • v i) :
    ∃ b : Fin m → (Fin n → V), (∀ a i, L a (b i) = χ a • b i) ∧
      (∀ c, (∀ a, L a c = χ a • c) → ∃! r : Fin m → V, c = ∑ i, r i • b i) ∧
      ∀ i, ∃ cf : Fin m → K, cf i ≠ 0 ∧ (∀ j, i < j → cf j = 0) ∧
        (fun j => algebraMap V K (b i j)) = ∑ j, cf j • v j := by
  classical
  let emb : (Fin n → V) → (Fin n → K) := fun c j => algebraMap V K (c j)
  have embinj : Function.Injective emb := fun c c' h =>
    funext fun j => IsFractionRing.injective V K (congrFun h j)
  have embadd : ∀ c c', emb (c + c') = emb c + emb c' := fun c c' => funext fun j => by simp [emb]
  have embsmul : ∀ (r : V) c, emb (r • c) = algebraMap V K r • emb c := fun r c =>
    funext fun j => by simp [emb]
  have embM : ∀ a c, M a (emb c) = emb (L a c) := fun a c => hM a c
  let E : Submodule V (Fin n → V) :=
    { carrier := {c | ∀ a, L a c = χ a • c}
      add_mem' := fun {c c'} hc hc' a => by
        simp only [Set.mem_setOf_eq] at hc hc' ⊢
        rw [map_add, hc a, hc' a, smul_add]
      zero_mem' := fun a => by simp
      smul_mem' := fun r c hc a => by
        simp only [Set.mem_setOf_eq] at hc ⊢
        rw [map_smul, hc a, smul_comm] }
  have memE : ∀ c, c ∈ E ↔ ∀ a, L a c = χ a • c := fun c => Iff.rfl
  have eigK : ∀ c ∈ E, ∀ a, M a (emb c) = algebraMap V K (χ a) • emb c := fun c hc a => by
    rw [embM, (memE c).1 hc a, embsmul]
  have hco : ∀ c : E, ∃! cf : Fin m → K, emb c = ∑ i, cf i • v i := fun c => hb _ (eigK c c.2)
  choose g spec hgu using hco
  let f : E →ₗ[V] (Fin m → K) :=
    { toFun := g
      map_add' := fun c c' => (hgu (c + c') _ (by
        rw [Submodule.coe_add, embadd, spec c, spec c', ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.add_apply, add_smul])).symm
      map_smul' := fun r c => (hgu (r • c) _ (by
        rw [Submodule.coe_smul, embsmul, spec c, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [RingHom.id_apply, Pi.smul_apply, smul_smul]
        congr 1
        exact (Algebra.smul_def _ _).symm)).symm }
  have fspec : ∀ c : E, emb c = ∑ i, f c i • v i := spec
  have finj : Function.Injective f := fun x y h => Subtype.ext (embinj (by rw [fspec x, fspec y, h]))
  have hfg : (LinearMap.range f).FG := by
    rw [LinearMap.range_eq_map]
    exact (IsNoetherian.noetherian (⊤ : Submodule V E)).map f
  have hne : ∀ i : Fin m, ∃ α ∈ LinearMap.range f, (∀ j, i < j → α j = 0) ∧ α i ≠ 0 := by
    intro i
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors V) (Finset.univ) (v i)
    choose c hc using fun j => hd j (Finset.mem_univ j)
    have hcv : emb c = algebraMap V K (d : V) • v i := by
      funext j
      show algebraMap V K (c j) = _
      rw [hc j, Algebra.smul_def, Pi.smul_apply, smul_eq_mul]
    have hcE : c ∈ E := fun a => embinj (by
      rw [← embM, hcv, map_smul, hv, embsmul, hcv, smul_comm])
    have hfc : f ⟨c, hcE⟩ = Pi.single i (algebraMap V K (d : V)) := (hgu ⟨c, hcE⟩ _ (by
      show emb c = _
      rw [hcv, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp),
        Pi.single_eq_same])).symm
    refine ⟨f ⟨c, hcE⟩, ⟨⟨c, hcE⟩, rfl⟩, fun j hj => ?_, ?_⟩
    · rw [hfc, Pi.single_eq_of_ne (ne_of_gt hj)]
    · rw [hfc, Pi.single_eq_same]
      intro h0
      exact nonZeroDivisors.ne_zero d.2 (IsFractionRing.injective V K (by rw [h0, map_zero]))
  obtain ⟨β, hβΛ, hβz, hβd, hβu⟩ := herm m (LinearMap.range f) hfg hne
  choose e he using hβΛ
  refine ⟨fun i => (e i : Fin n → V), fun a i => (e i).2 a, ?_, ?_⟩
  · intro c hc
    have key : ∀ r' : Fin m → V, c = ∑ i, r' i • (e i : Fin n → V) ↔ f ⟨c, hc⟩ = ∑ i, r' i • β i := by
      intro r'
      have hsum : ((∑ i, r' i • e i : E) : Fin n → V) = ∑ i, r' i • (e i : Fin n → V) := by simp
      have hf : f (∑ i, r' i • e i) = ∑ i, r' i • β i := by simp [map_sum, map_smul, he]
      constructor
      · intro h
        rw [← hf]
        congr 1
        exact Subtype.ext (by rw [hsum]; exact h)
      · intro h
        rw [← hf] at h
        have h' := congrArg Subtype.val (finj h)
        rw [hsum] at h'
        exact h'
    obtain ⟨r, hr, hru⟩ := hβu (f ⟨c, hc⟩) ⟨⟨c, hc⟩, rfl⟩
    exact ⟨r, (key r).2 hr, fun r' h => hru r' ((key r').1 h)⟩
  · intro i
    refine ⟨β i, hβd i, hβz i, ?_⟩
    have h9 := fspec (e i)
    rw [he i] at h9
    exact h9

theorem tri_basis {n m : ℕ} (P : (Fin n → K) → Prop) (v : Fin m → (Fin n → K))
    (hb : ∀ w, P w → ∃! cf : Fin m → K, w = ∑ i, cf i • v i) (C : Fin m → Fin m → K)
    (hCz : ∀ i j, i < j → C i j = 0) (hCd : ∀ i, C i i ≠ 0) :
    ∀ w, P w → ∃! d : Fin m → K, w = ∑ i, d i • ∑ j, C i j • v j := by
  classical
  let A : Matrix (Fin m) (Fin m) K := Matrix.of C
  have hA : A.IsLowerTriangular := fun i j h => hCz i j h
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular A hA]
    exact Finset.prod_ne_zero_iff.2 (fun i _ => hCd i)
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  have expand : ∀ d : Fin m → K, ∑ i, d i • ∑ j, C i j • v j = ∑ j, (Matrix.vecMul d A) j • v j := by
    intro d
    simp only [Matrix.vecMul, dotProduct, A, Matrix.of_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  intro w hw
  obtain ⟨cf, hcf, huniq⟩ := hb w hw
  refine ⟨Matrix.vecMul cf A⁻¹, ?_, fun d hd => ?_⟩
  · show w = _
    rw [expand, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul A hu, Matrix.vecMul_one]
    exact hcf
  · have h1 : Matrix.vecMul d A = cf := huniq _ (by show w = _; rw [← expand]; exact hd)
    rw [← h1, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hu, Matrix.vecMul_one]

end Formalism.L2.Pj.LieAlg
