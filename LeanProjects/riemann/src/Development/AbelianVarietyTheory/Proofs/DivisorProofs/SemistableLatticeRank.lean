import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.LieRead

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieRead

theorem exists_ne_zero_smul_mem {K : Type} [Field K] [NumberField K] {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K))
    {c : Fin m → K} (hc : c ∈ Submodule.span K (L : Set (Fin m → K))) :
    ∃ n : 𝓞 K, n ≠ 0 ∧ n • c ∈ L := by
  refine Submodule.span_induction (p := fun c _ => ∃ n : 𝓞 K, n ≠ 0 ∧ n • c ∈ L)
    (fun c hc => ⟨1, one_ne_zero, by rwa [one_smul]⟩) ⟨1, one_ne_zero, by simp⟩ ?_ ?_ hc
  · rintro x y - - ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [_root_.mul_comm, mul_smul]; exact L.smul_mem _ hx
    · rw [mul_smul]; exact L.smul_mem _ hy
  · rintro a x - ⟨n, hn, hx⟩
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    have hs' := nonZeroDivisors.ne_zero hs
    refine ⟨n * s, mul_ne_zero hn hs', ?_⟩
    have hs'' : algebraMap (𝓞 K) K s ≠ 0 := fun h => hs' (RingOfIntegers.coe_injective (h.trans (map_zero _).symm))
    have : (n * s) • (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) • x = r • n • x := by
      rw [← algebraMap_smul K (n * s), ← algebraMap_smul K r, ← algebraMap_smul K n, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem _ hx

theorem span_inf_restrictScalars {K : Type} [Field K] [NumberField K] {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K))
    (hL : Submodule.span K (L : Set (Fin m → K)) = ⊤) (W : Submodule K (Fin m → K)) :
    Submodule.span K ((L ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin m → K)) : Set (Fin m → K)) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro v hv
    exact hv.2
  · intro v hv
    obtain ⟨n, hn, hnv⟩ := exists_ne_zero_smul_mem L (c := v) (hL ▸ Submodule.mem_top)
    have hn' : algebraMap (𝓞 K) K n ≠ 0 := fun h => hn (RingOfIntegers.coe_injective (h.trans (map_zero _).symm))
    have hmem : n • v ∈ (L ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin m → K)) := by
      refine ⟨hnv, ?_⟩
      show n • v ∈ W
      rw [← algebraMap_smul K n]
      exact W.smul_mem _ hv
    have h2 := Submodule.smul_mem (Submodule.span K _) (algebraMap (𝓞 K) K n)⁻¹ (Submodule.subset_span hmem)
    rwa [← algebraMap_smul K n, inv_smul_smul₀ hn'] at h2

section Letters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)

theorem letters_nodup : (letters Dw).Nodup := by
  unfold letters
  rw [List.nodup_flatMap]
  refine ⟨fun a _ => (List.nodup_finRange _).map ?_, ?_⟩
  · intro i j h
    exact eq_of_heq (Sigma.mk.inj_iff.1 h).2
  · refine List.Pairwise.imp ?_ (List.nodup_finRange (Fintype.card (E →+* ℂ)))
    intro a b hab
    rw [Function.onFun, List.disjoint_left]
    intro x hx hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, -, h⟩ := List.mem_map.1 hy
    exact hab ((Fintype.equivFin _).symm.injective (congrArg Sigma.fst h).symm)

theorem mem_letters (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, j⟩ := x
  obtain ⟨a, rfl⟩ := (Fintype.equivFin (E →+* ℂ)).symm.surjective τ
  rw [letters, List.mem_flatMap]
  exact ⟨a, List.mem_finRange _, List.mem_map.2 ⟨j, List.mem_finRange _, rfl⟩⟩

end Letters

theorem latRank_stepLat : ∀ (D : D7) (O : Setup D) (K : Type) [Field K] [NumberField K] (F : SemiFib K),
    F.P₀.g = (letters O.S.Dw).length → Full F.lieLat → ∀ (τ : D.host.E →+* ℂ) (k : ℕ), k ≤ O.S.Dw.mult τ →
    latRank K (stepLat O F τ k) = k := by
  intro D O K _ _ F hg hF τ k hk
  classical
  let P : Fin F.P₀.g → Prop := fun i =>
    ∃ x : Letter O.S.Dw, x.1 = τ ∧ (x.2 : ℕ) < k ∧ (letters O.S.Dw)[(i : ℕ)]? = some x
  have hset : {v : Fin F.P₀.g → K | ∃ (i : Fin F.P₀.g) (x : Letter O.S.Dw), x.1 = τ ∧ (x.2 : ℕ) < k ∧
      (letters O.S.Dw)[(i : ℕ)]? = some x ∧ v = Pi.single i 1} =
      Set.range (fun i : {i // P i} => (Pi.single (i : Fin F.P₀.g) (1 : K) : Fin F.P₀.g → K)) := by
    ext v
    constructor
    · rintro ⟨i, x, h1, h2, h3, rfl⟩
      exact ⟨⟨i, x, h1, h2, h3⟩, rfl⟩
    · rintro ⟨⟨i, x, h1, h2, h3⟩, rfl⟩
      exact ⟨i, x, h1, h2, h3, rfl⟩
  have hli : LinearIndependent K
      (fun i : {i // P i} => (Pi.single (i : Fin F.P₀.g) (1 : K) : Fin F.P₀.g → K)) := by
    have := (Pi.basisFun K (Fin F.P₀.g)).linearIndependent.comp (Subtype.val : {i // P i} → Fin F.P₀.g)
      Subtype.val_injective
    simpa [Function.comp_def, Pi.basisFun_apply] using this
  unfold latRank stepLat
  rw [span_inf_restrictScalars _ hF.2, hset, finrank_span_eq_card hli, Fintype.card_subtype]
  let f : Fin F.P₀.g → ℕ := fun i => (((letters O.S.Dw)[(i : ℕ)]?).map fun x => (x.2 : ℕ)).getD 0
  have hf : ∀ (i : Fin F.P₀.g) (x : Letter O.S.Dw), (letters O.S.Dw)[(i : ℕ)]? = some x → f i = x.2 := by
    intro i x h
    simp [f, h]
  refine Eq.trans ?_ (Finset.card_range k)
  refine Finset.card_bij (fun i _ => f i) ?_ ?_ ?_
  · intro i hi
    obtain ⟨x, -, h2, h3⟩ := (Finset.mem_filter.1 hi).2
    rw [Finset.mem_range, hf i x h3]
    exact h2
  · intro i₁ hi₁ i₂ hi₂ he
    obtain ⟨x₁, h₁, -, h₃⟩ := (Finset.mem_filter.1 hi₁).2
    obtain ⟨x₂, h₁', -, h₃'⟩ := (Finset.mem_filter.1 hi₂).2
    have hv : (x₁.2 : ℕ) = x₂.2 := by
      have : f i₁ = f i₂ := he
      rw [hf _ _ h₃, hf _ _ h₃'] at this
      exact this
    have hx : x₁ = x₂ := by
      obtain ⟨τ₁, j₁⟩ := x₁
      obtain ⟨τ₂, j₂⟩ := x₂
      simp only at h₁ h₁' hv
      subst h₁ h₁'
      exact Sigma.ext rfl ((Fin.heq_ext_iff rfl).2 hv)
    subst hx
    obtain ⟨hl₁, e₁⟩ := List.getElem?_eq_some_iff.1 h₃
    obtain ⟨hl₂, e₂⟩ := List.getElem?_eq_some_iff.1 h₃'
    exact Fin.ext (((letters_nodup O.S.Dw).getElem_inj_iff).1 (e₁.trans e₂.symm))
  · intro b hb
    rw [Finset.mem_range] at hb
    let x : Letter O.S.Dw := ⟨τ, ⟨b, lt_of_lt_of_le hb hk⟩⟩
    obtain ⟨n, hn, hx⟩ := List.getElem_of_mem (mem_letters O.S.Dw x)
    have h3 : (letters O.S.Dw)[((⟨n, hg ▸ hn⟩ : Fin F.P₀.g) : ℕ)]? = some x :=
      List.getElem?_eq_some_iff.2 ⟨hn, hx⟩
    refine ⟨⟨n, hg ▸ hn⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, x, rfl, hb, h3⟩, ?_⟩
    exact hf _ x h3

end GlobalTheory.LieRead

end
