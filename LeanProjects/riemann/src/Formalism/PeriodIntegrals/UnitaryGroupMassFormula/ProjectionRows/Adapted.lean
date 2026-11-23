import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.AsmDual

noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv

variable {K : Type} [Field K] [NumberField K] [StarRing K]

lemma exists_smul_mem_of_span {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) {x : V}
    (hx : x ∈ Submodule.span K (M : Set V)) : ∃ s : 𝓞 K, s ≠ 0 ∧ s • x ∈ M := by
  obtain ⟨s, hs, hsx⟩ := span_le_locS M hx
  exact ⟨s, nonZeroDivisors.ne_zero hs, hsx⟩

lemma mem_span_of_smul_mem {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) {x : V} (s : 𝓞 K) (hs : s ≠ 0)
    (hsx : s • x ∈ M) : x ∈ Submodule.span K (M : Set V) := by
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
    intro h0; exact hs (IsFractionRing.injective (𝓞 K) K (by rw [h0, map_zero]))
  have : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
    rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)

lemma extend_family {V : Type} [AddCommGroup V] [Module K V] {k m : ℕ} (u : Fin k → V) (t : Fin m → V)
    (hu : LinearIndependent K u) :
    ∃ (d : ℕ) (z : Fin d → V), LinearIndependent K (Fin.append u z) ∧ (∀ i, ∃ j, z i = t j) ∧
      Set.range u ∪ Set.range t ⊆ Submodule.span K (Set.range (Fin.append u z)) := by
  classical
  let v : Fin k ⊕ Fin m → V := Sum.elim u t
  have hs : LinearIndepOn K v (Set.range Sum.inl) := by
    rw [linearIndepOn_range_iff Sum.inl_injective]
    exact hu
  obtain ⟨b, -, hsb, hspan, hli⟩ := exists_linearIndepOn_extension hs (Set.subset_univ _)
  let T : Finset (Fin m) := Finset.univ.filter (fun j => Sum.inr j ∈ b)
  let en : Fin T.card ↪o Fin m := T.orderEmbOfFin rfl
  have hen : ∀ i, en i ∈ T := fun i => T.orderEmbOfFin_mem rfl i
  let g : Fin (k + T.card) → Fin k ⊕ Fin m := Fin.append Sum.inl (Sum.inr ∘ en)
  have hg : Function.Injective g := by
    intro i j hij
    revert hij
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;>
      refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j <;> intro hij <;>
      simp [g, Fin.append_left, Fin.append_right] at hij ⊢
    · exact hij
    · exact hij
  have hrange : Set.range g = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
      · simp only [g, Fin.append_left]; exact hsb ⟨i', rfl⟩
      · simp only [g, Fin.append_right, Function.comp]
        have := hen i'
        simpa [T] using this
    · intro hx
      rcases x with x | x
      · exact ⟨Fin.castAdd _ x, by simp [g]⟩
      · have hxT : x ∈ T := by simp [T, hx]
        obtain ⟨i, hi⟩ : ∃ i, en i = x := by
          have := T.range_orderEmbOfFin rfl
          have hx' : x ∈ Set.range (T.orderEmbOfFin rfl) := by rw [this]; exact hxT
          exact hx'
        exact ⟨Fin.natAdd _ i, by simp [g, hi]⟩
  have hvg : v ∘ g = Fin.append u (t ∘ en) := by
    funext i
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
    · simp [g, v]
    · simp [g, v]
  refine ⟨T.card, t ∘ en, ?_, fun i => ⟨en i, rfl⟩, ?_⟩
  · rw [← hvg, ← linearIndepOn_range_iff hg, hrange]
    exact hli
  · have h1 : v '' b = Set.range (Fin.append u (t ∘ en)) := by
      rw [← hvg, Set.range_comp, hrange]
    rw [← h1]
    intro x hx
    apply hspan
    rcases hx with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨Sum.inl i, Set.mem_univ _, rfl⟩
    · exact ⟨Sum.inr j, Set.mem_univ _, rfl⟩

theorem adapted_bases_exist : Adapted := by
  classical
  intro K _ _ _ _ _ A e n h hyp U hU
  obtain ⟨hS, hP, hH, hC⟩ := hyp
  obtain ⟨hG, hn, hee, hnL, -⟩ := hP
  haveI : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  have hidem : ∀ x ∈ LinearMap.range e, e x = x := by
    rintro x ⟨z, rfl⟩
    change (e * e) z = e z
    rw [hee]
  set M := cutE A e A.L with hMdef
  set S := M ⊓ U.restrictScalars (𝓞 K) with hSdef
  have hMfg : M.FG := Submodule.FG.of_le hG.2.1 inf_le_left
  have hSfg : S.FG := Submodule.FG.of_le hG.2.1 (inf_le_left.trans inf_le_left)
  have hspanM : Submodule.span K (M : Set A.V) = LinearMap.range e := by
    apply le_antisymm
    · exact Submodule.span_le.2 (fun x hx => hx.2)
    · rintro _ ⟨x', rfl⟩
      have hx' : x' ∈ Submodule.span K (A.L : Set A.V) := by rw [hG.2.2]; trivial
      have key : ∀ a ∈ A.L, e a ∈ Submodule.span K (M : Set A.V) := by
        intro a ha
        have h1 : ((n : ℕ) : 𝓞 K) • e a ∈ M :=
          ⟨hnL a ha, Submodule.smul_of_tower_mem _ _ (LinearMap.mem_range_self e a)⟩
        exact mem_span_of_smul_mem M _ (by exact_mod_cast hn.ne') h1
      induction hx' using Submodule.span_induction with
      | mem a ha => exact key a ha
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have hspanS : Submodule.span K (S : Set A.V) = U := by
    apply le_antisymm
    · exact Submodule.span_le.2 (fun x hx => hx.2)
    · intro x hx
      have hxM : x ∈ Submodule.span K (M : Set A.V) := by rw [hspanM]; exact hU hx
      obtain ⟨s, hs0, hsx⟩ := exists_smul_mem_of_span M hxM
      refine mem_span_of_smul_mem S s hs0 ⟨hsx, ?_⟩
      show s • x ∈ U
      exact Submodule.smul_of_tower_mem _ s hx
  obtain ⟨k, u, hu, huS, hspu⟩ := covolume_exists K A.V S
  obtain ⟨m, t, ht, htM, hspt⟩ := covolume_exists K A.V M
  obtain ⟨d, z, hlin, hzt, hsub⟩ := extend_family u t hu
  have hzfM : ∀ i, Fin.append u z i ∈ M := by
    intro i
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
    · simp only [Fin.append_left]; exact (huS i').1
    · simp only [Fin.append_right]
      obtain ⟨j, hj⟩ := hzt i'
      rw [hj]; exact htM j
  have hspz : Submodule.span K (Set.range (Fin.append u z)) = LinearMap.range e := by
    apply le_antisymm
    · rw [← hspanM]
      exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span (hzfM i))
    · rw [← hspanM, hspt]
      exact Submodule.span_le.2 (fun x hx => hsub (Or.inr hx))
  have hspu' : Submodule.span K (Set.range u) = U := by rw [← hspu, hspanS]
  set Λ := lamSub A e h U with hΛ
  obtain ⟨d', y, hy, hyΛ, hspy⟩ := covolume_exists K A.V Λ
  have hkU : Module.finrank K U = k := by
    rw [← hspu', finrank_span_eq_card hu, Fintype.card_fin]
  have hkd : k + d = dimE A e := by
    unfold dimE
    rw [← hspz, finrank_span_eq_card hlin, Fintype.card_fin]
  have h1 : d' + k ≤ dimE A e := by
    have := card_le_of_orth A e h hee hH U hU y hy (fun i => (hyΛ i).1) (fun i => (hyΛ i).2.1)
    rwa [hkU] at this

  let Ψ : A.V →ₗ[K] (Fin k → K) := LinearMap.pi (fun i => h (u i))
  have hW : LinearMap.range e ⊓ LinearMap.ker Ψ ≤ Submodule.span K (Λ : Set A.V) := by
    rintro x ⟨hxe, hxk⟩
    have hxk' : ∀ i, h (u i) x = 0 := fun i => congrFun (LinearMap.mem_ker.1 hxk) i
    have hxU : ∀ v ∈ U, h x v = 0 := by
      have : U ≤ LinearMap.ker (h x) := by
        rw [← hspu']
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, rfl⟩
        show h x (u i) = 0
        rw [hH.1 (u i) x, hxk' i, star_zero]
      exact fun v hv => LinearMap.mem_ker.1 (this hv)
    obtain ⟨gens, hgens⟩ := hMfg
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
      (gens.image (h x))
    set tt : 𝓞 K := (b : 𝓞 K) with htt
    have ht0 : tt ≠ 0 := nonZeroDivisors.ne_zero b.2
    obtain ⟨s, hs⟩ := star_mem_range tt
    have hss : star (algebraMap (𝓞 K) K s) = algebraMap (𝓞 K) K tt := by rw [hs, star_star]
    have hs0 : s ≠ 0 := by
      rintro rfl
      apply ht0
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_zero, ← hss, map_zero, star_zero]
    refine mem_span_of_smul_mem Λ s hs0 ⟨Submodule.smul_of_tower_mem _ s hxe, fun v hv => ?_, fun mm hmm => ?_⟩
    · rw [h_smul_left, hxU v hv, mul_zero]
    · rw [h_smul_left, hss]
      have hgen : ∀ g ∈ gens, algebraMap (𝓞 K) K tt * h x g ∈ Set.range (algebraMap (𝓞 K) K) := by
        intro g hg
        obtain ⟨r, hr⟩ := hb (h x g) (Finset.mem_image_of_mem _ hg)
        exact ⟨r, by rw [hr, Algebra.smul_def]⟩
      have hmm' : mm ∈ Submodule.span (𝓞 K) (gens : Set A.V) := by rw [hgens]; exact hmm
      clear hmm
      induction hmm' using Submodule.span_induction with
      | mem g hg => exact hgen g hg
      | zero => exact ⟨0, by simp⟩
      | add a c _ _ ha hc =>
        obtain ⟨r1, hr1⟩ := ha
        obtain ⟨r2, hr2⟩ := hc
        exact ⟨r1 + r2, by rw [map_add, hr1, hr2, map_add, mul_add]⟩
      | smul c a _ ha =>
        obtain ⟨r1, hr1⟩ := ha
        refine ⟨c * r1, ?_⟩
        rw [h_smul_right, map_mul, hr1]; ring
  have h2 : d ≤ d' := by
    have hΨ := LinearMap.finrank_range_add_finrank_ker Ψ
    have hΨr : Module.finrank K (LinearMap.range Ψ) ≤ k := by
      have := Submodule.finrank_le (LinearMap.range Ψ)
      simpa using this
    have hsi := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range e) (LinearMap.ker Ψ)
    have hsup := Submodule.finrank_le (LinearMap.range e ⊔ LinearMap.ker Ψ)
    have hWle := Submodule.finrank_mono hW
    have hΛd : Module.finrank K (Submodule.span K (Λ : Set A.V)) = d' := by
      rw [hspy, finrank_span_eq_card hy, Fintype.card_fin]
    unfold dimE at hkd
    omega
  have hdd : d' = d := by omega
  subst hdd
  exact ⟨k, d', u, z, y, hlin, hspz, hspu', hzfM, hy, hyΛ, hspy, hMfg, hSfg,
    hspanM.trans hspz.symm, hspu⟩

end PI.DvRows
