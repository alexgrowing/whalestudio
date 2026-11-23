import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceIntegralBasis

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace RealPlaceEmbeddings

open NumberField Module Submodule
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

instance finite_int : Module.Finite ℤ X.Λ := by
  have : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.mpr X.Λ_fg
  exact Module.Finite.trans (𝓞 E) X.Λ

instance free_int : Module.Free ℤ X.Λ := inferInstance

noncomputable def zb : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ := Module.finBasis ℤ X.Λ

theorem smul_mem_spanQ (α : E) {l : Fin r → E} (hl : l ∈ X.Λ) :
    α • l ∈ span ℚ (X.Λ : Set (Fin r → E)) := by
  have hα : α = ∑ k, (integralBasis E).repr α k • integralBasis E k :=
    ((integralBasis E).sum_repr α).symm
  rw [hα, Finset.sum_smul]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [smul_assoc]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [integralBasis_apply]
  exact X.Λ.smul_of_tower_mem (RingOfIntegers.basis E k) hl

theorem spanQ_eq_top {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) :
    span ℚ (Set.range fun i => (g i : Fin r → E)) = ⊤ := by
  set S := span ℚ (Set.range fun i => (g i : Fin r → E)) with hS
  have hΛ : ∀ l ∈ X.Λ, l ∈ S := by
    intro l hl
    have h1 : (⟨l, hl⟩ : X.Λ) = ∑ i, g.repr ⟨l, hl⟩ i • g i := (g.sum_repr ⟨l, hl⟩).symm
    have h2 : l = ∑ i, ((g.repr ⟨l, hl⟩ i : ℤ) : ℚ) • (g i : Fin r → E) := by
      refine (congrArg Subtype.val h1).trans ?_
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul]
      rfl
    rw [h2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspanΛ : span ℚ (X.Λ : Set (Fin r → E)) ≤ S := Submodule.span_le.mpr fun l hl => hΛ l hl
  have hE : ∀ α : E, ∀ w ∈ S, α • w ∈ S := by
    intro α w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hspanΛ (smul_mem_spanQ X α (g i).2)
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact S.add_mem hy hz
    | smul q y _ hy => rw [smul_comm]; exact S.smul_mem q hy
  refine eq_top_iff.mpr ?_
  rintro v -
  have hv : v ∈ span E (X.Λ : Set (Fin r → E)) := by rw [X.Λ_span]; trivial
  induction hv using Submodule.span_induction with
  | mem y hy => exact hΛ y hy
  | zero => exact S.zero_mem
  | add y z _ _ hy hz => exact S.add_mem hy hz
  | smul α y _ hy => exact hE α y hy

theorem linIndQ {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) :
    LinearIndependent ℚ fun i => (g i : Fin r → E) := by
  have hZ : LinearIndependent ℤ fun i => (g i : Fin r → E) :=
    g.linearIndependent.map' (X.Λ.toAddSubgroup.subtype.toIntLinearMap)
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp hZ

noncomputable def qb {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) : Basis ι ℚ (Fin r → E) :=
  Basis.mk (linIndQ X g) (spanQ_eq_top X g).ge

theorem qb_apply {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) (i : ι) : qb X g i = (g i : Fin r → E) := by
  unfold qb
  exact Basis.mk_apply _ _ _

theorem card_qb {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) :
    Fintype.card ι = r * finrank ℚ E := by
  rw [← Module.finrank_eq_card_basis (qb X g), Module.finrank_pi_fintype]
  simp

theorem two_card_Psi : 2 * Fintype.card X.Ψ = finrank ℚ E := by
  classical
  rw [← NumberField.Embeddings.card E ℂ]
  have h1 : (X.Ψᶜ).card = X.Ψ.card := by
    refine Finset.card_bij (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_
    · intro τ hτ
      rw [Finset.mem_compl] at hτ
      exact (X.cmType _).mpr (by rw [TraceIntegralBasis.conj_conj]; exact hτ)
    · intro a _ b _ h
      have := congrArg ComplexEmbedding.conjugate h
      rwa [TraceIntegralBasis.conj_conj, TraceIntegralBasis.conj_conj] at this
    · intro τ hτ
      refine ⟨ComplexEmbedding.conjugate τ, ?_, TraceIntegralBasis.conj_conj τ⟩
      rw [Finset.mem_compl]
      intro h
      exact ((X.cmType _).mp h) (by rw [TraceIntegralBasis.conj_conj]; exact hτ)
  have h2 := Finset.card_add_card_compl X.Ψ
  rw [Fintype.card_coe]
  omega

noncomputable def plc (τ : X.Ψ) : TraceIntegralBasis.CP E :=
  ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩

open scoped Classical in

noncomputable def Tm : TraceIntegralBasis.VS E →ₗ[ℝ] (X.Ψ → ℂ) where
  toFun z τ := if (plc X τ).1.embedding = τ.1 then z (plc X τ) else conj (z (plc X τ))
  map_add' z z' := by
    funext τ
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul]

open scoped Classical in
theorem Tm_iota (x : E) (τ : X.Ψ) : Tm X (TraceIntegralBasis.iota E x) τ = τ.1 x := by
  simp only [Tm, LinearMap.coe_mk, AddHom.coe_mk, TraceIntegralBasis.iota_apply]
  split_ifs with h
  · rw [h]
  · rcases InfinitePlace.embedding_mk_eq τ.1 with h' | h'
    · exact absurd h' h
    · change conj ((InfinitePlace.mk τ.1).embedding x) = τ.1 x
      rw [h', ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

open scoped Classical in
theorem Tm_injective : Function.Injective (Tm X) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  ext w
  obtain ⟨τ, hτ⟩ : ∃ τ : X.Ψ, plc X τ = w := by
    by_cases h : w.1.embedding ∈ X.Ψ
    · exact ⟨⟨_, h⟩, Subtype.ext (InfinitePlace.mk_embedding w.1)⟩
    · have h2 : ComplexEmbedding.conjugate w.1.embedding ∈ X.Ψ :=
        (X.cmType _).mpr (by rw [TraceIntegralBasis.conj_conj]; exact h)
      exact ⟨⟨_, h2⟩, Subtype.ext ((InfinitePlace.mk_conjugate_eq _).trans
        (InfinitePlace.mk_embedding w.1))⟩
  have h3 := congrFun hz τ
  simp only [Tm, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h3
  subst hτ
  split_ifs at h3
  · simpa using h3
  · simpa using h3

theorem finrank_Psi : finrank ℝ (X.Ψ → ℂ) = finrank ℚ E := by
  rw [Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← two_card_Psi X]
  ring

theorem span_real_embeddings_eq_top : span ℝ (Set.range fun x : E => fun τ : X.Ψ => τ.1 x) = ⊤ := by
  have hs : span ℝ (Set.range (TraceIntegralBasis.iota E)) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← (TraceIntegralBasis.bas E).span_eq]
    exact span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨_, (TraceIntegralBasis.bas_apply i).symm⟩)
  have hdim : finrank ℝ (TraceIntegralBasis.VS E) = finrank ℝ (X.Ψ → ℂ) := by
    rw [TraceIntegralBasis.finrank_VS, finrank_Psi]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (Tm_injective X)
  rw [eq_top_iff]
  intro z _
  obtain ⟨y, rfl⟩ := hsurj z
  have hy : y ∈ span ℝ (Set.range (TraceIntegralBasis.iota E)) := by rw [hs]; trivial
  have h1 := Submodule.mem_map_of_mem (f := Tm X) hy
  rw [Submodule.map_span] at h1
  refine span_mono ?_ h1
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨x, funext fun τ => (Tm_iota X x τ).symm⟩

noncomputable def Ja (a : Fin r) : (X.Ψ → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun z τ b := if b = a then z τ else 0
  map_add' z z' := by
    funext τ b
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    funext τ b
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

theorem span_embV {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) :
    span ℝ (Set.range fun i => X.embV (g i : Fin r → E)) = ⊤ := by
  set S := span ℝ (Set.range fun i => X.embV (g i : Fin r → E)) with hS
  have h1 : ∀ v : Fin r → E, X.embV v ∈ S := by
    intro v
    have hv : X.embV v = ∑ i, (((qb X g).repr v i : ℚ) : ℝ) • X.embV (g i : Fin r → E) := by
      conv_lhs => rw [← (qb X g).sum_repr v]
      funext τ a
      simp only [Data.embV, Data.emb, qb_apply, Finset.sum_apply, Pi.smul_apply, Rat.smul_def,
        map_sum, map_mul, map_ratCast, Complex.real_smul, Complex.ofReal_ratCast]
    rw [hv]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩)
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ a : Fin r, Ja X a (fun τ => w τ a) := by
    funext τ b
    simp [Ja, Finset.sum_apply]
  rw [hw]
  refine Submodule.sum_mem _ fun a _ => ?_
  have hz : (fun τ : X.Ψ => w τ a) ∈ span ℝ (Set.range fun x : E => fun τ : X.Ψ => τ.1 x) := by
    rw [span_real_embeddings_eq_top]; trivial
  have h2 := Submodule.mem_map_of_mem (f := Ja X a) hz
  rw [Submodule.map_span] at h2
  refine (span_le.mpr ?_) h2
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  have h3 : Ja X a (fun τ : X.Ψ => τ.1 x) = X.embV (Pi.single a x) := by
    funext τ b
    simp only [Ja, LinearMap.coe_mk, AddHom.coe_mk, Data.embV, Data.emb, Pi.single_apply]
    split_ifs <;> simp
  rw [h3]
  exact h1 _

theorem linIndR {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) :
    LinearIndependent ℝ fun i => X.embV (g i : Fin r → E) := by
  refine linearIndependent_of_top_le_span_of_card_eq_finrank (span_embV X g).ge ?_
  rw [card_qb X g, Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← two_card_Psi X]
  ring

end RealPlaceEmbeddings

end ReciprocityTheory.ChartRestriction.G.FD
