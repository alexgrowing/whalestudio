import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenConnectedComponentOfOneInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Filter Topology

namespace GlobalTheory.NormSign

open scoped Classical

theorem ext_algebraMap {K : Type} [Field K] [NumberField K] (v : InfinitePlace K) (x : K) :
    InfinitePlace.Completion.extensionEmbedding v (algebraMap K v.Completion x) = v.embedding x :=
  InfinitePlace.Completion.extensionEmbedding_coe v ((WithAbs.equiv v.1).symm x)

theorem tendsto_completion_iff {K : Type} [Field K] [NumberField K] (v : InfinitePlace K) {α : Type}
    {l : Filter α} (f : α → K) (c : v.Completion) :
    Tendsto (fun x => algebraMap K v.Completion (f x)) l (𝓝 c) ↔
      Tendsto (fun x => v.embedding (f x)) l (𝓝 (InfinitePlace.Completion.extensionEmbedding v c)) := by
  rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.isInducing.tendsto_nhds_iff]
  exact iff_of_eq (congrArg (fun g => Tendsto g l _) (funext fun x => ext_algebraMap v (f x)))

theorem mk_eq_mk_iff_of_isReal {K : Type} [Field K] [NumberField K] {j σ : K →+* ℂ}
    (hj : ComplexEmbedding.IsReal j) : InfinitePlace.mk σ = InfinitePlace.mk j ↔ σ = j := by
  rw [InfinitePlace.mk_eq_iff]
  refine ⟨fun h => h.elim id fun h => ?_, Or.inl⟩
  have e : ComplexEmbedding.conjugate j = j := ComplexEmbedding.isReal_iff.mp hj
  ext x
  have h1 := RingHom.congr_fun h x
  have h2 := RingHom.congr_fun e x
  rw [ComplexEmbedding.conjugate_coe_eq] at h1 h2
  calc σ x = starRingEnd ℂ (j x) := by rw [← h1, Complex.conj_conj]
    _ = j x := h2

theorem tendsto_embedding {K : Type} [Field K] [NumberField K] {j : K →+* ℂ} (hj : ComplexEmbedding.IsReal j)
    {l : Filter K}
    (hl : ∀ u : InfinitePlace K, Tendsto (fun x => algebraMap K u.Completion x) l
      (𝓝 (if u = InfinitePlace.mk j then -1 else 1))) (σ : K →+* ℂ) :
    Tendsto (fun x => σ x) l (𝓝 (if σ = j then -1 else 1)) := by
  have h := (tendsto_completion_iff (InfinitePlace.mk σ) id _).1 (hl (InfinitePlace.mk σ))
  have hc : InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ)
      (if InfinitePlace.mk σ = InfinitePlace.mk j then -1 else 1) = if σ = j then -1 else 1 := by
    by_cases hσ : σ = j
    · subst hσ; simp
    · rw [if_neg (fun e => hσ ((mk_eq_mk_iff_of_isReal hj).1 e)), if_neg hσ, map_one]
  rw [hc] at h
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rw [e] at h; exact h
  · rw [e] at h
    have h' := (Complex.continuous_conj.tendsto _).comp h
    have hs : starRingEnd ℂ (if σ = j then -1 else 1) = if σ = j then -1 else 1 := by
      split_ifs <;> simp
    rw [hs] at h'
    refine h'.congr fun x => ?_
    simp [ComplexEmbedding.conjugate_coe_eq]

theorem tendsto_norm {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    {j : K →+* ℂ} (hj : ComplexEmbedding.IsReal j) {l : Filter K}
    (hσ : ∀ σ : K →+* ℂ, Tendsto (fun x => σ x) l (𝓝 (if σ = j then -1 else 1))) (u : InfinitePlace E) :
    Tendsto (fun x => u.embedding (Algebra.norm E x)) l
      (𝓝 (if u = InfinitePlace.mk (j.comp (algebraMap E K)) then -1 else 1)) := by
  letI : Algebra E ℂ := u.embedding.toAlgebra
  have hn : ∀ x : K, u.embedding (Algebra.norm E x) = ∏ σ : K →ₐ[E] ℂ, σ x :=
    fun x => Algebra.norm_eq_prod_embeddings E ℂ x
  simp_rw [hn]
  have hlim : Tendsto (fun x => ∏ σ : K →ₐ[E] ℂ, σ x) l
      (𝓝 (∏ σ : K →ₐ[E] ℂ, if (σ : K →+* ℂ) = j then (-1 : ℂ) else 1)) :=
    tendsto_finset_prod _ fun σ _ => hσ (σ : K →+* ℂ)
  convert hlim using 2
  by_cases hu : u = InfinitePlace.mk (j.comp (algebraMap E K))
  · have he : u.embedding = j.comp (algebraMap E K) := by
      rw [hu]; exact InfinitePlace.embedding_mk_eq_of_isReal (hj.comp _)
    let σ₀ : K →ₐ[E] ℂ := { toRingHom := j, commutes' := fun e => (RingHom.congr_fun he e).symm }
    have hiff : ∀ σ : K →ₐ[E] ℂ, (σ : K →+* ℂ) = j ↔ σ = σ₀ := fun σ =>
      ⟨fun h => AlgHom.coe_ringHom_injective h, fun h => by rw [h]; rfl⟩
    rw [if_pos hu, Finset.prod_congr rfl fun σ _ => if_congr (hiff σ) rfl rfl]
    simp
  · rw [if_neg hu]
    refine (Finset.prod_eq_one fun σ _ => if_neg fun h => hu ?_).symm
    have he : u.embedding = j.comp (algebraMap E K) := by
      ext e
      have := σ.commutes e
      rw [← h]
      exact this.symm
    rw [← he, InfinitePlace.mk_embedding]

end GlobalTheory.NormSign

namespace GlobalTheory.NormSign

open scoped Classical

theorem exists_norm_sign : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (j : K →+* ℂ), NumberField.ComplexEmbedding.IsReal j → ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (M : ℕ) (W : Set (Ideles E)), W ∈ nhds (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E (InfinitePlace.mk (j.comp (algebraMap E K))) (-1)) → ∃ a : Kˣ, (∀ w ∈ T, w.valuation K ((a : K) - 1) ≤ WithZero.exp (-(M : ℤ))) ∧ Units.map (ReciprocityTheory.Neutral.Bridge.HCFR.infPart E) (diagUnits E (Units.map (Algebra.norm E (S := K)) a)) ∈ W := by
  intro E K _ _ _ _ _ j hj T M W hW
  set w₀ := InfinitePlace.mk (j.comp (algebraMap E K)) with hw₀

  let y : GlobalTheory.FrobDense.Loc T := (fun u => if u = InfinitePlace.mk j then -1 else 1, fun _ => 1)
  let f : K → GlobalTheory.FrobDense.Loc T := fun x => GlobalTheory.FrobDense.proj T (algebraMap K (AdeleRing (𝓞 K) K) x)
  let l : Filter K := comap f (𝓝 y)
  haveI : l.NeBot := comap_neBot_iff.2 fun t ht => by
    obtain ⟨_, hz, a, rfl⟩ := mem_closure_iff_nhds.1 (GlobalTheory.FrobDense.denseRange_proj T y) t ht
    exact ⟨a, hz⟩
  have hf : Tendsto f l (𝓝 y) := tendsto_comap
  have hinf : ∀ u : InfinitePlace K, Tendsto (fun x => algebraMap K u.Completion x) l
      (𝓝 (if u = InfinitePlace.mk j then -1 else 1)) := fun u =>
    (((continuous_apply u).comp continuous_fst).tendsto y).comp hf
  have hfin : ∀ v : T, Tendsto (fun x => algebraMap K (v.1.adicCompletion K) x) l (𝓝 1) := fun v =>
    (((continuous_apply v).comp continuous_snd).tendsto y).comp hf
  have hσ := tendsto_embedding hj hinf

  have h0 : ∀ᶠ x in l, x ≠ 0 := by
    have hj' := hσ j
    rw [if_pos rfl] at hj'
    filter_upwards [hj'.eventually_ne (by norm_num : (-1 : ℂ) ≠ 0)] with x hx e
    exact hx (by rw [e, map_zero])

  have h1 : ∀ᶠ x in l, ∀ v : T, v.1.valuation K (x - 1) ≤ WithZero.exp (-(M : ℤ)) := by
    rw [eventually_all]
    intro v
    have ho : IsOpen {z : v.1.adicCompletion K | Valued.v (z - 1) ≤ WithZero.exp (-(M : ℤ))} :=
      (GlobalTheory.Mem.UnitOpen.isOpen_val_le v.1 (-(M : ℤ))).preimage (continuous_sub_right 1)
    have hm : (1 : v.1.adicCompletion K) ∈ {z : v.1.adicCompletion K | Valued.v (z - 1) ≤ WithZero.exp (-(M : ℤ))} := by
      show Valued.v ((1 : v.1.adicCompletion K) - 1) ≤ _
      rw [sub_self, map_zero]
      exact zero_le'
    filter_upwards [hfin v (ho.mem_nhds hm)] with x hx
    have e : Valued.v (algebraMap K (v.1.adicCompletion K) x - 1) = v.1.valuation K (x - 1) := by
      rw [← map_one (algebraMap K (v.1.adicCompletion K)), ← map_sub]
      exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 (x - 1)
    rw [← e]
    exact hx

  let Φ : (InfiniteAdeleRing E)ˣ →* Ideles E :=
    Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  have hΦ : Continuous Φ := Continuous.units_map _ (continuous_id.prodMk continuous_const)
  let P := ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w₀ (-1)
  let p : (InfiniteAdeleRing E)ˣ := Units.map (MonoidHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) P
  have hP : Φ p = P := Units.ext rfl
  have hpW : Φ ⁻¹' W ∈ 𝓝 p := hΦ.continuousAt.preimage_mem_nhds (by rw [hP]; exact hW)
  rw [(GlobalTheory.HeckeGal.isOpenEmbedding_val_inf E).isInducing.nhds_eq_comap, mem_comap] at hpW
  obtain ⟨U, hU, hUW⟩ := hpW
  have hpu : ∀ u : InfinitePlace E, InfinitePlace.Completion.extensionEmbedding u ((p : InfiniteAdeleRing E) u) =
      if u = w₀ then -1 else 1 := by
    intro u
    by_cases hu : u = w₀
    · subst hu
      rw [if_pos rfl]
      show InfinitePlace.Completion.extensionEmbedding _ ((P : AdeleRing (𝓞 E) E).1 _) = _
      rw [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self]
      simp
    · rw [if_neg hu]
      show InfinitePlace.Completion.extensionEmbedding _ ((P : AdeleRing (𝓞 E) E).1 _) = _
      rw [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_ne E w₀ u hu, map_one]
  have hg : Tendsto (fun x => algebraMap E (InfiniteAdeleRing E) (Algebra.norm E x)) l
      (𝓝 (p : InfiniteAdeleRing E)) := by
    refine tendsto_pi_nhds.2 fun u => ?_
    have := (tendsto_completion_iff u (fun x => Algebra.norm E x) ((p : InfiniteAdeleRing E) u)).2
      (by rw [hpu u]; exact tendsto_norm hj hσ u)
    exact this
  have h2 : ∀ᶠ x in l, algebraMap E (InfiniteAdeleRing E) (Algebra.norm E x) ∈ U := hg hU
  obtain ⟨x, ⟨hx0, hx1⟩, hx2⟩ := ((h0.and h1).and h2).exists
  refine ⟨Units.mk0 x hx0, fun w hw => hx1 ⟨w, hw⟩, ?_⟩
  let q : (InfiniteAdeleRing E)ˣ := Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom
    (Units.map (Algebra.norm E (S := K)) (Units.mk0 x hx0))
  have hq : Units.map (ReciprocityTheory.Neutral.Bridge.HCFR.infPart E)
      (diagUnits E (Units.map (Algebra.norm E (S := K)) (Units.mk0 x hx0))) = Φ q := Units.ext rfl
  rw [hq]
  exact hUW (show (q : InfiniteAdeleRing E) ∈ U from hx2)

end GlobalTheory.NormSign
