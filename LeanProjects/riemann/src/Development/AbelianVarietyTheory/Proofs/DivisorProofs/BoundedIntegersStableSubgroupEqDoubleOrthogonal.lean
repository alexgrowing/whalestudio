import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

namespace GlobalTheory.LatticeDual

theorem exists_integral_form_separating {R K : Type} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [Field K] [Algebra R K] [IsFractionRing R K] {κ : Type} [Fintype κ]
    (M : Submodule R (κ → K)) (hM : M.FG) (z : K) (hz : z ∉ (algebraMap R K).range)
    (t : κ → K) (ht : t ∉ M) :
    ∃ y : κ → K, (∀ s ∈ M, s ⬝ᵥ y ∈ (algebraMap R K).range) ∧ t ⬝ᵥ y ∉ (algebraMap R K).range := by
  classical
  haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  haveI : Module.Free R M := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R M
  let ι := Module.Free.ChooseBasisIndex R M
  let a : ι → (κ → K) := fun i => (b i : κ → K)
  have hliR : LinearIndependent R a := b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent K a := (LinearIndependent.iff_fractionRing R K).mp hliR
  let B := Module.Basis.sumExtend hli
  have hfin : Finite (ι ⊕ Module.Basis.sumExtendIndex hli) := Module.Finite.finite_basis B
  have : Finite (Module.Basis.sumExtendIndex hli) :=
    Finite.of_injective (Sum.inr : _ → ι ⊕ _) Sum.inr_injective
  have : Fintype (Module.Basis.sumExtendIndex hli) := Fintype.ofFinite _
  have hB : ∀ i, B (Sum.inl i) = a i := by
    intro i
    simp only [B, Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend,
      Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply]
    rfl

  have key : ∀ f : (κ → K) →ₗ[K] K, (∀ i, f (a i) ∈ (algebraMap R K).range) →
      ∀ s ∈ M, f s ∈ (algebraMap R K).range := by
    intro f hf s hs
    have hs' : s = ∑ i, b.repr ⟨s, hs⟩ i • a i := by
      have := congrArg Subtype.val (b.sum_repr ⟨s, hs⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hs', map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [f.map_smul_of_tower]
    obtain ⟨r, hr⟩ := hf i
    exact ⟨b.repr ⟨s, hs⟩ i * r, by rw [map_mul, hr, Algebra.smul_def]⟩

  have dot : ∀ f : (κ → K) →ₗ[K] K, ∃ y : κ → K, ∀ x, x ⬝ᵥ y = f x := by
    intro f
    refine ⟨fun k => f (fun j => if k = j then 1 else 0), fun x => ?_⟩
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    simp [dotProduct, smul_eq_mul]
  suffices h : ∃ f : (κ → K) →ₗ[K] K, (∀ i, f (a i) ∈ (algebraMap R K).range) ∧
      f t ∉ (algebraMap R K).range by
    obtain ⟨f, hf, hft⟩ := h
    obtain ⟨y, hy⟩ := dot f
    exact ⟨y, fun s hs => (hy s).symm ▸ key f hf s hs, (hy t).symm ▸ hft⟩
  by_cases h1 : ∃ i, B.repr t (Sum.inl i) ∉ (algebraMap R K).range
  · obtain ⟨i, hi⟩ := h1
    refine ⟨B.coord (Sum.inl i), fun i' => ?_, by simpa using hi⟩
    rw [← hB, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  by_cases h2 : ∃ j, B.repr t (Sum.inr j) ≠ 0
  · obtain ⟨j, hj⟩ := h2
    refine ⟨(z / B.repr t (Sum.inr j)) • B.coord (Sum.inr j), fun i => ?_, ?_⟩
    · rw [LinearMap.smul_apply, ← hB, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply, if_neg Sum.inl_ne_inr, smul_zero]
      exact ⟨0, map_zero _⟩
    · rw [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul, div_mul_cancel₀ _ hj]
      exact hz
  push_neg at h1 h2
  choose c hc using h1
  exfalso
  apply ht
  have htc : t = ∑ i, c i • a i := by
    conv_lhs => rw [← B.sum_repr t]
    rw [Fintype.sum_sum_type]
    simp [h2, hB, ← hc, algebraMap_smul]
  rw [htc]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2

end GlobalTheory.LatticeDual

namespace GlobalTheory.LatticeDual

theorem mem_of_mem_doubleOrth : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ₀ : AddChar (Fv F v) ℂ),
    (∀ x : Fv F v, (∀ y ∈ HeightOneSpectrum.adicCompletionIntegers F v, ψ₀ (x * y) = 1) ↔ x ∈ HeightOneSpectrum.adicCompletionIntegers F v) →
    ∀ A : AddSubgroup (κ → Fv F v), (∀ c ∈ HeightOneSpectrum.adicCompletionIntegers F v, ∀ t ∈ A, c • t ∈ A) →
    (∃ c : Fv F v, c ≠ 0 ∧ ∀ t ∈ A, ∀ k, c * t k ∈ HeightOneSpectrum.adicCompletionIntegers F v) →
    ∀ t : κ → Fv F v, (∀ y : κ → Fv F v, (∀ s ∈ A, ψ₀ (s ⬝ᵥ y) = 1) → ψ₀ (t ⬝ᵥ y) = 1) → t ∈ A := by
  intro F _ _ v κ _ ψ₀ hψ A hA hbd t ht
  classical
  let O := HeightOneSpectrum.adicCompletionIntegers F v
  have hrange : ∀ x : Fv F v, x ∈ (algebraMap O (Fv F v)).range ↔ x ∈ O :=
    fun x => ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hψO : ∀ x ∈ O, ψ₀ x = 1 := fun x hx => by
    simpa using (hψ 1).mpr (one_mem _) x hx

  let M : Submodule O (κ → Fv F v) :=
    { carrier := A
      add_mem' := fun h h' => A.add_mem h h'
      zero_mem' := A.zero_mem
      smul_mem' := fun c x hx => hA _ c.2 x hx }
  obtain ⟨c, hc0, hc⟩ := hbd

  let N : Submodule O (κ → Fv F v) :=
    Submodule.span O (Set.range fun k : κ => c⁻¹ • (Pi.single k 1 : κ → Fv F v))
  have hN : N.FG := Submodule.fg_span (Set.finite_range _)
  have hMN : M ≤ N := by
    intro s hs
    have hs' : s = ∑ k, (⟨c * s k, hc s hs k⟩ : O) • (c⁻¹ • (Pi.single k 1 : κ → Fv F v)) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
      show s j = c * s j * c⁻¹
      rw [mul_comm c, mul_inv_cancel_right₀ hc0]
    rw [hs']
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hMfg : M.FG := by
    haveI := isNoetherian_of_fg_of_noetherian N hN
    have h1 : (M.comap N.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map N.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hMN] at h2

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : (ϖ : Fv F v) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hz : (ϖ : Fv F v)⁻¹ ∉ (algebraMap O (Fv F v)).range := by
    rw [hrange]
    intro h
    apply hϖ.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, h⟩, Subtype.ext ?_⟩
    simp [hϖ0]
  by_contra htA
  obtain ⟨y', hyA, hyt⟩ := exists_integral_form_separating M hMfg _ hz t htA
  simp only [hrange] at hyA hyt
  obtain ⟨b, hb, hbψ⟩ : ∃ b ∈ O, ψ₀ ((t ⬝ᵥ y') * b) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hyt ((hψ _).mp h)
  apply hbψ
  have := ht (b • y') (fun s hs => by
    rw [dotProduct_smul, smul_eq_mul, mul_comm]
    exact hψO _ (mul_mem (hyA s hs) hb))
  rwa [dotProduct_smul, smul_eq_mul, mul_comm] at this

end GlobalTheory.LatticeDual
