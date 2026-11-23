import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationCmExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.FinUniq

theorem rank_SB_le (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (SB X) ≤ Cardinal.aleph0 := by
  classical
  set 𝓑 := TopologicalSpace.countableBasis X
  have hB := TopologicalSpace.isBasis_countableBasis X
  haveI : Countable 𝓑 := (TopologicalSpace.countable_countableBasis X).to_subtype
  set S : Set (X → ℂ) := Set.range fun s : Finset 𝓑 => Set.indicator (⋃ b ∈ s, (b : Set X)) (1 : X → ℂ)
  have hS : S.Countable := Set.countable_range _

  have hco : ∀ U : Set X, IsOpen U → IsCompact U → Set.indicator U (1 : X → ℂ) ∈ S := by
    intro U hU hK
    have hcov : U ⊆ ⋃ i : {b : 𝓑 // (b : Set X) ⊆ U}, (i.1 : Set X) := by
      intro x hx
      obtain ⟨b, hb, hxb, hbU⟩ := hB.exists_subset_of_mem_open hx hU
      exact Set.mem_iUnion.2 ⟨⟨⟨b, hb⟩, hbU⟩, hxb⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : {b : 𝓑 // (b : Set X) ⊆ U} => (i.1 : Set X))
      (fun i => hB.isOpen i.1.2) hcov
    refine ⟨t.image Subtype.val, ?_⟩
    show Set.indicator _ 1 = _
    congr 1
    apply Set.Subset.antisymm
    · intro x hx
      simp only [Set.mem_iUnion, Finset.mem_image] at hx
      obtain ⟨b, ⟨i, -, rfl⟩, hxb⟩ := hx
      exact i.2 hxb
    · intro x hx
      have := ht hx
      simp only [Set.mem_iUnion] at this ⊢
      obtain ⟨i, hi, hxi⟩ := this
      exact ⟨i.1, Finset.mem_image_of_mem _ hi, hxi⟩
  have hle : SB X ≤ Submodule.span ℂ S := by
    intro f hf
    obtain ⟨hlc, hcs⟩ := hf
    have hK : IsCompact (tsupport f) := hcs
    haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hK
    have hfin0 : (Set.range fun x : tsupport f => f x).Finite :=
      (hlc.comp_continuous continuous_subtype_val).range_finite
    have hfin : (Set.range f).Finite := by
      refine (hfin0.insert 0).subset ?_
      rintro _ ⟨x, rfl⟩
      by_cases hx : f x = 0
      · exact Or.inl hx
      · exact Or.inr ⟨⟨x, subset_tsupport _ hx⟩, rfl⟩
    have heq : f = ∑ c ∈ hfin.toFinset.filter (· ≠ 0), c • Set.indicator (f ⁻¹' {c}) (1 : X → ℂ) := by
      funext x
      rw [Finset.sum_apply]
      by_cases hx : f x = 0
      · rw [hx]
        refine (Finset.sum_eq_zero fun c hc => ?_).symm
        have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
        simp [Set.indicator, hx, Ne.symm hc0]
      · rw [Finset.sum_eq_single (f x)]
        · simp [Set.indicator]
        · intro c _ hcx
          simp [Set.indicator, Ne.symm hcx]
        · intro h
          exact absurd (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨x, rfl⟩, hx⟩) h
    rw [heq]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span (hco _ ?_ ?_))
    · exact hlc.isOpen_fiber c
    · have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
      refine hK.of_isClosed_subset (hlc.isClosed_fiber c) ?_
      intro x hx
      exact subset_tsupport _ (by rw [Set.mem_preimage, Set.mem_singleton_iff] at hx; rw [Function.mem_support, hx]; exact hc0)
  calc Module.rank ℂ (SB X) ≤ Module.rank ℂ (Submodule.span ℂ S) := Submodule.rank_mono hle
    _ ≤ Cardinal.mk S := rank_span_le S
    _ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.2 hS.to_subtype

theorem sc_Fv {F : Type} [Field F] [NumberField F] (v : Pl F) : SecondCountableTopology (Fv F v) := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    ⟨_, Set.countable_range _, v.denseRange_algebraMap F⟩
  infer_instance

theorem scalar_of_irred {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V → Prop)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0) (hirr : ∀ N, P N → N = ⊥ ∨ N = ⊤) (T : Module.End ℂ V)
    (hker : ∀ c : ℂ, P (LinearMap.ker (T - c • 1))) (hran : ∀ c : ℂ, P (LinearMap.range (T - c • 1))) :
    ∃ c : ℂ, T = c • 1 := by
  by_contra hne
  push_neg at hne
  have hinj : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.ker_eq_bot]
    rcases hirr _ (hker c) with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp (LinearMap.ker_eq_top.mp h)) (hne c)
  obtain ⟨v₀, hv₀⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h; push_neg at h
    exact hne 0 (LinearMap.ext fun v => (h _).trans (h _).symm)
  have hsurj : ∀ c : ℂ, Function.Surjective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.range_eq_top]
    rcases hirr _ (hran c) with h | h
    · exfalso
      have h1 : (T - c • 1) v₀ ∈ LinearMap.range (T - c • 1) := LinearMap.mem_range_self _ _
      rw [h, Submodule.mem_bot] at h1
      exact hv₀ (hinj c (by rw [h1, map_zero]))
    · exact h
  have hrep : ∀ p : Polynomial ℂ, p ≠ 0 → Function.Injective (Polynomial.aeval T p) := by
    intro p hp
    have hs := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) IsAlgClosed.card_roots_eq_natDegree
    have hlin : ∀ a : ℂ, Polynomial.aeval T (Polynomial.X - Polynomial.C a) = T - a • 1 := by
      intro a; simp [Algebra.algebraMap_eq_smul_one]
    have key : ∀ m : Multiset ℂ,
        Function.Injective (Polynomial.aeval T (m.map fun a => Polynomial.X - Polynomial.C a).prod) := by
      intro m
      induction m using Multiset.induction_on with
      | empty =>
        simp only [Multiset.map_zero, Multiset.prod_zero, map_one, Module.End.one_eq_id, LinearMap.id_coe]
        exact Function.injective_id
      | cons a m ih =>
        rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
        refine Function.Injective.comp ?_ ih
        rw [hlin]; exact hinj a
    rw [← hs, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
    refine Function.Injective.comp ?_ (key _)
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    intro x y hxy
    simp only [LinearMap.smul_apply, Module.End.one_apply] at hxy
    exact smul_right_injective V (Polynomial.leadingCoeff_ne_zero.mpr hp) hxy
  let S : ℂ → V ≃ₗ[ℂ] V := fun c => LinearEquiv.ofBijective (T - c • 1) ⟨hinj c, hsurj c⟩
  let w : ℂ → V := fun c => (S c).symm v₀
  have hw : ∀ c, (T - c • (1 : Module.End ℂ V)) (w c) = v₀ := fun c => (S c).apply_symm_apply v₀
  have hlin : ∀ a : ℂ, Polynomial.aeval T (Polynomial.X - Polynomial.C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have hli : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    let q : ℂ → Polynomial ℂ := fun c => ∏ d ∈ s.erase c, (Polynomial.X - Polynomial.C d)
    have hq : ∀ c ∈ s, Polynomial.aeval T (∏ d ∈ s, (Polynomial.X - Polynomial.C d)) (w c) =
        Polynomial.aeval T (q c) v₀ := by
      intro c hc
      rw [← Finset.mul_prod_erase s _ hc, mul_comm, map_mul, Module.End.mul_apply, hlin, hw]
    have h0 : Polynomial.aeval T (∑ c ∈ s, g c • q c) v₀ = 0 := by
      have h2 := congrArg (Polynomial.aeval T (∏ d ∈ s, (Polynomial.X - Polynomial.C d))) hsum
      rw [map_zero, map_sum] at h2
      rw [map_sum, LinearMap.sum_apply, ← h2]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [LinearMap.map_smul, hq c hc, map_smul, LinearMap.smul_apply]
    have hp0 : ∑ c ∈ s, g c • q c = 0 := by
      by_contra hp
      exact hv₀ (hrep _ hp (by rw [h0, map_zero]))
    have h3 := congrArg (Polynomial.eval i) hp0
    rw [Polynomial.eval_finset_sum, Finset.sum_eq_single i] at h3
    · simp only [Polynomial.eval_smul, q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, smul_eq_mul, Polynomial.eval_zero] at h3
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h
        obtain ⟨d, hd, hd0⟩ := h
        exact (Finset.ne_of_mem_erase hd) (sub_eq_zero.mp hd0).symm
    · intro c hc hci
      simp only [Polynomial.eval_smul, q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, smul_eq_mul]
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hci, hi⟩) (sub_self i), mul_zero]
    · intro h; exact absurd hi h
  have h4 := hli.cardinal_le_rank
  rw [Cardinal.mk_complex] at h4
  exact absurd (h4.trans hrank) (not_le.mpr Cardinal.aleph0_lt_continuum)

theorem exists_equiv_of_ker_eq {M P Q : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Q] [Module ℂ Q] (f : M →ₗ[ℂ] P) (g : M →ₗ[ℂ] Q) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : LinearMap.ker f = LinearMap.ker g) : ∃ e : P ≃ₗ[ℂ] Q, ∀ x, g x = e (f x) := by
  refine ⟨(f.quotKerEquivOfSurjective hf).symm.trans ((Submodule.quotEquivOfEq _ _ h).trans
    (g.quotKerEquivOfSurjective hg)), fun x => ?_⟩
  rw [← LinearMap.quotKerEquivOfSurjective_apply_mk f hf, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

section Ker

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem acts_zero_zero {κ : Type} [Fintype κ] (v : Pl F) (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evFin F v) T (0 : (κ → Fv F v) → ℂ) 0 := by
  intro r _
  have e : tens (evFin F v) (0 : (κ → Fv F v) → ℂ) r = 0 := by funext x; simp [tens]
  rw [e, map_zero]

theorem ker_maximal {n d : ℕ} {Y : Spc F E n} {Z : Spc F E d} (om : Rep σ Y Z) (v : Pl F) {P : Type} [AddCommGroup P]
    [Module ℂ P] [Nontrivial P] (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P)
    (onto : (SB (Fin n × Fin d → Fv F v)).map p = ⊤) (inv : augAt om v ≤ LinearMap.ker p)
    (stab : ∀ h ∈ UAt σ Z (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → p φ = 0 → p φ₁ = 0)
    (irred : ∀ N : Submodule ℂ P, (∀ h ∈ UAt σ Z (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → p φ ∈ N → p φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) :
    Maximal (fun N => GlobalTheory.Published.ThetaSub om v N ∧ N ≠ SB (Fin n × Fin d → Fv F v))
      (LinearMap.ker p ⊓ SB (Fin n × Fin d → Fv F v)) := by
  have haug : augAt om v ≤ SB (Fin n × Fin d → Fv F v) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact sub_mem hφ₁ hφ

  have hfill : ∀ Q : Submodule ℂ _, LinearMap.ker p ⊓ SB (Fin n × Fin d → Fv F v) ≤ Q →
      Q ≤ SB (Fin n × Fin d → Fv F v) → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ ψ ∈ Q, p ψ = p φ → φ ∈ Q := by
    intro Q hNQ hQ φ hφ ψ hψ e
    have h1 : φ - ψ ∈ Q := hNQ ⟨LinearMap.mem_ker.2 (by rw [map_sub, e, sub_self]), sub_mem hφ (hQ hψ)⟩
    simpa using add_mem h1 hψ
  refine ⟨⟨⟨le_inf inv haug, inf_le_right, ?_⟩, ?_⟩, ?_⟩
  · intro h hh φ hφ φ₁ hφ₁ hact
    exact ⟨stab h hh φ hφ.2 φ₁ hφ₁ hact hφ.1, hφ₁⟩
  · intro hN
    obtain ⟨y, hy⟩ := exists_ne (0 : P)
    have hy' : y ∈ (SB (Fin n × Fin d → Fv F v)).map p := by rw [onto]; trivial
    obtain ⟨x, hx, rfl⟩ := hy'
    have : x ∈ LinearMap.ker p ⊓ SB (Fin n × Fin d → Fv F v) := by rw [hN]; exact hx
    exact hy this.1
  · rintro Q ⟨⟨-, hQ, hQs⟩, hQne⟩ hNQ
    rcases irred (Q.map p) (fun h hh φ hφ φ₁ hφ₁ hact hmem => by
      obtain ⟨ψ, hψ, e⟩ := hmem
      exact ⟨φ₁, hQs h hh φ (hfill Q hNQ hQ φ hφ ψ hψ e) φ₁ hφ₁ hact, rfl⟩) with h0 | h1
    · intro x hx
      refine ⟨?_, hQ hx⟩
      have : p x ∈ Q.map p := ⟨x, hx, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact this
    · exfalso
      refine hQne (le_antisymm hQ fun φ hφ => ?_)
      have : p φ ∈ Q.map p := by rw [h1]; trivial
      obtain ⟨ψ, hψ, e⟩ := this
      exact hfill Q hNQ hQ φ hφ ψ hψ e

theorem det_ne_zero_herm {B : Base F E} {n : ℕ} {Y : Spc F E n} {r s : ℕ} (h : Y.IsHerm σ B r s) : Y.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  intro h0
  apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem det_ne_zero_skew {B : Base F E} {n : ℕ} {Y : Spc F E n} {r s : ℕ} (h : Y.IsSkew σ B r s) : Y.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  intro h0
  apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w)
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]

theorem equiv_of_ker_eq' {κ : Type} [TopologicalSpace κ] {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q]
    [Module ℂ Q] (p : (κ → ℂ) →ₗ[ℂ] P) (q : (κ → ℂ) →ₗ[ℂ] Q) (hp : (SB κ).map p = ⊤) (hq : (SB κ).map q = ⊤)
    (h : LinearMap.ker p ⊓ SB κ = LinearMap.ker q ⊓ SB κ) : ∃ e : P ≃ₗ[ℂ] Q, ∀ φ ∈ SB κ, q φ = e (p φ) := by
  have sp : Function.Surjective (p.comp (SB κ).subtype) := fun y => by
    have : y ∈ (SB κ).map p := by rw [hp]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have sq : Function.Surjective (q.comp (SB κ).subtype) := fun y => by
    have : y ∈ (SB κ).map q := by rw [hq]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have hk : LinearMap.ker (p.comp (SB κ).subtype) = LinearMap.ker (q.comp (SB κ).subtype) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype]
    constructor
    · intro e
      have : (x : κ → ℂ) ∈ LinearMap.ker p ⊓ SB κ := ⟨e, x.2⟩
      rw [h] at this
      exact this.1
    · intro e
      have : (x : κ → ℂ) ∈ LinearMap.ker q ⊓ SB κ := ⟨e, x.2⟩
      rw [← h] at this
      exact this.1
  obtain ⟨e, he⟩ := exists_equiv_of_ker_eq _ _ sp sq hk
  exact ⟨e, fun φ hφ => he ⟨φ, hφ⟩⟩

end Ker

section Main

theorem finMaps_unique : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (Rf₃ : FinMaps F a a'), IsFinMaps B (reG G V V' W) X om om' Rf₃ →
    ∀ v : Pl F, ∃ (ψ : Rf.Pi v ≃ₗ[ℂ] Rf₃.Pi v) (l : ℂ), l ≠ 0 ∧ (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf₃.p v φ = ψ (Rf.p v φ)) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf₃.p' v φ = l • ψ (Rf.p' v φ)) ∧ (v ∉ X.T → l = 1) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM V V' W Rf₃ h₃ v
  have hT := hM.triple
  have hf := hM.fin
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hP' := GlobalTheory.ThK.Inhab.pairV' hT
  have hAE := GlobalTheory.ThK.LocalOps.actsEx hK.base
  have h1V : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := fun u _ => by
    show u • ((1 : UA σ G.V.J).1.1 - 1) = 0
    rw [show (1 : UA σ G.V.J).1.1 = 1 from rfl, sub_self, smul_zero]
  have h1V' : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := fun u _ => by
    show u • ((1 : UA σ G.V'.J).1.1 - 1) = 0
    rw [show (1 : UA σ G.V'.J).1.1 = 1 from rfl, sub_self, smul_zero]
  have exV : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ := fun h hh φ hφ => by
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := (hAE F E σ B _ _ _ _ _ _ _ om _ _ _ _ hP v).1 1 h1V h hh φ hφ
    exact ⟨φ₁, h1, h2⟩
  have exV' : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ := fun h hh φ hφ => by
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := (hAE F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hP' v).1 1 h1V' h hh φ hφ
    exact ⟨φ₁, h1, h2⟩

  have props : ∀ Q : FinMaps F a a',
      (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v) = ⊤ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' → Q.p v φ = Q.p' v φ' →
          Q.p v φ₁ = Q.p' v φ₁') →
      (∀ N : Submodule ℂ (Q.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Q.p v φ ∈ N → Q.p v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Q.p v φ = 0 → Q.p v φ₁ = 0) ∧
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, h)) φ φ₁ → Q.p' v φ = 0 → Q.p' v φ₁ = 0) ∧
      (∀ N : Submodule ℂ (Q.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, h)) φ φ₁ → Q.p' v φ ∈ N → Q.p' v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) := by
    intro Q onto' eqv irr
    refine ⟨fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun N hN => irr N ?_⟩
    · rw [eqv h hh φ hφ 0 (zero_mem _) φ₁ hφ₁ 0 (zero_mem _) hact (acts_zero_zero v _) (by rw [e, map_zero]), map_zero]
    · rw [← eqv h hh 0 (zero_mem _) φ hφ 0 (zero_mem _) φ₁ hφ₁ (acts_zero_zero v _) hact (by rw [e, map_zero]), map_zero]
    · intro h hh φ hφ φ₁ hφ₁ hact hmem
      obtain ⟨φ', hφ', e⟩ : ∃ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Q.p' v φ' = Q.p v φ := by
        have : Q.p v φ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v) := by rw [onto']; trivial
        exact this
      obtain ⟨φ₁', hφ₁', hact'⟩ := exV' h hh φ' hφ'
      rw [eqv h hh φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' hact hact' e.symm]
      exact hN h hh φ' hφ' φ₁' hφ₁' hact' (e ▸ hmem)
  obtain ⟨sV, sV', iV'⟩ := props Rf (hf.onto' v) (hf.equiv v) (hf.irred v)
  obtain ⟨tV, tV', jV'⟩ := props Rf₃ (h₃.onto' v) (h₃.equiv v) (h₃.irred v)
  haveI := hf.nontriv v
  haveI := h₃.nontriv v
  have mV := ker_maximal om v (Rf.p v) (hf.onto v) (hf.inv v) sV (hf.irred v)
  have mV₃ := ker_maximal (Y := G.V) (Z := G.W) om v (Rf₃.p v) (h₃.onto v) (h₃.inv v) tV (h₃.irred v)
  have mV' := ker_maximal om' v (Rf.p' v) (hf.onto' v) (hf.inv' v) sV' iV'
  have mV₃' := ker_maximal (Y := G.V') (Z := G.W) om' v (Rf₃.p' v) (h₃.onto' v) (h₃.inv' v) tV' jV'
  have howe := GlobalTheory.T.weil_representation_cm_extension hK.base hK.howeDualityUnitary hK.minguezThetaGL F E σ hT.base.cm
  have eV := howe a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om hT.base.std hP.herm.herm (det_ne_zero_herm hP.herm)
    hP.skew.skew (det_ne_zero_skew hP.skew) hP.resX hP.resW hP.hX hP.hW hP.weil v _ _ mV mV₃
  have eV' := howe a' (a + a') G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' hT.base.std hP'.herm.herm (det_ne_zero_herm hP'.herm)
    hP'.skew.skew (det_ne_zero_skew hP'.skew) hP'.resX hP'.resW hP'.hX hP'.hW hP'.weil v _ _ mV' mV₃'
  obtain ⟨ψ, hψ⟩ := equiv_of_ker_eq' (Rf.p v) (Rf₃.p v) (hf.onto v) (h₃.onto v) eV
  obtain ⟨ψ', hψ'⟩ := equiv_of_ker_eq' (Rf.p' v) (Rf₃.p' v) (hf.onto' v) (h₃.onto' v) eV'
  set T : Module.End ℂ (Rf.Pi v) := ψ.symm.toLinearMap ∘ₗ ψ'.toLinearMap with hTdef
  have hTapp : ∀ x, T x = ψ.symm (ψ' x) := fun x => rfl
  have comm : ∀ h ∈ UAt σ G.W (evFin F v), ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ χ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) χ χ₁ → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ = T (Rf.p v χ) → Rf.p v φ₁ = T (Rf.p v χ₁) := by
    intro h hh χ hχ χ₁ hχ₁ hc φ hφ φ₁ hφ₁ ha e
    obtain ⟨χ', hχ', e1⟩ : ∃ χ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v χ' = Rf.p v χ := by
      have : Rf.p v χ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Rf.p' v) := by rw [hf.onto' v]; trivial
      exact this
    obtain ⟨χ₁', hχ₁', hc'⟩ := exV' h hh χ' hχ'
    have e2 : Rf.p v χ₁ = Rf.p' v χ₁' := hf.equiv v h hh χ hχ χ' hχ' χ₁ hχ₁ χ₁' hχ₁' hc hc' e1.symm
    have e3 : Rf₃.p v φ = Rf₃.p' v χ' := by
      rw [hψ φ hφ, e, hTapp, ← e1, LinearEquiv.apply_symm_apply, ← hψ' χ' hχ']
    have e4 : Rf₃.p v φ₁ = Rf₃.p' v χ₁' := h₃.equiv v h hh φ hφ χ' hχ' φ₁ hφ₁ χ₁' hχ₁' ha hc' e3
    rw [hTapp, e2, ← hψ' χ₁' hχ₁', ← e4, hψ φ₁ hφ₁, LinearEquiv.symm_apply_apply]
  have hrank : Module.rank ℂ (Rf.Pi v) ≤ Cardinal.aleph0 := by
    haveI := sc_Fv v
    have sp : Function.Surjective ((Rf.p v).comp (SB (Fin a × Fin (a + a') → Fv F v)).subtype) := fun y => by
      have : y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) := by rw [hf.onto v]; trivial
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨⟨x, hx⟩, rfl⟩
    exact (LinearMap.rank_le_of_surjective _ sp).trans (rank_SB_le _)
  have hker : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.ker (T - c • 1) →
        Rf.p v φ₁ ∈ LinearMap.ker (T - c • 1) := by
    intro c h hh φ hφ φ₁ hφ₁ hact hmem
    rw [LinearMap.mem_ker] at hmem ⊢
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hmem ⊢
    have hsc := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hφ hact hact c 0
    rw [zero_smul, zero_smul, add_zero, add_zero] at hsc
    have e : Rf.p v (c • φ) = T (Rf.p v φ) := by rw [map_smul, hmem]
    have := comm h hh φ hφ φ₁ hφ₁ hact (c • φ) ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ) (c • φ₁)
      ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ₁) hsc e
    rw [← this, map_smul]
  have hran : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.range (T - c • 1) →
        Rf.p v φ₁ ∈ LinearMap.range (T - c • 1) := by
    intro c h hh φ hφ φ₁ hφ₁ hact hmem
    obtain ⟨y, hy⟩ := hmem
    obtain ⟨χ, hχ, rfl⟩ : ∃ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v χ = y := by
      have : y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) := by rw [hf.onto v]; trivial
      exact this
    obtain ⟨χ₁, hχ₁, hc⟩ := exV h hh χ hχ
    have hsum := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hχ hact hc 1 c
    rw [one_smul, one_smul] at hsum
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hy
    have e : Rf.p v (φ + c • χ) = T (Rf.p v χ) := by
      rw [map_add, map_smul, ← hy]; abel
    have := comm h hh χ hχ χ₁ hχ₁ hc (φ + c • χ) (add_mem hφ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ)) (φ₁ + c • χ₁)
      (add_mem hφ₁ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ₁)) hsum e
    refine ⟨Rf.p v χ₁, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [← this, map_add, map_smul]; abel
  obtain ⟨l, hl⟩ := scalar_of_irred (fun N => ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ N → Rf.p v φ₁ ∈ N)
    hrank (hf.irred v) T hker hran
  have hTl : ∀ x, ψ' x = l • ψ x := fun x => by
    have := congrArg (fun f : Module.End ℂ (Rf.Pi v) => f x) hl
    simp only [hTapp, LinearMap.smul_apply, Module.End.one_apply] at this
    rw [← map_smul, ← this, LinearEquiv.apply_symm_apply]
  have hl0 : l ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : Rf.Pi v)
    have := hTl x
    rw [zero_smul, LinearEquiv.map_eq_zero_iff] at this
    exact hx this
  refine ⟨ψ, l, hl0, hψ, fun φ hφ => by rw [hψ' φ hφ, hTl], fun hv => ?_⟩
  obtain ⟨s1, s2⟩ := hf.sph v hv
  obtain ⟨s3, -⟩ := h₃.sph v hv
  have hvac := (hT.geo.hM.vac v).1
  have hvac' := (hT.geo.hM'.vac v).1
  change Rf₃.p v (G.M.vac v) = Rf₃.p' v (G.M'.vac v) at s3
  have e1 : Rf₃.p' v (G.M'.vac v) = l • Rf₃.p v (G.M.vac v) := by
    rw [hψ' _ hvac', hTl, ← s1, ← hψ _ hvac]
  have hne : Rf₃.p v (G.M.vac v) ≠ 0 := by
    rw [hψ _ hvac]; exact (LinearEquiv.map_ne_zero_iff ψ).2 s2
  rw [← s3] at e1
  have : (l - 1) • Rf₃.p v (G.M.vac v) = 0 := by rw [sub_smul, one_smul, ← e1, sub_self]
  rcases smul_eq_zero.1 this with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hne

end Main

end GlobalTheory.FinUniq
