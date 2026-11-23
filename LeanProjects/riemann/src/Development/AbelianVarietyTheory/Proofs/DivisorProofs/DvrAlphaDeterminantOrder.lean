import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanValuationSubringIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumEigenMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisQuotientLatticeEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrAlphaDeterminantPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerMapsEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankEqFinrankEigenInterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationHerbrandEigenspaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiEigenSublatticeFreeEqDifferentScaledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationOfLsmulShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanOfIsLatticeBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiltrationOfComponentsMemEigenSpanStatement

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.FrameModel Matrix TensorProduct

namespace GlobalTheory.FrameModel

theorem isFiltration_modelLattice_ker : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (Λ : Type) [CommRing Λ] [Finite (Λ →+* O)] (α : Λ) (h N : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) O) (X : Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C)), (∀ l, X * ρ l = ρ' l * X) → (∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ) → (∀ z, (∀ i, z i ∈ (algebraMap O C).range) ↔ ∀ i, ∃ f : Polynomial O, ∀ σ, Φ z σ i = algebraMap O C (f.eval (σ α))) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration (embVal v hv α) (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X))) := by
  intro C _ v O _ _ hv Λ _ _ α h N ρ ρ' X Φ hX hΦ1 hΦ2
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw c hc hcw => ?_⟩
  · obtain ⟨t, -, rfl⟩ := (mem_modelLattice v hv Φ _ _).1 hw
    exact (mem_freeLattice_iff v hv α Φ hΦ2 _).2 ⟨t, rfl⟩
  · obtain ⟨t, ht, rfl⟩ := (mem_modelLattice v hv Φ _ _).1 hw
    refine (mem_modelLattice v hv Φ _ _).2 ⟨ρ α *ᵥ t, ?_, ?_⟩
    · rw [LinearMap.mem_ker, Matrix.toLin'_apply] at ht ⊢
      rw [Matrix.mulVec_mulVec, hX, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_zero]
    · funext s
      rw [← mulVec_incl, hΦ1]
      rfl
  · obtain ⟨t, rfl⟩ := (mem_freeLattice_iff v hv α Φ hΦ2 _).1 hw
    obtain ⟨t', ht', e⟩ := (mem_modelLattice v hv Φ _ _).1 hcw
    refine (mem_modelLattice v hv Φ _ _).2 ⟨t, ?_, rfl⟩
    have hc' : (c : C) ≠ 0 := fun e => hc (Subtype.ext e)
    have e1 : incl C h t' = (c : C) • incl C h t := by
      apply Φ.injective
      rw [e, map_smul]
      rfl
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at ht' ⊢
    have e2 := congrArg (fun y => X.map (algebraMap O C) *ᵥ y) e1
    simp only [Matrix.mulVec_smul, mulVec_incl, ht', map_zero] at e2
    apply incl_injective v hv
    rw [map_zero]
    exact (smul_eq_zero.1 e2.symm).resolve_left hc'

theorem mulVec_eq_zero_iff_mem_filSpace : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (Λ : Type) [CommRing Λ] [Finite (Λ →+* O)] (α : Λ) (h N : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) O) (X : Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C)), (∀ l, X * ρ l = ρ' l * X) → (∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ) → (∀ z, (∀ i, z i ∈ (algebraMap O C).range) ↔ ∀ i, ∃ f : Polynomial O, ∀ σ, Φ z σ i = algebraMap O C (f.eval (σ α))) → Function.Injective (embVal v hv α) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration (embVal v hv α) (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X))) → ∀ y : Fin h → C, (Matrix.toLin' (X.map (algebraMap O C))) y = 0 ↔ ∀ s, Φ y s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X))) s := by
  intro C _ v O _ _ hv Λ _ _ α h N ρ ρ' X Φ hX hΦ1 hΦ2 hinj hfilt y
  classical
  letI : Fintype (Λ →+* O) := Fintype.ofFinite _
  obtain ⟨o, t, ho, ht⟩ := exists_smul_eq_incl v hv y
  have hb : X.map (algebraMap O C) *ᵥ y = 0 ↔ t ∈ LinearMap.ker (Matrix.toLin' X) := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, ← (incl_injective v hv h).eq_iff, ← mulVec_incl, ht,
      map_zero, Matrix.mulVec_smul, smul_eq_zero]
    exact ⟨Or.inr, fun e => e.resolve_left ho⟩
  have hs : ∀ s, Φ (incl C h t) s = algebraMap O C o • Φ y s := fun s => by
    rw [ht, map_smul, Pi.smul_apply]
  rw [Matrix.toLin'_apply, hb]
  constructor
  · intro htk s
    rw [← Submodule.smul_mem_iff _ ho, ← hs]
    exact Submodule.subset_span ⟨_, (mem_modelLattice v hv Φ _ _).2 ⟨t, htk, rfl⟩, rfl⟩
  · intro hy
    have := GlobalTheory.T.mem_filtration_of_components_mem_eigenSpan C v (Λ →+* O) (embVal v hv α) N _ hinj hfilt (Φ (incl C h t))
      ((mem_freeLattice_iff v hv α Φ hΦ2 _).2 ⟨t, rfl⟩)
      (fun s => by rw [hs]; exact Submodule.smul_mem _ _ (hy s))
    obtain ⟨t', ht', e⟩ := (mem_modelLattice v hv Φ _ _).1 this
    rwa [← incl_injective v hv h (Φ.injective e)]

theorem finrank_add_finrank_map_eig : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (Λ : Type) [CommRing Λ] (h N : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C)) (b : (Fin h → C) →ₗ[C] (Fin h → C)) (F : (Λ →+* O) → Submodule C (Fin N → C)), (∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ) → (∀ y, b y = 0 ↔ ∀ s, Φ y s ∈ F s) → ∀ s, Module.finrank C (F s) + Module.finrank C ((eig C ρ s).map b) = N := by
  intro C _ v O _ _ hv Λ _ h N ρ Φ b F hΦ hb s
  let π : eig C ρ s →ₗ[C] (Fin N → C) :=
    ((LinearMap.proj s : ((Λ →+* O) → Fin N → C) →ₗ[C] _) ∘ₗ Φ.toLinearMap) ∘ₗ (eig C ρ s).subtype
  have hπ : Function.Bijective π := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      exact Subtype.ext (eq_zero_of_apply_eq_zero v hv ρ Φ hΦ s x x.2 hx)
    · intro w
      obtain ⟨x, hx, e⟩ := exists_eig_apply_eq v hv ρ Φ hΦ s w
      exact ⟨⟨x, hx⟩, e⟩
  let e := LinearEquiv.ofBijective π hπ
  have h1 := LinearMap.finrank_range_add_finrank_ker (b ∘ₗ (eig C ρ s).subtype)
  have h2 : Module.finrank C (eig C ρ s) = N := by
    rw [e.finrank_eq, Module.finrank_fin_fun]
  have h3 : LinearMap.range (b ∘ₗ (eig C ρ s).subtype) = (eig C ρ s).map b := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have h4 : LinearMap.ker (b ∘ₗ (eig C ρ s).subtype) = (F s).comap e.toLinearMap := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    show b x = 0 ↔ Φ x s ∈ F s
    rw [hb]
    refine ⟨fun H => H s, fun H σ => ?_⟩
    by_cases hσ : σ = s
    · rwa [hσ]
    · rw [(mem_eig_iff_support v hv ρ Φ hΦ s x).1 x.2 σ hσ]
      exact zero_mem _
  have h5 : Module.finrank C ((F s).comap e.toLinearMap) = Module.finrank C (F s) := by
    rw [Submodule.comap_equiv_eq_map_symm]
    exact LinearEquiv.finrank_map_eq _ _
  rw [h2, h3, h4, h5] at h1
  omega

theorem isLatticeBasis_lie : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (Λ : Type) [CommRing Λ] [Finite (Λ →+* O)] (α : Λ) (h N : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) O) (X : Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C)), (∀ l, X * ρ l = ρ' l * X) → (∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ) → (∀ z, (∀ i, z i ∈ (algebraMap O C).range) ↔ ∀ i, ∃ f : Polynomial O, ∀ σ, Φ z σ i = algebraMap O C (f.eval (σ α))) → (∀ y : Fin h → C, (Matrix.toLin' (X.map (algebraMap O C))) y = 0 ↔ ∀ s, Φ y s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X))) s) → ∀ [DecidableEq (Λ →+* O)] (τ : Λ →+* O) (n : ℕ) (y : Fin n → eig C ρ τ), IsBasisOf C ((LinearMap.range (Matrix.toLin' X) ⊓ ⨅ l : Λ, Module.End.eigenspace (Matrix.toLin' (ρ' l)) (τ l)).map (incl C h)) (fun i => (Matrix.toLin' (X.map (algebraMap O C))) (y i)) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis v (fun i => (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X))) τ).mkQ (Φ (y i) τ)) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice (embVal v hv α) N) (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X)))) τ) := by
  intro C _ v O _ _ hv Λ _ _ α h N ρ ρ' X Φ hX hΦ1 hΦ2 hker _ τ n y hy
  set F := GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X))) with hF
  set b := Matrix.toLin' (X.map (algebraMap O C)) with hb
  have hsup := mem_eig_iff_support v hv ρ Φ hΦ1 τ
  let π : (Fin h → C) →ₗ[C] ((Fin N → C) ⧸ F τ) :=
    (F τ).mkQ ∘ₗ (LinearMap.proj τ : ((Λ →+* O) → Fin N → C) →ₗ[C] _) ∘ₗ Φ.toLinearMap
  have hπ : ∀ x, π x = (F τ).mkQ (Φ x τ) := fun _ => rfl
  have hk : ∀ x ∈ eig C ρ τ, (b x = 0 ↔ π x = 0) := by
    intro x hx
    rw [hker, hπ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨fun H => H τ, fun H σ => ?_⟩
    by_cases hσ : σ = τ
    · rwa [hσ]
    · rw [(hsup x).1 hx σ hσ]
      exact zero_mem _
  have hmem : ∀ x ∈ eig C ρ τ, (π x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice (embVal v hv α) N)
      (modelLattice v Φ (LinearMap.ker (Matrix.toLin' X)))) τ ↔
      ∃ t : Fin h → O, b (incl C h t) = b x) := by
    intro x hx
    have key : ∀ t : Fin h → O, b (incl C h t) = b x ↔
        ∀ s, (F s).mkQ (Φ (incl C h t) s) =
          (Pi.single τ (π x) : ∀ s, (Fin N → C) ⧸ F s) s := by
      intro t
      rw [← sub_eq_zero, ← map_sub, hker]
      refine forall_congr' fun s => ?_
      rw [map_sub, Pi.sub_apply]
      by_cases hs : s = τ
      · subst hs
        rw [Pi.single_eq_same, hπ, Submodule.mkQ_apply, Submodule.mkQ_apply,
          Submodule.Quotient.eq]
      · rw [Pi.single_eq_of_ne hs, (hsup x).1 hx s hs, sub_zero, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie
    rw [Submodule.mem_comap, Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, e⟩
      obtain ⟨t, rfl⟩ := (mem_freeLattice_iff v hv α Φ hΦ2 _).1 hw
      exact ⟨t, (key t).2 fun s => congrFun e s⟩
    · rintro ⟨t, ht⟩
      exact ⟨_, (mem_freeLattice_iff v hv α Φ hΦ2 _).2 ⟨t, rfl⟩, funext ((key t).1 ht)⟩
  have hlie : ∀ x ∈ eig C ρ τ, ((∃ t : Fin h → O, b (incl C h t) = b x) ↔
      b x ∈ Submodule.span O (Set.range fun i => b (y i))) := by
    intro x hx
    rw [hy.2, Submodule.mem_map]
    constructor
    · rintro ⟨t, ht⟩
      have ht' : incl C h (X *ᵥ t) = b x := by rw [← ht, hb, Matrix.toLin'_apply, mulVec_incl]
      refine ⟨X *ᵥ t, ⟨⟨t, rfl⟩, ?_⟩, ht'⟩
      rw [SetLike.mem_coe, Submodule.mem_iInf]
      intro l
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      apply incl_injective v hv
      rw [← mulVec_incl, map_smul, ht', hb, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        ← Matrix.map_mul, ← hX, Matrix.map_mul, ← Matrix.mulVec_mulVec,
        (mem_eig_iff ρ τ x).1 hx l, Matrix.mulVec_smul, algebraMap_smul]
    · rintro ⟨_, ⟨⟨t, rfl⟩, -⟩, ht⟩
      exact ⟨t, by rw [← ht, hb, Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_incl]⟩
  have hsum : ∀ g : Fin n → C, ∑ i, g i • (y i : Fin h → C) ∈ eig C ρ τ := fun g =>
    sum_mem fun i _ => Submodule.smul_mem _ _ (y i).2
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    refine Fintype.linearIndependent_iff.1 hy.1 g ?_
    have := (hk _ (hsum g)).2 (by rw [map_sum]; simp only [map_smul]; exact hg)
    rw [map_sum] at this
    simpa only [map_smul] using this
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (hmem _ (y i).2).2 ((hlie _ (y i).2).2 (Submodule.subset_span ⟨i, rfl⟩))
    · intro q hq
      obtain ⟨w, rfl⟩ := (F τ).mkQ_surjective q
      obtain ⟨x, hx, rfl⟩ := exists_eig_apply_eq v hv ρ Φ hΦ1 τ w
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun O).1
        ((hlie x hx).1 ((hmem x hx).1 hq))
      have h0 := (hk _ (sub_mem hx (hsum fun i => algebraMap O C (g i)))).1 (by
        rw [map_sub, map_sum, ← hg, sub_eq_zero]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul, algebraMap_smul])
      rw [map_sub, map_sum, sub_eq_zero] at h0
      rw [← hπ, h0]
      refine sum_mem fun i _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem _ (⟨algebraMap O C (g i),
        (Valuation.mem_valuationSubring_iff _ _).2 (hv.map_le_one _)⟩ : v.valuationSubring)
        (Submodule.subset_span ⟨i, rfl⟩)

theorem det_append_eq_mul_det : ∀ (C : Type) [Field C] (w : Valuation C NNReal) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (Fil : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil → ∀ (x : Fin (p + q) → Fin (p + q) → C) (u : Fin p → Fin (p + q) → C) (m : Fin q → Fin (p + q) → C), GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w x (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) τ) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w (fun i => (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ).mkQ (u i)) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) Fil) τ) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w m (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ) → ∃ c : C, w c = ∏ s ∈ Finset.univ.erase τ, w ((a τ : C) - (a s : C)) ^ (p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s)) ∧ (Matrix.of (Fin.append u m)).det = c * (Matrix.of x).det := by
  intro C _ w ℓ hℓ0 hℓ1 S _ _ a p q Fil τ ha hFil x u m hx hu hm
  set F := GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ with hF
  have hfin : Module.finrank C F = q := by
    have hsp : F = Submodule.span C (Set.range m) := by
      rw [hF, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace, ← hm.2, Submodule.span_span_of_tower]
    rw [hsp, finrank_span_eq_card hm.1, Fintype.card_fin]
  have hd0 : GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr ?_
    exact ha.ne (Finset.ne_of_mem_erase hs).symm
  have h1 := GlobalTheory.T.latticeDetRelation_herbrand_eigenspace C w ℓ hℓ0 hℓ1 S a p q Fil τ ha hFil hfin
  rw [GlobalTheory.T.piEigenSublattice_free_eq_differentScaled C w S a (p + q) τ ha] at h1
  have h2 := GlobalTheory.T.latticeDetRelation_of_lsmul_shift C w ℓ hℓ0 hℓ1 p q _ _ _ _ _ _ hd0 h1
  obtain ⟨x', u', m', c, hx', hu', hm', hmF, ⟨hc0, hcv⟩, hdet⟩ := h2
  obtain ⟨P, hP, hPdet⟩ := GlobalTheory.DetRelCompare.transition x' x _ hx' hx
  obtain ⟨A, hA, hAdet⟩ := GlobalTheory.DetRelCompare.transition _ _ _ hu' hu
  obtain ⟨B, hB, hBdet⟩ := GlobalTheory.DetRelCompare.transition m' m _ hm' hm
  have hx'0 : (Matrix.of x').det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hx'.1)).ne_zero
  have happ0 : (Matrix.of (Fin.append u' m')).det ≠ 0 := by
    intro h0
    exact hx'0 (by rw [hdet, h0, mul_zero])
  have hrel := GlobalTheory.DetRelCompare.det_append_eq F u u' m m' A B hA hB hu'.1 hmF happ0
  have hxP : (Matrix.of x).det = P.det * (Matrix.of x').det := by
    have hmat : Matrix.of x = P * Matrix.of x' := by
      ext i k
      simp [Matrix.mul_apply, hP i, Finset.sum_apply]
    rw [hmat, Matrix.det_mul]
  have hP0 : P.det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hPdet
    exact zero_ne_one hPdet
  refine ⟨A.det * B.det * (P.det * c)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv₀, map_mul, hAdet, hBdet, hPdet, one_mul, one_mul, one_mul]
    have hlam : Real.log (w ℓ : ℝ) ≠ 0 :=
      (Real.log_neg (NNReal.coe_pos.mpr hℓ0) (NNReal.coe_lt_one.mpr hℓ1)).ne
    have hds : ∀ s ∈ Finset.univ.erase τ, ((w ((a τ : C) - (a s : C)) : NNReal) : ℝ) ≠ 0 := by
      intro s hs
      rw [NNReal.coe_ne_zero, Valuation.ne_zero_iff]
      exact sub_ne_zero.mpr (Subtype.coe_injective.ne (ha.ne (Finset.ne_of_mem_erase hs).symm))
    have hdiff : ((GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ : w.valuationSubring) : C)
        = ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) := by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen]
    have hle : ∀ s, Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) ≤ p + q := fun s =>
      (Submodule.finrank_le _).trans_eq (Module.finrank_fin_fun C)
    have hlogc : Real.log (w c : ℝ) = - ∑ s ∈ Finset.univ.erase τ,
        ((p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) : ℕ) : ℝ)
          * Real.log (w ((a τ : C) - (a s : C)) : ℝ) := by
      have e := hcv
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal] at e
      rw [hdiff, map_prod, NNReal.coe_prod, Real.log_prod hds, div_eq_iff hlam] at e
      rw [e, sub_mul, Finset.sum_mul, mul_assoc, div_mul_cancel₀ _ hlam, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Nat.cast_sub (hle s)]
      field_simp
      ring
    have hwc : 0 < ((w c : NNReal) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff w).mpr hc0))
    apply NNReal.coe_injective
    rw [NNReal.coe_inv, NNReal.coe_prod]
    simp only [NNReal.coe_pow]
    have hpos2 : 0 < ∏ s ∈ Finset.univ.erase τ, ((w ((a τ : C) - (a s : C)) : NNReal) : ℝ)
        ^ (p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s)) :=
      Finset.prod_pos fun s hs => pow_pos (lt_of_le_of_ne (NNReal.coe_nonneg _) (hds s hs).symm) _
    rw [← Real.exp_log (inv_pos.mpr hwc), ← Real.exp_log hpos2, Real.log_inv, hlogc, neg_neg,
      Real.log_prod fun s hs => pow_ne_zero _ (hds s hs)]
    simp only [Real.log_pow]
  · rw [hrel, hxP, hdet]
    field_simp

end GlobalTheory.FrameModel

namespace GlobalTheory.FrameModel

section Small

variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]

theorem alternating_apply_eq_det_smul {E W : Type} [AddCommGroup E] [Module C E] [AddCommGroup W]
    [Module C W] {n : ℕ} (f : E [⋀^Fin n]→ₗ[C] W) (e : Module.Basis (Fin n) C E) (z : Fin n → E) :
    f z = e.det z • f e := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff C]
  intro φ
  have := congrArg (fun g => g z) ((φ.compAlternatingMap f).eq_smul_basis_det e)
  simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at this
  rw [map_sub, this, map_smul, smul_eq_mul, mul_comm, sub_self]

theorem isLatticeBasis_map (hv : v.Integers O) {h N n : ℕ} (π : (Fin h → C) →ₗ[C] (Fin N → C))
    (E : Submodule C (Fin h → C)) (hE : ∀ x ∈ E, π x = 0 → x = 0) (y : Fin n → Fin h → C)
    (hy : ∀ i, y i ∈ E) (hli : LinearIndependent C y)
    (L : Submodule v.valuationSubring (Fin N → C))
    (hL : ∀ w, w ∈ L ↔ ∃ x ∈ Submodule.span O (Set.range y), π x = w) :
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis v (fun i => π (y i)) L := by
  constructor
  · refine hli.map (f := π) ?_
    rw [Submodule.disjoint_def]
    intro x hx hx0
    refine hE x ?_ hx0
    exact (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hy i)) hx
  · ext w
    rw [mem_span_valuationSubring_iff v hv, hL]
    have : Set.range (fun i => π (y i)) = (π.restrictScalars O) '' Set.range y := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, Submodule.mem_map]
    rfl

end Small

end GlobalTheory.FrameModel

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.DetInv.span_wedge_lie_fil_eq_smul_detLattice : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (α : Λ), Algebra.adjoin ℤ_[p] {α} = ⊤ → ∀ (a b h : ℕ), h = Module.finrank ℤ_[p] Λ * (a + b) → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) (z : Fin (a + b) → eig C (actH D) τ), IsBasisOf C (lieSub C D τ) (fun i => bC C D (z (Fin.castAdd b i))) → IsBasisOf C (filQuot C D τ) (fun i => (z (Fin.natAdd a i) : Fin h → C)) → ∃ c : C, v c = ∏ᶠ σ : {σ : Λ →+* O // σ ≠ τ}, v (algebraMap O C (τ α) - algebraMap O C (σ.1 α)) ^ D.lieRank σ.1 ∧ (Submodule.span O {exteriorPower.ιMulti C (a + b) z} : Set (detLine C (actH D) τ (a + b))) = (fun w => c • w) '' (detLattice C (actH D) τ (a + b) : Set (detLine C (actH D) τ (a + b))) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ α hα a b h hh D τ z hzL hzF
  classical
  obtain ⟨⟨hindT, -, -⟩, ⟨hindH, htopH, hdimH⟩⟩ :=
    GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ (a + b) h hh D
  obtain ⟨e, hQ, -, -, hdet⟩ :=
    GlobalTheory.T.exists_basis_quotient_lattice_eigen C v O Λ h (a + b) hv (actH D) τ hindH htopH (hdimH τ)
  obtain ⟨Φ, hΦ1, hΦ2⟩ := GlobalTheory.T.dvr_alpha_determinant_property p C v O hv ε hε Λ α hα (a + b) h hh D
  haveI : Finite (Λ →+* O) := (GlobalTheory.T.ring_homs_dvr_card_eq_finrank p C v O hv Λ).1
  letI : Fintype (Λ →+* O) := Fintype.ofFinite _
  have hinj : Function.Injective (embVal v hv α) := by
    intro σ σ' he
    have he' : σ α = σ' α := hv.hom_inj (congrArg Subtype.val he)
    let S : Subalgebra ℤ_[p] Λ :=
      { σ.eqLocus σ' with
        algebraMap_mem' := fun r => by
          show σ (algebraMap ℤ_[p] Λ r) = σ' (algebraMap ℤ_[p] Λ r)
          have h1 := GlobalTheory.T.padic_ring_hom_eq_canonical p O (σ.comp (algebraMap ℤ_[p] Λ))
          have h2 := GlobalTheory.T.padic_ring_hom_eq_canonical p O (σ'.comp (algebraMap ℤ_[p] Λ))
          exact (RingHom.congr_fun h1 r).trans (RingHom.congr_fun h2 r).symm }
    have hle : Algebra.adjoin ℤ_[p] {α} ≤ S := Algebra.adjoin_le (by simpa [S] using he')
    ext x
    have hx : x ∈ Algebra.adjoin ℤ_[p] {α} := hα ▸ Algebra.mem_top
    exact hle hx
  have hint := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
  have hX : ∀ l, D.G.map (WittVector.fontaineTheta O p) * actH D l =
      actT D l * D.G.map (WittVector.fontaineTheta O p) := by
    intro l
    have e' := congrArg (fun M => M.map (WittVector.fontaineTheta O p)) (hint.2.2.1 l)
    simp only [Matrix.map_mul] at e'
    unfold actH actT
    rw [e']
    simp only [rhoTA, Matrix.map_map]
    rfl
  have hfilt : GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration (embVal v hv α) (modelLattice v Φ D.Fil) :=
    isFiltration_modelLattice_ker C v O hv Λ α h (a + b) (actH D) (actT D) _ Φ hX hΦ1 hΦ2
  have hker : ∀ y : Fin h → C, bC C D y = 0 ↔
      ∀ s, Φ y s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace (modelLattice v Φ D.Fil) s :=
    mulVec_eq_zero_iff_mem_filSpace C v O hv Λ α h (a + b) (actH D) (actT D) _ Φ hX hΦ1 hΦ2 hinj hfilt
  have hrank : ∀ s, a + b - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace (modelLattice v Φ D.Fil) s) =
      D.lieRank s := by
    intro s
    have h1 := finrank_add_finrank_map_eig C v O hv Λ h (a + b) (actH D) Φ (bC C D) _ hΦ1 hker s
    have h2 : LinearMap.range (bC C D) ⊓ eig C (actT D) s = (eig C (actH D) s).map (bC C D) :=
      (GlobalTheory.T.intertwiner_maps_eigenspaces C O Λ h (actH D) (actT D)
        (D.G.map (WittVector.fontaineTheta O p)) hX).2 htopH hindT s
    rw [GlobalTheory.T.lie_rank_eq_finrank_eigen_inter p C v O hv ε Λ h D s, h2]
    omega
  have hu := isLatticeBasis_lie C v O hv Λ α h (a + b) (actH D) (actT D) _ Φ hX hΦ1 hΦ2 hker τ a
    (fun i => z (Fin.castAdd b i)) hzL
  let π : (Fin h → C) →ₗ[C] (Fin (a + b) → C) :=
    (LinearMap.proj τ : ((Λ →+* O) → Fin (a + b) → C) →ₗ[C] _) ∘ₗ Φ.toLinearMap
  have hπ : ∀ x, π x = Φ x τ := fun _ => rfl
  have hE : ∀ x ∈ eig C (actH D) τ, π x = 0 → x = 0 :=
    eq_zero_of_apply_eq_zero v hv (actH D) Φ hΦ1 τ
  have hm := isLatticeBasis_map v hv π _ hE (fun i => (z (Fin.natAdd a i) : Fin h → C))
    (fun i => (z _).2) hzF.1
    (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (a + b) → C) (modelLattice v Φ D.Fil) τ) (by
      intro w
      rw [hzF.2]
      unfold GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot filQuot
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨t, ht, rfl⟩ := (mem_modelLattice v hv Φ _ _).1 hy
        obtain ⟨x, hx, hxe⟩ := exists_eig_apply_eq v hv (actH D) Φ hΦ1 τ (Φ (incl C h t) τ)
        exact ⟨x, (mem_eigPart_iff v hv (actH D) Φ hΦ1 τ _ x).2 ⟨hx, t, ht, hxe.symm⟩, hxe⟩
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨-, t, ht, hte⟩ := (mem_eigPart_iff v hv (actH D) Φ hΦ1 τ _ x).1 hx
        exact ⟨_, (mem_modelLattice v hv Φ _ _).2 ⟨t, ht, rfl⟩, hte⟩)
  have hspan : ∀ x : Fin h → C, x ∈ Submodule.span O (Set.range fun i => (e i : Fin h → C)) ↔
      ∃ x' ∈ quotLattice C (actH D) τ, (x' : Fin h → C) = x := by
    intro x
    have : Set.range (fun i => (e i : Fin h → C)) =
        ((eig C (actH D) τ).subtype.restrictScalars O) '' Set.range e := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, Submodule.mem_map, hQ]
    rfl
  have hx := isLatticeBasis_map v hv π _ hE (fun i => (e i : Fin h → C))
    (fun i => (e _).2) (e.linearIndependent.map' _ (Submodule.ker_subtype _))
    (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (a + b) → C)
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice (embVal v hv α) (a + b)) τ) (by
      intro w
      unfold GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨t, rfl⟩ := (mem_freeLattice_iff v hv α Φ hΦ2 _).1 hy
        obtain ⟨x, hx, hxe⟩ := exists_eig_apply_eq v hv (actH D) Φ hΦ1 τ (Φ (incl C h t) τ)
        refine ⟨x, (hspan x).2 ⟨⟨x, hx⟩, ⟨t, ?_⟩, rfl⟩, hxe⟩
        rw [mem_iSup_eig_iff v hv (actH D) Φ hΦ1, map_sub, Pi.sub_apply, sub_eq_zero]
        exact hxe.symm
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨x', ⟨t, ht⟩, rfl⟩ := (hspan x).1 hx
        rw [mem_iSup_eig_iff v hv (actH D) Φ hΦ1, map_sub, Pi.sub_apply, sub_eq_zero] at ht
        exact ⟨_, (mem_freeLattice_iff v hv α Φ hΦ2 _).2 ⟨t, rfl⟩, ht⟩)
  have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hv0 : 0 < v (p : C) := zero_lt_iff.2 ((v.ne_zero_iff).2 hp0)
  have hv1 : v (p : C) < 1 := by
    have hp : algebraMap O C (p : O) = (p : C) := map_natCast _ _
    refine lt_of_le_of_ne (hp ▸ hv.map_le_one _) fun h1 => (Fact.out : ¬IsUnit (p : O)) ?_
    exact hv.isUnit_of_one (hp ▸ hp0.isUnit) (hp ▸ h1)
  obtain ⟨c, hc, hcd⟩ := det_append_eq_mul_det C v (p : C) hv0 hv1 (Λ →+* O) (embVal v hv α) a b
    (modelLattice v Φ D.Fil) τ hinj hfilt _ _ _ hx hu hm
  have hX0 : (Matrix.of fun i => π (e i)).det ≠ 0 := by
    have hu : IsUnit (Matrix.of fun i => π (e i)) :=
      Matrix.linearIndependent_rows_iff_isUnit.1 hx.1
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  have hce : e.det z = c := by
    have h1 := alternating_apply_eq_det_smul
      ((Matrix.detRowAlternating : (Fin (a + b) → C) [⋀^Fin (a + b)]→ₗ[C] C).compLinearMap
        (π ∘ₗ (eig C (actH D) τ).subtype)) e z
    have h2 : (Fin.append (fun i => Φ (z (Fin.castAdd b i)) τ)
        (fun i => π (z (Fin.natAdd a i)))) = fun i => π (z i) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; rfl
      · rw [Fin.append_right]
    rw [h2] at hcd
    apply mul_right_cancel₀ hX0
    rw [← hcd]
    exact h1.symm
  refine ⟨c, ?_, ?_⟩
  · rw [hc, finprod_eq_prod_of_fintype]
    rw [Finset.prod_subtype (p := fun σ : Λ →+* O => σ ≠ τ) (Finset.univ.erase τ) (by simp)]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [hrank]
    rfl
  · rw [hdet, alternating_apply_eq_det_smul _ e z, hce]
    ext w
    simp only [SetLike.mem_coe, Submodule.mem_span_singleton, Set.mem_image]
    constructor
    · rintro ⟨o, rfl⟩
      exact ⟨_, ⟨o, rfl⟩, smul_comm _ _ _⟩
    · rintro ⟨_, ⟨o, rfl⟩, rfl⟩
      exact ⟨o, smul_comm _ _ _⟩
