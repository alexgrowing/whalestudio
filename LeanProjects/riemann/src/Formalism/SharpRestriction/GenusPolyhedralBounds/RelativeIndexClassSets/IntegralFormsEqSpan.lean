import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SectionMonomialGenerators

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module TensorProduct

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem comap_span_of_subset {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module S M] [Module R M] [SMul R S]
    [IsScalarTower R S M] (p : Submodule S M) (s : Set M) (hs : s ⊆ p) :
    (Submodule.span R s).comap (p.subtype.restrictScalars R) = Submodule.span R ((↑) ⁻¹' s : Set ↥p) := by
  apply Submodule.map_injective_of_injective (f := p.subtype.restrictScalars R) Subtype.val_injective
  rw [Submodule.map_comap_eq, Submodule.map_span]
  have h : (p.subtype.restrictScalars R) '' ((↑) ⁻¹' s : Set ↥p) = s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hs hx⟩, hx, rfl⟩
  rw [h, inf_eq_right, Submodule.span_le]
  intro x hx
  exact ⟨⟨x, hs hx⟩, rfl⟩

theorem mem_span_subtype_iff {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module S M] [Module R M] [SMul R S]
    [IsScalarTower R S M] (p : Submodule S M) (s : Set ↥p) (x : ↥p) :
    x ∈ Submodule.span R s ↔ (x : M) ∈ Submodule.span R ((↑) '' s : Set M) := by
  have h : Submodule.span R ((↑) '' s : Set M) = (Submodule.span R s).map (p.subtype.restrictScalars R) := by
    rw [Submodule.map_span]; rfl
  rw [h]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

theorem isBaseChange_span {K K' V : Type*} [Field K] [Field K'] [Algebra K K'] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (p : Submodule K' (K' ⊗[K] V))
    (hp : p = Submodule.span K' ((fun v => (1 : K') ⊗ₜ[K] v) '' (W : Set V)))
    (f : ↥W →ₗ[K] ↥p) (hf : ∀ w, (f w : K' ⊗[K] V) = (1 : K') ⊗ₜ[K] (w : V)) : IsBaseChange K' f := by
  have hg : ∀ x : K' ⊗[K] ↥W, ((f.liftBaseChange K' x : ↥p) : K' ⊗[K] V) = W.subtype.baseChange K' x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul, Submodule.coe_smul, hf, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
      rfl
    | add x y hx hy => rw [map_add, map_add, Submodule.coe_add, hx, hy]
  have hbij : Function.Bijective (f.liftBaseChange K') := by
    constructor
    · intro x y hxy
      have h1 : W.subtype.baseChange K' x = W.subtype.baseChange K' y := by rw [← hg, ← hg, hxy]
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := K') W.subtype Subtype.val_injective h1
    · rw [← LinearMap.range_eq_top, eq_top_iff]
      rintro ⟨y, hy⟩ -
      have hy' := hy
      rw [hp] at hy'
      induction hy' using Submodule.span_induction with
      | mem y h =>
        obtain ⟨w, hw, rfl⟩ := h
        refine ⟨(1 : K') ⊗ₜ[K] (⟨w, hw⟩ : ↥W), Subtype.ext ?_⟩
        rw [LinearMap.liftBaseChange_tmul, one_smul, hf]
      | zero => exact (LinearMap.range (f.liftBaseChange K')).zero_mem
      | add a b ha hb iha ihb =>
        exact (LinearMap.range (f.liftBaseChange K')).add_mem (iha (hp ▸ ha)) (ihb (hp ▸ hb))
      | smul r a ha ih => exact (LinearMap.range (f.liftBaseChange K')).smul_mem r (ih (hp ▸ ha))
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective (f.liftBaseChange K') hbij) (fun x => by simp)

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (ka : WeightFamilies.Wt D j)

def embV (F : B.Cusp j ka) : ↥(Vw X la N ka) := ⟨emb X la N (X.inc ka F), emb_mem_Vw X la N ka F⟩

theorem coe_embV (F : B.Cusp j ka) : (embV X la N ka F : Rp X la N) = emb X la N (X.inc ka F) := rfl

theorem jW_toW (F : B.Mlat j ka) : jW X la N ka (toW X la ka F) = embV X la N ka F := rfl

theorem inW_loc_eq_span (M : Submodule (𝓞 B.KO) X.Forms) (hM : M ≤ X.Msup ka) :
    T0.inW X ka la (X.loc la M) =
      Submodule.span (X.Ol la) {x : ↥(T0.WL X ka la) | ∃ F ∈ M, (x : X.Vl la) = X.bc la F} := by
  unfold T0.inW PJ.loc
  rw [comap_span_of_subset (R := X.Ol la) (T0.WL X ka la) (X.bc la '' (M : Set X.Forms))]
  · congr 1
    ext x
    constructor
    · rintro ⟨F, hF, h⟩; exact ⟨F, hF, h.symm⟩
    · rintro ⟨F, hF, h⟩; exact ⟨F, hF, h.symm⟩
  · rintro _ ⟨F, hF, rfl⟩
    exact Submodule.subset_span ⟨F, hM hF, rfl⟩

theorem span_jW_inW (M : Submodule (𝓞 B.KO) X.Forms) (hM : M ≤ X.Msup ka) :
    Submodule.span (Op X la N) (jW X la N ka '' (T0.inW X ka la (X.loc la M) : Set ↥(T0.WL X ka la))) =
      Submodule.span (Op X la N) {f : ↥(Vw X la N ka) | ∃ F ∈ M, (f : Rp X la N) = emb X la N F} := by
  rw [inW_loc_eq_span X la ka M hM]
  have h1 : jW X la N ka '' (Submodule.span (X.Ol la) {x : ↥(T0.WL X ka la) | ∃ F ∈ M, (x : X.Vl la) = X.bc la F} :
      Set ↥(T0.WL X ka la)) =
      ((Submodule.span (X.Ol la) {x : ↥(T0.WL X ka la) | ∃ F ∈ M, (x : X.Vl la) = X.bc la F}).map
        ((jW X la N ka).restrictScalars (X.Ol la)) : Set ↥(Vw X la N ka)) := rfl
  rw [h1, Submodule.map_span, Submodule.span_span_of_tower]
  congr 1
  ext f
  constructor
  · rintro ⟨x, ⟨F, hF, hx⟩, rfl⟩
    refine ⟨F, hF, ?_⟩
    show bcV X la N (x : X.Vl la) = _
    rw [hx, emb_eq_bcV]
  · rintro ⟨F, hF, hf⟩
    refine ⟨⟨X.bc la F, Submodule.subset_span ⟨F, hM hF, rfl⟩⟩, ⟨F, hF, rfl⟩, Subtype.ext ?_⟩
    rw [hf, emb_eq_bcV]
    rfl

theorem integralForms_eq_span : M1 X la N ka = Submodule.span (Op X la N) (Set.range fun F : B.Mlat j ka => embV X la N ka F) := by
  unfold M1 T0.MW
  rw [span_jW_inW X la N ka _ le_rfl]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨F, hF, rfl⟩, hf⟩
    exact ⟨⟨F, hF⟩, Subtype.ext hf.symm⟩
  · rintro ⟨F, rfl⟩
    exact ⟨_, ⟨F, F.2, rfl⟩, rfl⟩

theorem Th1_eq (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T : ℕ) (h : X.Theta S ka wL wF T ≤ X.Msup ka) :
    Th1 X la N ka S wL wF T = Submodule.span (Op X la N)
      {f : ↥(Vw X la N ka) | ∃ F ∈ X.Theta S ka wL wF T, (f : Rp X la N) = emb X la N F} :=
  span_jW_inW X la N ka _ h

theorem jW_isBaseChange (hM : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤) :
    IsBaseChange (Kp X la N) (jW X la N ka) := by
  have hp : Vw X la N ka = Submodule.span (Kp X la N) ((fun v => bcV X la N v) '' (T0.WL X ka la : Set (X.Vl la))) := by
    refine le_antisymm ?_ ?_
    · rw [Vw_eq_span_image X la N ka hM]
      refine Submodule.span_mono ?_
      rintro _ ⟨F, hF, rfl⟩
      exact ⟨X.bc la (X.inc ka F), Submodule.subset_span ⟨X.inc ka F, ⟨F, hF, rfl⟩, rfl⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact bcV_mem_Vw X la N ka hx
  exact isBaseChange_span (K := X.Kl la) (K' := Kp X la N) (V := X.Vl la) (T0.WL X ka la) (Vw X la N ka) hp
    (jW X la N ka) (fun w => rfl)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
