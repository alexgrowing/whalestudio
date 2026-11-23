import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroSmulMemOfMemSpan

noncomputable section

open NumberField IsDedekindDomain Module

namespace GlobalTheory.GoodLat

section General

variable {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem exists_smul_mem (N : Submodule R V) {x : V} (hx : x ∈ Submodule.span K (N : Set V)) :
    ∃ a : R, a ≠ 0 ∧ a • x ∈ N := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 N x hx; exact @_root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span)
  | exact @_root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span
  | exact _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span
  | (apply _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span ..)

theorem isLattice_comap [IsNoetherianRing R] {U : Type} [AddCommGroup U] [Module K U] [Module R U] [IsScalarTower R K U]
    (N : Submodule R V) (hN : Submodule.IsLattice K N) (f : U →ₗ[K] V) (hf : Function.Injective f) :
    Submodule.IsLattice K (N.comap (f.restrictScalars R)) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (f.restrictScalars R) hf ?_
    exact hN.fg.of_le (Submodule.map_comap_le _ _)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, hax⟩ := exists_smul_mem (K := K) N (x := f x) (hN.span_eq_top ▸ Submodule.mem_top)
    have ha1 : algebraMap R K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ha
    have e : x = (algebraMap R K a)⁻¹ • (a • x) := by
      rw [← algebraMap_smul K a x, smul_smul, inv_mul_cancel₀ ha1, one_smul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    show (f.restrictScalars R) (a • x) ∈ N
    rw [map_smul]
    exact hax

end General

section Forms

open Formalism.IndefR.Arith

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0] [Fintype G0]
variable (A : FormsL LL Ks WL W G0)

omit [Fintype G0] in

theorem isLattice_span_MK (hK : A.IsKsForm) (hM : A.MKFull) :
    Submodule.IsLattice LL (Submodule.span (𝓞 LL) (A.MK : Set WL)) := by
  obtain ⟨⟨s, hs⟩, hsp⟩ := hM
  refine ⟨⟨s, le_antisymm (Submodule.span_mono (hs ▸ Submodule.subset_span)) (Submodule.span_le.2 ?_)⟩, ?_⟩
  · intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => exact Submodule.add_mem _ ihx ihy
    | smul a x _ ih =>
      have e : a • x = (algebraMap (𝓞 Ks) (𝓞 LL) a) • x := by
        rw [← algebraMap_smul Ks a x, ← algebraMap_smul LL (algebraMap (𝓞 Ks) Ks a) x,
          ← algebraMap_smul LL (algebraMap (𝓞 Ks) (𝓞 LL) a) x]
        rfl
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ ih
  · obtain ⟨n, b, hb, -, -, -, h4⟩ := hK
    rw [eq_top_iff, ← h4, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : b i ∈ Submodule.span Ks (A.MK : Set WL) := hsp ▸ hb i
    exact Submodule.span_mono Submodule.subset_span (Submodule.span_le_restrictScalars Ks LL _ h1)

theorem isLattice_Mcoord (hK : A.IsKsForm) (hM : A.MKFull) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL)
    {d : ℕ} (b : Fin d → WL) (hb : LinearIndependent LL b) (hW : ∀ i, b i ∈ A.Wgood J0 lam0 eC) :
    Submodule.IsLattice LL (A.Mcoord J0 lam0 eC b) := by
  have e : A.Mcoord J0 lam0 eC b = (Submodule.span (𝓞 LL) (A.MK : Set WL)).comap
      ((Fintype.linearCombination LL b).restrictScalars (𝓞 LL)) := by
    ext c
    have hc : Fintype.linearCombination LL b c ∈ A.Wgood J0 lam0 eC := by
      rw [Fintype.linearCombination_apply]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hW i)
    exact ⟨fun h => h.1.1, fun h => ⟨⟨h, hc.1⟩, hc.2⟩⟩
  rw [e]
  refine isLattice_comap _ (isLattice_span_MK A hK hM) _ ?_
  refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun c hc => funext ?_)
  exact Fintype.linearIndependent_iff.1 hb c hc

theorem mj_full (hK : A.IsKsForm) (hM : A.MKFull) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) :
    (A.Mj J0 lam0 eC).FG ∧ Submodule.span LL (A.Mj J0 lam0 eC : Set WL) = A.Wgood J0 lam0 eC := by
  have h := isLattice_comap _ (isLattice_span_MK A hK hM) (A.Wgood J0 lam0 eC).subtype Subtype.val_injective
  have e : A.Mj J0 lam0 eC = ((Submodule.span (𝓞 LL) (A.MK : Set WL)).comap
      ((A.Wgood J0 lam0 eC).subtype.restrictScalars (𝓞 LL))).map
        ((A.Wgood J0 lam0 eC).subtype.restrictScalars (𝓞 LL)) := by
    ext x
    exact ⟨fun hx => ⟨⟨x, hx.1.2, hx.2⟩, hx.1.1, rfl⟩, by rintro ⟨y, hy, rfl⟩; exact ⟨⟨hy, y.2.1⟩, y.2.2⟩⟩
  refine ⟨e ▸ h.fg.map _, ?_⟩
  rw [e]
  show Submodule.span LL ((A.Wgood J0 lam0 eC).subtype '' _) = _
  rw [Submodule.span_image, h.span_eq_top, Submodule.map_subtype_top]

end Forms

section Record

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem mLat_of_full {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hK : ∀ i, (R.FW i).IsKsForm) (hM : ∀ i, (R.FW i).MKFull) (b : Bool) : (R.toCx F).MLat b := fun i =>
  isLattice_Mcoord (R.FW i) (hK i) (hM i) _ _ _ (R.bL F b i)
    ((Module.finBasis D.what₂.LL (R.WL F b i)).linearIndependent.map' (R.WL F b i).subtype (Submodule.ker_subtype _))
    fun k => (Module.finBasis D.what₂.LL (R.WL F b i) k).2

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem mkFull_of_tie (t : FWTie T R κ v₀) (hl : LatFull T κ) (i : Fin D.R.m) : (R.FW i).MKFull := by
  refine mkFull_of _ ((R.FW i).WK.subtype ∘ₗ (t.e i).toLinearMap) ?_ (fun x => ?_) (hl i)
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_subtype_top]
  · constructor
    · intro hx
      obtain ⟨f, hf⟩ := (t.e i).surjective ⟨x, hx.1⟩
      have hfx : ((t.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = x := congrArg Subtype.val hf
      have h1 := (t.mem_MK i f).1 (hfx ▸ hx)
      exact ⟨f, fun la v hv => h1 la ⟨v, hv⟩, hfx⟩
    · rintro ⟨f, hf, rfl⟩
      exact (t.mem_MK i f).2 fun la y => hf la y.1 y.2

theorem mLat_of_tie (t : FWTie T R κ v₀) (hl : LatFull T κ) (F : Face D A) (b : Bool) : (R.toCx F).MLat b :=
  mLat_of_full R F t.ks (mkFull_of_tie t hl) b

end Record

end GlobalTheory.GoodLat
