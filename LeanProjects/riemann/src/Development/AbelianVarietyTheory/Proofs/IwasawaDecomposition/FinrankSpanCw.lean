import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.GoodBC

open Module

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {n : ℕ}

def cw (x : Fin n → K) : Fin n → K' := fun k => φ (x k)

def IsBC (V : Submodule K (Fin n → K)) (V' : Submodule K' (Fin n → K')) : Prop :=
  V' = Submodule.span K' (cw φ '' (V : Set (Fin n → K)))

theorem cw_zero : cw φ (0 : Fin n → K) = 0 := by funext k; simp [cw]

theorem cw_add (x y : Fin n → K) : cw φ (x + y) = cw φ x + cw φ y := by funext k; simp [cw]

theorem cw_sub (x y : Fin n → K) : cw φ (x - y) = cw φ x - cw φ y := by funext k; simp [cw]

theorem cw_smul (a : K) (x : Fin n → K) : cw φ (a • x) = φ a • cw φ x := by funext k; simp [cw]

theorem cw_sum {ι : Type} (s : Finset ι) (x : ι → Fin n → K) : cw φ (∑ i ∈ s, x i) = ∑ i ∈ s, cw φ (x i) := by
  funext k; simp [cw, Finset.sum_apply, map_sum]

theorem span_cw_span (X : Set (Fin n → K)) :
    Submodule.span K' (cw φ '' (Submodule.span K X : Set (Fin n → K))) = Submodule.span K' (cw φ '' X) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [cw_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [cw_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [cw_smul]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem finrank_span_cw (V : Submodule K (Fin n → K)) :
    finrank K' (Submodule.span K' (cw φ '' (V : Set (Fin n → K)))) = finrank K V := by
  set b := Module.finBasis K V
  have hV : Submodule.span K (Set.range fun i => (b i : Fin n → K)) = V := by
    have : (Set.range fun i => (b i : Fin n → K)) = V.subtype '' Set.range b := by
      ext y; simp
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hs : Submodule.span K' (cw φ '' (V : Set (Fin n → K))) =
      Submodule.span K' (Set.range fun i => cw φ (b i : Fin n → K)) := by
    conv_lhs => rw [← hV]
    rw [span_cw_span, ← Set.range_comp]
    rfl
  have hli : LinearIndependent K' fun i => cw φ (b i : Fin n → K) := by
    letI := φ.toAlgebra
    have h0 : LinearIndependent K (fun i => (b i : Fin n → K)) := b.linearIndependent.map' V.subtype V.ker_subtype
    exact (linearIndependent_algebraMap_comp_iff).2 h0
  rw [hs, finrank_span_eq_card hli, Fintype.card_fin]

theorem isBC_inf {S T : Submodule K (Fin n → K)} {S' T' : Submodule K' (Fin n → K')} (hS : IsBC φ S S')
    (hT : IsBC φ T T') : IsBC φ (S ⊓ T) (S' ⊓ T') := by
  unfold IsBC at *
  subst hS hT
  have hle : Submodule.span K' (cw φ '' ((S ⊓ T : Submodule K (Fin n → K)) : Set (Fin n → K))) ≤
      Submodule.span K' (cw φ '' (S : Set (Fin n → K))) ⊓ Submodule.span K' (cw φ '' (T : Set (Fin n → K))) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨Submodule.subset_span ⟨x, hx.1, rfl⟩, Submodule.subset_span ⟨x, hx.2, rfl⟩⟩
  have hST : S ⊔ T = Submodule.span K ((S : Set (Fin n → K)) ∪ T) := by
    rw [Submodule.span_union, Submodule.span_eq, Submodule.span_eq]
  have hsup : Submodule.span K' (cw φ '' (S : Set (Fin n → K))) ⊔ Submodule.span K' (cw φ '' (T : Set (Fin n → K))) =
      Submodule.span K' (cw φ '' ((S ⊔ T : Submodule K (Fin n → K)) : Set (Fin n → K))) := by
    rw [hST, span_cw_span, Set.image_union, Submodule.span_union]
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq S T
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K' (cw φ '' (S : Set (Fin n → K))))
    (Submodule.span K' (cw φ '' (T : Set (Fin n → K))))
  rw [hsup] at h2
  simp only [finrank_span_cw] at h2
  rw [finrank_span_cw]
  omega

theorem isBC_range (f : (Fin n → K) →ₗ[K] (Fin n → K)) (f' : (Fin n → K') →ₗ[K'] (Fin n → K'))
    (h : ∀ x, f' (cw φ x) = cw φ (f x)) : IsBC φ (LinearMap.range f) (LinearMap.range f') := by
  unfold IsBC
  apply le_antisymm
  · rintro _ ⟨x', rfl⟩
    have hx : x' = ∑ i, x' i • cw φ (Pi.single i (1 : K)) := by
      conv_lhs => rw [pi_eq_sum_univ x']
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      funext j
      by_cases hij : i = j
      · subst hij; simp [cw]
      · simp [cw, hij, Pi.single_apply, Ne.symm hij]
    rw [hx, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul, h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨cw φ x, h x⟩

theorem isBC_ker (f : (Fin n → K) →ₗ[K] (Fin n → K)) (f' : (Fin n → K') →ₗ[K'] (Fin n → K'))
    (h : ∀ x, f' (cw φ x) = cw φ (f x)) : IsBC φ (LinearMap.ker f) (LinearMap.ker f') := by
  unfold IsBC
  have hle : Submodule.span K' (cw φ '' (LinearMap.ker f : Set (Fin n → K))) ≤ LinearMap.ker f' := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    show f' (cw φ x) = 0
    rw [h, LinearMap.mem_ker.1 hx, cw_zero]
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hr := isBC_range φ f f' h
  unfold IsBC at hr
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker f'
  rw [hr, finrank_span_cw] at h2
  rw [finrank_span_cw]
  simp only [Module.finrank_fin_fun] at h1 h2
  omega

theorem isBC_top : IsBC φ (⊤ : Submodule K (Fin n → K)) (⊤ : Submodule K' (Fin n → K')) := by
  have := isBC_ker φ (0 : (Fin n → K) →ₗ[K] (Fin n → K)) 0 (fun x => by simp [cw_zero])
  simpa only [LinearMap.ker_zero] using this

theorem isBC_biInf {ι : Type} (s : Finset ι) (S : ι → Submodule K (Fin n → K)) (S' : ι → Submodule K' (Fin n → K'))
    (h : ∀ i, IsBC φ (S i) (S' i)) : IsBC φ (⨅ i ∈ s, S i) (⨅ i ∈ s, S' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isBC_top φ
  | insert a s _ ih =>
    rw [Finset.iInf_insert, Finset.iInf_insert]
    exact isBC_inf φ (h a) ih

end GlobalTheory.Mem.R3.GoodBC

namespace GlobalTheory.Mem.R3.GoodBC

open Formalism.IndefR.Arith Module

theorem wgood_bc {LL LL' Ks Ks' : Type} [Field LL] [NumberField LL] [Field LL'] [NumberField LL'] [Field Ks] [NumberField Ks]
    [Field Ks'] [NumberField Ks'] [Algebra Ks LL] [Algebra Ks' LL'] {n : ℕ}
    [Module Ks (Fin n → LL)] [IsScalarTower Ks LL (Fin n → LL)] [Module Ks' (Fin n → LL')] [IsScalarTower Ks' LL' (Fin n → LL')]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {W' : (LL' →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)]
    {G0 G0' : Type} [Group G0] [Fintype G0] [Group G0'] [Fintype G0']
    (A : FormsL LL Ks (Fin n → LL) W G0) (A' : FormsL LL' Ks' (Fin n → LL') W' G0') (φ : LL →+* LL') (e : G0 ≃* G0')
    (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) (J0' : Subgroup G0') (lam0' : J0' →* LL'ˣ) (eC' : G0' → LL')
    (hρ : ∀ g x, A'.ρ (e g) (cw φ x) = cw φ (A.ρ g x))
    (hchi : ∀ g, ((A'.chi (e g) : LL'ˣ) : LL') = φ (A.chi g))
    (hJ : ∀ g, e g ∈ J0' ↔ g ∈ J0)
    (hlam : ∀ g (hg : g ∈ J0) (hg' : e g ∈ J0'), ((lam0' ⟨e g, hg'⟩ : LL'ˣ) : LL') = φ (lam0 ⟨g, hg⟩))
    (heC : ∀ g, eC' (e g) = φ (eC g)) :
    A'.Wgood J0' lam0' eC' = Submodule.span LL' (cw φ '' (A.Wgood J0 lam0 eC : Set (Fin n → LL))) := by
  classical

  have hT : A.typeP J0 lam0 = ⨅ p ∈ (Finset.univ : Finset J0),
      LinearMap.ker (A.ρ p - ((A.chi p * lam0 p : LLˣ) : LL) • LinearMap.id) := by
    ext x
    simp only [Finset.mem_univ, iInf_pos, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hT' : A'.typeP J0' lam0' = ⨅ p ∈ (Finset.univ : Finset J0),
      LinearMap.ker (A'.ρ (e p) - ((A'.chi (e p) * lam0' ⟨e p, (hJ p).2 p.2⟩ : LL'ˣ) : LL') • LinearMap.id) := by
    ext x
    simp only [Finset.mem_univ, iInf_pos, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    constructor
    · intro h p
      exact h ⟨e p, (hJ p).2 p.2⟩
    · intro h p'
      obtain ⟨g, hg⟩ := e.surjective p'
      have hm : g ∈ J0 := (hJ g).1 (hg ▸ p'.2)
      have := h ⟨g, hm⟩
      have hp : p' = ⟨e g, (hJ g).2 hm⟩ := Subtype.ext hg.symm
      subst hp
      exact this
  have hTy : IsBC φ (A.typeP J0 lam0) (A'.typeP J0' lam0') := by
    rw [hT, hT']
    refine isBC_biInf φ _ _ _ fun p => isBC_ker φ _ _ fun x => ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hρ, cw_sub, cw_smul, Units.val_mul, Units.val_mul, map_mul, hchi, hlam p p.2]
  have hE : ∀ x, A'.eOp eC' (cw φ x) = cw φ (A.eOp eC x) := by
    intro x
    unfold FormsL.eOp
    rw [← Equiv.sum_comp e.toEquiv]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    rw [cw_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hρ, cw_smul, map_mul, heC, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, hchi]
  have hG : IsBC φ (A.good eC) (A'.good eC') := isBC_range φ _ _ hE
  exact isBC_inf φ hTy hG

end GlobalTheory.Mem.R3.GoodBC

namespace GlobalTheory.Mem.R3.GoodBC

open Formalism.IndefR.Arith Module

theorem wgood_bc_rel {LL LL' Ks Ks' : Type} [Field LL] [NumberField LL] [Field LL'] [NumberField LL'] [Field Ks] [NumberField Ks]
    [Field Ks'] [NumberField Ks'] [Algebra Ks LL] [Algebra Ks' LL'] {n n' : ℕ} (hn : n = n')
    [Module Ks (Fin n → LL)] [IsScalarTower Ks LL (Fin n → LL)] [Module Ks' (Fin n' → LL')] [IsScalarTower Ks' LL' (Fin n' → LL')]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {W' : (LL' →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)]
    {G0 G0' : Type} [Group G0] [Fintype G0] [Group G0'] [Fintype G0']
    (A : FormsL LL Ks (Fin n → LL) W G0) (A' : FormsL LL' Ks' (Fin n' → LL') W' G0') (φ : LL →+* LL') (e : G0 ≃* G0')
    (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) (J0' : Subgroup G0') (lam0' : J0' →* LL'ˣ) (eC' : G0' → LL')
    (hρ : ∀ g (x : Fin n → LL) (x' : Fin n' → LL'), (∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)) →
      ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → A'.ρ (e g) x' k' = φ (A.ρ g x k))
    (hchi : ∀ g, ((A'.chi (e g) : LL'ˣ) : LL') = φ (A.chi g))
    (hJ : ∀ g, e g ∈ J0' ↔ g ∈ J0)
    (hlam : ∀ g (hg : g ∈ J0) (hg' : e g ∈ J0'), ((lam0' ⟨e g, hg'⟩ : LL'ˣ) : LL') = φ (lam0 ⟨g, hg⟩))
    (heC : ∀ g, eC' (e g) = φ (eC g)) :
    A'.Wgood J0' lam0' eC' = Submodule.span LL' {x' | ∃ x ∈ A.Wgood J0 lam0 eC,
      ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)} := by
  subst hn
  have hS : {x' : Fin n → LL' | ∃ x ∈ A.Wgood J0 lam0 eC, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} =
      cw φ '' (A.Wgood J0 lam0 eC : Set (Fin n → LL)) := by
    ext x'
    constructor
    · rintro ⟨x, hx, h⟩
      exact ⟨x, hx, funext fun k => (h k k rfl).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, fun k k' hk => by rw [Fin.ext hk]; rfl⟩
  rw [hS]
  refine wgood_bc A A' φ e J0 lam0 eC J0' lam0' eC' (fun g x => ?_) hchi hJ hlam heC
  funext k
  exact hρ g x (cw φ x) (fun k k' hk => by rw [Fin.ext hk]; rfl) k k rfl

end GlobalTheory.Mem.R3.GoodBC

namespace GlobalTheory.Mem.R3.GoodBC

theorem gc_iso (B B' : Base) (h : B'.toPre = B.toPre) (px : PreX B.toPre) (px' : PreX B'.toPre) (hp : HEq px' px) :
    ∃ e : Gc B px ≃* Gc B' px', ∀ g, HEq (e g) g := by
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  dsimp only at h px px' hp
  subst h
  cases hp
  exact ⟨MulEquiv.refl _, fun g => HEq.rfl⟩

theorem nat_heq_app {m m' : ℕ} (hm : m' = m) (f : Fin m → ℕ) (f' : Fin m' → ℕ) (h : HEq f' f) (i : Fin m) (i' : Fin m')
    (hi : (i : ℕ) = i') : f' i' = f i := by
  subst hm
  cases h
  rw [Fin.ext hi]

end GlobalTheory.Mem.R3.GoodBC
