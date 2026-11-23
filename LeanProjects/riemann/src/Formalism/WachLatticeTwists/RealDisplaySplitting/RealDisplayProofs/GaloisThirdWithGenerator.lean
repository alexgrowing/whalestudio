import Formalism.WachLatticeTwists.RealDisplaySplitting.GaloisThirdWithGenerator
import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.GaloisTheoremWithGenerator
import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TheoremNFiveRealAllLiftThird

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2 Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG IsCycOn)

set_option maxHeartbeats 8000000 in

theorem realDisplay3_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R') (δ : Tc)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞)
    (h : RealDisplay2 ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ δ t ht bl ρk δO ε gI lhs) :
    RealDisplay3 ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ t ht bl ρk δO ε gI lhs := by
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD _ _ _ _ Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hnlam hseq hwD hliftR hH0 hJC hJR
  have hfin : ∀ w ∈ cols, Module.Finite (FractionRing O) (Hf₂ (conj w)) := by
    intro w hw
    have hr := hRows (conj w) (hrows ▸ Finset.mem_image_of_mem conj hw)
    exact finite_Hf_dec ℓ (Aw (conj w)) hr.1 (Dat (conj w)) ε hO hFr hcyc hr.2.2.1 hr.2.2.2.1 (Hf₂ (conj w))
  exact h ι colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u s₀ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne
    (fun Kc k0 _ _ c φ =>
      colPsi_lc ℓ (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ hO hA hur (fun m => pi_ko_torsion O _ m) _ _ Kc k0 φ)
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC
    (fun w hw => ⟨(hJR w hw).1, (hJR w hw).2.1, hfin w hw, (hJR w hw).2.2⟩)

set_option maxHeartbeats 8000000 in

theorem realDisplayWA3_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R') (δ : Tc)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞)
    (h : RealDisplayWA ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ δ t ht bl ρk δO ε gI lhs) :
    RealDisplayWA3 ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ t ht bl ρk δO ε gI lhs := by
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD _ _ _ _ Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hnlam hseq hwD hliftR hH0 hJC hJR
  have hfin : ∀ w ∈ cols, Module.Finite (FractionRing O) (Hf₂ (conj w)) := by
    intro w hw
    have hr := hRows (conj w) (hrows ▸ Finset.mem_image_of_mem conj hw)
    exact finite_Hf_dec ℓ (Aw (conj w)) hr.1 (Dat (conj w)) ε hO hFr hcyc hr.2.2.1 hr.2.2.2.1 (Hf₂ (conj w))
  exact h ι colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u s₀ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne
    (fun Kc k0 _ _ c φ =>
      colPsi_lc ℓ (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ hO hA hur (fun m => pi_ko_torsion O _ m) _ _ Kc k0 φ)
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC
    (fun w hw => ⟨(hJR w hw).1, (hJR w hw).2.1, hfin w hw, (hJR w hw).2.2⟩)

set_option maxHeartbeats 8000000 in

theorem realDisplayAll3_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R') (δ : Tc)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞)
    (h : RealDisplayAll2 ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ δ t ht bl ρk δO ε gI lhs) :
    RealDisplayAll3 ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ t ht bl ρk δO ε gI lhs := by
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne
  exact h ι colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u s₀ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne
    (fun Kc k0 _ _ c φ =>
      colPsi_lc ℓ (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ hO hA hur (fun m => pi_ko_torsion O _ m) _ _ Kc k0 φ)

set_option maxHeartbeats 8000000 in

theorem realDisplayAllWA3_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R') (δ : Tc)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞)
    (h : RealDisplayAllWA ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ δ t ht bl ρk δO ε gI lhs) :
    RealDisplayAllWA3 ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ t ht bl ρk δO ε gI lhs := by
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne
  exact h ι colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u s₀ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne
    (fun Kc k0 _ _ c φ =>
      colPsi_lc ℓ (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ hO hA hur (fun m => pi_ko_torsion O _ m) _ _ Kc k0 φ)

theorem primOver3_of (ℓ : ℕ) [Fact ℓ.Prime] (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (e : ℕ) {X d : Type}
    [Fintype d] [DecidableEq d] (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω]
    [IsAlgClosure Ek Ω] (T : Subalgebra O (X → O)) (r : (Ω ≃ₐ[Ek] Ω) →* (X → Matrix d d O))
    (π : X) (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1)) (χ₁ ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (g₀ : (Ω ≃ₐ[Ek] Ω))
    (eB e₁ s : X → Matrix d d O) (h : PrimOver ℓ O O' e Ek Ω T r π t ht bl χ₁ ε g₀ eB e₁ s) :
    PrimOver3 ℓ O O' e Ek Ω T r π t ht bl χ₁ ε g₀ eB e₁ s := by
  obtain ⟨D, hD, h1, h2, h3, h4, i1, i2, i3, i4, i5, hall⟩ := h
  refine ⟨D, hD, h1, h2, h3, h4, i1, i2, i3, i4, i5, ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ Z
  obtain ⟨a1, a2, a3, a4⟩ := hall Z
  exact ⟨realDisplay3_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a1,
    realDisplayWA3_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a2,
    realDisplayAll3_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a3,
    realDisplayAllWA3_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a4⟩

theorem galois_theorem_third_form : GaloisTheoremThirdForm := by
  intro ℓ _ O _ _ _ _ X _ T d _ _ Ek Ω _ _ _ _ _ r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  obtain ⟨eB, e₁, s, hAB, hall⟩ := galois_theorem_primitive_data ℓ O X T d Ek Ω r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  exact ⟨eB, e₁, s, hAB, fun O' _ _ _ _ _ _ e he hspl =>
    primOver3_of ℓ O O' e Ek Ω T r π t ht bl χ₁ ε g₀ eB e₁ s (hall O' e he hspl)⟩

theorem galois_third_with_extension : GaloisThirdWithExtension := by
  intro ℓ _ O _ _ _ _ X _ T d _ _ Ek Ω _ _ _ _ _ r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  obtain ⟨eB, e₁, s, hAB, O', i1, i2, i3, i4, i5, i6, e, he, hO⟩ :=
    galois_theorem_with_extension ℓ O X T d Ek Ω r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  exact ⟨eB, e₁, s, hAB, O', i1, i2, i3, i4, i5, i6, e, he,
    primOver3_of ℓ O O' e Ek Ω T r π t ht bl χ₁ ε g₀ eB e₁ s hO⟩

theorem galois_third_with_generator : GaloisThirdWithGenerator := by
  intro ℓ _ O _ _ _ _ X _ T d _ _ Ek Ω _ _ _ _ _ r π t ht bl χ₁ ε g₀ s₀ y hP hA h2 hG3 hg hcyc L ϖ hϖ
  obtain ⟨eB, e₁, s, hAB, O', i1, i2, i3, i4, i5, i6, e, he, hO, hc, hg'⟩ :=
    galois_theorem_with_generator ℓ O X T d Ek Ω r π t ht bl χ₁ ε g₀ s₀ y hP hA h2 hG3 hg hcyc L ϖ hϖ
  exact ⟨eB, e₁, s, hAB, O', i1, i2, i3, i4, i5, i6, e, he,
    primOver3_of ℓ O O' e Ek Ω T r π t ht bl χ₁ ε g₀ eB e₁ s hO, hc, hg'⟩

end Formalism.RepresentationBoundsCohomology.SF
