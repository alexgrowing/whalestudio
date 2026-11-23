import Formalism.WachLatticeTwists.RealDisplaySplitting.Statement
import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.TopAllF

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2 Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG IsCycOn)

set_option maxHeartbeats 8000000 in
theorem realDisplay2_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
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
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (q : ℕ) (b : Fin q → (X' → O)) (π' : X')
    (ρπ : R' →ₐ[O] Matrix d d O) (sE : Finset (Ω ≃ₐ[Ek] Ω)) (tE : (Ω ≃ₐ[Ek] Ω) → Tc) (rr : ℕ → Tc) (u₁ : Oˣ)
    (hR : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingTop O X X' T T' p q b d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hF : Formalism.RepresentationBoundsCohomology.ringDataObjects.LocalToDisplayFree O X X' T Z p d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' t ht bl ρk δO)
    (hδ : δ = ∏ i ∈ Finset.Ioo 0 t, (rr 0 - rr i))
    (hδO : δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)))
    (hrr : ∀ (c : Fin (t + 1)) (i : ℕ), i < t → ∀ m : blockRestrictedRepresentationType bl ρk c,
      rr i • m = ((u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)) • m)
    (hba : ∀ c : Fin (t + 1), c ≠ 0 → ∀ g (m : blockRestrictedRepresentationType bl ρk c),
      uElt r χ g • m = ((((ε g) ^ ((c : ℕ) - 1))⁻¹ : Oˣ) : O) • m)
    (hl : lhs = vcc T Z (p π')) :
    RealDisplay2 ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ δ t ht bl ρk δO ε gI lhs := by
  obtain ⟨ha, hb, hc, hEE, hee, hpts, hρπ, hbl, hsurj, hblk, hcard1, hEsum, hE0, hδ0, hτ0, hne, hC0,
    hOne0⟩ := hR
  obtain ⟨p1, p2, p3, -⟩ := hOne0
  subst hl
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD _ _ _ _ Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC hJR
  exact realization_second_form ℓ O X X' T T' Z p q b ha (fun x _ => hb x) d R' hc Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e'
    hEE hee π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum hF
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE
    (fun x' hx' => by
      obtain ⟨δx, q1, q2, q3, q4⟩ := hpts x'
      exact ⟨δx, q1, q2, q3, q4, (hrat0 x' hx').1, (hrat0 x' hx').2⟩)
    hE0 hτ0 hne hFix hRows
    (fun c hc2 => ⟨(hC0 c hc2).1, (hC0 c hc2).2.1, (hC0 c hc2).2.2.2, (hC c hc2).1,
      fun w hw => ⟨((hC c hc2).2.1 w hw).1,
        fun g _ m => hba c (by rintro rfl; simp at hc2) g m, ((hC c hc2).2.1 w hw).2⟩, (hC c hc2).2.2⟩)
    ⟨p1, p2, p3, hOne⟩
    hrest conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC hJR

set_option maxHeartbeats 8000000 in
theorem realDisplayWA_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
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
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (q : ℕ) (b : Fin q → (X' → O)) (π' : X')
    (ρπ : R' →ₐ[O] Matrix d d O) (sE : Finset (Ω ≃ₐ[Ek] Ω)) (tE : (Ω ≃ₐ[Ek] Ω) → Tc) (rr : ℕ → Tc) (u₁ : Oˣ)
    (hR : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingTop O X X' T T' p q b d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hF : Formalism.RepresentationBoundsCohomology.ringDataObjects.LocalToDisplayFree O X X' T Z p d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' t ht bl ρk δO)
    (hδ : δ = ∏ i ∈ Finset.Ioo 0 t, (rr 0 - rr i))
    (hδO : δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)))
    (hrr : ∀ (c : Fin (t + 1)) (i : ℕ), i < t → ∀ m : blockRestrictedRepresentationType bl ρk c,
      rr i • m = ((u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)) • m)
    (hba : ∀ c : Fin (t + 1), c ≠ 0 → ∀ g (m : blockRestrictedRepresentationType bl ρk c),
      uElt r χ g • m = ((((ε g) ^ ((c : ℕ) - 1))⁻¹ : Oˣ) : O) • m)
    (hl : lhs = vcc T Z (p π')) :
    RealDisplayWA ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ δ t ht bl ρk δO ε gI lhs := by
  obtain ⟨ha, hb, hc, hEE, hee, hpts, hρπ, hbl, hsurj, hblk, hcard1, hEsum, hE0, hδ0, hτ0, hne, hC0,
    hOne0⟩ := hR
  obtain ⟨p1, p2, p3, -⟩ := hOne0
  subst hl
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD _ _ _ _ Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC hJR
  exact realization_weight_form ℓ O X X' T T' Z p q b ha (fun x _ => hb x) d R' hc Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e'
    hEE hee π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum hF
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE
    (fun x' hx' => by
      obtain ⟨δx, q1, q2, q3, q4⟩ := hpts x'
      exact ⟨δx, q1, q2, q3, q4, (hrat0 x' hx').1, (hrat0 x' hx').2⟩)
    hE0 hτ0 hne hFix hRows
    (fun c hc2 => ⟨(hC0 c hc2).1, (hC0 c hc2).2.1, (hC0 c hc2).2.2.2, (hC c hc2).1,
      fun w hw => ⟨((hC c hc2).2.1 w hw).1,
        fun g _ m => hba c (by rintro rfl; simp at hc2) g m, ((hC c hc2).2.1 w hw).2⟩, (hC c hc2).2.2⟩)
    ⟨p1, p2, p3, hOne⟩
    hrest conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC hJR

set_option maxHeartbeats 8000000 in
theorem realDisplayAll2_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
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
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (q : ℕ) (b : Fin q → (X' → O)) (π' : X')
    (ρπ : R' →ₐ[O] Matrix d d O) (sE : Finset (Ω ≃ₐ[Ek] Ω)) (tE : (Ω ≃ₐ[Ek] Ω) → Tc) (rr : ℕ → Tc) (u₁ : Oˣ)
    (hR : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingTop O X X' T T' p q b d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hF : Formalism.RepresentationBoundsCohomology.ringDataObjects.LocalToDisplayFree O X X' T Z p d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' t ht bl ρk δO)
    (hδ : δ = ∏ i ∈ Finset.Ioo 0 t, (rr 0 - rr i))
    (hδO : δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)))
    (hrr : ∀ (c : Fin (t + 1)) (i : ℕ), i < t → ∀ m : blockRestrictedRepresentationType bl ρk c,
      rr i • m = ((u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)) • m)
    (hba : ∀ c : Fin (t + 1), c ≠ 0 → ∀ g (m : blockRestrictedRepresentationType bl ρk c),
      uElt r χ g • m = ((((ε g) ^ ((c : ℕ) - 1))⁻¹ : Oˣ) : O) • m)
    (hl : lhs = vcc T Z (p π')) :
    RealDisplayAll2 ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ δ t ht bl ρk δO ε gI lhs := by
  obtain ⟨ha, hb, hc, hEE, hee, hpts, hρπ, hbl, hsurj, hblk, hcard1, hEsum, hE0, hδ0, hτ0, hne, hC0,
    hOne0⟩ := hR
  obtain ⟨p1, p2, p3, -⟩ := hOne0
  subst hl
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne hrest
  exact realization_all_second_form ℓ O X X' T T' Z p q b ha (fun x _ => hb x) d R' hc Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e'
    hEE hee π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum hF
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE
    (fun x' hx' => by
      obtain ⟨δx, q1, q2, q3, q4⟩ := hpts x'
      exact ⟨δx, q1, q2, q3, q4, (hrat0 x' hx').1, (hrat0 x' hx').2⟩)
    hE0 hτ0 hne hFix hRows
    (fun c hc2 => ⟨(hC0 c hc2).1, (hC0 c hc2).2.1, (hC0 c hc2).2.2.2, (hC c hc2).1,
      fun w hw => ⟨((hC c hc2).2.1 w hw).1,
        fun g _ m => hba c (by rintro rfl; simp at hc2) g m, ((hC c hc2).2.1 w hw).2⟩, (hC c hc2).2.2⟩)
    ⟨p1, p2, p3, hOne⟩
    hrest

set_option maxHeartbeats 8000000 in
theorem realDisplayAllWA_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
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
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (q : ℕ) (b : Fin q → (X' → O)) (π' : X')
    (ρπ : R' →ₐ[O] Matrix d d O) (sE : Finset (Ω ≃ₐ[Ek] Ω)) (tE : (Ω ≃ₐ[Ek] Ω) → Tc) (rr : ℕ → Tc) (u₁ : Oˣ)
    (hR : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingTop O X X' T T' p q b d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hF : Formalism.RepresentationBoundsCohomology.ringDataObjects.LocalToDisplayFree O X X' T Z p d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' t ht bl ρk δO)
    (hδ : δ = ∏ i ∈ Finset.Ioo 0 t, (rr 0 - rr i))
    (hδO : δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)))
    (hrr : ∀ (c : Fin (t + 1)) (i : ℕ), i < t → ∀ m : blockRestrictedRepresentationType bl ρk c,
      rr i • m = ((u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)) • m)
    (hba : ∀ c : Fin (t + 1), c ≠ 0 → ∀ g (m : blockRestrictedRepresentationType bl ρk c),
      uElt r χ g • m = ((((ε g) ^ ((c : ℕ) - 1))⁻¹ : Oˣ) : O) • m)
    (hl : lhs = vcc T Z (p π')) :
    RealDisplayAllWA ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ δ t ht bl ρk δO ε gI lhs := by
  obtain ⟨ha, hb, hc, hEE, hee, hpts, hρπ, hbl, hsurj, hblk, hcard1, hEsum, hE0, hδ0, hτ0, hne, hC0,
    hOne0⟩ := hR
  obtain ⟨p1, p2, p3, -⟩ := hOne0
  subst hl
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha uT wT sT mT dT UT cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne hrest
  exact realization_all_weight_form ℓ O X X' T T' Z p q b ha (fun x _ => hb x) d R' hc Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e'
    hEE hee π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum hF
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE
    (fun x' hx' => by
      obtain ⟨δx, q1, q2, q3, q4⟩ := hpts x'
      exact ⟨δx, q1, q2, q3, q4, (hrat0 x' hx').1, (hrat0 x' hx').2⟩)
    hE0 hτ0 hne hFix hRows
    (fun c hc2 => ⟨(hC0 c hc2).1, (hC0 c hc2).2.1, (hC0 c hc2).2.2.2, (hC c hc2).1,
      fun w hw => ⟨((hC c hc2).2.1 w hw).1,
        fun g _ m => hba c (by rintro rfl; simp at hc2) g m, ((hC c hc2).2.1 w hw).2⟩, (hC c hc2).2.2⟩)
    ⟨p1, p2, p3, hOne⟩
    hrest

end Formalism.RepresentationBoundsCohomology.SF
