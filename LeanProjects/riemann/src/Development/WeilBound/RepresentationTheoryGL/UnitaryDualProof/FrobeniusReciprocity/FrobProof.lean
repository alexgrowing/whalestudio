import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.TrivSymmApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousSectionQuotientStatement
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.HaarDistr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzBruhatCharacterIntegralOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHaarRightInvariantStatement

noncomputable section

open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil

namespace PositivityTheory.PfBern.Frob

theorem pull_symm_pull {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (F : SB X) : pullHomeo e (pullHomeo e.symm F) = F :=
  Subtype.ext (funext fun x => by simp)

theorem pull_pull_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (F : SB Y) : pullHomeo e.symm (pullHomeo e F) = F :=
  Subtype.ext (funext fun y => by simp)

section Main

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {H : Subgroup G} [LocallyCompactSpace H]
  {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)
  (hpc : Continuous p) (μH : Measure H) [μH.IsHaarMeasure] [LocallyCompactSpace (Fib p)]
  (μG : Measure G) [μG.IsHaarMeasure] (χ : G →* ℂˣ)

theorem fibSmul_fibSmul (a b : H) (z : Fib p) :
    fibSmul hp a (fibSmul hp b z) = fibSmul hp (a * b) z :=
  Subtype.ext (by simp [smul_smul])

theorem int_chi_right [μG.IsMulRightInvariant] (α : SB G) (h0 : G) :
    ∫ g, (α : G → ℂ) (g * h0⁻¹) * (χ g : ℂ) ∂μG =
      (χ h0 : ℂ) * ∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG := by
  calc ∫ g, (α : G → ℂ) (g * h0⁻¹) * (χ g : ℂ) ∂μG
      = ∫ g, (α : G → ℂ) (g * h0 * h0⁻¹) * (χ (g * h0) : ℂ) ∂μG :=
        (integral_mul_right_eq_self (fun g => (α : G → ℂ) (g * h0⁻¹) * (χ g : ℂ)) h0).symm
    _ = ∫ g, ((α : G → ℂ) g * (χ g : ℂ)) * (χ h0 : ℂ) ∂μG := by
        congr 1; funext g
        simp only [mul_inv_cancel_right, map_mul, Units.val_mul]
        ring
    _ = _ := by rw [integral_mul_const, mul_comm]

theorem int_chi_left (α : SB G) (g0 : G) :
    ∫ g, ((transl g0 α : SB G) : G → ℂ) g * (χ g : ℂ) ∂μG =
      (χ g0 : ℂ) * ∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG := by
  calc ∫ g, ((transl g0 α : SB G) : G → ℂ) g * (χ g : ℂ) ∂μG
      = ∫ g, (α : G → ℂ) (g0⁻¹ * g) * (χ (g0 * (g0⁻¹ * g)) : ℂ) ∂μG := by
        congr 1; funext g
        simp only [transl_apply, smul_eq_mul, mul_inv_cancel_left]
    _ = ∫ g, (α : G → ℂ) g * (χ (g0 * g) : ℂ) ∂μG :=
        integral_mul_left_eq_self (fun g => (α : G → ℂ) g * (χ (g0 * g) : ℂ)) g0⁻¹
    _ = ∫ g, (χ g0 : ℂ) * ((α : G → ℂ) g * (χ g : ℂ)) ∂μG := by
        congr 1; funext g
        simp only [map_mul, Units.val_mul]
        ring
    _ = _ := integral_const_mul _ _

theorem avg_pull (F : SB (X × H)) :
    avg hp σ hpc μH (pullHomeo (triv hp σ hpc).symm F) =
      intB μH (fun _ => (1 : ℂ)) continuous_const F := by
  show intB μH (fun _ => (1 : ℂ)) continuous_const
    (pullHomeo (triv hp σ hpc) (pullHomeo (triv hp σ hpc).symm F)) = _
  rw [pull_symm_pull]

theorem avg_lift (b0 : SB H) (hb0 : ∫ y, (b0 : H → ℂ) y ∂μH = 1) (f : SB X) :
    avg hp σ hpc μH (pullHomeo (triv hp σ hpc).symm (tens f b0)) = f := by
  rw [avg_pull, intB_tens]
  simp [hb0]

theorem exists_schwartz_integral_one : ∃ b0 : SB H, ∫ y, (b0 : H → ℂ) y ∂μH = 1 := by
  obtain ⟨b0, hb0⟩ := GlobalTheory.T.exists_schwartzBruhat_character_integral_one H μH 1
    (by simp only [MonoidHom.one_apply, Units.val_one]; exact continuous_const)
  exact ⟨b0, by simpa using hb0⟩

theorem span_fap :
    Submodule.span ℂ (Set.range fun q : SB G × SB (Fib p) => fap hp σ hpc μH q.1 q.2) = ⊤ := by
  obtain ⟨b0, hb0⟩ := exists_schwartz_integral_one μH
  rw [eq_top_iff]
  intro f _
  rw [← avg_lift hp σ hpc μH b0 hb0 f]
  exact tens_induction (avg hp σ hpc μH) _ _ (fun a b _ => Submodule.subset_span ⟨(a, b), rfl⟩)

theorem transl_fap (g0 : G) (α : SB G) (φ : SB (Fib p)) :
    transl g0 (fap hp σ hpc μH α φ) = fap hp σ hpc μH (transl g0 α) φ := by
  apply eq_fap
  intro g z
  rw [transl_apply, smul_smul, fap_smul]
  simp only [transl_apply, smul_eq_mul, mul_assoc]

theorem fap_translF (uH : IsUnimod H) (h0 : H) (α : SB G) (φ : SB (Fib p)) :
    fap hp σ hpc μH α (translF hp h0 φ) =
      fap hp σ hpc μH (pullHomeo (Homeomorph.mulRight ((h0 : G)⁻¹)) α) φ := by
  haveI : SecondCountableTopology H := inferInstanceAs (SecondCountableTopology (H : Set G))
  haveI := GlobalTheory.T.unimodular_haar_right_invariant H uH μH
  apply eq_fap
  intro g z
  rw [fap_smul]
  refine Eq.trans ?_ (integral_mul_right_eq_self (μ := μH) _ h0)
  congr 1
  funext h
  simp [translF_apply, pullHomeo_apply, Homeomorph.coe_mulRight, fibSmul_fibSmul, mul_assoc]

theorem eval_fap (hχ : Continuous fun g => (χ g : ℂ)) (ξ : eqv X χ) (α0 : SB G)
    (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) (α : SB G) (φ : SB (Fib p)) :
    (ξ : Distr X) (fap hp σ hpc μH α φ) =
      (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) * (ξ : Distr X) (fap hp σ hpc μH α0 φ) := by
  obtain ⟨c, hc⟩ := PositivityTheory.RgUd.T2.HaarDistr.eq_const_mul_integral_char G μG χ hχ ((ξ : Distr X) ∘ₗ (avg hp σ hpc μH ∘ₗ tensL φ))
    (fun g α => by
      show (ξ : Distr X) (fap hp σ hpc μH (transl g α) φ) =
        (χ g : ℂ) * (ξ : Distr X) (fap hp σ hpc μH α φ)
      rw [← transl_fap]
      exact (mem_eqv.1 ξ.2) g _)
  have h1 : (ξ : Distr X) (fap hp σ hpc μH α φ) = c * ∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG := hc α
  have h2 : (ξ : Distr X) (fap hp σ hpc μH α0 φ) =
      c * ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG := hc α0
  rw [h1, h2, hα0, mul_one, mul_comm]

def FrMap (uG : IsUnimod G) (uH : IsUnimod H) (hχ : Continuous fun g => (χ g : ℂ)) (α0 : SB G)
    (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) :
    eqv X χ →ₗ[ℂ] eqvF hp (χ.comp H.subtype) where
  toFun ξ := ⟨(ξ : Distr X) ∘ₗ (avg hp σ hpc μH ∘ₗ tensR α0), fun h0 φ => by
    haveI := GlobalTheory.T.unimodular_haar_right_invariant G uG μG
    show (ξ : Distr X) (fap hp σ hpc μH α0 (translF hp h0 φ)) =
      (χ (h0 : G) : ℂ) * (ξ : Distr X) (fap hp σ hpc μH α0 φ)
    rw [fap_translF hp σ hpc μH uH, eval_fap hp σ hpc μH μG χ hχ ξ α0 hα0]
    congr 1
    have := int_chi_right μG χ α0 (h0 : G)
    rw [hα0, mul_one] at this
    exact this⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem FrMap_apply (uG : IsUnimod G) (uH : IsUnimod H) (hχ : Continuous fun g => (χ g : ℂ))
    (α0 : SB G) (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) (ξ : eqv X χ)
    (φ : SB (Fib p)) :
    ((FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0 ξ : eqvF hp _) : Distr (Fib p)) φ =
      (ξ : Distr X) (fap hp σ hpc μH α0 φ) :=
  rfl

theorem FrMap_injective (uG : IsUnimod G) (uH : IsUnimod H)
    (hχ : Continuous fun g => (χ g : ℂ)) (α0 : SB G)
    (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) :
    Function.Injective (FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ξ hξ
  have h0 : ∀ φ, (ξ : Distr X) (fap hp σ hpc μH α0 φ) = 0 := fun φ => by
    have := LinearMap.congr_fun (congrArg Subtype.val hξ) φ
    rw [FrMap_apply] at this
    exact this
  apply Subtype.ext
  show (ξ : Distr X) = 0
  apply LinearMap.ext_on_range (span_fap hp σ hpc μH)
  rintro ⟨α, φ⟩
  show (ξ : Distr X) (fap hp σ hpc μH α φ) = 0
  rw [eval_fap hp σ hpc μH μG χ hχ ξ α0 hα0, h0, mul_zero]

def intG (hχ : Continuous fun g => (χ g : ℂ)) : SB (G × Fib p) →ₗ[ℂ] SB (Fib p) :=
  intB μG (fun g => (χ g : ℂ)) hχ ∘ₗ pullHomeo (Homeomorph.prodComm (Fib p) G)

theorem intG_tens (hχ : Continuous fun g => (χ g : ℂ)) (α : SB G) (φ : SB (Fib p)) :
    intG μG χ hχ (tens α φ) = (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) • φ := by
  apply Subtype.ext
  funext z
  show ∫ g, ((α : G → ℂ) g * (φ : Fib p → ℂ) z) * (χ g : ℂ) ∂μG =
    (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) * (φ : Fib p → ℂ) z
  rw [← integral_mul_const]
  congr 1
  funext g
  ring

theorem FrMap_surjective (uG : IsUnimod G) (uH : IsUnimod H)
    (hχ : Continuous fun g => (χ g : ℂ)) (α0 : SB G)
    (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) :
    Function.Surjective (FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0) := by
  intro η
  haveI := GlobalTheory.T.unimodular_haar_right_invariant G uG μG
  obtain ⟨b0, hb0⟩ := exists_schwartz_integral_one μH
  let Ψ := triv hp σ hpc
  let Lη : SB (G × Fib p) →ₗ[ℂ] ℂ := (η : Distr (Fib p)) ∘ₗ intG μG χ hχ
  have hL : ∀ α φ, Lη (tens α φ) =
      (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) * (η : Distr (Fib p)) φ := by
    intro α φ
    show (η : Distr (Fib p)) (intG μG χ hχ (tens α φ)) = _
    rw [intG_tens, LinearMap.map_smul, smul_eq_mul]
  let M : SB (X × H) →ₗ[ℂ] ℂ := Lη ∘ₗ pullHomeo Ψ.symm
  have hM : ∀ (h0 : H) (F : SB (X × H)), M (rtr h0 F) = M F := by
    intro h0 F
    have key2 : (M ∘ₗ rtr h0 ∘ₗ pullHomeo Ψ - Lη) (pullHomeo Ψ.symm F) ∈
        (⊥ : Submodule ℂ ℂ) := by
      refine tens_induction _ ⊥ _ (fun α φ _ => ?_)
      rw [Submodule.mem_bot, LinearMap.sub_apply, sub_eq_zero]
      have e : rtr h0 (pullHomeo Ψ (tens α φ)) =
          pullHomeo Ψ (tens (pullHomeo (Homeomorph.mulRight (h0 : G)) α) (translF hp h0 φ)) := by
        apply Subtype.ext
        funext q
        simp [Ψ, translF_apply, fibSmul_fibSmul, mul_assoc]
      show Lη (pullHomeo Ψ.symm (rtr h0 (pullHomeo Ψ (tens α φ)))) = Lη (tens α φ)
      rw [e, pull_pull_symm, hL, hL, (η.2 h0 φ)]
      have e2 : ∫ g, ((pullHomeo (Homeomorph.mulRight (h0 : G)) α : SB G) : G → ℂ) g *
          (χ g : ℂ) ∂μG = (χ ((h0 : G)⁻¹) : ℂ) * ∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG := by
        have := int_chi_right μG χ α ((h0 : G)⁻¹)
        simpa using this
      have hu : (χ ((h0 : G)⁻¹) : ℂ) * (χ (h0 : G) : ℂ) = 1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      rw [e2]
      calc (χ ((h0 : G)⁻¹) : ℂ) * (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) *
            (((χ.comp H.subtype) h0 : ℂˣ) * (η : Distr (Fib p)) φ)
          = ((χ ((h0 : G)⁻¹) : ℂ) * (χ (h0 : G) : ℂ)) *
            ((∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) * (η : Distr (Fib p)) φ) := by
            simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
            ring
        _ = _ := by rw [hu, one_mul]
    rw [Submodule.mem_bot, LinearMap.sub_apply, sub_eq_zero] at key2
    simp only [LinearMap.comp_apply, pull_symm_pull] at key2
    exact key2
  let ξ0 : Distr X := M ∘ₗ tensL b0
  have hfac : ∀ F, M F = ξ0 (intB μH (fun _ => (1 : ℂ)) continuous_const F) :=
    fun F => factor_intB μH uH b0 hb0 M hM F
  have hξ0 : ∀ α φ, ξ0 (fap hp σ hpc μH α φ) =
      (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) * (η : Distr (Fib p)) φ := by
    intro α φ
    show ξ0 (intB μH (fun _ => (1 : ℂ)) continuous_const (pullHomeo Ψ (tens α φ))) = _
    rw [← hfac]
    show Lη (pullHomeo Ψ.symm (pullHomeo Ψ (tens α φ))) = _
    rw [pull_pull_symm, hL]
  have hmem : ξ0 ∈ eqv X χ := by
    rw [mem_eqv]
    intro g f
    have : ξ0 ∘ₗ transl g = (χ g : ℂ) • ξ0 := by
      apply LinearMap.ext_on_range (span_fap hp σ hpc μH)
      rintro ⟨α, φ⟩
      show ξ0 (transl g (fap hp σ hpc μH α φ)) = (χ g : ℂ) * ξ0 (fap hp σ hpc μH α φ)
      rw [transl_fap, hξ0, hξ0, int_chi_left]
      ring
    exact LinearMap.congr_fun this f
  refine ⟨⟨ξ0, hmem⟩, ?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro φ
  show ξ0 (fap hp σ hpc μH α0 φ) = (η : Distr (Fib p)) φ
  rw [hξ0, hα0, one_mul]

theorem supportedIn_FrMap (uG : IsUnimod G) (uH : IsUnimod H)
    (hχ : Continuous fun g => (χ g : ℂ)) (α0 : SB G)
    (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) (ξ : eqv X χ) (C : Set X)
    (hC : ∀ (g : G), ∀ x ∈ C, g • x ∈ C) :
    SupportedIn (ξ : Distr X) C ↔
      SupportedIn ((FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0 ξ : eqvF hp _) : Distr (Fib p))
        (Subtype.val ⁻¹' C) := by
  constructor
  · intro hξ φ hφ
    rw [FrMap_apply]
    apply hξ
    intro x hx
    by_contra hxC
    rw [Set.mem_compl_iff, not_not] at hxC
    apply hx
    rw [fap_apply]
    have h0 : ∀ h : H, (φ : Fib p → ℂ) (fibSmul hp h⁻¹ (zpart hp σ x)) = 0 := by
      intro h
      by_contra hne
      have hc := hφ hne
      apply hc
      show ((h⁻¹ : H) : G) • ((σ.s (p x))⁻¹ • x) ∈ C
      exact hC _ _ (hC _ _ hxC)
    simp [h0]
  · intro hF f hf
    obtain ⟨b0, hb0⟩ := exists_schwartz_integral_one μH
    rw [← avg_lift hp σ hpc μH b0 hb0 f]
    have key3 : ((ξ : Distr X) ∘ₗ avg hp σ hpc μH)
        (pullHomeo (triv hp σ hpc).symm (tens f b0)) ∈ (⊥ : Submodule ℂ ℂ) := by
      refine tens_induction _ ⊥ _ (fun a b hab => ?_)
      rw [Submodule.mem_bot]
      show (ξ : Distr X) (fap hp σ hpc μH a b) = 0
      rw [eval_fap hp σ hpc μH μG χ hχ ξ α0 hα0]
      by_cases ha : ∃ g, (a : G → ℂ) g ≠ 0
      · obtain ⟨g, hg⟩ := ha
        have hb : (ξ : Distr X) (fap hp σ hpc μH α0 b) = 0 := by
          rw [← FrMap_apply hp σ hpc μH μG χ uG uH hχ α0 hα0]
          apply hF
          intro z hz hzC
          have h1 := hab (g, z) hg hz
          simp only [pullHomeo_apply, triv_symm_apply, tens_apply] at h1
          exact hf (left_ne_zero_of_mul h1) (hC g _ hzC)
        rw [hb, mul_zero]
      · push_neg at ha
        have : ∫ g, (a : G → ℂ) g * (χ g : ℂ) ∂μG = 0 := by simp [ha]
        rw [this, zero_mul]
    rw [Submodule.mem_bot] at key3
    exact key3

end Main

theorem frobeniusReciprocity : FrobeniusReciprocity := by
  intro G _ _ _ _ _ _ _ _ _ H _ hH uG uH X _ _ _ _ _ _ p hpc hp χ hχ μG _ μH _
  haveI : IsClosed (H : Set G) := hH
  haveI : LocallyCompactSpace (Fib p) := by
    have hc : IsClosed {x : X | p x = ((1 : G) : G ⧸ H)} :=
      (isClosed_singleton (x := ((1 : G) : G ⧸ H))).preimage hpc
    exact hc.locallyCompactSpace
  obtain ⟨s, hs, hsec⟩ := GlobalTheory.T.exists_continuous_section_quotient G H hH
  let σ : Sec H := ⟨s, hs, hsec⟩
  obtain ⟨α0, hα0⟩ := GlobalTheory.T.exists_schwartzBruhat_character_integral_one G μG χ hχ
  let Fr := LinearEquiv.ofBijective (FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0)
    ⟨FrMap_injective hp σ hpc μH μG χ uG uH hχ α0 hα0,
      FrMap_surjective hp σ hpc μH μG χ uG uH hχ α0 hα0⟩
  refine ⟨Fr, ?_, ?_⟩
  · intro ξ C _ hC
    exact supportedIn_FrMap hp σ hpc μH μG χ uG uH hχ α0 hα0 ξ C hC
  · intro ξ α φ f hf
    rw [eq_fap hp σ hpc μH α φ f hf]
    exact eval_fap hp σ hpc μH μG χ hχ ξ α0 hα0 α φ

end PositivityTheory.PfBern.Frob
