import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadLimit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PCompat

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH
attribute [local instance] PositivityTheory.Rg.BcB.CG.lc_GLf PositivityTheory.Rg.BcB.CG.sc_GLf PositivityTheory.Rg.BcB.CG.t2_GL_finite_adeles

namespace PositivityTheory.Rg.BcB.F.Rd.B

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finH_mul {a b : ℕ} (g h : Hf E a b) : finH (g * h) = finH g * finH h := by
  simp only [finH, Prod.fst_mul, Prod.snd_mul, map_mul, Prod.mk_mul_mk]

section Level

variable (B : Block E) (K₁ : Subgroup (GL (Fin B.a) (Af E))) (K₂ : Subgroup (GL (Fin B.b) (Af E)))

theorem typeH_rinv {W₁ : Submodule ℂ (Kinf E B.a → ℂ)} {W₂ : Submodule ℂ (Kinf E B.b → ℂ)}
    (F : B.I → H E B.a B.b → ℂ) (hF : ∀ i, TypeH K₁ K₂ W₁ W₂ (F i)) :
    ∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, F i (x * finH u) = F i x := by
  intro i u hu x
  exact (hF i).1 u.1 (Subgroup.mem_prod.1 hu).1 u.2 (Subgroup.mem_prod.1 hu).2 x

theorem mulF_idem_rinv (cK : ℂ) (ψ₀ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ))
    (hψ₀ : ∀ x y h, ψ₀ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    (ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)) :
    ∀ x y, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ h, mulF B.ν ψ ψ₀ x y (h * u) = mulF B.ν ψ ψ₀ x y h := by
  intro x y u hu h
  simp only [mulF]
  refine Finset.sum_congr rfl fun z _ => integral_congr_ae (Eventually.of_forall fun k => ?_)
  have e : k⁻¹ * (h * u) ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) ↔ k⁻¹ * h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) := by
    rw [← mul_assoc]; exact Subgroup.mul_mem_cancel_right _ hu
  simp only [hψ₀, e]

theorem convF_idem (hK₁o : IsOpen (K₁ : Set (GL (Fin B.a) (Af E)))) (hK₂o : IsOpen (K₂ : Set (GL (Fin B.b) (Af E))))
    (cK : ℂ) (hcK : cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1)
    (ψ₀ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ))
    (hψ₀ : ∀ x y h, ψ₀ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    {A : Type} (f : A × B.κ → H E B.a B.b → ℂ)
    (hf : ∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, f i (x * finH u) = f i x) :
    convF B.ν ψ₀ f = f := by
  have : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  have hKo : IsOpen (((K₁.prod K₂ : Subgroup (Hf E B.a B.b))) : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]; exact hK₁o.prod hK₂o
  funext i x
  simp only [convF]
  rw [Finset.sum_eq_single i.2]
  · have e : (fun h => ψ₀ i.2 i.2 h * f (i.1, i.2) (x * finH h)) =
        Set.indicator (((K₁.prod K₂ : Subgroup (Hf E B.a B.b))) : Set (Hf E B.a B.b)) (fun _ => cK * f i x) := by
      funext h
      rw [hψ₀]
      by_cases hh : h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b))
      · rw [Set.indicator_of_mem (SetLike.mem_coe.2 hh), if_pos ⟨rfl, hh⟩, Prod.mk.eta, hf i h hh x]
      · rw [Set.indicator_of_notMem (fun h' => hh (SetLike.mem_coe.1 h')), if_neg (fun h' => hh h'.2), zero_mul]
    rw [e, integral_indicator_const _ hKo.measurableSet, Complex.real_smul, ← mul_assoc,
      mul_comm ((_ : ℝ) : ℂ) cK, hcK, one_mul]
  · intro z _ hz
    have e : (fun h => ψ₀ i.2 z h * f (i.1, z) (x * finH h)) = fun _ => 0 := by
      funext h
      rw [hψ₀, if_neg (fun h' => hz h'.1.symm), zero_mul]
    rw [e, integral_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem convF_mulF_idem (hK₁o : IsOpen (K₁ : Set (GL (Fin B.a) (Af E))))
    (hK₁c : IsCompact (K₁ : Set (GL (Fin B.a) (Af E)))) (hK₂o : IsOpen (K₂ : Set (GL (Fin B.b) (Af E))))
    (hK₂c : IsCompact (K₂ : Set (GL (Fin B.b) (Af E))))
    (cK : ℂ) (hcK : cK * (B.ν.real ((K₁.prod K₂ : Subgroup (Hf E B.a B.b)) : Set (Hf E B.a B.b)) : ℂ) = 1)
    (ψ₀ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ))
    (hψ₀ : ∀ x y h, ψ₀ x y h = if x = y ∧ h ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)) then cK else 0)
    (ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)) (hψ : IsFinM ψ)
    {A : Type} (f : A × B.κ → H E B.a B.b → ℂ)
    (hf : ∀ i, ∀ u ∈ (K₁.prod K₂ : Subgroup (Hf E B.a B.b)), ∀ x, f i (x * finH u) = f i x) :
    convF B.ν (mulF B.ν ψ ψ₀) f = convF B.ν ψ f := by
  have := B.hν
  have : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  set K : Subgroup (Hf E B.a B.b) := K₁.prod K₂ with hKdef
  have hKo : IsOpen (K : Set (Hf E B.a B.b)) := by
    rw [hKdef, Subgroup.coe_prod]; exact hK₁o.prod hK₂o
  have hKc : IsCompact (K : Set (Hf E B.a B.b)) := by
    rw [hKdef, Subgroup.coe_prod]; exact hK₁c.prod hK₂c
  have hKcl : IsClosed (K : Set (Hf E B.a B.b)) := K.isClosed_of_isOpen hKo
  funext i x
  simp only [convF]
  refine Finset.sum_congr rfl fun z _ => ?_
  set F : Hf E B.a B.b → ℂ := fun g => f (i.1, z) (x * finH g) with hFdef
  have hFinv : ∀ g, ∀ u ∈ K, F (g * u) = F g := fun g u hu => by
    simp only [hFdef, finH_mul, ← mul_assoc]; exact hf _ u hu _
  have hFc : Continuous F := by
    refine continuous_iff_continuousAt.2 fun g => ?_
    have hU : IsOpen ((fun g' => g⁻¹ * g') ⁻¹' (K : Set (Hf E B.a B.b))) :=
      hKo.preimage (continuous_const.mul continuous_id)
    have hgU : g ∈ (fun g' => g⁻¹ * g') ⁻¹' (K : Set (Hf E B.a B.b)) := by
      simp only [Set.mem_preimage, inv_mul_cancel]; exact K.one_mem
    refine (continuousAt_const (y := F g)).congr (Filter.eventually_of_mem (hU.mem_nhds hgU) fun g' hg' => ?_)
    have := hFinv g (g⁻¹ * g') hg'
    rw [mul_inv_cancel_left] at this
    exact this.symm
  set φ : Hf E B.a B.b → ℂ := ψ i.2 z with hφdef
  set ι : Hf E B.a B.b → ℂ := (K : Set (Hf E B.a B.b)).indicator (fun _ => cK) with hιdef
  have hm : ∀ g, mulF B.ν ψ ψ₀ i.2 z g = ∫ h, φ h * ι (h⁻¹ * g) ∂B.ν := by
    intro g
    simp only [mulF]
    rw [Finset.sum_eq_single z]
    · refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      simp only [hφdef, hιdef]
      rw [hψ₀]
      by_cases hh : h⁻¹ * g ∈ K
      · rw [if_pos ⟨rfl, hh⟩, Set.indicator_of_mem (SetLike.mem_coe.2 hh)]
      · rw [if_neg (fun h' => hh h'.2), Set.indicator_of_notMem (fun h' => hh (SetLike.mem_coe.1 h'))]
    · intro w _ hw
      have e : (fun h => ψ i.2 w h * ψ₀ w z (h⁻¹ * g)) = fun _ => 0 := by
        funext h; rw [hψ₀, if_neg (fun h' => hw h'.1), mul_zero]
      rw [e, integral_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have e1 : ∀ g, mulF B.ν ψ ψ₀ i.2 z g * f (i.1, z) (x * finH g) = ∫ h, φ h * ι (h⁻¹ * g) * F g ∂B.ν := fun g => by
    rw [hm g, ← integral_mul_const]
  simp_rw [e1]
  have hcl : IsClopen (K : Set (Hf E B.a B.b)) := ⟨hKcl, hKo⟩
  have hcont : Continuous (Function.uncurry fun (g h : Hf E B.a B.b) => φ h * ι (h⁻¹ * g) * F g) := by
    have c1 : Continuous φ := (hψ i.2 z).1
    have c2 : Continuous ι := hcl.continuous_indicator continuous_const
    exact ((c1.comp continuous_snd).mul (c2.comp (continuous_snd.inv.mul continuous_fst))).mul (hFc.comp continuous_fst)
  have hcs : HasCompactSupport (Function.uncurry fun (g h : Hf E B.a B.b) => φ h * ι (h⁻¹ * g) * F g) := by
    have hc : IsCompact ((fun p : Hf E B.a B.b × Hf E B.a B.b => (p.1 * p.2, p.1)) '' (tsupport φ ×ˢ (K : Set _))) :=
      ((hψ i.2 z).2.prod hKc).image ((continuous_fst.mul continuous_snd).prodMk continuous_fst)
    refine HasCompactSupport.intro hc fun p hp => ?_
    by_cases h1 : p.2 ∈ tsupport φ
    · by_cases h2 : p.2⁻¹ * p.1 ∈ K
      · exact absurd ⟨(p.2, p.2⁻¹ * p.1), ⟨h1, h2⟩, by simp⟩ hp
      · show φ p.2 * ι (p.2⁻¹ * p.1) * F p.1 = 0
        rw [hιdef, Set.indicator_of_notMem (fun h' => h2 (SetLike.mem_coe.1 h')), mul_zero, zero_mul]
    · show φ p.2 * ι (p.2⁻¹ * p.1) * F p.1 = 0
      rw [image_eq_zero_of_notMem_tsupport h1, zero_mul, zero_mul]
  rw [integral_integral_swap_of_hasCompactSupport hcont hcs]
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  show ∫ g, φ h * ι (h⁻¹ * g) * F g ∂B.ν = ψ i.2 z h * f (i.1, z) (x * finH h)
  calc ∫ g, φ h * ι (h⁻¹ * g) * F g ∂B.ν = ∫ k, φ h * ι (h⁻¹ * (h * k)) * F (h * k) ∂B.ν :=
        (integral_mul_left_eq_self (fun g => φ h * ι (h⁻¹ * g) * F g) h).symm
    _ = ∫ k, (K : Set (Hf E B.a B.b)).indicator (fun _ => cK * (φ h * F h)) k ∂B.ν := by
        refine integral_congr_ae (Eventually.of_forall fun k => ?_)
        simp only [inv_mul_cancel_left]
        by_cases hk : k ∈ K
        · rw [hιdef, Set.indicator_of_mem (SetLike.mem_coe.2 hk), Set.indicator_of_mem (SetLike.mem_coe.2 hk),
            hFinv h k hk]
          ring
        · rw [hιdef, Set.indicator_of_notMem (fun h' => hk (SetLike.mem_coe.1 h')),
            Set.indicator_of_notMem (fun h' => hk (SetLike.mem_coe.1 h'))]
          ring
    _ = ψ i.2 z h * f (i.1, z) (x * finH h) := by
        rw [integral_indicator_const _ hKo.measurableSet, Complex.real_smul, ← mul_assoc,
          mul_comm ((_ : ℝ) : ℂ) cK, hcK, one_mul]

end Level

end PositivityTheory.Rg.BcB.F.Rd.B

end
