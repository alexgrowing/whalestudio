import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.NotIsSRepsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepsModKM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvertibleUnitaryAdelicMatrixOfRationalUnitary
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section
namespace GlobalTheory.SUCount
open GlobalTheory.UCls.Model GlobalTheory.SUVol.TamModel
open scoped Pointwise nonZeroDivisors TensorProduct

theorem covolume_le_of_covers {H X : Type} [Group H] [MulAction H X] [MeasurableSpace X] (μ : Measure X)
    [Countable H] [MeasurableConstSMul H X] [SMulInvariantMeasure H X μ] {B : Set X}
    (hB : MeasurableSet B) (hc : ∀ x, ∃ h : H, h • x ∈ B) : covolume H X μ ≤ μ B := by
  by_cases h : HasFundamentalDomain H X μ
  · rw [← GlobalTheory.quotMeasure_univ_eq_covolume]
    exact GlobalTheory.quotMeasure_univ_le hB.nullMeasurableSet (Filter.Eventually.of_forall hc)
  · simp [covolume, h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem eq_zero_of_small {Ψ : Finset (E →+* ℂ)}
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (α : 𝓞 E)
    (h : ∀ τ ∈ Ψ, ‖τ (α : E)‖ < 1) : α = 0 := by
  by_contra h0
  obtain ⟨σ, hσ⟩ := exists_conjugate_one_le_norm h0
  by_cases hs : σ ∈ Ψ
  · exact absurd (h σ hs) (not_lt.2 hσ)
  · have h1 : ComplexEmbedding.conjugate σ ∈ Ψ := by
      by_contra h2; exact hs ((hΨ σ).2 h2)
    have h2 := h _ h1
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h2
    exact absurd h2 (not_lt.2 hσ)

theorem discrete_inReal {Ψ : Finset (E →+* ℂ)}
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (G : Matrix (Fin r) (Fin r) E)
    (Γ : Subgroup (GL (Fin r) E)) (L : Submodule (𝓞 E) (Fin r → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin r → E)) = ⊤)
    (hΓ : ∀ γ ∈ Γ, ∀ x ∈ L, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ L) :
    DiscreteTopology (inReal Ψ G Γ) := by
  have hd : ∀ a : Fin r, ∃ d ∈ (𝓞 E)⁰, ∀ x ∈ L, ∃ z : 𝓞 E, (z : E) = (d : E) * x a := by
    intro a
    obtain ⟨d, hd, h⟩ := FractionalIdeal.isFractional_of_fg (S := (𝓞 E)⁰)
      (hfg.map (LinearMap.proj a : (Fin r → E) →ₗ[𝓞 E] E))
    refine ⟨d, hd, fun x hx => ?_⟩
    obtain ⟨z, hz⟩ := h (x a) ⟨x, hx, rfl⟩
    exact ⟨z, by rw [Algebra.smul_def] at hz; exact hz⟩
  choose d hd0 hd using hd
  obtain ⟨T, hT⟩ := hfg
  let f : inReal Ψ G Γ → Ψ → (Fin r → E) → Fin r → ℂ := fun g τ x a =>
    τ.1 (d a) * (((g.1.1 τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ fun b => τ.1 (x b)) a - τ.1 (x a))
  have hf : ∀ τ x a, Continuous fun g => f g τ x a := by
    intro τ x a
    have h1 : Continuous fun g : inReal Ψ G Γ => (g.1.1 τ : Matrix (Fin r) (Fin r) ℂ) :=
      Units.continuous_val.comp ((continuous_apply τ).comp
        (continuous_subtype_val.comp continuous_subtype_val))
    exact continuous_const.mul
      (((continuous_apply a).comp (h1.matrix_mulVec continuous_const)).sub continuous_const)
  have hopen : IsOpen (⋂ τ : Ψ, ⋂ x : T, ⋂ a : Fin r, {g | ‖f g τ x a‖ < 1}) :=
    isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun x => isOpen_iInter_of_finite fun a =>
      isOpen_lt (hf τ x a).norm continuous_const
  refine discreteTopology_of_isOpen_singleton_one ?_
  convert hopen using 1
  ext g
  simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · rintro rfl τ x a
    simp [f]
  · intro h
    obtain ⟨γ, hγ, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
    have hfix : ∀ x ∈ T, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x = x := by
      intro x hx
      have hxL : x ∈ L := hT ▸ Submodule.subset_span hx
      funext a
      obtain ⟨z, hz⟩ := hd a _ (L.sub_mem (hΓ γ hγ x hxL) hxL)
      have hz0 : z = 0 := by
        refine eq_zero_of_small hΨ z fun τ hτ => ?_
        have h1 := h ⟨τ, hτ⟩ ⟨x, hx⟩ a
        have e1 : (g.1.1 ⟨τ, hτ⟩ : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ := by
          rw [← e]; rfl
        simp only [f, e1] at h1
        rw [hz, map_mul, Pi.sub_apply, map_sub, RingHom.map_mulVec]
        exact h1
      rw [hz0] at hz
      have hd' : (d a : E) ≠ 0 := by
        have := nonZeroDivisors.ne_zero (hd0 a)
        exact_mod_cast this
      have := (mul_eq_zero.1 hz.symm).resolve_left hd'
      exact sub_eq_zero.1 this
    have hall : ∀ x, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x = x := by
      intro x
      have hx : x ∈ Submodule.span E (T : Set (Fin r → E)) := by
        rw [← Submodule.span_span_of_tower (𝓞 E) E, hT, hsp]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx => exact hfix x hx
      | zero => simp
      | add x y _ _ hx hy => rw [mulVec_add, hx, hy]
      | smul c x _ hx => rw [mulVec_smul, hx]
    have hγ1 : γ = 1 := by
      ext a b
      have := congrFun (hall (Pi.single b 1)) a
      rw [mulVec_single_one] at this
      simpa [Matrix.one_apply, Pi.single_apply] using this
    rw [hγ1, map_one] at e
    exact Subtype.ext (Subtype.ext e.symm)

theorem rat_of_isSA {G γ : Matrix (Fin r) (Fin r) E} (h : IsSA G (ratM (maximalRealSubfield E) γ)) :
    γ.det = 1 ∧ ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y := by
  refine ⟨?_, fun x y => ?_⟩
  · have h1 := h.2
    rw [ratM_det] at h1
    exact one_tmul_injective (F := maximalRealSubfield E) h1
  · have key : ∀ x y : Fin r → E, hermA (IsCMField.complexConj E) G (fv (maximalRealSubfield E) x)
        (fv (maximalRealSubfield E) y) =
        (1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ herm G x y := by
      intro x y
      simp [hermA, herm, cc, fv, sg, TensorProduct.tmul_sum]
    have h1 := h.1.2 (fv _ x) (fv _ y)
    rw [GlobalTheory.LocGlob.ratM_mulVec_fv, GlobalTheory.LocGlob.ratM_mulVec_fv, key, key] at h1
    exact one_tmul_injective (F := maximalRealSubfield E) h1

def ratSU (G : Matrix (Fin r) (Fin r) E) : Subgroup (GL (Fin r) E) where
  carrier := {γ | (γ : Matrix (Fin r) (Fin r) E).det = 1 ∧
    ∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' {g g'} hg hg' :=
    ⟨by simp [hg.1, hg'.1], fun u w => by simp only [Units.val_mul, ← mulVec_mulVec, hg.2, hg'.2]⟩
  inv_mem' {g} hg := by
    refine ⟨?_, fun u w => ?_⟩
    · have := congrArg Matrix.det g.mul_inv
      rwa [det_mul, hg.1, one_mul, det_one] at this
    · rw [← hg.2]
      simp only [mulVec_mulVec, Units.mul_inv, one_mulVec]

def congSU (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (M : ℕ) :
    Subgroup (GL (Fin r) (RA (maximalRealSubfield E) E)) where
  carrier := {k | IsKM (IsCMField.complexConj E) G L M (k : Matrix (Fin r) (Fin r) _) ∧
    (k : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)).det = 1}
  one_mem' := ⟨isKM_one _ G L M, det_one⟩
  mul_mem' {g g'} hg hg' := ⟨isKM_mul _ G L M hg.1 hg'.1, by rw [Units.val_mul, det_mul, hg.2, hg'.2, one_mul]⟩
  inv_mem' {g} hg := by
    refine ⟨by rw [Matrix.coe_units_inv]; exact isKM_inv _ G L M hg.1, ?_⟩
    have := congrArg Matrix.det g.mul_inv
    rwa [det_mul, hg.2, one_mul, det_one] at this

def toAd (E : Type) [Field E] [NumberField E] (r : ℕ) :
    GL (Fin r) E →* GL (Fin r) (RA (maximalRealSubfield E) E) :=
  Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeRight :
    E →ₐ[maximalRealSubfield E] RA (maximalRealSubfield E) E).toRingHom

omit [IsCMField E] in
theorem coe_toAd (γ : GL (Fin r) E) :
    (toAd E r γ : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) =
      ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E) := rfl

theorem isSA_toAd {G : Matrix (Fin r) (Fin r) E} {γ : GL (Fin r) E} (h : γ ∈ ratSU G) :
    IsSA G (ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E)) :=
  ⟨GlobalTheory.RatUnit.isUA_ratM E r G _ (by rw [h.1]; exact one_ne_zero) h.2, by rw [ratM_det, h.1]; rfl⟩

theorem sEquiv_iff {G : Matrix (Fin r) (Fin r) E} {L : Set (Fin r → E)} {M : ℕ}
    (g g' : GL (Fin r) (RA (maximalRealSubfield E) E)) :
    SEquiv G L M (g : Matrix (Fin r) (Fin r) _) (g' : Matrix (Fin r) (Fin r) _) ↔
      ∃ γ ∈ ratSU G, ∃ k ∈ congSU G L M, g' = toAd E r γ * g * k := by
  constructor
  · rintro ⟨γ, hγ, k, hk, hk1, e⟩
    have h1 := rat_of_isSA hγ
    obtain ⟨γ, rfl⟩ := (Matrix.isUnit_iff_isUnit_det γ).2 (h1.1 ▸ isUnit_one)
    obtain ⟨k, rfl⟩ := (Matrix.isUnit_iff_isUnit_det k).2 hk.1.1
    exact ⟨γ, h1, k, ⟨hk, hk1⟩, Units.ext e⟩
  · rintro ⟨γ, hγ, k, hk, rfl⟩
    exact ⟨γ, isSA_toAd hγ, k, hk.1, hk.2, rfl⟩

theorem conj_mem_congSU {G : Matrix (Fin r) (Fin r) E} {L : Set (Fin r → E)}
    {t : GL (Fin r) (RA (maximalRealSubfield E) E)} (ht : IsSA G (t : Matrix (Fin r) (Fin r) _))
    {β : GL (Fin r) E} (hβ : β ∈ ratStab G L (t : Matrix (Fin r) (Fin r) _)) :
    t⁻¹ * toAd E r β * t ∈ congSU G L 1 := by
  have hβ' := isSA_toAd (G := G) (γ := β) ⟨hβ.1, hβ.2.1⟩
  have back : ∀ z, z ∈ (t : Matrix (Fin r) (Fin r) _).mulVec '' (hat (maximalRealSubfield E) L : Set _) →
      ((t⁻¹ : GL (Fin r) _) : Matrix (Fin r) (Fin r) _) *ᵥ z ∈ hat (maximalRealSubfield E) L := by
    rintro z ⟨y, hy, rfl⟩
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]; exact hy
  refine ⟨⟨?_, fun x hx => ?_, fun x hx => ?_⟩, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact isUA_mul _ G (isUA_mul _ G (isUA_inv _ G ht.1) hβ'.1) ht.1
  · refine ⟨_, sub_mem ?_ hx, (one_smul _ _).symm⟩
    rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    exact back _ ((hβ.2.2 _).2 ⟨x, hx, rfl⟩)
  · have h1 := back _ ((((ratStab G L _).inv_mem hβ).2.2 _).2 ⟨x, hx, rfl⟩)
    refine ⟨_, h1, ?_⟩
    rw [← coe_toAd, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      ← Units.val_mul, map_inv]
    have : t⁻¹ * toAd E r β * t * t⁻¹ * (toAd E r β)⁻¹ * t = 1 := by group
    rw [this, Units.val_one, one_mulVec]
  · have h1 := congrArg Matrix.det t.inv_mul
    rw [det_mul, ht.2, mul_one, det_one] at h1
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, ht.2, coe_toAd, hβ'.2, mul_one, mul_one]
    exact h1

open Classical in

theorem covolume_le_sum {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {L : Set (Fin r → E)} {M : ℕ}
    (μ : Measure (realSU Ψ G)) [μ.IsMulLeftInvariant]
    (A : Finset (Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)))
    (hA : ∀ g, IsKM (IsCMField.complexConj E) G L 1 g → g.det = 1 → ∃ a ∈ A,
      IsKM (IsCMField.complexConj E) G L 1 a ∧ a.det = 1 ∧
        ∃ k, IsKM (IsCMField.complexConj E) G L M k ∧ g = a * k)
    {s t : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)} (hs : IsSA G s) (ht : IsSA G t)
    (hts : SEquiv G L 1 t s) (Δ : Subgroup (GL (Fin r) E))
    (hΔ : ∀ δ ∈ ratSU G, IsKM (IsCMField.complexConj E) G L M
      (s⁻¹ * ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) * s) → δ ∈ Δ)
    {D : Set (realSU Ψ G)} (hD : MeasurableSet D)
    (hc : ∀ x, ∃ g : inReal Ψ G (ratStab G L t), g • x ∈ D) :
    covolume (inReal Ψ G Δ) (realSU Ψ G) μ ≤ ∑ _a ∈ A.filter (fun a => SEquiv G L M (t * a) s), μ D := by
  obtain ⟨s, rfl⟩ := (Matrix.isUnit_iff_isUnit_det s).2 hs.1.1
  obtain ⟨t, rfl⟩ := (Matrix.isUnit_iff_isUnit_det t).2 ht.1.1
  obtain ⟨δ, hδ, κ, hκ, hsδ⟩ := (sEquiv_iff _ _).1 hts
  let e : ratSU G →* realSU Ψ G :=
    ((embGL Ψ r).comp (ratSU G).subtype).codRestrict _ fun γ => embGL_mem_realSU Ψ G γ.1 γ.2.1 γ.2.2
  have hγ : ∀ a : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E), ∃ γ : ratSU G,
      ∀ a' : GL (Fin r) (RA (maximalRealSubfield E) E), a = a' → SEquiv G L M (t * a) s →
        ∃ k ∈ congSU G L M, s = toAd E r γ * (t * a') * k := by
    intro a
    by_cases h : ∃ a' : GL (Fin r) (RA (maximalRealSubfield E) E), a = a' ∧ SEquiv G L M (t * a) s
    · obtain ⟨a', rfl, h⟩ := h
      obtain ⟨γ, hγ, k, hk, e⟩ := (sEquiv_iff (t * a') s).1 h
      refine ⟨⟨γ, hγ⟩, fun a'' ha _ => ⟨k, hk, ?_⟩⟩
      rw [← Units.ext ha]; exact e
    · exact ⟨1, fun a' h1 h2 => absurd ⟨a', h1, h2⟩ h⟩
  choose γ hγ using hγ
  haveI : Countable (inReal Ψ G Δ) := by
    haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
    haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
    haveI : Countable (GL (Fin r) E) :=
      Function.Injective.countable (f := (Units.val : GL (Fin r) E → _)) fun _ _ h => Units.ext h
    have : ((inReal Ψ G Δ : Subgroup (realSU Ψ G)) : Set (realSU Ψ G)).Countable := by
      refine ((Set.countable_range (embGL Ψ r)).preimage Subtype.val_injective).mono fun g hg => ?_
      obtain ⟨δ, -, hδ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
      exact ⟨δ, hδ⟩
    exact this.to_subtype
  refine (covolume_le_of_covers μ (B := ⋃ a ∈ A.filter (fun a => SEquiv G L M (t * a) s), e (γ a) • D)
    (Finset.measurableSet_biUnion _ fun a _ => hD.const_smul _) fun x => ?_).trans
    ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun a _ => (measure_smul μ _ _).le))
  obtain ⟨g, hg⟩ := hc ((e ⟨δ, hδ⟩)⁻¹ * x)
  obtain ⟨β, hβ, eβ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
  have hβ' : β ∈ ratSU G := ⟨hβ.1, hβ.2.1⟩
  have hg' : (g : realSU Ψ G) = e ⟨β, hβ'⟩ := Subtype.ext eβ.symm
  have h1 := mul_mem (conj_mem_congSU ht hβ) hκ
  obtain ⟨a, haA, ha, ha1, k, hk, eak⟩ := hA _ h1.1 h1.2
  obtain ⟨a, rfl⟩ := (Matrix.isUnit_iff_isUnit_det a).2 ha.1.1
  obtain ⟨k, rfl⟩ := (Matrix.isUnit_iff_isUnit_det k).2 hk.1.1
  have eak' : t⁻¹ * toAd E r β * t * κ = a * k := Units.ext eak
  have hk' : k ∈ congSU G L M := by
    refine ⟨hk, ?_⟩
    have := h1.2
    rwa [eak, det_mul, ha1, one_mul] at this
  have hsa : s = toAd E r (δ * β⁻¹) * (t * a) * k := by
    rw [hsδ, map_mul, map_inv, eq_mul_inv_iff_mul_eq.2 eak'.symm]; group
  have hP : SEquiv G L M (t.1 * a.1) s.1 :=
    (sEquiv_iff (t * a) s).2 ⟨_, mul_mem hδ (inv_mem hβ'), k, hk', hsa⟩
  obtain ⟨k', hk'', hsk⟩ := hγ a a rfl hP
  set h : ratSU G := γ a * ⟨β, hβ'⟩ * (⟨δ, hδ⟩ : ratSU G)⁻¹ with hh
  have hhΔ : h.1 ∈ Δ := by
    refine hΔ _ h.2 ?_
    have e1 : s⁻¹ * toAd E r h.1 * s = k'⁻¹ * k := by
      have e2 : toAd E r h.1 = toAd E r (γ a) * (toAd E r (δ * β⁻¹))⁻¹ := by
        rw [← map_inv, ← map_mul, hh]; congr 1; simp [mul_assoc]
      rw [e2]
      calc _ = s⁻¹ * (toAd E r (γ a) * (toAd E r (δ * β⁻¹))⁻¹) * (toAd E r (δ * β⁻¹) * (t * a) * k) := by
            rw [← hsa]
        _ = s⁻¹ * (toAd E r (γ a) * (t * a) * k') * k'⁻¹ * k := by group
        _ = _ := by rw [← hsk]; group
    rw [← Matrix.coe_units_inv, ← coe_toAd, ← Units.val_mul, ← Units.val_mul, e1]
    exact (mul_mem (inv_mem hk'') hk').1
  refine ⟨⟨e h, Subgroup.mem_subgroupOf.2 ⟨h.1, hhΔ, rfl⟩⟩, ?_⟩
  refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨haA, hP⟩)) ⟨_, hg, ?_⟩
  simp only [Subgroup.smul_def, smul_eq_mul, hg', hh, map_mul, map_inv, mul_assoc]

theorem sum_covolume_le_pow_mul_tsum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M p0 : ℕ) (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) (ι : Type) (S : Finset ι) (s : ι → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (Δ : ι → Subgroup (GL (Fin r) E)), 2 ≤ r → 1 ≤ M → SelfDualLat G L → (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → (∀ i ∈ S, IsSA G (s i)) → (∀ i ∈ S, ∀ j ∈ S, SEquiv G (L : Set (Fin r → E)) M (s i) (s j) → i = j) → (∀ i ∈ S, ∀ δ : GL (Fin r) E, (δ : Matrix (Fin r) (Fin r) E).det = 1 → (∀ u v, herm G ((δ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((δ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) → (δ ∈ Δ i ↔ IsKM (IsCMField.complexConj E) G (L : Set (Fin r → E)) M ((s i)⁻¹ * ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) * s i))) → ∃ (J : Type) (t : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), IsSReps G (L : Set (Fin r → E)) 1 t ∧ ∑ i ∈ S, covolume (inReal Ψ G (Δ i)) (realSU Ψ G) (riemHaar Ψ G x) ≤ (M : ℝ≥0∞) ^ (2 * fdeg E * r ^ 2) * ∑' j, covolume (inReal Ψ G (ratStab G (L : Set (Fin r → E)) (t j))) (realSU Ψ G) (riemHaar Ψ G x) := by
  classical
  intro E _ _ _ r M p0 G L Ψ x ι S s Δ _ hM hL hΨ _ hs hne hΔ
  obtain ⟨J, t, ⟨j0⟩, ht⟩ := exists_sReps G (L : Set (Fin r → E)) 1
  obtain ⟨A, hAc, hA⟩ := GlobalTheory.UCls.IdxK.exists_reps_mod_KM E r M G L hM hL
  refine ⟨J, t, ht, ?_⟩
  haveI : (riemHaar Ψ G x).IsMulLeftInvariant := by unfold riemHaar; infer_instance
  set c : J → ℝ≥0∞ := fun j =>
    covolume (inReal Ψ G (ratStab G (L : Set (Fin r → E)) (t j))) (realSU Ψ G) (riemHaar Ψ G x) with hc
  have hj : ∀ i, ∃ j, i ∈ S → SEquiv G (L : Set (Fin r → E)) 1 (t j) (s i) := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨j, hj⟩ := ht.2.2 _ (hs i hi)
      exact ⟨j, fun _ => hj⟩
    · exact ⟨j0, fun h => absurd h hi⟩
  choose j hj using hj
  let P : ι → Finset (J × Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) := fun i =>
    {j i} ×ˢ A.filter (fun a => SEquiv G (L : Set (Fin r → E)) M (t (j i) * a) (s i))
  have h1 : ∀ i ∈ S, covolume (inReal Ψ G (Δ i)) (realSU Ψ G) (riemHaar Ψ G x) ≤ ∑ p ∈ P i, c p.1 := by
    intro i hi
    obtain ⟨L', hL', -, hsd⟩ := GlobalTheory.UCls.selfDual_latOf_translate E r G L (t (j i)) hL (ht.1 _).1
    haveI := discrete_inReal hΨ G (ratStab G (L : Set (Fin r → E)) (t (j i))) L' hsd.2.2.1 hsd.2.2.2.1
      fun γ hγ y hy => by
        rw [← SetLike.mem_coe, hL'] at hy ⊢
        have := (hγ.2.2 _).2 hy
        rw [GlobalTheory.LocGlob.ratM_mulVec_fv] at this
        exact this
    haveI := GlobalTheory.countable_of_discrete_subgroup (inReal Ψ G (ratStab G (L : Set (Fin r → E)) (t (j i))))
    obtain ⟨D, hD, hu, hF⟩ :=
      GlobalTheory.exists_isFundamentalDomain_subgroup (inReal Ψ G (ratStab G (L : Set (Fin r → E)) (t (j i))))
    refine (covolume_le_sum (riemHaar Ψ G x) A hA (hs i hi) (ht.1 _) (hj i hi) (Δ i)
      (fun δ hδ h => (hΔ i hi δ hδ.1 hδ.2).2 h) hD fun y => (hu y).exists).trans (le_of_eq ?_)
    rw [Finset.sum_product, Finset.sum_singleton, ← (hF _).covolume_eq_volume]
  have h2 : (S : Set ι).PairwiseDisjoint P := by
    intro i hi i' hi' hii'
    refine Finset.disjoint_left.2 fun p hp hp' => hii' (hne i hi i' hi' ?_)
    simp only [P, Finset.mem_product, Finset.mem_singleton, Finset.mem_filter] at hp hp'
    have e : j i = j i' := hp.1.symm.trans hp'.1
    exact sEquiv_trans (sEquiv_symm hp.2.2) (e ▸ hp'.2.2)
  calc _ ≤ ∑ i ∈ S, ∑ p ∈ P i, c p.1 := Finset.sum_le_sum h1
    _ = ∑ p ∈ S.biUnion P, c p.1 := (Finset.sum_biUnion h2).symm
    _ ≤ ∑ p ∈ S.image j ×ˢ A, c p.1 := by
        refine Finset.sum_le_sum_of_subset fun p hp => ?_
        obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.1 hp
        simp only [P, Finset.mem_product, Finset.mem_singleton, Finset.mem_filter] at hp
        exact Finset.mem_product.2 ⟨Finset.mem_image.2 ⟨i, hi, hp.1.symm⟩, hp.2.1⟩
    _ = (A.card : ℝ≥0∞) * ∑ j ∈ S.image j, c j := by
        rw [Finset.sum_product, Finset.mul_sum]; simp
    _ ≤ _ := mul_le_mul' (by exact_mod_cast hAc) (ENNReal.sum_le_tsum _)

end GlobalTheory.SUCount
