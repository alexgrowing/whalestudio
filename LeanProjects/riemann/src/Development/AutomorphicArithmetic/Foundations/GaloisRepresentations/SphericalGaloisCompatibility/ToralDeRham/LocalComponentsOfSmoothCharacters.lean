import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotientProdIrrUc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharacters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharCMEtaLocalEqNegOnePowValInert
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SphUnr

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_equiv_of_eq {N h : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin N) k) V} {x y : Fin h → IrrGL k} {hd : ∑ a, (x a).1 = N}
    (φ : Nonempty (ρ.Equiv (prodIrr x hd))) (e : x = y) :
    ∃ hd' : ∑ a, (y a).1 = N, Nonempty (ρ.Equiv (prodIrr y hd')) := by
  subst e
  exact ⟨hd, φ⟩

theorem sum_singleton_eq_map {α : Type*} {h : ℕ} (f : Fin h → α) :
    (∑ i, ({f i} : Multiset α)) = Finset.univ.val.map f := by
  rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton (Finset.univ.val.map f), Multiset.map_map]
  rfl

theorem ms_eq_singleton {Δ : Segment k} (h1 : Δ.len = 1) : Δ.ms = {Δ.first} := by
  obtain ⟨z, hz⟩ := Multiset.card_eq_one.1 ((Segment.card_ms Δ).trans h1)
  have h3 : z = Δ.first := by
    have hm : z ∈ Δ.ms := by rw [hz]; exact Multiset.mem_singleton_self z
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hm)
    obtain rfl : a = 0 := by omega
    simp
  rw [hz, h3]

theorem equiv_prodIrr_chars (hGU : GlobalTheory.Published.GenericUnitaryDualGL) [CharZero k] {N : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth ρ)
    (hi : ρ.IsIrreducible) (hu : IsUnitarisable ρ) (hg : IsGeneric ρ) {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ))
    (hξ : ∀ j, IsSmoothChar (ξ j)) (hsup : HasSupport ρ (chars ξ hξ)) (hun : Unlinked (chars ξ hξ)) :
    ∃ (h : ℕ) (τ : Fin h → Fin n) (hd : ∑ i, (IrrGL.ofChar (ξ (τ i)) (hξ (τ i))).1 = N),
      Nonempty (ρ.Equiv (prodIrr (fun i => IrrGL.ofChar (ξ (τ i)) (hξ (τ i))) hd)) ∧
      Finset.univ.val.map (fun i => IrrGL.ofChar (ξ (τ i)) (hξ (τ i))) = chars ξ hξ := by
  obtain ⟨h, δ, Δ, s, hL, -, -, hd, ⟨φ⟩⟩ := hGU.exists_prod hs hi hu hg
  let D : Fin h → Segment k := fun i => (Δ i).nu ((s i : ℝ) : ℂ)
  have hL' : ∀ i, IsLSeg (D i) ((δ i).nu ((s i : ℝ) : ℂ)).rep := fun i => GlobalTheory.isLSeg_nu (hL i) _
  have hG : GlobalTheory.Published.GeometricLemma :=
    GlobalTheory.geometricLemma_of_filtration GlobalTheory.Laid.bzfin_holds GlobalTheory.geometricLemmaFiltration_holds
  have hs2 : HasSupport ρ (∑ i, (D i).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun i => (hL' i).hasSupport) hi
      (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have he := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hs2 hsup
  have hmem : ∀ i (a : ℕ), a < (D i).len → (D i).first.nu (a : ℂ) ∈ chars ξ hξ := fun i a ha => by
    rw [← he]
    exact Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, Segment.mem_ms.2 (Segment.mem_carrier.2 ⟨a, ha, rfl⟩)⟩
  have hlen : ∀ i, (D i).len = 1 := fun i => by
    by_contra hne
    have h2 : 1 < (D i).len := by have := (D i).len_pos; omega
    have h0 := hmem i 0 (D i).len_pos
    have h1 := hmem i 1 h2
    rw [Nat.cast_zero, IrrGL.nu_zero] at h0
    rw [Nat.cast_one] at h1
    exact hun _ h1 _ h0 rfl
  have hex : ∀ i, ∃ j, (D i).first = IrrGL.ofChar (ξ j) (hξ j) := fun i => by
    have h0 := hmem i 0 (D i).len_pos
    rw [Nat.cast_zero, IrrGL.nu_zero] at h0
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h0
    exact ⟨j, hj.symm⟩
  choose τ hτ using hex
  have hfam : (fun i => (δ i).nu ((s i : ℝ) : ℂ)) = fun i => IrrGL.ofChar (ξ (τ i)) (hξ (τ i)) :=
    funext fun i => (GlobalTheory.GenSph.eq_first_of_isLSeg (hL' i) (hlen i)).trans (hτ i)
  obtain ⟨hd', hφ⟩ := exists_equiv_of_eq ⟨φ⟩ hfam
  refine ⟨h, τ, hd', hφ, ?_⟩
  rw [← he, ← sum_singleton_eq_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ms_eq_singleton (hlen i), hτ i]

theorem equiv_prodIrr_untwist {N h : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (x : Fin h → IrrGL k)
    (hd : ∑ a, (x a).1 = N) (φ : Nonempty ((twist ρ (detChar (Fin N) χ)).Equiv (prodIrr x hd))) :
    Nonempty (ρ.Equiv (prodIrr (fun a => (x a).tw χ⁻¹ hχ.inv) hd)) := by
  obtain ⟨φ⟩ := φ
  have e : twist (twist ρ (detChar (Fin N) χ)) (detChar (Fin N) χ⁻¹) = ρ := by
    rw [twist_twist]
    convert twist_one ρ
    ext g
    simp [detChar_apply]
  refine ⟨?_⟩
  rw [← e]
  exact (twistEquiv φ _).trans (prodIrrTwistEquiv x hd χ⁻¹ hχ.inv)

open scoped Classical in

noncomputable def valAt (ϖ : kˣ) (y : IrrGL k) : ℂˣ :=
  if h : ∃ (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ), y = IrrGL.ofChar μ hμ then h.choose ϖ else 1

theorem valAt_ofChar (ϖ : kˣ) (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) : valAt ϖ (IrrGL.ofChar μ hμ) = μ ϖ := by
  have h : ∃ (μ' : kˣ →* ℂˣ) (hμ' : IsSmoothChar μ'), IrrGL.ofChar μ hμ = IrrGL.ofChar μ' hμ' := ⟨μ, hμ, rfl⟩
  rw [valAt, dif_pos h]
  obtain ⟨hμ', e⟩ := h.choose_spec
  exact (congrArg (fun f : kˣ →* ℂˣ => f ϖ) (IrrGL.ofChar_inj.1 e)).symm

end Local

section Sph

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem hasSatGL_of_equiv_prodIrr {n h : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (ζ : Fin h → ((w.adicCompletion E)ˣ →* ℂˣ)) (hζ : ∀ i, IsSmoothChar (ζ i))
    (hd : ∑ i, (IrrGL.ofChar (ζ i) (hζ i)).1 = n)
    (φ : Nonempty (σ.ρ.Equiv (prodIrr (fun i => IrrGL.ofChar (ζ i) (hζ i)) hd)))
    (hunr : ∀ i (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ζ i x = 1)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) :
    GlobalTheory.LFun.HasSatGL w σ.ρ (Finset.univ.val.map fun i => ζ i ϖ) := by
  obtain rfl : h = n := by rw [← hd]; simp [IrrGL.ofChar]
  have hu : ∀ i, IrrGL.ofChar (ζ i) (hζ i) = GlobalTheory.GenSph.uc (w.adicCompletion E) (ζ i ϖ) := fun i =>
    IrrGL.ofChar_inj.2 (eq_unrChar (fun x hx => hunr i x (GlobalTheory.MuInert.valued_eq_one w hx))
      (GlobalTheory.MuInert.valuation_eq_uniformizer w hϖ))
  obtain ⟨hd', ⟨ψ⟩⟩ := GlobalTheory.SphUnr.exists_equiv_of_eq φ (funext hu)
  have hsph : IsSpherical σ.ρ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.GenSph.isSpherical_prodIrr_uc (fun i => ζ i ϖ) hd')
    refine (Submodule.ne_bot_iff _).2 ⟨ψ.symm v, GlobalTheory.LGrp.mem_fixed.2 fun g hg => ?_, fun e => hv0 ?_⟩
    · exact (ψ.symm.toIntertwiningMap.isIntertwining _ _ g v).symm.trans
        (congrArg ψ.symm (GlobalTheory.LGrp.mem_fixed.1 hv g hg))
    · exact ψ.symm.toLinearEquiv.injective (e.trans (map_zero _).symm)
  have hS : HasSatake σ.ρ (fun i => ζ i ϖ) := ⟨σ.irred, hsph,
    (IsSubquotient.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective).trans
      (GlobalTheory.GenSph.isSubquotient_prodIrr_uc (fun i => ζ i ϖ) hd')⟩
  exact GlobalTheory.LFun.SatCompare.hasSatGL_of_hasSatakeGL
    ((GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ _).2 ⟨_, rfl, hS⟩)

end Sph

section Glob

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem exists_isUnitarisable_twist {a : ℕ} (ha : 1 ≤ a) (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (hσ : π.IsLocComp w σ) :
    ∃ t : ℝ, IsUnitarisable (twist σ.ρ (detChar (Fin a) (absPow (w.adicCompletion E) ((t : ℝ) : ℂ)))) := by
  obtain ⟨π₀, t, hu, he⟩ := CG.exists_isUnitary_twist_absPow (CG.mk π) ha
  obtain ⟨π₀, rfl⟩ : ∃ p : CuspSub E a, CG.mk p = π₀ := ⟨π₀.out, Quotient.out_eq π₀⟩
  have hiso : CG.mk (π.twist (Model.absPow E (-t))) = CG.mk π₀ := by
    have e1 : CG.mk (π.twist (Model.absPow E (-t))) = (CG.mk π).twist (Model.absPow E (-t)) := rfl
    rw [e1, he, ← CG.twist_mul, mul_comm, CG.absPow_neg_mul, CG.twist_one]
  have hlc := (hσ.twist (Model.absPow E (-t))).congr (Quotient.exact hiso) ⟨Representation.Equiv.refl _⟩
  have hU := GlobalTheory.ResW.isUnitarisable_of_isLocComp_cusp E a π₀ ha ((CG.isUnitary_mk π₀).1 hu) w _ hlc
  refine ⟨-t, ?_⟩
  have hl := GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (Model.absPow_isAbsPow E (-t)) w
  change IsUnitarisable (twRep σ.ρ ((GlobalTheory.HeckeGal.Model.absPow E (-t)).loc w |>.comp Matrix.GeneralLinearGroup.det)) at hU
  rw [hl] at hU
  exact hU

end Glob

end GlobalTheory.SphUnr

namespace GlobalTheory.SphUnr

theorem hasSat_of_unlinked_unr : UpperTheory.Gal.ToralGalois.Inq → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E)), ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)),
    π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)),
    HasSupport σ.ρ (chars ξ hξ) → Unlinked (chars ξ hξ) →
    (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) →
    ∀ ϖ : (w.adicCompletion E)ˣ, Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) →
    (CG.mk π).HasSat w (Finset.univ.val.map fun j => ξ j ϖ) := by
  intro hI E _ _ _ n hn π w σ hσ ξ hξ hsup hun hunr ϖ hϖ
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨t, hU⟩ := exists_isUnitarisable_twist hn π w σ hσ
  set χ : (w.adicCompletion E)ˣ →* ℂˣ := absPow (w.adicCompletion E) ((t : ℝ) : ℂ) with hχdef
  have hχ : IsSmoothChar χ := isSmoothChar_absPow _
  have hg : IsGeneric σ.ρ := Generic.isGeneric_of_isLocComp E n π w σ hσ
  have hc := TwistSupp.chars_eq_map_nu ξ (fun j => ξ j * χ) hξ (fun j => (hξ j).mul hχ) ((t : ℝ) : ℂ) fun j => rfl
  have hsup' : HasSupport (twist σ.ρ (detChar (Fin n) χ)) (chars (fun j => ξ j * χ) fun j => (hξ j).mul hχ) := by
    rw [hc]
    exact hsup.tw χ hχ
  have hun' : Unlinked (chars (fun j => ξ j * χ) fun j => (hξ j).mul hχ) := by
    rw [hc, TwistSupp.unlinked_map_nu]
    exact hun
  obtain ⟨h, τ, hd, hφ, hmap⟩ := equiv_prodIrr_chars hI.gen _ (isSmooth_twist σ.smooth hχ.detChar)
    (isIrreducible_twist σ.irred _) hU ((isGeneric_twist_iff χ).2 hg) _ _ hsup' hun'
  have hφ' := equiv_prodIrr_untwist σ.ρ χ hχ _ hd hφ
  have hfam : (fun i => (IrrGL.ofChar (ξ (τ i) * χ) ((hξ (τ i)).mul hχ)).tw χ⁻¹ hχ.inv) =
      fun i => IrrGL.ofChar (ξ (τ i)) (hξ (τ i)) := funext fun i => by
    rw [IrrGL.tw_ofChar]
    exact IrrGL.ofChar_inj.2 (by rw [mul_assoc, mul_inv_cancel, mul_one])
  obtain ⟨hd2, hφ2⟩ := exists_equiv_of_eq hφ' hfam
  have hS := hasSatGL_of_equiv_prodIrr w σ (fun i => ξ (τ i)) (fun i => hξ (τ i)) hd2 hφ2 (fun i => hunr (τ i)) ϖ hϖ
  have hm : Finset.univ.val.map (fun i => ξ (τ i) ϖ) = Finset.univ.val.map fun j => ξ j ϖ := by
    have e := congrArg (Multiset.map fun y => valAt ϖ y * (χ ϖ)⁻¹) hmap
    simp only [chars, Multiset.map_map, Function.comp_def, valAt_ofChar, MonoidHom.mul_apply,
      mul_inv_cancel_right] at e
    exact e
  rw [CG.hasSat_mk, ← hm]
  exact GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ hS

end GlobalTheory.SphUnr

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.T.local_components_of_smooth_characters : UpperTheory.Gal.ToralGalois.Inq → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E)), ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport σ.ρ (chars ξ hξ) → Unlinked (chars ξ hξ) → (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) → ∀ ϖ : (w.adicCompletion E)ˣ, Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) → (CG.mk π).HasSat w (Finset.univ.val.map fun j => ξ j ϖ) := by
  first | (exact @GlobalTheory.SphUnr.hasSat_of_unlinked_unr) | (exact GlobalTheory.SphUnr.hasSat_of_unlinked_unr) | (intros; apply GlobalTheory.SphUnr.hasSat_of_unlinked_unr  <;> assumption)

end
