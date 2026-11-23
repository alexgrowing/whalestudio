import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SupCLeISupGeneric
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.VVAlgebraMapNonneg

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompHS

open NumberField IsDedekindDomain TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.AllWt GlobalTheory.FlagTan

theorem finite_of_finRes {T₀ T : CDVR} (hT : T.FinRes) (g : T₀.V →+* T.V) (hg : Function.Injective g)
    [IsLocalHom g] : g.Finite := by
  letI := g.toAlgebra
  haveI : Finite (T.V ⧸ maximalIdeal T.V) := hT
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  refine GlobalTheory.finite_of_forall_prime_mem (R := T₀.V) (B := T.V) hp.ne_zero (fun P hP h0 => ?_) ?_ ?_
  · rw [eq_maximalIdeal (hP.isMaximal h0)]
    exact hp.not_isUnit
  · exact fun h => IsDiscreteValuationRing.not_a_field _ ((Ideal.map_eq_bot_iff_of_injective hg).1 h)
  · exact ne_top_of_le_ne_top (maximalIdeal.isMaximal T.V).ne_top (map_maximalIdeal_le g)

theorem exists_common_extension {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {T T' : CDVR}
    (hT' : T'.FinRes) {j : K →+* T.Fr} {j' : K →+* T'.Fr} {e e' : ℕ} (ho : OverLa la T.V j e)
    (ho' : OverLa la T'.V j' e') :
    ∃ (W : CDVR) (i : T.Fr →+* W.Fr) (i' : T'.Fr →+* W.Fr) (r r' : ℕ), 0 < r ∧ 0 < r' ∧ r * e = r' * e' ∧
      (∀ x, vV W.V (i x) = (r : ℤ) * vV T.V x) ∧ (∀ x, vV W.V (i' x) = (r' : ℤ) * vV T'.V x) ∧
      ∀ a, i' (j' a) = i (j a) := by
  obtain ⟨T₀, j₀, ho₀, -, hini⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion K la
  obtain ⟨g, χ, -, h₁, h₂, -⟩ := hini T j e ho
  obtain ⟨g', χ', hl, h₁', h₂', -⟩ := hini T' j' e' ho'
  replace h₂ := RingHom.congr_fun h₂
  replace h₂' := RingHom.congr_fun h₂'
  simp only [RingHom.comp_apply] at h₂ h₂'
  obtain ⟨s, hs, -, hv, -⟩ := GlobalTheory.IntegralFrameCheck.nval_map_of_overLa ho₀ ho' χ' (RingHom.congr_fun h₁')
    fun a => ⟨_, (h₂' a).symm⟩
  have hg' : g'.Finite := finite_of_finRes hT' g' fun a b h => IsFractionRing.injective T₀.V T₀.Fr
    (χ'.injective (by rw [h₂', h₂', h]))
  letI := χ.toAlgebra
  letI := χ'.toAlgebra
  haveI : Module.Finite T₀.Fr T'.Fr := GlobalTheory.AlgLawsCompare.finite_of_finite_residueField χ' hs hv hT'
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (T.Fr ⊗[T₀.Fr] T'.Fr)
  letI := Ideal.Quotient.field m
  obtain ⟨W, i, r, ψ, α, hr, hi, hψ, hα, -⟩ :=
    GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T ((T.Fr ⊗[T₀.Fr] T'.Fr) ⧸ m)
  let i' : T'.Fr →+* W.Fr := ψ.toRingHom.comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeRight : T'.Fr →ₐ[T₀.Fr] T.Fr ⊗[T₀.Fr] T'.Fr).toRingHom)
  have hc : ∀ a, i' (χ' a) = i (χ a) := fun a => by
    rw [← hψ]
    refine congrArg ψ (congrArg (Ideal.Quotient.mk m) ?_)
    exact (Algebra.TensorProduct.includeRight : T'.Fr →ₐ[T₀.Fr] T.Fr ⊗[T₀.Fr] T'.Fr).commutes a
  have hc' : ∀ a, i' (j' a) = i (j a) := fun a => by
    rw [← h₁, ← h₁']
    exact hc _
  obtain ⟨r', hr', he, hi', -⟩ := GlobalTheory.IntegralFrameCheck.nval_map_of_overLa ho' (ho.bc i hr hi) i' hc' fun a =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (R := W.V) (K := W.Fr) (by
      letI := g'.toAlgebra
      exact IsIntegral.map_of_comp_eq (α.comp g) (i'.comp (algebraMap T'.V T'.Fr)) (RingHom.ext fun b => by
        show algebraMap W.V W.Fr (α (g b)) = i' (algebraMap T'.V T'.Fr (g' b))
        rw [hα, ← h₂, ← h₂', hc]) (hg'.to_isIntegral a))
  exact ⟨W, i, i', r, r', hr, hr', he, hi, hi', hc'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [NumberField K] [Algebra c.F K] {y : FrPt Xo c K}
  {v : FinitePlace K}

theorem FinFr.exists_baseChange (F : FinFr y v) {W : CDVR} (i : F.T.Fr →+* W.Fr) {r : ℕ} (hr : 0 < r)
    (hi : ∀ x, vV W.V (i x) = (r : ℤ) * vV F.T.V x) (io : c.F →+* W.Fr) (φ : CoefHom c io K)
    (hφ : ∀ a, i (F.φ a) = φ a) : ∃ z : IntFr Xo c W io, letI := io.toAlgebra
      Reframes φ y (fun k => Units.map (i : F.T.Fr →* W.Fr) (F.t k)) z.1 := by
  obtain rfl : i.comp F.io = io := RingHom.ext fun a => by
    letI := io.toAlgebra
    exact (congrArg i (F.φ.commutes a).symm).trans ((hφ _).trans (φ.commutes a))
  letI := (i.comp F.io).toAlgebra
  obtain ⟨z, ψ, hψ, hz⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c F.T W F.io F.pt i r hr
    fun a _ => hi a
  obtain rfl : ψ = ⟨i, fun _ => rfl⟩ := AlgHom.ext (RingHom.congr_fun hψ)
  obtain ⟨w, h₁, h₂⟩ := F.tri
  obtain ⟨w', hw'⟩ := exists_frMap (⟨i, fun _ => rfl⟩ : F.T.Fr →ₐ[c.F] W.Fr) w
  exact ⟨z, w', frMap_comp h₁ hw' hφ, GlobalTheory.SupGeneric.frBor_of_frMap _ h₂ hw' hz⟩

theorem FinFr.abs_t_eq (F F' : FinFr y v) (k : Ix Dw) : F.abs (F.t k) = F'.abs (F'.t k) := by
  obtain ⟨W, i, i', r, r', hr, hr', he, hi, hi', hc⟩ := exists_common_extension F'.fin F.lies F'.lies
  letI := (i.comp F.io).toAlgebra
  let φ : K →ₐ[c.F] W.Fr := ⟨i.comp F.φ.toRingHom, fun a => congrArg i (F.φ.commutes a)⟩
  obtain ⟨z, w, h₁, h₂⟩ := F.exists_baseChange i hr hi (i.comp F.io) φ fun _ => rfl
  obtain ⟨z', w', h₁', h₂'⟩ := F'.exists_baseChange i' hr' hi' (i.comp F.io) φ hc
  obtain rfl := frMap_unique h₁ h₁'
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c W.Fr
  have hu := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).2.1 W _ z z' _ (hmul _ _ _ _ _ (hinv _ _ _ h₂) h₂') k
  have h0 : i (F.t k) ≠ 0 := (map_ne_zero i).2 (F.t k).ne_zero
  have h0' : i' (F'.t k) ≠ 0 := (map_ne_zero i').2 (F'.t k).ne_zero
  have hv : valV W.V (i (F.t k)) = valV W.V (i' (F'.t k)) := by
    refine (inv_mul_eq_one₀ (valV_ne_zero h0)).1 ?_
    simpa using hu
  rw [FinFr.abs_apply, FinFr.abs_apply, ← nval_bc i hr hi, ← nval_bc i' hr' hi', nval_of_ne h0, nval_of_ne h0', vV, vV,
    hv, he]

theorem FinFr.fac_indep (F F' : FinFr y v) (e : Ix Dw → ℤ) : F.fac e = F'.fac e := by
  simp only [FinFr.fac, Units.coe_prod, Units.val_zpow_eq_zpow_val, map_prod, map_zpow₀, F.abs_t_eq F']

theorem FinFr.nrm_indep (F F' : FinFr y v) {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) :
    F.nrm f = F'.nrm f := by
  rw [F.nrm_eq hf, F'.nrm_eq hf, F.fac_indep F']

theorem FinFr.fac_nrm_indep (F F' : FinFr y v) (e : Ix Dw → ℤ) :
    F.fac e = F'.fac e ∧ ∀ f ∈ secZ Xo c e, F.nrm f = F'.nrm f :=
  ⟨F.fac_indep F' e, fun _ => F.nrm_indep F'⟩

end GlobalTheory.CompHS
