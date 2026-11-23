import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoefMove
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtensionIntegralFramedPointLiftCoveStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverLiftVal

theorem valV_le_one_of_nval {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {e : ℕ} (he : 0 < e) {x : K'} (h : 0 ≤ nval V e x) : valV V x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx; simp
  rw [nval_of_ne hx, EReal.coe_nonneg] at h
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have h1 : (0 : ℝ) ≤ (vV V x : ℝ) := by
    have := mul_nonneg h he'.le
    rwa [div_mul_cancel₀ _ he'.ne'] at this
  have h2 : 0 ≤ vV V x := by exact_mod_cast h1
  unfold vV at h2
  rw [← WithZero.log_le_log (valV_ne_zero hx) one_ne_zero, WithZero.log_one]
  omega

theorem le_one_at_lift : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, ∀ C : Cover T j σ, C.IsUnif → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c) (g : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n) → (∀ k, g k ∈ sec C.d.Xo₂ C.d.c₂ a n) → (∀ k, C.IsPull (β k) (g k)) → ∀ y : Fin m → C.d.c₂.F, (∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v (∑ k, y k • g k)) → ∀ (T0 : CDVR) (io : T.Q.c.F →+* T0.Fr) (pt : IntFr (T.Q.Xo j) T.Q.c T0 io), T0.FinRes → ∀ (T' : CDVR) (i : T0.Fr →+* T'.Fr) (e' : ℕ) (τ : C.d.c₂.F →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T0.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T0.V z) → T'.FinRes → (∀ z : T.Q.c.F, τ (C.inc z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (evI pt (β k))) ≤ 1 := by
  intro D T hL j hj σ C hU la a n m β g hβ hg hpull y hint T0 io pt hT0 T' i e' τ e'' he' hi hT' hτ ho
  obtain ⟨y₁, φ, hφ, hmap⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange _ _ _ _ (T.Q.Xo j) T.Q.c T0 T' io pt i e' he' hi
  let σ' : C.c'.F →+* T'.Fr := τ.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)
  have hσ' : ∀ z, σ' (incF T.Q.c C.c' C.hle z) = (i.comp io) z := fun z => hτ z
  obtain ⟨y₂, hy₂⟩ := GlobalTheory.SupDescent.exists_intFr_ext C.hle (io := i.comp io) σ' hσ' y₁
  obtain ⟨T'', iT, e₃, y₃, io₂, y₄, hext, hT'', hio₂, hover⟩ := GlobalTheory.T.exists_finiteExtension_integralFramedPoint_lift_cover _ _ _ _ (T.Q.Xo j) C.c' 0 C.d hU.1 T' σ' y₂ hT'
  obtain ⟨he₃, hv₃, ψ, hψe, hψ⟩ := hext
  have hio : io₂ = iT.comp τ := by
    ext z
    obtain ⟨w, rfl⟩ := C.d.eF.surjective z
    exact hio₂ w
  subst hio
  letI : Algebra C.c'.F T''.Fr := (iT.comp σ').toAlgebra
  letI : Algebra C.d.c₂.F T''.Fr := (iT.comp τ).toAlgebra
  letI : Algebra T.Q.c.F T''.Fr := (iT.comp (i.comp io)).toAlgebra
  letI : Algebra T.Q.c.F T'.Fr := (i.comp io).toAlgebra
  letI : Algebra C.c'.F T'.Fr := σ'.toAlgebra
  have hA : AlgOver T.Q.c C.c' C.hle T''.Fr := fun z => congrArg iT (hσ' z)
  let φ₂ : T'.Fr →ₐ[T.Q.c.F] T''.Fr := { iT with commutes' := fun _ => rfl }
  have hmap₂ : FrMap φ₂ (y₂.1.res C.hle hσ') (y₃.1.res C.hle hA) := by
    obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hψ
    rw [hψe] at hx hu h2
    exact ⟨hx, hu, pm, h1, h2, h3⟩
  have hval : ∀ k, evI y₄ (g k) = iT (i (evI pt (β k))) := fun k => by
    have h1 := hpull k T''.Fr hA (fun _ => rfl) y₄.1 y₃.1 hover
    have h2 := GlobalTheory.FlagTan.evR_frMap (hβ k).1 hmap₂
    letI : Algebra T.Q.c.F T0.Fr := io.toAlgebra
    have h3 := GlobalTheory.FlagTan.evR_frMap (hβ k).1 hmap
    rw [hy₂] at h2
    show evR _ _ (g k) y₄.1 = _
    rw [h1, h2, h3]
    exact congrArg iT (DFunLike.congr_fun hφ _)
  have hsum : evI y₄ (∑ k, y k • g k) = iT (∑ k, τ (y k) * i (evI pt (β k))) := by
    show evR _ _ (∑ k, y k • g k) y₄.1 = _
    rw [GlobalTheory.SupDescent.evR_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    exact congrArg₂ (· * ·) rfl (hval k)
  have ho₂ : OverLa la T''.V (iT.comp τ) (e₃ * e'') := ho.bc iT he₃ hv₃
  have h : 0 ≤ nval T''.V (e₃ * e'') (evI y₄ (∑ k, y k • g k)) := hint _ ⟨PtV.mk (cls := algCls C.d.Xo₂ C.d.c₂) (PY := Unit) (lies := fun _ _ _ _ => True) la ho₂ y₄ hT''
    () trivial, rfl⟩
  rw [hsum, nval_bc iT he₃ hv₃] at h
  exact valV_le_one_of_nval ho.1 h

end GlobalTheory.CoverLiftVal
