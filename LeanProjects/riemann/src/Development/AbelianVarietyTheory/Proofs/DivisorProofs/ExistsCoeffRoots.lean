import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CXiValIff
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdmissibleSmulIffOfCoprime
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEmbExt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsThClsDDdBCIff
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqOfForallAlgClosed
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsIntegralCoeffCof
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {r n : ℕ}

theorem exists_coeff_roots (c : Coeff l) {z w : ℂ} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) (hw : ∃ m : ℕ, 0 < m ∧ w ^ m = 1) :
    ∃ c' : Coeff l, c.F ≤ c'.F ∧ z ∈ c'.F ∧ w ∈ c'.F := by
  have hi : ∀ x : ℂ, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → IsIntegral ℚ x := by
    rintro x ⟨m, hm, h⟩
    exact IsIntegral.of_pow hm (h ▸ isIntegral_one)
  have := c.fin
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({z, w} : Set ℂ)) :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro x (rfl | rfl)
      · exact hi _ hz
      · exact hi _ hw)
  have hle : c.F ≤ c.F ⊔ IntermediateField.adjoin ℚ ({z, w} : Set ℂ) := le_sup_left
  have hle' : IntermediateField.adjoin ℚ ({z, w} : Set ℂ) ≤ c.F ⊔ IntermediateField.adjoin ℚ ({z, w} : Set ℂ) := le_sup_right
  exact ⟨⟨c.F ⊔ IntermediateField.adjoin ℚ ({z, w} : Set ℂ), inferInstance, fun τ a => hle (c.conj τ a), hle c.zeta_mem,
    c.le.trans hle⟩, hle, hle' (IntermediateField.subset_adjoin _ _ (by simp)),
    hle' (IntermediateField.subset_adjoin _ _ (by simp))⟩

theorem exists_coef_ext {K K' : Type} [Field K] [Field K'] (j : K →+* K') {σ : K →+* ℂ} (σ' : K' →+* ℂ)
    (hσ : ∀ a, σ' (j a) = σ a) {I : Type} [Fintype I] (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (c₀ : VV K lam →ₛₗ[σ] W) : ∃ c₁ : VV K' lam →ₛₗ[σ'] W, ∀ (v : VV K lam) (v' : VV K' lam),
      (v' : Pol K' I n) = MvPolynomial.map j (v : Pol K I n) → c₁ v' = c₀ v := by
  classical
  obtain ⟨p, hp⟩ := LinearMap.exists_extend (p := VV K lam) (LinearMap.id : VV K lam →ₗ[K] VV K lam)
  have hp' : ∀ v : VV K lam, p v = v := fun v => LinearMap.congr_fun hp v
  let C : Pol K' I n →ₛₗ[σ'] W :=
    { toFun := fun F => Finsupp.sum ((MvPolynomial.basisMonomials _ K').repr F)
        fun m a => σ' a • c₀ (p (MvPolynomial.monomial m 1))
      map_add' := fun F F' => by
        rw [map_add]
        exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
      map_smul' := fun a F => by
        rw [map_smul, Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.smul_sum]
        simp [mul_smul] }
  have hC : ∀ m a, C (MvPolynomial.monomial m a) = σ' a • c₀ (p (MvPolynomial.monomial m 1)) := fun m a => by
    have e : MvPolynomial.monomial m a = a • MvPolynomial.basisMonomials _ K' m := by
      simp [MvPolynomial.smul_monomial]
    rw [e, map_smulₛₗ]
    congr 1
    show Finsupp.sum ((MvPolynomial.basisMonomials _ K').repr (MvPolynomial.basisMonomials _ K' m))
      (fun m a => σ' a • c₀ (p (MvPolynomial.monomial m 1))) = _
    rw [Module.Basis.repr_self, Finsupp.sum_single_index (by simp), map_one, one_smul]
  have key : ∀ F : Pol K I n, C (MvPolynomial.map j F) = c₀ (p F) := by
    intro F
    induction F using MvPolynomial.induction_on' with
    | monomial m a =>
      rw [MvPolynomial.map_monomial, hC, hσ, ← map_smulₛₗ, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    | add F F' h h' => rw [map_add, map_add, h, h', map_add, map_add]
  exact ⟨C.comp (VV K' lam).subtype, fun v v' h => by
    show C v' = _
    rw [h, key, hp']⟩

theorem covPin_covBC (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) {u : c'.F} (hu : u ≠ 0)
    (h : d.IsLev ∧ d.l₂.A = 1 ∧ ∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) :
    (covBC hle d u).IsLev ∧ (covBC hle d u).l₂.A = 1 ∧
      ∃ _ : StarRing (𝓞 E), IsNab (covBC hle d u).Xo₂ (covBC hle d u).c₂ (covBC hle d u).nab₂ := by
  obtain ⟨h1, h2, s, h3⟩ := h
  exact ⟨GlobalTheory.LevelCoverDatum.isLev_smul (ddBC hle d) (GlobalTheory.FieldBCModel.isLev_ddBC hle d h1) u hu, h2, s,
    GlobalTheory.FieldBCModel.isNab_nabBC (le_covCoeff hle d) d.nab₂ h3⟩

theorem phiHat_covBC (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) (u : c'.F) (φ : (Fin n → LevQc Dw d.l₂) → c.F)
    (w : c.F) (q : Fin n → LevQ Dw d.l₂) (h : d.eF w = phiHat d.c₂ (fun x => d.eF (φ x)) q) :
    (covBC hle d u).eF (incF c c' hle w) =
      phiHat (covBC hle d u).c₂ (fun x => (covBC hle d u).eF (incF c c' hle (φ x))) q := by
  have e := congrArg (incF d.c₂ (covCoeff hle d) (le_covCoeff hle d)) h
  refine Eq.trans (Subtype.ext rfl) (e.trans ?_)
  unfold phiHat
  have hz : zetaM (covCoeff hle d) = incF d.c₂ (covCoeff hle d) (le_covCoeff hle d) (zetaM d.c₂) := by
    unfold zetaM; rw [map_pow]; rfl
  refine (AddMonoidHom.map_finsum_of_injective
    (incF d.c₂ (covCoeff hle d) (le_covCoeff hle d)).toAddMonoidHom (RingHom.injective _) _).trans ?_
  refine finsum_congr fun x => ?_
  show incF d.c₂ (covCoeff hle d) (le_covCoeff hle d) (_ * _) = _
  rw [map_mul, map_zpow₀, ← hz]
  rfl

theorem epIs_map (hle : c.F ≤ c'.F) {bad : ℕ} {B : Ideal (𝓞 E) → c.F} {epF : Submodule (𝓞 E) (Fin n → E) → c.F}
    (h : EpIs (Dw := Dw) c bad B epF) :
    EpIs (Dw := Dw) c' bad (fun I => incF c c' hle (B I)) (fun L => incF c c' hle (epF L)) := by
  intro L cc h1 h2 h3 h4 h5
  obtain ⟨q, a, b, e⟩ := h L cc h1 h2 h3 h4 h5
  exact ⟨q, a, b, by simp only [e, map_mul, map_inv₀, map_ratCast]⟩

theorem isThClsD_covBC_one (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) {u : c'.F} (hu : u = 1) {Cl : Type} [Fintype Cl]
    (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F)
    {Vs : Type} [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    {Vs' : Type} [AddCommGroup Vs'] [Module c'.F Vs'] (io' : Vs' →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
    (x : Cl → Vs) (x' : Cl → Vs') (hx : ∀ k, io' (x' k) = MvPolynomial.map (incF c c' hle) (io (x k)))
    (hd : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a m)
    (h : IsThClsD Xo c d w La Nc gam vol ep io x f) :
    IsThClsD Xo c' (covBC hle d u) (fun k q => incF c c' hle (w k q)) La Nc gam (incF c c' hle vol)
      (fun k => incF c c' hle (ep k)) io' x' (rulBC hle f) := by
  subst hu
  have h' := (GlobalTheory.ClassSumFieldChange.isThClsD_ddBC_iff E H Dw l Xo c c' hle n d Cl w La Nc gam vol ep Vs io Vs' io' x x'
    hx hd a m f hf).2 h
  intro k _ _ _ i hk y y₂ hy
  obtain ⟨vc, h1, h2⟩ := @h' k _ _ _ i hk y y₂ hy
  refine ⟨vc, h1, h2.trans ?_⟩
  have e : (covBC hle d 1).cδ = (ddBC hle d).cδ := one_smul (covCoeff hle d).F (rulBC (le_covCoeff hle d) d.cδ)
  rw [e]
  rfl

theorem isBC_rulBC_trans {c₀ : Coeff l} (h₀ : c₀.F ≤ c.F) (hle : c.F ≤ c'.F) (h₁ : c₀.F ≤ c'.F)
    {a : (E →+* ℂ) × ℕ → ℕ} {k m : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a k) {as : Fin m → c.F} {fs : Fin m → Rul Xo c₀}
    (h : IsBC h₀ f as fs) : IsBC h₁ (rulBC hle f) (fun i => incF c c' hle (as i)) fs := by
  intro S _ _ _ hS y
  letI := resAlg hle S
  rw [GlobalTheory.FieldBCModel.evR_rulBC hle hf.1 (fun _ => rfl) y, h S (fun a => hS a) _]
  rfl

end Gen

section Forms

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  {K' : Type} [Field K'] {σ' : K' →+* ℂ} (t : T0) {Cl : Type} (h : Cl → GA D (Vc D i))
  (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)

theorem adForms_ext {Gp Γ W I : Type} [Group Gp] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* Gp}
    {ρ : Γ →* Module.End ℂ W} {J J' : Subgroup Gp} {χ : J →* ℂˣ} {F F' : Gp → W} (hF : F ∈ Bridge.AdForms ι ρ J χ)
    (hF' : F' ∈ Bridge.AdForms ι ρ J χ) (hJ : J' ≤ J) {y : I → Gp} (hr : Bridge.IsReps ι J' y)
    (h : ∀ k, F (y k) = F' (y k)) : F = F' := by
  funext g
  obtain ⟨k, ⟨γ, κ, rfl⟩, -⟩ := hr g
  have h1 := hF γ (y k) ⟨κ, hJ κ.2⟩
  have h2 := hF' γ (y k) ⟨κ, hJ κ.2⟩
  rw [h k] at h1
  exact h1.trans h2.symm

theorem place_unique (hV : R.models_HV) {J' : Subgroup (Bridge.Gf (Vc D i))} (hJ : J' ≤ levJ R i t)
    (hr : Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k))) {y y' : (R.HV i t).H} {x : Cl → VsV D i K'}
    (hy : Place R i t h c0' y x) (hy' : Place R i t h c0' y' x) : y = y' := by
  exact (hV i t).1 (adForms_ext ((hV i t).2.1.le (LinearMap.mem_range_self (R.HV i t).e y))
    ((hV i t).2.1.le (LinearMap.mem_range_self (R.HV i t).e y')) hJ hr fun k => (hy k).trans (hy' k).symm)

open Classical in

def thAdOf (v₀ : (R.MW i (sg0 D A)).Vec) (x : Cl → VsV D i K') : AutQ (Wc D i) → ℂ :=
  if hx : ∃ y, Place R i t h c0' y x then onQ (Wc D i) (R.thF i t hx.choose v₀) else 0

theorem thAdIs_thAdOf (hV : R.models_HV) {J' : Subgroup (Bridge.Gf (Vc D i))} (hJ : J' ≤ levJ R i t)
    (hr : Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k))) (v₀ : (R.MW i (sg0 D A)).Vec) :
    ThAdIs R i t h c0' v₀ (thAdOf R i t h c0' v₀) := by
  intro y x hy
  have hx : ∃ y, Place R i t h c0' y x := ⟨y, hy⟩
  have e := place_unique R i t h c0' hV hJ hr hx.choose_spec hy
  exact (dif_pos hx).trans (congrArg (fun y => onQ (Wc D i) (R.thF i t y v₀)) e)

end Forms

end GlobalTheory.OneMapAll
