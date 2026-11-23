import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeSupportLattices
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOnMemGoodPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpMSelfEqZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSupA

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeSup

section Lin

open Formalism.IndefR.Arith GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls

theorem baseChange_mem {K K' M : Type} [Field K] [Field K'] [Algebra K K'] [AddCommGroup M] [Module K M]
    (φ : M →ₗ[K] M) (V : Submodule K M) (h : ∀ x ∈ V, φ x ∈ V) : ∀ x ∈ V.baseChange K', φ.baseChange K' x ∈ V.baseChange K' := by
  intro x hx
  rw [Submodule.baseChange_eq_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact Submodule.subset_span ⟨φ v, h v hv, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem span_mem {K' M : Type} [Field K'] [AddCommGroup M] [Module K' M] (O : ValuationSubring K')
    (φ : M →ₗ[K'] M) (S : Set M) (h : ∀ x ∈ S, φ x ∈ S) : ∀ x ∈ Submodule.span O S, φ x ∈ Submodule.span O S := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h x hx)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : φ (a • x) = a • φ x := φ.map_smul (a : K') x
    rw [this]; exact Submodule.smul_mem _ _ hx

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] [Fintype G] (Φ : FormsL LL Ks WL W G)

theorem keeps_of (la : HeightOneSpectrum (𝓞 Ks)) (hL : WL →ₗ[LL] WL) (hW : ∀ x ∈ Φ.WK, hL x ∈ Φ.WK)
    (hs : ∀ f : Φ.WK, (∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) → ∀ y : Φ.Pt la, Φ.nrm la y ⟨hL f, hW f f.2⟩ ≤ 1)
    (hr : ∀ g : G, hL ∘ₗ Φ.ρ g = Φ.ρ g ∘ₗ hL) : Keeps Φ la hL hW := by
  have he : ∀ eC : G → LL, hL ∘ₗ Φ.eOp eC = Φ.eOp eC ∘ₗ hL := fun eC => by
    ext x
    simp only [FormsL.eOp, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    exact Finset.sum_congr rfl fun g _ => congrArg _ (LinearMap.congr_fun (hr g) x)
  have ht : ∀ (J : Subgroup G) (lam : J →* LLˣ), ∀ x ∈ Φ.typeP J lam, hL x ∈ Φ.typeP J lam := fun J lam x hx p => by
    have h1 : Φ.ρ p (hL x) = hL (Φ.ρ p x) := (LinearMap.congr_fun (hr p) x).symm
    rw [h1, hx p, map_smul]
  have hg : ∀ eC : G → LL, ∀ x ∈ Φ.good eC, hL x ∈ Φ.good eC := by
    rintro eC _ ⟨x, rfl⟩
    exact ⟨hL x, (LinearMap.congr_fun (he eC) x).symm⟩
  have hw : ∀ (J : Subgroup G) (lam : J →* LLˣ) (eC : G → LL), ∀ x ∈ Φ.Wgood J lam eC, hL x ∈ Φ.Wgood J lam eC :=
    fun J lam eC x hx => ⟨ht J lam x hx.1, hg eC x hx.2⟩
  refine ⟨hs, hr, he, ht, hg, fun K' _ _ O _ => ?_, fun K' _ _ _ _ O _ => ?_⟩
  · have h1 : ∀ x ∈ latK Φ la O, (resW Φ hL hW).baseChange K' x ∈ latK Φ la O := by
      refine span_mem O _ _ ?_
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨⟨hL f, hW f f.2⟩, hs f hf, rfl⟩
    have h2 : ∀ V : Submodule LL WL, (∀ x ∈ V, hL x ∈ V) →
        ∀ x ∈ latKIn Φ la O V, (resW Φ hL hW).baseChange K' x ∈ latKIn Φ la O V := fun V hV x hx =>
      ⟨h1 x hx.1, baseChange_mem (resW Φ hL hW) _ (fun y hy => hV _ hy) x hx.2⟩
    exact ⟨h1, fun J lam => ⟨h2 _ (ht J lam), fun eC => h2 _ (hw J lam eC)⟩⟩
  · have h1 : ∀ x ∈ latL Φ la O, hL.baseChange K' x ∈ latL Φ la O := by
      refine span_mem O _ _ ?_
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨⟨hL f, hW f f.2⟩, hs f hf, rfl⟩
    have h2 : ∀ V : Submodule LL WL, (∀ x ∈ V, hL x ∈ V) →
        ∀ x ∈ latLIn Φ la O V, hL.baseChange K' x ∈ latLIn Φ la O V := fun V hV x hx =>
      ⟨h1 x hx.1, baseChange_mem hL _ hV x hx.2⟩
    exact ⟨h1, fun J lam => ⟨h2 _ (ht J lam), fun eC => h2 _ (hw J lam eC)⟩⟩

end Lin

section Grp

open Formalism.IndefR.Bridge GlobalTheory.HeckeModel

theorem exists_local_isDC {G : Type} [Group G] {J K L : Subgroup G} (hs : Splits J K L) {x : G} (hx : x ∈ L) {A : Finset G}
    (hA : IsDC J x A) : ∃ A₀, IsDC K x A₀ := by
  classical
  have hex : ∀ a : G, ∃ b : G, a ∈ A → (∃ k ∈ K, b = k * x) ∧ b⁻¹ * a ∈ J := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨k₁, k₂, rfl⟩ := hA.1 a ha
      obtain ⟨a₁, ha₁, b₁, hb₁, e₁, c₁⟩ := hs.dec k₁ k₁.2
      refine ⟨a₁ * x, fun _ => ⟨⟨a₁, ha₁, rfl⟩, ?_⟩⟩
      have : (a₁ * x)⁻¹ * ((k₁ : G) * x * k₂) = b₁ * k₂ := by
        rw [e₁, mul_assoc a₁ b₁ x, (c₁ x hx).eq]; group
      rw [this]
      exact J.mul_mem hb₁ k₂.2
    · exact ⟨1, fun h => absurd h ha⟩
  choose f hf using hex
  refine ⟨A.image f, fun b hb => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨k, hk, e⟩ := (hf a ha).1
    exact ⟨⟨k, hk⟩, 1, by simp [e]⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ⟨ha, hag⟩, hu⟩ := hA.2 ((k₁ : G) * x * k₂) ⟨⟨k₁, hs.le' k₁.2⟩, ⟨k₂, hs.le' k₂.2⟩, rfl⟩
    refine ⟨f a, ⟨Finset.mem_image_of_mem f ha, ?_⟩, ?_⟩
    · obtain ⟨k, hk, e⟩ := (hf a ha).1
      refine (hs.mem _ ?_).1 ?_
      · rw [e]
        exact L.mul_mem (L.inv_mem (L.mul_mem (hs.le hk) hx)) (L.mul_mem (L.mul_mem (hs.le k₁.2) hx) (hs.le k₂.2))
      · have := J.mul_mem (hf a ha).2 hag
        simpa [mul_assoc] using this
    · rintro b ⟨hb, hbg⟩
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hb
      rw [hu a' ⟨ha', ?_⟩]
      have := J.mul_mem (J.inv_mem (hf a' ha').2) (hs.le' hbg)
      simpa [mul_assoc] using this

end Grp

section Geo

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem nval_nonneg_of_int {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K'] [Algebra V K'] [IsFractionRing V K'] (e : ℕ) (a : V) : 0 ≤ nval V e (algebraMap V K' a) := by
  by_cases h0 : algebraMap V K' a = 0
  · rw [h0, nval_zero]; exact le_top
  rw [nval_of_ne h0]
  have hne : valV V (algebraMap V K' a) ≠ 0 := valV_ne_zero h0
  have hle : valV V (algebraMap V K' a) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one a
  have hlog : WithZero.log (valV V (algebraMap V K' a)) ≤ 0 := by
    have := (WithZero.log_le_log hne one_ne_zero).2 hle
    simpa using this
  have hv : (0 : ℝ) ≤ (vV V (algebraMap V K' a) : ℝ) := by
    have : (0 : ℤ) ≤ vV V (algebraMap V K' a) := by simp only [vV]; omega
    exact_mod_cast this
  exact EReal.coe_nonneg.2 (div_nonneg hv (Nat.cast_nonneg e))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem transform_integral (hI : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeValueInt Xo c (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c))
    (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    {P : Ideal (𝓞 E)} {p i : ℕ} (hP : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p) (hF : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.FinKer Xo c P p i)
    {la : HeightOneSpectrum (𝓞 c.F)} (hp : (p : 𝓞 c.F) ∉ la.asIdeal) {s : c.F} (hs : la.valuation c.F s ≤ 1)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f g : Rul Xo c} (hf : f ∈ sec Xo c a n) (hg : g ∈ sec Xo c a n)
    (hr : HkRel (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)
      (fun Ω _ _ _ y C z => hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω y C z) s f g)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v g := by
  rintro _ ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  show 0 ≤ nval T.V e (evI y g)
  letI := io.toAlgebra
  let Ω := AlgebraicClosure T.Fr
  letI : Algebra c.F Ω := ((algebraMap T.Fr Ω).comp io).toAlgebra
  let k : T.Fr →ₐ[c.F] Ω := ⟨algebraMap T.Fr Ω, fun _ => rfl⟩
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1 E H Dw l Xo c _ _ k y.1
  have e1 : evR Xo c g z = k (evI y g) := evR_frMap hWD g hg.1 k y.1 y.2.1 z hz
  have e2 := hr Ω z
  haveI := hF Ω z
  set x := hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)
      (fun Ω _ _ _ y C z => hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω y C z) f z with hx
  have halg : (letI := k.toRingHom.toAlgebra; Algebra.IsAlgebraic T.Fr Ω) := by
    have hA : k.toRingHom.toAlgebra = (inferInstance : Algebra T.Fr Ω) := Algebra.algebra_ext _ _ fun _ => rfl
    rw [hA]
    exact AlgebraicClosure.isAlgebraic T.Fr
  have hint : IsIntegral T.V x := by
    rw [hx, hkVal]
    refine finsum_induction (IsIntegral T.V) isIntegral_zero (fun _ _ => IsIntegral.add) fun C => ?_
    unfold hkTerm
    split_ifs with h
    · exact (hI la P p i hP hp T io e ho y hy trivial Ω k halg z hz C _ h.choose_spec).2
        a n f hf h0
    · exact isIntegral_zero
  by_cases hs0 : s = 0
  · have : evI y g = 0 := by
      apply k.toRingHom.injective
      show k _ = k _
      rw [← e1, map_zero]
      refine e2.trans ?_
      rw [hs0, map_zero, zero_mul]
    rw [this, nval_zero]; exact le_top
  have e3 : algebraMap T.Fr Ω ((io s)⁻¹ * evI y g) = x := by
    rw [map_mul, map_inv₀]
    show (algebraMap c.F Ω s)⁻¹ * k _ = x
    rw [← e1]
    have : evR Xo c g z = algebraMap c.F Ω s * x := e2
    rw [this, inv_mul_cancel_left₀ ((map_ne_zero _).2 hs0)]
  rw [← e3, isIntegral_algebraMap_iff (algebraMap T.Fr Ω).injective] at hint
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have e4 : evI y g = io s * algebraMap T.V T.Fr w := by
    rw [hw, mul_inv_cancel_left₀ ((map_ne_zero _).2 hs0)]
  rw [e4, nval_smul ho hs0]
  refine add_nonneg ?_ (nval_nonneg_of_int e w)
  have h5 := (WithZero.log_le_log ((la.valuation c.F).ne_zero_iff.2 hs0) one_ne_zero).2 hs
  rw [WithZero.log_one] at h5
  have : (0 : ℤ) ≤ vLa la s := by unfold vLa; omega
  exact_mod_cast this

end Geo

end GlobalTheory.HeckeSup
