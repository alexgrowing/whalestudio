import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsSeparatedOfAffineBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationClosedChartsSubordinateToCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCrystallineChernOnAnalyticThickeningsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameFactorOfAutomorphyLogStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitsComparingLiftedTransitionsFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCocycleCohomologousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupPeriodClassesSumConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstBiadditiveCoboundarySymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianDotProductMulVecStarSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegZeroCocycleExistsCoboundaryOfRichBasedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicParamOfDegZeroCompatibleStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.ChernClause

theorem pchern_of (hsep : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → A.left.IsSeparated)
 (hcharts : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ {N : Type} (𝒰 : N → X.Opens), ⨆ i, 𝒰 i = ⊤ → ∃ (K : Charts F) (r : Real K s σ) (j : K.K → N), K.Rich ∧ (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') ∧ r.IsFor u ∧ ∀ k, ⊤ ≤ r.x k ⁻¹ᵁ 𝒰 (j k))
 (hpull : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X) (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ z : SecondDeRham s, IsChern (dp0 B) s M z → ∃ (i : K.Obj → M.ι) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) ∧ (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) ∧ (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ ((show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) ∧ r.coef.pull2 z = GlobalTheory.CatCoh.H2.mk K.Oc ℓ)
 (hframe : ∀ (A : Over (Sp ℂ)) [GrpObj A] {g : ℕ} (L : LB A.left) (u : HolUnif A L g) (M : LB A.left) (u' : HolUnif A M g), M.IsLB → u'.ex = u.ex → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ), u'.IsAH H χ → ∀ (K : Charts (fibFam u)) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V))), r.IsFor (fibUnif u) → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∃ (fr : ∀ k, Hol (K.W k)) (a lg : u.Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) ∧ (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) ∧ (∀ l k, IsUnit (a l k)) ∧ (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) ∧ (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') ∧ (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (algebraMap ℂ (Hol (fibFam u).V) ((Real.pi : ℂ) * ((m : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ)))))) ∧ (∀ l m k, lg (l + m) k = lg l k + lg m k))
 (hlift : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X), M.IsLB → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ (fr : ∀ k, Hol (K.W k)) (a : Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) → (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) → ∀ (i : K.Obj → M.ι), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) → ∀ (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C), (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) → ∃ e : ∀ T : K.Obj, (T.C)ˣ, (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J))
 (halg : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (a lg : Λ → ∀ k, Hol (K.W k)) (β : Λ → Λ → Hol F.V), (∀ l k, IsUnit (a l k)) → (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) → (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') → (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (β l m)) → (∀ l m k, lg (l + m) k = lg l k + lg m k) → ∀ (e : ∀ T : K.Obj, (T.C)ˣ) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C), (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ (ℓ T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) → ∃ c : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg))
 (hcup : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) {n : ℕ} (p q : Fin n → Λ →+ Hol F.V) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc) (c : GlobalTheory.CatCoh.C1 K.Oc) (β : Λ → Λ → Hol F.V), (∑ i, GlobalTheory.CatCoh.cup K.Oc (K.perCl (p i)) (K.perCl (q i))) = GlobalTheory.CatCoh.H2.mk K.Oc ℓ → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show T''.C from ℓ.1 T T' T'' φ ψ) = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg)) → ∃ c' : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), GlobalTheory.CatCoh.d1 K.Oc c' T T' T'' φ ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (∑ i, p i φ.deg * q i ψ.deg - β φ.deg ψ.deg))
 (hsym : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), (∀ c : GlobalTheory.CatCoh.C1 K.Oc, (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → c T T'' (φ ≫ ψ) = GlobalTheory.CatCoh.mp K.Oc ψ (c T T' φ) + c T' T'' ψ) → ∃ G : GlobalTheory.CatCoh.C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → c T T' φ = GlobalTheory.CatCoh.d0 K.Oc G T T' φ) → (∀ G : GlobalTheory.CatCoh.C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → GlobalTheory.CatCoh.mp K.Oc φ (G T) = G T') → ∃ r : Hol F.V, ∀ T, G T = algebraMap (Hol F.V) (K.Oc.obj T) r) → (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') → K.Rich → ∀ (β : Λ →+ Λ →+ Hol F.V) (c : GlobalTheory.CatCoh.C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (β φ.deg ψ.deg)) → ∀ l m, β l m = β m l)
 (hah : ∀ {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ), H.IsHermitian → ∀ x y : Fin g → ℂ, (Real.pi : ℂ) * (y ⬝ᵥ H.mulVec (star x)) - Real.pi * (x ⬝ᵥ H.mulVec (star y)) = (((-1 : ℤˣ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) * ((x ⬝ᵥ H.mulVec (star y)).im : ℂ))
 (h1 : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ (h : GlobalTheory.CatCoh.C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∃ G : GlobalTheory.CatCoh.C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → h T T' φ = G T' - φ.φ (G T))
 (h0 : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ G : GlobalTheory.CatCoh.C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) → ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p) : PChern (-1) := by
  intro A _ g hA L u P hP M u' hM hex H χ ψ hAH hψ x x'
  obtain ⟨n, a, b, hc, rfl⟩ := hψ
  obtain ⟨K, r, j, hR, hS, hF, hj⟩ := hcharts (fibUnif u) (hsep A hA) M.U hM.cover
  have hB : K.Based := by
    obtain ⟨k, hk⟩ := hR.1 (0, 0) trivial
    exact ⟨k, fun z _ ↦ by rwa [Subsingleton.elim z 0]⟩
  obtain ⟨i, uu, ℓ, hi, huu, hℓ, hz⟩ := hpull K r M j hj _ hc
  obtain ⟨fr, af, lg, f1, f2, a1, a2, a3, a4, a5⟩ := hframe A L u M u' hM hex H χ hAH K r hF j hj
  obtain ⟨e, he⟩ := hlift K r M hM j hj fr af f1 f2 i hi uu huu
  let β : u.Λ → u.Λ → ℂ := fun l m ↦ (Real.pi : ℂ) * ((m : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ)))
  obtain ⟨c, hcc⟩ := halg K af lg (fun l m ↦ algebraMap ℂ (Hol (fibFam u).V) (β l m)) a1 a2 a3 a4 a5 e uu ℓ.1 he hℓ
  let pr : primDR A → (u.Λ →+ Hol (fibFam u).V) := fun c ↦
    { toFun x := algebraMap ℂ (Hol (fibFam u).V) (P x c)
      map_zero' := by rw [map_zero, LinearMap.zero_apply, map_zero]
      map_add' x y := by rw [map_add, LinearMap.add_apply, map_add] }
  have hpr : ∀ c : primDR A, r.coef.pull1 c.1 = K.perCl (pr c) := fun c ↦ hP c K r hF
  obtain ⟨c', hc'⟩ := hcup K (fun k ↦ pr (a k)) (fun k ↦ pr (b k)) ℓ c
    (fun l m ↦ algebraMap ℂ (Hol (fibFam u).V) (β l m)) (by
      rw [← hz, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [GlobalTheory.CatCoh.CoefMap.pullCohomologyTwo_cup, hpr, hpr]) hcc
  let δ : u.Λ → u.Λ → ℂ := fun l m ↦ ∑ k, P l (a k) * P m (b k) - β l m
  have d1 : ∀ l l' m, δ (l + l') m = δ l m + δ l' m := fun l l' m ↦ by
    simp only [δ, β, map_add, LinearMap.add_apply, Submodule.coe_add, star_add, Matrix.mulVec_add, dotProduct_add,
      add_mul, Finset.sum_add_distrib]
    ring
  have d2 : ∀ l m m', δ l (m + m') = δ l m + δ l m' := fun l m m' ↦ by
    simp only [δ, β, map_add, LinearMap.add_apply, Submodule.coe_add, add_dotProduct,
      mul_add, Finset.sum_add_distrib]
    ring
  let β' : u.Λ →+ u.Λ →+ Hol (fibFam u).V := AddMonoidHom.mk'
    (fun l ↦ AddMonoidHom.mk' (fun m ↦ algebraMap ℂ (Hol (fibFam u).V) (δ l m)) fun m m' ↦ by rw [d2, map_add])
    fun l l' ↦ AddMonoidHom.ext fun m ↦ by
      change algebraMap ℂ (Hol (fibFam u).V) (δ (l + l') m) = algebraMap ℂ (Hol (fibFam u).V) (δ l m) + algebraMap ℂ (Hol (fibFam u).V) (δ l' m)
      rw [d1, map_add]
  have hs := hsym K (fun c hc ↦ h1 K hR hB c hc) (fun G hG ↦ h0 K hR G fun T T' φ h ↦ (hG T T' φ h).symm) hS hR β' c'
    (fun T T' T'' φ ψ ↦ by
      rw [hc']
      congr 1
      change _ = algebraMap ℂ (Hol (fibFam u).V) (δ φ.deg ψ.deg)
      simp only [δ, map_sub, map_sum, map_mul]
      rfl) x x'
  have hs' : δ x x' = δ x' x := by
    have := congrArg (Hol.ev (W := (fibFam u).V) 0 trivial) hs
    change Hol.ev (W := (fibFam u).V) 0 trivial (algebraMap ℂ _ (δ x x')) = Hol.ev (W := (fibFam u).V) 0 trivial (algebraMap ℂ _ (δ x' x)) at this
    simpa using this
  rw [wedgeForm_apply, ← hah H hAH.1 x x', Finset.sum_sub_distrib]
  simp only [δ, β] at hs'
  have e2 : ∑ k, P x (b k) * P x' (a k) = ∑ k, P x' (a k) * P x (b k) := Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  rw [e2]
  linear_combination hs'

theorem pchern : GlobalTheory.AnPer.PChern (-1) :=
  pchern_of @_root_.GlobalTheory.T.abelianScheme_isSeparated_of_affine_base @_root_.GlobalTheory.T.exists_translationClosed_charts_subordinate_to_cover @_root_.GlobalTheory.T.isCrystallineChern_on_analytic_thickenings @_root_.GlobalTheory.T.exists_frame_factorOfAutomorphy_log @_root_.GlobalTheory.T.exists_units_comparing_lifted_transitions_factor @_root_.GlobalTheory.T.log_cocycle_cohomologous_alt @_root_.GlobalTheory.T.cup_period_classes_sum_const @_root_.GlobalTheory.T.const_biadditive_coboundary_symmetric @GlobalTheory.pi_mul_hermitian_alternation @_root_.GlobalTheory.T.degZeroCocycle_exists_coboundary_of_rich_based @_root_.GlobalTheory.T.exists_holomorphic_param_of_degZero_compatible

end GlobalTheory.AnPer.ChernClause
