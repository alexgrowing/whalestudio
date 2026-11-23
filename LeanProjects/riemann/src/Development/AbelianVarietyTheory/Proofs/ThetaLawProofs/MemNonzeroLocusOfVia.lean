import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyViaIsPullback
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantFromIntersectionUniqueStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAfterDvrExtensionStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsUnitKoszulInvariantOfFiniteClosedFibreZerosStatement

set_option autoImplicit false

section

open Polynomial TensorProduct

namespace GlobalTheory.KeyLine

theorem exists_common_field {F L₁ L₂ : Type} [Field F] [Field L₁] [Field L₂] (a : F →+* L₁) (b : F →+* L₂) :
    ∃ (L : Type) (_ : Field L) (i : L₁ →+* L) (j : L₂ →+* L), i.comp a = j.comp b := by
  letI := a.toAlgebra
  letI := b.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (L₁ ⊗[F] L₂)
  letI := Ideal.Quotient.field m
  refine ⟨L₁ ⊗[F] L₂ ⧸ m, inferInstance, (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := F) (A := L₁) (B := L₂)).toRingHom, ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  congr 1
  exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

theorem mem_range_of_forall_eq {F E : Type} [Field F] [CharZero F] [Field E] (i : F →+* E) (κ : E)
    (h : ∀ (L : Type) [Field L] (g₁ g₂ : E →+* L), g₁.comp i = g₂.comp i → g₁ κ = g₂ κ) : ∃ c, i c = κ := by
  letI := i.toAlgebra
  let D : IntermediateField F E := IntermediateField.adjoin F {κ}
  have key : ∀ (L : Type) [Field L] [Algebra F L] (f₁ f₂ : D →ₐ[F] L), f₁ = f₂ := by
    intro L _ _ f₁ f₂
    obtain ⟨L₁, _, i₁, g₁, e₁⟩ := exists_common_field f₁.toRingHom D.val.toRingHom
    obtain ⟨L₂, _, i₂, g₂, e₂⟩ := exists_common_field f₂.toRingHom D.val.toRingHom
    obtain ⟨L₃, _, j₁, j₂, e₃⟩ := exists_common_field i₁ i₂
    have a₁ : ∀ d : D, i₁ (f₁ d) = g₁ d := fun d => RingHom.congr_fun e₁ d
    have a₂ : ∀ d : D, i₂ (f₂ d) = g₂ d := fun d => RingHom.congr_fun e₂ d
    have a₃ : ∀ d : L, j₁ (i₁ d) = j₂ (i₂ d) := fun d => RingHom.congr_fun e₃ d
    have e : j₁ (g₁ κ) = j₂ (g₂ κ) := h L₃ (j₁.comp g₁) (j₂.comp g₂) (RingHom.ext fun c => by
      have b₁ := a₁ (algebraMap F D c)
      have b₂ := a₂ (algebraMap F D c)
      rw [AlgHom.commutes] at b₁ b₂
      exact (congrArg j₁ b₁.symm).trans ((a₃ _).trans (congrArg j₂ b₂)))
    refine IntermediateField.algHom_ext_of_eq_adjoin F (S := D) rfl fun y hy => ?_
    obtain rfl : y = κ := hy
    refine i₁.injective (j₁.injective ?_)
    exact (congrArg j₁ (a₁ ⟨y, IntermediateField.mem_adjoin_simple_self F y⟩)).trans (e.trans
      ((congrArg j₂ (a₂ ⟨y, IntermediateField.mem_adjoin_simple_self F y⟩)).symm.trans (a₃ _).symm))
  have key' : ∀ (L : Type) [Field L] (f₁ f₂ : D →+* L),
      f₁.comp (algebraMap F D) = f₂.comp (algebraMap F D) → f₁ = f₂ := by
    intro L _ f₁ f₂ hf
    letI := (f₁.comp (algebraMap F D)).toAlgebra
    exact congrArg AlgHom.toRingHom (key L ⟨f₁, fun _ => rfl⟩ ⟨f₂, fun c => (RingHom.congr_fun hf c).symm⟩)
  haveI : IsPurelyInseparable F D := by
    haveI : Nonempty (D →+* AlgebraicClosure E) := ⟨(algebraMap E _).comp D.val.toRingHom⟩
    refine IsPurelyInseparable.of_injective_comp_algebraMap F D (AlgebraicClosure E) fun f₁ f₂ hf => ?_
    exact key' _ f₁ f₂ hf
  obtain ⟨c, hc⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F D
    ⟨κ, IntermediateField.mem_adjoin_simple_self F κ⟩
  exact ⟨c, congrArg Subtype.val hc⟩

theorem exists_lift_fraction {A E : Type} (F : Type) [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F] [Field E]
    (g : A →+* E) (hg : Function.Injective g) : ∃ i : F →+* E, i.comp (algebraMap A F) = g :=
  ⟨IsFractionRing.lift hg, RingHom.ext fun p => IsFractionRing.lift_algebraMap hg p⟩

theorem exists_field_extend {K O : Type} [Field K] [CommRing O] [IsDomain O] (ψ : K[X] →+* O)
    (hψ : Function.Injective ψ) : ∃ (E : Type) (_ : Field E) (ι : O →+* E) (i : RatFunc K →+* E),
      Function.Injective ι ∧ i.comp (algebraMap K[X] (RatFunc K)) = ι.comp ψ := by
  obtain ⟨E, _, ι, hι⟩ : ∃ (E : Type) (_ : Field E) (ι : O →+* E), Function.Injective ι :=
    ⟨FractionRing O, inferInstance, algebraMap _ _, IsFractionRing.injective O (FractionRing O)⟩
  obtain ⟨i, hi⟩ := exists_lift_fraction (RatFunc K) (ι.comp ψ) (hι.comp hψ)
  exact ⟨E, inferInstance, ι, i, hι, hi⟩

theorem exists_localRing (K : Type) [Field K] (a : K) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (ψ : K[X] →+* O) (r : O →+* K)
      (g : O →+* RatFunc K), r.comp ψ = evalRingHom a ∧ RingHom.ker r = IsLocalRing.maximalIdeal O ∧
      g.comp ψ = algebraMap K[X] (RatFunc K) ∧ Function.Injective g := by
  let P : Ideal K[X] := RingHom.ker (evalRingHom a)
  haveI hP : P.IsPrime := RingHom.ker_isPrime _
  have h0 : P ≠ ⊥ := fun h => by
    have : X - C a ∈ P := by simp [P, RingHom.mem_ker]
    rw [h] at this
    exact X_sub_C_ne_zero a this
  let O := Localization.AtPrime P
  haveI : IsDomain O := IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing O := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain K[X] h0 O
  have hr : ∀ y : P.primeCompl, IsUnit (evalRingHom a y) := fun y => Ne.isUnit y.2
  have hg : ∀ y : P.primeCompl, IsUnit (algebraMap K[X] (RatFunc K) y) := fun y =>
    Ne.isUnit fun h => y.2 (by
      rw [(map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).1 h]; exact P.zero_mem)
  have hs : Function.Surjective (IsLocalization.lift (S := O) hr) := fun k =>
    ⟨algebraMap K[X] O (C k), by rw [IsLocalization.lift_eq]; simp⟩
  refine ⟨O, inferInstance, inferInstance, inferInstance, algebraMap K[X] O, IsLocalization.lift hr, IsLocalization.lift hg,
    IsLocalization.lift_comp hr, IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hs),
    IsLocalization.lift_comp hg, ?_⟩
  rw [IsLocalization.lift_injective_iff]
  intro p q
  rw [(IsFractionRing.injective K[X] (RatFunc K)).eq_iff,
    (IsLocalization.injective O P.primeCompl_le_nonZeroDivisors).eq_iff]

theorem exists_eq_C {K : Type} [Field K] [IsAlgClosed K] (c : RatFunc K) (hc : c ≠ 0)
    (h : ∀ (a : K) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ψ : K[X] →+* O) (r : O →+* K)
      (g : O →+* RatFunc K), r.comp ψ = evalRingHom a → RingHom.ker r = IsLocalRing.maximalIdeal O →
      g.comp ψ = algebraMap K[X] (RatFunc K) → Function.Injective g → ∀ (u : O) (e : ℤ), e ≠ 0 → c ^ e = g u → IsUnit u) :
    ∃ k : K, c = algebraMap K[X] (RatFunc K) (C k) := by
  have hq := c.denom_ne_zero
  have hp := RatFunc.num_ne_zero hc
  have key : ∀ (a : K) (p q : K[X]) (e : ℤ), e ≠ 0 → q.eval a ≠ 0 →
      c ^ e = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q → p.eval a ≠ 0 := by
    intro a p q e he hqa hce
    obtain ⟨O, _, _, _, ψ, r, g, hr, hk, hg, hi⟩ := exists_localRing K a
    have hr' : ∀ p, r (ψ p) = p.eval a := fun p => RingHom.congr_fun hr p
    have hg' : ∀ p, g (ψ p) = algebraMap K[X] (RatFunc K) p := fun p => RingHom.congr_fun hg p
    have hu : IsUnit (ψ q) := by
      by_contra hn
      have : ψ q ∈ RingHom.ker r := hk ▸ hn
      exact hqa ((hr' q).symm.trans this)
    obtain ⟨v, hv⟩ := hu
    have := h a O ψ r g hr hk hg hi (ψ p * v⁻¹.val) e he (by
      rw [hce, map_mul, map_units_inv, hv, hg', hg', div_eq_mul_inv])
    have := (isUnit_of_mul_isUnit_left this).map r
    rw [hr'] at this
    exact this.ne_zero
  have hboth : ∀ a : K, c.num.eval a ≠ 0 ∧ c.denom.eval a ≠ 0 := by
    intro a
    have h₁ := key a c.num c.denom 1 one_ne_zero
    have h₂ := key a c.denom c.num (-1) (by norm_num)
    rw [zpow_one, c.num_div_denom] at h₁
    rw [zpow_neg_one, ← inv_div, c.num_div_denom] at h₂
    obtain ⟨u, v, huv⟩ := c.isCoprime_num_denom
    have e := congrArg (eval a) huv
    rw [eval_add, eval_mul, eval_mul, eval_one] at e
    by_cases hd : c.denom.eval a = 0
    · have hn : c.num.eval a ≠ 0 := fun hn => by simp [hn, hd] at e
      exact absurd hd (h₂ hn rfl)
    · exact ⟨h₁ hd rfl, hd⟩
  have hconst : ∀ p : K[X], (∀ a, p.eval a ≠ 0) → ∃ k, p = C k := fun p hp => by
    by_cases hd : p.degree = 0
    · exact ⟨_, eq_C_of_degree_eq_zero hd⟩
    · obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hd
      exact absurd ha (hp a)
  obtain ⟨k, hk⟩ := hconst _ fun a => (hboth a).1
  obtain ⟨k', hk'⟩ := hconst _ fun a => (hboth a).2
  refine ⟨k / k', ?_⟩
  rw [← c.num_div_denom, hk, hk', RatFunc.algebraMap_C, RatFunc.algebraMap_C, RatFunc.algebraMap_C, map_div₀]

theorem eq_of_line {K : Type} [Field K] [CharZero K] [IsAlgClosed K]
    (V : ∀ (R : Type) [CommRing R], (K[X] →+* R) → Rˣ → Prop)
    (hmap : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R']
      (ψ : K[X] →+* R) (g : R →+* R') (κ : Rˣ), V R ψ κ → V R' (g.comp ψ) (Units.map g.toMonoidHom κ))
    (huniq : ∀ (L : Type) [Field L] (ψ : K[X] →+* L) (κ κ' : Lˣ), V L ψ κ → V L ψ κ' → κ = κ')
    (hlift : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ψ : K[X] →+* O) (r : O →+* K) (κ : Kˣ),
      RingHom.ker r = IsLocalRing.maximalIdeal O → V K (r.comp ψ) κ →
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (j : O →+* O') (r' : O' →+* K)
        (u : O'ˣ), Function.Injective j ∧ r'.comp j = r ∧ V O' (j.comp ψ) u)
    (hunit : ∀ (a : K) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ψ : K[X] →+* O) (r : O →+* K)
      (L : Type) [Field L] (g : O →+* L) (κ : Lˣ) (u : O) (e : ℤ), r.comp ψ = evalRingHom a →
      RingHom.ker r = IsLocalRing.maximalIdeal O → Function.Injective g → V L (g.comp ψ) κ → (κ : L) ^ e = g u →
      e ≠ 0 → IsUnit u)
    {a₀ a₁ : K} {κ₀ κ₁ : Kˣ} (h₀ : V K (evalRingHom a₀) κ₀) (h₁ : V K (evalRingHom a₁) κ₁) : κ₀ = κ₁ := by
  let χ : K[X] →+* RatFunc K := algebraMap _ _
  have hχ : Function.Injective χ := IsFractionRing.injective _ _
  haveI : CharZero (RatFunc K) := (RingHom.charZero_iff (χ.comp C).injective).1 inferInstance

  have gen : ∀ (a : K) (κ : Kˣ), V K (evalRingHom a) κ → ∃ (E : Type) (_ : Field E) (i : RatFunc K →+* E) (μ : Eˣ),
      V E (i.comp χ) μ ∧ ∀ k : K, (μ : E) = i (χ (C k)) → (κ : K) = k := by
    intro a κ hκ
    obtain ⟨O, _, _, _, ψ, r, g, hr, hk, hg, hi⟩ := exists_localRing K a
    obtain ⟨O', _, _, _, j, r', u, hj, hr', hu⟩ := hlift O ψ r κ hk (hr ▸ hκ)
    have hψ : Function.Injective ψ := Function.Injective.of_comp (f := g) (by
      rw [← RingHom.coe_comp, hg]; exact hχ)
    obtain ⟨E, _, ι, i, hι, hi'⟩ := exists_field_extend (j.comp ψ) (hj.comp hψ)
    refine ⟨E, inferInstance, i, Units.map ι.toMonoidHom u, ?_, fun k hk => ?_⟩
    · rw [show i.comp χ = _ from hi']
      exact hmap _ _ _ ι u hu
    · have e : (u : O') = j (ψ (C k)) := hι ((show ι u = i (χ (C k)) from hk).trans (RingHom.congr_fun hi' (C k)))
      have h' := hmap _ _ _ r' u hu
      rw [← RingHom.comp_assoc, hr', hr] at h'
      rw [huniq K _ _ _ hκ h']
      change r' u = k
      rw [e]
      exact (RingHom.congr_fun hr' _).trans ((RingHom.congr_fun hr _).trans eval_C)
  obtain ⟨E₀, _, i₀, μ₀, v₀, e₀⟩ := gen a₀ κ₀ h₀
  obtain ⟨E₁, _, i₁, μ₁, v₁, e₁⟩ := gen a₁ κ₁ h₁
  obtain ⟨c, hc⟩ := mem_range_of_forall_eq i₀ μ₀ fun L _ g₁ g₂ hg => by
    have b₁ := hmap _ _ _ g₁ μ₀ v₀
    have b₂ := hmap _ _ _ g₂ μ₀ v₀
    rw [← RingHom.comp_assoc] at b₁ b₂
    rw [hg] at b₁
    exact congrArg Units.val (huniq L _ _ _ b₁ b₂)
  obtain ⟨k, rfl⟩ := exists_eq_C c (fun h => μ₀.ne_zero (by rw [← hc, h, map_zero]))
    fun a O _ _ _ ψ r g hr hk hg hi u e he hu => hunit a O ψ r E₀ (i₀.comp g) μ₀ u e hr hk (i₀.injective.comp hi)
      (by rw [RingHom.comp_assoc, hg]; exact v₀) (by rw [← hc, ← map_zpow₀, hu]; rfl) he
  obtain ⟨L, _, j₀, j₁, hj⟩ := exists_common_field i₀ i₁
  have b₀ := hmap _ _ _ j₀ μ₀ v₀
  have b₁ := hmap _ _ _ j₁ μ₁ v₁
  rw [← RingHom.comp_assoc] at b₀ b₁
  rw [hj] at b₀
  have e : j₀ μ₀ = j₁ μ₁ := congrArg Units.val (huniq L _ _ _ b₀ b₁)
  refine Units.ext ((e₀ k hc.symm).trans (e₁ k (j₁.injective ?_)).symm)
  rw [← e, ← hc]
  exact RingHom.congr_fun hj _

end GlobalTheory.KeyLine

end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyLine

variable {K R R' : Type} [CommRing K] [CommRing R] [CommRing R'] {n : ℕ}

def lineFn {X : Scheme.{0}} {L : LB X} (p : X ⟶ Sp R) (τ : R) (a b : ∀ i, Γ(X, L.U i)) : ∀ i, Γ(X, L.U i) :=
  fun i => AbLaw.cst p _ (1 - τ) * a i + AbLaw.cst p _ τ * b i

theorem via_lineFn {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X} (f : R →+* R') (p : X ⟶ Sp R) (p' : Y ⟶ Sp R')
    (hφ : φ ≫ p = p' ≫ spMap f) {w : LB.Iso L' (L.pull φ)} {l : ℕ} {a' b' : ∀ i, Γ(Y, L'.U i)}
    {a b : ∀ j, Γ(X, L.U j)} (ha : KeyVia.Via w l a' a) (hb : KeyVia.Via w l b' b) (τ : R) :
    KeyVia.Via w l (lineFn p' (f τ) a' b') (lineFn p τ a b) := by
  intro j i h
  simp only [lineFn]
  rw [map_add, map_mul, map_mul, ha j i h, hb j i h, KeyVia.appLE_cst f p p' hφ, KeyVia.appLE_cst f p p' hφ, map_add,
    map_mul, map_mul, rs_cst, rs_cst, map_sub f, map_one f]
  exact (congrArg₂ (· + ·) (mul_left_comm _ _ _) (mul_left_comm _ _ _)).trans (mul_add _ _ _).symm

theorem exists_lineSec {X : Scheme.{0}} {M : LB X} (p : X ⟶ Sp R) (τ : R) (a b : M.Sec) :
    ∃ s : M.Sec, s.f = lineFn p τ a.f b.f := by
  refine ⟨⟨lineFn p τ a.f b.f, fun i j => ?_⟩, rfl⟩
  have ha := a.compat i j
  have hb := b.compat i j
  simp only [lineFn]
  rw [map_add, map_add, map_mul, map_mul, map_mul, map_mul, ha, hb, rs_cst, rs_cst, rs_cst, rs_cst]
  ring

def OnLine (y : KeyIn R) (τ : R) (a b s : RR y n) : Prop :=
  s.f = lineFn (L := y.P.L) y.P.A.hom τ a.f b.f

theorem exists_onLine (y : KeyIn R) (τ : R) (a b : RR y n) : ∃ s, OnLine y τ a b s :=
  exists_lineSec (M := AbLaw.pw y.P.L (n : ℤ)) y.P.A.hom τ a b

theorem secVia_iff_onLine {y : KeyIn R} {y' : KeyIn R'} {g : R →+* R'} {φ w} (H : KeyVia y' y g φ w) {τ : R}
    {a b s : RR y n} {a' b' s' : RR y' n} (ha : SecVia y' y φ w a' a) (hb : SecVia y' y φ w b' b)
    (hs : OnLine y τ a b s) : SecVia y' y φ w s' s ↔ OnLine y' (g τ) a' b' s' := by
  have e := via_lineFn (L := y.P.L) (L' := y'.P.L) (w := w) (l := n) (a := a.f) (b := b.f) (a' := a'.f) (b' := b'.f)
    g y.P.A.hom y'.P.A.hom (keyVia_isPullback H).w ha hb τ
  have e' : KeyVia.Via (L := y.P.L) (L' := y'.P.L) w n (lineFn (L := y'.P.L) y'.P.A.hom (g τ) a'.f b'.f) s.f :=
    (congrArg (KeyVia.Via (L := y.P.L) (L' := y'.P.L) w n _) hs).mpr e
  constructor
  · intro h
    exact KeyVia.Via.unique (L := y.P.L) (L' := y'.P.L) (w := w) (l := n) (a := s.f) (a' := s'.f) y.P.isLB h e'
  · intro h
    exact (congrArg (fun q => KeyVia.Via (L := y.P.L) (L' := y'.P.L) w n q s.f) h).mpr e'

theorem lineFn_zero {X : Scheme.{0}} {L : LB X} (p : X ⟶ Sp R) (a b : ∀ i, Γ(X, L.U i)) : a = lineFn p 0 a b := by
  funext i
  simp only [lineFn, sub_zero, map_one, map_zero, _root_.one_mul, zero_mul, add_zero]

theorem lineFn_one {X : Scheme.{0}} {L : LB X} (p : X ⟶ Sp R) (a b : ∀ i, Γ(X, L.U i)) : b = lineFn p 1 a b := by
  funext i
  simp only [lineFn, sub_self, map_one, map_zero, _root_.one_mul, zero_mul, zero_add]

theorem onLine_zero (y : KeyIn R) (a b : RR y n) : OnLine y 0 a b a := lineFn_zero (L := y.P.L) _ a.f b.f

theorem onLine_one (y : KeyIn R) (a b : RR y n) : OnLine y 1 a b b := lineFn_one (L := y.P.L) _ a.f b.f

theorem mem_nonzeroLocus_of_via {y : KeyIn R} {y' : KeyIn R'} {φ w} {s' : RR y' n} {s : RR y n}
    (hs : SecVia y' y φ w s' s) (z : y'.P.A.left) (hz : z ∈ Out.nonzeroLocus s') : φ z ∈ Out.nonzeroLocus s := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  obtain ⟨k, hk⟩ := exists_chart y.P.isLB (φ z)
  have hle : (y.P.L.pull φ).U (fun _ => k) ⊓ y'.P.L.U i ≤ φ ⁻¹ᵁ y.P.L.U k := fun y hy => mem_pull.1 hy.1
  have e := hs (fun _ => k) i hle
  have hm : z ∈ (y.P.L.pull φ).U (fun _ => k) ⊓ y'.P.L.U i := ⟨mem_pull.2 hk, y'.P.A.left.basicOpen_le _ hi⟩
  have h1 : z ∈ y'.P.A.left.basicOpen ((φ.appLE _ _ hle).hom (s.f k)) := by
    refine (congrArg y'.P.A.left.basicOpen e).ge ((Scheme.basicOpen_mul _ _ _).ge ⟨?_, ?_⟩)
    · exact (Scheme.basicOpen_of_isUnit _ ((Units.isUnit (w.s (fun _ => k, i))).pow n)).ge hm
    · exact (Scheme.basicOpen_res _ _ _).ge ⟨hm, hi⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, ((Scheme.basicOpen_appLE φ _ (y.P.L.U k) hle (s.f k)).le h1).2⟩

variable {x : KeyIn K} (s₀ s₁ : Fin x.P.g → RR x n)

def IsLinePt (f : K →+* R) (τ : R) (y : KeyIn R) (s : Fin y.P.g → RR y n) : Prop :=
  ∃ φ w, ∃ hg : y.P.g = x.P.g, KeyVia y x f φ w ∧ ∀ i, ∃ a b, SecVia y x φ w a (s₀ (i.cast hg)) ∧
    SecVia y x φ w b (s₁ (i.cast hg)) ∧ OnLine y τ a b (s i)

theorem exists_isLinePt (f : K →+* R) (τ : R) : ∃ y s, IsLinePt s₀ s₁ f τ y s := by
  obtain ⟨y, hy⟩ := KeyPow.exists_keyPB_ring x f
  obtain ⟨φ, w, H⟩ := (KeyVia.main _ _ x y f).1.1 hy
  have hp := ((KeyVia.main _ _ x y f).2 φ w H).1 n
  choose a ha using fun i : Fin y.P.g => (hp (s₀ (i.cast (keyVia_g H)))).exists
  choose b hb using fun i : Fin y.P.g => (hp (s₁ (i.cast (keyVia_g H)))).exists
  choose s hs using fun i => exists_onLine y τ (a i) (b i)
  exact ⟨y, s, φ, w, keyVia_g H, H, fun i => ⟨a i, b i, ha i, hb i, hs i⟩⟩

variable {s₀ s₁} {f : K →+* R} {τ : R} {y : KeyIn R} {s : Fin y.P.g → RR y n} {g : R →+* R'} {y' : KeyIn R'}
  {s' : Fin y'.P.g → RR y' n}

theorem IsLinePt.g_eq (h : IsLinePt s₀ s₁ f τ y s) : y.P.g = x.P.g := by
  obtain ⟨_, _, hg, _⟩ := h
  exact hg

theorem IsLinePt.cancel (h : IsLinePt s₀ s₁ f τ y s) (h' : IsLinePt s₀ s₁ (g.comp f) (g τ) y' s') :
    ∃ φ w, ∃ hg : y'.P.g = y.P.g, KeyVia y' y g φ w ∧ ∀ i, SecVia y' y φ w (s' i) (s (i.cast hg)) := by
  obtain ⟨φ, w, hg, H, hs⟩ := h
  obtain ⟨φ'', w'', hg'', H'', hs''⟩ := h'
  obtain ⟨φ', w', H', -, hv⟩ := keyVia_cancel H H''
  refine ⟨φ', w', hg''.trans hg.symm, H', fun i => ?_⟩
  obtain ⟨a, b, ha, hb, hl⟩ := hs (i.cast (hg''.trans hg.symm))
  obtain ⟨a', b', ha', hb', hl'⟩ := hs'' i
  exact (secVia_iff_onLine H' (hv _ _ _ _ ha ha') (hv _ _ _ _ hb hb') hl).2 hl'

theorem IsLinePt.trans (h : IsLinePt s₀ s₁ f τ y s) {φ' w'} (hg' : y'.P.g = y.P.g) (H' : KeyVia y' y g φ' w')
    (hs' : ∀ i, SecVia y' y φ' w' (s' i) (s (i.cast hg'))) : IsLinePt s₀ s₁ (g.comp f) (g τ) y' s' := by
  obtain ⟨φ, w, hg, H, hs⟩ := h
  obtain ⟨w'', H'', hv⟩ := keyVia_trans H H'
  refine ⟨φ' ≫ φ, w'', hg'.trans hg, H'', fun i => ?_⟩
  obtain ⟨a, b, ha, hb, hl⟩ := hs (i.cast hg')
  obtain ⟨a', ha'⟩ := (((KeyVia.main _ _ y y' g).2 φ' w' H').1 n a).exists
  obtain ⟨b', hb'⟩ := (((KeyVia.main _ _ y y' g).2 φ' w' H').1 n b).exists
  exact ⟨a', b', hv _ _ _ _ ha ha', hv _ _ _ _ hb hb', (secVia_iff_onLine H' ha' hb' hl).1 (hs' i)⟩

theorem IsLinePt.via {t : K} (h : IsLinePt s₀ s₁ f (f t) y s) {r : Fin x.P.g → RR x n}
    (hr : ∀ i, OnLine x t (s₀ i) (s₁ i) (r i)) :
    ∃ φ w, ∃ hg : y.P.g = x.P.g, KeyVia y x f φ w ∧ ∀ i, SecVia y x φ w (s i) (r (i.cast hg)) := by
  obtain ⟨φ, w, hg, H, hs⟩ := h
  refine ⟨φ, w, hg, H, fun i => ?_⟩
  obtain ⟨a, b, ha, hb, hl⟩ := hs i
  exact (secVia_iff_onLine H ha hb (hr _)).2 hl

theorem finZ_of_via_id {z : KeyIn K} {φ w} (hg : z.P.g = x.P.g) (H : KeyVia z x (RingHom.id K) φ w)
    {r : Fin x.P.g → RR x n} {r' : Fin z.P.g → RR z n} (hs : ∀ i, SecVia z x φ w (r' i) (r (i.cast hg)))
    (h : FinZ x r) : FinZ z r' := by
  have hp := keyVia_isPullback H
  haveI : IsIso (spMap (RingHom.id K)) := by
    have : spMap (RingHom.id K) = 𝟙 _ := Spec.map_id _
    rw [this]
    infer_instance
  haveI : IsIso φ := hp.isIso_fst_of_isIso
  refine Set.Finite.of_finite_image (f := φ) (h.subset ?_) φ.homeomorph.injective.injOn
  rintro _ ⟨p, hp, rfl⟩ i hi
  exact hp (i.cast hg.symm) (EtBaseChange.mem_nonzeroLocus_via (hs _) p hi)

theorem finite_closedFibre {O k : Type} [CommRing O] [IsLocalRing O] [Field k] {r : O →+* k}
    (hr : RingHom.ker r = IsLocalRing.maximalIdeal O) {z : KeyIn O} {zk : KeyIn k} {φ w} (hg : zk.P.g = z.P.g)
    (H : KeyVia zk z r φ w) {t : Fin z.P.g → RR z n} {tk : Fin zk.P.g → RR zk n}
    (hs : ∀ i, SecVia zk z φ w (tk i) (t (i.cast hg))) (h : FinZ zk tk) :
    {p : z.P.A.left | z.P.A.hom p = IsLocalRing.closedPoint O ∧ ∀ i, p ∉ Out.nonzeroLocus (t i)}.Finite := by
  refine (h.image φ).subset ?_
  rintro p ⟨hp, hz⟩
  have e : spMap r (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint O := by
    apply PrimeSpectrum.ext
    change Ideal.comap r (IsLocalRing.maximalIdeal k) = IsLocalRing.maximalIdeal O
    rw [IsLocalRing.maximalIdeal_eq_bot, ← hr, RingHom.ker_eq_comap_bot]
  obtain ⟨q, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (keyVia_isPullback H) p (IsLocalRing.closedPoint k)
    (hp.trans e.symm)
  exact ⟨q, fun i hi => hz _ (mem_nonzeroLocus_of_via (hs i) q hi), rfl⟩

open Polynomial in

theorem kaVal_eq_of_line : Out.Laws → ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x' : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s₀ s₁ : Fin x'.P.g → RR x' n) (κ₀ κ₁ : Kˣ), admitted x'.P.g n l l' al → (∀ (t : K) (s : Fin x'.P.g → RR x' n), (∀ i c, (show Γ(x'.P.A.left, x'.P.L.U c) from (s i).f c) = AbLaw.cst x'.P.A.hom _ (1 - t) * (show Γ(x'.P.A.left, x'.P.L.U c) from (s₀ i).f c) + AbLaw.cst x'.P.A.hom _ t * (show Γ(x'.P.A.left, x'.P.L.U c) from (s₁ i).f c)) → FinZ x' s) → KaVal x' n l l' al s₀ κ₀ → KaVal x' n l l' al s₁ κ₁ → κ₀ = κ₁ := by
  intro hL K _ _ _ x n l l' al s₀ s₁ κ₀ κ₁ hA hfin h₀ h₁
  let V : ∀ (R : Type) [CommRing R], (K[X] →+* R) → Rˣ → Prop := fun R _ ψ κ =>
    ∃ y s, IsLinePt s₀ s₁ (ψ.comp C) (ψ X) y s ∧ KaVal y n l l' al s κ
  have adm : ∀ {R : Type} [CommRing R] {f : K →+* R} {τ : R} {y : KeyIn R} {s : Fin y.P.g → RR y n},
      IsLinePt s₀ s₁ f τ y s → admitted y.P.g n l l' al := fun h => by rw [h.g_eq]; exact hA
  have hev : ∀ a : K, (evalRingHom a).comp C = RingHom.id K := fun a => RingHom.ext fun _ => eval_C
  have hpt : ∀ (a : K) (r : Fin x.P.g → RR x n) (κ : Kˣ), (∀ i, OnLine x a (s₀ i) (s₁ i) (r i)) →
      KaVal x n l l' al r κ → V K (evalRingHom a) κ := by
    intro a r κ hr hκ
    obtain ⟨y, s, hy⟩ := exists_isLinePt s₀ s₁ (RingHom.id K) a
    obtain ⟨φ, w, hg, H, hs⟩ := IsLinePt.via (t := a) hy hr
    refine ⟨y, s, ?_, GlobalTheory.T.keyInvariant_baseChange hL K K x y _ φ w n l l' al hg r s κ hA H hs hκ⟩
    rw [hev, show evalRingHom a X = a from eval_X]
    exact hy
  refine eq_of_line V ?_ ?_ ?_ ?_ (hpt 0 s₀ κ₀ (fun i => onLine_zero x _ _) h₀)
    (hpt 1 s₁ κ₁ (fun i => onLine_one x _ _) h₁)
  · rintro R R' _ _ _ _ _ ψ g κ ⟨y, s, hy, hκ⟩
    obtain ⟨y', s', hy'⟩ := exists_isLinePt s₀ s₁ (g.comp (ψ.comp C)) (g (ψ X))
    obtain ⟨φ, w, hg, H, hs⟩ := hy.cancel hy'
    exact ⟨y', s', hy', GlobalTheory.T.keyInvariant_baseChange hL R R' y y' g φ w n l l' al hg s s' κ (adm hy) H hs hκ⟩
  · rintro L _ ψ κ κ' ⟨y, s, hy, hκ⟩ ⟨y', s', hy', hκ'⟩
    haveI : CharZero L := (RingHom.charZero_iff (ψ.comp C).injective).1 inferInstance
    obtain ⟨φ, w, hg, H, hs⟩ := hy.cancel (g := RingHom.id L) hy'
    exact GlobalTheory.T.keyInvariantFromIntersection_unique hL L y' n l l' al s' _ _ (adm hy')
      (GlobalTheory.T.keyInvariant_baseChange hL L L y y' _ φ w n l l' al hg s s' κ (adm hy) H hs hκ) hκ'
  · rintro O _ _ _ ψ r κ hr ⟨yk, sk, hyk, zk, chk, -, -, -, -, -, -, -, hE, -⟩
    obtain ⟨y, s, hy⟩ := exists_isLinePt s₀ s₁ (ψ.comp C) (ψ X)
    obtain ⟨φ, w, hg, H, hs⟩ := hy.cancel (g := r) hyk
    have hu : IsUnit ((degProd y.P.g n l l' : ℕ) : O) := by
      obtain ⟨-, h₂, h₃, -⟩ := adm hy
      have hne : degProd y.P.g n l l' ≠ 0 := Finset.prod_ne_zero_iff.2 fun j hj => by
        have : j * n ≤ y.P.g * n := Nat.mul_le_mul_right n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
        exact Nat.mul_ne_zero (by omega) (by omega)
      have := (Ne.isUnit (Nat.cast_ne_zero.2 hne : ((degProd y.P.g n l l' : ℕ) : K) ≠ 0)).map (ψ.comp C)
      rwa [map_natCast] at this
    obtain ⟨O', _, _, _, j, r', y', φ', w', hg', s', u, hj, -, hr', H', hs', hu'⟩ :=
      GlobalTheory.T.exists_keyInvariant_after_dvr_extension hL O K r y yk φ w n l l' al _ hg s sk zk chk hr (adm hy) hu H hs hE
    exact ⟨O', inferInstance, inferInstance, inferInstance, j, r', u, hj, hr', y', s', hy.trans hg' H' hs', hu'⟩
  · rintro a O _ _ _ ψ r L _ g κ u e hψ hr hgi ⟨yL, sL, hyL, hκ⟩ hu he
    letI : Algebra ℚ O := ((ψ.comp C).comp (algebraMap ℚ K)).toAlgebra
    obtain ⟨y, s, hy⟩ := exists_isLinePt s₀ s₁ (ψ.comp C) (ψ X)
    obtain ⟨φ, w, hg, H, hs⟩ := hy.cancel (g := g) hyL
    obtain ⟨yk, sk, hyk⟩ := exists_isLinePt s₀ s₁ (RingHom.id K) a
    choose t ht using fun i => exists_onLine x a (s₀ i) (s₁ i)
    obtain ⟨φ₀, w₀, hg₀, H₀, hs₀⟩ := IsLinePt.via (t := a) hyk ht
    have hk := finZ_of_via_id hg₀ H₀ hs₀ (hfin a t fun i c => congrFun (ht i) c)
    obtain ⟨φ₁, w₁, hg₁, H₁, hs₁⟩ := hy.cancel (g := r) (y' := yk) (s' := sk) (by
      rw [← RingHom.comp_assoc, hψ, hev, show r (ψ X) = a from (RingHom.congr_fun hψ X).trans eval_X]
      exact hyk)
    exact GlobalTheory.T.isUnit_koszulInvariant_of_finite_closedFibre_zeros hL O L g y yL φ w n l l' al hg s sL κ u e hgi (adm hy) H hs
      (finite_closedFibre hr hg₁ H₁ hs₁ hk) hκ hu he

end GlobalTheory.KeyLine
