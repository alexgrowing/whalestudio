import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmSpMapUnitOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishTorsion
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIsoRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionNe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.Coef

section Core

open GlobalTheory.UT GlobalTheory.UT.SymFrame ReciprocityTheory.ChartRestriction.G.DVR

variable {V₁ W₀ K : Type} [CommRing V₁] [IsDomain V₁] [CommRing W₀] [Field K] [IsAlgClosed K] {D : DegPre V₁}
  {B₀ : Over (Sp W₀)} [GrpObj B₀] {f : W₀ →+* V₁} {q : Fin 8 → (D.P.A.left ⟶ B₀.left)} {ev : V₁ →+* K} {k₀ : Subfield K}
  {X₂ : Scheme.{0}} {L₂ : LB X₂} {I : Type} [Fintype I] {π : I → (D.P.A.left ⟶ X₂)} {e : I → ℤ}
  {u : LB.Iso D.P.L (LB.LinComb L₂ π e)}

theorem step [IsLocalRing V₁] [IsNoetherianRing V₁] [IsIntegrallyClosed V₁] (H : Desc f q ev k₀ u) {N : ℕ} (hN : 1 ≤ N)
    (htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ N = 1 → RatP q k₀ x.left)
    (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (g : GtPtF D (FractionRing V₁)) (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A)
    (hgb : g.b = toUnit _ ≫ b) (ho : ∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) (w : Frm D (FractionRing V₁) 1 g.b)
    (hw : w.IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J = 1) (χ : D.X)
    (hχ : RatP q k₀ (toUnit (Over.mk (spMap ev)) ≫ D.c χ).left)
    (t₃ : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (h₃ : t₃.IsGen)
    (m₃ : ∀ (z : Sp K) J J₂, Good D.P.L z J → Good L₂ z J₂ → ∃ c ∈ k₀,
      ((om (Z := Sp K) u z J J₂ (toUnit (Over.mk (spMap ev)) ≫ D.c χ).left)⁻¹ *
        val (Z := Sp K) t₃ (toUnit (Over.mk (spMap ev))).left z J).val = toStk z c) :
    ∃ R : V₁, (∀ z J, Good D.P.L z J → sval θ (cP D _ χ * g.b).left z J * (val (g.s χ) (𝟙 _) z J).val *
        (val w (𝟙 _) z J).val * (val t₃ (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val =
          cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) R)) ∧
      ∀ (z : Sp K) J J₂, Good D.P.L z J → Good L₂ z J₂ → ∃ c ∈ k₀, c ≠ 0 ∧ toStk z (ev R) = toStk z c *
        ((om (Z := Sp K) u z J J₂ (toUnit (Over.mk (spMap ev)) ≫ (D.c χ * b)).left).val *
          sval (Z := Sp K) θ (toUnit (Over.mk (spMap ev)) ≫ (D.c χ * b)).left z J) := by
  obtain ⟨t₁, h₁⟩ := exists_gen_of_local D.P.L D.P.isLB
    ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left] DegPre.gtε
  obtain ⟨t₂, h₂⟩ := exists_gen_of_local D.P.L D.P.isLB ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)
  obtain ⟨a₁, g₁, m₁⟩ := char_mem H hN htor g b hgb ho χ hχ t₁ h₁
  obtain ⟨a₂, g₂, m₂⟩ := frame_mem H hN htor g b hgb ho w hw t₂ h₂
  obtain ⟨G, hG, vG⟩ := (((grep_gen (Y := 𝟙_ (Over (Sp V₁))) t₁ h₁ (𝟙 _)).mul (grep_gen t₂ h₂ (𝟙 _))).mul
    (grep_gen t₃ h₃ (𝟙 _))).inv.out D.P.isLB (fun k => (D.c χ * b).left ≫ D.famφB 0 k) (DegPre.famε 1) (fun U _ h => by
      rw [prod_gt (Z := Sp K), prod_ln, prod_famφB_zero, Fintype.prod_unique, Category.id_comp, zpow_neg_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  obtain ⟨x, hx⟩ := GlobalTheory.TwistUnit.exists_ratio_local D.P.isLB (H1.SectionArithmetic.pullSec θ (D.c χ * b).left) G hG
  have key : ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
      sval θ (toUnit T ≫ (D.c χ * b)).left z J * (val t₁ (toUnit T).left z J * val t₂ (toUnit T).left z J *
        val t₃ (toUnit T).left z J).val = gs (toUnit T).left z ⊤ x := fun T z J hJ => by
    have e₁ := (H1.SectionArithmetic.sval_pullSec θ (D.c χ * b).left (toUnit T).left z hJ).symm.trans (hx _ (toUnit T).left z J hJ)
    have e₂ := vG T (toUnit T) z J hJ
    simp only [Category.comp_id] at e₂
    refine (congrArg (· * _) (e₁.trans (congrArg (fun t => _ * Units.val t) e₂))).trans ?_
    rw [_root_.mul_assoc]
    erw [Units.inv_mul, _root_.mul_one]
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V₁)).hom.hom x * a₁ * a₂, fun z J hJ => ?_, fun z J J₂ hJ hJ₂ => ?_⟩
  · have e₁ := (key _ z J hJ).trans (gs_gen x z)
    have e₂ : cP D _ χ * g.b = toUnit (TF (R := V₁) (FractionRing V₁)) ≫ (D.c χ * b) := by
      rw [hgb, MonObj.comp_mul]; rfl
    rw [e₂, g₁ z J hJ, g₂ z J hJ]
    simp only [CoefBasic.cst_eq, map_mul, Units.val_mul] at e₁ ⊢
    rw [← e₁]
    ring
  · have e₁ := (key (Over.mk (spMap ev)) z J hJ).trans (gs_ev ev x z)
    obtain ⟨c₁, hc₁, n₁⟩ := m₁ z J J₂ hJ hJ₂
    obtain ⟨c₂, hc₂, n₂⟩ := m₂ z J J₂ hJ hJ₂
    obtain ⟨c₃, hc₃, n₃⟩ := m₃ z J J₂ hJ hJ₂
    have ne : ∀ {c : K} {s : (Sp K).presheaf.stalk z}, IsUnit s → s = toStk z c → c ≠ 0 := by
      rintro c s hs e rfl
      rw [e, map_zero] at hs
      exact not_isUnit_zero hs
    refine ⟨c₁ * c₂ * c₃, k₀.mul_mem (k₀.mul_mem hc₁ hc₂) hc₃, mul_ne_zero (mul_ne_zero
      (ne (((a₁.isUnit.map ev).map _).mul (Units.isUnit _)) n₁) (ne (((a₂.isUnit.map ev).map _).mul (Units.isUnit _)) n₂))
      (ne (Units.isUnit _) n₃), ?_⟩
    have alg : ∀ {S : Type} [CommRing S] (p c b o v₁ v₂ v₃ : Sˣ) (s a₁ a₂ : S),
        s * (v₁ * v₂ * v₃).val * a₁ * a₂ = a₁ * (p⁻¹ * c * b * o⁻¹ * v₁).val * (a₂ * (o * b⁻¹ * v₂).val) *
          (c⁻¹ * v₃).val * (p.val * s) := by
      intro S _ p c b o v₁ v₂ v₃ s a₁ a₂
      have : v₁ * v₂ * v₃ = (p⁻¹ * c * b * o⁻¹ * v₁) * (o * b⁻¹ * v₂) * (c⁻¹ * v₃) * p := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [this]
      generalize p⁻¹ * c * b * o⁻¹ * v₁ = A
      generalize o * b⁻¹ * v₂ = B
      generalize c⁻¹ * v₃ = C
      simp only [Units.val_mul]
      ring
    simp only [map_mul]
    rw [← n₁, ← n₂, ← n₃, ← e₁]
    exact alg _ _ _ _ _ _ _ _ _ _

theorem core [IsLocalRing V₁] (hV : IsCN V₁) (H : Desc f q ev k₀ u) {N : ℕ} (hN : 2 ≤ N) (hNK : (N : K) ≠ 0)
    (htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ N = 1 → RatP q k₀ x.left)
    {X C : Type} [AddCommGroup X] (eX : X ≃+ D.X) (T : X → C → V₁) (hT : IsThetaTerms D N eX T)
    (hc : ∀ mu, RatP q k₀ (toUnit (Over.mk (spMap ev)) ≫ D.c (eX mu)).left) (y : X → FractionRing V₁) (hy : y 0 = 1)
    (hψ : ∀ mu, ∃ t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c (eX mu)).left) (fun _ => -1)), t.IsGen ∧
      (∀ (z : (TF (R := V₁) (FractionRing V₁)).left) J, Good D.P.L z J →
        (val (D.psi (eX mu)) (jFK (R := V₁) (FractionRing V₁)) z J).val =
          (val t (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val * cst (FractionRing V₁) z (y mu)) ∧
      ∀ (z : Sp K) J J₂, Good D.P.L z J → Good L₂ z J₂ → ∃ c ∈ k₀,
        ((om (Z := Sp K) u z J J₂ (toUnit (Over.mk (spMap ev)) ≫ D.c (eX mu)).left)⁻¹ *
          val (Z := Sp K) t (toUnit (Over.mk (spMap ev))).left z J).val = toStk z c) (mu : X) (c : C) :
    ∃ R R₀ : V₁, algebraMap V₁ (FractionRing V₁) (T mu c * R₀) = algebraMap V₁ (FractionRing V₁) R * y mu ∧
      ev R₀ ≠ 0 ∧ ∃ r ∈ k₀, ev R = r * ev R₀ := by
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅, c₀, h₆⟩ := hT
  obtain ⟨θ, hθ, hnz, hlam, -, -⟩ := ThetaOne.main hV D
  obtain ⟨lam, hlam, -⟩ := hlam (FractionRing V₁) th
  choose t ht gt mt using hψ
  choose R gR mR using fun mu c => step H (by omega) htor θ (g c) (b c) (h₁ c) (h₂ c) (w c) (h₄ c) (eX mu) (hc mu) (t mu)
    (ht mu) (mt mu)
  obtain ⟨κ, hκ, hθκ⟩ := theta_mem H θ (hθ K ev)
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := V₁) (F := FractionRing V₁)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.P.isLB z
  have gen : ∀ mu c, CoefBasic.cstH z (algebraMap V₁ (FractionRing V₁) (T mu c)) *
      (rigV D (TF (R := V₁) (FractionRing V₁)).hom z J).val =
      cst (FractionRing V₁) z lam * (@id ((TF (R := V₁) (FractionRing V₁)).left.presheaf.stalk z)ˣ
        (val (D.psi 0) (jFK (R := V₁) (FractionRing V₁)) z J))⁻¹.val *
        CoefBasic.cstH z (algebraMap V₁ (FractionRing V₁) (R mu c) * y mu) := fun mu c => by
    have e₁ := h₅ mu c z J hJ
    rw [pow_one, term_val D _ th θ lam hlam _ _ z J hJ, Units.val_mul] at e₁
    have e₂ : (@id ((TF (R := V₁) (FractionRing V₁)).left.presheaf.stalk z)ˣ
      (val (D.psi (eX mu)) (jFK (R := V₁) (FractionRing V₁)) z J)).val = _ := gt mu z J hJ
    rw [map_mul, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq, e₁, e₂, ← gR mu c z J hJ]
    ring
  have rel : ∀ mu c, algebraMap V₁ (FractionRing V₁) (T mu c * R 0 c₀) =
      algebraMap V₁ (FractionRing V₁) (R mu c) * y mu := fun mu c => by
    have e₀ := gen 0 c₀
    rw [h₆, hy, map_one, map_one, _root_.one_mul, _root_.mul_one] at e₀
    have e₁ := gen mu c
    refine CoefBasic.cstH_inj z ((rigV D (TF (R := V₁) (FractionRing V₁)).hom z J).isUnit.mul_right_cancel ?_)
    rw [map_mul, map_mul]
    linear_combination CoefBasic.cstH z (algebraMap V₁ (FractionRing V₁) (R 0 c₀)) * e₁ -
      CoefBasic.cstH z (algebraMap V₁ (FractionRing V₁) (R mu c) * y mu) * e₀
  let zK : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  obtain ⟨JK, hJK⟩ := CoefBasic.exists_good' D.P.isLB zK
  obtain ⟨J₂, hJ₂⟩ := CoefBasic.exists_good' H.hL₂ zK
  have inK : ∀ mu c, ∃ r ∈ k₀, ev (R mu c) = κ * r := fun mu c => by
    obtain ⟨r, hr, -, e₁⟩ := mR mu c zK JK J₂ hJK hJ₂
    obtain ⟨r', hr', e₂⟩ := hθκ (toUnit _ ≫ (D.c (eX mu) * b c)) (by
      rw [MonObj.comp_mul]
      refine ratP_mul H.hP H.hk (hc mu) (htor _ ?_)
      rw [← MonObj.comp_pow, (Frames.torsion_of_nsmul (g c) (b c) (h₁ c) (h₂ c)).2, MonObj.comp_one]) zK JK J₂ hJK hJ₂
    rw [e₂, ← map_mul] at e₁
    exact ⟨r * r', k₀.mul_mem hr hr', ((toStk zK).injective e₁).trans (mul_left_comm _ _ _)⟩
  have ne : ev (R 0 c₀) ≠ 0 := fun h0 => by
    obtain ⟨p, hp, hne⟩ := exists_torsion_ne D ev θ (hnz K ev) N hN hNK
    obtain ⟨c₁, rfl⟩ := h₃ K (spMap ev) p hp
    obtain ⟨r, -, hr, e₁⟩ := mR 0 c₁ zK JK J₂ hJK hJ₂
    have e₂ := rel 0 c₁
    rw [hy, _root_.mul_one] at e₂
    rw [← IsFractionRing.injective V₁ (FractionRing V₁) e₂, map_mul, h0, mul_zero, map_zero, map_zero eX, ThetaOne.c_zero,
      _root_.one_mul] at e₁
    have u₁ : IsUnit (toStk zK r) := (IsUnit.mk0 r hr).map _
    exact hne zK JK hJK ((Units.mul_right_eq_zero _).1 (u₁.mul_right_eq_zero.1 e₁.symm))
  obtain ⟨r, hr, e₁⟩ := inK mu c
  obtain ⟨r₀, hr₀, e₀⟩ := inK 0 c₀
  have h0 : r₀ ≠ 0 := by
    rintro rfl
    exact ne (e₀.trans (mul_zero _))
  refine ⟨R mu c, R 0 c₀, rel mu c, ne, r / r₀, k₀.div_mem hr hr₀, ?_⟩
  rw [e₁, e₀]
  field_simp

end Core

section Main

open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem prod_split {V₁ : Type} [CommRing V₁] [IsDomain V₁] {m N : ℕ} (s : Fin m ⊕ Fin N → V₁) (n : Fin m ⊕ Fin N → ℤ)
    (σ : Fin N → V₁ˣ) (hσ : ∀ k, (σ k : V₁) = s (.inr k)) (hn : ∀ k, 0 ≤ n (.inl k)) :
    ∏ i : Fin (m + N), algebraMap V₁ (FractionRing V₁) (s (finSumFinEquiv.symm i)) ^ n (finSumFinEquiv.symm i) =
      algebraMap V₁ (FractionRing V₁) ((∏ k, s (.inl k) ^ (n (.inl k)).toNat) * (∏ k, σ k ^ n (.inr k)).val) := by
  rw [Equiv.prod_comp finSumFinEquiv.symm (fun i => algebraMap V₁ (FractionRing V₁) (s i) ^ n i), Fintype.prod_sum_type,
    map_mul, map_prod, Units.coe_prod, map_prod]
  congr 1
  · exact Finset.prod_congr rfl fun k _ => by rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (hn k)]
  · refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hσ]
    exact ((congrArg Units.val (map_zpow (Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom) (σ k) _)).trans
      (Units.val_zpow_eq_zpow_val _ _)).symm

theorem coef_monomial : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (τ₀ : Gens Q) (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X), (∀ k, IsUnit (s (.inr k))) → (∀ k mu, 0 ≤ qW W (ε (.inl k)) mu) → TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → (∀ mu, mo mu = mono W (fun k => ρ (s (.inl k))) (fun k => ε (.inl k)) mu) → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V), FromBase Q τ₀ ib → (∀ a, ev (ρ (ib a)) ∈ k₀) → ∀ mu c, ∃ r ∈ k₀, ev (u mu c) = r * ∏ k, ev (ρ (s (.inr k))) ^ qW W (ε (.inr k)) mu := by
  intro g l hl _ W _
  refine ⟨1, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hV hlu Q _ ρ hρ D e hS C u mo hmo hT K _ _ ev k₀ hk₀ τ₀ m N s ε hs hε hτ hmono W₀ _ ib hB hk mu c
  haveI : IsNoetherianRing V₁ := hV.1
  obtain ⟨pr, w, hpr, huniv, hw, hc, B₀, iG, iC, M₀, c₀, τ₁, β, β₂, w₀, -, hM₀, hβ, hsq, hw₀, hβc, hτ₁, -, hψ⟩ :=
    PsiMono.psi_val_of W Q ρ hρ D e hS τ₀ _ _ hτ ib hB
  obtain ⟨Ω, hΩ, vΩ⟩ := exists_omega W ρ Q D pr B₀ β₂ w hw M₀ hM₀ w₀ hw₀
  have hN : 2 ≤ (l ^ j) ^ 2 := hl.two_le.trans ((Nat.le_self_pow (by omega) l).trans (Nat.le_self_pow (by omega) _))
  have hNu : IsUnit (((l ^ j) ^ 2 : ℕ) : V₁) := by push_cast; exact (hlu.pow _).pow _
  have htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ ((l ^ j) ^ 2) = 1 →
      RatP (fun a => (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) k₀ x.left := fun x hx a =>
    sharp_torsion_defOver ρ ib Q D pr hpr huniv B₀ β hβ K ev k₀ hk₀ hk _ (by omega) hNu x hx a
  have h2 : spMap (ρ.comp ib) = spMap ρ ≫ spMap ib := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have H : Desc (ρ.comp ib) (fun a => (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) ev k₀ Ω :=
    ⟨hk₀, fun T g hg => exists_points_equiv ρ ib Q D pr hpr huniv B₀ β hβ T.hom g (h2 ▸ hg), hk, hM₀, hΩ,
      piB_congr ρ Q D pr B₀ β₂ hsq, htor 1 (one_pow _)⟩
  obtain ⟨R, R₀, e₁, hne, r, hr, e₂⟩ := core hV H hN (by simpa using (hNu.map ev).ne_zero) htor e _ hT
    (fun mu a => sharp_c_defOver ρ ib Q D e pr hc B₀ β c₀ hβc K ev k₀ hk mu a)
    (fun mu => ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s (finSumFinEquiv.symm i))) ^ qW W (ε (finSumFinEquiv.symm i)) mu)
    (by simp [qW]) (fun mu => by
      obtain ⟨t, ht, vt⟩ := exists_psi_gen W ρ Q D pr B₀ β₂ hM₀ hsq Ω hΩ (spMap ρ ≫ spMap ib) (D.c (e mu))
        (fun a => c₀ (mu a)) (fun a => by
          have := congrArg (· ≫ β) (hc mu a)
          simp only [Category.assoc, Over.comp_left, hβc] at this ⊢
          exact this) (fun a b => τ₁ (mu a) (mu b)) (fun a b => hτ₁ _ _)
      refine ⟨t, ht, fun z J hJ => ?_, fun z J J₂ hJ hJ₂ => ?_⟩
      · obtain ⟨JQ, hJQ⟩ := CoefBasic.exists_good' Q.M.isLB z
        obtain ⟨J₀, hJ₀⟩ := CoefBasic.exists_good' hM₀ z
        obtain ⟨y, hy, ey⟩ := hψ mu z JQ J J₀ hJQ hJ hJ₀
        have j1 : jFK (R := V₁) (FractionRing V₁) = 𝟙 _ := Spec.map_id _
        have t1 : (toUnit (TF (R := V₁) (FractionRing V₁))).left = (toUnit (TK V₁)).left := by
          show jFK (R := V₁) (FractionRing V₁) ≫ jK V₁ = jK V₁
          rw [j1]; exact Category.id_comp _
        have et := vt (TK V₁) z J J₀ hJ hJ₀
        rw [vΩ _ _ z J JQ J₀ hJ hJQ hJ₀] at et
        have pe : ∀ a b, (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ sharpPair ρ Q D pr a b =
            (lift (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu b))).left := by
          have k : ∀ a, (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) =
              (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu a)).left := fun a => by
            show (jK V₁ ≫ (D.c (e mu)).left) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) =
              (PsiMono.fracPt ρ hρ ≫ jK V) ≫ (Q.c (mu a)).left
            rw [PsiMono.fracPt_comp]
            exact (Category.assoc _ _ _).trans ((congrArg (jK V₁ ≫ ·) (hc mu a)).trans (Category.assoc _ _ _).symm)
          intro a b
          have hP := isGrpPullback_pullback Q.B (spMap ρ)
          apply pullback.hom_ext
          · refine Eq.trans ?_ ((k a).trans (congrArg (fun m => m.left) (lift_fst
              (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu b)))).symm)
            exact (Category.assoc _ _ _).trans (congrArg (fun m => (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ m.left)
              (lift_fst (pushPt hP.1.w (pr a)) (pushPt hP.1.w (pr b))))
          · refine Eq.trans ?_ ((k b).trans (congrArg (fun m => m.left) (lift_snd
              (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (PsiMono.fracOver ρ hρ) ≫ Q.c (mu b)))).symm)
            exact (Category.assoc _ _ _).trans (congrArg (fun m => (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ m.left)
              (lift_snd (pushPt hP.1.w (pr a)) (pushPt hP.1.w (pr b))))
        have ge : (TK V₁).hom ≫ spMap ρ ≫ spMap ib = (PsiMono.fracPt ρ hρ ≫ jK V) ≫ spMap ib := by
          rw [PsiMono.fracPt_comp]; exact (Category.assoc _ _ _).symm
        simp only [pe, ge] at et
        simp only [mul_zpow, Finset.prod_mul_distrib] at ey
        rw [j1, t1, ← hy]
        refine (congrArg Units.val (ey.trans (congrArg (· * _) ((_root_.mul_assoc _ _ _).symm.trans et.symm)))).trans ?_
        exact (Units.val_mul _ _).trans (congrArg₂ (· * ·) rfl (gs_unit _ _ ⊤ trivial _).symm)
      · have et := vt (Over.mk (spMap ev)) z J J₂ hJ hJ₂
        obtain ⟨x, hx, ex⟩ := prod_mem (k₀ := k₀) (z := z) Finset.univ (fun a => prod_mem Finset.univ fun b =>
          zpow_mem (val_spMap_mem k₀ (τ₁ (mu a) (mu b)) ((ev.comp ρ).comp ib) hk z hJ₂) (W a b))
        refine ⟨x, hx, Eq.trans (congrArg Units.val ?_) ex⟩
        rw [← spMap_three]
        exact inv_mul_eq_iff_eq_mul.2 et) mu c
  refine ⟨r, hr, ?_⟩
  have e₃ := prod_split (fun i => ρ (s i)) (fun i => qW W (ε i) mu) (fun k => ((hs k).map ρ).unit) (fun _ => rfl)
    (fun k => hε k mu)
  rw [e₃, ← map_mul] at e₁
  have e₄ := IsFractionRing.injective V₁ (FractionRing V₁) e₁
  have e₅ : ∏ k, ρ (s (.inl k)) ^ (qW W (ε (.inl k)) mu).toNat = mo mu := (hmono mu).symm
  rw [e₅] at e₄
  have e₆ : u mu c * R₀ = R * (∏ k, ((hs k).map ρ).unit ^ qW W (ε (.inr k)) mu).val :=
    mul_left_cancel₀ (hmo mu).1 (by linear_combination e₄)
  have e₇ : ev (∏ k, ((hs k).map ρ).unit ^ qW W (ε (.inr k)) mu).val =
      ∏ k, ev (ρ (s (.inr k))) ^ qW W (ε (.inr k)) mu := by
    rw [Units.coe_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => (congrArg Units.val (map_zpow (Units.map ev.toMonoidHom) _ _)).trans
      (Units.val_zpow_eq_zpow_val _ _)
  have e₈ := congrArg ev e₆
  rw [map_mul, map_mul, e₇, e₂] at e₈
  exact mul_right_cancel₀ hne (by linear_combination e₈)

end Main

end GlobalTheory.Poinc.Sep.Coef
