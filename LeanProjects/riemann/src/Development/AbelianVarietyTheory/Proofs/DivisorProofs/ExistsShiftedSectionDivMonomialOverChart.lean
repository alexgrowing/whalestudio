import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentFormsSymmOfIsUnitTauOnToricChartStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ShiftUnitPart

open ReciprocityTheory.ChartRestriction.G.DVR

theorem good_comp' {X Y Z : Scheme.{0}} {L : LB X} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => by
  have := hJ (r ≫ ψ)
  rwa [Scheme.Hom.comp_apply] at this

theorem gs_comp_stalk' {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ h) z U a = (r.stalkMap z).hom (gs h (r z) U a) := by
  rw [← gs_pull r h z U hU, gs_eq r z (h ⁻¹ᵁ U) hU, gs_eq h (r z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply r (h ⁻¹ᵁ U) z hU _).symm

theorem gm_comp_stalk' {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (r z) ∈ U)
    (a : Γ(X, U)ˣ) : (gm (r ≫ h) z U a).val = (r.stalkMap z).hom (gm h (r z) U a).val := by
  rw [← gs_unit _ _ _ hU, ← gs_unit (r ≫ h) z U (by rwa [Scheme.Hom.comp_apply])]
  exact gs_comp_stalk' r h z U hU _

theorem val_comp_stalk' {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    (val t (r ≫ h) z J).val = (r.stalkMap z).hom (val t h (r z) (fun ψ => J (r ≫ ψ))).val := by
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc]),
    val_of t h (r z) (fun ψ => J (r ≫ ψ)) (fun k => J (r ≫ h ≫ φ k)) (fun k => rfl)]
  have hm : (r ≫ h) z ∈ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) := Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  exact (gs_unit _ z _ hm _).symm.trans ((gs_comp_stalk' r h z _ hm _).trans (congrArg _ (gs_unit h (r z) _ hm _)))

theorem val_transport {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (c : Γ(Y, ⊤)ˣ) (h : ∀ y J, Good L y J → val t (𝟙 Y) y J = gm (𝟙 Y) y ⊤ c * val t' (𝟙 Y) y J)
    (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) : val t r z J = gm r z ⊤ c * val t' r z J := by
  apply Units.ext
  have e1 := val_comp_stalk' t (𝟙 Y) r z hJ
  have e2 := val_comp_stalk' t' (𝟙 Y) r z hJ
  have e3 := gm_comp_stalk' r (𝟙 Y) z ⊤ trivial c
  simp only [Category.comp_id] at e1 e2 e3
  rw [Units.val_mul, e1, e2, e3, h _ _ (good_comp' r z hJ), Units.val_mul, map_mul]

section Gen
variable {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R)

theorem prod_famB (ρ : Q.P.A ⟶ Q.P.A) (α : Q.X) (k : ℕ) {U : Type} [CommGroup U] (h : (Q.P.A.left ⟶ Q.P.A.left) → U) :
    ∏ i, h (ρ.left ≫ Q.famφB α i) ^ DegPre.famε k i =
      h ρ.left ^ ((k : ℤ) - 1) * h (ρ * cP Q _ α).left * (h (cP Q _ α).left)⁻¹ * h (1 : Q.P.A ⟶ Q.P.A).left := by
  have e₀ : ρ.left ≫ Q.famφB α 0 = ρ.left := Category.comp_id _
  have e₁ : ρ.left ≫ Q.famφB α 1 = (ρ * cP Q _ α).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (𝟙 _) (cP Q _ α)).trans (by rw [Category.comp_id, comp_cP]))
  have e₂ : ρ.left ≫ Q.famφB α 2 = (cP Q _ α).left := congrArg (fun q => q.left) (comp_cP Q ρ α)
  have e₃ : ρ.left ≫ Q.famφB α 3 = (1 : Q.P.A ⟶ Q.P.A).left :=
    congrArg (fun q : Q.P.A ⟶ Q.P.A => q.left) (MonObj.comp_one (M := Q.P.A) ρ)
  rw [Fin.prod_univ_four, e₀, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]

theorem exists_U (e : ℕ) (mu α : Q.X) {Kv : Type} [Fintype Kv]
    {φv : Kv → ((𝟙_ (Over (Spec (CommRingCat.of R)))).left ⟶ Q.P.A.left)} {εv : Kv → ℤ}
    (v : LB.Gen (LB.LinComb Q.P.L φv εv)) (hv : v.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : ((𝟙_ (Over (Spec (CommRingCat.of R)))).left ⟶ Q.P.A.left) → U),
      ∏ i, h (φv i) ^ εv i = (h (cP Q _ (mu + α)).left)⁻¹ * h (cP Q _ mu).left * h (cP Q _ α).left *
        (h (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Q.P.A).left)⁻¹ * (h (cP Q _ mu).left ^ e)⁻¹ *
        h (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Q.P.A).left ^ e)
    (σ : Q.SecB e α) :
    ∃ σ₁u : Q.SecB e (α + e • mu), ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ Q.P.A) (z : T.left)
      (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J →
      sval σ₁u ρ.left z J = sval σ (ρ ≫ (𝟙 Q.P.A * cP Q _ mu)).left z J *
        (cubN (cubV Q.cub z J) e (ρ ≫ cP Q _ α) (ρ ≫ cP Q _ mu) ρ *
          (cubV Q.cub z J (ρ ≫ cP Q _ α) ρ (ρ ≫ cP Q _ mu))⁻¹ * val v (ρ ≫ toUnit _).left z J).val := by
  obtain ⟨a, ha⟩ : ∃ a : Q.P.A ⟶ Q.P.A, cP Q _ α = a := ⟨_, rfl⟩
  obtain ⟨mm, hmm⟩ : ∃ mm : Q.P.A ⟶ Q.P.A, cP Q _ mu = mm := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : Q.P.A ⟶ Q.P.A, 𝟙 Q.P.A = x := ⟨_, rfl⟩
  rw [ha, hmm, hx]
  obtain ⟨N, hN, vN⟩ := exists_cubN Q.cub a mm x e
  let U := LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ N (LB.invGen Q.P.L _ _
      (LB.pullGen Q.P.L (thφ Q.P.A (x3 Q.P.A)) thε Q.cub.t (lift a (lift x mm)).left)))
    (LB.pullGen Q.P.L _ _ v (toUnit Q.P.A).left)
  have hU : U.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ Q.cub.isGen _))) (pullGen_isGen _ _ _ _ hv _)
  have c₁ : x * mm * a = a * x * mm := by rw [mul_comm, ← _root_.mul_assoc]
  have c₂ : mm * x = x * mm := mul_comm _ _
  have c₃ : cP Q Q.P.A (mu + α) = a * mm := by rw [cPoint_add, ha, hmm, mul_comm]
  have c₄ : cP Q Q.P.A (α + e • mu) = a * mm ^ e := by rw [cPoint_add, cPoint_nsmul, ha, hmm]
  have c₅ : x * (a * mm ^ e) = a * mm ^ e * x := mul_comm _ _
  obtain ⟨σ₁u, hσ⟩ := exists_sec Q.P.isLB (φ' := Q.famφB (α + e • mu)) (ε' := DegPre.famε e) (fun U _ h => by
      have p₀ := prod_famB Q (x * mm) α e h
      have p₁ := prod_cub a x mm h
      have p₂ := hF U (fun q => h ((toUnit Q.P.A).left ≫ q))
      have p₃ := prod_famB Q (𝟙 _) (α + e • mu) e h
      have e₀ : ∀ i, (𝟙 Q.P.A : Q.P.A ⟶ Q.P.A).left ≫ Q.famφB (α + e • mu) i = Q.famφB (α + e • mu) i := fun i => by
        rw [Over.id_left, Category.id_comp]
      simp only [e₀] at p₃
      rw [hx] at p₃
      have t₁ : ∀ χ, (toUnit Q.P.A).left ≫ (cP Q (𝟙_ (Over (Spec (CommRingCat.of R)))) χ).left = (cP Q Q.P.A χ).left :=
        fun χ => congrArg (fun q => q.left) (comp_cP Q (toUnit Q.P.A) χ)
      have t₂ : (toUnit Q.P.A).left ≫ (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Q.P.A).left = (1 : Q.P.A ⟶ Q.P.A).left :=
        congrArg (fun q : Q.P.A ⟶ Q.P.A => q.left) (MonObj.comp_one (M := Q.P.A) (toUnit Q.P.A))
      simp only [t₁, t₂] at p₂
      rw [c₃, hmm, ha] at p₂
      rw [ha, c₁] at p₀
      rw [c₄, c₅] at p₃
      refine Eq.trans (prod_sum₂ _ p₀ (prod_sum₂ _ (prod_sum₂ _ rfl (prod_neg _ _ p₁)) p₂)) (Eq.trans ?_ p₃.symm)
      rw [c₂]
      apply Additive.ofMul.injective
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_one, Matrix.head_cons, _root_.mul_one, ofMul_one]
      module)
    (pullMulSec σ (x * mm).left U hU)
  refine ⟨σ₁u, fun T ρ z J hJ => ?_⟩
  rw [hσ _ _ z J hJ, sval_pullMulSec _ _ _ _ _ z hJ, Over.comp_left]
  congr 2
  refine (val_mul hJ _ _ _).trans ?_
  rw [val_pull hJ]
  refine congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((vN T ρ z J hJ).trans (by rw [← hx, Category.comp_id])) ((val_inv _ _).trans (congrArg (·⁻¹) ((val_cub Q.cub ρ hJ _ _ _).trans (by rw [← hx, Category.comp_id])))))) (by rw [Over.comp_left])
end Gen

theorem nonneg_shift {X : Type} [AddCommGroup X] (g : LinearMap.BilinForm ℤ X) (mu α : X) (hs : g mu α = g α mu)
    (hnn : ∀ y, 0 ≤ g y y) (n : ℕ) (hn : g mu mu = 2 * n) (e : ℕ) (he : (g mu α).natAbs ≤ e) :
    0 ≤ (e : ℤ) * n + g mu α := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have key : ∀ x : ℤ, 0 ≤ 2 * x * g mu α + g α α := fun x => by
      have := hnn (x • mu + α)
      simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hn, ← hs] at this
      push_cast at this
      linarith
    have h0 : g mu α = 0 := by
      by_contra hne
      have := key (-(g α α + 1) * g mu α)
      nlinarith [sq_pos_of_ne_zero hne, hnn α]
    simp [h0]
  · have h1 : -(g mu α) ≤ ((g mu α).natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact neg_le_abs _
    have h2 : ((g mu α).natAbs : ℤ) ≤ e := by exact_mod_cast he
    have h3 : (1 : ℤ) ≤ n := by exact_mod_cast hpos
    nlinarith

theorem gs_zero' {Y Z : Scheme.{0}} (f : Z ⟶ Y) (z : Z) : gs f z ⊤ (0 : Γ(Y, ⊤)) = 0 := by
  rw [gs_eq f z ⊤ trivial, map_zero, map_zero]

theorem sval_secScale' {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem gs_appTop {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (a : Γ(X, ⊤)) :
    gs f z ⊤ (g.appTop.hom a) = gs (f ≫ g) z ⊤ a :=
  gs_pull f g z ⊤ trivial a

theorem exists_shift_div_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ (mu α : P.D.toPre.X) (n : Fin m → ℕ) (ψ₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (K := PUnit) (fun _ => (P.D.toPre.c mu).left) fun _ => -1)) τ₀, GlobalTheory.LogKSChart.IsUnitPart P.D.toPre (bdParam k m d) gam mu n ψ₀ → IsUnitTau P.D.toPre (bdParam k m d) gam mu α τ₀ → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → (∀ i, 0 ≤ (e : ℤ) * n i + gam i mu α) ∧ ∀ σ : P.D.toPre.SecB e α, ∃ σ₁ σ₁u : P.D.toPre.SecB e (α + e • mu), ShiftEq P.D.toPre e mu α σ σ₁ 0 σ₁ ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁ x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ ((e : ℤ) * n i + gam i mu α).toNat)) * sval σ₁u x z J) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (ChartRing k m d)) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁u (r ≫ (P.D.toPre.c 0).left) z J = ((val ψ₀ r z J) ^ e * val τ₀ r z J * (val P.D.toPre.rig r z J) ^ e).val * sval σ (r ≫ (P.D.toPre.c mu).left) z J := by
  intro E _ _ _ H k _ _ m d t P gam hM hli hab
  intro Y n' v' dd hdd D q hq h hB hDef hΘ ρ hρ B' _ π₁ π₂ c' h₁ h₂ h₃ h₄ mu α n ψ₀ τ₀ hψ hτ
  have hsym : ∀ i, gam i mu α = gam i α mu := GlobalTheory.T.exponentForms_symm_of_isUnit_tau_on_toricChart k m d P.D.toPre gam hM mu α τ₀ hτ
  have hN : ∀ e : ℕ, (∑ i, (gam i mu α).natAbs) ≤ e → ∀ i, 0 ≤ (e : ℤ) * n i + gam i mu α := fun e he i =>
    nonneg_shift (gam i) mu α (hsym i) (hM.nonneg i) (n i) (hψ.2.1 i) e
      ((Finset.single_le_sum (f := fun i => (gam i mu α).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans he)
  refine ⟨∑ i, (gam i mu α).natAbs, fun e he => ⟨hN e he, fun σ => ?_⟩⟩
  have hG : GlobalFnsSt := GlobalTheory.ExpansionTotal.globalFns
  have hc0 : P.D.toPre.c 0 = η[P.D.toPre.P.A] := by
    have h := P.D.toPre.c_add 0 0
    rw [add_zero] at h
    have h' : P.D.toPre.c 0 * P.D.toPre.c 0 = P.D.toPre.c 0 := h.symm
    have h1 : P.D.toPre.c 0 = 1 := mul_eq_left.1 h'
    rw [h1, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  let v₀ := LB.mulGen P.D.toPre.P.L _ _ _ _ (LB.mulGen P.D.toPre.P.L _ _ _ _ (GeneratorPullback.powGen P.D.toPre.P.L _ _ ψ₀ e) τ₀)
    (GeneratorPullback.powGen P.D.toPre.P.L _ _ P.D.toPre.rig e)
  have hv₀ : v₀.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ hψ.1 e) hτ.1)
    (powGen_isGen _ _ _ _ P.D.toPre.rig_gen e)
  have kc : ∀ χ, (P.D.toPre.c χ).left =
      (cP P.D.toPre (𝟙_ (Over (Spec (CommRingCat.of (ChartRing k m d))))) χ).left := fun χ => by
    rw [cP, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have k1 : (P.D.toPre.c 0).left = (1 : 𝟙_ (Over (Spec (CommRingCat.of (ChartRing k m d)))) ⟶ P.D.toPre.P.A).left := by
    rw [hc0, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have k0 : eSec P.D.toPre.P.A = (1 : 𝟙_ (Over (Spec (CommRingCat.of (ChartRing k m d)))) ⟶ P.D.toPre.P.A).left := by
    rw [← k1, hc0]; rfl
  obtain ⟨σ₁u, hσu⟩ := exists_U P.D.toPre e mu α v₀ hv₀ (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Fin.prod_univ_four, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons]
      rw [k1, k0, kc, kc, kc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]
      module) σ
  have hne : ∀ i, algebraMap (ChartRing k m d) (FractionRing (ChartRing k m d)) (bdParam k m d i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (by
      intro h0
      have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin d) 1)) h0
      simp [bdParam, MvPowerSeries.coeff_X] at this)
  obtain ⟨-, -, e1, he1, hv1⟩ := hψ
  obtain ⟨-, e', he', hv'⟩ := hτ
  let tN : ChartRing k m d := ∏ i, bdParam k m d i ^ ((e : ℤ) * n i + gam i mu α).toNat
  have hE : ((e1 ^ e * e' : (FractionRing (ChartRing k m d))ˣ) : FractionRing (ChartRing k m d)) =
      algebraMap (ChartRing k m d) _ tN := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, he1, he']
    simp only [tN, map_prod, map_pow]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_mul, ← zpow_natCast, ← zpow_natCast (algebraMap _ _ _) (((e : ℤ) * n i + gam i mu α).toNat),
      ← zpow_add₀ (hne i), Int.toNat_of_nonneg (hN e he i)]
    congr 1
    push_cast
    ring
  refine ⟨DVR.SecOps.secScale (Out.scal P.D.toPre.P.A.hom tN) σ₁u, σ₁u, ?_, fun Z x z J hJ => ?_, ?_⟩
  rotate_left
  · rw [sval_secScale' _ _ _ _ hJ]
    exact congrArg (· * _) (gs_appTop x P.D.toPre.P.A.hom z _)
  · intro Z r z J hJ
    let T' : Over (Spec (CommRingCat.of (ChartRing k m d))) := Over.mk r
    have ht : (toUnit T').left = r := (Category.comp_id _).symm.trans (Over.w (toUnit T'))
    let ρ' : T' ⟶ P.D.toPre.P.A := Over.homMk (r ≫ (P.D.toPre.c 0).left) (by
        show (r ≫ (P.D.toPre.c 0).left) ≫ P.D.toPre.P.A.hom = r
        rw [Category.assoc, Over.w (P.D.toPre.c 0)]
        exact Category.comp_id r)
    have hρ1 : ρ' = 1 := by
      rw [Hom.one_def]
      apply Over.OverMorphism.ext
      rw [Over.comp_left, ht, ← hc0]
      rfl
    have hρu : ρ' ≫ toUnit P.D.toPre.P.A = toUnit T' := toUnit_unique _ _
    have hρm : ρ' ≫ (𝟙 P.D.toPre.P.A * cP P.D.toPre _ mu) = toUnit T' ≫ P.D.toPre.c mu := by
      rw [MonObj.comp_mul, Category.comp_id, comp_cP, hρ1, _root_.one_mul]
      rfl
    have C : IsCub (cubV P.D.toPre.cub z J) := isCub_cubV (T := T') P.D.toPre.cub hJ
    have c1 : cubN (cubV P.D.toPre.cub z J) e (ρ' ≫ cP P.D.toPre _ α) (ρ' ≫ cP P.D.toPre _ mu) ρ' = 1 := by
      rw [hρ1]; exact C.N_one _ _ _
    have c2 : cubV P.D.toPre.cub z J (ρ' ≫ cP P.D.toPre _ α) ρ' (ρ' ≫ cP P.D.toPre _ mu) = 1 := by
      rw [hρ1]; exact C.face₂ _ _
    have hv := hσu T' ρ' z J hJ
    rw [c1, c2, hρu, hρm, inv_one, _root_.one_mul, _root_.one_mul] at hv
    show sval σ₁u ρ'.left z J = _
    rw [hv, Over.comp_left, ht]
    rw [val_mul hJ, val_mul hJ, val_pow, val_pow, mul_comm]
  · intro uu hu hc z J hJ
    have hr : ((fst (TF (R := ChartRing k m d) (FractionRing (ChartRing k m d))) P.D.toPre.P.A).left ≫
        jFK (R := ChartRing k m d) (FractionRing (ChartRing k m d))) ≫ (toUnit (TK (ChartRing k m d))).left =
        (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d)) ≫ toUnit P.D.toPre.P.A).left := by
      have := congrArg (fun q => q.left) (toUnit_unique (fst (TF (R := ChartRing k m d) (FractionRing (ChartRing k m d)))
        P.D.toPre.P.A ≫ (Over.homMk (jFK (R := ChartRing k m d) (FractionRing (ChartRing k m d))) rfl :
          TF (R := ChartRing k m d) (FractionRing (ChartRing k m d)) ⟶ TK (ChartRing k m d)) ≫ toUnit (TK (ChartRing k m d)))
        (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d)) ≫ toUnit P.D.toPre.P.A))
      simpa [Category.assoc] using this
    have hu' : unitOn (e1 ^ e * e') = unitOn e1 ^ e * unitOn e' := by simp [unitOn, map_mul, map_pow]
    have hfm : val (DegPre.famMult P.D.toPre (FractionRing (ChartRing k m d)) e mu α)
        (fst (TF (R := ChartRing k m d) (FractionRing (ChartRing k m d))) P.D.toPre.P.A).left z J =
        gm ((fst (TF (R := ChartRing k m d) (FractionRing (ChartRing k m d))) P.D.toPre.P.A).left ≫
          jFK (R := ChartRing k m d) (FractionRing (ChartRing k m d))) z ⊤ (unitOn (e1 ^ e * e')) *
        val v₀ (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d)) ≫ toUnit P.D.toPre.P.A).left z J := by
      have P1 := val_transport (P.D.toPre.psi mu) (LB.pullGen P.D.toPre.P.L _ _ ψ₀ (toUnit (TK (ChartRing k m d))).left)
        (unitOn e1) (fun y J hJ => (hv1 y J hJ).trans (by rw [val_pull hJ, Category.id_comp]))
        ((fst (TF (R := ChartRing k m d) (FractionRing (ChartRing k m d))) P.D.toPre.P.A).left ≫
          jFK (R := ChartRing k m d) (FractionRing (ChartRing k m d))) z J hJ
      have P2 := val_transport (P.D.toPre.tau mu α) (LB.pullGen P.D.toPre.P.L _ _ τ₀ (toUnit (TK (ChartRing k m d))).left)
        (unitOn e') (fun y J hJ => (hv' y J hJ).trans (by rw [val_pull hJ, Category.id_comp]))
        ((fst (TF (R := ChartRing k m d) (FractionRing (ChartRing k m d))) P.D.toPre.P.A).left ≫
          jFK (R := ChartRing k m d) (FractionRing (ChartRing k m d))) z J hJ
      rw [val_pull hJ] at P1 P2
      rw [val_famMult (fst _ _) hJ e mu α, val_pow, val_pow, P1, P2, DegPre.rigK, val_pull hJ, hr, val_mul hJ,
        val_mul hJ, val_pow, val_pow, hu', map_mul, map_pow, mul_pow]
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    have hGv : (gm ((fst (TF (R := ChartRing k m d) (FractionRing (ChartRing k m d))) P.D.toPre.P.A).left ≫
          jFK (R := ChartRing k m d) (FractionRing (ChartRing k m d))) z ⊤ (unitOn (e1 ^ e * e'))).val =
        gs (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z ⊤ (Out.scal P.D.toPre.P.A.hom tN) := by
      rw [← gs_unit _ z ⊤ trivial]
      show gs _ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing (ChartRing k m d)))).inv.hom
        ((e1 ^ e * e' : (FractionRing (ChartRing k m d))ˣ) : FractionRing (ChartRing k m d))) = _
      rw [hE]
      all_goals
        have nat := congrArg (fun f => f.hom tN) (Scheme.ΓSpecIso_inv_naturality
          (CommRingCat.ofHom (algebraMap (ChartRing k m d) (FractionRing (ChartRing k m d)))))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
        rw [nat, gs_appTop, Out.scal, gs_appTop]
        congr 1
    have G := (gen_fe (F := FractionRing (ChartRing k m d)) hG e mu α).2 uu hu hc _ (𝟙 _) z J hJ
    rw [Over.id_left] at G
    rw [G]
    have hz0 : Out.scal (DegPre.BF P.D.toPre (FractionRing (ChartRing k m d))).hom (0 : ChartRing k m d) = 0 := by
      simp [Out.scal]
    rw [hz0, gs_zero', zero_mul, add_zero, sval_secScale' _ _ _ _ hJ]
    have etr : DegPre.trF P.D.toPre (FractionRing (ChartRing k m d)) mu ≫ DegPre.prB P.D.toPre _ =
        DegPre.prB P.D.toPre _ ≫ (𝟙 P.D.toPre.P.A * cP P.D.toPre _ mu) := by
      rw [MonObj.comp_mul, Category.comp_id, comp_cP]
      exact lift_snd _ _
    rw [etr, hσu _ (DegPre.prB P.D.toPre _) z J hJ, uVal_id, Category.id_comp, hfm]
    simp only [comp_cP, Units.val_mul, th]
    rw [hGv]
    ring

end GlobalTheory.ShiftUnitPart
