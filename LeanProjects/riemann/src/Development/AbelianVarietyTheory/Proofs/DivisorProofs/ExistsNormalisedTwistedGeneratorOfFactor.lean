import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationBundleTrivialAbelianParStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGenerat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPowDeg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwNorm

open GlobalTheory.TwFac

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_normalised (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h : D.X →+ D.X) [IsMonHom a]
    (hh : ∀ y, D.c (h y) = D.c y ≫ a) (n j : ℤ) (mu β' : D.X)
    (g : ∀ y : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c y).left) (fun _ => -1)))
    (hg : ∀ y, (g y).IsGen)
    (w : LB.Gen (LB.LinComb D.P.L (Sum.elim (tφ D a β')
      (fun k => (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left ≫ tφ D a 0 k)) (dε n j))) (hw : w.IsGen) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (tφ D a β')
      (fun k => (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left ≫ tφ D a 0 k)) (dε n j)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Sp R))).left) (z : Z) J, Good D.P.L z J →
        val u (r ≫ eSec D.P.A) z J = val (g mu) r z J ^ n * val (g (h mu)) r z J ^ j * val D.rig r z J ^ (n + j) := by
  obtain ⟨p₁, h₁, v₁⟩ := exists_zpow (g mu) (hg mu) n
  obtain ⟨p₂, h₂, v₂⟩ := exists_zpow (g (h mu)) (hg _) j
  obtain ⟨p₃, h₃, v₃⟩ := exists_zpow D.rig D.rig_gen (n + j)
  have i₀ : toUnit (𝟙_ (Over (Sp R))) = 𝟙 _ := toUnit_unique _ _
  have a₁ : ∀ χ, DVR.cP D (𝟙_ _) χ = D.c χ := fun χ => by rw [DVR.cP, i₀, Category.id_comp]
  have a₂ : η[D.P.A] = 1 := by rw [Hom.one_def, i₀, Category.id_comp]
  have z₃ : η[D.P.A] ≫ padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu) = D.c mu := by
    refine (MonObj.comp_mul _ (𝟙 _) (DVR.cP D _ mu)).trans ?_
    rw [DVR.comp_cP, Category.comp_id, a₂, _root_.one_mul, a₁]
  obtain ⟨u, hu, vu⟩ := exists_norm D.P.isLB (toUnit D.P.A).left (eSec D.P.A)
    (congrArg (fun q => q.left) (toUnit_unique (η[D.P.A] ≫ toUnit _) (𝟙 _))) (fun U _ f => by
      have q₁ := prod_t D a β' n j η[D.P.A] f
      have q₂ := prod_t D a 0 n j (η[D.P.A] ≫ padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)) f
      have b₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) ≫ a = 1 := MonObj.one_comp _
      conv_rhs at q₁ => rw [a₂, b₁, _root_.one_mul]
      conv_rhs at q₂ => rw [z₃, ← hh, cPoint_zero, _root_.mul_one]
      simp only [Over.comp_left, Category.assoc] at q₂
      refine (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5) (U := U) _ q₁ (DVR.prod_neg _ _ q₂)).trans ?_
      have a₃ : eSec D.P.A = (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A).left := congrArg (fun q => q.left) a₂
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    w hw (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ p₁ p₂) p₃)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁ h₂) h₃)
  have hc := corr_of_val D.P.isLB (t := LB.pullGen D.P.L _ _ u (eSec D.P.A))
    (t' := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ p₁ p₂) p₃) fun y J hJ => by
      rw [val_pull hJ, Category.id_comp]; exact vu y J hJ
  refine ⟨u, hu, fun Z r z J hJ => (val_pull hJ _ _ _).symm.trans ((val_corr hJ hc r).trans ?_)⟩
  exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v₁ _ _ _ _) (v₂ _ _ _ _))) (v₃ _ _ _ _))

theorem val_tau_zero (D : DegPre R) (hB : D.TauBimult) (x : D.X) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val (D.tau x 0) (𝟙 _) z J = 1 := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv,
    congrArg (fun w => val (D.psi w) (𝟙 _) z J) (add_zero x), mul_inv_cancel, _root_.one_mul,
    GlobalTheory.PsiInPow.val_psi_zero D hB hJ, inv_inv, mul_inv_cancel]

def germK (K : Type) [Field K] (z : Sp K) : K →+* (Sp K).presheaf.stalk z :=
  ((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem gs_sec {K : Type} [Field K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (e : Sp K ⟶ Y) (he : e ≫ p = 𝟙 _) (z : Sp K) (c : K) :
    gs e z ⊤ (scal p c) = germK K z c := by
  refine (gs_pull e p z ⊤ trivial _).trans ?_
  rw [he, gs_eq _ z ⊤ trivial]
  rfl

theorem gs_generic (z : Sp (FractionRing R)) (r : R) :
    gs (𝟙 _) z ⊤ (scal (jK R) r) = germK (FractionRing R) z (algebraMap R _ r) := by
  have nat := congrArg (fun g => g.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  rw [gs_eq _ z ⊤ trivial]
  exact congrArg ((Sp (FractionRing R)).presheaf.germ ⊤ z trivial).hom nat.symm

theorem const_eq {S : Type} [CommRing S] {u u₀ p t k k' G : Sˣ} {c r : S} {m : ℤ} (e₁ : u.val = c * u₀.val)
    (e₂ : u = p * t * k ^ m) (ht : t = 1) (hk : k = k') (e₃ : p.val = r * G.val) (e₄ : u₀ = G * k' ^ m) : c = r := by
  subst ht hk e₂
  refine (Units.mul_left_inj u₀).1 ?_
  rw [← e₁, e₄, _root_.mul_one, Units.val_mul, Units.val_mul, e₃, _root_.mul_assoc]

theorem exists_gen_fac : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → ∀ (r : D.toPre.X → R) (g : ∀ y : D.toPre.X, LB.Gen (LB.LinComb D.toPre.P.L (K := PUnit) (fun _ => (D.toPre.c y).left) (fun _ => -1))), (∀ y, (g y).IsGen) → (∀ y (z : (TK R).left) (J), Good D.toPre.P.L z J → (val (D.toPre.psi y) (𝟙 _) z J ^ N * (val (D.toPre.psi (h y)) (𝟙 _) z J)⁻¹).val = gs (𝟙 _) z ⊤ (scal (jK R) (r y)) * (val (g y) (toUnit (TK R)).left z J ^ N * (val (g (h y)) (toUnit (TK R)).left z J)⁻¹).val) → ∀ ν : D.toPre.X, ∃ u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a (shift h h' N (-1) ν)) (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left ≫ tφ D.toPre a 0 k)) (dε N (-1))), u₀.IsGen ∧ ∀ u, IsFac D.toPre a h N (-1) ν 0 (shift h h' N (-1) ν) u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) (r ν))) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  intro R _ _ _ hR D a a' h h' hE N _ r g hg hr ν
  have ha : IsMonHom a := hE.1
  have hh : ∀ y, D.toPre.c (h y) = D.toPre.c y ≫ a := hE.2.2.2.1
  obtain ⟨w, hw⟩ := GlobalTheory.T.twistedFunctionalEquation_bundle_trivial_abelianPart R hR D a a' h h' hE N (-1) ν 0 (shift h h' N (-1) ν) (zero_add _).symm
  obtain ⟨u₀, hu₀, v₀⟩ := exists_normalised D.toPre a h hh N (-1) ν _ g hg w hw
  refine ⟨u₀, hu₀, fun u hu => ?_⟩
  obtain ⟨c, hc⟩ := (fac_exists_unique_const R hR D a h ha hh N (-1) ν 0 _ u₀ hu₀).2.2 u hu.1
  suffices e : c = algebraMap R (FractionRing R) (r ν) by subst e; exact hc
  obtain ⟨z⟩ : Nonempty (Sp (FractionRing R)) := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  choose J hJ using fun ψ : Sp (FractionRing R) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
  have j₁ : jFK (R := R) (FractionRing R) = 𝟙 _ := Spec.map_id _
  have z₁ : DegPre.zF D.toPre (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : (DegPre.zF D.toPre (FractionRing R)).left ≫ (DegPre.prB D.toPre (FractionRing R)).left =
      (toUnit (TK R)).left ≫ eSec D.toPre.P.A := by
    refine (congrArg (fun q => q.left) (lift_snd (𝟙 (TF (R := R) (FractionRing R))) (toUnit _ ≫ η[D.toPre.P.A]))).trans ?_
    show (jFK (R := R) (FractionRing R) ≫ (toUnit (TK R)).left) ≫ eSec D.toPre.P.A = _
    rw [j₁, Category.id_comp]
  have e₁ := hc _ (DegPre.zF D.toPre (FractionRing R)).left z J hJ
  have e₂ := hu.2 z J hJ
  have e₃ := hr ν z J hJ
  have e₄ := v₀ _ (toUnit (TK R)).left z J hJ
  have e₅ : val D.toPre.rigK (𝟙 _) z J = val D.toPre.rig (toUnit (TK R)).left z J :=
    (val_pull hJ _ _ _).trans (congrArg (fun q => val D.toPre.rig q z J) (Category.id_comp _))
  rw [j₁, zpow_natCast, zpow_neg_one] at e₂
  rw [zpow_natCast, zpow_neg_one] at e₄
  have e₆ := gs_sec _ _ (congrArg (fun q => q.left) z₁) z c
  have e₇ := gs_generic z (r ν)
  exact (germK (FractionRing R) z).injective (e₆.symm.trans ((const_eq e₁ e₂ (val_tau_zero D.toPre D.tau_bimult ν hJ) e₅ e₃
    ((congrArg (fun q => val u₀ q z J) z₂).trans e₄)).trans e₇))

end GlobalTheory.TwNorm
