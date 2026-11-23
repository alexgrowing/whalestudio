import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValPsiZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UnitPartPt

variable {R : Type} [CommRing R] [IsDomain R]

theorem appTop_jK_injective : Function.Injective (jK R).appTop.hom := by
  intro a b h
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom h
  have ea := congrArg (fun f => f.hom a) e
  have eb := congrArg (fun f => f.hom b) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at ea eb
  rw [ea, eb] at h2
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
    (IsFractionRing.injective R (FractionRing R) h2)

theorem eq_one_of_jK (a : Γ(Sp R, ⊤)) (z : (TK R).left) (h : gs (jK R) z ⊤ a = 1) : a = 1 := by
  rw [gs_eq _ z ⊤ trivial] at h
  have h1 := germ_injective_of_isIntegral (Spec (CommRingCat.of (FractionRing R))) (U := (jK R) ⁻¹ᵁ ⊤) z trivial
    (h.trans (map_one _).symm)
  exact appTop_jK_injective (h1.trans (map_one _).symm)

theorem toUnit_TK : (toUnit (TK R)).left = jK R := rfl

theorem val_eq_one_of_generic {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K]
    {φ : K → ((𝟙_ (Over (Sp R))).left ⟶ X)} {ε : K → ℤ}
    (hF : FormEq φ ε (PEmpty.elim : PEmpty → ((𝟙_ (Over (Sp R))).left ⟶ X)) PEmpty.elim)
    {u : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen)
    (h : ∀ z J, Good M z J → val u (toUnit (TK R)).left z J = 1) (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Sp R))).left)
    (z : Z) (J) (hJ : Good M z J) : val u r z J = 1 := by
  obtain ⟨t, -, hv⟩ := exists_gen hM hF u hu
  have le : (⊤ : (𝟙_ (Over (Sp R))).left.Opens) ≤
      LB.wchart M (PEmpty.elim : PEmpty → ((𝟙_ (Over (Sp R))).left ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Sp R))).left) (z : Z) (J), Good M z J →
      (val u r z J).val = gs r z ⊤ (res le (t.s PEmpty.elim)).val := by
    intro Z r z J hJ
    rw [← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans (gs_unit r z ⊤ trivial _).symm
  obtain ⟨z0⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  choose I hI using fun χ : (TK R).left ⟶ X => exists_chart hM (χ z0)
  have h0 := key _ (toUnit (TK R)).left z0 I hI
  rw [h z0 I hI, Units.val_one] at h0
  have a1 := eq_one_of_jK _ z0 h0.symm
  have := key Z r z J hJ
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact Units.ext this

theorem formEq_empty {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε') :
    FormEq (Sum.elim φ φ') (Sum.elim ε fun k => -ε' k) (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := by
  intro U _ f
  refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [h U f, mul_inv_cancel]

theorem prod_sum {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) {U : Type} [CommGroup U] (f : (Y ⟶ X) → U) :
    ∏ k, f (Sum.elim φ φ' k) ^ Sum.elim ε ε' k = (∏ k, f (φ k) ^ ε k) * ∏ k, f (φ' k) ^ ε' k :=
  Fintype.prod_sum_type _

variable (Q : DegPre R)

def vφ (mu χ : Q.X) : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit → ((𝟙_ (Over (Sp R))).left ⟶ Q.P.A.left) :=
  Sum.elim (Sum.elim (Sum.elim (fun _ => (Q.c (mu + χ)).left) (fun _ => (Q.c mu).left)) (fun _ => (Q.c χ).left))
    (fun _ => eSec Q.P.A)

def vε : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit → ℤ :=
  Sum.elim (Sum.elim (Sum.elim (fun _ => -1) (fun _ => -(-1))) (fun _ => -(-1))) (fun _ => -1)

def vgen (ψ₀ : ∀ χ : Q.X, LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) fun _ => -1))
    (mu χ : Q.X) : LB.Gen (LB.LinComb Q.P.L (vφ Q mu χ) (vε)) :=
  LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ (ψ₀ (mu + χ))
    (LB.invGen Q.P.L _ _ (ψ₀ mu))) (LB.invGen Q.P.L _ _ (ψ₀ χ))) (LB.invGen Q.P.L _ _ Q.rig)

theorem c_eq (a : Q.X) : cP Q (𝟙_ (Over (Sp R))) a = Q.c a := by
  rw [cP, toUnit_unit, Category.id_comp]

theorem c_add' (a b : Q.X) : Q.c (a + b) = Q.c a * Q.c b := by
  rw [← c_eq, ← c_eq, ← c_eq, cPoint_add]

theorem one_left : (1 : 𝟙_ (Over (Sp R)) ⟶ Q.P.A).left = eSec Q.P.A := by
  rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl

theorem prod_vφ (mu χ : Q.X) {U : Type} [CommGroup U] (f : ((𝟙_ (Over (Sp R))).left ⟶ Q.P.A.left) → U) :
    ∏ k, f (vφ Q mu χ k) ^ vε k =
      (f (Q.c χ * Q.c mu).left)⁻¹ * f (Q.c χ).left * f (Q.c mu).left * (f (1 : 𝟙_ (Over (Sp R)) ⟶ Q.P.A).left)⁻¹ := by
  simp only [vφ, vε, Fintype.prod_sum_type, Finset.univ_unique, Finset.prod_singleton, Sum.elim_inl, Sum.elim_inr]
  rw [c_add', one_left, mul_comm (Q.c mu)]
  simp only [zpow_neg, zpow_one, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.UnitPartPt

namespace GlobalTheory.UnitPartPt

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R}

theorem cst_mul'' {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) (a b : V) :
    cst q z (a * b) = cst q z a * cst q z b := by
  simp only [cst, map_mul, gs_mul q z ⊤ trivial]

theorem cst_one'' {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) : cst q z 1 = 1 := by
  rw [cst, map_one, gs_eq _ _ ⊤ trivial, map_one, map_one]

section
variable (ψ₀ : ∀ χ : Q.X, LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) fun _ => -1))

theorem vgen_isGen (hψ₀ : ∀ χ, (ψ₀ χ).IsGen) (mu χ : Q.X) : (vgen Q ψ₀ mu χ).IsGen :=
  mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (hψ₀ _)
    (invGen_isGen _ _ _ _ (hψ₀ _))) (invGen_isGen _ _ _ _ (hψ₀ _))) (invGen_isGen _ _ _ _ Q.rig_gen)

theorem val_vgen {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ Q.P.A.left) → Q.P.L.ι} (hJ : Good Q.P.L z J) (mu χ : Q.X)
    (r : Z ⟶ (𝟙_ (Over (Sp R))).left) :
    val (vgen Q ψ₀ mu χ) r z J = val (ψ₀ (mu + χ)) r z J * (val (ψ₀ mu) r z J)⁻¹ * (val (ψ₀ χ) r z J)⁻¹ *
      (val Q.rig r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
end

theorem val_tau' {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ Q.P.A.left) → Q.P.L.ι} (hJ : Good Q.P.L z J) (a b : Q.X)
    (r : Z ⟶ (TK R).left) :
    val (Q.tau a b) r z J = val (Q.psi (a + b)) r z J * (val (Q.psi a) r z J)⁻¹ * (val (Q.psi b) r z J)⁻¹ *
      (val Q.rig (r ≫ jK R) z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) ((val_inv _ _).trans (congrArg _ (val_pull hJ _ _ _))))

theorem val_mmi {X Y Z : Scheme.{0}} {L : LB X} {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J)
    {K₁ K₂ K₃ K₄ : Type} [Fintype K₁] [Fintype K₂] [Fintype K₃] [Fintype K₄] {φ₁ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {φ₃ : K₃ → (Y ⟶ X)} {ε₃ : K₃ → ℤ} {φ₄ : K₄ → (Y ⟶ X)} {ε₄ : K₄ → ℤ}
    (a : LB.Gen (LB.LinComb L φ₁ ε₁)) (b : LB.Gen (LB.LinComb L φ₂ ε₂)) (c : LB.Gen (LB.LinComb L φ₃ ε₃))
    (d : LB.Gen (LB.LinComb L φ₄ ε₄)) (r : Z ⟶ Y) :
    val (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ a b) (LB.invGen L _ _ (LB.mulGen L _ _ _ _ c d))) r z J =
      val a r z J * val b r z J * (val c r z J * val d r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) ((val_inv _ _).trans (congrArg _ (val_mul hJ _ _ _))))

theorem exp_id {m : ℕ} (gam : Fin m → LinearMap.BilinForm ℤ Q.X) (n : Q.X → Fin m → ℕ)
    (hn : ∀ χ i, gam i χ χ = 2 * n χ i) (a b c : Q.X) (i : Fin m) :
    n (a + (b + c)) i + n a i + n b i + n c i = n (a + b) i + n (a + c) i + n (b + c) i := by
  have h1 := hn (a + (b + c)) i
  have h2 := hn a i
  have h3 := hn b i
  have h4 := hn c i
  have h5 := hn (a + b) i
  have h6 := hn (a + c) i
  have h7 := hn (b + c) i
  simp only [map_add, LinearMap.add_apply] at h1 h5 h6 h7
  omega

end GlobalTheory.UnitPartPt

namespace GlobalTheory.UnitPartPt

theorem exists_unitPartPt : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), Q.TauBimult → (∀ i, t i ≠ 0) → ∀ (n : Q.X → Fin m → ℕ), (∀ χ i, gam i χ χ = 2 * n χ i) → ∀ (ψ₀ : ∀ χ : Q.X, LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) fun _ => -1)), (∀ χ, (ψ₀ χ).IsGen) → (∀ χ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi χ) r z J).val = cst (r ≫ jK R) z (∏ i, t i ^ n χ i) * (val (ψ₀ χ) (r ≫ jK R) z J).val) → ∀ mu : Q.X, ∃ xp : 𝟙_ (Over (Sp R)) ⟶ Y.H, xp ≫ Y.q = Q.c mu ∧ ∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (χ : Q.X) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z (∏ i, t i ^ n (mu + χ) i) * (val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s χ) (𝟙 Z) z J).val = cst (g ≫ jK R) z (∏ i, t i ^ (n mu i + n χ i)) * (val (Q.tau mu χ) g z J).val := by
  intro R _ _ Q O _ _ _ oa Y m t gam hB ht n hn ψ₀ hψ₀ hψ mu
  have hM := Q.P.isLB

  have hF : ∀ χ, FormEq (vφ Q mu χ) vε (DegPre.gtφT Q (𝟙_ (Over (Sp R))) (Q.c mu) χ) DegPre.gtε := fun χ U _ f => by
    rw [prod_vφ, TorusModel.prod_pt, c_eq]

  have n0 : ∀ i, n 0 i = 0 := fun i => by
    have := hn 0 i
    simp only [map_zero, LinearMap.zero_apply] at this
    omega
  have h₀ : ∀ y J, Good Q.P.L y J → val (vgen Q ψ₀ mu 0) (𝟙 _) y J = 1 := by
    refine val_eq_one_of_generic hM (fun U _ f => ?_) (vgen_isGen ψ₀ hψ₀ mu 0) (fun z J hJ => ?_) _ _
    · rw [prod_vφ, Fintype.prod_empty]
      have c0 : Q.c 0 = 1 := by rw [← c_eq]; exact GlobalTheory.PsiZero.cPoint_zero' Q _
      rw [c0, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    · rw [toUnit_TK, val_vgen ψ₀ hJ]
      have p0 : val (ψ₀ 0) (jK R) z J = (val Q.rig (jK R) z J)⁻¹ := by
        refine Units.ext ?_
        have e := hψ 0 _ (𝟙 _) z J hJ
        simp only [n0, pow_zero, Finset.prod_const_one, cst_one'', _root_.one_mul, Category.id_comp] at e
        rw [← e, GlobalTheory.PsiZero.val_psi_zero hB hJ]
      have hp : ∀ a, a = mu → val (ψ₀ a) (jK R) z J = val (ψ₀ mu) (jK R) z J := by rintro a rfl; rfl
      rw [hp _ (add_zero mu), p0, inv_inv, mul_inv_cancel, _root_.one_mul, mul_inv_cancel]
  have hm : ∀ χ χ' y J, Good Q.P.L y J → val (vgen Q ψ₀ mu (χ + χ')) (𝟙 _) y J *
      th Q y J (cP Q _ χ) (cP Q _ χ') (Q.c mu) = val (vgen Q ψ₀ mu χ) (𝟙 _) y J * val (vgen Q ψ₀ mu χ') (𝟙 _) y J := by
    intro χ χ' y J hJ
    have key := val_eq_one_of_generic hM (u := LB.mulGen Q.P.L _ _ _ _
      (LB.mulGen Q.P.L _ _ _ _ (vgen Q ψ₀ mu (χ + χ'))
        (DegPre.cubAtT Q (𝟙_ (Over (Sp R))) (cP Q _ χ) (cP Q _ χ') (Q.c mu)))
      (LB.invGen Q.P.L _ _ (LB.mulGen Q.P.L _ _ _ _ (vgen Q ψ₀ mu χ) (vgen Q ψ₀ mu χ'))))
      (formEq_empty (fun U _ f => ?_))
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (vgen_isGen ψ₀ hψ₀ mu _)
        (pullGen_isGen _ _ _ _ Q.cub.isGen _))
        (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (vgen_isGen ψ₀ hψ₀ mu _) (vgen_isGen ψ₀ hψ₀ mu _))))
      (fun z J hJ => ?_) _ (𝟙 _) y J hJ
    · have k2 := (val_mmi hJ _ _ _ _ _).symm.trans key
      rw [TorusModel.val_cubAtT hJ] at k2
      exact mul_inv_eq_one.1 k2
    · refine (prod_sum _ _ _ _ f).trans (Eq.trans ?_ (prod_sum _ _ _ _ f).symm)
      rw [prod_vφ, prod_vφ, prod_vφ]
      refine congrArg₂ (· * ·) rfl (prod_cub (cP Q _ χ) (cP Q _ χ') (Q.c mu) f) |>.trans ?_
      simp only [c_eq, c_add']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · refine (val_mmi hJ _ _ _ _ _).trans ?_
      have ec : val (DegPre.cubAtT Q (𝟙_ (Over (Sp R))) (cP Q _ χ) (cP Q _ χ') (Q.c mu)) (toUnit (TK R)).left z J =
          th Q z J (cP Q (TK R) χ) (cP Q (TK R) χ') (cP Q (TK R) mu) := by
        refine (val_cub Q.cub (toUnit (TK R)) hJ _ _ _).trans ?_
        rw [comp_cP, comp_cP]; rfl
      rw [ec, val_vgen ψ₀ hJ, val_vgen ψ₀ hJ, val_vgen ψ₀ hJ]
      have eB := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB χ χ' mu) (𝟙 (TK R).left)).trans (val_mul hJ _ _ _))
      have ecb : val (LB.pullGen Q.P.L (thφ Q.P.A (x3 Q.P.A)) thε Q.cub.t (Q.pt3 χ χ' mu)) (𝟙 _) z J =
          th Q z J (cP Q (TK R) χ) (cP Q (TK R) χ') (cP Q (TK R) mu) := by
        refine (val_cub Q.cub (𝟙 (TK R)) hJ (cP Q _ χ) (cP Q _ χ') (cP Q _ mu)).trans ?_
        rw [Category.id_comp, Category.id_comp, Category.id_comp]
      rw [ecb, val_tau' hJ, val_tau' hJ, val_tau' hJ] at eB
      have hC : ∀ y, (val (Q.psi y) (𝟙 _) z J * (val (ψ₀ y) (𝟙 (TK R).left ≫ jK R) z J)⁻¹).val =
          cst (𝟙 (TK R).left ≫ jK R) z (∏ i, t i ^ n y i) := fun y => by
        rw [Units.val_mul, hψ y _ (𝟙 _) z J hJ, _root_.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, _root_.mul_one]
      obtain ⟨U, hU⟩ : ∃ U : Q.X → ((TK R).left.presheaf.stalk z)ˣ, ∀ y, val (Q.psi y) (𝟙 _) z J = U y :=
        ⟨_, fun _ => rfl⟩
      obtain ⟨B, hB'⟩ : ∃ B : Q.X → ((TK R).left.presheaf.stalk z)ˣ, ∀ y, val (ψ₀ y) (toUnit (TK R)).left z J = B y :=
        ⟨_, fun _ => rfl⟩
      obtain ⟨ρ, hρ⟩ : ∃ ρ : ((TK R).left.presheaf.stalk z)ˣ, val Q.rig (toUnit (TK R)).left z J = ρ := ⟨_, rfl⟩
      have hρ' : val Q.rig (𝟙 (TK R).left ≫ jK R) z J = ρ := by rw [← hρ, Category.id_comp]; rfl
      have hB2 : ∀ y, val (ψ₀ y) (𝟙 (TK R).left ≫ jK R) z J = B y := fun y => by
        rw [← hB', Category.id_comp]; rfl
      rw [hρ'] at eB
      rw [hρ]
      simp only [hU, hB', hB2] at eB hC ⊢
      obtain ⟨C, hCd⟩ : ∃ C : Q.X → ((TK R).left.presheaf.stalk z)ˣ, ∀ y, U y * (B y)⁻¹ = C y := ⟨_, fun _ => rfl⟩
      simp only [hCd] at hC
      have hUC : ∀ y, U y = C y * B y := fun y => by rw [← hCd, inv_mul_cancel_right]
      simp only [hUC] at eB
      rw [show χ + χ' + mu = mu + (χ + χ') by abel, add_comm χ mu, add_comm χ' mu] at eB
      have eC : C (mu + (χ + χ')) * C mu * C χ * C χ' = C (mu + χ) * C (mu + χ') * C (χ + χ') := by
        apply Units.ext
        simp only [Units.val_mul, hC, ← cst_mul'']
        congr 1
        simp only [← Finset.prod_mul_distrib, ← pow_add, exp_id gam n hn]
      have eB' := congrArg Additive.ofMul eB
      have eC' := congrArg Additive.ofMul eC
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at eB' eC' ⊢
      linear_combination (norm := abel) eB' - eC'
  obtain ⟨gp, hgb, hgv⟩ := TorusModel.exists_pt (Q.c mu) (fun χ => vgen Q ψ₀ mu χ)
    (fun χ => vgen_isGen ψ₀ hψ₀ mu χ) hF h₀ hm
  refine ⟨(Y.Φ _).symm gp, ?_, fun Z g χ z J hJ => ?_⟩
  · rw [← Ray.Φ_b, Equiv.apply_symm_apply, hgb]
  · have hp := ((TorusModel.isPull_iff _ _ _).1
      (Y.rep.1 (Over.mk (g ≫ jK R)) (𝟙_ _) (toUnit _) ((Y.Φ _).symm gp))).2 χ z J hJ
    rw [Equiv.apply_symm_apply] at hp
    have e1 : val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ (Y.Φ _).symm gp)).s χ) (𝟙 Z) z J =
        val (vgen Q ψ₀ mu χ) (g ≫ jK R) z J := hp.trans (hgv χ Z _ z J hJ)
    rw [e1, val_vgen ψ₀ hJ, val_tau' hJ]
    have hC : ∀ y, (val (Q.psi y) g z J * (val (ψ₀ y) (g ≫ jK R) z J)⁻¹).val =
        cst (g ≫ jK R) z (∏ i, t i ^ n y i) := fun y => by
      rw [Units.val_mul, hψ y Z g z J hJ, _root_.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        _root_.mul_one]
    have e2 : cst (g ≫ jK R) z (∏ i, t i ^ (n mu i + n χ i)) =
        cst (g ≫ jK R) z (∏ i, t i ^ n mu i) * cst (g ≫ jK R) z (∏ i, t i ^ n χ i) := by
      rw [← cst_mul'', ← Finset.prod_mul_distrib]
      simp only [pow_add]
    rw [e2, ← hC, ← hC, ← hC, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end GlobalTheory.UnitPartPt
