import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionLinCombFiberProductSeparatedStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfGenericFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace KunnethDomain

open ReciprocityTheory.ChartRestriction.G.DVR

variable {X Y Y' T : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def cst {R : Type} [CommRing R] (q : T ⟶ Spec (CommRingCat.of R)) (z : T) : R →+* T.presheaf.stalk z :=
  (T.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_scal_eq {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (ρ : T ⟶ Y) (z : T) (c : R) :
    gs ρ z ⊤ (scal p c) = cst (ρ ≫ p) z c := by
  rw [gs_eq ρ z ⊤ trivial]; rfl

theorem sval_scale {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε))
    (r : T ⟶ Y) (z : T) {J} (hJ : Good L z J) :
    sval (SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem sval_pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (r : T ⟶ Y') (z : T) {J} (hJ : Good L z J) : sval (pullSec L φ ε s h) r z J = sval s (r ≫ h) z J := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm := hJ.mem (fun k => h ≫ φ k) r
  exact (gs_res r z _ hm _).trans (gs_pull r h z (LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)))
    (wchart_comp_le φ h _ hm) _)

theorem sval_mul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (r : T ⟶ Y) (z : T) {J} (hJ : Good L z J) :
    sval (mulSec L φ ε φ' ε' s s') r z J = sval s r z J * sval s' r z J :=
  have hm := hJ.mem (Sum.elim φ φ') r
  (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _))

def secSum {M : LB Y} {n : ℕ} (s : Fin n → LB.Sec M) : LB.Sec M where
  f := fun j => ∑ i, (s i).f j
  compat := fun j j' => by simp only [map_sum, (s _).compat, Finset.mul_sum]

theorem sval_sum {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ} (s : Fin n → LB.Sec (LB.LinComb L φ ε))
    (r : T ⟶ Y) (z : T) {J} (hJ : Good L z J) : sval (secSum s) r z J = ∑ i, sval (s i) r z J := by
  have hm := hJ.mem φ r
  refine (gs_eq r z _ hm _).trans (Eq.trans ?_ (Finset.sum_congr rfl fun i _ => (gs_eq r z _ hm _).symm))
  exact map_sum ((T.presheaf.germ (r ⁻¹ᵁ LB.wchart L φ fun k => J (r ≫ φ k)) z hm).hom.comp
    (r.app (LB.wchart L φ fun k => J (r ≫ φ k))).hom) (fun i => (s i).f fun k => J (r ≫ φ k)) Finset.univ

theorem sec_ext_of_app_injective (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (κ : Y' ⟶ Y) (hκ : ∀ U : Y.Opens, Function.Injective (κ.app U).hom)
    {u t : LB.Sec (LB.LinComb L φ ε)} (h : ∀ y J, Good L y J → sval u κ y J = sval t κ y J) : u = t :=
  SecOps.sec_ext fun j => by
    refine hκ (LB.wchart L φ j) (fn_ext fun y hy => ?_)
    choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    refine (gs_pull (𝟙 Y') κ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') κ y _ hy _).symm)
    rw [Category.id_comp]
    exact (sec_trans u κ y hy (Good.mem hI φ κ)).trans ((congrArg _ (h y I hI)).trans
      (sec_trans t κ y hy (Good.mem hI φ κ)).symm)

theorem app_generic_injective {V : Type} [CommRing V] [IsDomain V] (B : Over (Spec (CommRingCat.of V))) [Flat B.hom]
    (U : B.left.Opens) : Function.Injective ((snd (TK V) B).left.app U).hom := by
  have : IsDominant (jK V) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK V)
  exact (pullback.snd (jK V) B.hom).app_injective U

end KunnethDomain

open KunnethDomain ReciprocityTheory.ChartRestriction.G.DVR in

theorem exists_smul_eq_sum_mul_of_isDomain : ∀ (V : Type) [CommRing V] [IsDomain V] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y₁ Y₂ : Over (Spec (CommRingCat.of V))) [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom] [Flat Y₁.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom] [Flat Y₂.hom] (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y₁.left ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂.left ⟶ Z)) (ε₂ : K₂ → ℤ) (v : LB.Sec (LB.LinComb L (K := K₁ ⊕ K₂) (Sum.elim (fun k => (fst Y₁ Y₂).left ≫ φ₁ k) (fun k => (snd Y₁ Y₂).left ≫ φ₂ k)) (Sum.elim ε₁ ε₂))), ∃ (r : V) (_ : r ≠ 0) (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)), ∀ (T : Scheme.{0}) (ρ : T ⟶ (Y₁ ⊗ Y₂).left) (z : T) (J), Good L z J → ∑ i, sval (a i) (ρ ≫ (fst Y₁ Y₂).left) z J * sval (b i) (ρ ≫ (snd Y₁ Y₂).left) z J = gs ρ z ⊤ (scal (Y₁ ⊗ Y₂).hom r) * sval v ρ z J := by
  intro V _ _ Z L hL Y₁ Y₂ _ _ _ _ _ _ K₁ K₂ _ _ φ₁ ε₁ φ₂ ε₂ v
  classical
  let G₁ : Over (Spec (CommRingCat.of (FractionRing V))) := Over.mk (fst (TK V) Y₁).left
  let G₂ : Over (Spec (CommRingCat.of (FractionRing V))) := Over.mk (fst (TK V) Y₂).left
  have : QuasiCompact G₁.hom := inferInstanceAs (QuasiCompact (pullback.fst (jK V) Y₁.hom))
  have : IsSeparated G₁.hom := inferInstanceAs (IsSeparated (pullback.fst (jK V) Y₁.hom))
  have : QuasiCompact G₂.hom := inferInstanceAs (QuasiCompact (pullback.fst (jK V) Y₂.hom))
  have : IsSeparated G₂.hom := inferInstanceAs (IsSeparated (pullback.fst (jK V) Y₂.hom))
  have : Flat (Y₁ ⊗ Y₂).hom := inferInstanceAs (Flat (pullback.fst Y₁.hom Y₂.hom ≫ Y₁.hom))
  let p₁ : (G₁ ⊗ G₂).left ⟶ (TK V ⊗ Y₁).left := (fst G₁ G₂).left
  let p₂ : (G₁ ⊗ G₂).left ⟶ (TK V ⊗ Y₂).left := (snd G₁ G₂).left
  have hp : p₁ ≫ (fst (TK V) Y₁).left = p₂ ≫ (fst (TK V) Y₂).left := (Over.w (fst G₁ G₂)).trans (Over.w (snd G₁ G₂)).symm
  have hp' : p₁ ≫ (TK V ⊗ Y₁).hom = p₂ ≫ (TK V ⊗ Y₂).hom := by
    rw [← Over.w (fst (TK V) Y₁), ← Over.w (fst (TK V) Y₂), ← Category.assoc, hp, Category.assoc]
  obtain ⟨g, g₁, g₂⟩ : ∃ g : (G₁ ⊗ G₂).left ⟶ (Y₁ ⊗ Y₂).left, g ≫ (fst Y₁ Y₂).left = p₁ ≫ (snd (TK V) Y₁).left ∧
      g ≫ (snd Y₁ Y₂).left = p₂ ≫ (snd (TK V) Y₂).left :=
    ⟨pullback.lift (p₁ ≫ (snd (TK V) Y₁).left) (p₂ ≫ (snd (TK V) Y₂).left) (by
      rw [Category.assoc, Category.assoc, Over.w, Over.w, hp']), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨h, h₁, h₂⟩ : ∃ h : (TK V ⊗ Y₁ ⊗ Y₂).left ⟶ (G₁ ⊗ G₂).left, h ≫ p₁ = (TK V ◁ fst Y₁ Y₂).left ∧
      h ≫ p₂ = (TK V ◁ snd Y₁ Y₂).left :=
    ⟨pullback.lift (TK V ◁ fst Y₁ Y₂).left (TK V ◁ snd Y₁ Y₂).left (by
      show (TK V ◁ fst Y₁ Y₂).left ≫ (fst (TK V) Y₁).left = (TK V ◁ snd Y₁ Y₂).left ≫ (fst (TK V) Y₂).left
      rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_fst, whiskerLeft_fst]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hg : h ≫ g = (snd (TK V) (Y₁ ⊗ Y₂)).left := by
    apply pullback.hom_ext
    · show (h ≫ g) ≫ (fst Y₁ Y₂).left = _ ≫ (fst Y₁ Y₂).left
      rw [Category.assoc, g₁, ← Category.assoc, h₁, ← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
    · show (h ≫ g) ≫ (snd Y₁ Y₂).left = _ ≫ (snd Y₁ Y₂).left
      rw [Category.assoc, g₂, ← Category.assoc, h₂, ← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  obtain ⟨v', hv'⟩ := exists_sec hL (K' := K₁ ⊕ K₂)
    (φ' := Sum.elim (fun k => p₁ ≫ (snd (TK V) Y₁).left ≫ φ₁ k) (fun k => p₂ ≫ (snd (TK V) Y₂).left ≫ φ₂ k))
    (ε' := Sum.elim ε₁ ε₂) (fun U _ f => Finset.prod_congr rfl (by
      rintro (k | k) _
      · simp only [Sum.elim_inl]
        rw [← Category.assoc, g₁, Category.assoc]
      · simp only [Sum.elim_inr]
        rw [← Category.assoc, g₂, Category.assoc])) (pullSec L _ _ v g)
  obtain ⟨n, a', b', hab⟩ := (GlobalTheory.T.section_lin_comb_fiber_product_separated (FractionRing V) Z L hL G₁ G₂ K₁ K₂
    (fun k => (snd (TK V) Y₁).left ≫ φ₁ k) ε₁ (fun k => (snd (TK V) Y₂).left ≫ φ₂ k) ε₂).1 v'
  choose r hr σ hσ using fun i => exists_sec_of_generic_fibre V Z L hL Y₁ K₁ φ₁ ε₁ (a' i)
  choose s hs τ hτ using fun i => exists_sec_of_generic_fibre V Z L hL Y₂ K₂ φ₂ ε₂ (b' i)
  let c : Fin n → V := fun i => ∏ j ∈ Finset.univ.erase i, r j * s j
  have hc : ∀ i, c i * (r i * s i) = ∏ j, r j * s j := fun i =>
    Finset.prod_erase_mul Finset.univ (fun j => r j * s j) (Finset.mem_univ i)
  refine ⟨∏ j, r j * s j, Finset.prod_ne_zero_iff.2 fun j _ => mul_ne_zero (hr j) (hs j), n,
    fun i => SecOps.secScale (scal Y₁.hom (c i)) (σ i), τ, ?_⟩
  have val_sum : ∀ (T : Scheme.{0}) (ρ : T ⟶ (Y₁ ⊗ Y₂).left) (z : T) (J), Good L z J →
      sval (secSum fun i => mulSec L _ _ _ _
        (pullSec L _ _ (SecOps.secScale (scal Y₁.hom (c i)) (σ i)) (fst Y₁ Y₂).left)
        (pullSec L _ _ (τ i) (snd Y₁ Y₂).left)) ρ z J =
      ∑ i, sval (SecOps.secScale (scal Y₁.hom (c i)) (σ i)) (ρ ≫ (fst Y₁ Y₂).left) z J *
        sval (τ i) (ρ ≫ (snd Y₁ Y₂).left) z J := fun T ρ z J hJ =>
    (sval_sum _ ρ z hJ).trans (Finset.sum_congr rfl fun i _ => (sval_mul _ _ ρ z hJ).trans
      (congrArg₂ (· * ·) (sval_pull _ _ ρ z hJ) (sval_pull _ _ ρ z hJ)))
  have E : (secSum fun i => mulSec L _ _ _ _
        (pullSec L _ _ (SecOps.secScale (scal Y₁.hom (c i)) (σ i)) (fst Y₁ Y₂).left)
        (pullSec L _ _ (τ i) (snd Y₁ Y₂).left)) = SecOps.secScale (scal (Y₁ ⊗ Y₂).hom (∏ j, r j * s j)) v := by
    refine sec_ext_of_app_injective hL _ (app_generic_injective (Y₁ ⊗ Y₂)) fun y J hJ => ?_
    have q₀ : (h ≫ g) ≫ (Y₁ ⊗ Y₂).hom = (h ≫ p₁) ≫ (TK V ⊗ Y₁).hom := by
      rw [hg, h₁, Over.w, Over.w]
    have q₁ : ((h ≫ p₁) ≫ (snd (TK V) Y₁).left) ≫ Y₁.hom = (h ≫ p₁) ≫ (TK V ⊗ Y₁).hom := by
      rw [Category.assoc, Over.w]
    have q₂ : (h ≫ p₂) ≫ (TK V ⊗ Y₂).hom = (h ≫ p₁) ≫ (TK V ⊗ Y₁).hom := by
      rw [Category.assoc, Category.assoc, hp']
    have e₁ : (h ≫ g) ≫ (fst Y₁ Y₂).left = (h ≫ p₁) ≫ (snd (TK V) Y₁).left := by
      rw [Category.assoc, Category.assoc, g₁]
    have e₂ : (h ≫ g) ≫ (snd Y₁ Y₂).left = (h ≫ p₂) ≫ (snd (TK V) Y₂).left := by
      rw [Category.assoc, Category.assoc, g₂]
    have e₃ : sval v (h ≫ g) y J = ∑ i, sval (a' i) (h ≫ p₁) y J * sval (b' i) (h ≫ p₂) y J :=
      (sval_pull v g h y hJ).symm.trans ((hv' _ h y J hJ).symm.trans (hab _ h y J hJ))
    rw [val_sum _ _ y J hJ, sval_scale _ _ _ y hJ, ← hg, e₁, e₂, e₃, gs_scal_eq, q₀, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sval_scale _ _ _ y hJ, hσ i _ _ y J hJ, hτ i _ _ y J hJ, gs_scal_eq, gs_scal_eq, gs_scal_eq, q₁, q₂, ← hc i,
      map_mul, map_mul]
    ring
  intro T ρ z J hJ
  rw [← val_sum T ρ z J hJ, E, sval_scale _ _ _ z hJ]

end GlobalTheory
