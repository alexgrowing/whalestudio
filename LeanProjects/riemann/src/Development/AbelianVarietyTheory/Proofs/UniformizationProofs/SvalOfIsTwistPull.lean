import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.FinrankComplexReal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ThetaLin

theorem gs_scal_comp {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y)
    (z : Z) (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

theorem exists_linearEquiv {F : Type} [CommRing F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (q : Y ⟶ Spec (CommRingCat.of F)) (pr m : Y ⟶ X) (τ σ : Y ⟶ Y) (hm : τ ≫ pr = m) (h₁ : σ ≫ τ = 𝟙 Y)
    (h₂ : τ ≫ σ = 𝟙 Y) (hq : τ ≫ q = q) (k : ℤ)
    (u : LB.Gen (LB.LinComb L (K := Fin 2) ![pr, m] ![k, -k])) (hu : u.IsGen) :
    ∃ Φ : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) ≃ₗ[F]
        SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∀ v (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval (Φ v).sec r z J = (val u r z J).val * sval v.sec (r ≫ τ) z J := by
  have ex : ∀ v : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∃ w : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval w.sec r z J = (val u r z J).val * sval v.sec (r ≫ τ) z J := fun v => by
    obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => pr) (ε' := fun _ => k)
      (fun U _ h => by
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
          hm, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, mul_inv_cancel_comm_assoc])
      (pullMulSec v.sec τ u hu)
    exact ⟨SecMod.mk q s', fun Z r z J hJ =>
      (hs' Z r z J hJ).trans ((sval_pullMulSec _ _ u hu r z hJ).trans (_root_.mul_comm _ _))⟩
  choose f hf using ex
  have ext : ∀ v w : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      (∀ y J, Good L y J → sval v.sec (𝟙 Y) y J = sval w.sec (𝟙 Y) y J) → v = w :=
    fun v w h => SecMod.ext (sec_ext_val hL h)
  let Φ₀ : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) →ₗ[F]
      SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) :=
    { toFun := f
      map_add' := fun v w => ext _ _ fun y J hJ => by
        rw [SecMod.sval_add hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, SecMod.sval_add hJ, mul_add]
      map_smul' := fun c v => ext _ _ fun y J hJ => by
        rw [RingHom.id_apply, SecMod.sval_smul hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, SecMod.sval_smul hJ,
          gs_scal_comp q (𝟙 Y ≫ τ), Category.assoc, hq, Category.id_comp q, mul_left_comm] }
  refine ⟨LinearEquiv.ofBijective Φ₀ ⟨fun v w h => ext _ _ fun y J hJ => ?_, fun w => ?_⟩, hf⟩
  · have e : f v = f w := h
    have := (hf v _ σ y J hJ).symm.trans (e ▸ hf w _ σ y J hJ)
    rwa [h₁, Units.mul_right_inj] at this
  · have hv := DVR.pullGen_isGen _ _ _ _ (DVR.invGen_isGen _ _ _ _ hu) σ
    have h₃ : σ ≫ m = pr := by rw [← hm, ← Category.assoc, h₁, Category.id_comp]
    obtain ⟨s, hs⟩ := exists_sec (φ' := fun _ : Fin 1 => pr) (ε' := fun _ => k) hL (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        h₃, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, inv_inv, mul_inv_cancel_left])
      (pullMulSec w.sec σ _ hv)
    refine ⟨SecMod.mk q s, ext _ _ fun y J hJ => (hf _ _ _ y J hJ).trans ?_⟩
    rw [SecMod.sec_mk, hs _ _ y J hJ, sval_pullMulSec _ σ _ hv _ y hJ, val_pull hJ, val_inv, Category.assoc, h₂,
      Category.comp_id, mul_left_comm, Units.mul_inv, _root_.mul_one]

section Twist

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
  {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}

theorem sval_of_isTwistPull {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (H : IsTwistPull A L ψ m hm a b α s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' r z J = (val α r z J).val * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  have hz := hJ.mem ![(snd T A).left, m.left] r
  have key : ∀ j : Fin 2 → L.ι, r z ∈ LB.wchart L ![(snd T A).left, m.left] j →
      gs r z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) (s'.f (fun _ => j 0)) =
        (gm r z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j)).val *
          gs (r ≫ ψ.left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
            (s.f (fun _ => j 1)) := fun j hz =>
    (gs_res r z _ hz _).symm.trans ((congrArg (gs r z _) (H j)).trans ((gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit r z _ hz _) ((gs_res r z _ hz _).trans
        (gs_pull r ψ.left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
          (chart_le_pull A L ψ m hm j hz) _)))))
  have e₁ := sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J
    (fun _ => J (r ≫ m.left)) (fun _ => by rw [Category.assoc, e])
  exact (key _ hz).trans (congrArg _ e₁.symm)

theorem isTwistPull_of_sval (hL : L.IsLB) (hα : α.IsGen) {s : LB.Sec (LPow A L b T)}
    {s' : LB.Sec (LPow A L a T)}
    (H : ∀ y J, Good L y J → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y J = (val α (𝟙 _) y J).val * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y J) :
    IsTwistPull A L ψ m hm a b α s s' := by
  intro j
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have h0 := chart_le_zero A L m j hy
  have h1 := chart_le_pull A L ψ m hm j hy
  refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ y _ hy _) ((gs_res _ y _ hy _).trans
      (gs_pull _ ψ.left y _ h1 _)))).symm)
  refine (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y h0
    (Good.mem hJ _ _)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val (gen_trans hα (𝟙 _) y hy (Good.mem hJ _ _)))
    (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y h1
    (Good.mem hJ _ _))).symm
  refine (congrArg _ (H y J hJ)).trans ?_
  rw [Units.val_mul]
  refine Eq.trans ?_ (_root_.mul_mul_mul_comm _ _ _ _)
  rw [← Units.val_mul]
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
  have e' : (𝟙 _ ≫ ψ.left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by rw [Category.assoc, e]
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, zpow_neg]
  rw [e']
  exact (inv_mul_cancel_right _ _).symm

end Twist

section Transl

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S}

theorem lift_translT {T' : Over S} (ρ : T' ⟶ T) (x : T' ⟶ A) (c : T ⟶ A) :
    lift ρ x ≫ translT A c = lift ρ ((ρ ≫ c) * x) := by
  have e : translPt A c = (fst T A ≫ c) * snd T A := rfl
  rw [translT, comp_lift, lift_fst, e, MonObj.comp_mul, lift_fst_assoc, lift_snd]

theorem translT_comp (c d : T ⟶ A) (h : d * c = 1) : translT A c ≫ translT A d = 𝟙 _ := by
  have e : translPt A c = (fst T A ≫ c) * snd T A := rfl
  rw [translT, lift_translT, e, ← _root_.mul_assoc, ← MonObj.comp_mul, h, MonObj.comp_one, _root_.one_mul,
    lift_fst_snd]

end Transl

theorem main : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (k : ℕ) (θ : ThetaGrp P.A P.L (k : ℤ) (Over.mk p)), ∃ Φ : EA P p k ≃ₗ[F] EA P p k, (∀ v, IsActOf P.A P.L (k : ℤ) θ v.sec (Φ v).sec) ∧ (∀ v v', IsActOf P.A P.L (k : ℤ) θ v v' → v' = (Φ (SecMod.mk _ v)).sec) ∧ ∀ (v : EA P p k) (T : Over S) (ρ : T ⟶ Over.mk p) (x : T ⟶ P.A) (z : T.left) (J), Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((k : ℕ) : ℤ)) (Φ v).sec (lift ρ x).left z J = (val (L := P.L) (φ := ![(snd (Over.mk p) P.A).left, (translPt P.A θ.pt).left]) (ε := ![(k : ℤ), -(k : ℤ)]) θ.φ (lift ρ x).left z J).val * sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((k : ℕ) : ℤ)) v.sec (lift ρ ((ρ ≫ θ.pt) * x)).left z J := by
  intro S P F _ p k θ
  obtain ⟨Φ, hΦ⟩ := exists_linearEquiv (F := F) P.isLB (fst (Over.mk p) P.A).left (snd (Over.mk p) P.A).left
    (translPt P.A θ.pt).left (translT P.A θ.pt).left (translT P.A θ.pt⁻¹).left
    (by rw [← Over.comp_left, translT, lift_snd])
    (by rw [← Over.comp_left, translT_comp _ _ _ (mul_inv_cancel _), Over.id_left])
    (by rw [← Over.comp_left, translT_comp _ _ _ (inv_mul_cancel _), Over.id_left])
    (((Over.comp_left _ _ _ _ _).symm.trans (by rw [translT, lift_fst]))) (k : ℤ) θ.φ θ.isGen
  refine ⟨Φ, fun v => isTwistPull_of_sval P.A P.isLB θ.isGen fun y J hJ => hΦ v _ _ y J hJ, fun v v' h => ?_,
    fun v T ρ x z J hJ => ?_⟩
  · exact DVR.SecOps.sec_ext (sec_ext_val P.isLB fun y J hJ =>
      (sval_of_isTwistPull P.A h (𝟙 _) y hJ).trans (hΦ (SecMod.mk _ v) _ _ y J hJ).symm)
  · refine (hΦ v _ _ z J hJ).trans ?_
    rw [← Over.comp_left, lift_translT]
    rfl

end GlobalTheory.ThetaLin

end
