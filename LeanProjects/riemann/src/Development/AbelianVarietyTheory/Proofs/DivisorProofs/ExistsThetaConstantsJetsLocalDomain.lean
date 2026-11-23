import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationSectionFirstPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.JetEx

open TrivSqZeroExt

variable {W : Type} [CommRing W]

theorem dual_isLocalRing [IsLocalRing W] : IsLocalRing (DualNumber W) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
  exact IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst

theorem fstHom_isLocalHom : IsLocalHom (TrivSqZeroExt.fstHom W W W).toRingHom :=
  ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩

abbrev red (W : Type) [CommRing W] : Sp W ⟶ Sp (DualNumber W) := spMap (TrivSqZeroExt.fstHom W W W).toRingHom

theorem red_closedPoint [IsLocalRing W] :
    letI := dual_isLocalRing (W := W)
    (red W).base (IsLocalRing.closedPoint W) = IsLocalRing.closedPoint (DualNumber W) := by
  letI := dual_isLocalRing (W := W)
  haveI := fstHom_isLocalHom (W := W)
  rw [Spec.map_base]
  exact IsLocalRing.comap_closedPoint _

theorem top_le_of_red [IsLocalRing W] {X : Scheme.{0}} (y : Sp (DualNumber W) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (red W ≫ y) ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  letI := dual_isLocalRing (W := W)
  rw [Scheme.preimage_eq_top_of_closedPoint_mem y (U := U) ?_]
  have := h (show IsLocalRing.closedPoint W ∈ (⊤ : (Sp W).Opens) from trivial)
  rw [← red_closedPoint]
  exact this

theorem valR_fst {X : Scheme.{0}} (y : Sp (DualNumber W) ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)) :
    (valR y U f).fst = valR (red W ≫ y) U f := by
  have h' : ⊤ ≤ (red W ≫ y) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage]; exact fun p _ => h trivial
  unfold valR
  rw [dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE (red W) y U ⊤ ⊤ h le_top]
  have n := congrArg (fun q => q.hom ((y.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom W W W).toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [show (red W).appLE ⊤ ⊤ le_top = (red W).appTop from (Scheme.Hom.app_eq_appLE _).symm]
  exact n.symm

end GlobalTheory.MBLow.JetEx

namespace GlobalTheory.MBLow.JetEx

open TrivSqZeroExt

variable {W : Type} [CommRing W]

theorem epsLift_fst {A : Over (Sp W)} [GrpObj A] (u : epsR W ⟶ A) :
    epsLift u ≫ (fst (baseOver (Sp W)) A).left = (epsR W).hom := by
  rw [epsLift, ← Over.comp_left, lift_fst]; rfl

theorem epsLift_snd {A : Over (Sp W)} [GrpObj A] (u : epsR W ⟶ A) :
    epsLift u ≫ (snd (baseOver (Sp W)) A).left = u.left := by
  rw [epsLift, ← Over.comp_left, lift_snd]

theorem red_epsLift {A : Over (Sp W)} [GrpObj A] (v v' : epsR W ⟶ A) (hv : IsTangent v) (hv' : IsTangent v') :
    red W ≫ epsLift v = red W ≫ epsLift v' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, ← Over.fst_left, epsLift_fst, epsLift_fst]
  · rw [Category.assoc, Category.assoc, ← Over.snd_left, epsLift_snd, epsLift_snd]
    exact hv.trans hv'.symm

theorem red_epsLift_snd {A : Over (Sp W)} [GrpObj A] (v : epsR W ⟶ A) (hv : IsTangent v) :
    (red W ≫ epsLift v) ≫ (snd (baseOver (Sp W)) A).left = 𝟙 (Sp W) ≫ eSec A := by
  rw [Category.assoc, epsLift_snd, Category.id_comp]
  exact hv

open Classical in
theorem exists_jets [IsLocalRing W] (P : PolAV (Sp W)) (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) {I : Type}
    (t : I → LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W))))) {g : ℕ} (v : Fin g → (epsR W ⟶ P.A))
    (hv : ∀ j, IsTangent (v j)) :
    ∃ (i₀ : P.L.ι) (c : Fin g → W) (ϑ : I → W) (J : I → Fin g → W),
      ⊤ ≤ (𝟙 (Sp W) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ ∧
      ∀ i j, valR (epsLift (v j)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀) ((t i).f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (𝟙 (Sp W)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl (ϑ i) + TrivSqZeroExt.inr (J i j + c j * ϑ i)) := by
  have hL := P.isLB
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ((eSec P.A : Sp W ⟶ P.A.left).base (IsLocalRing.closedPoint W))
  have htop : ⊤ ≤ (𝟙 (Sp W) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ := by
    rw [Category.id_comp, Scheme.preimage_eq_top_of_closedPoint_mem (eSec P.A : Sp W ⟶ P.A.left) hi₀]
  have hρt : ⊤ ≤ (𝟙 (Sp W)) ⁻¹ᵁ ((P.L.pull (eSec P.A)).U fun _ => i₀) := fun p _ =>
    Set.mem_iInter.2 fun _ => by
      have := htop (show p ∈ (⊤ : (Sp W).Opens) from trivial)
      exact this
  set u := valR (𝟙 (Sp W)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val with hu_def
  have hu : IsUnit u := by
    rw [hu_def, valR, dif_pos hρt]
    exact ((ρ.s _).isUnit.map _).map _
  set ui := Ring.inverse (u ^ k)
  have hui : u ^ k * ui = 1 := Ring.mul_inverse_cancel _ (hu.pow k)
  have hch : ∀ j, ⊤ ≤ (epsLift (v j)) ⁻¹ᵁ ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀) := fun j =>
    top_le_of_red _ _ fun p _ => Set.mem_iInter.2 fun _ => by
      have := htop (show p ∈ (⊤ : (Sp W).Opens) from trivial)
      rw [← red_epsLift_snd (v j) (hv j)] at this
      exact this
  refine ⟨i₀, 0, fun i => if hn : Nonempty (Fin g) then
      ui * (valR (epsLift (v hn.some)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀)
        ((t i).f fun _ => i₀)).fst else 0,
    fun i j => ui * (valR (epsLift (v j)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀)
        ((t i).f fun _ => i₀)).snd, htop, fun i j => ?_⟩
  have hn : Nonempty (Fin g) := ⟨j⟩
  simp only [dif_pos hn]
  have hf : (valR (epsLift (v hn.some)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀)
        ((t i).f fun _ => i₀)).fst =
      (valR (epsLift (v j)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀) ((t i).f fun _ => i₀)).fst := by
    rw [valR_fst _ _ (hch _), valR_fst _ _ (hch _), red_epsLift _ _ (hv _) (hv j)]
  rw [hf]
  ext
  · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr, add_zero]
    rw [← _root_.mul_assoc, hui, _root_.one_mul]
  · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, add_zero, Pi.zero_apply, zero_mul,
      smul_eq_mul, MulOpposite.smul_eq_mul_unop, zero_add, MulOpposite.unop_op]
    rw [← _root_.mul_assoc, hui, _root_.one_mul]

end GlobalTheory.MBLow.JetEx

namespace GlobalTheory.MBLow.JetEx

variable {W : Type} [CommRing W]

theorem exists_symLift_tr [IsNoetherianRing W] [IsLocalRing W] (P : PolAV (Sp W)) (ρ : LB.Gen (P.L.pull (eSec P.A)))
    (hρ : ρ.IsGen) (m : ℕ) (hm : Odd m) (hmu : IsUnit (m : W))
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (Over.mk (𝟙 (Sp W))))) (x : Over.mk (𝟙 (Sp W)) ⟶ P.A)
    (hx : x ^ (m ^ 2) = 1) :
    ∃ (U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk (𝟙 (Sp W))))
      (t : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk (𝟙 (Sp W))))),
      SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U ∧ Tr P ρ m th U t := by
  have hLaw : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hL := P.isLB
  let T : Over (Sp W) := Over.mk (𝟙 (Sp W))
  have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Sp W, ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    exact (by rw [Nat.cast_pow]; exact hmu.pow 2 : IsUnit ((m ^ 2 : ℕ) : W)).map e
  obtain ⟨hex, -⟩ := hLaw.symLift _ P (m ^ 2) hm.pow hu T x hx
  obtain ⟨V, hV, θ₀, hθ₀⟩ := hex (IsLocalRing.closedPoint W)
  have hVt : V = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem (𝟙 (Sp W)) hV
  subst hVt
  let h : T ⟶ overRes (T := T) ⊤ := Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  have hh : h ≫ overResι (T := T) ⊤ = 𝟙 T := Over.OverMorphism.ext T.left.toIso_inv_ι
  obtain ⟨θ, hθ⟩ := GlobalLift.exists_symLift_pull hL h hθ₀
  rw [← Category.assoc, hh, Category.id_comp] at hθ
  obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ P m
  have e₁ : (snd T P.A).left ≫ (mulA P.A m).left = (snd T P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α₁, hα₁, -⟩ := exists_gen hL (φ' := ![(snd T P.A).left, (snd T P.A ^ m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow m 2).symm
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨α, hα, hn⟩ := GlobalTheory.NormTheta.exists_normalised hL hρ m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) (by simp) α₁ hα₁
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _)
    ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  obtain ⟨t, ht⟩ := ThetaPtExist.exists_isTwistPull hL (translT P.A θ.pt) (translPt P.A θ.pt) (lift_snd _ _)
    ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) θ.φ θ.isGen s₁
  exact ⟨θ, t, hθ, α, s₁, hα, hn, hs₁, ht⟩

end GlobalTheory.MBLow.JetEx

namespace GlobalTheory.MBLow

theorem exists_thJet_local : ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (x : KeyIn W)
    (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → IsUnit (m : W) → ∀ (I : Type) (pt : I → (baseOver (Sp W) ⟶ x.P.A)),
    (∀ i, pt i ^ (m ^ 2) = 1) → ∃ ϑ J, ThJet x hg m pt ϑ J := by
  intro W _ _ _ _ x g hg m hm hmu I pt hpt
  choose U t hUt using fun i =>
    JetEx.exists_symLift_tr x.P x.rig x.rig_gen m hm hmu (TrSec.thSec x.P x.th) (pt i) (hpt i)
  obtain ⟨i₀, c, ϑ, J, htop, hval⟩ :=
    JetEx.exists_jets x.P x.rig (m ^ 2) t (fun j => x.v (j.cast hg.symm)) (fun j => x.basis.1 _)
  exact ⟨ϑ, J, TrSec.thSec x.P x.th, TrSec.projectionPullbackSectionBaseProduct_isInverseImage x.P x.th, U, t, i₀, c, fun i => hUt i, htop, hval⟩

end GlobalTheory.MBLow
