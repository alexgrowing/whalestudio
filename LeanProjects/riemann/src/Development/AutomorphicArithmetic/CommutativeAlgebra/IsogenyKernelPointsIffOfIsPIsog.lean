import Development.AutomorphicArithmetic.SpecialMaps.QuotObjDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomTorsionFree
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfKillsKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFieldSmoothOfRelativeDimensionExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsDualPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiadditiveClassEqPoincarePullbackUniqueHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointUpToIntegerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointUniqueAdditiveScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointCancelNonzeroMultiple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsTypeTjPIsogeny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointLocallyConstantGeomPoinStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO
namespace UpperTheory.KEq

section
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

private theorem hom_cancel :
    ∀ (Ω : Type) [Field Ω] (A B : Over (Sp Ω)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B →
      ∀ (f g : A ⟶ B), IsMonHom f → IsMonHom g → ∀ (n : ℕ), 0 < n → f ^ n = g ^ n → f = g := by
  intro Ω _ A B _ _ _ _ hA hB f g hf hg n hn hfg
  obtain ⟨dA, hsA⟩ := GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists Ω A hA
  obtain ⟨dB, hsB⟩ := GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists Ω B hB
  let A' : GlobalTheory.AV.AbVar Ω := ⟨A, hA, dA, hsA⟩
  let B' : GlobalTheory.AV.AbVar Ω := ⟨B, hB, dB, hsB⟩
  let F : A' ⟶ B' := GlobalTheory.AV.AbVar.Hom.mk (A := A') (B := B') f
  let G : A' ⟶ B' := GlobalTheory.AV.AbVar.Hom.mk (A := A') (B := B') g
  have hFG : GlobalTheory.AV.AbVar.Hom.hom (F - G) = f / g := rfl
  have key : GlobalTheory.AV.AbVar.Hom.hom ((n : ℤ) • (F - G)) = 1 := by
    rw [GlobalTheory.AV.AbVar.zsmul_hom, hFG, zpow_natCast, div_pow, hfg, div_self']
  have h0 : (n : ℤ) • (F - G) = 0 :=
    GlobalTheory.AV.AbVar.hom_ext (by rw [key, GlobalTheory.AV.AbVar.zero_hom])
  have h1 := GlobalTheory.AV.AbVar.hom_torsionFree Ω A' B' n (F - G) (by exact_mod_cast hn.ne') h0
  have h2 : F = G := sub_eq_zero.mp h1
  exact congrArg GlobalTheory.AV.AbVar.Hom.hom h2

end

section
open GlobalTheory.AV GlobalTheory.AV.AbVar

private theorem eq_zero_of_zsmul_eq_zero {K : Type} [Field K] (A B : AbVar K)
    (β : GlobalTheory.CechPic.Pic (A.X ⊗ B.X).left)
    (hadd : ∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ B.X),
      GlobalTheory.CechPic.pull (lift (a * a') t).left β =
        GlobalTheory.CechPic.pull (lift a t).left β + GlobalTheory.CechPic.pull (lift a' t).left β)
    (hnorm : GlobalTheory.CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ B.X)).left β = 0)
    (m : ℤ) (hm : m ≠ 0) (hmβ : m • β = 0) : β = 0 := by
  obtain ⟨A', P, hdual, -⟩ := GlobalTheory.T.abelianVariety_exists_dual_pair K A
  have hP := hdual.1
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom K A A' B P hP β hadd hnorm
  obtain ⟨ψ0, -, huniq⟩ := GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom K A A' B P hP 0 (by intros; simp) (by simp)
  have e1 : (0 : GlobalTheory.CechPic.Pic (A.X ⊗ B.X).left) =
      GlobalTheory.AbDual.evc hP.isLB (fst A.X B.X) (snd A.X B.X ≫ GlobalTheory.AV.AbVar.Hom.hom (m • ψ)) := by
    rw [GlobalTheory.AV.AbVar.zsmul_hom, GlobalTheory.AV.AbVar.AdjCalc.comp_zpow', (GlobalTheory.AdjCancel.evc_zpow hP _ _ m).1,
      ← hψ, hmβ]
  have e2 : (0 : GlobalTheory.CechPic.Pic (A.X ⊗ B.X).left) =
      GlobalTheory.AbDual.evc hP.isLB (fst A.X B.X) (snd A.X B.X ≫ GlobalTheory.AV.AbVar.Hom.hom (0 : B ⟶ A')) := by
    rw [GlobalTheory.AV.AbVar.zero_hom, MonObj.comp_one, (GlobalTheory.AdjCancel.evc_zpow hP (fst A.X B.X) (snd A.X B.X ≫ GlobalTheory.AV.AbVar.Hom.hom ψ) 0).2]
  have hm0 : m • ψ = 0 := (huniq _ e1).trans (huniq _ e2).symm
  have hψ0 := GlobalTheory.AV.AbVar.hom_torsionFree K B A' m ψ hm hm0
  rw [hψ, hψ0, GlobalTheory.AV.AbVar.zero_hom, MonObj.comp_one,
    (GlobalTheory.AdjCancel.evc_zpow hP (fst A.X B.X) (snd A.X B.X ≫ GlobalTheory.AV.AbVar.Hom.hom ψ) 0).2]

end

private theorem pic_eq_zero :
    ∀ (Ω : Type) [Field Ω] (A B : Over (Sp Ω)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ β : GlobalTheory.CechPic.Pic (A ⊗ B).left, (∀ (Y : Over (Sp Ω)) (a a' : Y ⟶ A) (t : Y ⟶ B), GlobalTheory.CechPic.pull (lift (a * a') t).left β = GlobalTheory.CechPic.pull (lift a t).left β + GlobalTheory.CechPic.pull (lift a' t).left β) → GlobalTheory.CechPic.pull (lift (𝟙 A) (1 : A ⟶ B)).left β = 0 → ∀ n : ℕ, 0 < n → n • β = 0 → β = 0 := by
  intro Ω _ A B _ _ _ _ hA hB β hadd hnorm n hn hnβ
  obtain ⟨dA, hsA⟩ := GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists Ω A hA
  obtain ⟨dB, hsB⟩ := GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists Ω B hB
  let A' : GlobalTheory.AV.AbVar Ω := ⟨A, hA, dA, hsA⟩
  let B' : GlobalTheory.AV.AbVar Ω := ⟨B, hB, dB, hsB⟩
  refine eq_zero_of_zsmul_eq_zero A' B' β hadd hnorm (n : ℤ) (by exact_mod_cast hn.ne') ?_
  rw [natCast_zsmul]
  exact hnβ

private theorem ker_pow :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (Ω : Type) [Field Ω] (σ : Sp Ω ⟶ Sp R) (o : Obj b N σ), ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over (Sp Ω)) (x : T ⟶ o.A), (∀ (Y : Over (Sp Ω)) (z : Y ⟶ T) (y : Y ⟶ o.A), GlobalTheory.BirigidPow.val o.isLB (z ≫ x) y = 0) → x ^ e = 1 := by
  intro p _ D R _ b N Ω _ σ o
  obtain ⟨e, he, hk⟩ := o.kerP
  refine ⟨e, he, fun T x hx => hk T x ?_⟩
  have h0 := hx (o.A ⊗ T) (snd o.A T) (fst o.A T)
  rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB o.isLB _), GlobalTheory.CechPic.cls_pull o.isLB _ (pull_isLB o.isLB _)]
  exact h0

private theorem val_symm :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (T : Over S) (x y : T ⟶ o.A), GlobalTheory.BirigidPow.val o.isLB x y = GlobalTheory.BirigidPow.val o.isLB y x := by
  intro p _ D R _ b N S s o T x y
  have e : GlobalTheory.CechPic.cls o.P o.isLB =
      GlobalTheory.CechPic.pull (lift (snd o.A o.A) (fst o.A o.A)).left (GlobalTheory.CechPic.cls o.P o.isLB) := by
    rw [← GlobalTheory.CechPic.cls_pull o.isLB _ (pull_isLB o.isLB _)]
    exact (GlobalTheory.CechPic.cls_eq_iff _ _).mpr o.symm
  unfold GlobalTheory.BirigidPow.val
  conv_lhs => rw [e]
  rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd]

open GlobalTheory.UPel.HT.ESDual in
private theorem val_adj_left (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (Ω : Type)
    [Field Ω] (σ : Sp Ω ⟶ Sp R) (o o' : Obj b N σ) (c : ℕ) (ψ : o.A ⟶ o'.A) (φ : o'.A ⟶ o.A)
    (hI : IsPIsog c o o' ψ) (hφ : IsMonHom φ) (_ : ψ ≫ φ = (𝟙 o.A) ^ c) (h2 : φ ≫ ψ = (𝟙 o'.A) ^ c)
    (T : Over (Sp Ω)) (x : T ⟶ o.A) (y : T ⟶ o'.A) :
    GlobalTheory.BirigidPow.val o'.isLB (x ≫ ψ) y = GlobalTheory.BirigidPow.val o.isLB x (y ≫ φ) := by
  haveI := hφ
  rw [val_symm p D R b N (Sp Ω) σ o' T (x ≫ ψ) y, GlobalTheory.UPel.HT.ESDual.val_adj hI h2 y x,
    val_symm p D R b N (Sp Ω) σ o T (y ≫ φ) x]

private theorem hom_eq_of_val :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (Ω : Type) [Field Ω] (σ : Sp Ω ⟶ Sp R) (o₁ o₂ : Obj b N σ) (f g : o₁.A ⟶ o₂.A), IsMonHom f → IsMonHom g → (∀ (T : Over (Sp Ω)) (x : T ⟶ o₁.A) (y : T ⟶ o₂.A), GlobalTheory.BirigidPow.val o₂.isLB y (x ≫ f) = GlobalTheory.BirigidPow.val o₂.isLB y (x ≫ g)) → f = g := by
  intro p _ D R _ b N Ω _ σ o₁ o₂ f g hf hg hfg
  obtain ⟨e, he, hk⟩ := ker_pow p D R b N Ω σ o₂
  have hd : (f * g⁻¹) ^ e = 1 := by
    apply hk o₁.A (f * g⁻¹)
    intro Y z y
    rw [val_symm p D R b N (Sp Ω) σ o₂ Y (z ≫ (f * g⁻¹)) y]
    have h1 := GlobalTheory.BirigidPow.val_mul_right o₂.isLB o₂.ab o₂.ample o₂.rig₁ o₂.rig₂ y (z ≫ (f * g⁻¹)) (z ≫ g)
    rw [← MonObj.comp_mul, inv_mul_cancel_right, hfg Y z y] at h1
    simpa using h1
  rw [mul_pow, inv_pow, mul_inv_eq_one] at hd
  have hpos : 0 < e := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    rw [Nat.coprime_zero_left] at he
    exact (Fact.out : p.Prime).ne_one he
  exact hom_cancel Ω o₁.A o₂.A o₁.ab o₂.ab f g hf hg e hpos hd

namespace AdjointAveraging

open GlobalTheory.BirigidPow

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {Ω : Type} [Field Ω] {σ : Sp Ω ⟶ Sp R}

private noncomputable def av (o : Obj b N σ) : GlobalTheory.AV.AbVar Ω :=
  haveI : ConnectedSpace (Sp Ω) := GlobalTheory.AbelianDim.connectedSpace_spec_of_isLocalRing Ω
  { X := o.A
    ab := o.ab
    dim := (GlobalTheory.AbelianDim.exists_relDim_of_connected o.A o.ab).choose
    smooth := (GlobalTheory.AbelianDim.exists_relDim_of_connected o.A o.ab).choose_spec }

private noncomputable def dg (o : Obj b N σ) : GlobalTheory.CechPic.Pic o.A.left :=
  val o.isLB (𝟙 o.A) (𝟙 o.A)

private theorem val_comp {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    {P : LB (G2 A).left} (hP : P.IsLB) {T T' : Over S} (z : T' ⟶ T) (x y : T ⟶ A) :
    GlobalTheory.CechPic.pull z.left (val hP x y) = val hP (z ≫ x) (z ≫ y) := by
  unfold GlobalTheory.BirigidPow.val
  rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, comp_lift]

private theorem dg_ample (o : Obj b N σ) : GlobalTheory.AV.AbVar.IsAmpleCls (A := av o) (dg o) :=
  ⟨o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left, pull_isLB o.isLB _, o.ample,
    GlobalTheory.CechPic.cls_pull o.isLB _ (pull_isLB o.isLB _)⟩

private theorem lam_dg (o : Obj b N σ) {Y : Over (Sp Ω)} (x y : Y ⟶ o.A) :
    GlobalTheory.AV.AbVar.lam (A := av o) (dg o) x y = 2 • val o.isLB x y := by
  have hv : ∀ z : Y ⟶ o.A, GlobalTheory.CechPic.pull z.left (dg o) = val o.isLB z z := by
    intro z
    unfold dg GlobalTheory.BirigidPow.val
    rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
  show GlobalTheory.CechPic.pull (x * y).left (dg o) - GlobalTheory.CechPic.pull x.left (dg o) -
    GlobalTheory.CechPic.pull y.left (dg o) = 2 • val o.isLB x y
  rw [hv, hv, hv, val_mul_left o.isLB o.ab o.ample o.rig₁ o.rig₂,
    val_mul_right o.isLB o.ab o.ample o.rig₁ o.rig₂,
    val_mul_right o.isLB o.ab o.ample o.rig₁ o.rig₂,
    val_symm p D R b N _ σ o Y y x]
  abel

private theorem cancel (o₁ o₂ : Obj b N σ) (f : o₂.A ⟶ o₁.A) [IsMonHom f] (g : o₁.A ⟶ o₂.A)
    [IsMonHom g] (m l : ℕ) (hm : 0 < m)
    (H : ∀ (Y : Over (Sp Ω)) (y : Y ⟶ o₂.A) (x : Y ⟶ o₁.A),
      (m * l) • val o₁.isLB (y ≫ f) x = m • val o₂.isLB y (x ≫ g))
    (Y : Over (Sp Ω)) (y : Y ⟶ o₂.A) (x : Y ⟶ o₁.A) :
    l • val o₁.isLB (y ≫ f) x = val o₂.isLB y (x ≫ g) := by
  let β : GlobalTheory.CechPic.Pic (o₂.A ⊗ o₁.A).left :=
    l • val o₁.isLB (fst o₂.A o₁.A ≫ f) (snd o₂.A o₁.A) - val o₂.isLB (fst o₂.A o₁.A) (snd o₂.A o₁.A ≫ g)
  have hpb : ∀ (Y : Over (Sp Ω)) (y : Y ⟶ o₂.A) (x : Y ⟶ o₁.A),
      GlobalTheory.CechPic.pull (lift y x).left β = l • val o₁.isLB (y ≫ f) x - val o₂.isLB y (x ≫ g) := by
    intro Y y x
    simp only [β, map_sub, map_nsmul, val_comp, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc]
  have hβ : β = 0 := by
    refine pic_eq_zero Ω o₂.A o₁.A o₂.ab o₁.ab β ?_ ?_ m hm ?_
    · intro Y a a' t
      rw [hpb, hpb, hpb, MonObj.mul_comp, val_mul_left o₁.isLB o₁.ab o₁.ample o₁.rig₁ o₁.rig₂,
        val_mul_left o₂.isLB o₂.ab o₂.ample o₂.rig₁ o₂.rig₂, smul_add]
      abel
    · rw [hpb, Category.id_comp, MonObj.one_comp, val_one_right o₁.isLB o₁.rig₂,
        val_one_right o₂.isLB o₂.rig₂, smul_zero, sub_zero]
    · have hH := H (o₂.A ⊗ o₁.A) (fst o₂.A o₁.A) (snd o₂.A o₁.A)
      simp only [β, smul_sub, smul_smul]
      rw [hH, sub_self]
  have := hpb Y y x
  rw [hβ, map_zero] at this
  exact (sub_eq_zero.mp this.symm)

end AdjointAveraging

open AdjointAveraging in
private theorem exists_adjoint :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (Ω : Type) [Field Ω] (σ : Sp Ω ⟶ Sp R) (o₁ o₂ : Obj b N σ) (κ : o₂.A ⟶ o₁.A), IsMonHom κ → ∃ (e : ℕ) (ν : o₁.A ⟶ o₂.A), e.Coprime p ∧ IsMonHom ν ∧ ∀ (T : Over (Sp Ω)) (x : T ⟶ o₁.A) (y : T ⟶ o₂.A), GlobalTheory.BirigidPow.val o₂.isLB y (x ≫ ν) = e • GlobalTheory.BirigidPow.val o₁.isLB (y ≫ κ) x := by
  intro p _ D R _ b N Ω _ σ o₁ o₂ κ hκ
  have hp := (Fact.out : p.Prime)
  let fκ : av o₂ ⟶ av o₁ := @GlobalTheory.AV.AbVar.Hom.mk _ _ (av o₂) (av o₁) κ hκ
  obtain ⟨n, h, hn, hadj⟩ := GlobalTheory.T.exists_adjoint_up_to_integer Ω (av o₂) (av o₁) (dg o₂) (dg o₁) (dg_ample o₂) fκ
  obtain ⟨ν₀, hν₀, hνdef⟩ : ∃ ν₀ : o₁.A ⟶ o₂.A, IsMonHom ν₀ ∧ ν₀ = GlobalTheory.AV.AbVar.Hom.hom h :=
    ⟨_, (Additive.toMul h).2, rfl⟩
  have H1 : ∀ (Y : Over (Sp Ω)) (y : Y ⟶ o₂.A) (x : Y ⟶ o₁.A),
      (2 * n) • GlobalTheory.BirigidPow.val o₁.isLB (y ≫ κ) x = 2 • GlobalTheory.BirigidPow.val o₂.isLB y (x ≫ ν₀) := by
    intro Y y x
    have e := GlobalTheory.AV.AbVar.AdjCalc.isAdj_pt hadj (Y := Y) y x
    have e' : (n : ℤ) • (2 • GlobalTheory.BirigidPow.val o₁.isLB (y ≫ κ) x) =
        2 • GlobalTheory.BirigidPow.val o₂.isLB y (x ≫ ν₀) := by
      rw [← lam_dg o₁ (y ≫ κ) x, ← lam_dg o₂ y (x ≫ ν₀), hνdef]
      exact e
    rw [natCast_zsmul, smul_smul, mul_comm] at e'
    exact e'
  have H2 : ∀ (Y : Over (Sp Ω)) (y : Y ⟶ o₂.A) (x : Y ⟶ o₁.A),
      n • GlobalTheory.BirigidPow.val o₁.isLB (y ≫ κ) x = GlobalTheory.BirigidPow.val o₂.isLB y (x ≫ ν₀) :=
    cancel o₁ o₂ κ ν₀ 2 n two_pos H1
  obtain ⟨a, n', hn', hnn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.one_lt.ne'
  have hcop : n'.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn').symm
  obtain ⟨e₂, he₂, hker₂⟩ := ker_pow p D R b N Ω σ o₂
  have hkill : ∀ (T : Over (Sp Ω)) (x : T ⟶ o₁.A), x ^ (p ^ a) = 1 → x ≫ ν₀ = 1 := by
    intro T x hx
    have h1 : (x ≫ ν₀) ^ e₂ = 1 := by
      apply hker₂
      intro Y w y
      rw [val_symm p D R b N _ σ o₂ Y, ← Category.assoc, ← H2, hnn, mul_comm, mul_smul,
        ← GlobalTheory.BirigidPow.val_pow_right o₁.isLB o₁.ab o₁.ample o₁.rig₁ o₁.rig₂, ← MonObj.comp_pow, hx,
        MonObj.comp_one, GlobalTheory.BirigidPow.val_one_right o₁.isLB o₁.rig₂, smul_zero]
    have h2 : (x ≫ ν₀) ^ (p ^ a) = 1 := by
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    have hg : Nat.gcd e₂ (p ^ a) = 1 := Nat.Coprime.pow_right a he₂
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [hg, pow_one] at this
  let q : av o₁ ⟶ av o₁ := ((p ^ a : ℕ) : ℤ) • 𝟙 (av o₁)
  have hq := (GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree Ω (av o₁) ((p ^ a : ℕ) : ℤ) (by exact_mod_cast (pow_pos hp.pos a).ne')).1
  have hqhom : ∀ (T : Over (Sp Ω)) (x : T ⟶ o₁.A), x ≫ GlobalTheory.AV.AbVar.Hom.hom q = x ^ (p ^ a) := by
    intro T x
    have e1 := congrArg (fun u => x ≫ u)
      (GlobalTheory.AV.AbVar.zsmul_hom (A := av o₁) (B := av o₁) ((p ^ a : ℕ) : ℤ) (𝟙 (av o₁)))
    have e2 := GlobalTheory.AV.AbVar.AdjCalc.comp_zpow' (G := o₁.A) x (𝟙 o₁.A) ((p ^ a : ℕ) : ℤ)
    rw [Category.comp_id, zpow_natCast] at e2
    exact e1.trans e2
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_factor_through_isogeny_of_kills_kernel Ω (av o₁) (av o₁) (av o₂) q h hq (fun T x hx => by
    have := hkill T x ((hqhom T x).symm.trans hx)
    rw [hνdef] at this
    exact this)
  obtain ⟨ν, hν, hνg⟩ : ∃ ν : o₁.A ⟶ o₂.A, IsMonHom ν ∧ ν = GlobalTheory.AV.AbVar.Hom.hom g :=
    ⟨_, (Additive.toMul g).2, rfl⟩
  have key : ∀ (Y : Over (Sp Ω)) (x : Y ⟶ o₁.A), x ≫ ν₀ = (x ^ (p ^ a)) ≫ ν := by
    intro Y x
    rw [hνdef, hνg, ← hg, ← hqhom]
    exact (Category.assoc x (GlobalTheory.AV.AbVar.Hom.hom q) (GlobalTheory.AV.AbVar.Hom.hom g)).symm
  refine ⟨n', ν, hcop, hν, fun T x y => ?_⟩
  have H3 : ∀ (Y : Over (Sp Ω)) (y : Y ⟶ o₂.A) (x : Y ⟶ o₁.A),
      (p ^ a * n') • GlobalTheory.BirigidPow.val o₁.isLB (y ≫ κ) x =
        p ^ a • GlobalTheory.BirigidPow.val o₂.isLB y (x ≫ ν) := by
    intro Y y x
    rw [← hnn, H2, key, MonObj.pow_comp,
      GlobalTheory.BirigidPow.val_pow_right o₂.isLB o₂.ab o₂.ample o₂.rig₁ o₂.rig₂]
  exact (cancel o₁ o₂ κ ν (p ^ a) n' (pow_pos hp.pos a) H3 T y x).symm

private noncomputable def avOf {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {Ω : Type} [Field Ω] {σ : Sp Ω ⟶ Sp R} (o : Obj b N σ) : GlobalTheory.AV.AbVar Ω :=
  { X := o.A
    ab := o.ab
    dim := (GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists Ω o.A o.ab).choose
    smooth := (GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists Ω o.A o.ab).choose_spec }

private theorem idPow_comp {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (f : A ⟶ B) [IsMonHom f] (n : ℕ) : ((𝟙 A) ^ n) ≫ f = f ^ n := by
  rw [MonObj.pow_comp, Category.id_comp]

private theorem act_natCast {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {Ω : Type} [Field Ω] {σ : Sp Ω ⟶ Sp R} (o : Obj b N σ) (k : ℕ) : o.act.act (k : D.O) = 𝟙 o.A ^ k := by
  have h0 : o.act.act (0 : D.O) = 1 := by
    have h := o.act.add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := o.act.act 0) (by rw [_root_.mul_one]; exact h.symm)
  induction k with
  | zero => rw [Nat.cast_zero, h0, _root_.pow_zero]
  | succ k ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one, _root_.pow_succ]

private theorem exists_div :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N E : ℕ) (r : ℤ) (Ω : Type) [Field Ω] (σ : Sp Ω ⟶ Sp R) (o₁ o₂ o' : Obj b N σ) (ψ₁ : o₁.A ⟶ o'.A) (φ₁ : o'.A ⟶ o₁.A) (φ₂ : o'.A ⟶ o₂.A) (β : 𝓞 D.F), IsPIsog (p ^ E) o₁ o' ψ₁ → IsMonHom φ₁ → IsMonHom φ₂ → ψ₁ ≫ φ₁ = (𝟙 o₁.A) ^ (p ^ E) → φ₁ ≫ ψ₁ = (𝟙 o'.A) ^ (p ^ E) → (∀ a ∈ uIdeal D r ^ E, ∃ v : 𝓞 D.F, a * β = v * (p : 𝓞 D.F) ^ E) → (∀ (T : Over (Sp Ω)) (x : T ⟶ o'.A), (∃ e : ℕ, KilledBy o' (uIdeal D r ^ e) x) → (x ≫ φ₁ = 1 ↔ x ≫ φ₂ = 1)) → ∃ κ : o₁.A ⟶ o₂.A, IsMonHom κ ∧ o₁.act.act (algebraMap (𝓞 D.F) D.O β) ≫ ψ₁ ≫ φ₂ = κ ^ (p ^ E) := by
  intro p _ D R _ b N E r Ω _ σ o₁ o₂ o' ψ₁ φ₁ φ₂ β h₁ hφ₁ hφ₂ e₁ e₁' hβ H
  haveI := h₁.2.1
  haveI := hφ₂
  haveI := o₁.act.hom (algebraMap (𝓞 D.F) D.O β)
  have hker' : ∀ (T : Over (Sp Ω)) (x : T ⟶ o₁.A), x ≫ (𝟙 o₁.A) ^ (p ^ E) = 1 →
      x ≫ o₁.act.act (algebraMap (𝓞 D.F) D.O β) ≫ ψ₁ ≫ φ₂ = 1 := by
    intro T x hx0
    have hx : x ^ (p ^ E) = 1 := by rw [← hx0, MonObj.comp_pow, Category.comp_id]
    have hy1 : (x ≫ o₁.act.act (algebraMap (𝓞 D.F) D.O β) ≫ ψ₁) ≫ φ₁ = 1 := by
      rw [Category.assoc, Category.assoc, e₁, ← Category.assoc, MonObj.comp_pow, Category.comp_id,
        ← MonObj.pow_comp, hx, MonObj.one_comp]
    have hkill : ∃ e : ℕ, KilledBy o' (uIdeal D r ^ e) (x ≫ o₁.act.act (algebraMap (𝓞 D.F) D.O β) ≫ ψ₁) := by
      refine ⟨E, fun a ha => ?_⟩
      obtain ⟨v, hv⟩ := hβ a ha
      haveI := o₁.act.hom (algebraMap (𝓞 D.F) D.O v)
      rw [Category.assoc, Category.assoc, ← h₁.2.2.1, ← Category.assoc (o₁.act.act (algebraMap (𝓞 D.F) D.O β)),
        ← o₁.act.mul, ← map_mul, hv, map_mul, o₁.act.mul, map_pow, map_natCast, ← Nat.cast_pow, act_natCast]
      simp only [Category.assoc]
      rw [← Category.assoc x, MonObj.comp_pow, Category.comp_id, hx, MonObj.one_comp]
    have := (H T _ hkill).mp hy1
    simpa only [Category.assoc] using this
  have hmon : IsMonHom (o₁.act.act (algebraMap (𝓞 D.F) D.O β) ≫ ψ₁ ≫ φ₂) := inferInstance
  let f : avOf o₁ ⟶ avOf o₂ :=
    @GlobalTheory.AV.AbVar.Hom.mk _ _ (avOf o₁) (avOf o₂) (o₁.act.act (algebraMap (𝓞 D.F) D.O β) ≫ ψ₁ ≫ φ₂) hmon
  let q : avOf o₁ ⟶ avOf o₁ := ((p ^ E : ℕ) : ℤ) • 𝟙 (avOf o₁)
  have hq : GlobalTheory.AV.AbVar.Hom.hom q = 𝟙 o₁.A ^ (p ^ E) := by
    simp only [q]
    rw [GlobalTheory.AV.AbVar.zsmul_hom, GlobalTheory.AV.AbVar.id_hom, _root_.zpow_natCast]
    rfl
  have hf : GlobalTheory.AV.AbVar.Hom.hom f = o₁.act.act (algebraMap (𝓞 D.F) D.O β) ≫ ψ₁ ≫ φ₂ := rfl
  have hqi : GlobalTheory.AV.AbVar.IsIsogeny q :=
    (GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree Ω (avOf o₁) _ (Nat.cast_ne_zero.mpr (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))).1
  have hker : ∀ (T : Over (Sp Ω)) (x : T ⟶ (avOf o₁).X), x ≫ GlobalTheory.AV.AbVar.Hom.hom q = 1 →
      x ≫ GlobalTheory.AV.AbVar.Hom.hom f = 1 := by
    intro T x hx0
    rw [hf]
    exact hker' T x (hq ▸ hx0)
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_factor_through_isogeny_of_kills_kernel Ω (avOf o₁) (avOf o₁) (avOf o₂) q f hqi hker
  haveI hgm : IsMonHom (GlobalTheory.AV.AbVar.Hom.hom g) := (Additive.toMul g).property
  refine ⟨GlobalTheory.AV.AbVar.Hom.hom g, hgm, ?_⟩
  rw [← hf, ← hg, GlobalTheory.AV.AbVar.comp_hom, hq]
  exact idPow_comp _ _

section

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {Ω : Type} [Field Ω]
  {σ : Sp Ω ⟶ Sp R}

private theorem lin {o o' : Obj b N σ} {c : ℕ} (hc : 0 < c) {ψ : o.A ⟶ o'.A} {φ : o'.A ⟶ o.A}
    (hψl : ∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) (hφ : IsMonHom φ)
    (h1 : ψ ≫ φ = (𝟙 o.A) ^ c) (h2 : φ ≫ ψ = (𝟙 o'.A) ^ c) (a : D.O) :
    o'.act.act a ≫ φ = φ ≫ o.act.act a := by
  haveI := o.act.hom a
  haveI := o'.act.hom a
  apply hom_cancel Ω o'.A o.A o'.ab o.ab _ _ inferInstance inferInstance c hc
  calc (o'.act.act a ≫ φ) ^ c = ((𝟙 o'.A) ^ c) ≫ o'.act.act a ≫ φ := by
        rw [MonObj.pow_comp, Category.id_comp]
    _ = φ ≫ (ψ ≫ o'.act.act a) ≫ φ := by rw [← h2]; simp only [Category.assoc]
    _ = φ ≫ o.act.act a ≫ ψ ≫ φ := by rw [← hψl a]; simp only [Category.assoc]
    _ = (φ ≫ o.act.act a) ^ c := by rw [h1, MonObj.comp_pow, Category.comp_id, MonObj.comp_pow]

private theorem rosVal (o : Obj b N σ) (c : D.O) {T : Over (Sp Ω)} (x y : T ⟶ o.A) :
    GlobalTheory.BirigidPow.val o.isLB (x ≫ o.act.act c) y =
      GlobalTheory.BirigidPow.val o.isLB x (y ≫ o.act.act (D.star c).unop) := by
  have hL1 := pull_isLB o.isLB (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left
  have hL2 := pull_isLB o.isLB (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star c).unop)).left
  have key := (GlobalTheory.CechPic.cls_eq_iff hL1 hL2).mpr (o.rosati c)
  rw [GlobalTheory.CechPic.cls_pull o.isLB _ hL1, GlobalTheory.CechPic.cls_pull o.isLB _ hL2] at key
  have e1 : lift (x ≫ o.act.act c) y = lift x y ≫ lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A) := by
    ext <;> simp
  have e2 : lift x (y ≫ o.act.act (D.star c).unop) =
      lift x y ≫ lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star c).unop) := by
    ext <;> simp
  unfold GlobalTheory.BirigidPow.val
  rw [e1, e2, Over.comp_left, Over.comp_left, GlobalTheory.CechPic.pull_comp, GlobalTheory.CechPic.pull_comp, key]

private theorem conj (D : Datum p) (r : ℤ) (hr : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm) :
    IsCoprime (uIdeal D r) (Ideal.span {(p : 𝓞 D.F), D.bar D.ω - r}) ∧
      uIdeal D r * Ideal.span {(p : 𝓞 D.F), D.bar D.ω - r} ≤ Ideal.span {(p : 𝓞 D.F)} := by
  have hprod : (D.ω - (r : 𝓞 D.F)) * (D.bar D.ω - (r : 𝓞 D.F)) =
      ((r ^ 2 - D.tr * r + D.nm : ℤ) : 𝓞 D.F) := by
    push_cast
    linear_combination D.nm_eq - (r : 𝓞 D.F) * D.tr_eq
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out)
  have hnd : ¬ (p : ℤ) ∣ D.tr - 2 * r := by
    intro hd
    apply D.disc_p
    have e : D.tr ^ 2 - 4 * D.nm = (D.tr - 2 * r) ^ 2 - 4 * (r ^ 2 - D.tr * r + D.nm) := by ring
    rw [e]
    exact dvd_sub (dvd_pow hd two_ne_zero) (dvd_mul_of_dvd_right hr 4)
  obtain ⟨u, v, huv⟩ := (Prime.coprime_iff_not_dvd hpz).mpr hnd
  refine ⟨?_, ?_⟩
  · rw [Ideal.isCoprime_iff_exists]
    refine ⟨(u : 𝓞 D.F) * p + (v : 𝓞 D.F) * (D.ω - r), ?_, (v : 𝓞 D.F) * (D.bar D.ω - r), ?_, ?_⟩
    · exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (p_mem_uIdeal D r))
        (Ideal.mul_mem_left _ _ (sub_mem_uIdeal D r))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · have h1 : ((u * p + v * (D.tr - 2 * r) : ℤ) : 𝓞 D.F) = 1 := by rw [huv]; simp
      push_cast at h1
      linear_combination h1 + (v : 𝓞 D.F) * D.tr_eq
  · unfold uIdeal
    rw [Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    have hp : (p : 𝓞 D.F) ∈ Ideal.span {(p : 𝓞 D.F)} := Ideal.mem_span_singleton_self _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Ideal.mul_mem_right _ _ hp
    · exact Ideal.mul_mem_right _ _ hp
    · exact Ideal.mul_mem_left _ _ hp
    · show (D.ω - (r : 𝓞 D.F)) * (D.bar D.ω - (r : 𝓞 D.F)) ∈ Ideal.span {(p : 𝓞 D.F)}
      rw [hprod]
      obtain ⟨k, hk⟩ := hr
      rw [hk]
      push_cast
      exact Ideal.mul_mem_right _ _ hp

private theorem exists_ab (D : Datum p) (r : ℤ) (hr : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm) (E : ℕ) :
    ∃ a β : 𝓞 D.F, a + β = 1 ∧ (∀ x ∈ uIdeal D r ^ E, ∃ v : 𝓞 D.F, x * β = v * (p : 𝓞 D.F) ^ E) ∧
      ∃ t : 𝓞 D.F, a = D.bar β + t * (p : 𝓞 D.F) ^ E := by
  obtain ⟨hcop, hle⟩ := conj D r hr
  have hcopE := hcop.pow (m := E) (n := E)
  obtain ⟨a, ha, β, hβ, hab⟩ := Ideal.isCoprime_iff_exists.mp hcopE
  have hUJ : uIdeal D r ^ E * Ideal.span {(p : 𝓞 D.F), D.bar D.ω - r} ^ E ≤
      Ideal.span {(p : 𝓞 D.F) ^ E} := by
    rw [← mul_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono hle E
  have h1 : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by linear_combination D.tr_eq
  have hbb : D.bar (D.bar D.ω) = D.ω := by
    rw [h1, map_sub, map_intCast, h1]
    ring
  have hJU : Ideal.span {(p : 𝓞 D.F), D.bar D.ω - r} ≤ (uIdeal D r).comap D.bar := by
    rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · simpa [Ideal.mem_comap] using p_mem_uIdeal D r
    · show D.bar (D.bar D.ω - r) ∈ uIdeal D r
      rw [map_sub, map_intCast, hbb]
      exact sub_mem_uIdeal D r
  have hUJ' : uIdeal D r ≤ (Ideal.span {(p : 𝓞 D.F), D.bar D.ω - r}).comap D.bar := by
    unfold uIdeal
    rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · simpa [Ideal.mem_comap] using Ideal.subset_span (by simp : (p : 𝓞 D.F) ∈ ({(p : 𝓞 D.F), D.bar D.ω - r} : Set (𝓞 D.F)))
    · show D.bar (D.ω - r) ∈ Ideal.span {(p : 𝓞 D.F), D.bar D.ω - r}
      rw [map_sub, map_intCast]
      exact Ideal.subset_span (by simp)
  have hJUE := (Ideal.pow_right_mono hJU E).trans (Ideal.le_comap_pow D.bar E)
  have hUJE := (Ideal.pow_right_mono hUJ' E).trans (Ideal.le_comap_pow D.bar E)
  refine ⟨a, β, hab, ?_, ?_⟩
  · intro x hx
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp (hUJ (Ideal.mul_mem_mul hx hβ))
    exact ⟨v, hv.symm⟩
  · have hb : D.bar a + D.bar β = 1 := by
      have := congrArg D.bar hab
      rwa [map_add, map_one] at this
    have m1 : a - D.bar β ∈ uIdeal D r ^ E := sub_mem ha (hJUE hβ)
    have m2 : a - D.bar β ∈ Ideal.span {(p : 𝓞 D.F), D.bar D.ω - r} ^ E := by
      have e : a - D.bar β = D.bar a - β := by linear_combination hab - hb
      rw [e]
      exact sub_mem (hUJE ha) hβ
    have m3 : a - D.bar β ∈ Ideal.span {(p : 𝓞 D.F) ^ E} := by
      apply hUJ
      rw [← Ideal.inf_eq_mul_of_isCoprime hcopE]
      exact ⟨m1, m2⟩
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp m3
    exact ⟨t, by rw [ht]; ring⟩

end

section

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {Ω : Type} [Field Ω]
  {σ : Sp Ω ⟶ Sp R}

private def homSub (A B : Over (Sp Ω)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] :
    Subgroup (A ⟶ B) where
  carrier := {f | IsMonHom f}
  mul_mem' := fun {f g} hf hg => by
    have : IsMonHom f := hf
    have : IsMonHom g := hg
    exact inferInstanceAs (IsMonHom (lift f g ≫ μ[B]))
  one_mem' := by
    change IsMonHom (1 : A ⟶ B)
    rw [CategoryTheory.Hom.one_def]
    infer_instance
  inv_mem' := fun {f} hf => by
    have : IsMonHom f := hf
    change IsMonHom (f⁻¹)
    infer_instance

private theorem act_nat (o : Obj b N σ) (k : ℕ) : o.act.act (k : D.O) = 𝟙 o.A ^ k := by
  have h0 : o.act.act 0 = 1 := by
    have h := o.act.add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  induction k with
  | zero => simpa using h0
  | succ n ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one, pow_succ]

private theorem half {E : ℕ} {r : ℤ} (o₁ o₂ o' : Obj b N σ) (ψ₁ : o₁.A ⟶ o'.A) (ψ₂ : o₂.A ⟶ o'.A)
    (φ₁ : o'.A ⟶ o₁.A) (φ₂ : o'.A ⟶ o₂.A) (h₁ : IsPIsog (p ^ E) o₁ o' ψ₁) (h₂ : IsPIsog (p ^ E) o₂ o' ψ₂)
    (hφ₁ : IsMonHom φ₁) (hφ₂ : IsMonHom φ₂)
    (e₁ : ψ₁ ≫ φ₁ = (𝟙 o₁.A) ^ (p ^ E)) (e₁' : φ₁ ≫ ψ₁ = (𝟙 o'.A) ^ (p ^ E))
    (e₂ : ψ₂ ≫ φ₂ = (𝟙 o₂.A) ^ (p ^ E)) (e₂' : φ₂ ≫ ψ₂ = (𝟙 o'.A) ^ (p ^ E))
    (H : ∀ (T : Over (Sp Ω)) (x : T ⟶ o'.A), (∃ e : ℕ, KilledBy o' (uIdeal D r ^ e) x) →
      (x ≫ φ₁ = 1 ↔ x ≫ φ₂ = 1))
    (a β t : 𝓞 D.F) (hab : a + β = 1)
    (hβ : ∀ x ∈ uIdeal D r ^ E, ∃ v : 𝓞 D.F, x * β = v * (p : 𝓞 D.F) ^ E)
    (ht : a = D.bar β + t * (p : 𝓞 D.F) ^ E) :
    ∃ τ : o₁.A ⟶ o₂.A, IsMonHom τ ∧ ψ₁ ≫ φ₂ = τ ^ (p ^ E) := by
  have hpE : 0 < p ^ E := pow_pos (Fact.out : p.Prime).pos E
  haveI := h₁.2.1
  haveI := h₂.2.1
  haveI := hφ₁
  haveI := hφ₂
  obtain ⟨κ, hκ, eκ⟩ := exists_div p D R b N E r Ω σ o₁ o₂ o' ψ₁ φ₁ φ₂ β h₁ hφ₁ hφ₂ e₁ e₁' hβ H
  obtain ⟨κ₂, hκ₂, eκ₂⟩ := exists_div p D R b N E r Ω σ o₂ o₁ o' ψ₂ φ₂ φ₁ β h₂ hφ₂ hφ₁ e₂ e₂' hβ
    (fun T x hx => (H T x hx).symm)
  haveI := hκ₂
  obtain ⟨e, ν, hcop, hν, eν⟩ := exists_adjoint p D R b N Ω σ o₁ o₂ κ₂ hκ₂
  haveI := hν
  obtain ⟨bβ, hbβ⟩ : ∃ c : D.O, c = algebraMap (𝓞 D.F) D.O (D.bar β) := ⟨_, rfl⟩
  haveI : IsMonHom (o₁.act.act bβ) := o₁.act.hom _
  haveI : IsMonHom (o₂.act.act bβ) := o₂.act.hom _
  haveI : IsMonHom (o₂.act.act (algebraMap (𝓞 D.F) D.O β)) := o₂.act.hom _
  obtain ⟨M, hMdef⟩ : ∃ M : o₁.A ⟶ o₂.A, M = o₁.act.act bβ ≫ ψ₁ ≫ φ₂ := ⟨_, rfl⟩
  have hMcomm : M = ψ₁ ≫ φ₂ ≫ o₂.act.act bβ := by
    rw [hMdef, ← Category.assoc, h₁.2.2.1 bβ, Category.assoc, lin hpE h₂.2.2.1 hφ₂ e₂ e₂' bβ]
  have hMmon : IsMonHom M := by
    rw [hMdef]
    infer_instance
  have hstar : (D.star (algebraMap (𝓞 D.F) D.O β)).unop = bβ := by
    rw [D.star_F, hbβ]
    rfl
  have hval : ∀ (T : Over (Sp Ω)) (x : T ⟶ o₁.A) (y : T ⟶ o₂.A),
      GlobalTheory.BirigidPow.val o₂.isLB y (x ≫ M) = (p ^ E) • GlobalTheory.BirigidPow.val o₁.isLB (y ≫ κ₂) x := by
    intro T x y
    have r1 := rosVal o₂ (algebraMap (𝓞 D.F) D.O β) y (x ≫ ψ₁ ≫ φ₂)
    rw [hstar] at r1
    calc GlobalTheory.BirigidPow.val o₂.isLB y (x ≫ M)
        = GlobalTheory.BirigidPow.val o₂.isLB y ((x ≫ ψ₁ ≫ φ₂) ≫ o₂.act.act bβ) := by
          rw [hMcomm]
          simp only [Category.assoc]
      _ = GlobalTheory.BirigidPow.val o₂.isLB (y ≫ o₂.act.act (algebraMap (𝓞 D.F) D.O β)) ((x ≫ ψ₁) ≫ φ₂) := by
          rw [← r1, Category.assoc]
      _ = GlobalTheory.BirigidPow.val o'.isLB ((y ≫ o₂.act.act (algebraMap (𝓞 D.F) D.O β)) ≫ ψ₂) (x ≫ ψ₁) :=
          (val_adj_left p D R b N Ω σ o₂ o' (p ^ E) ψ₂ φ₂ h₂ hφ₂ e₂ e₂' T _ _).symm
      _ = GlobalTheory.BirigidPow.val o'.isLB (x ≫ ψ₁) ((y ≫ o₂.act.act (algebraMap (𝓞 D.F) D.O β)) ≫ ψ₂) :=
          val_symm p D R b N (Sp Ω) σ o' T _ _
      _ = GlobalTheory.BirigidPow.val o₁.isLB x (((y ≫ o₂.act.act (algebraMap (𝓞 D.F) D.O β)) ≫ ψ₂) ≫ φ₁) :=
          val_adj_left p D R b N Ω σ o₁ o' (p ^ E) ψ₁ φ₁ h₁ hφ₁ e₁ e₁' T _ _
      _ = GlobalTheory.BirigidPow.val o₁.isLB x ((y ≫ κ₂) ^ (p ^ E)) := by
          rw [← MonObj.comp_pow, ← eκ₂]
          simp only [Category.assoc]
      _ = (p ^ E) • GlobalTheory.BirigidPow.val o₁.isLB x (y ≫ κ₂) :=
          GlobalTheory.BirigidPow.val_pow_right o₁.isLB o₁.ab o₁.ample o₁.rig₁ o₁.rig₂ _ _ _
      _ = (p ^ E) • GlobalTheory.BirigidPow.val o₁.isLB (y ≫ κ₂) x := by
          rw [val_symm p D R b N (Sp Ω) σ o₁ T x]
  have hMe : M ^ e = ν ^ (p ^ E) := by
    refine hom_eq_of_val p D R b N Ω σ o₁ o₂ _ _ (by exact (homSub o₁.A o₂.A).pow_mem hMmon e)
      (by exact (homSub o₁.A o₂.A).pow_mem hν (p ^ E)) (fun T x y => ?_)
    rw [MonObj.comp_pow, MonObj.comp_pow,
      GlobalTheory.BirigidPow.val_pow_right o₂.isLB o₂.ab o₂.ample o₂.rig₁ o₂.rig₂,
      GlobalTheory.BirigidPow.val_pow_right o₂.isLB o₂.ab o₂.ample o₂.rig₁ o₂.rig₂, hval, eν, smul_smul, smul_smul,
      mul_comm]
  obtain ⟨u', w, huw⟩ : IsCoprime (e : ℤ) ((p ^ E : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right E hcop)
  have hA : (ν ^ u' * M ^ w) ^ (p ^ E) = M := by
    rw [mul_pow, ← zpow_natCast (ν ^ u'), ← zpow_natCast (M ^ w), ← zpow_mul, ← zpow_mul]
    have h1 : ν ^ (u' * ((p ^ E : ℕ) : ℤ)) = M ^ (u' * (e : ℤ)) := by
      rw [mul_comm u', zpow_mul, zpow_natCast, ← hMe, ← zpow_natCast, ← zpow_mul, mul_comm]
    rw [h1, ← zpow_add, huw, zpow_one]
  haveI : IsMonHom (o₁.act.act (algebraMap (𝓞 D.F) D.O t)) := o₁.act.hom _
  have hsplit : ψ₁ ≫ φ₂ = (o₁.act.act (algebraMap (𝓞 D.F) D.O a) ≫ ψ₁ ≫ φ₂) *
      (o₁.act.act (algebraMap (𝓞 D.F) D.O β) ≫ ψ₁ ≫ φ₂) := by
    rw [← MonObj.mul_comp, ← o₁.act.add, ← map_add, hab, map_one, o₁.act.one, Category.id_comp]
  have ha : o₁.act.act (algebraMap (𝓞 D.F) D.O a) ≫ ψ₁ ≫ φ₂ =
      M * (o₁.act.act (algebraMap (𝓞 D.F) D.O t) ≫ ψ₁ ≫ φ₂) ^ (p ^ E) := by
    rw [ht, map_add, o₁.act.add, MonObj.mul_comp, map_mul, map_pow, map_natCast, ← Nat.cast_pow,
      o₁.act.mul, act_nat, idPow_comp, MonObj.pow_comp, ← hbβ, ← hMdef]
  refine ⟨ν ^ u' * M ^ w * (o₁.act.act (algebraMap (𝓞 D.F) D.O t) ≫ ψ₁ ≫ φ₂) * κ, ?_, ?_⟩
  · have hX : IsMonHom (o₁.act.act (algebraMap (𝓞 D.F) D.O t) ≫ ψ₁ ≫ φ₂) := inferInstance
    exact (homSub o₁.A o₂.A).mul_mem ((homSub o₁.A o₂.A).mul_mem
      ((homSub o₁.A o₂.A).mul_mem ((homSub o₁.A o₂.A).zpow_mem hν u')
        ((homSub o₁.A o₂.A).zpow_mem hMmon w)) hX) hκ
  · rw [mul_pow, mul_pow, hA, ← eκ, ← ha, ← hsplit]

end

end UpperTheory.KEq

namespace UpperTheory.KEq

private theorem sec_ext {k : Type} [Field k] {B : Over (Sp k)} (hs : IsSeparated B.hom) (V : Over (Sp k))
    (w : V.left) (f g : 𝟙_ (Over (Sp k)) ⟶ B) (h : toUnit V ≫ f = toUnit V ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  haveI : IsSeparated B.hom := hs
  haveI : Surjective V.hom := ⟨fun y => ⟨w, Subsingleton.elim _ _⟩⟩
  refine ext_of_isDominant_of_isSeparated (X := Sp k) B.hom ?_ V.hom ?_
  · rw [Over.w f, Over.w g]
  · have := congrArg Over.Hom.left h
    simp only [Over.comp_left] at this
    exact this

private theorem glue_ext {S : Scheme.{0}} {T B : Over S} (f g : T ⟶ B)
    (h : ∀ w : T.left, ∃ (V : Over S) (i : V ⟶ T) (w' : V.left), IsOpenImmersion i.left ∧ i.left w' = w ∧
      i ≫ f = i ≫ g) : f = g := by
  choose V i w' hi hiw hfg using h
  apply Over.OverMorphism.ext
  let U : T.left → T.left.Opens := fun w => @Scheme.Hom.opensRange _ _ (i w).left (hi w)
  have hU : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro w _
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨w, w' w, hiw w⟩
  refine (T.left.openCoverOfIsOpenCover U hU).hom_ext _ _ fun (w : T.left) => ?_
  haveI := hi w
  show (U w).ι ≫ f.left = (U w).ι ≫ g.left
  have e : (U w).ι = ((i w).left.isoOpensRange).inv ≫ (i w).left := by
    rw [Iso.eq_inv_comp]
    exact Scheme.Hom.isoOpensRange_hom_ι _
  rw [e, Category.assoc, Category.assoc, ← Over.comp_left, hfg w, Over.comp_left]

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

private theorem ker_le {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {σ : Sp k ⟶ Sp R} {o o₂ : Obj b N σ}
    (c : ℕ) (hc : 0 < c) (v : Ideal (𝓞 D.F)) {O₁ : Over (Sp k)} [GrpObj O₁] (hs₁ : IsSeparated O₁.hom)
    (ψ₁ : o.A ⟶ O₁) (ψ₂ : o.A ⟶ o₂.A)
    (hk : ∀ h : 𝟙_ (Over (Sp k)) ⟶ o.A, h ≫ ψ₁ = 1 → KilledBy o v h → h ≫ ψ₂ = 1)
    (T : Over (Sp k)) (x : T ⟶ o.A) (hv : KilledBy o v x) (h1 : x ≫ ψ₁ = 1) (hxc : x ^ c = 1) : x ≫ ψ₂ = 1 := by
  haveI := o.ab
  haveI : IsProper o.A.hom := IsAbelianScheme.proper
  have hsepA : IsSeparated o.A.hom := inferInstance
  have hc0 : ((c : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  apply glue_ext
  intro w
  obtain ⟨V, i, y, w', hi, hiw, hyc, hix⟩ :=
    GlobalTheory.T.abelianScheme_torsionPoint_locally_constant_geomPoint (Sp k) o.A o.ab k (𝟙 (Sp k)) c hc0 T (toUnit T) x hxc w
  refine ⟨V, i, w', hi, hiw, ?_⟩
  have hpt : i ≫ toUnit T = toUnit V := toUnit_unique _ _
  have hVy : toUnit V ≫ y = i ≫ x := by
    rw [← hpt, Category.assoc, ← hix]
  have hy1 : y ≫ ψ₁ = 1 := by
    apply sec_ext hs₁ V w'
    rw [← Category.assoc, hVy, Category.assoc, h1]
    simp only [MonObj.comp_one]
  have hyv : KilledBy o v y := by
    intro a ha
    apply sec_ext hsepA V w'
    rw [← Category.assoc, hVy, Category.assoc, hv a ha]
    simp only [MonObj.comp_one]
  have hy2 := hk y hy1 hyv
  rw [← Category.assoc, hix, Category.assoc, Category.assoc, hy2]
  simp only [MonObj.comp_one]

end UpperTheory.KEq

namespace UpperTheory.KEq

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

private theorem root_dvd (D : Datum p) {r : ℤ} {w : Ideal (𝓞 D.F)} (hw : w ≠ ⊤) (hu : uIdeal D r ≤ w) :
    (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm := by
  by_contra hnd
  apply hw
  have hq : ((r : 𝓞 D.F) ^ 2 - (D.tr : 𝓞 D.F) * r + (D.nm : 𝓞 D.F)) ∈ w := by
    apply hu
    have e : ((r : 𝓞 D.F) ^ 2 - (D.tr : 𝓞 D.F) * r + (D.nm : 𝓞 D.F)) =
        (D.ω - r) * (D.bar D.ω - r) := by
      rw [← D.tr_eq, ← D.nm_eq]
      ring
    rw [e]
    exact Ideal.mul_mem_right _ _ (sub_mem_uIdeal D r)
  have hp : ((p : ℕ) : 𝓞 D.F) ∈ w := hu (p_mem_uIdeal D r)
  have hcop : IsCoprime (p : ℤ) (r ^ 2 - D.tr * r + D.nm) :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp (Fact.out)).irreducible).mpr hnd
  obtain ⟨a, c, hac⟩ := hcop
  rw [Ideal.eq_top_iff_one]
  have h1 := congrArg (Int.cast : ℤ → 𝓞 D.F) hac
  push_cast at h1
  rw [← h1]
  exact w.add_mem (w.mul_mem_left _ hp) (w.mul_mem_left _ hq)

private theorem factor {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {σ : Sp k ⟶ Sp R} {o o₁ o₂ : Obj b N σ}
    (E : ℕ) (r : ℤ) (hr : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A)
    (h₁ : IsPIsog (p ^ E) o o₁ ψ₁) (h₂ : IsPIsog (p ^ E) o o₂ ψ₂)
    (hk : ∀ h : 𝟙_ (Over (Sp k)) ⟶ o.A, (h ≫ ψ₁ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) h) ↔
      (h ≫ ψ₂ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) h)) :
    ∃ τ : o₁.A ⟶ o₂.A, IsMonHom τ ∧ ψ₁ ≫ τ = ψ₂ := by
  obtain ⟨φ₁, hφ₁, e₁, e₁'⟩ := h₁.2.2.2.2.2
  obtain ⟨φ₂, hφ₂, e₂, e₂'⟩ := h₂.2.2.2.2.2
  have hq₁ : IsMonHom ψ₁ ∧ IsMonHom φ₁ ∧ ψ₁ ≫ φ₁ = 𝟙 o.A ^ (p ^ E) ∧ φ₁ ≫ ψ₁ = 𝟙 o₁.A ^ (p ^ E) :=
    ⟨h₁.2.1, hφ₁, e₁, e₁'⟩
  have hq₂ : IsMonHom ψ₂ ∧ IsMonHom φ₂ ∧ ψ₂ ≫ φ₂ = 𝟙 o.A ^ (p ^ E) ∧ φ₂ ≫ ψ₂ = 𝟙 o₂.A ^ (p ^ E) :=
    ⟨h₂.2.1, hφ₂, e₂, e₂'⟩
  haveI := hq₁.1
  haveI := hq₁.2.1
  haveI := hq₂.1
  haveI := hq₂.2.1
  haveI := o.ab
  haveI := o₁.ab
  haveI := o₂.ab
  haveI : IsProper o₁.A.hom := IsAbelianScheme.proper
  haveI : IsProper o₂.A.hom := IsAbelianScheme.proper
  have hs₁ : IsSeparated o₁.A.hom := inferInstance
  have hs₂ : IsSeparated o₂.A.hom := inferInstance
  let o' : Obj b N σ := ESDual.scale o E rfl
  have dc₁ := ESDual.dual_clauses h₁ hq₁.2.2.1 hq₁.2.2.2
  have dc₂ := ESDual.dual_clauses h₂ hq₂.2.2.1 hq₂.2.2.2
  have g₁ : IsPIsog (p ^ E) o₁ o' φ₁ :=
    ⟨⟨E, rfl⟩, hq₁.2.1, dc₁.1, fun x => dc₁.2.1 x, dc₁.2.2, ψ₁, hq₁.1, hq₁.2.2.2, hq₁.2.2.1⟩
  have g₂ : IsPIsog (p ^ E) o₂ o' φ₂ :=
    ⟨⟨E, rfl⟩, hq₂.2.1, dc₂.1, fun x => dc₂.2.1 x, dc₂.2.2, ψ₂, hq₂.1, hq₂.2.2.2, hq₂.2.2.1⟩
  obtain ⟨a, β, hab, hβ, t, ht⟩ := exists_ab D r hr E
  have H : ∀ (T : Over (Sp k)) (x : T ⟶ o'.A), (∃ e : ℕ, KilledBy o' (uIdeal D r ^ e) x) →
      (x ≫ ψ₁ = 1 ↔ x ≫ ψ₂ = 1) := by
    rintro T (x : T ⟶ o.A) ⟨e, he⟩
    have hxc : x ^ (p ^ e) = 1 := by
      have h0 := he _ (Ideal.pow_mem_pow (p_mem_uIdeal D r) e)
      change x ≫ o.act.act _ = 1 at h0
      rw [map_pow, map_natCast, ← Nat.cast_pow, act_nat o (p ^ e), MonObj.comp_pow,
        Category.comp_id] at h0
      exact h0
    have hc : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
    constructor
    · intro h1
      exact ker_le (p ^ e) hc _ hs₁ ψ₁ ψ₂ (fun h hh hv => ((hk h).mp ⟨hh, e, hv⟩).1) T x he h1 hxc
    · intro h2
      exact ker_le (p ^ e) hc _ hs₂ ψ₂ ψ₁ (fun h hh hv => ((hk h).mpr ⟨hh, e, hv⟩).1) T x he h2 hxc
  obtain ⟨τ, hτ, hτe⟩ := half o₁ o₂ o' φ₁ φ₂ ψ₁ ψ₂ g₁ g₂ hq₁.1 hq₂.1 hq₁.2.2.2 hq₁.2.2.1
    hq₂.2.2.2 hq₂.2.2.1 H a β t hab hβ ht
  haveI := hτ
  refine ⟨τ, hτ, ?_⟩
  refine hom_cancel k o.A o₂.A o.ab o₂.ab (ψ₁ ≫ τ) ψ₂ inferInstance hq₂.1 (p ^ E)
    (pow_pos (Fact.out : p.Prime).pos E) ?_
  calc (ψ₁ ≫ τ) ^ (p ^ E) = ψ₁ ≫ τ ^ (p ^ E) := (MonObj.comp_pow _ _ _).symm
    _ = ψ₁ ≫ φ₁ ≫ ψ₂ := congrArg (fun f => ψ₁ ≫ f) hτe.symm
    _ = (ψ₁ ≫ φ₁) ≫ ψ₂ := (Category.assoc _ _ _).symm
    _ = (𝟙 o.A ^ (p ^ E)) ≫ ψ₂ := by rw [e₁]
    _ = ψ₂ ^ (p ^ E) := by rw [MonObj.pow_comp, Category.id_comp]

end UpperTheory.KEq

theorem UpperTheory.isogeny_kernel_points_iff_of_isPIsog :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (c : ℕ), w.IsMaximal → uIdeal D r ≤ w → ∀ (k : Type) [Field k] [IsAlgClosed k] (σ : Sp k ⟶ Sp R) (o o₁ o₂ : Obj b N σ) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsPIsog c o o₁ ψ₁ → IsPIsog c o o₂ ψ₂ → (∀ h : 𝟙_ (Over (Sp k)) ⟶ o.A, (h ≫ ψ₁ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) h) ↔ (h ≫ ψ₂ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) h)) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Sp k) (g : Over.mk x ⟶ o.A), g ≫ ψ₁ = 1 ↔ g ≫ ψ₂ = 1 := by
  intro p _ D R _ b N hp r w c hw hu k _ _ σ o o₁ o₂ ψ₁ ψ₂ h₁ h₂ hk κ _ _ x g
  haveI := GlobalTheory.UPel.HT.ES.TjExists.charZero_of_base b hp σ
  obtain ⟨E, rfl⟩ := h₁.1
  have hr := UpperTheory.KEq.root_dvd D hw.ne_top hu
  obtain ⟨τ, hτ, e⟩ := UpperTheory.KEq.factor E r hr ψ₁ ψ₂ h₁ h₂ hk
  obtain ⟨τ', hτ', e'⟩ := UpperTheory.KEq.factor E r hr ψ₂ ψ₁ h₂ h₁ fun h => (hk h).symm
  constructor
  · intro h
    rw [← e, ← Category.assoc, h, MonObj.one_comp]
  · intro h
    rw [← e', ← Category.assoc, h, MonObj.one_comp]
