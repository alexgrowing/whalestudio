import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AevalFirstChernSurjective

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)

namespace GlobalTheory.ShFam.Pad

namespace NModel

section GenIso

variable {O : Type} [CommRing O] [IsLocalRing O] (Z : NModel O)

@[ext] structure GenIso (L L' : LB Z.X) : Type where

  u : ∀ (i : L.ι) (j : L'.ι), Γ(Z.X, Z.gen ⊓ (L.U i ⊓ L'.U j))ˣ

  rel : ∀ (i i₁ : L.ι) (j j₁ : L'.ι),
    res (inf_le_left : Z.gen ⊓ (L.U i ⊓ L'.U j) ⊓ (L.U i₁ ⊓ L'.U j₁) ≤ _) (u i j) *
      res (inf_le_inf (inf_le_right.trans inf_le_right) inf_le_right) (L'.g j j₁) =
    res (inf_le_inf (inf_le_right.trans inf_le_left) inf_le_left) (L.g i i₁) *
      res (inf_le_inf_right _ inf_le_left) (u i₁ j₁)

namespace GenIso

variable {Z} {L L' L'' : LB Z.X} (φ : Z.GenIso L L')

theorem rel' (i i₁ : L.ι) (j j₁ : L'.ι) {W : Z.X.Opens} (h : W ≤ Z.gen ⊓ (L.U i ⊓ L'.U j))
    (h₁ : W ≤ Z.gen ⊓ (L.U i₁ ⊓ L'.U j₁)) (hi : W ≤ L.U i ⊓ L.U i₁) (hj : W ≤ L'.U j ⊓ L'.U j₁) :
    res h (φ.u i j) * res hj (L'.g j j₁) = res hi (L.g i i₁) * res h₁ (φ.u i₁ j₁) := by
  have := congrArg (fun u => (res (le_inf h (h₁.trans inf_le_right)) u).val) (φ.rel i i₁ j j₁)
  refine Units.ext ?_
  simpa only [map_mul, Units.val_mul, val_res, resG_resG] using this

def pair (hL : L.IsLB) (hL' : L'.IsLB) : VPair Z :=
  .ofUnits (LB.div L L') (Semi.LB.isLB_div hL hL') (fun p => (φ.u p.1 p.2).val) (fun _ => Units.isUnit _) fun p q => by
    have := congrArg Units.val (eq_mul_inv_iff_mul_eq.2 (φ.rel p.1 q.1 p.2 q.2))
    rw [mul_right_comm] at this
    refine this.trans (congrArg (· * _) ?_)
    change _ = (res _ (res _ _ * (res _ _)⁻¹)).val
    rw [map_mul, map_inv]
    exact congrArg Units.val (congrArg₂ (fun a b => a * b⁻¹) (Semi.LB.res_res _ _ _) (Semi.LB.res_res _ _ _)).symm

def dual : Z.GenIso (CechPic.dual L) (CechPic.dual L') where
  u i j := (φ.u i j)⁻¹
  rel i i₁ j j₁ := by
    have := congrArg (·⁻¹) (φ.rel i i₁ j j₁)
    simp only [mul_inv, ← map_inv] at this
    exact this

def symm : Z.GenIso L' L where
  u j i := res (inf_le_inf_left _ (inf_comm _ _).le) (φ.u i j)⁻¹
  rel j j₁ i i₁ := by
    have h := φ.rel' i i₁ j j₁ (W := Z.gen ⊓ (L'.U j ⊓ L.U i) ⊓ (L'.U j₁ ⊓ L.U i₁))
      (inf_le_left.trans (inf_le_inf_left _ (inf_comm _ _).le))
      (inf_le_inf inf_le_left (inf_comm _ _).le)
      (inf_le_inf (inf_le_right.trans inf_le_right) inf_le_right)
      (inf_le_inf (inf_le_right.trans inf_le_left) inf_le_left)
    have e (a b) {W W' : Z.X.Opens} (h₁ : W ≤ Z.gen ⊓ (L.U a ⊓ L'.U b)) (h₂ : W' ≤ W) :
        res h₂ (res h₁ (φ.u a b)⁻¹) = (res (h₂.trans h₁) (φ.u a b))⁻¹ :=
      (Units.ext (resG_resG _ _ _)).trans (map_inv _ _)
    rw [e, e, inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
    exact h.symm

def ofGlobal (w : LB.Iso L' L) (hw : w.IsGen) : Z.GenIso L L' where
  u i j := res inf_le_right (w.s (i, j))
  rel i i₁ j j₁ := by
    have h : res _ (w.s (i, j)) = res _ _ * (res _ _)⁻¹ * res _ (w.s (i₁, j₁)) := hw (i, j) (i₁, j₁)
    rw [mul_right_comm, eq_mul_inv_iff_mul_eq] at h
    have := congrArg (res (inf_le_inf_right (L.U i₁ ⊓ L'.U j₁) (inf_le_right : Z.gen ⊓ (L.U i ⊓ L'.U j) ≤ _))) h
    rw [map_mul, map_mul] at this
    exact (congrArg₂ (· * ·) ((Semi.LB.res_res _ _ _).trans (Semi.LB.res_res _ _ _).symm)
      (Semi.LB.res_res _ _ _).symm).trans (this.trans (congrArg₂ (· * ·) (Semi.LB.res_res _ _ _)
        ((Semi.LB.res_res _ _ _).trans (Semi.LB.res_res _ _ _).symm)))

theorem chart_eq (p : (L.pull Z.gen.ι).ι × (L'.pull Z.gen.ι).ι) :
    (L.pull Z.gen.ι).U p.1 ⊓ (L'.pull Z.gen.ι).U p.2 = Z.gen.ι ⁻¹ᵁ (Z.gen ⊓ (L.U (p.1 ⟨⟩) ⊓ L'.U (p.2 ⟨⟩))) :=
  le_antisymm (fun x hx => ⟨x.2, mem_pull.1 hx.1, mem_pull.1 hx.2⟩) fun _ hx => ⟨mem_pull.2 hx.2.1, mem_pull.2 hx.2.2⟩

def toIso : LB.Iso (L'.pull Z.gen.ι) (L.pull Z.gen.ι) :=
  ⟨fun p => res (chart_eq p).le (pullU Z.gen.ι _ (φ.u (p.1 ⟨⟩) (p.2 ⟨⟩)))⟩

theorem isGen_iff (u : ∀ (i : L.ι) (j : L'.ι), Γ(Z.X, Z.gen ⊓ (L.U i ⊓ L'.U j))ˣ) :
    LB.Gen.IsGen (L := LB.div (L.pull Z.gen.ι) (L'.pull Z.gen.ι))
      ⟨fun p => res (chart_eq p).le (pullU Z.gen.ι _ (u (p.1 ⟨⟩) (p.2 ⟨⟩)))⟩ ↔
    ∀ (y : Z.gen.toScheme) i i₁ j j₁, y.1 ∈ L.U i ⊓ L'.U j → y.1 ∈ L.U i₁ ⊓ L'.U j₁ →
      gm Z.gen.ι y _ (u i j) * gm Z.gen.ι y _ (L'.g j j₁) = gm Z.gen.ι y _ (L.g i i₁) * gm Z.gen.ι y _ (u i₁ j₁) := by
  have key (y : Z.gen.toScheme) (p q : (L.pull Z.gen.ι).ι × (L'.pull Z.gen.ι).ι)
      (hp : y ∈ (L.pull Z.gen.ι).U p.1 ⊓ (L'.pull Z.gen.ι).U p.2)
      (hq : y ∈ (L.pull Z.gen.ι).U q.1 ⊓ (L'.pull Z.gen.ι).U q.2) :=
    (gm_div' (L.pull Z.gen.ι) (L'.pull Z.gen.ι) (𝟙 _) y p q hp hq).trans (congrArg₂ (fun a b => a * b⁻¹)
      (gm_pull_g L Z.gen.ι (𝟙 _) y p.1 q.1 hp.1 hq.1) (gm_pull_g L' Z.gen.ι (𝟙 _) y p.2 q.2 hp.2 hq.2))
  simp only [Category.id_comp] at key
  rw [isGen_iff_germ]
  constructor
  · intro h y i i₁ j j₁ hp hq
    have hp' : y ∈ (L.pull Z.gen.ι).U (fun _ => i) ⊓ (L'.pull Z.gen.ι).U (fun _ => j) :=
      ⟨mem_pull.2 hp.1, mem_pull.2 hp.2⟩
    have hq' : y ∈ (L.pull Z.gen.ι).U (fun _ => i₁) ⊓ (L'.pull Z.gen.ι).U (fun _ => j₁) :=
      ⟨mem_pull.2 hq.1, mem_pull.2 hq.2⟩
    have := (gm_rp₁ _ y _ _ _ hp' _).symm.trans ((h y (fun _ => i, fun _ => j) (fun _ => i₁, fun _ => j₁) hp' hq').trans
      (congrArg₂ (· * ·) (key y (fun _ => i, fun _ => j) (fun _ => i₁, fun _ => j₁) hp' hq') (gm_rp₁ _ y _ _ _ hq' _)))
    rwa [mul_right_comm, eq_mul_inv_iff_mul_eq] at this
  · intro h y p q hp hq
    refine (gm_rp₁ _ y _ _ _ hp _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (key y p q hp hq) (gm_rp₁ _ y _ _ _ hq _)).symm)
    rw [mul_right_comm, eq_mul_inv_iff_mul_eq]
    exact h y _ _ _ _ ⟨mem_pull.1 hp.1, mem_pull.1 hp.2⟩ ⟨mem_pull.1 hq.1, mem_pull.1 hq.2⟩

theorem isGen_toIso : φ.toIso.IsGen := (isGen_iff φ.u).2 fun y i i₁ j j₁ hp hq => by
  have hy : Z.gen.ι y ∈ Z.gen ⊓ (L.U i ⊓ L'.U j) ⊓ (L.U i₁ ⊓ L'.U j₁) := ⟨⟨y.2, hp⟩, hq⟩
  simpa only [map_mul, gm_res _ y _ hy] using congrArg (gm Z.gen.ι y _) (φ.rel i i₁ j j₁)

theorem bijective_res_pullU {V : Z.X.Opens} (hV : V ≤ Z.gen) {W : Z.gen.toScheme.Opens} (h : W = Z.gen.ι ⁻¹ᵁ V) :
    Function.Bijective fun u => res h.le (pullU Z.gen.ι V u) := by
  subst h
  have := Z.gen.ι.isIso_app V (hV.trans Z.gen.opensRange_ι.ge)
  have e : (fun u => res le_rfl (pullU Z.gen.ι V u)) =
      Units.mapEquiv (asIso (Z.gen.ι.app V)).commRingCatIsoToRingEquiv.toMulEquiv :=
    funext fun u => Units.ext (resG_self _ _)
  rw [e]
  exact MulEquiv.bijective _

variable (L L') in

def equivIso : Z.GenIso L L' ≃ {w : LB.Iso (L'.pull Z.gen.ι) (L.pull Z.gen.ι) // w.IsGen} :=
  Equiv.ofBijective (fun φ => ⟨φ.toIso, φ.isGen_toIso⟩) <| by
    refine ⟨fun φ ψ h => GenIso.ext (funext₂ fun i j => ?_), fun ⟨w, hw⟩ => ?_⟩
    · exact (bijective_res_pullU inf_le_left (chart_eq (fun _ => i, fun _ => j))).1
        (congrArg (fun w => w.1.s (fun _ => i, fun _ => j)) h)
    · choose u hu using fun (i : L.ι) (j : L'.ι) =>
        (bijective_res_pullU inf_le_left (chart_eq (fun _ => i, fun _ => j))).2 (w.s (fun _ => i, fun _ => j))
      have e : (⟨fun p => res (chart_eq p).le (pullU Z.gen.ι _ (u (p.1 ⟨⟩) (p.2 ⟨⟩)))⟩ :
          LB.Iso (L'.pull Z.gen.ι) (L.pull Z.gen.ι)) = w := congrArg LB.Gen.mk (funext fun p => hu _ _)
      refine ⟨⟨u, fun i i₁ j j₁ => (bijective_res_pullU (inf_le_left.trans inf_le_left) rfl).1
        (unit_ext fun y hy => ?_)⟩, Subtype.ext e⟩
      refine (gm_rp₁ _ y _ _ _ hy _).trans (Eq.trans ?_ (gm_rp₁ _ y _ _ _ hy _).symm)
      have hy' : Z.gen.ι y ∈ Z.gen ⊓ (L.U i ⊓ L'.U j) ⊓ (L.U i₁ ⊓ L'.U j₁) := hy
      simp only [map_mul, gm_res Z.gen.ι y _ hy']
      exact (isGen_iff u).1 (e ▸ hw) y i i₁ j j₁ hy.1.2 hy.2

end GenIso

end GenIso

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : NModel O}

namespace GenIso

variable {L L' L'' : LB Z.X} (φ : Z.GenIso L L') (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB)

def smul (g : O) (hg : g ≠ 0) : Z.GenIso L L where
  u i j := (Z.isUnit_const hg inf_le_left).unit * res inf_le_right (L.g i j)
  rel i i₁ j j₁ := by
    refine unit_ext fun y hy => ?_
    have e (a b : L.ι) (h : y ∈ Z.gen ⊓ (L.U a ⊓ L.U b)) :
        gm (𝟙 Z.X) y _ (Z.isUnit_const hg (inf_le_left : Z.gen ⊓ (L.U a ⊓ L.U b) ≤ _)).unit =
          gm (𝟙 Z.X) y _ (Z.isUnit_const hg le_rfl).unit := by
      rw [← gm_res (𝟙 Z.X) y (inf_le_left : Z.gen ⊓ (L.U a ⊓ L.U b) ≤ _) h]
      exact congrArg _ (Units.ext (resG_resG _ _ _).symm)
    have h₁ : y ∈ Z.gen ⊓ (L.U i₁ ⊓ L.U j₁) := ⟨hy.1.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 Z.X) y _ hy, gm_res (𝟙 Z.X) y _ hy.1, gm_res (𝟙 Z.X) y _ h₁, e _ _ hy.1, e _ _ h₁]
    rw [mul_assoc, gm_cocycle hL (𝟙 _) y hy.1.2.1 hy.1.2.2 hy.2.2, mul_left_comm,
      gm_cocycle hL (𝟙 _) y hy.1.2.1 hy.2.1 hy.2.2]

def div : Z.VDivZ := (φ.pair hL hL').cls

@[simp] theorem vCls_div : Z.vCls (φ.div hL hL') = cls L hL - cls L' hL' := (vCls_cls _).trans (cls_div _ _ _)

theorem div_eq_add (φ' : Z.GenIso L' L'') (φ'' : Z.GenIso L L'')
    (h : ∀ i j k, res (inf_le_inf_left _ (inf_le_inf_right _ inf_le_left) :
        Z.gen ⊓ (L.U i ⊓ L'.U j ⊓ L''.U k) ≤ _) (φ''.u i k) =
      res (inf_le_inf_left _ inf_le_left) (φ.u i j) *
        res (inf_le_inf_left _ (inf_le_inf_right _ inf_le_right)) (φ'.u j k)) :
    φ''.div hL hL'' = φ.div hL hL' + φ'.div hL' hL'' := by
  refine VPair.isSum_iff.1 fun a b c => ?_
  obtain ⟨i, j⟩ := a
  obtain ⟨j₁, k⟩ := b
  obtain ⟨i₁, k₁⟩ := c
  let V := L.U i ⊓ L'.U j ⊓ (L'.U j₁ ⊓ L''.U k) ⊓ (L.U i₁ ⊓ L''.U k₁)
  have hi : V ≤ L.U i := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hj : V ≤ L'.U j := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hj₁ : V ≤ L'.U j₁ := inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hk : V ≤ L''.U k := inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hi₁ : V ≤ L.U i₁ := inf_le_right.trans inf_le_left
  have hk₁ : V ≤ L''.U k₁ := inf_le_right.trans inf_le_right
  refine ⟨res (le_inf hi₁ hi) (L.g i₁ i) * res (le_inf hj hj₁) (L'.g j j₁) * (res (le_inf hk₁ hk) (L''.g k₁ k))⁻¹, ?_⟩
  have e (W W' W'' : Z.X.Opens) (h₁ : W' ≤ W) (h₂ : W'' ≤ W') (u : Γ(Z.X, W)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u := Units.ext (resG_resG _ _ _)
  have h₁ := φ''.rel' i₁ i k₁ k (W := Z.gen ⊓ V) (inf_le_inf_left _ (le_inf hi₁ hk₁))
    (inf_le_inf_left _ (le_inf hi hk)) (inf_le_right.trans (le_inf hi₁ hi)) (inf_le_right.trans (le_inf hk₁ hk))
  have h₂ := φ.rel' i i j j₁ (W := Z.gen ⊓ V) (inf_le_inf_left _ (le_inf hi hj))
    (inf_le_inf_left _ (le_inf hi hj₁)) (inf_le_right.trans (le_inf hi hi)) (inf_le_right.trans (le_inf hj hj₁))
  have h₃ := congrArg (res (inf_le_inf_left Z.gen (le_inf (le_inf hi hj₁) hk))) (h i j₁ k)
  have h₄ := congrArg (res ((inf_le_right : Z.gen ⊓ V ≤ V).trans hi)) (hL.g_self i)
  simp only [map_mul, e, map_one] at h₃ h₄
  rw [h₄, one_mul] at h₂
  rw [h₃, ← h₂, ← eq_mul_inv_iff_mul_eq] at h₁
  refine (congrArg Units.val h₁).trans ?_
  change _ = (res (inf_le_right : Z.gen ⊓ V ≤ V) _ * (res _ (φ.u i j) * res _ (φ'.u j₁ k))).val
  refine congrArg Units.val ?_
  simp only [map_mul, map_inv, e]
  ac_rfl

@[simp] theorem div_ofGlobal (w : LB.Iso L' L) (hw : w.IsGen) : (ofGlobal w hw : Z.GenIso L L').div hL hL' = 0 := by
  rw [← VPair.cls_zero]
  refine (VPair.cls_eq_iff.2 (VPair.isIsom_of_units (fun p _ => res inf_le_left (w.s p)) fun p q => ?_)).symm
  change resG _ _ (resG _ _ _) = resG _ _ (resG _ _ _) * resG _ _ 1
  rw [map_one, mul_one]
  exact (resG_resG _ _ _).trans (resG_resG _ _ _).symm

@[simp] theorem div_smul (g : O) (hg : g ≠ 0) : (smul hL g hg).div hL hL = Z.div g hg := by
  refine (VPair.cls_eq_iff.2 (VPair.isIsom_of_units
    (P' := (smul hL g hg).pair hL hL) (fun p _ => res inf_le_left (L.g p.1 p.2)) fun p q => ?_)).symm
  change resG _ _ (resG _ _ _ * resG _ _ _) = resG _ _ (resG _ _ _) * resG _ _ (resG _ _ _)
  rw [map_mul, mul_comm]
  exact congrArg₂ (· * ·) ((resG_resG _ _ _).trans (resG_resG _ _ _).symm)
    ((resG_resG _ _ _).trans (resG_resG _ _ _).symm)

@[simp] theorem div_symm : φ.symm.div hL' hL = -φ.div hL hL' := by
  refine eq_neg_of_add_eq_zero_right ((φ.div_eq_add hL hL' hL φ.symm (ofGlobal (idIso L) (idIso_isGen hL))
    fun i j k => ?_).symm.trans (div_ofGlobal _ _ _ _))
  have h₁ := φ.rel' i k j j (W := Z.gen ⊓ (L.U i ⊓ L'.U j ⊓ L.U k)) (inf_le_inf_left _ inf_le_left)
    (inf_le_inf_left _ (le_inf inf_le_right (inf_le_left.trans inf_le_right)))
    (inf_le_right.trans (inf_le_inf_right _ inf_le_left))
    (inf_le_right.trans (inf_le_left.trans (le_inf inf_le_right inf_le_right)))
  have h₂ := congrArg (res ((inf_le_right : Z.gen ⊓ (L.U i ⊓ L'.U j ⊓ L.U k) ≤ _).trans
    (inf_le_left.trans inf_le_right))) (hL'.g_self j)
  rw [Semi.LB.res_res, map_one] at h₂
  rw [h₂, mul_one, ← mul_inv_eq_iff_eq_mul, ← map_inv] at h₁
  exact (Semi.LB.res_res _ _ _).trans (h₁.symm.trans (congrArg _ (Semi.LB.res_res _ _ _).symm))

@[simp] theorem div_dual : φ.dual.div (isLB_dual hL) (isLB_dual hL') = -φ.div hL hL' := by
  refine eq_neg_of_add_eq_zero_right ((VPair.isSum_iff.1 fun a b c => ?_).symm.trans (VPair.cls_zero Z))
  obtain ⟨i, j⟩ := a
  obtain ⟨i₁, j₁⟩ := b
  let V := L.U i ⊓ L'.U j ⊓ (L.U i₁ ⊓ L'.U j₁) ⊓ ⊤
  have hi : V ≤ L.U i ⊓ L.U i₁ := inf_le_left.trans (inf_le_inf inf_le_left inf_le_left)
  have hj : V ≤ L'.U j ⊓ L'.U j₁ := inf_le_left.trans (inf_le_inf inf_le_right inf_le_right)
  refine ⟨res hj (L'.g j j₁) * (res hi (L.g i i₁))⁻¹, ?_⟩
  have h₁ := φ.rel' i i₁ j j₁ (W := Z.gen ⊓ V) (inf_le_inf_left _ (inf_le_left.trans inf_le_left))
    (inf_le_inf_left _ (inf_le_left.trans inf_le_right)) (inf_le_right.trans hi) (inf_le_right.trans hj)
  refine (map_one _).trans ?_
  change (1 : Γ(Z.X, Z.gen ⊓ V)ˣ).val =
    (res (inf_le_right : Z.gen ⊓ V ≤ V) _ * (res _ (φ.u i j) * res _ (φ.u i₁ j₁)⁻¹)).val
  refine congrArg Units.val ?_
  simp only [map_mul, map_inv, Semi.LB.res_res]
  rw [mul_mul_mul_comm, mul_comm (res _ (L'.g j j₁)), h₁, ← mul_inv, mul_inv_cancel]

end GenIso

variable (Z)

abbrev VDivQ : Type := ℚ ⊗[ℤ] Z.VDivZ

variable {Z} in

def toQ : Z.VDivZ →+ Z.VDivQ := (TensorProduct.mk ℤ ℚ Z.VDivZ 1).toAddMonoidHom

def cDQ : Z.VDivQ →ₗ[ℚ] PicSym Z.X := LinearMap.liftBaseChange ℚ (firstChernPic.comp Z.vCls).toIntLinearMap

def capDeg_vp (p d : ℕ) : Z.VDivQ →ₗ[ℚ] PicSym Z.X →ₗ[ℚ] ℚ :=
  (ramIdx O p : ℚ)⁻¹ • LinearMap.liftBaseChange ℚ (Z.vDeg d).toIntLinearMap

variable {Z}

@[simp] theorem cDQ_toQ (D : Z.VDivZ) : Z.cDQ (toQ D) = firstChernPic (Z.vCls D) := by simp [cDQ, toQ]

theorem capDeg_vp_toQ (p d : ℕ) (D : Z.VDivZ) (Q : PicSym Z.X) :
    Z.capDeg_vp p d (toQ D) Q = Z.vDeg d D Q / ramIdx O p := by
  simp [capDeg_vp, toQ, div_eq_inv_mul]

def vResQ (C : Z.Comp) : Z.VDivQ →ₗ[ℚ] (Z.comp C).VDivQ := (Z.vRes C).toIntLinearMap.baseChange ℚ

@[simp] theorem vResQ_toQ (C : Z.Comp) (D : Z.VDivZ) : vResQ C (toQ D) = Model.toQ (Z.vRes C D) := rfl

theorem capDeg_vp_eq_sum (p d : ℕ) (D : Z.VDivQ) (Q : PicSym Z.X) : Z.capDeg_vp p d D Q =
    ∑ C ∈ Finset.univ.filter fun C : Z.Comp => (Z.comp C).relDim = d,
      (Z.comp C).capDeg_vp p (vResQ C D) (picSymPull (Z.compι C) Q) := by
  induction D using TensorProduct.induction_on with
  | zero => simp
  | tmul a D =>
    have : a ⊗ₜ[ℤ] D = a • toQ D := by simp [toQ, smul_tmul']
    simp only [this, map_smul, LinearMap.smul_apply, capDeg_vp_toQ, vResQ_toQ, Model.capDeg_vp_toQ, vDeg_apply,
      Finset.sum_div, Finset.smul_sum]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, Finset.sum_add_distrib]

theorem capDeg_vp_eq_zero (p : ℕ) {d n : ℕ} (D : Z.VDivQ) (hn : n ≠ d) {x : PicSym Z.X}
    (hx : x ∈ symDeg (SmallPic Z.X) n) : Z.capDeg_vp p d D x = 0 := by
  induction D using TensorProduct.induction_on with
  | zero => simp
  | tmul a D => simp [capDeg_vp, vDeg_eq_zero D hn hx]
  | add a b ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]

theorem vDeg_prod {d : ℕ} {D : Z.VDivZ} {I : ∀ C, (Z.comp C).effVert} (h : ∀ C, Z.vRes C D = Model.ofEff (I C))
    (L : Fin d → FinLB Z.X) : Z.vDeg d D (∏ i, (L i).c1) =
      ∑ C ∈ Finset.univ.filter fun C : Z.Comp => (Z.comp C).relDim = d,
        (interLen O (divMod (I C).1) fun i => ((L i).pull (Z.compι C)).lb : ℚ) := by
  rw [vDeg_apply]
  refine Finset.sum_congr rfl fun C hC => ?_
  simp only [h, map_prod, FinLB.pullback_firstChern]
  exact (Model.vDeg_ofEff_prod _ fun i => ((L i).pull (Z.compι C)).isLB).trans
    (if_pos ((Fintype.card_fin _).trans (Finset.mem_filter.1 hC).2.symm))

section Theory

variable (Z) (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

def divP : Z.VDivZ := Z.div p (natCast_ne_zero O p)

theorem toQ_div (g : O) (hg : g ≠ 0) : toQ (Z.div g hg) =
    (((IsDiscreteValuationRing.addVal O g).toNat : ℚ) / ramIdx O p) • toQ (Z.divP p) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  rw [divP, div_eq_addVal_smul hϖ, div_eq_addVal_smul hϖ (natCast_ne_zero O p), map_nsmul, map_nsmul,
    ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, ← ramIdx,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.2 (ramIdx_ne_zero O p))]

set_option linter.overlappingInstances false in

@[reducible] def toITh [CharP (ResidueField O) p] (d : ℕ) : Formalism.BasicNotions.DV.ITh where
  LB := FinLB Z.X
  Ch := PicSym Z.X
  c1 := FinLB.c1
  VDiv := Z.VDivQ
  cD := Z.cDQ
  capDeg := Z.capDeg_vp p d
  divP := toQ (Z.divP p)
  cD_divP := by simp [divP]
  dim := d + 1

end Theory

variable (Z) in

def vdiv (L L' : FinLB Z.X) (u : Z.GenIso L.lb L'.lb) : Z.VDivQ := toQ (u.div L.isLB L'.isLB)

theorem firstChern_eq_sub_divisor (L L' : FinLB Z.X) (u : Z.GenIso L.lb L'.lb) : L'.c1 = L.c1 - Z.cDQ (Z.vdiv L L' u) := by
  rw [vdiv, cDQ_toQ, GenIso.vCls_div, map_sub]
  exact (sub_sub_cancel _ _).symm

theorem vdiv_dual (L L' : FinLB Z.X) (u : Z.GenIso L.lb L'.lb) : Z.vdiv L.dual L'.dual u.dual = -Z.vdiv L L' u :=
  (congrArg toQ (u.div_dual L.isLB L'.isLB)).trans (map_neg _ _)

theorem vdiv_symm (L L' : FinLB Z.X) (u : Z.GenIso L.lb L'.lb) : Z.vdiv L' L u.symm = -Z.vdiv L L' u :=
  (congrArg toQ (u.div_symm L.isLB L'.isLB)).trans (map_neg _ _)

theorem vdiv_smul (L : FinLB Z.X) (g : O) (hg : g ≠ 0) : Z.vdiv L L (.smul L.isLB g hg) = toQ (Z.div g hg) :=
  congrArg toQ (GenIso.div_smul L.isLB g hg)

end NModel

theorem chiLenPic_pushforward_of_isClosedImmersion {X Y : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)]
    [Algebra R Γ(Y, ⊤)] (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : ∀ r : R, i.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r) (H : Y.Modules) :
    chiLenPic R ((Scheme.Modules.pushforward i).obj H) = chiLenPic R H ∘ pull i := by
  funext c
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  refine (chiLen_congr R (Twist.projIso M i H)).symm.trans ?_
  rw [chiLen_eq_of_linearEquiv R fun n => LinearEquiv.ofBijective _
    (cohPushMap_bijective_of_isClosedImmersion R i hi _ ⊤ n)]
  rfl

section Iso

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B B' : Model O} {f : B'.X ⟶ B.X} [IsIso f]
  (hf : f ≫ B.str = B'.str)

variable (f) in
include f in

theorem relDim_eq_of_isIso : B'.relDim = B.relDim := by
  refine Model.relDim_eq_iff.2 (Eq.trans ?_ B.dim_eq)
  rw [← topologicalKrullDim_eq_of_isEmbedding f.isOpenEmbedding.isEmbedding f.surjective.range_eq,
    topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id]

theorem vDeg_vPull_of_isIso (D : B.VDivZ) (x : PicSym B.X) :
    B'.vDeg (Model.vPull hf D) (picSymPull f x) = B.vDeg D x := by
  have key (I : B.effVert) : B'.vDeg (Model.vPull hf (Model.ofEff I)) (picSymPull f x) = B.vDeg (Model.ofEff I) x := by
    let g := (I.1.comapIso f).hom ≫ pullback.snd _ _
    have hg : (I.1.comap f).subschemeι ≫ f = g ≫ I.1.subschemeι := by
      simp [g, ← pullback.condition]
    have e : (Scheme.Modules.pushforward f).obj (divMod (I.1.comap f)) ≅ divMod I.1 :=
      (Scheme.Modules.pushforwardComp _ _ ≪≫ Scheme.Modules.pushforwardCongr hg ≪≫
        (Scheme.Modules.pushforwardComp _ _).symm).app _ ≪≫
        ((Scheme.Modules.pushforward I.1.subschemeι).mapIso (asIso (unitToPush g))).symm
    have h := (chiLenPic_congr O e).symm.trans
      (chiLenPic_pushforward_of_isClosedImmersion O f (Model.appTop_const hf) _)
    refine LinearMap.congr_fun (picSym_linearMap_ext
      (l := B'.vDeg (Model.vPull hf (Model.ofEff I)) ∘ₗ (picSymPull f).toLinearMap) fun n c => ?_) x
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_prod, picSymPull_c1Pic, Model.vPull_ofEff,
      Model.vDeg_ofEff, Model.effDeg, Model.IsVertical.deg, picForm_prod, relDim_eq_of_isIso f]
    rw [h, multiDiff_comap, Function.comp_apply, map_zero]
    rfl
  obtain ⟨I, J, rfl⟩ := Model.exists_eq_ofEff_sub D
  simp only [map_sub, LinearMap.sub_apply, key]

end Iso

namespace NModel

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : NModel O}

theorem vDeg_div_of_cover {ι : Type} [Fintype ι] {B : ι → Model O} (f : ∀ i, (B i).X ⟶ Z.X) [∀ i, IsOpenImmersion (f i)]
    (hf : ∀ i, f i ≫ Z.str = (B i).str) (hc : ∀ x, ∃ i, x ∈ Set.range (f i))
    (hd : ∀ i j, (Set.range (f i) ∩ Set.range (f j)).Nonempty → i = j) (d : ℕ) {g : O} (hg : g ≠ 0) (x : PicSym Z.X) :
    Z.vDeg d (Z.div g hg) x = ∑ i ∈ Finset.univ.filter fun i => (B i).relDim = d,
      (B i).vDeg ((B i).div g hg) (picSymPull (f i) x) := by
  have hirr (i) : IsIrreducible (Set.range (f i)) := by
    simpa using (IrreducibleSpace.isIrreducible_univ (B i).X).image _ (f i).continuous.continuousOn
  have hmem (i) : Set.range (f i) ∈ irreducibleComponents Z.X := ⟨hirr i, fun T hT hle y hy => by
    obtain ⟨j, hj⟩ := hc y
    obtain ⟨z, -, hz⟩ := hT.2 _ _ (f i).isOpenEmbedding.isOpen_range (f j).isOpenEmbedding.isOpen_range
      ((hirr i).1.mono fun _ h => ⟨hle h, h⟩) ⟨y, hy, hj⟩
    exact hd i j ⟨z, hz⟩ ▸ hj⟩
  let σ : ι → Z.Comp := fun i => ⟨_, hmem i⟩
  have hσ : Function.Bijective σ := ⟨fun i j h => hd i j (by
      rw [show Set.range (f j) = Set.range (f i) from (congrArg Subtype.val h).symm, Set.inter_self]
      exact (hirr i).1), fun C => by
    obtain ⟨y, hy⟩ := C.2.1.1
    obtain ⟨i, hi⟩ := hc y
    exact ⟨i, Subtype.ext (IsNormalScheme.eq_of_mem_irreducibleComponents (hmem i) C.2 hi hy)⟩⟩
  let e (i) : (B i).X ≅ (Z.comp (σ i)).X :=
    IsOpenImmersion.isoOfRangeEq (f i) (σ i).opens.ι (Scheme.Opens.range_ι (σ i).opens).symm
  have he (i) : (e i).hom ≫ Z.compι (σ i) = f i := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have he' (i) : (e i).hom ≫ (Z.comp (σ i)).str = (B i).str := by rw [← compι_str, ← Category.assoc, he, hf]
  rw [vDeg_apply, Finset.sum_filter, Finset.sum_filter, ← hσ.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [relDim_eq_of_isIso (e i).hom, vRes_div, ← vDeg_vPull_of_isIso (he' i), Model.vPull_div, ← he]
  refine if_congr Iff.rfl (congrArg _ ?_) rfl
  refine LinearMap.congr_fun (picSym_linearMap_ext (l := (picSymPull _).toLinearMap ∘ₗ (picSymPull _).toLinearMap)
    (l' := (picSymPull _).toLinearMap) fun n c => ?_) x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_prod, picSymPull_c1Pic, pull_comp]

def sigma {ι : Type} [Finite ι] (B : ι → Model O) [∀ i, GlobalTheory.IsNormalScheme (B i).X] : NModel O where
  X := ∐ fun i => (B i).X
  str := Sigma.desc fun i => (B i).str
  isProjOver := ProjSpace.isProjOver_sigmaDesc _ fun i => (B i).isProjOver
  flat := IsZariskiLocalAtSource.sigmaDesc fun i => (B i).flat

section Example

variable (O) (n N : ℕ) (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

def copies : NModel O :=
  haveI := Model.isNormalScheme_projSpace O N
  sigma fun _ : Fin n => Model.projSpace O N

def twistingSheafOnCopies : FinLB (copies O n N).X :=
  FinLB.pull ⟨N + 1, (ProjSpace.O1 O N).U, (ProjSpace.O1 O N).g, ProjSpace.O1_isLB O N⟩
    (Sigma.desc fun _ : Fin n => 𝟙 (PSpace O N))

theorem capDeg_divP_copies : ((copies O n (N + 1)).toITh p (N + 1)).capDeg ((copies O n (N + 1)).toITh p (N + 1)).divP
    ((twistingSheafOnCopies O n (N + 1)).c1 ^ (N + 1)) = n := by
  have h (i : Fin n) : picSymPull (Sigma.ι (fun _ : Fin n => (Model.projSpace O (N + 1)).X) i)
      ((twistingSheafOnCopies O n (N + 1)).c1 ^ (N + 1)) = c1 (Model.formalTwistingSheaf O (N + 1)) (ProjSpace.O1_isLB O _) ^ (N + 1) := by
    refine (map_pow _ _ _).trans (congrArg (· ^ (N + 1)) ((picSymPull_c1Pic _ _).trans (congrArg firstChernPic ?_)))
    refine (congrArg _ (FinLB.cls_pull _ _)).trans ((pull_comp _ _ _).symm.trans ?_)
    erw [Sigma.ι_desc, pull_id]
    rfl
  rw [capDeg_vp_toQ, divP, vDeg_div_of_cover (Z := copies O n (N + 1)) (B := fun _ : Fin n => Model.projSpace O (N + 1))
    (fun i => Sigma.ι (fun _ : Fin n => (Model.projSpace O (N + 1)).X) i) (fun i => Sigma.ι_desc _ _)
    (fun x => (sigmaOpenCover _).exists_eq x)
    (fun i j ⟨x, hi, hj⟩ => by_contra fun hij => Set.disjoint_left.1
      (Opens.coe_disjoint.2 (disjoint_opensRange_sigmaι _ i j hij)) hi hj)]
  refine (congrArg (· / (ramIdx O p : ℚ)) (Finset.sum_congr rfl fun i _ =>
    (congrArg _ (h i)).trans (Model.vDeg_div_projSpace N (natCast_ne_zero O p)))).trans ?_
  simp only [Model.relDim_projSpace, Finset.filter_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_div_cancel_right₀ (n : ℚ) (b := ramIdx O p) (Nat.cast_ne_zero.2 (ramIdx_ne_zero O p))

example : let Z := copies O 2 1; let L := twistingSheafOnCopies O 2 1
    let D := Z.vdiv L L (.smul L.isLB p (natCast_ne_zero O p))
    (Z.toITh p 1).capDeg D L.c1 = 2 ∧ (Z.toITh p 1).capDeg D L.dual.c1 = -2 ∧ (Z.toITh p 1).capDeg D 1 = 0 := by
  intro Z L D
  have h : (Z.toITh p 1).capDeg D L.c1 = 2 := by
    rw [show D = _ from vdiv_smul _ _ _, ← pow_one L.c1]
    exact capDeg_divP_copies O 2 0 p
  exact ⟨h, by rw [FinLB.firstChern_dual, map_neg, h],
    capDeg_vp_eq_zero p _ (n := 0) (by simp) (Submodule.subset_span ⟨finZeroElim, by simp⟩)⟩

example : ¬ (VPair.const (copies O 1 1) p (natCast_ne_zero O p)).IsIsom (.zero _) := fun h => by
  have := capDeg_divP_copies O 1 0 p
  rw [capDeg_vp_toQ, divP, div, VPair.cls_eq_iff.2 h, VPair.cls_zero] at this
  simp at this

end Example

end NModel

section Mdl

open NumberField GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

@[reducible] def nmodel (Z : Mdl Y i₀) : NModel (Z.i.c.V W) where
  X := Z.X
  str := Z.s
  normal := Z.normal
  isProjOver := ⟨Z.n, Z.I.subschemeι, inferInstance, rfl⟩
  flat := Z.flat

theorem natCast_mem_nonunits_V {l : Level H} (c : Coeff l) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) :
    (p : c.F) ∈ (c.V W).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp.ne_zero
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

theorem isDiscreteValuationRing_V {l : Level H} (c : Coeff l) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) :
    IsDiscreteValuationRing (c.V W) :=
  haveI := c.fin
  haveI : NumberField c.F := {}
  (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp.ne_zero
    (natCast_mem_nonunits_V c hp hW)).1

theorem charP_residueField_of_mem_nonunits {l : Level H} (c : Coeff l) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) :
    CharP (ResidueField (c.V W)) p := by
  refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
  rw [← map_natCast (residue (c.V W)), residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  exact_mod_cast natCast_mem_nonunits_V c hp hW

abbrev GenIso (Z : Mdl Y i₀) (L L' : FinLB Z.X) : Type := (nmodel Z).GenIso L.lb L'.lb

variable (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (d : ℕ)

@[reducible] def ithOf : Formalism.BasicNotions.DV.ITh :=
  haveI := Fact.mk hp
  haveI := isDiscreteValuationRing_V Z.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits Z.i.c hp hW
  (nmodel Z).toITh p d

theorem dim_ithOf : (ithOf hp hW Z d).dim = d + 1 := rfl

theorem LB_ithOf : (ithOf hp hW Z d).LB = FinLB Z.X := rfl

theorem firstChern_lineBundleTheory (L : FinLB Z.X) : (ithOf hp hW Z d).c1 L = L.c1 := rfl

theorem firstChern_dual_eq_neg (L : FinLB Z.X) : (ithOf hp hW Z d).c1 L.dual = -(ithOf hp hW Z d).c1 L := L.firstChern_dual

theorem capDeg_ithOf (D : (ithOf hp hW Z d).VDiv) (Q : (ithOf hp hW Z d).Ch) :
    haveI := Fact.mk hp
    haveI := isDiscreteValuationRing_V Z.i.c hp hW
    haveI := charP_residueField_of_mem_nonunits Z.i.c hp hW
    (ithOf hp hW Z d).capDeg D Q = ∑ C ∈ Finset.univ.filter fun C : (nmodel Z).Comp => ((nmodel Z).comp C).relDim = d,
      (((nmodel Z).comp C).toITh p).capDeg (NModel.vResQ C D) (picSymPull ((nmodel Z).compι C) Q) :=
  haveI := isDiscreteValuationRing_V Z.i.c hp hW
  NModel.capDeg_vp_eq_sum p d D Q

variable {Z}

def vdiv (L L' : FinLB Z.X) (u : GenIso Z L L') : (ithOf hp hW Z d).VDiv :=
  haveI := isDiscreteValuationRing_V Z.i.c hp hW
  (nmodel Z).vdiv L L' u

theorem firstChern_eq_sub_divisor (L L' : FinLB Z.X) (u : GenIso Z L L') :
    (ithOf hp hW Z d).c1 L' = (ithOf hp hW Z d).c1 L - (ithOf hp hW Z d).cD (vdiv hp hW d L L' u) :=
  haveI := isDiscreteValuationRing_V Z.i.c hp hW
  NModel.firstChern_eq_sub_divisor (Z := nmodel Z) L L' u

theorem vdiv_dual (L L' : FinLB Z.X) (u : GenIso Z L L') :
    vdiv hp hW d L.dual L'.dual (NModel.GenIso.dual u) = -vdiv hp hW d L L' u :=
  haveI := isDiscreteValuationRing_V Z.i.c hp hW
  NModel.vdiv_dual (Z := nmodel Z) L L' u

def fpairOf {r : ℕ} (x x' : Fin r → FinLB Z.X) (u : ∀ i, GenIso Z (x i) (x' i)) :
    Formalism.BasicNotions.DV.FPair (ithOf hp hW Z d) r :=
  ⟨x, x', fun i => vdiv hp hW d _ _ (u i), fun i => firstChern_eq_sub_divisor hp hW d _ _ (u i)⟩

include hp hW

theorem gen_eq_basicOpen : (nmodel Z).gen = Z.X.basicOpen (p : Γ(Z.X, ⊤)) := by
  have := Fact.mk hp
  have := isDiscreteValuationRing_V Z.i.c hp hW
  have := charP_residueField_of_mem_nonunits Z.i.c hp hW
  rw [(nmodel Z).gen_eq_basicOpen (natCast_ne_zero _ p) (natCast_mem_maximalIdeal _ p), map_natCast]

theorem mem_gen_iff_inQ {x : Z.X} : x ∈ (nmodel Z).gen ↔ Z.inQ x := by
  have := isDiscreteValuationRing_V Z.i.c hp hW
  have h (g : Z.i.c.V W) : (Z.X.evaluation ⊤ x trivial).hom ((nmodel Z).const g) ≠ 0 ↔
      x ∈ Z.X.basicOpen ((nmodel Z).const g) := Z.X.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) x trivial _
  refine ⟨fun hx => charZero_of_inj_zero fun n hn => by_contra fun h0 => ?_, fun hx => ?_⟩
  · exact (h n).2 ((nmodel Z).gen_le_basicOpen (Nat.cast_ne_zero.2 h0) hx) (by simpa using hn)
  · have : CharZero (Z.X.residueField x) := hx
    rw [gen_eq_basicOpen hp hW, ← map_natCast (nmodel Z).const, ← h]
    simpa using hp.ne_zero

theorem chart_le_gen (a : Fin Z.m) : (Z.U a).1 ≤ (nmodel Z).gen := by
  rw [gen_eq_basicOpen hp hW]
  refine le_basicOpen_of_isUnit le_top ?_
  rw [map_natCast, ← map_natCast (Z.alg a)]
  exact (Ne.isUnit (Nat.cast_ne_zero.2 hp.ne_zero)).map _

theorem opn_subset_gen : Z.opn ⊆ (nmodel Z).gen := by
  rw [← Z.cover]
  exact Set.iUnion_subset (chart_le_gen hp hW)

end Mdl

end GlobalTheory.ShFam.Pad
