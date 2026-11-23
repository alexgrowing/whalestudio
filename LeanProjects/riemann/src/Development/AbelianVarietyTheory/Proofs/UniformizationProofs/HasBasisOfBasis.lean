import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecKIsUnit

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericSectionBasis

section Calc

variable {F : Type} [CommRing F] {X Y Y' Z : Scheme.{0}} {n : ℕ}

def IsComb {M : LB Y} (p : Y ⟶ Sp F) (b : Fin n → LB.Sec M) (c : Fin n → F) (s : LB.Sec M) : Prop :=
  ∀ j, s.f j = ∑ i, resTop _ (scal p (c i)) * (b i).f j

def HasBasis (M : LB Y) (p : Y ⟶ Sp F) (n : ℕ) : Prop :=
  ∃ b : Fin n → LB.Sec M, ∀ s : LB.Sec M, ∃! c : Fin n → F, IsComb p b c s

theorem exists_comb {M : LB Y} (p : Y ⟶ Sp F) (b : Fin n → LB.Sec M) (c : Fin n → F) :
    ∃ s : LB.Sec M, IsComb p b c s :=
  ⟨⟨fun j => ∑ i, resTop _ (scal p (c i)) * (b i).f j, fun j j' => by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (scal p (c i)) (b i)).compat j j'⟩, fun _ => rfl⟩

theorem gs_comb {M : LB Y} (p : Y ⟶ Sp F) (b : Fin n → LB.Sec M) (c : Fin n → F) (r : Z ⟶ Y) (z : Z) (j : M.ι)
    (hz : r z ∈ M.U j) :
    gs r z (M.U j) (∑ i, resTop _ (scal p (c i)) * (b i).f j) =
      ∑ i, cst (r ≫ p) z (c i) * gs r z (M.U j) ((b i).f j) := by
  rw [gs_eq r z _ hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← gs_eq r z _ hz, gs_mul r z _ hz, GlobalTheory.IndivisibleSection.gs_scal p r z _ hz]

theorem HasBasis.transfer {A : LB Y'} {B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (σ : Y' ⟶ Y) (τ : Y ⟶ Y')
    (h₁ : τ ≫ σ = 𝟙 Y) (p : Y ⟶ Sp F) (p' : Y' ⟶ Sp F) (hp : σ ≫ p = p')
    (u : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y') (z : Z), A.ι → B.ι → (Z.presheaf.stalk z)ˣ)
    (Rel : LB.Sec A → LB.Sec B → Prop)
    (hRel : ∀ s t, Rel s t → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (a : A.ι) (b : B.ι), r z ∈ A.U a →
      (r ≫ σ) z ∈ B.U b → gs r z (A.U a) (s.f a) = (u Z r z a b).val * gs (r ≫ σ) z (B.U b) (t.f b))
    (hl : ∀ t, ∃ s, Rel s t) (hr : ∀ s, ∃ t, Rel s t) (H : HasBasis B p n) : HasBasis A p' n := by
  obtain ⟨β, hβ⟩ := H
  choose β' hβ' using fun i => hl (β i)
  refine ⟨β', fun s => ?_⟩
  obtain ⟨t, ht⟩ := hr s
  have key : ∀ c, IsComb p' β' c s ↔ IsComb p β c t := fun c => by
    constructor
    · intro h j
      refine fn_ext fun y hy => ?_
      obtain ⟨a, ha⟩ := exists_chart hA (τ y)
      have hy' : (τ ≫ σ) y ∈ B.U j := by rw [h₁]; exact hy
      have e := hRel s t ht Y τ y a j ha hy'
      rw [h a, gs_comb p' β' c τ y a ha] at e
      simp only [fun i => hRel _ _ (hβ' i) Y τ y a j ha hy', h₁] at e
      rw [gs_comb p β c (𝟙 Y) y j hy, ← (u Y τ y a j).mul_right_inj, ← e, Finset.mul_sum, ← hp,
        ← Category.assoc, h₁]
      exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
    · intro h a
      refine fn_ext fun y hy => ?_
      obtain ⟨j, hj⟩ := exists_chart hB (σ y)
      have hy' : (𝟙 Y' ≫ σ) y ∈ B.U j := hj
      rw [hRel s t ht Y' (𝟙 Y') y a j hy hy', h j, gs_comb p β c _ y j hy', gs_comb p' β' c (𝟙 Y') y a hy,
        Finset.mul_sum, ← hp, Category.assoc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hRel _ _ (hβ' i) Y' (𝟙 Y') y a j hy hy']
      exact mul_left_comm _ _ _
  simp only [key]
  exact hβ t

theorem exists_inv_iso {A B : LB X} (w : LB.Iso A B) (hw : w.IsGen) : ∃ w' : LB.Iso B A, w'.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (a : A.ι) (b : B.ι), r z ∈ A.U a ⊓ B.U b →
      gm r z ((LB.div A B).U (a, b)) (w'.s (a, b)) = (gm r z ((LB.div B A).U (b, a)) (w.s (b, a)))⁻¹ := by
  have le : ∀ p : A.ι × B.ι, A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1 := fun p y hy => ⟨hy.2, hy.1⟩
  refine ⟨⟨fun p => (res (le p) (w.s (p.2, p.1)))⁻¹⟩, fun p q => unit_ext fun y hy => ?_,
    fun Z r z a b hz => (map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z (le (a, b)) hz _))⟩
  have hm : (𝟙 X : X ⟶ X) y ∈ B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1))) (hw (p.2, p.1) (q.2, q.1))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) y (p.2, p.1) (q.2, q.1) hm) (gm_res _ y _ hm _))))
  have v : ∀ p : A.ι × B.ι, y ∈ A.U p.1 ⊓ B.U p.2 → gm (𝟙 X) y (A.U p.1 ⊓ B.U p.2) (res (le p) (w.s (p.2, p.1)))⁻¹ =
      (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹ := fun p hp =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))
  refine ((gm_res _ y _ hy _).trans ((v p hy.1).trans (congrArg (·⁻¹) e'))).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div B A (𝟙 X) y p q hy)
    ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
  rw [mul_inv, mul_inv, inv_inv, mul_comm (gm (𝟙 X) y _ (A.g p.1 q.1))]
  rfl

theorem HasBasis.of_iso {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B) {p : Y ⟶ Sp F}
    (H : HasBasis B p n) : HasBasis A p n := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw', e⟩ := exists_inv_iso w hw
  refine H.transfer hA hB (𝟙 Y) (𝟙 Y) (Category.id_comp _) p p (Category.id_comp _)
    (fun Z r z a b => (gm r z ((LB.div B A).U (b, a)) (w.s (b, a)))⁻¹) _ (fun _ _ h => h)
    (fun t => ⟨secOfIso t hw hA hB, fun Z r z a b ha hb => ?_⟩)
    (fun s => ⟨secOfIso s hw' hB hA, fun Z r z a b ha hb => ?_⟩)
  · rw [Category.comp_id] at hb ⊢
    exact GlobalTheory.GenericGenerated.gs_secOfIso w t hw hA hB a b r z ⟨ha, hb⟩
  · rw [Category.comp_id] at hb ⊢
    rw [GlobalTheory.GenericGenerated.gs_secOfIso w' s hw' hB hA b a r z ⟨hb, ha⟩, e Z r z a b ⟨ha, hb⟩, inv_inv,
      Units.inv_mul_cancel_left]

theorem exists_pull_gs {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = φ' k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L φ' j →
      gs r z (LB.wchart L φ' j) (s'.f j) = gs (r ≫ h) z (LB.wchart L φ j) (s.f j) := by
  obtain ⟨s', hs'⟩ := GlobalTheory.IndivisibleSection.exists_pull_chart s h φ' e
  refine ⟨s', fun Z r z j hz => ?_⟩
  have le : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j := fun y hy => Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy k
    rw [← e] at this
    exact this
  rw [hs' j le]
  exact (gs_res r z le hz _).trans (gs_pull r h z _ (le hz) _)

theorem HasBasis.pull {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)}
    {ε : K → ℤ} (σ : Y' ⟶ Y) (τ : Y ⟶ Y') (h₁ : τ ≫ σ = 𝟙 Y) (h₂ : σ ≫ τ = 𝟙 Y') (e : ∀ k, σ ≫ φ k = φ' k)
    (p : Y ⟶ Sp F) (p' : Y' ⟶ Sp F) (hp : σ ≫ p = p') (H : HasBasis (LB.LinComb L φ ε) p n) :
    HasBasis (LB.LinComb L φ' ε) p' n := by
  have e' : ∀ k, τ ≫ φ' k = φ k := fun k => by rw [← e, ← Category.assoc, h₁, Category.id_comp]
  have mem : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (b : K → L.ι), (r ≫ σ) z ∈ LB.wchart L φ b →
      r z ∈ LB.wchart L φ' b := fun Z r z b hb => Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hb k
    rw [← e]
    exact this
  refine H.transfer (linComb_isLB L hL _ _) (linComb_isLB L hL _ _) σ τ h₁ p p' hp
    (fun Z r z a b => trF φ' ε r z a b) _ (fun _ _ h => h) (fun t => ?_) (fun s => ?_)
  · obtain ⟨s, hs⟩ := exists_pull_gs t σ φ' e
    exact ⟨s, fun Z r z a b ha hb => (sec_trans s r z ha (mem Z r z b hb)).trans
      (congrArg _ (hs Z r z b (mem Z r z b hb)))⟩
  · obtain ⟨t, ht⟩ := exists_pull_gs s τ φ e'
    refine ⟨t, fun Z r z a b ha hb => (sec_trans s r z ha (mem Z r z b hb)).trans (congrArg _ ?_)⟩
    refine Eq.trans ?_ (ht Z (r ≫ σ) z b hb).symm
    rw [Category.assoc, h₂, Category.comp_id]

end Calc

section Field

variable {F : Type} [Field F] (P : PolAV (Spec (CommRingCat.of F))) (k : ℕ)

theorem hasBasis_of_basis (q : Sp F ⟶ Sp F) (hq : q = 𝟙 _) {n : ℕ}
    (β : Fin n → LB.Sec (LPow P.A P.L k (Over.mk q)))
    (hli : LinearIndependent Γ((Over.mk q).left, ⊤) (fun i => (SecM.ofSec P.A (β i) : SecM P.A P.L k (Over.mk q))))
    (hsp : Submodule.span Γ((Over.mk q).left, ⊤)
      (Set.range fun i => (SecM.ofSec P.A (β i) : SecM P.A P.L k (Over.mk q))) = ⊤) :
    HasBasis (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => (k : ℤ))) P.A.hom n := by
  subst hq
  let u : P.A ⟶ Over.mk (𝟙 (Sp F)) := Over.homMk P.A.hom (Category.comp_id _)
  have hw : (snd (Over.mk (𝟙 (Sp F))) P.A).left ≫ P.A.hom = (fst (Over.mk (𝟙 (Sp F))) P.A).left :=
    (Over.w (snd (Over.mk (𝟙 (Sp F))) P.A)).trans
      ((Over.w (fst (Over.mk (𝟙 (Sp F))) P.A)).symm.trans (Category.comp_id _))
  have hu : snd (Over.mk (𝟙 (Sp F))) P.A ≫ u = fst (Over.mk (𝟙 (Sp F))) P.A := Over.OverMorphism.ext hw
  have e₁ : lift u (𝟙 P.A) ≫ snd (Over.mk (𝟙 (Sp F))) P.A = 𝟙 _ := lift_snd _ _
  have e₂ : snd (Over.mk (𝟙 (Sp F))) P.A ≫ lift u (𝟙 P.A) = 𝟙 _ := by
    rw [comp_lift, hu, Category.comp_id, lift_fst_snd]
  have e₃ : lift u (𝟙 P.A) ≫ fst (Over.mk (𝟙 (Sp F))) P.A = u := lift_fst _ _
  refine HasBasis.pull P.isLB (φ := fun _ : Fin 1 => (snd (Over.mk (𝟙 (Sp F))) P.A).left)
    (lift u (𝟙 P.A)).left (snd (Over.mk (𝟙 (Sp F))) P.A).left
    (congrArg CommaMorphism.left e₂) (congrArg CommaMorphism.left e₁) (fun _ => congrArg CommaMorphism.left e₁)
    (fst (Over.mk (𝟙 (Sp F))) P.A).left _ (congrArg CommaMorphism.left e₃) ⟨β, fun s => ?_⟩
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv
  have key : ∀ c : Fin n → F, IsComb (fst (Over.mk (𝟙 (Sp F))) P.A).left β c s ↔
      ∑ i, (show Γ((Over.mk (𝟙 (Sp F))).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) •
        (SecM.ofSec P.A (β i) : SecM P.A P.L k (Over.mk (𝟙 (Sp F)))) = SecM.ofSec P.A s := fun c => by
    rw [Subtype.ext_iff, Submodule.coe_sum, funext_iff]
    refine forall_congr' fun j => ?_
    rw [Finset.sum_apply]
    exact eq_comm
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
  choose c hc using fun i => bij.2 (r i)
  obtain rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) = r := funext hc
  refine ⟨c, (key c).2 hr, fun c' hc' => funext fun i => bij.1 ?_⟩
  exact Fintype.linearIndependent_iffₛ.1 hli _ _ (((key c').1 hc').trans hr.symm) i

theorem hasBasis_field (hS : SecBaseChangeSt) (hk : 1 ≤ k) :
    HasBasis (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => (k : ℤ))) P.A.hom (k ^ P.g) := by
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of F)) P k hk (IsLocalRing.closedPoint F)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  let t : Spec (CommRingCat.of F) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of F))) ⊤).left :=
    (Spec (CommRingCat.of F)).topIso.inv
  have ht : t ≫ (overRes (T := baseOver (Spec (CommRingCat.of F))) ⊤).hom = 𝟙 _ := by
    show (Spec (CommRingCat.of F)).topIso.inv ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of F)).topIso.inv_hom_id
  have pull : ∀ i, ∃ b' : LB.Sec (LPow P.A P.L k (baseAt t)),
      IsPullSec P.A P.L k (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i) b' := fun i => by
    obtain ⟨s', hs'⟩ := GlobalTheory.IndivisibleSection.exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
    exact ⟨s', fun j => hs' j _⟩
  choose b' hb' using pull
  obtain ⟨hli, hsp⟩ := hb F t b' hb'
  exact hasBasis_of_basis P k _ ht b' hli hsp

end Field

theorem iso_pow {X X' Y : Scheme.{0}} {L : LB X} {M : LB X'}
    (g : Y ⟶ X) (gi : X ⟶ Y) (e₁ : gi ≫ g = 𝟙 X) (e₂ : g ≫ gi = 𝟙 Y) (p : Y ⟶ X')
    (H : LBIso (L.pull g) (M.pull p)) (k : ℤ) :
    LBIso (LB.LinComb M (K := Fin 1) (fun _ => p) (fun _ => k))
      (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k)) := by
  obtain ⟨w, hw⟩ : LBIso L (M.pull (gi ≫ p)) :=
    LBIso.chartPull (chartPullSec L g gi e₁)
      (chartPullSame M (fun _ : PUnit => gi ≫ p) (fun _ => p) (fun _ => 1) gi fun _ => rfl) H
  have H₂ := iso_linComb ((isGen_iff w).1 hw) (fun _ : Fin 1 => g) (fun _ => k)
  have ep : (fun _ : Fin 1 => g ≫ gi ≫ p) = fun _ => p := by
    funext _; rw [← Category.assoc, e₂, Category.id_comp]
  rw [ep] at H₂
  exact LBIso.symm H₂

theorem exists_secK_basis : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), 1 ≤ k → ∃ b : Fin (k ^ A.g) → U.SecK k, (∀ c : Fin (k ^ A.g) → FractionRing R, ∃ s : U.SecK k, (∀ j, (s).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j)) ∧ ∀ s : U.SecK k, ∃! c : Fin (k ^ A.g) → FractionRing R, (∀ j, (s).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j) := by
  intro hS R _ _ I D A G _ _ U k hk
  have e₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.inv_hom_id
  have e₂ : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.hom_inv_id
  have H₁ := (hasBasis_field A k hS hk).pull A.isLB (φ' := fun _ => U.gen.hom.left) U.gen.hom.left U.gen.inv.left
    e₁ e₂ (fun _ => Category.comp_id _) _ (pullback.snd G.hom (jK R)) (Over.w U.gen.hom)
  obtain ⟨b, hb⟩ := H₁.of_iso (linComb_isLB _ U.LG.isLB _ _) (linComb_isLB _ A.isLB _ _)
    (iso_pow U.gen.hom.left U.gen.inv.left e₁ e₂ (pullback.fst G.hom (jK R)) U.ext k)
  exact ⟨b, fun c => exists_comb _ b c, hb⟩

end GlobalTheory.GenericSectionBasis
