import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFamGlue

section General

variable {X₁ X₂ Y T : Scheme.{0}} {L : LB X₁} {M : LB X₂} {a : Y ⟶ X₁} {b : Y ⟶ X₂} {K : Type} [Fintype K]

def isoGerm (w : LB.Iso (L.pull a) (M.pull b)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : M.ι) (q : L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z ((M.pull b).U (fun _ => p) ⊓ (L.pull a).U (fun _ => q)) (w.s (fun _ => p, fun _ => q))

theorem isoGerm_trans {w : LB.Iso (L.pull a) (M.pull b)} (hw : w.IsGen) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    {p p' : M.ι} {q q' : L.ι}
    (hp : b (r z) ∈ M.U p) (hp' : b (r z) ∈ M.U p') (hq : a (r z) ∈ L.U q) (hq' : a (r z) ∈ L.U q') :
    isoGerm w r z p q = gm (r ≫ b) z _ (M.g p p') * (gm (r ≫ a) z _ (L.g q q'))⁻¹ * isoGerm w r z p' q' := by
  have hm : r z ∈ (M.pull b).U (fun _ => p) ⊓ (L.pull a).U (fun _ => q) ⊓
      ((M.pull b).U (fun _ => p') ⊓ (L.pull a).U (fun _ => q')) :=
    ⟨⟨mem_pull.2 hp, mem_pull.2 hq⟩, mem_pull.2 hp', mem_pull.2 hq'⟩
  refine (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _)
    (hw (fun _ => p, fun _ => q) (fun _ => p', fun _ => q'))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ((gm_div (L.pull a) (M.pull b) r z (fun _ => p, fun _ => q) (fun _ => p', fun _ => q') hm).trans ?_)
      (gm_res r z _ hm _))))
  exact congrArg₂ (· * ·) (gm_pull_g M b r z _ _ hm.1.1 hm.2.1) (congrArg (·⁻¹) (gm_pull_g L a r z _ _ hm.1.2 hm.2.2))

theorem prod_trans {w : LB.Iso (L.pull a) (M.pull b)} (hw : w.IsGen) (ψ : K → (T ⟶ Y)) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z) {p p' : K → M.ι} {q q' : K → L.ι}
    (hp : r z ∈ LB.wchart M (fun k => ψ k ≫ b) p) (hp' : r z ∈ LB.wchart M (fun k => ψ k ≫ b) p')
    (hq : r z ∈ LB.wchart L (fun k => ψ k ≫ a) q) (hq' : r z ∈ LB.wchart L (fun k => ψ k ≫ a) q') :
    ∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k = trF (fun k => ψ k ≫ b) ε r z p p' *
      (trF (fun k => ψ k ≫ a) ε r z q q')⁻¹ * ∏ k, isoGerm w (r ≫ ψ k) z (p' k) (q' k) ^ ε k := by
  rw [trF, trF, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [isoGerm_trans hw (r ≫ ψ k) z (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k)
    (Set.mem_iInter.1 hq' k), mul_zpow, mul_zpow, inv_zpow]
  simp only [Category.assoc]

theorem exists_down (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull a) (M.pull b)} (hw : w.IsGen) (ψ : K → (T ⟶ Y))
    (ε : K → ℤ) (σ : LB.Sec (LB.LinComb M (fun k => ψ k ≫ b) ε)) :
    ∃ τ : LB.Sec (LB.LinComb L (fun k => ψ k ≫ a) ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) (p : K → M.ι) (q : K → L.ι),
      r z ∈ LB.wchart M (fun k => ψ k ≫ b) p → r z ∈ LB.wchart L (fun k => ψ k ≫ a) q →
      (∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k).val * gs r z (LB.wchart L (fun k => ψ k ≫ a) q) (τ.f q) =
        gs r z (LB.wchart M (fun k => ψ k ≫ b) p) (σ.f p) := by
  have cov : ∀ y : T, ∃ p, y ∈ LB.wchart M (fun k => ψ k ≫ b) p := fun y => by
    choose I hI using fun k => exists_chart hM ((ψ k ≫ b) y)
    exact ⟨I, Set.mem_iInter.2 hI⟩
  have glue : ∀ q : K → L.ι, ∃ c : Γ(T, LB.wchart L (fun k => ψ k ≫ a) q), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z)
      (p : K → M.ι), r z ∈ LB.wchart M (fun k => ψ k ≫ b) p → r z ∈ LB.wchart L (fun k => ψ k ≫ a) q →
      gs r z _ c = (∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k)⁻¹.val *
        gs r z (LB.wchart M (fun k => ψ k ≫ b) p) (σ.f p) := by
    intro q
    let V : (K → M.ι) → T.Opens := fun p => LB.wchart M (fun k => ψ k ≫ b) p ⊓ LB.wchart L (fun k => ψ k ≫ a) q
    have h₃ : ∀ p k, V p ≤ ψ k ⁻¹ᵁ ((M.pull b).U (fun _ => p k) ⊓ (L.pull a).U (fun _ => q k)) := fun p k y hy =>
      ⟨mem_pull.2 (Set.mem_iInter.1 hy.1 k), mem_pull.2 (Set.mem_iInter.1 hy.2 k)⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ p, Γ(T, V p), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) p, r z ∈ V p →
        gs r z (V p) (u p) = (∏ k, isoGerm w (r ≫ ψ k) z (p k) (q k) ^ ε k)⁻¹.val *
          gs r z (LB.wchart M (fun k => ψ k ≫ b) p) (σ.f p) :=
      ⟨fun p => (∏ k, res (h₃ p k) (pullU (ψ k) _ (w.s (fun _ => p k, fun _ => q k))) ^ ε k)⁻¹.val *
          (T.presheaf.map (homOfLE (inf_le_left : V p ≤ LB.wchart M (fun k => ψ k ≫ b) p)).op).hom (σ.f p),
        fun Z r z p hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans
          (congrArg Units.val ((map_inv _ _).trans (congrArg (·⁻¹) ((map_prod _ _ _).trans
            (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
              ((gm_res r z (h₃ p k) hz _).trans (gm_pull r (ψ k) z _ (h₃ p k hz) _))))))))) (gs_res r z _ hz _))⟩
    obtain ⟨c, hc, -⟩ := T.sheaf.existsUnique_gluing' V (LB.wchart L (fun k => ψ k ≫ a) q)
      (fun p => homOfLE inf_le_right) (fun y hy => by
        obtain ⟨p, hp⟩ := cov y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hp, hy⟩) u
      (fun p p' => fn_ext (V := V p ⊓ V p') fun y hy => by
        refine (gs_res (𝟙 T) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 T) y inf_le_right hy _).symm)
        rw [hu _ _ y p hy.1, hu _ _ y p' hy.2, sec_trans σ (𝟙 T) y hy.1.1 hy.2.1,
          prod_trans hw ψ ε (𝟙 T) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          mul_eq_left.1 (trF_trans hL _ ε (𝟙 T) y hy.1.2 hy.1.2 hy.1.2), ← _root_.mul_assoc, ← Units.val_mul]
        congr 2
        rw [inv_one, _root_.mul_one, mul_inv_rev, inv_mul_cancel_right])
    refine ⟨c, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ V p := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_right hz c).symm.trans ((congrArg (gs r z (V p)) (hc p)).trans (hu Z r z p hz))
  choose c hc using glue
  refine ⟨⟨c, fun q q' => fn_ext fun y hy => ?_⟩, fun Z r z p q hp hq => ?_⟩
  · obtain ⟨p, hp⟩ := cov y
    refine (gs_res (𝟙 T) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 T) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 T) y _ hy _).trans (congrArg Units.val (gm_linComb L _ ε (𝟙 T) y q q' hy.1 hy.2)))
      (gs_res (𝟙 T) y _ hy _))).symm)
    refine (hc q _ (𝟙 T) y p hp hy.1).trans (Eq.trans ?_ (congrArg _ (hc q' _ (𝟙 T) y p hp hy.2)).symm)
    rw [prod_trans hw ψ ε (𝟙 T) y hp hp hy.1 hy.2, mul_eq_left.1 (trF_trans hM _ ε (𝟙 T) y hp hp hp),
      ← _root_.mul_assoc, ← Units.val_mul, _root_.one_mul, mul_inv_rev, inv_inv, _root_.mul_comm _⁻¹]
    rfl
  · exact (congrArg _ (hc q Z r z p hp hq)).trans (Units.mul_inv_cancel_left _ _)

def sumSec {N : LB Y} {A : Type} (S : Finset A) (s : A → N.Sec) : N.Sec where
  f i := ∑ x ∈ S, (s x).f i
  compat i j := by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => (s x).compat i j

theorem sval_sumSec {φ : K → (Y ⟶ X₁)} {ε : K → ℤ} {A : Type} (S : Finset A) (s : A → (LB.LinComb L φ ε).Sec)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (sumSec S s) r z J = ∑ x ∈ S, sval (s x) r z J := DVR.gs_fsum r z _ (hJ.mem φ r) S _

end General

section Main

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ)

theorem formEq_term (a : D.toPre.P.A ⟶ D.toPre.P.A) (b : thickObj R I e G ⟶ thickObj R I e G)
    (hb : b.left ≫ DVR.pGl U e = DVR.pGl U e ≫ a.left) (n j : ℤ) (β : D.toPre.X) :
    FormEq (Sum.elim (fun k => DVR.pGl U e ≫ tφ D.toPre a β k) (DVR.Oφl U e β)) (Sum.elim (tε n j) Oinvε)
      (fun k => (![𝟙 _, b.left] : Fin 2 → _) k ≫ DVR.pGl U e) ![n, j] := by
  intro V _ h
  have a₀ : DVR.pGl U e ≫ tφ D.toPre a β 0 = DVR.pGl U e := Category.comp_id _
  have a₁ : DVR.pGl U e ≫ tφ D.toPre a β 1 = DVR.Oφl U e β 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U.gt e).pG (𝟙 _) (DVR.cP D.toPre _ β)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (DVR.comp_cP D.toPre _ β)))
  have a₂ : DVR.pGl U e ≫ tφ D.toPre a β 2 = DVR.Oφl U e β 1 :=
    congrArg (fun z => z.left) (DVR.comp_cP D.toPre (U.gt e).pG β)
  have a₃ : DVR.pGl U e ≫ tφ D.toPre a β 3 = DVR.Oφl U e β 3 :=
    congrArg (fun z : _ ⟶ D.toPre.P.A => z.left) (MonObj.comp_one (M := D.toPre.P.A) (U.gt e).pG)
  have a₄ : DVR.Oφl U e β 2 = DVR.pGl U e := rfl
  have a₅ : DVR.pGl U e ≫ tφ D.toPre a β 4 = b.left ≫ DVR.pGl U e := hb.symm
  have a₆ : (![𝟙 _, b.left] : Fin 2 → _) 0 ≫ DVR.pGl U e = DVR.pGl U e := Category.id_comp _
  have a₇ : (![𝟙 _, b.left] : Fin 2 → _) 1 ≫ DVR.pGl U e = b.left ≫ DVR.pGl U e := rfl
  rw [Fintype.prod_sum_type, Fin.prod_univ_five, Fin.prod_univ_four, Fin.prod_univ_two]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, tε, Oinvε, Matrix.cons_val]
  module

theorem exists_texp (a : D.toPre.P.A ⟶ D.toPre.P.A) (b : thickObj R I e G ⟶ thickObj R I e G)
    (hb : b ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map a) (n j : ℤ) {Ix : Type}
    {w : Ix → D.toPre.X} (s : ∀ i, SecT D.toPre a n j (w i)) (hs : Small I s) :
    ∃ τ : SecE U b n j, TExp U τ s := by
  classical
  have hb' : b.left ≫ DVR.pGl U e = DVR.pGl U e ≫ a.left := by
    have h₁ : b.left ≫ (U.gt e).q.left = (U.gt e).q.left ≫ ((Over.pullback (thick R I e)).map a).left :=
      congrArg (fun f => f.left) hb
    have h₂ : ((Over.pullback (thick R I e)).map a).left ≫ pullback.fst D.toPre.P.A.hom (thick R I e) =
        pullback.fst D.toPre.P.A.hom (thick R I e) ≫ a.left := pullback.lift_fst _ _ _
    show b.left ≫ (U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R I e) =
      ((U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R I e)) ≫ a.left
    rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]
  choose σ hσ using fun i => exists_sec D.toPre.P.isLB (formEq_term U e a b hb' n j (w i))
    (pullMulSec (s i) (DVR.pGl U e) (DVR.tG U e (w i)) ((U.gt e).t_gen (w i)))
  obtain ⟨τ₀, h₀⟩ := exists_down U.LG.isLB D.toPre.P.isLB (U.w_gen e) (![𝟙 _, b.left] : Fin 2 → _) ![n, j]
    (sumSec (hs e).toFinset σ)
  obtain ⟨τ, hτ⟩ := exists_sec U.LG.isLB (φ' := ![(fstG I e G).left, b.left ≫ (fstG I e G).left]) (ε' := ![n, j])
    (fun V _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      exact congrArg (fun f => h f ^ n * _) (Category.id_comp _)) τ₀
  refine ⟨τ, fun S hS Z x z J J' hJ hJ' => ?_⟩
  have H := h₀ Z x z _ _ (hJ.mem _ x) (hJ'.mem _ x)
  have van : ∀ i, Van I (s i) e → sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val = 0 :=
    fun i hi => by
      have := hi Z (x ≫ (U.gt e).q.left) z J hJ
      rw [Category.assoc] at this
      exact (congrArg (· * _) this).trans (zero_mul _)
  have H₂ : sval (sumSec (hs e).toFinset σ) x z J =
      ∑ i ∈ S, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val := by
    rw [sval_sumSec _ _ x z hJ]
    refine (Finset.sum_congr rfl fun i _ => (hσ i Z x z J hJ).trans (sval_pullMulSec _ _ _ _ x z hJ)).trans ?_
    refine Finset.sum_subset (fun i hi => by_contra fun h => (hs e).mem_toFinset.1 hi (hS i h)) fun i _ hi => ?_
    exact van i (by_contra fun h => hi ((hs e).mem_toFinset.2 h))
  refine Eq.trans ?_ (H.trans H₂)
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) (hτ Z x z J' hJ')
  rw [Fin.prod_univ_two]
  show _ = DVR.wv U e (x ≫ 𝟙 _) z (J (x ≫ 𝟙 _ ≫ _)) (J' (x ≫ 𝟙 _ ≫ _)) ^ n * _
  rw [Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

end Main

theorem glue : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), b ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map a → ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)), Small (maximalIdeal R) s → ∃ τ : SecE U.toUnifPre b n j, TExp U.toUnifPre τ s :=
  fun _ _ _ _ _ _ a _ _ _ _ _ U e b hb n j _ _ s hs => exists_texp U.toUnifPre e a b hb n j s hs

end GlobalTheory.TwFamGlue
