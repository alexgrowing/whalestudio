import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorMatchComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorMatchIdOneMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsGroupPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.PowChar

theorem isMonHom_of_coords {S : Scheme.{0}} {B C X : Over S} [GrpObj B] [GrpObj C] [GrpObj X]
    (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ C)), ∃! x : T ⟶ B, ∀ a, x ≫ pr a = y a)
    (z : X ⟶ B) (h : ∀ a, IsMonHom (z ≫ pr a)) : IsMonHom z := by
  refine GlobalTheory.GrpPullPow.isMonHom_of_mul_pts z fun T x y => ?_
  refine (huniv T (fun a => (x * y) ≫ z ≫ pr a)).unique (fun a => Category.assoc _ _ _) (fun a => ?_)
  haveI := hpr a
  haveI := h a
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, ← MonObj.mul_comp]

theorem isMonHom_one {S : Scheme.{0}} {B C : Over S} [GrpObj B] [GrpObj C] : IsMonHom (1 : B ⟶ C) :=
  inferInstanceAs (IsMonHom (toUnit B ≫ η[C]))

theorem exists_incl {S : Scheme.{0}} {B C : Over S} [GrpObj B] [GrpObj C]
    (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ C)), ∃! x : T ⟶ B, ∀ a, x ≫ pr a = y a) :
    ∃ z : Fin 8 → (C ⟶ B), (∀ u, IsMonHom (z u)) ∧ ∀ u v, z u ≫ pr v = if v = u then 𝟙 C else 1 := by
  choose z hz _ using fun u : Fin 8 => huniv C (fun v => if v = u then 𝟙 C else 1)
  refine ⟨z, fun u => isMonHom_of_coords pr hpr huniv (z u) fun a => ?_, hz⟩
  rw [hz u a]
  split_ifs
  · infer_instance
  · exact isMonHom_one

end GlobalTheory.Poinc.Eq8.PowChar

namespace GlobalTheory.Poinc.Eq8.PowChar

theorem isMonHom_prod {S : Scheme.{0}} {X M : Over S} [GrpObj X] [GrpObj M] [IsCommMonObj M] {J : Type}
    (f : J → (X ⟶ M)) (hf : ∀ i, IsMonHom (f i)) (s : Finset J) : IsMonHom (∏ i ∈ s, f i) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty]; exact isMonHom_one
  · intro a s ha ih
    rw [Finset.prod_insert ha]
    haveI := hf a
    exact inferInstanceAs (IsMonHom (lift (f a) (∏ i ∈ s, f i) ≫ μ[M]))

theorem prod_comp {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] [IsCommMonObj M] [IsCommMonObj N] {J : Type}
    (f : J → (X ⟶ M)) (s : Finset J) (g : M ⟶ N) [IsMonHom g] : (∏ i ∈ s, f i) ≫ g = ∏ i ∈ s, f i ≫ g := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty, MonObj.one_comp]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

end GlobalTheory.Poinc.Eq8.PowChar

namespace GlobalTheory.Poinc.Eq8

open PowChar in

theorem characters_eighthPower_elementaryMatrices : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → (Function.Bijective fun y : Fin 8 → D.toPre.X => ∑ v, c v (y v)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ w x, m (c w x) = if w = a then c b x else 0 := by
  intro R _ _ _ hR hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W _ pr hpr huniv _ pG hpG hgen c hc
  haveI := hdvr
  haveI := U.gen_hom
  haveI := U'.gen_hom
  have ext : ∀ {H H' : Over (Sp R)} [GrpObj H] [GrpObj H'], IsSemiAbelian H → IsSemiAbelian H' →
      ∀ (F₁ F₂ : H ⟶ H'), IsMonHom F₁ → IsMonHom F₂ →
        (Over.pullback (jK R)).map F₁ = (Over.pullback (jK R)).map F₂ → F₁ = F₂ := by
    intro H H' _ _ h h' F₁ F₂ h₁ h₂ e
    exact (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) H H' h h' _ inferInstance).unique
      ⟨h₁, e⟩ ⟨h₂, rfl⟩
  obtain ⟨z, hzm, hz⟩ := exists_incl pr hpr huniv
  have hic : ∀ u, ∃ ic : G ⟶ G', IsMonHom ic ∧ (Over.pullback (jK R)).map ic = U.gen.hom ≫ z u ≫ U'.gen.inv := by
    intro u
    haveI := hzm u
    obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) G G' hG hG'
      (U.gen.hom ≫ z u ≫ U'.gen.inv) inferInstance
    exact ⟨F, hF, hF'⟩
  choose ic hicm hicg using hic
  have hicp : ∀ u v, ic u ≫ pG v = if v = u then 𝟙 G else 1 := by
    intro u v
    haveI := hicm u
    haveI := hpG v
    have key : (Over.pullback (jK R)).map (ic u ≫ pG v) ≫ U.gen.hom = U.gen.hom ≫ (if v = u then 𝟙 A.A else 1) := by
      rw [Functor.map_comp, Category.assoc, hgen v, ← Category.assoc, hicg u]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, hz u v]
    by_cases h : v = u
    · rw [if_pos h] at key ⊢
      refine ext hG hG _ _ inferInstance inferInstance ?_
      rw [← cancel_mono U.gen.hom, key, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · rw [if_neg h] at key ⊢
      refine ext hG hG _ _ inferInstance isMonHom_one ?_
      rw [← cancel_mono U.gen.hom, key, Functor.map_one, MonObj.comp_one, MonObj.one_comp]
  have hpw : ∀ w, (∏ v, pG v ≫ ic v) ≫ pG w = pG w := by
    intro w
    haveI := hpG w
    rw [PowChar.prod_comp, Finset.prod_eq_single w]
    · rw [Category.assoc, hicp w w, if_pos rfl, Category.comp_id]
    · intro v _ hv
      rw [Category.assoc, hicp v w, if_neg (Ne.symm hv), MonObj.comp_one]
    · intro h
      exact absurd (Finset.mem_univ w) h
  have hprod : (∏ v, pG v ≫ ic v) = 𝟙 G' := by
    have hm : IsMonHom (∏ v, pG v ≫ ic v) :=
      isMonHom_prod _ (fun v => by haveI := hpG v; haveI := hicm v; infer_instance) _
    refine ext hG' hG' _ _ hm inferInstance ?_
    rw [CategoryTheory.Functor.map_id, ← cancel_mono U'.gen.hom, Category.id_comp]
    refine (huniv _ (fun w => U'.gen.hom ≫ pr w)).unique (fun w => ?_) (fun w => rfl)
    rw [Category.assoc, ← hgen w, ← Category.assoc, ← Functor.map_comp, hpw w]
  have hinj : Function.Injective (RingHom.id R) := Function.injective_id
  have hk : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : R) := fun _ h => h
  choose d hd using fun u => GlobalTheory.Poinc.HomTor.exists_torMatch R hR G' hG' D' A' U' G hG D A U (ic u) (hicm u)
  obtain ⟨hid, hone, -⟩ := torMatch_id_one_mul R hR G hG D A U G hG D A U
  obtain ⟨hid', hone', hmul'⟩ := torMatch_id_one_mul R hR G' hG' D' A' U' G' hG' D' A' U'
  obtain ⟨-, hone'', -⟩ := torMatch_id_one_mul R hR G hG D A U G' hG' D' A' U'
  have hdc : ∀ u v, (d u).comp (c v) = if v = u then AddMonoidHom.id _ else 0 := by
    intro u v
    have h1 := torMatch_comp R hR G hG D A U R hR G' hG' D' A' U' (RingHom.id R) (pG v).left R hR G hG D A U
      (RingHom.id R) (ic u).left hinj hk (c v) (d u) (hc v) (hd u)
    rw [← Over.comp_left, hicp u v, RingHom.id_comp] at h1
    by_cases h : v = u
    · rw [if_pos h] at h1 ⊢
      rw [Over.id_left] at h1
      exact torMatch_unique R hR G hG D A U R hR G hG D A U _ _ hinj _ _ h1 hid
    · rw [if_neg h] at h1 ⊢
      exact torMatch_unique R hR G hG D A U R hR G hG D A U _ _ hinj _ _ h1 hone
  have hcd : ∑ v, (c v).comp (d v) = AddMonoidHom.id _ := by
    have hs : ∀ s : Finset (Fin 8), TorMatch U' U' (RingHom.id R) (∏ v ∈ s, pG v ≫ ic v).left
        (∑ v ∈ s, (c v).comp (d v)) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · rw [Finset.prod_empty, Finset.sum_empty]
        exact hone'
      · intro a s ha ih
        rw [Finset.prod_insert ha, Finset.sum_insert ha]
        have h1 := torMatch_comp R hR G' hG' D' A' U' R hR G hG D A U (RingHom.id R) (ic a).left R hR G' hG' D' A' U'
          (RingHom.id R) (pG a).left hinj hk (d a) (c a) (hd a) (hc a)
        rw [← Over.comp_left, RingHom.id_comp] at h1
        exact hmul' _ _ _ _ h1 ih
    have h2 := hs Finset.univ
    rw [hprod, Over.id_left] at h2
    exact torMatch_unique R hR G' hG' D' A' U' R hR G' hG' D' A' U' _ _ hinj _ _ h2 hid'
  refine ⟨?_, ?_⟩
  · rw [Function.bijective_iff_has_inverse]
    refine ⟨fun x u => d u x, fun y => ?_, fun x => ?_⟩
    · funext u
      have e : ∀ v, d u (c v (y v)) = if v = u then y v else 0 := fun v => by
        have := DFunLike.congr_fun (hdc u v) (y v)
        rw [AddMonoidHom.comp_apply] at this
        rw [this]
        split_ifs <;> rfl
      simp only [map_sum, e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · have := DFunLike.congr_fun hcd x
      simpa [AddMonoidHom.finset_sum_apply] using this
  · intro a b f f₁ m hf hf₁ hff₁ hm w x
    haveI := hf
    haveI := hpG w
    have hfp : f ≫ pG w = if w = a then pG b else 1 := by
      have key : (Over.pullback (jK R)).map (f ≫ pG w) ≫ U.gen.hom = U'.gen.hom ≫ (if w = a then pr b else 1) := by
        rw [Functor.map_comp, Category.assoc, hgen w, ← Category.assoc, hff₁, Category.assoc, hf₁.2 w]
      by_cases h : w = a
      · rw [if_pos h] at key ⊢
        refine ext hG' hG _ _ inferInstance (hpG b) ?_
        rw [← cancel_mono U.gen.hom, key, hgen b]
      · rw [if_neg h] at key ⊢
        refine ext hG' hG _ _ inferInstance isMonHom_one ?_
        rw [← cancel_mono U.gen.hom, key, Functor.map_one, MonObj.comp_one, MonObj.one_comp]
    have h1 := torMatch_comp R hR G hG D A U R hR G' hG' D' A' U' (RingHom.id R) (pG w).left R hR G' hG' D' A' U'
      (RingHom.id R) f.left hinj hk (c w) m (hc w) (GlobalTheory.Poinc.TorEnd.torMatch_of_endChar R hR G' hG' D' A' U' f hf m hm)
    rw [← Over.comp_left, hfp, RingHom.id_comp] at h1
    have e : m.comp (c w) = if w = a then c b else 0 := by
      by_cases h : w = a
      · rw [if_pos h] at h1 ⊢
        exact torMatch_unique R hR G hG D A U R hR G' hG' D' A' U' _ _ hinj _ _ h1 (hc b)
      · rw [if_neg h] at h1 ⊢
        exact torMatch_unique R hR G hG D A U R hR G' hG' D' A' U' _ _ hinj _ _ h1 hone''
    have := DFunLike.congr_fun e x
    rw [AddMonoidHom.comp_apply] at this
    rw [this]
    split_ifs <;> rfl

end GlobalTheory.Poinc.Eq8
