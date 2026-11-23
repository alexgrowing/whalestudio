import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixHt.Uniq

variable {k : Type} [CommRing k]

theorem isometric_of_refines {X : Scheme.{0}} {p : X ⟶ Sp k} {N L : HermLB p} {π : N.B.ι → L.B.ι}
    (h : TwistTop.Refines N L π 0) : N.Isometric L :=
  HermLB.isometric_of_chart π h.le (fun x j j' hj hj' => h.g X (𝟙 X) x j j' hj hj')
    fun σ j y hy => ((h.φ σ j y hy).trans (add_zero _)).symm

theorem card_residueField {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    Nat.card (X.residueField (i z)) = Nat.card (Z.residueField z) := by
  refine Nat.card_eq_of_bijective (i.residueFieldMap z) ⟨(i.residueFieldMap z).hom.injective, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := Z.residue_surjective z a
  obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b
  exact ⟨X.residue _ c, (ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i z) c :)⟩

end GlobalTheory.MixHt.Uniq

open GlobalTheory.MixHt.Uniq in

theorem GlobalTheory.MixHt.eq_of_isMix : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p →
    ∀ (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q) (m m' : ℕ) T T', IsMix p m T → IsMix q m' T' →
    ∀ d : ℕ, d ≤ m → d ≤ m' → ∀ (L : Fin d → HermLB p) (L' : Fin d → HermLB q),
    (∀ a, ((L a).pull i hi).Isometric (L' a)) → ∀ y : Y, HasDim y d → T d L (i y) = T' d L' y := by
  intro k _ X Y p q hp i _ hi m m' T T' hT hT' d
  have hq : IsAmb q := hi ▸ hp.sub i
  have DX := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp
  have DY := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hq
  haveI : IsNoetherian Y := hq.isNoetherian
  induction d with
  | zero =>
    intro _ _ L L' _ y hy
    have hy' : HasDim (i y) 0 := (DX.2.2.2.2.1 Y i y 0).2 hy
    rw [hT.zero L (i y) hy', hT'.zero L' y hy, card_residueField i y]
  | succ e ih =>
    intro hm hm' L L' hL y hy
    have hW : IsAmb (cloι y ≫ q) := hq.sub (cloι y)
    have hgen : HasDim (genericPoint (clo y)) (e + 1) :=
      (DY.2.2.2.2.1 (clo y) (cloι y) (genericPoint (clo y)) (e + 1)).1 (by rw [cloι_genericPoint]; exact hy)
    have hdim : topologicalKrullDim (clo y) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
      (DY.2.2.2.2.2 (clo y) (e + 1)).1 hgen
    obtain ⟨r, hr⟩ := exists_isRatSec ((L' 0).pull (cloι y) rfl).isLB
    have hij : (cloι y ≫ i) ≫ p = cloι y ≫ q := by rw [Category.assoc, hi]
    have hiso : ∀ (A : HermLB p) (A' : HermLB q), (A.pull i hi).Isometric A' →
        (A.pull (cloι y ≫ i) hij).Isometric (A'.pull (cloι y) rfl) := fun A A' h =>
      (isometric_of_refines (HermLB.refines_pull_pull A i hi (cloι y) rfl hij)).symm.trans (h.pull (cloι y) rfl)
    have h1 := hT'.recur (clo y) (cloι y ≫ q) (cloι y) rfl e hm' hdim (L' 0) (Fin.tail L')
      ((L' 0).pull (cloι y) rfl) (fun a => (L' a.succ).pull (cloι y) rfl) (HermLB.Isometric.refl _)
      (fun a => HermLB.Isometric.refl _) r hr
    have h2 := hT.recur (clo y) (cloι y ≫ q) (cloι y ≫ i) hij e hm hdim (L 0) (Fin.tail L)
      ((L' 0).pull (cloι y) rfl) (fun a => (L' a.succ).pull (cloι y) rfl) (hiso _ _ (hL 0))
      (fun a => hiso _ _ (hL a.succ)) r hr
    rw [Fin.cons_self_tail, cloι_genericPoint] at h1
    rw [Fin.cons_self_tail, Scheme.Hom.comp_apply, cloι_genericPoint] at h2
    rw [h1, h2]
    unfold recVal
    congr 1
    refine finsum_congr fun z => ?_
    by_cases hz : ((((L' 0).pull (cloι y) rfl)).div hr).mult z = 0
    · simp [hz]
    · have hz1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hz
      have hzd : HasDim z e := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k (clo y) (cloι y ≫ q) hW e hdim).1 z).1 hz1
      have hjz : HasDim (cloι y z) e := (DY.2.2.2.2.1 (clo y) (cloι y) z e).2 hzd
      dsimp only
      rw [Scheme.Hom.comp_apply, ih (by omega) (by omega) (Fin.tail L) (Fin.tail L') (fun a => hL a.succ) _ hjz]
