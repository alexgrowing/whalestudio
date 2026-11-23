import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.MemFinsetInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZeroOfIsAffineOpen

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.MixedCross

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cross_pow {Γ : Type} [CommRing Γ] (W W' X : Γˣ) {k₁ k₂ m₁ m₂ N : ℕ} (hm : m₁ * k₁ = m₂ * k₂)
    (s₁ t₁ s₂ t₂ : Γ)
    (h₁ : (W ^ (k₁ * N)).val * s₁ = (X ^ k₁).val * ((W' ^ k₁).val * t₁))
    (h₂ : (W ^ (k₂ * N)).val * s₂ = (X ^ k₂).val * ((W' ^ k₂).val * t₂)) :
    s₁ ^ m₁ * t₂ ^ m₂ = s₂ ^ m₂ * t₁ ^ m₁ := by
  push_cast at h₁ h₂
  have e₁ := congrArg (· ^ m₁) h₁
  have e₂ := congrArg (· ^ m₂) h₂
  simp only [mul_pow, ← pow_mul] at e₁ e₂
  have a₁ : k₁ * N * m₁ = m₁ * k₁ * N := by ring
  have a₂ : k₂ * N * m₂ = m₁ * k₁ * N := by rw [hm]; ring
  have b₁ : k₁ * m₁ = m₁ * k₁ := by ring
  have b₂ : k₂ * m₂ = m₁ * k₁ := by rw [hm]; ring
  rw [a₁, b₁] at e₁
  rw [a₂, b₂] at e₂
  have hu : IsUnit ((W : Γ) ^ (m₁ * k₁ * N)) := W.isUnit.pow _
  apply hu.mul_left_cancel
  calc (W : Γ) ^ (m₁ * k₁ * N) * (s₁ ^ m₁ * t₂ ^ m₂)
      = ((W : Γ) ^ (m₁ * k₁ * N) * s₁ ^ m₁) * t₂ ^ m₂ := by ring
    _ = (X : Γ) ^ (m₁ * k₁) * ((W' : Γ) ^ (m₁ * k₁) * t₁ ^ m₁) * t₂ ^ m₂ := by rw [e₁]
    _ = ((W : Γ) ^ (m₁ * k₁ * N) * s₂ ^ m₂) * t₁ ^ m₁ := by rw [e₂]; ring
    _ = (W : Γ) ^ (m₁ * k₁ * N) * (s₂ ^ m₂ * t₁ ^ m₁) := by ring

theorem gs_sub' {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a b : Γ(X, U)) :
    gs r z U (a - b) = gs r z U a - gs r z U b := by
  simp only [gs, dif_pos h, map_sub]

theorem sec_eq_of_thick (hB : lemmaBSt.{0}) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (G.left ⟶ Y)} {ε : K → ℤ}
    (s s' : LB.Sec (LB.LinComb L φ ε))
    (h : ∀ (e : ℕ) (z : (thickObj V (maximalIdeal V) e G).left) (J), Good L z J →
      sval s (fGl (maximalIdeal V) G e) z J = sval s' (fGl (maximalIdeal V) G e) z J) (j : K → L.ι) :
    s.f j = s'.f j := by
  classical
  unfold sval fGl at h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hN : (LB.LinComb L φ ε).IsLB := linComb_isLB L hL φ ε
  refine sub_eq_zero.mp (hB V G (LB.LinComb L φ ε) hN (subSec s s') ϖ hϖ (fun i e => ?_) j)
  cases e with
  | zero => simp
  | succ e =>
    have hv : ∀ i', ((fstG (maximalIdeal V) e G).left.app ((LB.LinComb L φ ε).U i')).hom
        ((subSec s s').f i') = 0 := by
      intro i'
      apply fn_ext
      intro z hz
      have hz' : (fstG (maximalIdeal V) e G).left z ∈ LB.wchart L φ i' := hz
      obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)
      have hm := hJ.mem φ (fstG (maximalIdeal V) e G).left
      have h1 := h e z J hJ
      rw [gs_eq (𝟙 _) z _ hz 0, map_zero, map_zero, gs_pull (𝟙 _) _ z ((LB.LinComb L φ ε).U i') hz', Category.id_comp]
      show gs (fstG (maximalIdeal V) e G).left z (LB.wchart L φ i') (s.f i' - s'.f i') = 0
      refine (gs_sub' _ z (LB.wchart L φ i') hz' (s.f i') (s'.f i')).trans (sub_eq_zero.mpr ?_)
      rw [sec_trans s _ z hz' hm, sec_trans s' _ z hz' hm, h1]
    obtain ⟨τ, hτ⟩ := (GlobalTheory.ThickDiv.main V ϖ hϖ G (LB.LinComb L φ ε) (subSec s s') e).1 hv
    unfold SecIsMul at hτ
    rw [hτ i]
    refine Ideal.mul_mem_right _ _ ?_
    have hc : resTop ((LB.LinComb L φ ε).U i) (scal G.hom (ϖ ^ (e + 1))) =
        ((G.left.presheaf.map (homOfLE le_top).op).hom
          ((G.hom.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ϖ))) ^ (e + 1) := by
      simp only [resTop, scal, map_pow]
      rfl
    rw [hc]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _

theorem main : lemmaBSt.{0} → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (k₁ k₂ m₁ m₂ : ℕ), m₁ * k₁ = m₂ * k₂ → ∀ (σ₁ : H0 P.U.LG.L (k₁ * N)) (τ₁ : H0 P.U.LG.L k₁) (σ₂ : H0 P.U.LG.L (k₂ * N)) (τ₂ : H0 P.U.LG.L k₂), (∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k₁ * N)).val * sv P.U.toUnifPre (k₁ * N) σ₁ (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k₁).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k₁).val * sv P.U.toUnifPre k₁ τ₁ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL'))) → (∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k₂ * N)).val * sv P.U.toUnifPre (k₂ * N) σ₂ (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k₂).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k₂).val * sv P.U.toUnifPre k₂ τ₂ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (y : Z) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval σ₁ r y J ^ m₁ * Geo.Tor.sval τ₂ (r ≫ (t.act.act a).left) y J ^ m₂ = Geo.Tor.sval σ₂ r y J ^ m₂ * Geo.Tor.sval τ₁ (r ≫ (t.act.act a).left) y J ^ m₁ := by
  intro hB V _ _ _ E _ _ _ H t P a N haN hN X k₁ k₂ m₁ m₂ hm σ₁ τ₁ σ₂ τ₂ h₁ h₂
  classical
  have : Smooth t.G.hom := t.semi.smooth
  have : IsSeparated t.G.hom := t.semi.separated
  have : QuasiCompact t.G.hom := t.semi.quasiCompact
  have : GeometricallyConnected t.G.hom := t.semi.geomConnected
  have hL : P.U.LG.L.IsLB := P.U.LG.isLB
  have hD : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  have eA : ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (y : Z) (J : (Z ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L y J →
      sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => σ₁)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => τ₂)) (t.act.act a).left)) r y J = sval σ₁ r y J ^ m₁ * sval τ₂ (r ≫ (t.act.act a).left) y J ^ m₂ := by
    intro Z r y J hJ
    rw [H1.SectionArithmetic.sval_mulSec _ _ r y hJ, H1.SectionArithmetic.sval_pullSec _ _ r y hJ, H1.SectionArithmetic.sval_powSec _ r y hJ,
      H1.SectionArithmetic.sval_powSec _ _ y hJ]
    simp [Finset.prod_const]
  have eB : ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (y : Z) (J : (Z ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L y J →
      sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => σ₂)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => τ₁)) (t.act.act a).left)) r y J = sval σ₂ r y J ^ m₂ * sval τ₁ (r ≫ (t.act.act a).left) y J ^ m₁ := by
    intro Z r y J hJ
    rw [H1.SectionArithmetic.sval_mulSec _ _ r y hJ, H1.SectionArithmetic.sval_pullSec _ _ r y hJ, H1.SectionArithmetic.sval_powSec _ r y hJ,
      H1.SectionArithmetic.sval_powSec _ _ y hJ]
    simp [Finset.prod_const]
  obtain ⟨B', hB'⟩ : ∃ B' : type_of% (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => σ₁)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => τ₂)) (t.act.act a).left)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (J : (Z ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L z J →
        sval B' r z J = sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => σ₂)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => τ₁)) (t.act.act a).left)) r z J := by
    refine exists_sec hL ?_ _
    intro U _ h
    simp only [Fintype.prod_sum_type, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Sum.elim_inl, Sum.elim_inr, Category.comp_id]
    have hz : (m₁ : ℤ) * k₁ = m₂ * k₂ := by exact_mod_cast hm
    simp only [← zpow_natCast, ← zpow_mul]
    congr 2
    · push_cast
      linear_combination (-(N : ℤ)) * hz
    · push_cast
      linear_combination hz
  have hthick : ∀ (e : ℕ) (z : (thickObj V (maximalIdeal V) e t.G).left)
      (J : ((thickObj V (maximalIdeal V) e t.G).left ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L z J →
      sval (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.powSec (fun _ : Fin m₁ => σ₁)) (H1.SectionArithmetic.pullSec (H1.SectionArithmetic.powSec (fun _ : Fin m₂ => τ₂)) (t.act.act a).left)) (fGl (maximalIdeal V) t.G e) z J = sval B' (fGl (maximalIdeal V) t.G e) z J := by
    intro e z J hJ
    rw [hB' _ _ z J hJ, eA _ _ z J hJ, eB _ _ z J hJ]
    obtain ⟨JD, hJD, -⟩ := exists_good P.D.toPre.P.L hD z (K := Empty) Empty.elim Empty.elim
      (fun a => a.elim) (fun a => a.elim)
    have m1 : (𝟙 _ ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U (J (fGl (maximalIdeal V) t.G e ≫ 𝟙 t.G.left)) := by
      simpa using hJ (fGl (maximalIdeal V) t.G e ≫ 𝟙 t.G.left)
    have m2 : ((𝟙 _ ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫
        fGl (maximalIdeal V) t.G e) z ∈
          P.U.LG.L.U (J ((fGl (maximalIdeal V) t.G e ≫ (t.act.act a).left) ≫ 𝟙 t.G.left)) := by
      have hz := hJ ((fGl (maximalIdeal V) t.G e ≫ (t.act.act a).left) ≫ 𝟙 t.G.left)
      have eq : (𝟙 _ ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫
          fGl (maximalIdeal V) t.G e = (fGl (maximalIdeal V) t.G e ≫ (t.act.act a).left) ≫ 𝟙 t.G.left := by
        rw [Category.id_comp, Category.comp_id]
        exact fstG_act _ _ _
      rw [eq]
      exact hz
    have c := cross_pow _ _ _ hm _ _ _ _ (h₁ e _ (𝟙 _) z JD hJD _ _ m1 m2) (h₂ e _ (𝟙 _) z JD hJD _ _ m1 m2)
    unfold sv at c
    simp only [Category.id_comp, fGl, fstG_act] at c
    unfold sval
    simp only [fGl]
    exact c
  intro Z r y J hJ
  rw [← eA Z r y J hJ, ← eB Z r y J hJ, ← hB' Z r y J hJ]
  have hAB := sec_eq_of_thick hB t.G hL _ B' hthick
  unfold sval
  rw [hAB]

end GlobalTheory.MixedCross
