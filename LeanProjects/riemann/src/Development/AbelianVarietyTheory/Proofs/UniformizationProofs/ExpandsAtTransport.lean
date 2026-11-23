import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ExpTrans

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

section Generic

variable {X X' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

def om (w : LB.Iso L' (L.pull F)) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (ψ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ := gw w ψ z (J (ψ ≫ F)) (J' ψ)

variable (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} (φ' : K → (Y' ⟶ X'))
  (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)

theorem sec_val (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L' φ' ε))
    (r : Z ⟶ Y') (z : Z)
    (H : ∀ (p : K → L.ι) (q : K → L'.ι), (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
        (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (s'.f q))
    {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    sval s (r ≫ h) z J = (∏ κ, om w z J J' (r ≫ φ' κ) ^ ε κ).val * sval s' r z J' := by
  rw [sval_of s (r ≫ h) z J (fun κ => J ((r ≫ φ' κ) ≫ F))
    (fun κ => by rw [Category.assoc, Category.assoc, hc])]
  exact H _ (fun κ => J' (r ≫ φ' κ)) (fun κ => hJ ((r ≫ φ' κ) ≫ F)) (fun κ => hJ' (r ≫ φ' κ))

theorem gen_val (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L' φ' ε))
    (H : PMaps w φ' φ ε t' t h) (z : Y') {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t h z J = (∏ κ, om w z J J' (φ' κ) ^ ε κ) * val t' (𝟙 _) z J' := by
  have := H _ (𝟙 _) z (fun κ => J (φ' κ ≫ F)) (fun κ => J' (φ' κ)) (fun κ => hJ (φ' κ ≫ F)) (fun κ => hJ' (φ' κ))
  simp only [Category.id_comp] at this
  rw [val_of t h z J (fun κ => J (φ' κ ≫ F)) (fun κ => by rw [hc]),
    val_of t' (𝟙 _) z J' (fun κ => J' (φ' κ)) (fun κ => by rw [Category.id_comp])]
  exact this

end Generic

theorem prod_fam {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
    {M : Type} [CommGroup M] (ω : ((thickObj R I e G).left ⟶ D.toPre.P.A.left) → M) (α : D.toPre.X) :
    (∏ a, ω (pGl U e ≫ D.toPre.famφB α a) ^ DegPre.famε k a) * ∏ a, ω (Oφl U e α a) ^ Oinvε a =
      ω (pGl U e) ^ k := by
  have a₀ : pGl U e ≫ D.toPre.famφB α 0 = pGl U e := Category.comp_id _
  have a₁ : pGl U e ≫ D.toPre.famφB α 1 = Oφl U e α 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U.gt e).pG (𝟙 _) (cP D.toPre _ α)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D.toPre _ α)))
  have a₂ : pGl U e ≫ D.toPre.famφB α 2 = Oφl U e α 1 :=
    congrArg (fun z => z.left) (comp_cP D.toPre (U.gt e).pG α)
  have a₃ : pGl U e ≫ D.toPre.famφB α 3 = Oφl U e α 3 :=
    congrArg (fun z : _ ⟶ D.toPre.P.A => z.left) (MonObj.comp_one (M := D.toPre.P.A) (U.gt e).pG)
  have a₄ : Oφl U e α 2 = pGl U e := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module

end GlobalTheory.ExpTrans

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans in
set_option maxHeartbeats 1600000 in

theorem expandsAt_transport : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (D : DegData R I) (D' : DegData R' I') (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I' D' A' G') (Φ : D'.toPre.P.A.left ⟶ D.toPre.P.A.left) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ)) (xe : D'.toPre.X ≃+ D.toPre.X) (Ψ : G'.left ⟶ G.left) (wL : LB.Iso U'.LG.L (U.LG.L.pull Ψ)), w.IsGen → wL.IsGen → (∀ x κ, D'.toPre.famφB x κ ≫ Φ = Φ ≫ D.toPre.famφB (xe x) κ) → ∀ (e e' k : ℕ) (h : (thickObj R' I' e' G').left ⟶ (thickObj R I e G).left), (h ≫ (fstG I e G).left = (fstG I' e' G').left ≫ Ψ ∧ ((U'.gt e').pG.left ≫ Φ = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e').pG x κ ≫ Φ = h ≫ D.toPre.Oφ (U.gt e).pG (xe x) κ) ∧ Geo.Tor.PMaps w (D'.toPre.Oφ (U'.gt e').pG x) (D.toPre.Oφ (U.gt e).pG (xe x)) Oinvε ((U'.gt e').t x) ((U.gt e).t (xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e' G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (Φ) ((U'.gt e').pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e').pG.left (r z) ∈ D'.toPre.P.L.U jM' → (Ψ) ((fstG I' e' G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e' G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e').pG.left) z jM jM' * Geo.Tor.gw (U'.w e') r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e' G').left) z jL jL')) → ∀ (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (σ' : LB.Sec (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G'.left) (fun _ => (k : ℤ)))) (f : ∀ α, D.toPre.SecB k α) (f' : ∀ α, D'.toPre.SecB k α), (∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (p : Fin 1 → U.LG.L.ι) (q : Fin 1 → U'.LG.L.ι), (∀ κ, (Ψ) ((fun _ : Fin 1 => 𝟙 G'.left) κ (r z)) ∈ U.LG.L.U (p κ)) → (∀ κ, (fun _ : Fin 1 => 𝟙 G'.left) κ (r z) ∈ U'.LG.L.U (q κ)) → Geo.Tor.gs (r ≫ Ψ) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) p) ((σ).f p) = (∏ κ, Geo.Tor.gw wL (r ≫ (fun _ : Fin 1 => 𝟙 G'.left) κ) z (p κ) (q κ) ^ (fun _ : Fin 1 => (k : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) q) ((σ').f q)) → (∀ x : D'.toPre.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.toPre.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.toPre.P.L.ι), (∀ κ, (Φ) ((D'.toPre.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.toPre.famφB x) κ (r z) ∈ D'.toPre.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Φ) z (LB.wchart D.toPre.P.L (D.toPre.famφB (xe x)) p) ((f (xe x)).f p) = (∏ κ, Geo.Tor.gw w (r ≫ (D'.toPre.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.toPre.P.L (D'.toPre.famφB x) q) ((f' x).f q))) → U.ExpandsAt e k σ f → U'.ExpandsAt e' k σ' f' := by
  intro R R' _ _ _ _ I I' D D' A A' G _ _ G' _ _ U U' Φ w xe Ψ wL _ _ hφ e e' k h ⟨hG, ⟨hq, hO⟩, hW⟩ σ σ' f f' hσ hf hE
  classical
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f hE
  refine expandsAt_of_val U' e' k σ' f' (S.map xe.symm.toEquiv.toEmbedding) fun y J' hJ' => ?_
  choose J hJ using fun ψ : (thickObj R' I' e' G').left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have hq : pGl U' e' ≫ Φ = h ≫ pGl U e := hq
  have hG : h ≫ fGl I G e = fGl I' G' e' ≫ Ψ := hG
  have hF : ∀ α', sval (f (xe α')) (h ≫ pGl U e) y J =
      (∏ a, om w y J J' (pGl U' e' ≫ D'.toPre.famφB α' a) ^ DegPre.famε k a).val * sval (f' α') (pGl U' e') y J' := by
    intro α'
    rw [← hq]
    exact sec_val w _ _ _ Φ (hφ α') (f (xe α')) (f' α') (pGl U' e') y (hf α' _ (pGl U' e') y) hJ hJ'
  have hT : ∀ α', val (tG U e (xe α')) h y J =
      (∏ a, om w y J J' (Oφl U' e' α' a) ^ Oinvε a) * val (tG U' e' α') (𝟙 _) y J' := fun α' =>
    gen_val w (Oφl U' e' α') (Oφl U e (xe α')) Oinvε h (hO α').1 (tG U e (xe α')) (tG U' e' α') (hO α').2 y hJ hJ'
  have hω := prod_fam U' e' k (om w y J J')
  refine ⟨fun α' hα => ?_, fun jL' hL' => ?_⟩
  · have hi : xe α' ∉ S := fun hc => hα (Finset.mem_map.2 ⟨xe α', hc, xe.symm_apply_apply α'⟩)
    exact (Units.mul_right_eq_zero _).1 ((hF α').symm.trans ((hS _ h y J hJ).1 _ hi))
  · obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB (Ψ (fGl I' G' e' y))
    have hL₁ : fGl I G e (h y) ∈ U.LG.L.U jL := (congrArg (fun g => g y ∈ U.LG.L.U jL) hG).mpr hL
    have W' : om w y J J' (pGl U' e') * wv U' e' (𝟙 _) y (J' (pGl U' e')) jL' =
        wv U e h y (J (h ≫ pGl U e)) jL * gw wL (fGl I' G' e') y jL jL' := by
      have := hW _ (𝟙 _) y (J (pGl U' e' ≫ Φ)) (J' (pGl U' e')) jL jL' (hJ (pGl U' e' ≫ Φ)) (hJ' (pGl U' e')) hL hL'
      simp only [Category.id_comp] at this
      rw [← hq]
      exact this
    have Sg : sv U k σ (h ≫ fGl I G e) y jL =
        (gw wL (fGl I' G' e') y jL jL' ^ k).val * sv U' k σ' (fGl I' G' e') y jL' := by
      have := hσ _ (fGl I' G' e') y (fun _ => jL) (fun _ => jL') (fun _ => hL) (fun _ => hL')
      simp only [Category.comp_id, Fin.prod_univ_one, zpow_natCast] at this
      rw [hG]
      exact this
    refine (om w y J J' (pGl U' e') ^ k).mul_right_inj.1 ?_
    rw [← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, W', mul_pow, Units.val_mul, _root_.mul_assoc, ← Sg,
      (hS _ h y J hJ).2 jL hL₁, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    obtain ⟨α', rfl⟩ := xe.surjective x
    have e₀ : xe.symm.toEquiv.toEmbedding (xe α') = α' := xe.symm_apply_apply α'
    rw [e₀, hF α', hT α', ← hω α', Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm]

end GlobalTheory
