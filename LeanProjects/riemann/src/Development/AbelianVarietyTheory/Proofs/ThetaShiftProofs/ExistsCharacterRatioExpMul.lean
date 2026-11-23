import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbelianLetters

theorem exists_ratio_valR {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {ε : K → ℤ} (hL : L.IsLB) {φ φ' : K → (Sp A ⟶ X)} (e : φ = φ') (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε)) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ a : Γ(Sp A, ⊤)ˣ, (∀ z J, Good L z J → val t (𝟙 _) z J = gm (𝟙 _) z ⊤ a * val t' (𝟙 _) z J) ∧
      ∀ j, ⊤ ≤ LB.wchart L φ j → valR (𝟙 (Sp A)) (LB.wchart L φ j) (t.s j).val =
        valR (𝟙 (Sp A)) ⊤ a.val * valR (𝟙 (Sp A)) (LB.wchart L φ' j) (t'.s j).val := by
  subst e
  obtain ⟨a, ha⟩ := TorusCoord.exists_ratio hL (fun _ _ _ => rfl) t ht t' ht'
  refine ⟨a, fun z J hJ => ha _ _ z J hJ, fun j hj => ?_⟩
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL (cpt A)
  apply toStkA_injective
  have hm : (𝟙 (Sp A) : Sp A ⟶ Sp A) (cpt A) ∈ LB.wchart L φ j := hj (x := cpt A) trivial
  rw [map_mul, toStkA_valR _ ⊤ _ le_rfl, toStkA_valR _ (LB.wchart L φ j) _ hj (t.s j),
    toStkA_valR _ (LB.wchart L φ j) _ hj (t'.s j), ← Units.val_mul,
    gen_trans ht _ _ hm (hJ.mem φ _), gen_trans ht' _ _ hm (hJ.mem φ _), mul_left_comm]
  exact congrArg (fun q => Units.val (_ * q)) (ha _ _ _ J hJ)

theorem exists_isRatio_mul [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ)
    (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt)
    (hb : ∀ Tt b, (sB Tt b).b = b ^ n)
    (hadd : ∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b')))
    (hpull : ∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b)))
    (hex : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) :
    ∃ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u ∧ (∀ x z, u x z ≠ 0) ∧
      ∀ x z z', u x (z + z') = u x z * u x z' := by
  have eb : ∀ z, (ex ((n : ℂ) • z)).b = (sB (Out.TF (R := ℂ) ℂ) (ex z).b).b := fun z => by
    rw [b_nsmul hex, hb]
  choose a ha hv using fun x z => exists_ratio_valR (A := ℂ) D.P.isLB
    (φ := Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x)
    (φ' := Out.DegPre.gtφT D (Out.TF (R := ℂ) ℂ) (sB (Out.TF (R := ℂ) ℂ) (ex z).b).b x)
    (by rw [eb]; rfl) ((ex ((n : ℂ) • z)).s x) ((sB (Out.TF (R := ℂ) ℂ) (ex z).b).s x)
    ((ex _).isGen x) ((sB _ _).isGen x)
  have hev : ∀ c : Γ(Sp ℂ, ⊤), valR (𝟙 (Sp ℂ)) ⊤ c = HolHom.evalHom (𝟙 (Sp ℂ)) ⊤ le_rfl c := fun c =>
    HolHom.valR_eq _ _ _ c
  refine ⟨fun x z => valR (𝟙 (Sp ℂ)) ⊤ (a x z).val, fun x z j hj => ?_, fun x z => ?_, fun x z z' => ?_⟩
  · refine (hv x z j hj).trans (congrArg (_ * ·) ?_)
    have H := hpull D.P.A _ (ex z).b (𝟙 _)
    rw [Category.comp_id] at H
    exact valR_of_isPull H x j
  · exact (hev _).trans_ne ((a x z).isUnit.map _).ne_zero
  · have : a x (z + z') = a x z * a x z' := unit_ext fun w _ => by
      obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB w
      have e1 := (val_mul hJ _ _ _).symm.trans
        ((val_corr hJ ((hex ((n : ℂ) • z) ((n : ℂ) • z')).2 x) (𝟙 _)).trans (val_mul hJ _ _ _))
      have e2 := (val_mul hJ _ _ _).symm.trans
        ((val_corr hJ ((hadd _ (ex z).b (ex z').b).2 x) (𝟙 _)).trans (val_mul hJ _ _ _))
      have e3 : val (Out.DegPre.cubAt D ℂ (Out.DegPre.cF D ℂ x) (ex ((n : ℂ) • z)).b (ex ((n : ℂ) • z')).b) (𝟙 _) w J =
          val (Out.DegPre.cubAtT D _ (Out.DegPre.cT D _ x) (sB (Out.TF (R := ℂ) ℂ) (ex z).b).b
            (sB (Out.TF (R := ℂ) ℂ) (ex z').b).b) (𝟙 _) w J := by
        rw [eb, eb]; rfl
      rw [← smul_add] at e1
      rw [← b_add hex] at e2
      have key : ∀ {U : Type} [CommGroup U] {p q r c c' p' q' r' k₁ k₂ k₃ : U}, r * c = p * q → r' * c' = p' * q' →
          c = c' → p = k₁ * p' → q = k₂ * q' → r = k₃ * r' → k₃ = k₁ * k₂ := by
        intro U _ p q r c c' p' q' r' k₁ k₂ k₃ h₁ h₂ h₃ h₄ h₅ h₆
        rw [h₃, h₄, h₅, h₆, _root_.mul_assoc, h₂, _root_.mul_mul_mul_comm] at h₁
        exact mul_right_cancel h₁
      rw [map_mul]
      exact key e1 e2 e3 (ha x z w J hJ) (ha x z' w J hJ) (ha x (z + z') w J hJ)
    simp only [this, hev, Units.val_mul, map_mul]

end GlobalTheory.AbelianLetters
