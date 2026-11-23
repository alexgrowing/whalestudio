import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionCoordinatesEqDegenerationSeries
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HvHolds
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.MBLow
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefBasic GlobalTheory.UT.SymFrame GlobalTheory.Ex.GtValues GlobalTheory.Ex.CoordSeries

theorem symTranslate_expandsF : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1) (c : C), U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → ∀ m : ℕ, Odd m → ∀ (p : QkPt D.toPre C (m ^ 2)) (q : N.QT (m ^ 2)) (z : TFK (R := V) C ⟶ A.A), ν.QPt p q → QkToAkU U.toUnifPre C (m ^ 2) p z → ∃ (Θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := V) C)) (t : GlobalTheory.UT.SecA A C (m ^ 2)) (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C), SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) z Θ ∧ Tr A ρ m th Θ t ∧ U.ExpandsF C (m ^ 2) w₀ t s ∧ IsEvFam N m q f ∧ ν.FamV s (c • f) := by
  intro V _ _ _ _ hcpl D A G _ _ hG U C _ _ _ _ _ _ hC N ν _ w₀ ρ hN th ϑ c hth hϑ m hm p q z hq hz
  have hL : GlobalTheory.UT.LL := GlobalTheory.Ex.hv_holds.1
  have hfam : BrFamSt := GlobalTheory.Ex.brFam hL.1 hL.2.1
  have hB : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  have hLB := A.isLB
  let y : Sp C := IsLocalRing.closedPoint C

  have hgt : ∀ b : N.A, ∃ h : N.Gt, h.b = b := fun b => by
    obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_lift (D := D.toPre) (F := C) (ν.eA b)
    obtain ⟨h, hh⟩ := GtValues.exists_val ν g
    exact ⟨h, ν.eA.injective (hh.1.trans hg)⟩
  have main : ∀ (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1) (c : C), U.ExpandsF C 1 w₀ th ϑ →
      ν.FamV ϑ (c • N.vth) → ∃ (Θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := V) C)) (t : GlobalTheory.UT.SecA A C (m ^ 2))
        (s : Fam D.toPre C (m ^ 2)) (f : N.X → N.A → C),
        SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) z Θ ∧ Tr A ρ m th Θ t ∧ U.ExpandsF C (m ^ 2) w₀ t s ∧ ν.FamV s f ∧
        (∀ (h : N.Gt) (χ : N.X), f (q.1.1.toAdd + m • χ) h.b * h.s (q.1.1.toAdd + m • χ) = c * N.evT m q h χ) ∧
        ∀ β, (∀ χ, β ≠ q.1.1.toAdd + m • χ) → ∀ x, f β x = 0 := by
    intro th ϑ c hth hϑ
    obtain ⟨⟨_, _⟩, ⟨α, s₁, -, hα, hαn, hs₁, -⟩, -⟩ :=
      GlobalTheory.existsUnique_thetaConst hL V A C ρ hN.2.1 m hm th 1 (one_pow _)
    have hbij := (expBijF_and_expandsF_lin hL V _ hB D A G hG U).1 C (m ^ 2) hm2 w₀ hN.1
    obtain ⟨σ₁, hσ₁, -⟩ := hbij.1 s₁
    obtain ⟨hv₁, -, -, -, -, hv₂⟩ := hfam V D.toPre D.psi_even D.tau_bimult C N ν (m ^ 2) hm2
    obtain ⟨f₁, hf₁, -⟩ := hv₁ σ₁
    obtain ⟨E, hEG, hEA, hEB, hEh, hEact⟩ := (IntEnd.exists_nsmul_and_neg hL V _ hB D A G hG U).1 m
    have hsm : ∀ {X : Type} [AddCommGroup X] [Module.Free ℤ X], Function.Injective fun χ : X => m • χ := by
      intro X _ _ a b h
      have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using h
      exact smul_right_injective _ (Int.natCast_ne_zero.2 hm0) h'
    have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
    have hpull := (PullExp.main hL V _ hB D A G hG U C E hinj (m ^ 2) 1 le_rfl hm2
      (exists_gen_pow U.LG U.cubG U.symG U.symG_gen m E.aG hEG)).2 w₀ ρ hN (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _)
      (lift_fst _ _) (by rw [hEA, MonObj.comp_pow, Category.comp_id]) α hα hαn th s₁ ϑ σ₁ hth hσ₁ hs₁
    rw [hEB] at hpull
    obtain ⟨κ, hκ⟩ := exists_kap (D := D.toPre) hL.1.mulPull m
    have pull : ∀ h : N.Gt, (∀ χ, f₁ (m • χ) h.b * h.s (m • χ) =
        c * N.vt (h ^ m) χ * ((mulq N.θ N.σ m h.b)⁻¹ : Cˣ)) ∧ ∀ β, (∀ χ, β ≠ m • χ) → f₁ β h.b = 0 := fun h => by
      obtain ⟨g, hg⟩ := GtValues.exists_pt ν h
      obtain ⟨g', hg'⟩ := GtValues.exists_pt ν (h ^ m)
      have act := (hEact C g g').2 ((isNsmul_val ν m hg hg').2 rfl)
      obtain ⟨W, hW⟩ := (coef_basic V D.toPre C (m ^ 2) g).1
      obtain ⟨w, hw, hwv⟩ := exists_frm_kap (act.1.trans (congrArg _ hEB)) W hW κ hκ.1
      obtain ⟨r₁, r₂⟩ := hpull κ hκ g g' act W w hW hw hwv
      have hJ := good ν y
      have e₁ : val κ g.b.left y ν.J = _ := hg.1 ▸ kap_eq ν hL.1.globalFns hκ y h.b
      have e₂ : vF w (𝟙 (Sp C)) ν.J = vF W (𝟙 (Sp C)) ν.J * ((mulq N.θ N.σ m h.b)⁻¹ : Cˣ) :=
        (toStk y).injective ((GtValues.toStk_vF _ _ hJ).trans ((congrArg Units.val (hwv y ν.J hJ)).symm.trans
          (((Units.val_mul _ _).trans (congrArg₂ (· * ·) (GtValues.toStk_vF _ _ hJ).symm (congrArg Units.val e₁))).trans
            (map_mul (toStk y) _ _).symm)))
      refine ⟨fun χ => mul_right_cancel₀ (vF_ne ν W) ?_, fun β hβ => ?_⟩
      · have a := r₁ (ν.eX χ)
        rw [hEh, ← map_nsmul, coef_val ν hf₁ hg hW, coef_theta ν hϑ hg' hw, e₂] at a
        rw [a]; ring
      · have a := r₂ (ν.eX β) (by
          rintro ⟨χ, e⟩
          exact hβ (ν.eX.symm χ) (ν.eX.injective (by rw [map_nsmul, ν.eX.apply_symm_apply, ← hEh, e])))
        rw [coef_val ν hf₁ hg hW] at a
        exact (mul_eq_zero.1 ((mul_eq_zero.1 a).resolve_right (vF_ne ν W))).resolve_right (Units.ne_zero _)
    obtain ⟨⟨_, _⟩, ⟨_, _, θ, -, -, -, hθ, -⟩, -⟩ :=
      GlobalTheory.existsUnique_thetaConst hL V A C ρ hN.2.1 m hm th z (hz w₀ hN.1).1
    obtain ⟨t, ht⟩ := ThetaPtExist.exists_isTwistPull hLB (translT A.A θ.pt) (translPt A.A θ.pt) (lift_snd _ _)
      ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) θ.φ θ.isGen s₁
    obtain ⟨σ, hσ, -⟩ := hbij.1 t
    obtain ⟨f, hf, -⟩ := hv₁ σ
    obtain ⟨w, hw⟩ := (SymFrame.main hL V _ hB D C (m ^ 2) hm.pow p).1
    have hΦ := symLift_acts_as_phi hL V _ hB D A G hG U C (m ^ 2) hm.pow p z hz θ hθ w₀ hN.1 w hw s₁ t σ₁ σ
      hσ₁ hσ ht
    obtain rfl := (hv₂ p q w _ σ₁ σ f₁ f hq hw.1 (txFrame_val ν hL.1 hm.pow hq hw) hf₁ hf).1 hΦ
    have on : ∀ (h : N.Gt) (χ : N.X), N.phi q (N.wQ q) f₁ (q.1.1.toAdd + m • χ) h.b * h.s (q.1.1.toAdd + m • χ) =
        c * N.evT m q h χ := fun h χ => by
      rw [add_comm]
      exact phi_term N m q h f₁ c χ ((pull _).1 χ)
    have off : ∀ β, (∀ χ, β ≠ q.1.1.toAdd + m • χ) → ∀ x, N.phi q (N.wQ q) f₁ β x = 0 := fun β hβ x => by
      obtain ⟨h, hh⟩ := hgt (x * q.1.2.b)
      have a := (pull h).2 (β - q.1.1.toAdd) fun χ e => hβ χ (by rw [← e, add_sub_cancel])
      rw [hh] at a
      rw [NumD.phi, a, mul_zero]
    exact ⟨θ, t, σ, _, hθ, ⟨α, s₁, hα, hαn, hs₁, ht⟩, hσ, hf, on, off⟩
  obtain ⟨Θ, t, s, f, h1, h2, h3, h4, h5, h6⟩ := main th ϑ c hth hϑ
  refine ⟨Θ, t, s, ?_⟩
  by_cases hc : c = 0
  · subst hc
    obtain ⟨th', ϑ', c₀, hc₀, hth', hϑ', -⟩ := exists_theta hL hfam U hN.1 ν
    obtain ⟨-, -, -, f', -, -, -, -, h5', h6'⟩ := main th' ϑ' c₀ hth' hϑ'
    refine ⟨c₀⁻¹ • f', h1, h2, h3, ⟨fun h χ => ?_, fun β hβ x => ?_⟩, ?_⟩
    · rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, h5', inv_mul_cancel_left₀ hc₀]
    · rw [Pi.smul_apply, Pi.smul_apply, h6' β hβ x, smul_zero]
    · rw [zero_smul]
      convert h4 using 1
      funext β x
      rw [Pi.zero_apply, Pi.zero_apply]
      by_cases hβ : ∃ χ, β = q.1.1.toAdd + m • χ
      · obtain ⟨χ, rfl⟩ := hβ
        obtain ⟨h, rfl⟩ := hgt x
        have e := h5 h χ
        rw [zero_mul] at e
        exact ((mul_eq_zero.1 e).resolve_right (Units.ne_zero _)).symm
      · push_neg at hβ
        exact (h6 β hβ x).symm
  · refine ⟨c⁻¹ • f, h1, h2, h3, ⟨fun h χ => ?_, fun β hβ x => ?_⟩, ?_⟩
    · rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, h5, inv_mul_cancel_left₀ hc]
    · rw [Pi.smul_apply, Pi.smul_apply, h6 β hβ x, smul_zero]
    · rwa [smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.MBLow
end
