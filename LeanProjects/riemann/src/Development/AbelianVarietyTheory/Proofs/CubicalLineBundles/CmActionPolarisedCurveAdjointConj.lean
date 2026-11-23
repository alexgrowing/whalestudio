import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplexStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CurveAdjoint

theorem linear_eq_of_ex {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, u.ex (F z) = u.ex (G z)) : F = G := by
  have hD : ∀ z, (F - G) z ∈ u.Λ := by
    intro z
    rw [← u.ker]
    have h1 := u.ex_add (G z) ((F - G) z)
    have e : G z + (F - G) z = F z := by simp
    rw [e, h z] at h1
    exact mul_left_cancel (a := u.ex (G z)) (by rw [_root_.mul_one]; exact h1.symm)
  refine LinearMap.ext fun z => ?_
  have hc : Continuous (fun t : ℝ => (⟨(F - G) ((t : ℂ) • z), hD _⟩ : u.Λ)) :=
    Continuous.subtype_mk ((F - G).continuous_of_finiteDimensional.comp
      (Complex.continuous_ofReal.smul continuous_const)) _
  haveI := u.discrete
  have h2 := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := 1) (y := 0))
  simp only [Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_smul, map_zero] at h2
  exact sub_eq_zero.mp h2

theorem exists_scalar {g : ℕ} (hg : g = 1) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : ∃ c : ℂ, ∀ z, F z = c • z := by
  subst hg
  refine ⟨F (fun _ => 1) 0, fun z => ?_⟩
  have hz : z = z 0 • (fun _ : Fin 1 => (1 : ℂ)) := by
    funext i
    rw [Subsingleton.elim i 0]
    simp
  rw [hz, map_smul]
  funext i
  rw [Subsingleton.elim i 0]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem map_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (j : OK H →+* ℂ) (x y : OK H)
    (h : (y : 𝓞 E) = H.bar x) : j y = starRingEnd ℂ (j x) := by
  obtain ⟨-, huniq, ⟨br, hbr, hw, -⟩, hquad, -⟩ := OK_isDedekindDomain_and_projective E H
  have hy : y = br x := Subtype.ext (h.trans (hbr x).symm)
  have hbw : br (wK H) = 1 - wK H := eq_sub_of_add_eq' hw
  obtain ⟨⟨m₁, m₂⟩, hx, -⟩ := huniq x
  have hN : (1 : ℝ) ≤ (((1 + H.d) / 4 : ℕ) : ℝ) := by
    have := H.d_mod
    exact_mod_cast (by omega : 1 ≤ (1 + H.d) / 4)
  have hq := congrArg j hquad
  simp only [map_add, map_pow, map_natCast] at hq
  have hz : starRingEnd ℂ (j (wK H)) = 1 - j (wK H) := by
    have e := congrArg Complex.re hq
    have f := congrArg Complex.im hq
    simp [pow_two] at e f
    have ha : (j (wK H)).re = 1 / 2 := by
      rcases eq_or_ne (j (wK H)).im 0 with h0 | h0
      · exfalso
        rw [h0] at e
        nlinarith [sq_nonneg ((j (wK H)).re - 1 / 2)]
      · have h2 : 2 * (j (wK H)).re = 1 := by
          apply mul_left_cancel₀ h0
          linear_combination f
        linarith
    apply Complex.ext <;> simp <;> linarith
  rw [hy, hx]
  simp only [map_add, map_mul, map_intCast, hbw, map_sub, map_one, hz]

theorem lamEq_act_bar : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDedekindDomain R] (σ : R →+* ℂ) (P : Out.PolAV (Sp R)) (a : OAct (OK H) P.A), Function.Injective σ → P.g = 1 → ∀ x y : OK H, (y : 𝓞 E) = H.bar x → LamEq P.L (a.act x) (𝟙 P.A) P.L (𝟙 P.A) (a.act y) := by
  intro hT hL E _ _ _ H R _ _ σ P a hσ hg x y hxy
  haveI : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨Q, φ, hQg, hφ, hLφ⟩ := GlobalTheory.exists_isPolFibre hL.polBaseChange σ P
  haveI : IsCommMonObj Q.A := Q.isAb.comm
  have hQ1 : Q.g = 1 := hQg.trans hg
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, hend, -⟩ := hT Q rig hrig
  have hex : ∀ r : OK H, ∃ c : ℂ, ∃ w' : Q.A ⟶ Q.A, IsMonHom w' ∧ w'.left ≫ φ = φ ≫ (a.act r).left ∧
      ∀ z, u.ex (c • z) = u.ex z ≫ w' := by
    intro r
    haveI := a.hom r
    obtain ⟨w', hw'm, hw'⟩ := GlobalTheory.PairingFibre.exists_hom hφ hφ (a.act r)
    obtain ⟨F, hF⟩ := hend w' hw'm
    obtain ⟨c', hc'⟩ := exists_scalar hQ1 F
    exact ⟨c', w', hw'm, hw', fun z => by rw [← hc' z, hF z]⟩
  choose c w hmon hcomm hlift using hex
  have hcomm' : ∀ r {Z : Scheme.{0}} (h : P.A.left ⟶ Z), (w r).left ≫ φ ≫ h = φ ≫ (a.act r).left ≫ h := by
    intro r Z h
    rw [← Category.assoc, hcomm r, Category.assoc]
  have huniq : ∀ r (c' : ℂ) (w' : Q.A ⟶ Q.A), w'.left ≫ φ = φ ≫ (a.act r).left →
      (∀ z, u.ex (c' • z) = u.ex z ≫ w') → c' = c r := by
    intro r c' w' hw' hl
    have hww : w' = w r := by
      apply Over.OverMorphism.ext
      apply hφ.1.hom_ext
      · rw [hw', hcomm r]
      · rw [Over.w w', Over.w (w r)]
    subst hww
    have he := linear_eq_of_ex u (c' • LinearMap.id) (c r • LinearMap.id) (fun z => by
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [hl, hlift r])
    have he' := congrFun (LinearMap.congr_fun he (fun _ => 1)) ⟨0, by omega⟩
    simpa using he'
  have hone : c 1 = 1 :=
    (huniq 1 1 (𝟙 Q.A) (by rw [a.one]; simp) (fun z => by simp)).symm
  have hmul : ∀ r s, c (r * s) = c r * c s := by
    intro r s
    refine (huniq (r * s) (c r * c s) (w r ≫ w s) ?_ ?_).symm
    · simp only [a.mul, Over.comp_left, Category.assoc, hcomm, hcomm']
    · intro z
      rw [← Category.assoc, ← hlift r z, ← hlift s (c r • z), smul_smul, _root_.mul_comm]
  have hadd : ∀ r s, c (r + s) = c r + c s := by
    intro r s
    refine (huniq (r + s) (c r + c s) (w r * w s) ?_ ?_).symm
    · let jm : Over.mk (Q.A.hom ≫ spMap σ) ⟶ P.A := Over.homMk φ hφ.1.w
      have h := hφ.2 Q.A (w r) (w s) (jm ≫ a.act r) (jm ≫ a.act s) (by simp [jm, hcomm r]) (by simp [jm, hcomm s])
      rw [← h, ← MonObj.comp_mul, ← a.add, Over.comp_left]
      simp [jm]
    · intro z
      rw [add_smul, u.ex_add, hlift r, hlift s, MonObj.comp_mul]
  let j : OK H →+* ℂ := RingHom.mk' ⟨⟨c, hone⟩, hmul⟩ hadd
  have hj : c y = starRingEnd ℂ (c x) := map_bar H j x y hxy
  have hQ : WeilEq Q.L (w x) (𝟙 Q.A) Q.L (𝟙 Q.A) (w y) (𝟙 (Sp ℂ)) := by
    rw [GlobalTheory.T.weilEq_iff_hermForm_eq_complex hT hL Q Q Q Q u u u u Hm Hm χ χ hAH hAH (w x) (𝟙 Q.A) (𝟙 Q.A) (w y)
      (c x • LinearMap.id) LinearMap.id LinearMap.id (c y • LinearMap.id)
      (fun z => by simpa using hlift x z) (fun z => by simp) (fun z => by simp) (fun z => by simpa using hlift y z)]
    intro z v
    simp [hermForm, hj, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, star_smul]
  have hP : WeilEq P.L (a.act x) (𝟙 P.A) P.L (𝟙 P.A) (a.act y) (spMap σ) := by
    have hb := (GlobalTheory.PairingFibre.weilEq_iff hφ hφ hφ hφ P.isLB P.isLB Q.isLB Q.isLB (LBIso.symm hLφ) (LBIso.symm hLφ)
      (f₁ := a.act x) (f₂ := 𝟙 P.A) (g₁ := 𝟙 P.A) (g₂ := a.act y)
      (f₁' := w x) (f₂' := 𝟙 Q.A) (g₁' := 𝟙 Q.A) (g₂' := w y)
      (hcomm x) (by simp) (by simp) (hcomm y) (𝟙 (Sp ℂ))).mp hQ
    rwa [Category.id_comp] at hb
  exact (GlobalTheory.PairingFibre.lamEq_weilEq_over_ring hL R P P P P (a.act x) (𝟙 P.A) (𝟙 P.A) (a.act y)
    (a.hom x) inferInstance inferInstance (a.hom y) ℂ σ).2 inferInstance hσ hP

end GlobalTheory.CurveAdjoint
end
