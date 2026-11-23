import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointHasNonzeroLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImageZMCoordIdealOfEq
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.UnderIdeal

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {A Ω : Type*} [CommRing A] [Field Ω]

theorem eval_eq_zero_of_mem_mCoordIdeal (e : A →+* Ω) (he : Function.Injective e) (ρ : (Σ k, ι k) → A)
    {f : Geo.MRing ι} (hf : f ∈ Geo.mCoordIdeal fun p => e (ρ p)) (ε : A →+* ℂ) (t : K → ℂ) :
    eval (fun p => t p.1 * ε (ρ p)) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := by
  let q : Geo.MRing ι →+* MvPolynomial K A := eval₂Hom (Int.castRingHom _) fun p => C (ρ p) * X p.1
  have h1 : (MvPolynomial.map e).comp q =
      (Geo.mConeMap (fun p => e (ρ p)) : Geo.MRing ι →ₐ[ℤ] MvPolynomial K Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp [q]
    · simp [q, Geo.mConeMap]
  have h0 : q f = 0 := by
    refine map_injective e he ?_
    rw [map_zero]
    have := congrArg (fun g => g f) h1
    refine this.trans ?_
    exact hf
  have h2 : (eval₂Hom ε t).comp q =
      (eval (fun p => t p.1 * ε (ρ p))).comp (MvPolynomial.map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp [q]
    · simp [q, mul_comm]
  have := congrArg (fun g => g f) h2
  simp only [RingHom.comp_apply, h0, map_zero] at this
  exact this.symm

end Alg

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ptCoord_eq_mul (x : MP ℤ m n) (c : ∀ k, Bk n k) (hx : x ∈ mchart c) :
    ∃ b : Fin (m + 1) → (MP ℤ m n).residueField x, (∀ k, b k ≠ 0) ∧ ∀ p : Σ k, Bk n k,
      ptCoord x p = b p.1 * (MP ℤ m n).evaluation (mchart c) x hx
        (resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2)) := by
  have key : ∀ k, ∃ b : (MP ℤ m n).residueField x, b ≠ 0 ∧ ∀ j : Bk n k,
      ptCoord x ⟨k, j⟩ = b * (MP ℤ m n).evaluation (blockChart n k (c k)) x (mchart_le c k hx)
        (pullRatio (prB n k) _ (c k) le_rfl j) := by
    intro k
    let W₀ := blockChart n k (ptChart x k)
    let W₁ := blockChart n k (c k)
    let V := W₀ ⊓ W₁
    have hxV : x ∈ V := ⟨mem_ptChart x k, mchart_le c k hx⟩
    have hV₀ : V ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := inf_le_left
    have hV₁ : V ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (c k) := inf_le_right
    have e₀ : ∀ j : Bk n k, ptCoord x ⟨k, j⟩ =
        (MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (ptChart x k) hV₀ j) := by
      intro j
      show (MP ℤ m n).evaluation W₀ x (mem_ptChart x k) (pullRatio (prB n k) W₀ (ptChart x k) le_rfl j) = _
      rw [← ProjImage.evaluation_resG (inf_le_left : V ≤ W₀) x hxV]
      exact congrArg _ (resG_pullRatio (φ := prB n k) (hi := le_rfl) inf_le_left)
    have e₁ : ∀ j : Bk n k, (MP ℤ m n).evaluation W₁ x (mchart_le c k hx)
        (pullRatio (prB n k) W₁ (c k) le_rfl j) =
        (MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (c k) hV₁ j) := by
      intro j
      rw [← ProjImage.evaluation_resG (inf_le_right : V ≤ W₁) x hxV]
      exact congrArg _ (resG_pullRatio (φ := prB n k) (hi := le_rfl) inf_le_right)
    refine ⟨(MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (ptChart x k) hV₀ (c k)), ?_, fun j => ?_⟩
    · intro h0
      have e := congrArg ((MP ℤ m n).evaluation V x hxV)
        ((pullRatio_mul_pullRatio (φ := prB n k) (hi := hV₀) (hj := hV₁) (k := ptChart x k)).trans pullRatio_self)
      rw [map_mul, h0, zero_mul, map_one] at e
      exact zero_ne_one e
    · refine (e₀ j).trans ?_
      rw [e₁ j, ← map_mul]
      exact congrArg _ (pullRatio_mul_pullRatio (φ := prB n k) (hi := hV₀) (hj := hV₁) (k := j)).symm
  choose b hb hbe using key
  refine ⟨b, hb, fun p => ?_⟩
  rw [ProjImage.evaluation_resG]
  exact hbe p.1 p.2

theorem evaluation_genericPoint_injective {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (h : genericPoint X ∈ U) :
    Function.Injective (X.evaluation U (genericPoint X) h) := by
  have h1 : Function.Injective (X.residue (genericPoint X)).hom :=
    RingHom.injective (R := X.functionField) (X.residue (genericPoint X)).hom
  exact h1.comp (fnOf_injective U h)

end GlobalTheory.CompanionTheory.MPDict.UnderIdeal

namespace GlobalTheory.CompanionTheory.MPDict

open UnderIdeal in

theorem exists_mem_mcPts_isUnder : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀), ∃ z ∈ mcPts (ptIdeal (i (genericPoint X))), IsUnder (PtsOver.map i rfl _ y) z := by
  intro m n X _ i _ y
  obtain ⟨z, hz, hu⟩ := exists_isUnder_of_cxPt m n (PtsOver.map i rfl _ y)
  refine ⟨z, ⟨hz, fun f hf => ?_⟩, hu⟩
  choose c hc using hz
  have hwk : ∀ k, PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) :=
    fun k => (hu k (c k)).1.2 (hc k)
  have hwV : PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) :=
    CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => CxPts.mem_ptsIn.1 (hwk k))
  have hyV : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) := hwV
  have hη : genericPoint X ∈ i ⁻¹ᵁ mchart c :=
    ((genericPoint_spec X).mem_open_set_iff (i ⁻¹ᵁ mchart c).isOpen).2 ⟨_, trivial, CxPts.mem_ptsIn.1 hyV⟩
  obtain ⟨b, hb, hbe⟩ := ptCoord_eq_mul (i (genericPoint X)) c hη
  let r : (Σ k, Bk n k) → Γ(MP ℤ m n, mchart c) := fun p =>
    resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2)
  let ρ : (Σ k, Bk n k) → Γ(X, i ⁻¹ᵁ mchart c) := fun p => (i.app (mchart c)).hom (r p)
  let φ := (i.residueFieldMap (genericPoint X)).hom
  have hf' : f ∈ Geo.mCoordIdeal fun p => (X.evaluation _ _ hη).hom (ρ p) := by
    have e := ProjImage.imageZ_mCoordIdeal_of_eq (ι := Bk n) (ι' := Bk n) id Function.injective_id id (fun _ => rfl) φ
      (fun k => φ (b k)) (fun k => (map_ne_zero φ).2 (hb k))
      (ptCoord (i (genericPoint X))) (fun p => (X.evaluation _ _ hη).hom (ρ p)) (fun p => by
        rw [hbe p, map_mul]
        congr 1
        exact Scheme.evaluation_naturality_apply _ _ _ _)
    rw [ptIdeal, ← e] at hf
    simpa [ReciprocityTheory.ChartRestriction.G.AI.I4.imageZ] using hf
  have h := eval_eq_zero_of_mem_mCoordIdeal (X.evaluation _ _ hη).hom
    (evaluation_genericPoint_injective _ hη) ρ hf' (evHom hyV) (fun k => z ⟨k, c k⟩)
  have hz' : (fun p : Σ k, Bk n k => z ⟨p.1, c p.1⟩ * evHom hyV (ρ p)) = z := by
    funext ⟨k, j⟩
    have e1 : evHom hyV (ρ ⟨k, j⟩) = z ⟨k, j⟩ / z ⟨k, c k⟩ := by
      rw [← CxPts.ev_eq hyV]
      refine Eq.trans ?_ ((hu k (c k)).2 j (hwk k))
      refine Eq.trans ?_ (CxPts.ev_res (mchart_le c k) hwV _)
      exact (valR_comp y.1 i (mchart c) (r ⟨k, j⟩)).symm
    show z ⟨k, c k⟩ * evHom hyV (ρ ⟨k, j⟩) = z ⟨k, j⟩
    rw [e1, mul_div_cancel₀ _ (hc k)]
  rw [hz'] at h
  exact h

end GlobalTheory.CompanionTheory.MPDict
