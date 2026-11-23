import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnimodularAndTangentOfIsAH
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.LevelThreeSeparatesTangentVectors

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.LevelDict

section Charts

variable {X : Scheme.{0}} (L : LB X) (n : ℕ)

theorem sec_ext {M : LB X} {s t : M.Sec} (h : ∀ i, s.f i = t.f i) : s = t := by
  obtain ⟨f, hf⟩ := s
  obtain ⟨f', hf'⟩ := t
  obtain rfl : f = f' := funext h
  rfl

theorem powChart_le (j : (lbPow L n).ι) : (lbPow L n).U j ≤ L.U (j PUnit.unit) :=
  fun _ hy => Set.mem_iInter.1 hy PUnit.unit

theorem le_powChart (j : (lbPow L n).ι) : L.U (j PUnit.unit) ≤ (lbPow L n).U j :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy

theorem lbPow_g (j j' : (lbPow L n).ι) : ((lbPow L n).g j j').val =
    rs X (inf_le_inf (powChart_le L n j) (powChart_le L n j'))
      (L.g (j PUnit.unit) (j' PUnit.unit) ^ (n : ℤ)).val := by
  have h : (lbPow L n).g j j' = res (inf_le_inf (powChart_le L n j) (powChart_le L n j'))
      (L.g (j PUnit.unit) (j' PUnit.unit) ^ (n : ℤ)) := by
    rw [map_zpow]
    unfold lbPow LB.LinComb
    dsimp only
    rw [Fintype.prod_unique]
    rfl
  rw [h]
  rfl

def powSecEquiv : (lbPow L n).Sec ≃ (pw L (n : ℤ)).Sec where
  toFun s := ⟨fun i => rs X (le_powChart L n fun _ => i) (s.f fun _ => i), fun i k => by
    have h := congrArg (rs X (inf_le_inf (le_powChart L n fun _ => i) (le_powChart L n fun _ => k)))
      (s.compat (fun _ => i) (fun _ => k))
    refine (rs_rs _ _ _).trans ((rs_rs _ _ _).symm.trans (h.trans ((map_mul _ _ _).trans ?_)))
    exact congrArg₂ (· * ·) ((congrArg _ (lbPow_g L n _ _)).trans ((rs_rs _ _ _).trans (rs_self _ _)))
      ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)⟩
  invFun s := ⟨fun j => rs X (powChart_le L n j) (s.f (j PUnit.unit)), fun j k => by
    have h := congrArg (rs X (inf_le_inf (powChart_le L n j) (powChart_le L n k)))
      (s.compat (j PUnit.unit) (k PUnit.unit))
    rw [lbPow_g]
    refine (rs_rs _ _ _).trans ((rs_rs _ _ _).symm.trans (h.trans ((map_mul _ _ _).trans ?_)))
    exact congrArg _ ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)⟩
  left_inv s := sec_ext fun _ => (rs_rs _ _ _).trans (rs_self _ _)
  right_inv s := sec_ext fun _ => (rs_rs _ _ _).trans (rs_self _ _)

theorem valAt'_powSecEquiv (s : (lbPow L n).Sec) (x : Sp ℂ ⟶ X) (j : (lbPow L n).ι)
    (h : ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit)) :
    valAt' x (L.U (j PUnit.unit)) ((powSecEquiv L n s).f (j PUnit.unit)) = valAt' x ((lbPow L n).U j) (s.f j) :=
  valAt'_map x (homOfLE (le_powChart L n j)).op (s.f j) h

end Charts

theorem transfer {S S' T T' : Type*} (E : S ≃ S') (G : T ≃ T') {P : T → Prop} {P' : T' → Prop} {Q : S → T → Prop}
    {Q' : S' → T' → Prop} (hP : ∀ t, P' (G t) ↔ P t) (hQ : ∀ s t, Q' (E s) (G t) ↔ Q s t)
    (h : (∀ s, ∃! t, P t ∧ Q s t) ∧ ∀ t, P t → ∃! s, Q s t) :
    (∀ s, ∃! t, P' t ∧ Q' s t) ∧ ∀ t, P' t → ∃! s, Q' s t := by
  refine ⟨fun s => ?_, fun t ht => ?_⟩
  · obtain ⟨s, rfl⟩ := E.surjective s
    rw [← G.existsUnique_congr (p := fun t => P t ∧ Q s t) fun t => by rw [hP, hQ]]
    exact h.1 s
  · obtain ⟨t, rfl⟩ := G.surjective t
    rw [← E.existsUnique_congr (p := fun s => Q s t) fun s => by rw [hQ]]
    exact h.2 t ((hP t).1 ht)

theorem ext_of_ne_zero {g : ℕ} {θ f f' : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0) (hf : Continuous f)
    (hf' : Continuous f') (h : ∀ z, θ z ≠ 0 → f z = f' z) : ∀ z, f z = f' z :=
  congrFun (Continuous.ext_on (ThetaTangent.dense_ne_zero hθ h0) hf hf' h)

section Frames

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

open PullHermitian in

theorem exists_frame_ratio (hL : L.IsLB) (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) :
    ∃ r : (Fin g → ℂ) → ℂ, Differentiable ℂ r ∧ (∀ z, r z ≠ 0) ∧
      ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u₀.fr i (F z) = r z * u.fr i z := by
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have tr : ∀ {U : A.left.Opens} {z}, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → ⊤ ≤ (u₀.ex (F z)).left ⁻¹ᵁ U :=
    fun h => by rwa [hF]
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun i : L.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
    (fun i => (u.hol _ 0).1)
    (fun z => PullHermitian.exists_chart (u.ex z).left hL)
    (fun i z => u₀.fr i (F z) / u.fr i z)
    (fun i => by
      have d2 := (u₀.fr_hol i).comp (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
        hFd.differentiableOn fun z hz => tr hz
      simp only [div_eq_mul_inv]
      exact d2.mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz))
    (fun i j z hi hj => by
      have h1 := u.fr_compat i j z (inf_of _ hi hj)
      have h2 := u₀.fr_compat i j (F z) (tr (inf_of _ hi hj))
      rw [hF] at h2
      rw [div_eq_div_iff (u.fr_ne _ _ hi) (u.fr_ne _ _ hj), h1, h2]
      ring)
  refine ⟨r, hr, fun z => ?_, fun i z hi => ?_⟩
  · obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
    rw [hrφ i z hi]
    exact div_ne_zero (u₀.fr_ne _ _ (tr hi)) (u.fr_ne _ _ hi)
  · rw [hrφ i z hi, div_mul_cancel₀ _ (u.fr_ne _ _ hi)]

end Frames

theorem isLevel_thetaChar {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (hab : charHalf g a b) :
    IsLevel τ a b 1 (thetaChar τ a b) ∧ thetaChar τ a b ≠ 0 := by
  obtain ⟨h0, h1, -⟩ := TorusAlg.thetaChar_level hs hp hab.1 hab.2
  have hm : thetaChar τ a b ∈ thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) 1 τ := by
    rw [h1]
    exact Submodule.mem_span_singleton_self _
  rw [mem_thetaLevelChar, TorusAlg.ofRealVec_re hab.1, TorusAlg.ofRealVec_re hab.2] at hm
  refine ⟨⟨hm.1, fun m n z => ?_⟩, h0⟩
  have h := hm.2 n m z
  rw [add_assoc, add_comm (τ.mulVec _), ReciprocityTheory.PTheta.eC, ReciprocityTheory.PTheta.eC, ← Complex.exp_add] at h
  refine h.trans ?_
  rw [pow_one]
  congr 2
  unfold ReciprocityTheory.PTheta.ofIntVec
  push_cast
  ring

theorem sections_eq_level : ThetaUnifAV → ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (l : ℕ), charHalf g a b → Wit x h u τ a b → (∀ s : RR x l, ∃! F, IsLevel τ a b l F ∧ FnPw x u s F) ∧ ∀ F, IsLevel τ a b l F → ∃! s : RR x l, FnPw x u s F := by
  intro hT g x h u τ a b l hab ⟨hs, hp, hΛ, _, hth, _⟩
  subst h
  obtain ⟨u₀, H₀, χ₀, -, hu₀, -, hv, hw, -, hsec, -⟩ := hT x.P x.rig x.rig_gen
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g x.P.g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  let e : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := LinearEquiv.ofInjectiveEndo F (UnifCompare.injective u u₀ F hF)
  have he : ∀ z, e z = F z := fun z => rfl
  have hed : Differentiable ℂ e := (LinearMap.toContinuousLinearMap F).differentiable
  have hed' : Differentiable ℂ e.symm := (LinearMap.toContinuousLinearMap e.symm.toLinearMap).differentiable
  obtain ⟨r, hr, hr0, hrf⟩ := exists_frame_ratio x.P.isLB u u₀ F hF
  obtain ⟨hθ, hθ0⟩ := isLevel_thetaChar hs hp hab
  let G : ((Fin x.P.g → ℂ) → ℂ) ≃ ((Fin x.P.g → ℂ) → ℂ) :=
    { toFun := fun f z => f (e z) * r z ^ l
      invFun := fun f w => f (e.symm w) * (r (e.symm w) ^ l)⁻¹
      left_inv := fun f => funext fun w => by
        simp only [e.apply_symm_apply]
        exact mul_inv_cancel_right₀ (pow_ne_zero _ (hr0 _)) _
      right_inv := fun f => funext fun z => by
        simp only [e.symm_apply_apply]
        exact inv_mul_cancel_right₀ (pow_ne_zero _ (hr0 _)) _ }
  have hG : ∀ f z, G f z = f (e z) * r z ^ l := fun _ _ => rfl

  have key : ∀ (m n : Fin x.P.g → ℤ) (k : u₀.Λ), (k : Fin x.P.g → ℂ) =
      e ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) → ∀ z,
      χ₀ k * Complex.exp (Real.pi * hermForm H₀ (e z) k + Real.pi / 2 * hermForm H₀ k k) *
        r (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) =
      Complex.exp (2 * Real.pi * Complex.I * (a ⬝ᵥ (fun i => (m i : ℂ)) - b ⬝ᵥ (fun i => (n i : ℂ)) -
        ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z)) * r z := by
    intro m n k hk
    have hec := hed.continuous
    have hrc := hr.continuous
    refine ext_of_ne_zero hθ.1 hθ0 ?_ ?_ fun z hz => ?_
    · unfold hermForm
      fun_prop
    · fun_prop
    · have h1 := hθ.2 m n z
      rw [pow_one] at h1
      set w := (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) with hw
      have hper : u.ex (z + w) = u.ex z := by
        rw [u.ex_add, (u.ker w).2 ((hΛ w).2 ⟨m, n, hw⟩), _root_.mul_one]
      obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left x.P.isLB
      have hi' : ⊤ ≤ (u.ex (z + w)).left ⁻¹ᵁ x.P.L.U i := by rwa [hper]
      have h2 := hth i z hi
      have h3 := hth i _ hi'
      rw [hper, h2, h1] at h3
      have h4 := hu₀.2.2.2 k i (e z) (by rw [he, hF]; exact hi)
      rw [hk, ← map_add, he, he (z + w), hrf i z hi, hrf i _ hi', ← he, ← hk] at h4
      refine mul_right_cancel₀ (mul_ne_zero hz (u.fr_ne i _ hi')) ?_
      unfold hermForm
      linear_combination r z * h3 - thetaChar τ a b z * h4
  refine transfer (powSecEquiv x.P.L l) G (fun f => ?_) (fun s f => ?_) (hsec l)
  on_goal 1 => refine ⟨fun hf => ⟨?_, fun k w => ?_⟩, fun hf => ⟨?_, fun m n z => ?_⟩⟩
  on_goal 5 => refine ⟨fun hf j w hj => ?_, fun hf i z hi => ?_⟩
  · rw [← G.symm_apply_apply f]
    exact (hf.1.comp hed').mul (((hr.comp hed').pow l).inv fun w => pow_ne_zero _ (hr0 _))
  · obtain ⟨z, rfl⟩ := e.surjective w
    obtain ⟨m, n, hmn⟩ := (hΛ (e.symm k)).1 ((UnifCompare.mem_iff u u₀ F hF _).1 (by
      rw [← he, e.apply_symm_apply]; exact k.2))
    have hk := e.symm_apply_eq.1 hmn
    have h1 := hf.2 m n z
    rw [hG, hG, map_add, ← hk, mul_comm (f (e z)), ← _root_.mul_assoc, ← mul_pow, ← key m n k hk z, mul_pow] at h1
    refine mul_right_cancel₀ (pow_ne_zero l (hr0 _)) (h1.trans ?_)
    ring
  · exact (hf.1.comp hed).mul (hr.pow l)
  · have hk := (UnifCompare.mem_iff u u₀ F hF _).2 ((hΛ _).2 ⟨m, n, rfl⟩)
    have h1 := hf.2 ⟨e _, hk⟩ (e z)
    rw [hG, hG, map_add, mul_comm (f (e z)), ← _root_.mul_assoc, ← mul_pow, ← key m n ⟨e _, hk⟩ rfl z, mul_pow, h1]
    ring
  · obtain ⟨z, rfl⟩ := e.surjective w
    rw [he] at hj ⊢
    rw [hF] at hj ⊢
    have hi := top_le_preimage_mono _ (powChart_le _ _ j) hj
    rw [← valAt'_powSecEquiv _ _ s _ j hi, hrf _ z hi, mul_pow, ← _root_.mul_assoc]
    exact hf _ z hi
  · have h1 := hf (fun _ => i) (F z) (by rw [hF]; exact top_le_preimage_mono _ (le_powChart _ _ fun _ => i) hi)
    rw [hF, hrf i z hi, mul_pow, ← _root_.mul_assoc] at h1
    exact (valAt'_powSecEquiv _ _ s _ (fun _ => i) hi).trans h1

end GlobalTheory.LevelDict
