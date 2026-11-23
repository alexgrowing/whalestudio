import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdapted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneIntegralSkewHermitianTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConstantTermParabolicStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLocalLieRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationIntertwinesLieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModuleFiniteQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightDerivativeNilRadicalInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModuleRankOneRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModuleRankOneLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvelopingAlgebraLineWordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExponentialProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimTranslationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchUnipotentRadicalMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomainIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimProductTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNormAdaptedPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementInfinitePointsStatement

noncomputable section
namespace GlobalTheory.TorFin
open Matrix
open scoped ContDiff

section Mat
variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {x y : Fin n → ℂ}

theorem form_swap (hJ : Jᴴ = J) (x y : Fin n → ℂ) : (star y ᵥ* J) ⬝ᵥ x = star ((star x ᵥ* J) ⬝ᵥ y) := by
  rw [← dotProduct_mulVec, star_dotProduct, star_mulVec, hJ]

theorem projL_mulVec (x y v : Fin n → ℂ) : projL J x y *ᵥ v = ((star y ᵥ* J) ⬝ᵥ v) • x := by
  rw [projL, vecMulVec_mulVec, op_smul_eq_smul]

theorem vecMul_projL (x y φ : Fin n → ℂ) : φ ᵥ* projL J x y = (φ ⬝ᵥ x) • (star y ᵥ* J) := by
  rw [projL, vecMul_vecMulVec]

theorem projL_mul (x y x' y' : Fin n → ℂ) (h : (star y ᵥ* J) ⬝ᵥ x' = 0) : projL J x y * projL J x' y' = 0 := by
  rw [projL, projL, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]

theorem br_left (hxx : (star x ᵥ* J) ⬝ᵥ x = 0) (y : Fin n → ℂ) {Y : Matrix (Fin n) (Fin n) ℂ} (h : Y ∈ nilRad J x) :
    projL J x y * Y - Y * projL J x y ∈ nilRad J x := by
  have e : Y * projL J x y = 0 := by rw [projL, mul_vecMulVec, h.1, zero_vecMulVec]
  rw [e, sub_zero]
  refine ⟨by rw [← mulVec_mulVec, h.1, mulVec_zero], by rw [← vecMul_vecMul, vecMul_projL, hxx, zero_smul, zero_vecMul],
    fun v _ => ⟨_, by rw [← mulVec_mulVec, projL_mulVec]⟩⟩

theorem br_right (hxx : (star x ᵥ* J) ⬝ᵥ x = 0) (y : Fin n → ℂ) {Y : Matrix (Fin n) (Fin n) ℂ} (h : Y ∈ nilRad J x) :
    projL J y x * Y - Y * projL J y x ∈ nilRad J x := by
  have e : projL J y x * Y = 0 := by rw [projL, vecMulVec_mul, h.2.1, vecMulVec_zero]
  rw [e, zero_sub]
  refine neg_mem ⟨by rw [← mulVec_mulVec, projL_mulVec, hxx, zero_smul, mulVec_zero],
    by rw [← vecMul_vecMul, h.2.1, zero_vecMul],
    fun v hv => ⟨0, by rw [← mulVec_mulVec, projL_mulVec, hv, zero_smul, mulVec_zero, zero_smul]⟩⟩

theorem row_mem (hxx : (star x ᵥ* J) ⬝ᵥ x = 0) {ψ : Fin n → ℂ} (h : ψ ⬝ᵥ x = 0) : vecMulVec x ψ ∈ nilRad J x :=
  ⟨by rw [vecMulVec_mulVec, h, MulOpposite.op_zero, zero_smul], by rw [vecMul_vecMulVec, hxx, zero_smul],
    fun v _ => ⟨_, by rw [vecMulVec_mulVec, op_smul_eq_smul]⟩⟩

theorem col_mem (hxx : (star x ᵥ* J) ⬝ᵥ x = 0) {u : Fin n → ℂ} (h : (star x ᵥ* J) ⬝ᵥ u = 0) :
    vecMulVec u (star x ᵥ* J) ∈ nilRad J x :=
  ⟨by rw [vecMulVec_mulVec, hxx, MulOpposite.op_zero, zero_smul], by rw [vecMul_vecMulVec, h, zero_smul],
    fun v hv => ⟨0, by rw [vecMulVec_mulVec, hv, MulOpposite.op_zero, zero_smul, zero_smul]⟩⟩

theorem IsUni.isUnit (hd : IsUnit J.det) {u : Matrix (Fin n) (Fin n) ℂ} (hu : IsUni J u) : IsUnit u.det := by
  have := congrArg Matrix.det hu
  rw [det_mul, det_mul] at this
  exact isUnit_of_mul_isUnit_right (this.symm ▸ hd)

theorem IsSkew.exp (hd : IsUnit J.det) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (t : ℝ) :
    IsUni J (NormedSpace.exp (t • Z)) := by
  refine GlobalTheory.SmoothForms.exp_mem_UH hd ?_
  have : Zᴴ * J + J * Z = 0 := hZ
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, this, smul_zero]

end Mat

section Alg
variable {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A}

theorem IsIntMod.mono {Z : Subalgebra ℂ A} {I I' : Submodule ℂ A} {H : A} (h : IsIntMod Z I H) (hI : I ≤ I') :
    IsIntMod Z I' H := let ⟨N, hN⟩ := h; ⟨N, sup_le_sup_right hI _ hN⟩

theorem leftIdl_mono {S S' : Set (Matrix (Fin n) (Fin n) ℂ)} (h : S ⊆ S') : leftIdl ρ S ≤ leftIdl ρ S' :=
  Submodule.span_mono fun _ ⟨Y, hY, e⟩ => ⟨Y, h hY, e⟩

theorem mul_mem_leftIdl (hρ : IsLieRep ρ) {S : Set (Matrix (Fin n) (Fin n) ℂ)} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ Y ∈ S, X * Y - Y * X ∈ S) : ∀ i ∈ leftIdl ρ S, ρ X * i ∈ leftIdl ρ S := by
  intro i hi
  induction hi using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨Y, hY, w, hw, rfl⟩ := ha
    have e : ρ X * (ρ Y * w) = ρ (X * Y - Y * X) * w + ρ Y * (ρ X * w) := by rw [hρ]; noncomm_ring
    rw [e]
    exact add_mem (Submodule.subset_span ⟨_, hX Y hY, w, hw, rfl⟩)
      (Submodule.subset_span ⟨Y, hY, _, mul_mem (Algebra.subset_adjoin ⟨X, rfl⟩) hw, rfl⟩)
  | zero => simp
  | add a b _ _ h h' => rw [mul_add]; exact add_mem h h'
  | smul c a _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h

theorem leftIdl_mul_mem {S : Set (Matrix (Fin n) (Fin n) ℂ)} : ∀ i ∈ leftIdl ρ S, ∀ z ∈ invAlg ρ, i * z ∈ leftIdl ρ S := by
  intro i hi z hz
  induction hi using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨Y, hY, w, hw, rfl⟩ := ha
    exact Submodule.subset_span ⟨Y, hY, _, mul_mem hw hz.1, mul_assoc _ _ _⟩
  | zero => simp
  | add a b _ _ h h' => rw [add_mul]; exact add_mem h h'
  | smul c a _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

end Alg

theorem local_finite {n : ℕ} {G : Type} [Group G] {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hJ : Jᴴ = J) (hd : IsUnit J.det) (hs : IsMulOn J s) {x y : Fin n → ℂ} (hxx : (star x ᵥ* J) ⬝ᵥ x = 0)
    (hyy : (star y ᵥ* J) ⬝ᵥ y = 0) (hxy : (star x ᵥ* J) ⬝ᵥ y = 1) (N : Subgroup G)
    (hN : ∀ u, IsUni J u → u - 1 ∈ nilRad J x → s u ∈ N)
    (hG : ∀ a : G, ∃ u b, IsUni J u ∧ (∀ v, IsUni J v → b * s v = s v * b) ∧ a = s u * b)
    {c : G → ℂ} (hc : c ∈ smLoc J s) (hcN : ∀ ν ∈ N, ∀ g, c (ν * g) = c g)
    (hz : FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z : List (ℝ → G) →₀ ℂ,
      (∀ l ∈ z.support, ∀ γ ∈ l, ∃ Z, IsSkew J Z ∧ γ = lineOf s Z) ∧
      (∀ f ∈ smLoc J s, ∀ a g, wop z (fun x => f (x * a)) g = wop z f (g * a)) ∧ f = wop z c})) :
    FiniteDimensional ℂ (Submodule.span ℂ {f : G → ℂ | ∃ z : ℂ, z ≠ 0 ∧ f = fun g => c (s (torMat J x y z) * g)}) := by
  obtain ⟨ρ, hρ, hder⟩ := GlobalTheory.T.smooth_local_lie_representation n G J s hJ hd hs
  have hyx : (star y ᵥ* J) ⬝ᵥ x = 1 := by rw [form_swap hJ, hxy, star_one]
  have hRT := GlobalTheory.T.right_translation_intertwines_lie n G J s hJ hd hs ρ hder
  have hR : ∀ a : G, ∃ r : Module.End ℂ (smLoc J s), (∀ (f : smLoc J s) (g : G), (r f).1 g = f.1 (g * a)) ∧
      ∀ z ∈ invAlg ρ, r * z = z * r := fun a => by
    obtain ⟨u, b, hu, hb, rfl⟩ := hG a
    obtain ⟨r, h1, h2⟩ := hRT u b hu hb
    exact ⟨r, h1, fun z hz => (mem_invAlg.1 hz).2 r u u⁻¹ (mul_nonsing_inv _ (hu.isUnit hd)) h2⟩
  choose R hR1 hR2 using hR
  have hs1 : s 1 = 1 := by
    have h1 : IsUni J 1 := by simp [IsUni]
    have := hs 1 1 h1 h1
    rw [mul_one] at this
    exact left_eq_mul.1 this
  let c' : smLoc J s := ⟨c, hc⟩
  let Λ : Module.End ℂ (smLoc J s) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun T g => (T (R g c')).1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΛ : ∀ T g, Λ T g = (T (R g c')).1 1 := fun _ _ => rfl
  let κ : Module.End ℂ (smLoc J s) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun T => (T c').1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  set H := ρ (projL J x y) with hH
  set H' := ρ (projL J y x) with hH'
  have hpp : Commute (projL J x y) (projL J y x) := by
    change _ = _
    rw [projL_mul _ _ _ _ hyy, projL_mul _ _ _ _ hxx]
  have hHH : Commute H H' := by
    have := hρ (projL J x y) (projL J y x)
    rw [hpp.eq, sub_self, map_zero] at this
    exact sub_eq_zero.1 this.symm
  have hfin := GlobalTheory.T.integral_module_finite_quotient _ _ _ (invAlg ρ) (leftIdl ρ (nilRad J x : Set _)) H H' κ Λ hHH
    (mul_mem_leftIdl hρ fun Y hY => br_left hxx y hY) (mul_mem_leftIdl hρ fun Y hY => br_right hxx y hY) leftIdl_mul_mem
    (fun i hi => funext fun g => GlobalTheory.T.right_derivative_nil_radical_invariant n G J s hJ hd hs ρ hder x N hN (R g c')
      (fun ν hν g' => by rw [hR1, hR1, mul_assoc]; exact hcN ν hν _) i hi)
    ((GlobalTheory.T.integral_module_rank_one_right n _ ρ hρ x _ hyx).mono (leftIdl_mono fun _ ⟨ψ, h, e⟩ => e ▸ row_mem hxx h))
    ((GlobalTheory.T.integral_module_rank_one_left n _ ρ hρ y _ hxy).mono (leftIdl_mono fun _ ⟨u, h, e⟩ => e ▸ col_mem hxx h))
    (Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {f | ∃ z : List (ℝ → G) →₀ ℂ,
      (∀ l ∈ z.support, ∀ γ ∈ l, ∃ Z, IsSkew J Z ∧ γ = lineOf s Z) ∧
      (∀ f ∈ smLoc J s, ∀ a g, wop z (fun x => f (x * a)) g = wop z f (g * a)) ∧ f = wop z c}) (by
        rintro _ ⟨T, hT, rfl⟩
        obtain ⟨z, h1, h2⟩ := GlobalTheory.T.enveloping_algebra_line_words n G J s hJ hd hs ρ hder T hT.1
        refine Submodule.subset_span ⟨z, h1, fun f hf a g => ?_, h2 c'⟩
        have e : (fun x => f (x * a)) = (R a ⟨f, hf⟩).1 := funext fun g => (hR1 a ⟨f, hf⟩ g).symm
        rw [e, ← h2, ← h2 ⟨f, hf⟩, ← hR1, ← Module.End.mul_apply, ← hR2 a T hT, Module.End.mul_apply]))
    (fun z hz h0 T => funext fun g => by
      have h0' : z c' = 0 := Subtype.ext h0
      rw [hΛ, Module.End.mul_apply, ← Module.End.mul_apply z, ← hR2 g z hz, Module.End.mul_apply, h0', map_zero, map_zero]
      rfl)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun p : ℕ × ℕ => Λ (H ^ p.1 * H' ^ p.2)))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz0, rfl⟩
  obtain ⟨hZ, hexp⟩ := GlobalTheory.T.torus_exponential_projection n J hJ x y hxx hyy hxy (Complex.log z)
  rw [Complex.exp_log hz0] at hexp
  set ζ := Complex.log z
  set Z := ζ • projL J x y - star ζ • projL J y x with hZdef
  have hcomm : ∀ (t : ℝ) (p : ℕ × ℕ), R (lineOf s Z t) * (H ^ p.1 * H' ^ p.2) = (H ^ p.1 * H' ^ p.2) * R (lineOf s Z t) := by
    intro t p
    obtain ⟨r, h1, h2⟩ := hRT _ 1 (hZ.exp hd t) fun v _ => by rw [one_mul, mul_one]
    have e : R (lineOf s Z t) = r := LinearMap.ext fun f => Subtype.ext (funext fun g => by rw [hR1, h1, mul_one]; rfl)
    have key : ∀ X, Commute X Z → Commute r (ρ X) := fun X hX => by
      have : Commute (NormedSpace.exp (t • Z)) X := (hX.symm.smul_left t).exp_left
      have h3 := h2 X
      rwa [this.eq, mul_nonsing_inv_cancel_right _ _ ((hZ.exp hd t).isUnit hd)] at h3
    rw [e]
    exact (((key _ (((Commute.refl _).smul_right _).sub_right (hpp.smul_right _))).pow_right _).mul_right
      ((key _ ((hpp.symm.smul_right _).sub_right ((Commute.refl _).smul_right _))).pow_right _)).eq
  have hval : ∀ (T : Module.End ℂ (smLoc J s)) (t : ℝ) (g : G), R (lineOf s Z t) * T = T * R (lineOf s Z t) →
      Λ T (lineOf s Z t * g) = (T (R g c')).1 (1 * lineOf s Z t) := fun T t g hT => by
    have e : R (lineOf s Z t * g) c' = R (lineOf s Z t) (R g c') :=
      Subtype.ext (funext fun g' => by rw [hR1, hR1, hR1, mul_assoc])
    rw [hΛ, e, ← Module.End.mul_apply, ← hT, Module.End.mul_apply, hR1]
  have hρZ : ∀ p : ℕ × ℕ, ρ Z * (H ^ p.1 * H' ^ p.2) =
      ζ • (H ^ (p.1 + 1) * H' ^ p.2) - star ζ • (H ^ p.1 * H' ^ (p.2 + 1)) := fun p => by
    rw [hZdef, map_sub, map_smul, map_smul, ← hH, ← hH', sub_mul, smul_mul_assoc, smul_mul_assoc, ← mul_assoc, ← pow_succ',
      ← mul_assoc, (hHH.symm.pow_right _).eq, mul_assoc, ← pow_succ']
  have h1 := GlobalTheory.T.finite_dim_translation_invariant G _ (lineOf s Z) hfin (by simp [lineOf, hs1]) (fun ψ hψ => by
    induction hψ using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨p, rfl⟩ := hψ
      refine ⟨Λ (ρ Z * (H ^ p.1 * H' ^ p.2)), ?_, fun g t => ?_⟩
      · rw [hρZ, map_sub, map_smul, map_smul]
        exact sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(p.1 + 1, p.2), rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(p.1, p.2 + 1), rfl⟩))
      · have e : R (lineOf s Z t) * (ρ Z * (H ^ p.1 * H' ^ p.2)) = (ρ Z * (H ^ p.1 * H' ^ p.2)) * R (lineOf s Z t) := by
          rw [hρZ, mul_sub, sub_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
            hcomm t (p.1 + 1, p.2), hcomm t (p.1, p.2 + 1)]
        rw [hval _ t g e]
        simp only [fun τ => hval _ τ g (hcomm τ p)]
        exact hder Z hZ _ 1 t
    | zero => exact ⟨0, zero_mem _, fun g t => hasDerivAt_const t (0 : ℂ)⟩
    | add a b _ _ h h' =>
      obtain ⟨a', ha, e⟩ := h
      obtain ⟨b', hb, e'⟩ := h'
      exact ⟨a' + b', add_mem ha hb, fun g t => (e g t).add (e' g t)⟩
    | smul k a _ h =>
      obtain ⟨a', ha, e⟩ := h
      exact ⟨k • a', Submodule.smul_mem _ k ha, fun g t => (e g t).const_mul k⟩)
    (Λ (H ^ 0 * H' ^ 0)) (Submodule.subset_span ⟨(0, 0), rfl⟩) 1
  refine Set.mem_of_eq_of_mem (funext fun g => ?_) h1
  rw [hΛ, pow_zero, pow_zero, mul_one, Module.End.one_apply, hR1, one_mul, lineOf, one_smul, hexp]

end GlobalTheory.TorFin
end

noncomputable section
namespace GlobalTheory.TorFin
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.Orb (archMat)
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem exists_section (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} (τ : EmbOver E w) :
    (J.map τ.1)ᴴ = J.map τ.1 ∧ IsUnit (J.map τ.1).det ∧ ∃ s : Matrix (Fin n) (Fin n) ℂ → GAd σ J,
      (∀ y, s (archMat σ J τ y) = embArch σ J w y) ∧ (∀ y, IsUni (J.map τ.1) (archMat σ J τ y)) ∧
        ∀ u, IsUni (J.map τ.1) u → ∃ y, archMat σ J τ y = u := by
  classical
  have inj : Function.Injective (archMat σ J τ) := fun a b e => by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at e
    exact (archEquiv J h τ).injective (Subtype.ext (Units.ext e))
  have hd : IsUnit (J.map τ.1).det := by
    rw [show (J.map τ.1).det = τ.1 J.det from (RingHom.map_det τ.1 J).symm]
    exact ((map_ne_zero τ.1).2 hJ.2).isUnit
  refine ⟨Matrix.ext fun i j => ?_, hd, fun u => if hu : ∃ y, archMat σ J τ y = u then embArch σ J w hu.choose else 1,
    fun y => ?_, fun y => (archEquiv J h τ y).2, fun u hu => ?_⟩
  · rw [conjTranspose_apply, map_apply, map_apply, ← hJ.1 i j]
    exact (h.2.2.2 _ _).symm
  · have hu : ∃ y', archMat σ J τ y' = archMat σ J τ y := ⟨y, rfl⟩
    simp only [dif_pos hu]
    rw [inj hu.choose_spec]
  · refine ⟨(archEquiv J h τ).symm ⟨Matrix.nonsingInvUnit u (hu.isUnit hd), hu⟩, ?_⟩
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]
    rfl

theorem place_finite (h : IsCMExt F E σ) (hJ : IsHermND σ J) (x : Fin n → E) {w : InfinitePlace F} (τ : EmbOver E w)
    {y : Fin n → ℂ} (hxx : (star (fun i => τ.1 (x i)) ᵥ* J.map τ.1) ⬝ᵥ (fun i => τ.1 (x i)) = 0)
    (hyy : (star y ᵥ* J.map τ.1) ⬝ᵥ y = 0) (hxy : (star (fun i => τ.1 (x i)) ᵥ* J.map τ.1) ⬝ᵥ y = 1)
    {c : GAd σ J → ℂ} (hc : IsSm σ J c)
    (hcN : ∀ ν ∈ unipRad σ J (Matrix.of fun i (_ : Fin 1) => x i), ∀ g, c (ν * g) = c g)
    (hz : FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z c})) :
    FiniteDimensional ℂ (Submodule.span ℂ {f : GAd σ J → ℂ | ∃ a ∈ {a | ∃ (b : GArch σ J w) (z : ℂ), z ≠ 0 ∧
      archMat σ J τ b = torMat (J.map τ.1) (fun i => τ.1 (x i)) y z ∧ a = embArch σ J w b}, f = fun g => c (a * g)}) := by
  obtain ⟨h1, hd, s, hs1, hs2, hs3⟩ := exists_section h hJ τ
  have hs : IsMulOn (J.map τ.1) s := fun a b ha hb => by
    obtain ⟨a, rfl⟩ := hs3 a ha
    obtain ⟨b, rfl⟩ := hs3 b hb
    rw [← map_mul, hs1, hs1, hs1, map_mul]
  have hline : ∀ Z, IsSkew (J.map τ.1) Z → IsRealLine σ J (lineOf s Z) := fun Z hZ =>
    ⟨w, τ, Z, hZ, fun t => by
      obtain ⟨b, hb⟩ := hs3 _ (hZ.exp hd t)
      exact ⟨b, by rw [lineOf, ← hb, hs1], hb⟩⟩
  have hsm : ∀ f, IsSm σ J f → f ∈ smLoc (J.map τ.1) s := fun f hf k Z hZ g =>
    hf k (fun i => lineOf s (Z i)) (fun i => hline _ (hZ i)) g
  have := local_finite h1 hd hs hxx hyy hxy (unipRad σ J (Matrix.of fun i (_ : Fin 1) => x i))
    (fun u hu hu' => by
      obtain ⟨b, rfl⟩ := hs3 u hu
      rw [hs1]
      exact GlobalTheory.T.arch_unipotent_radical_mem F E σ h n J hJ x w τ b hu')
    (fun a => ⟨archMat σ J τ (projArch σ J w a), (embArch σ J w (projArch σ J w a))⁻¹ * a, hs2 _, fun v hv => by
      obtain ⟨b, rfl⟩ := hs3 v hv
      rw [hs1]
      exact (commute_embArch σ J b (by simp)).eq.symm, by rw [hs1, mul_inv_cancel_left]⟩)
    (hsm c hc) hcN
    (Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z c})
      (Submodule.span_mono fun f ⟨z, hz1, hz2, e⟩ => ⟨z, ⟨fun l hl γ hγ => by
        obtain ⟨Z, hZ, rfl⟩ := hz1 l hl γ hγ
        exact hline Z hZ, fun f hf a _ g => hz2 f (hsm f hf) a g⟩, e⟩))
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {f : GAd σ J → ℂ | ∃ z : ℂ, z ≠ 0 ∧
    f = fun g => c (s (torMat (J.map τ.1) (fun i => τ.1 (x i)) y z) * g)}) (Submodule.span_mono ?_)
  rintro _ ⟨_, ⟨b, z, hz0, hb, rfl⟩, rfl⟩
  exact ⟨z, hz0, by rw [← hb, hs1]⟩

omit [NumberField E] in

theorem prod_embArch {m : GAd σ J} (hm : m ∈ infPts σ J) :
    (((Finset.univ : Finset (InfinitePlace F)).toList).map fun w => embArch σ J w (projArch σ J w m)).prod = m := by
  classical
  have key : ∀ (l : List (InfinitePlace F)), l.Nodup → ∀ u,
      projArch σ J u (l.map fun w => embArch σ J w (projArch σ J w m)).prod = if u ∈ l then projArch σ J u m else 1 := by
    intro l hl u
    induction l with
    | nil => simp
    | cons w l ih =>
      rw [List.map_cons, List.prod_cons, map_mul, ih hl.of_cons]
      by_cases e : u = w
      · subst e
        simp [hl.notMem]
      · simp [projArch_embArch_ne σ J e, e]
  refine GAd_ext σ J (fun u => by rw [key _ (Finset.nodup_toList _), if_pos (by simp)]) fun v => ?_
  rw [mem_infPts_iff_forall.1 hm v, map_list_prod, List.map_map]
  exact List.prod_eq_one fun _ h => by
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 h
    simp

end GlobalTheory.TorFin
end

noncomputable section
namespace GlobalTheory.TorFin
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

theorem levi_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {i₀ i₁ : ℕ}
    (hA : H'.IsAdapted σ B G.W W₁ i₀ i₁) (t s : (AE F E)ˣ) :
    leviElt σ G.W W₁ H' (t * s) = leviElt σ G.W W₁ H' t * leviElt σ G.W W₁ H' s := by
  have ex := fun t => GlobalTheory.LeviPlane.levi_exists F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA t
  obtain ⟨t1, t2, t3⟩ := isLevi_leviElt (ex t)
  obtain ⟨s1, s2, s3⟩ := isLevi_leviElt (ex s)
  have hm : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g g' : UA σ J), mat (g * g') = mat g * mat g' := fun _ _ => rfl
  refine GlobalTheory.T.levi_element_unique F E σ B _ _ _ G.W hT.geo.hW d₁ W₁ H' i₀ i₁ hA (t * s) _ _ (isLevi_leviElt (ex (t * s))) ⟨?_, ?_, ?_⟩
  · rw [hm, ← Matrix.mulVec_mulVec, s1, Matrix.mulVec_smul, t1, smul_smul, Units.val_mul, mul_comm]
  · rw [hm, ← Matrix.mulVec_mulVec, s2, Matrix.mulVec_smul, t2, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [hm, Matrix.mul_assoc, s3, ← Matrix.mul_assoc, t3, Matrix.mul_assoc, ← hm, mul_one]

theorem ctLevi_arch_finite : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ f : UA σ G.W.J → ℂ, (∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧ IsAut σ (c • G.W.J.map σ) K (fun x => f ((toGAd hσ G.W.J hc).symm x))) → ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun a : idelesInf F E => fun a' : idelesInf F E => ctLevi σ G.W W₁ H' μ 𝓕 f h ((a' : (AE F E)ˣ) * a))) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH hσ c hc hcs f hf μ 𝓕 hμ h𝓕 h1 h
  obtain ⟨K, -, hA⟩ := hf
  have hcm := hT.base.cm
  have hJ := GlobalTheory.CtLeviCont.isHermND_smul σ B G.W hT.geo.hW hσ c hc hcs
  have hC := GlobalTheory.CtLeviCont.isIsoCols_plane σ B G.W W₁ H' hH hσ c
  obtain ⟨cc, hcc, -⟩ := existsUnique_isConstTerm hcm hJ hC (isAut_iff_isAutOn.1 hA).left
  have hct := GlobalTheory.T.unipotent_fundamental_domain_integral F E σ B hcm _ _ _ G.W hT.geo.hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH f μ 𝓕 hμ h𝓕 h1 cc hcc
  have haut := (GlobalTheory.T.automorphic_constant_term_parabolic F E σ hcm _ _ hJ 1 _ (fun _ => 0) hC _ K _ cc inf_le_left (isAut_iff_isAutOn.1 hA)
    (isConstTerm_iff_unipFlag.1 hcc)).1
  have hτ : ∀ w : InfinitePlace F, Nonempty (EmbOver E w) := fun w => inferInstance
  let τ : ∀ w : InfinitePlace F, EmbOver E w := fun w => (hτ w).some
  let T : InfinitePlace F → Set (GAd σ (c • G.W.J.map σ)) := fun w => {a | ∃ (b : GArch σ (c • G.W.J.map σ) w) (z : ℂ), z ≠ 0 ∧
      GlobalTheory.Orb.archMat σ _ (τ w) b = torMat ((c • G.W.J.map σ).map (τ w).1) (fun i => (τ w).1 (H'.x i))
        (fun i => (τ w).1 (c⁻¹ * H'.y i)) z ∧ a = embArch σ _ w b}
  have hfin := GlobalTheory.T.finite_dim_product_translates _ _ T cc
    (by
      rintro i j hij _ ⟨b, -, -, -, rfl⟩ _ ⟨b', -, -, -, rfl⟩
      exact (commute_embArch σ _ b (projArch_embArch_ne σ _ hij b')).eq)
    (fun w => by
      obtain ⟨e1, e2, e3⟩ := GlobalTheory.T.skew_hermitian_norm_adapted_pos F E σ B hcm _ _ _ G.W hT.geo.hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH (τ w).1
      exact place_finite hcm hJ H'.x (τ w) e1 e2 e3 haut.smooth
        (fun ν hν => haut.left ν (Subgroup.mem_sup_left (by rwa [unipFlag_const]))) haut.zfin)
    _ (Finset.nodup_toList Finset.univ)
  let L : (GAd σ (c • G.W.J.map σ) → ℂ) →ₗ[ℂ] (idelesInf F E → ℂ) :=
    LinearMap.funLeft ℂ ℂ fun a' => toGAd hσ G.W.J hc (leviElt σ G.W W₁ H' a' * h)
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ {f : GAd σ (c • G.W.J.map σ) → ℂ |
    ∃ a : InfinitePlace F → GAd σ (c • G.W.J.map σ), (∀ i, a i ∈ T i) ∧
      f = fun g => cc ((Finset.univ.toList.map a).prod * g)}).map L) (Submodule.span_le.2 ?_)
  rintro _ ⟨t, rfl⟩
  obtain ⟨hi, hz⟩ := GlobalTheory.T.levi_element_infinite_points F E σ B hcm _ _ _ G.W hT.geo.hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH t.1 t.2
  refine ⟨_, Submodule.subset_span ⟨fun w => embArch σ _ w (projArch σ _ w (toGAd hσ G.W.J hc (leviElt σ G.W W₁ H' t))),
    fun w => ?_, rfl⟩, funext fun t' => ?_⟩
  · obtain ⟨z, hz0, e⟩ := hz w (τ w)
    exact ⟨_, z, hz0, e, rfl⟩
  · rw [prod_embArch hi]
    change cc (_ * toGAd hσ G.W.J hc (leviElt σ G.W W₁ H' t' * h)) = ctLevi σ G.W W₁ H' μ 𝓕 f h (t'.1 * t.1)
    rw [ctLevi_apply, hct, mul_comm t'.1, levi_mul hT hH, mul_assoc, map_mul (toGAd hσ G.W.J hc) (leviElt σ G.W W₁ H' t)]

end GlobalTheory.TorFin
end
