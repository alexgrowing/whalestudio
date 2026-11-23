import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsLast

noncomputable section

namespace GlobalTheory.TwU.KerMove

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Mv
open Formalism.L2.KerInert Formalism.L2.KerInert.PullbackComparison Formalism.L2.KerInert.RepComb
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abs

variable {V : Type} [AddCommGroup V] [Module ℂ V] [DecidableEq V] (H : Sesq V) (α : V → ℂ) (T : V ≃+ V)

theorem brk_map (hH : ∀ x y, H (T x) (T y) = H x y) (y t : V) : brk H (T y) (T t) = brk H y t := by
  unfold brk altE
  rw [hH]

theorem hatS_map (hH : ∀ x y, H (T x) (T y) = H x y) (vol : ℝ) (SA : Finset V) (Φ : V → ℂ) (x y : V) :
    hatS H vol (SA.image T) (fun s => Φ (s - T x)) (T y) = hatS H vol SA (fun s => Φ (T (s - x))) y := by
  unfold hatS
  rw [Finset.card_image_of_injective _ T.injective, Finset.sum_image (fun a _ b _ h => T.injective h)]
  congr 2
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [brk_map H T hH]
  simp only [map_sub]

theorem opU_map (hH : ∀ x y, H (T x) (T y) = H x y) (x : V) (e : V → ℂ) (z : V) :
    opU H (T x) e (T z) = opU H x (fun v => e (T v)) z := by
  unfold opU
  rw [hH, hH, ← map_add]

theorem xiL_map (hH : ∀ x y, H (T x) (T y) = H x y) (hα : ∀ x, α (T x) = α x) (vol : ℝ) (SX SA SB : Finset V) (Φ e : V → ℂ) (z : V) :
    xiL H α vol (SX.image T) (SA.image T) (SB.image T) Φ e (T z) =
      xiL H α vol SX SA SB (fun v => Φ (T v)) (fun v => e (T v)) z := by
  rw [xiL_expand, xiL_expand, Finset.sum_image (fun a _ b _ h => T.injective h)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_image (fun a _ b _ h => T.injective h)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hatS_map H T hH, hα, hα, hH, hH, ← map_add, opU_map H T hH]

theorem isReps_image {Λ₁ Λ₂ M₁ M₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) (h1 : ∀ x, T x ∈ M₁ ↔ x ∈ Λ₁)
    (h2 : ∀ x, T x ∈ M₂ ↔ x ∈ Λ₂) : IsReps M₁ M₂ (S.image T) := by
  first
  | exact @_root_.GlobalTheory.TransportLemma.main
  | exact _root_.GlobalTheory.TransportLemma.main
  | (apply _root_.GlobalTheory.TransportLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.TransportLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TransportLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TransportLemma.main ..)

omit [DecidableEq V] in

theorem repsOf_of_exists {Λ₁ Λ₂ : AddSubgroup V} (h : ∃ S, IsReps Λ₁ Λ₂ S) : IsReps Λ₁ Λ₂ (repsOf Λ₁ Λ₂) := by
  unfold repsOf
  exact Classical.epsilon_spec h

theorem xiL_transport {A B Λ A₁ B₁ Λ₁ : AddSubgroup V} (hyp : SplitHyp H α A B Λ) (hH : ∀ x y, H (T x) (T y) = H x y)
    (hα : ∀ x, α (T x) = α x) (hΛ : ∀ x, T x ∈ Λ ↔ x ∈ Λ₁) (hA : ∀ x, T x ∈ A ↔ x ∈ A₁) (hB : ∀ x, T x ∈ B ↔ x ∈ B₁)
    {SX SA SB SX₁ SA₁ SB₁ : Finset V} (hSX : IsReps Λ A SX) (hSA : IsReps B (Λ ⊓ A) SA) (hSB : IsReps Λ B SB)
    (hSX₁ : IsReps Λ₁ A₁ SX₁) (hSA₁ : IsReps B₁ (Λ₁ ⊓ A₁) SA₁) (hSB₁ : IsReps Λ₁ B₁ SB₁) (vol : ℝ)
    {θ : V → ℂ} (hθ : θ ∈ fixedBy H α Λ) {Φ : V → ℂ} (hΦ : InvOn A B Φ) (z : V) :
    xiL H α vol SX₁ SA₁ SB₁ (fun v => Φ (T v)) (fun v => θ (T v)) z = xiL H α vol SX SA SB Φ θ (T z) := by
  have hΛA : ∀ x, T x ∈ Λ ⊓ A ↔ x ∈ Λ₁ ⊓ A₁ := fun x => by
    rw [AddSubgroup.mem_inf, AddSubgroup.mem_inf, hΛ, hA]
  rw [← xiL_map H α T hH hα]
  exact twist_representatives V H α A B Λ hyp SX SA SB _ _ _ hSX hSA hSB (isReps_image T hSX₁ hΛ hA)
    (isReps_image T hSA₁ hB hΛA) (isReps_image T hSB₁ hΛ hB) vol θ hθ Φ hΦ (T z)

theorem exists_reps_symm {Λ₁ Λ₂ M₁ M₂ : AddSubgroup V} {S : Finset V} (hS : IsReps M₁ M₂ S) (h1 : ∀ x, T x ∈ M₁ ↔ x ∈ Λ₁)
    (h2 : ∀ x, T x ∈ M₂ ↔ x ∈ Λ₂) : ∃ S₁, IsReps Λ₁ Λ₂ S₁ := by
  refine ⟨S.image T.symm, isReps_image T.symm hS (fun x => ?_) (fun x => ?_)⟩
  · rw [← h1, AddEquiv.apply_symm_apply]
  · rw [← h2, AddEquiv.apply_symm_apply]

end Abs

section Conc

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {a b : ℕ}

theorem tPull_tPull (e g : Matrix (Fin a) (Fin a) D.host.E) (e' g' : Matrix (Fin b) (Fin b) D.host.E) (z : TaylorLogMetric.VC D a b) :
    tPull D (TaylorLogMetric.tor0 D cc δ) g g' (tPull D (TaylorLogMetric.tor0 D cc δ) e e' z) = tPull D (TaylorLogMetric.tor0 D cc δ) (e * g) (e' * g') z := by
  funext τ
  show (Matrix.conjTranspose (g'.map (TaylorLogMetric.embT D τ)) * (Matrix.conjTranspose (e'.map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) *
      e.map (TaylorLogMetric.embT D τ)) * g.map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ) =
    Matrix.conjTranspose ((e' * g').map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * (e * g).map (TaylorLogMetric.embT D τ)
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem tPull_one (z : TaylorLogMetric.VC D a b) :
    tPull D (TaylorLogMetric.tor0 D cc δ) (1 : Matrix (Fin a) (Fin a) D.host.E) (1 : Matrix (Fin b) (Fin b) D.host.E) z = z := by
  funext τ
  show (Matrix.conjTranspose ((1 : Matrix (Fin b) (Fin b) D.host.E).map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) *
      (1 : Matrix (Fin a) (Fin a) D.host.E).map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ) = Matrix.of (z τ)
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]

variable (cc δ) in

def TT (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (he : e * star e = 1) (he' : e' * star e' = 1) :
    TaylorLogMetric.VC D a b ≃+ TaylorLogMetric.VC D a b where
  toFun := tPull D (TaylorLogMetric.tor0 D cc δ) e e'
  invFun := tPull D (TaylorLogMetric.tor0 D cc δ) (star e) (star e')
  left_inv := fun z => by rw [tPull_tPull, he, he', tPull_one]
  right_inv := fun z => by rw [tPull_tPull, mul_eq_one_comm.1 he, mul_eq_one_comm.1 he', tPull_one]
  map_add' := tPull_add cc δ e e'

theorem TT_apply (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (he : e * star e = 1)
    (he' : e' * star e' = 1) (z : TaylorLogMetric.VC D a b) : TT cc δ e e' he he' z = tPull D (TaylorLogMetric.tor0 D cc δ) e e' z := rfl

theorem hK_eq_Hf (z w : TaylorLogMetric.VC D a b) : hK D cc δ a b z w = TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z w := by
  simp only [TaylorLogMetric.Hf, TaylorLogMetric.tor0, hK, HV, LinearMap.mk₂'ₛₗ_apply]
  push_cast
  ring

theorem hK_TT (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (he : e * star e = 1)
    (he' : e' * star e' = 1) (x y : TaylorLogMetric.VC D a b) :
    hK D cc δ a b (TT cc δ e e' he he' x) (TT cc δ e e' he he' y) = hK D cc δ a b x y := by
  rw [hK_eq_Hf, hK_eq_Hf]
  exact Hf_tPull cc δ e e' he he' x y

theorem alK_TT (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (he : e * star e = 1)
    (he' : e' * star e' = 1) (x : TaylorLogMetric.VC D a b) :
    alK D cc δ a b (TT cc δ e e' he he' x) = alK D cc δ a b x := by
  have h := hK_TT (cc := cc) (δ := δ) e e' he he' x x
  unfold hK at h
  simp only [alK, alV, alphaQ, qOf, h]

def RR (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) :
    Formalism.L2.Col.HomE D.host.E a b →ₗ[D.host.E] Formalism.L2.Col.HomE D.host.E a b where
  toFun x := Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e
  map_add' x y := by
    refine LinearMap.ext fun v => ?_
    simp [Matrix.mulVec_add]
  map_smul' c x := by
    refine LinearMap.ext fun v => ?_
    simp

theorem RR_apply (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (x : Formalism.L2.Col.HomE D.host.E a b) :
    RR e e' x = Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e := rfl

theorem matH_RR (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (x : Formalism.L2.Col.HomE D.host.E a b) :
    RepComb.matH (RR e e' x) = star e' * RepComb.matH x * e := by
  refine Matrix.ext fun i j => ?_
  show Matrix.toLin' (star e') (x (Matrix.toLin' e (Pi.single j 1))) i = _
  rw [← RepComb.matH_mulVec x, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_single_one]
  rfl

theorem tPull_embH (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (x : Formalism.L2.Col.HomE D.host.E a b) :
    tPull D (TaylorLogMetric.tor0 D cc δ) e e' (embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ x) =
      embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (RR e e' x) := by
  funext τ i j
  have h1 : (Matrix.of (fun i j => δ * TaylorLogMetric.embT D τ (RepComb.matH x i j)) : Matrix (Fin b) (Fin a) ℂ) =
      δ • (RepComb.matH x).map (TaylorLogMetric.embT D τ) := by
    ext i j; rfl
  show (Matrix.conjTranspose (e'.map (TaylorLogMetric.embT D τ)) * Matrix.of (fun i j => δ * TaylorLogMetric.embT D τ (RepComb.matH x i j)) *
    e.map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ) i j = δ * TaylorLogMetric.embT D τ (RepComb.matH (RR e e' x) i j)
  rw [h1, matH_RR, ← Matrix.star_eq_conjTranspose, PullbackComparison.map_star, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul,
    ← Matrix.map_mul]
  rfl

section Map

variable {W : Type} [AddCommGroup W] [Module D.host.E W] [Module (𝓞 D.host.E) W] [IsScalarTower (𝓞 D.host.E) D.host.E W]
  (f : W →ₗ[D.host.E] W)

theorem localization_map₂ (M M' : Submodule (𝓞 D.host.E) W) (hM : ∀ x ∈ M, f x ∈ M') (Q : HeightOneSpectrum (𝓞 D.host.E)) (x : W)
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M) : f x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M' := by
  obtain ⟨s, hs, h⟩ := hx
  refine ⟨s, hs, ?_⟩
  have := hM _ h
  rwa [← LinearMap.coe_restrictScalars (𝓞 D.host.E) f, map_smul] at this

theorem twO_map (M M' : Submodule (𝓞 D.host.E) W) (hM : ∀ x ∈ M, f x ∈ M') (c : ℕ) (ex : HeightOneSpectrum (𝓞 D.host.E) → ℤ) (x : W)
    (hx : x ∈ twist₂ M c ex) : f x ∈ twist₂ M' c ex := by
  rw [mem_twO] at hx ⊢
  intro Q
  rw [← map_smul]
  exact localization_map₂ f M M' hM Q _ (hx Q)

end Map

theorem perO_map (AA0 : Submodule (𝓞 D.host.E) D.host.E) (N₁ N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a))
    (N₁' N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)) (f : Formalism.L2.Col.HomE D.host.E a b →ₗ[D.host.E] Formalism.L2.Col.HomE D.host.E a b)
    (hf : ∀ x ∈ homO N₁ N₁', f x ∈ homO N N') (x : Formalism.L2.Col.HomE D.host.E a b) (hx : x ∈ perO AA0 N₁ N₁') :
    f x ∈ perO AA0 N N' := by
  have h : (perO AA0 N₁ N₁').map (f.restrictScalars (𝓞 D.host.E)) ≤ perO AA0 N N' := by
    unfold perO
    rw [Submodule.map_span_le]
    rintro z ⟨r, hr, y, hy, rfl⟩
    refine Submodule.subset_span ⟨r, hr, f y, hf y hy, ?_⟩
    rw [LinearMap.coe_restrictScalars, map_smul]
  exact h (Submodule.mem_map_of_mem hx)

theorem homO_RR (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (he' : e' * star e' = 1)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)) (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b))
    (x : Formalism.L2.Col.HomE D.host.E a b) (hx : x ∈ homO (SDLat.smulLat e N) (SDLat.smulLat e' N')) : RR e e' x ∈ homO N N' := by
  intro y hy
  obtain ⟨n', hn', h⟩ := hx (Matrix.toLin' e y) ⟨y, hy, rfl⟩
  rw [RR_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  change Matrix.toLin' e' n' = x (Matrix.toLin' e y) at h
  rw [← h, ← LinearMap.comp_apply, ← Matrix.toLin'_mul, mul_eq_one_comm.1 he', Matrix.toLin'_one, LinearMap.id_apply]
  exact hn'

theorem homO_RR_inv (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (he : e * star e = 1)
    (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)) (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b))
    (x : Formalism.L2.Col.HomE D.host.E a b) (hx : x ∈ homO N N') :
    RR (star e) (star e') x ∈ homO (SDLat.smulLat e N) (SDLat.smulLat e' N') := by
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨x n, hx n hn, ?_⟩
  change Matrix.toLin' e' (x n) = Matrix.toLin' (star (star e')) (x (Matrix.toLin' (star e) (Matrix.toLin' e n)))
  rw [star_star, ← LinearMap.comp_apply (Matrix.toLin' (star e)), ← Matrix.toLin'_mul, mul_eq_one_comm.1 he, Matrix.toLin'_one,
    LinearMap.id_apply]

theorem laV_RR (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E)
    (M₁ M : Submodule (𝓞 D.host.E) (Formalism.L2.Col.HomE D.host.E a b)) (hM : ∀ x ∈ M₁, RR e e' x ∈ M) (v : TaylorLogMetric.VC D a b)
    (hv : v ∈ laV (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ M₁) :
    tPull D (TaylorLogMetric.tor0 D cc δ) e e' v ∈ laV (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ M := by
  obtain ⟨x, hx, rfl⟩ := hv
  exact ⟨RR e e' x, hM x hx, (tPull_embH e e' x).symm⟩

theorem TT_mem_iff (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (he : e * star e = 1)
    (he' : e' * star e' = 1) (M₁ M : Submodule (𝓞 D.host.E) (Formalism.L2.Col.HomE D.host.E a b))
    (hM : ∀ x ∈ M₁, RR e e' x ∈ M) (hM' : ∀ x ∈ M, RR (star e) (star e') x ∈ M₁) (v : TaylorLogMetric.VC D a b) :
    TT cc δ e e' he he' v ∈ laV (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ M ↔
      v ∈ laV (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ M₁ := by
  constructor
  · intro h
    have h1 := laV_RR (cc := cc) (star e) (star e') M M₁ hM' _ h
    have h2 : tPull D (TaylorLogMetric.tor0 D cc δ) (star e) (star e') (TT cc δ e e' he he' v) = v :=
      (TT cc δ e e' he he').left_inv v
    rwa [h2] at h1
  · exact laV_RR e e' M₁ M hM v

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩

theorem onV_embH (hδ0 : δ ≠ 0) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (x : Formalism.L2.Col.HomE D.host.E a b) :
    onV (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ Ξ (embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ x) = Ξ x := by
  have := tau_nonempty D
  have h : ∃ y, embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ y = embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ x := ⟨x, rfl⟩
  unfold onV
  rw [dif_pos h]
  exact congrArg Ξ (embH_inj _ hδ0 h.choose_spec)

theorem onV_TT (hδ0 : δ ≠ 0) (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (he : e * star e = 1)
    (he' : e' * star e' = 1) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (v : TaylorLogMetric.VC D a b) :
    onV (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (fun x => Ξ (RR e e' x)) v =
      onV (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ Ξ (TT cc δ e e' he he' v) := by
  by_cases h : ∃ x, embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ x = v
  · obtain ⟨x, rfl⟩ := h
    rw [TT_apply, tPull_embH, onV_embH hδ0, onV_embH hδ0]
  · have h2 : ¬ ∃ x, embH (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ x = TT cc δ e e' he he' v := by
      rintro ⟨y, hy⟩
      apply h
      refine ⟨RR (star e) (star e') y, ?_⟩
      rw [← tPull_embH (cc := cc), hy]
      exact (TT cc δ e e' he he').left_inv v
    unfold onV
    rw [dif_neg h, dif_neg h2]

theorem unimod_iff {n : ℕ} (L : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E n)) :
    Formalism.HermitianLatticesTheory.IsUnimodular (Formalism.L2.Col.hStd D.host.E n) L ↔
      ∀ y, y ∈ L ↔ ∀ x ∈ L, stdH D.host.E n x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have hm : ∀ y, y ∈ Formalism.HermitianLatticesTheory.dual (Formalism.L2.Col.hStd D.host.E n) L ↔
      ∀ x ∈ L, stdH D.host.E n x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
      Submodule.mem_one, RingHom.mem_range]
    rfl
  unfold Formalism.HermitianLatticesTheory.IsUnimodular
  constructor
  · intro h y
    rw [← hm y, h]
  · intro h
    ext y
    rw [hm y]
    exact (h y).symm

variable (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
  (N : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)) (N' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b))

theorem admissible_pair_twist (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl) (ex : HeightOneSpectrum (𝓞 D.host.E) → ℤ)
    (h01 : ∀ Q, ex Q = 1 ∨ ex Q = 0 ∨ ex Q = -1) (hc : ∀ Q, ex (Formalism.L2.Col.conjPrime₂ Q) = -ex Q) :
    TaylorLogMetric.admitted D a b N (twist₂ N' cl ex) := by
  have hl := hh_tw_lattice N' ⟨hA.2.2.2.1, hA.2.2.2.2.1⟩ hcl ex h01
  exact ⟨hA.1, hA.2.1, hA.2.2.1, hl.fg, hl.span_eq_top,
    (unimod_iff _).1 (twist_selfDual D.host.E b N' cl ex hA.2.2.2.1 hcl hc ((unimod_iff _).2 hA.2.2.2.2.2))⟩

theorem split_of_adm (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl) (hSS : ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS) :
    SplitHyp (hK D cc δ a b) (alK D cc δ a b) (halfA cc δ SS cl N N') (halfB cc δ SS cl N N') (lamK cc δ N N') := by
  have := tau_nonempty D
  have he1 : ∀ Q, expS SS Q = 1 ∨ expS SS Q = 0 ∨ expS SS Q = -1 := expS_cases SS
  have he2 : ∀ Q, (fun Q => -expS SS Q) Q = 1 ∨ (fun Q => -expS SS Q) Q = 0 ∨ (fun Q => -expS SS Q) Q = -1 := by
    intro Q
    have := he1 Q
    show -expS SS Q = 1 ∨ -expS SS Q = 0 ∨ -expS SS Q = -1
    omega
  have hconj1 : ∀ Q, expS SS (Formalism.L2.Col.conjPrime₂ Q) = -expS SS Q := exponent_set_conjugate D.host.E SS hSS
  have hconj2 : ∀ Q, (fun Q => -expS SS Q) (Formalism.L2.Col.conjPrime₂ Q) = -(fun Q => -expS SS Q) Q := by
    intro Q
    show -expS SS (Formalism.L2.Col.conjPrime₂ Q) = - -expS SS Q
    rw [hconj1 Q]
  exact half_periods_of_lattice D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (aaOf D cc) SS N N' cl
    hδ0 hcl hSS hA.2.2.1.1 (laFacts_of_adm B hcc hδ hA)
    (laFacts_of_adm B hcc hδ (admissible_pair_twist cl N N' hA hcl _ he1 hconj1)) (laFacts_of_adm B hcc hδ (admissible_pair_twist cl N N' hA hcl _ he2 hconj2))

theorem finIdx_of_adm (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl) : FinIdx cc δ SS cl N N' :=
  finite_index_of_fg D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) SS N N' cl hcl
    (period_lattice_finitely_generated D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) N N' hA.2.2.2.1 hA.2.2.1.2.1 (aaOf_fg cc))

theorem eNat_fixed (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (hVec : B.VecP χ) (hA : TaylorLogMetric.admitted D a b N N') :
    B.eNat χ a b N N' ∈ fixedBy (hK D cc δ a b) (alK D cc δ a b) (lamK cc δ N N') := by
  have hm := (hVec a b N N' hA).1
  intro x hx z
  have hx' : x ∈ TaylorLogMetric.La D B.tor N N' := by rw [← lamK_eq cc δ N N']; exact hx
  have h1 := hm.2 x hx' z
  rw [U_eq_opU] at h1
  have hal : alK D cc δ a b x = TaylorLogMetric.al D B.tor x := by
    rw [KS.Lat.al_eq_La B hcc hδ hA x hx']
    unfold alK alV
    rw [HV_eq_formV]
  rw [hal]
  exact h1

theorem kernel_theta_move_local (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hVec : B.VecP χ) (hEq : B.EqP χ) (hcl : 0 < cl) (hSS : ∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS)
    (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (hA : TaylorLogMetric.admitted D a b N N') (hDat : GlobalTheory.TwU.DatLoc D cc SS cl N N' Ξ)
    (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (he : e * star e = 1) (he' : e' * star e' = 1) :
    kerTh B χ SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') (fun x => Ξ (Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e)) =
      TaylorLogMetric.pull D B.tor e e' (kerTh B χ SS cl N N' Ξ) := by
  classical
  have := tau_nonempty D
  have p1 : ∀ x ∈ perO (aaOf D cc) (SDLat.smulLat e N) (SDLat.smulLat e' N'), RR e e' x ∈ perO (aaOf D cc) N N' :=
    perO_map _ _ _ _ _ (RR e e') (homO_RR e e' he' N N')
  have p2 : ∀ x ∈ perO (aaOf D cc) N N', RR (star e) (star e') x ∈ perO (aaOf D cc) (SDLat.smulLat e N) (SDLat.smulLat e' N') :=
    perO_map _ _ _ _ _ (RR (star e) (star e')) (homO_RR_inv e e' he N N')
  have hΛ : ∀ v, TT cc δ e e' he he' v ∈ lamK cc δ N N' ↔ v ∈ lamK cc δ (SDLat.smulLat e N) (SDLat.smulLat e' N') :=
    TT_mem_iff e e' he he' _ _ p1 p2
  have hAh : ∀ v, TT cc δ e e' he he' v ∈ halfA cc δ SS cl N N' ↔ v ∈ halfA cc δ SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') :=
    TT_mem_iff e e' he he' _ _ (twO_map (RR e e') _ _ p1 cl _) (twO_map (RR (star e) (star e')) _ _ p2 cl _)
  have hBh : ∀ v, TT cc δ e e' he he' v ∈ halfB cc δ SS cl N N' ↔ v ∈ halfB cc δ SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') :=
    TT_mem_iff e e' he he' _ _ (twO_map (RR e e') _ _ p1 cl _) (twO_map (RR (star e) (star e')) _ _ p2 cl _)
  have hΛA : ∀ v, TT cc δ e e' he he' v ∈ lamK cc δ N N' ⊓ halfA cc δ SS cl N N' ↔
      v ∈ lamK cc δ (SDLat.smulLat e N) (SDLat.smulLat e' N') ⊓ halfA cc δ SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') := fun v => by
    rw [AddSubgroup.mem_inf, AddSubgroup.mem_inf, hΛ, hAh]
  have hyp := split_of_adm SS cl N N' B hcc hδ hδ0 hA hcl hSS
  have hI := finIdx_of_adm (cc := cc) (δ := δ) SS cl N N' hA hcl
  have hθ := eNat_fixed N N' B χ hcc hδ hVec hA
  have hΦ : InvOn (halfA cc δ SS cl N N') (halfB cc δ SS cl N N') (onV (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ Ξ) :=
    hDat.invOn (fun τ => TaylorLogMetric.embT D τ) δ (embH_inj _ hδ0)
  have hvec : B.eNat χ a b (SDLat.smulLat e N) (SDLat.smulLat e' N') = fun v => B.eNat χ a b N N' (TT cc δ e e' he he' v) :=
    (hEq.1 a b ⟨N, hA.2.2.1⟩ ⟨N', hA.2.2.2⟩ hA.1 hA.2.1 ⟨e, Matrix.mem_unitaryGroup_iff.2 he⟩
      ⟨e', Matrix.mem_unitaryGroup_iff.2 he'⟩).symm
  have hdat : onV (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ (fun x => Ξ (Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e)) =
      fun v => onV (ι := D.what₂.Tau) (fun τ => TaylorLogMetric.embT D τ) δ Ξ (TT cc δ e e' he he' v) :=
    funext (onV_TT hδ0 e e' he he' Ξ)
  funext z
  unfold kerTh thC xiV
  rw [hdat, hvec]
  exact xiL_transport (hK D cc δ a b) (alK D cc δ a b) (TT cc δ e e' he he') hyp (hK_TT e e' he he') (alK_TT e e' he he') hΛ hAh hBh
    (repsOf_spec _ _ hI.1) (repsOf_spec _ _ hI.2.1) (repsOf_spec _ _ hI.2.2)
    (repsOf_of_exists (exists_reps_symm _ (repsOf_spec _ _ hI.1) hΛ hAh))
    (repsOf_of_exists (exists_reps_symm _ (repsOf_spec _ _ hI.2.1) hBh hΛA))
    (repsOf_of_exists (exists_reps_symm _ (repsOf_spec _ _ hI.2.2) hΛ hBh)) 1 hθ hΦ z

end Conc

section Main

open GlobalTheory.TwU TensorProduct

theorem kerTh_move : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → TaylorLogMetric.IsChi D χ → B.LatAll → B.VecP χ → B.EqP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N N' → DatLoc D cc SS cl N N' Ξ → ∀ (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E), e * star e = 1 → e' * star e' = 1 → kerTh B χ SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') (fun x => Ξ (Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e)) = TaylorLogMetric.pull D B.tor e e' (kerTh B χ SS cl N N' Ξ) := by
  intro D cc δ B χ hcc hδ hδ0 hχ _ hVec hEq SS cl hcl hSS a b N N' Ξ hA hDat e e' he he'
  exact kernel_theta_move_local SS cl N N' B χ hcc hδ hδ0 hVec hEq hcl hSS Ξ hA hDat e e' he he'

end Main

end GlobalTheory.TwU.KerMove
