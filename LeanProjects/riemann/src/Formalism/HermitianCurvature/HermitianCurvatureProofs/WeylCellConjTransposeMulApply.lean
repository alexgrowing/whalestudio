import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator

open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.Qx3

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem glev_one (i : Fin (r + 1)) : (1 : Mx k r) ∈ Glev k r i :=
  ⟨WeylGroupFacts.uh_one, fun _ _ => ⟨by simp, by simp⟩⟩

theorem glev_mul {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  refine ⟨WeylGroupFacts.uh_mul hg.1 hh.1, fun a ha => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mulVec_mulVec, (hh.2 a ha).1, (hg.2 a ha).1]
  · rw [← Matrix.mulVec_mulVec, (hh.2 a ha).2, (hg.2 a ha).2]

theorem glev_mono {i j : Fin (r + 1)} (h : j ≤ i) : Glev k r i ⊆ Glev k r j :=
  fun _ hg => ⟨hg.1, fun a ha => hg.2 a (lt_of_lt_of_le ha h)⟩

theorem nlev_mono {i j : Fin (r + 1)} (h : j ≤ i) : Nlev k r i ⊆ Nlev k r j :=
  fun _ hg => ⟨hg.1, glev_mono h hg.2⟩

theorem uw_glev {z : Fin (2 * r + k + 1) → ℂ} (i : Fin (r + 1)) : UWset k r z ⊆ Glev k r i :=
  fun _ hg => ⟨hg.1, fun a _ => hg.2.1 a⟩

def mulVecL (v : Fin (2 * r + k + 1) → ℂ) : Mx k r →L[ℝ] (Fin (2 * r + k + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A *ᵥ v
      map_add' := fun A B => Matrix.add_mulVec A B v
      map_smul' := fun c A => Matrix.smul_mulVec c A v }

theorem exp_fix {X : Mx k r} {v : Fin (2 * r + k + 1) → ℂ} (h : X *ᵥ v = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) *ᵥ v = v := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => mulVecL v ((1 : Mx k r) * NormedSpace.exp ((s : ℂ) • X))) 0 s := by
    intro s
    have h1 := B5.curve_hasDerivAt (1 : Mx k r) X s
    have h2 := (mulVecL v).hasFDerivAt.comp_hasDerivAt s h1
    refine h2.congr_deriv ?_
    show ((1 : Mx k r) * NormedSpace.exp ((s : ℂ) • X) * X) *ᵥ v = 0
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa [mulVecL, NormedSpace.exp_zero] using hc

def LieLev (i : Fin (r + 1)) (X : Mx k r) : Prop := ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i

theorem lieLev_of {i : Fin (r + 1)} {X : Mx k r} (hX : inLieLev k r i X) : LieLev i X :=
  fun t => ⟨B5.exp_mem hX.1 t, fun a ha => ⟨exp_fix (hX.2 a ha).1 t, exp_fix (hX.2 a ha).2 t⟩⟩

theorem hpk_e (a : Fin r) : Hpk k r *ᵥ bvec (eI k r a) = bvec (esI k r a) := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]
  unfold Hpk eI esI
  simp only [Fin.ext_iff]
  have := p.isLt
  have := a.isLt
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_es (a : Fin r) : Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]
  unfold Hpk eI esI
  simp only [Fin.ext_iff]
  have := p.isLt
  have := a.isLt
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_herm : (Hpk k r)ᴴ = Hpk k r := (hermitian_pos_facts_hold k r).1

theorem hpk_inv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_right_inv WeylGroupFacts.hpk_sq

theorem single_bvec {p q c : Fin (2 * r + k + 1)} (h : q ≠ c) :
    (Matrix.single p q (1 : ℂ)) *ᵥ bvec c = 0 := by
  funext x
  simp [bvec, h]

theorem posL_ne_e (i : Fin (r + 1)) (a : Fin (mdim k r i)) (b : Fin r) (hb : b.val < i.val) :
    posL k r i a ≠ eI k r b ∧ posL k r i a ≠ esI k r b := by
  have h1 := a.isLt
  have h2 := i.isLt
  unfold mdim at h1
  simp only [posL, eI, esI, ne_eq, Fin.ext_iff]
  omega

theorem hpart_skew {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hsq : H * H = 1) (hh : Hᴴ = H) :
    (hpart1 H Z)ᴴ * H + H * hpart1 H Z = 0 ∧ (hpart2 H Z)ᴴ * H + H * hpart2 H Z = 0 := by
  have hinv : H⁻¹ = H := Matrix.inv_eq_right_inv hsq
  have e1 : H * Z * H * H = H * Z := by rw [Matrix.mul_assoc, hsq, Matrix.mul_one]
  have e2 : H * (H * Zᴴ * H) = Zᴴ * H := by
    rw [Matrix.mul_assoc H Zᴴ H, ← Matrix.mul_assoc H H, hsq, Matrix.one_mul]
  have e3 : (H * Zᴴ * H)ᴴ = H * Z * H := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hh,
      Matrix.mul_assoc]
  constructor
  · unfold hpart1
    rw [hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, e3, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sub_mul, Matrix.mul_sub, e1, e2]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    simp
  · unfold hpart2
    rw [hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, e3, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, e1, e2]
    have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
      simp [Complex.conj_I]
    rw [this, neg_smul, add_comm (Zᴴ * H) (H * Z), neg_add_cancel]

theorem hpart_lie (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) ∧
    inLieLev k r i (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  have hs := hpart_skew (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) WeylGroupFacts.hpk_sq hpk_herm
  have hZh : (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ =
      Matrix.single (posL k r i b) (posL k r i a) 1 := by
    rw [Matrix.conjTranspose_single, star_one]
  have hkill : ∀ c : Fin r, c.val < i.val →
      (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ)) *ᵥ bvec (eI k r c) = 0 ∧
      (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ)) *ᵥ bvec (esI k r c) = 0 ∧
      (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r) *ᵥ bvec (eI k r c) = 0 ∧
      (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r) *ᵥ bvec (esI k r c) = 0 := by
    intro c hc
    refine ⟨single_bvec (posL_ne_e i b c hc).1, single_bvec (posL_ne_e i b c hc).2, ?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec, hpk_e, ← Matrix.mulVec_mulVec, hZh, single_bvec (posL_ne_e i a c hc).2,
        Matrix.mulVec_zero]
    · rw [← Matrix.mulVec_mulVec, hpk_es, ← Matrix.mulVec_mulVec, hZh, single_bvec (posL_ne_e i a c hc).1,
        Matrix.mulVec_zero]
  refine ⟨⟨hs.1, fun c hc => ?_⟩, ⟨hs.2, fun c hc => ?_⟩⟩
  · obtain ⟨k1, k2, k3, k4⟩ := hkill c hc
    unfold hpart1
    rw [hpk_inv]
    simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, k1, k2, k3, k4, sub_zero, smul_zero, and_self]
  · obtain ⟨k1, k2, k3, k4⟩ := hkill c hc
    unfold hpart2
    rw [hpk_inv]
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, k1, k2, k3, k4, add_zero, smul_zero, and_self]

section Fam

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev XX (k r : ℕ) := (Fin r → ℂ) × Mx k r

variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}

theorem sf_rdV {Φ : Fn k r E} {X : Mx k r} (hX : LieLev i X) (h : SmoothFam k r i U₀ Φ) :
    SmoothFam k r i U₀ (fun c => RdV X (Φ c)) := by
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x₀ hx₀ hg₀
  let L : XX k r →L[ℝ] XX k r := (ContinuousLinearMap.inr ℝ (Fin r → ℂ) (Mx k r)).comp
    ((mulRightRealCLM X).comp (ContinuousLinearMap.snd ℝ (Fin r → ℂ) (Mx k r)))
  refine ⟨U, fun x => fderiv ℝ F x (L x), hU, hxU, ?_, ?_⟩
  · exact (hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty).clm_apply L.contDiff.contDiffOn
  · intro x hx hxG
    have hγ : HasDerivAt (fun t : ℝ => ((x.1, x.2 * NormedSpace.exp ((t : ℂ) • X)) : XX k r)) (L x) 0 :=
      (hasDerivAt_const (0 : ℝ) x.1).prodMk (hasDerivAt_mul_exp_smul_zero x.2 X)
    have hγ0 : ((x.1, x.2 * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) : XX k r) = x := by
      simp [NormedSpace.exp_zero]
    have hFd : DifferentiableAt ℝ F x :=
      (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    have hcomp : HasDerivAt (fun t : ℝ => F (x.1, x.2 * NormedSpace.exp ((t : ℂ) • X)))
        (fderiv ℝ F x (L x)) 0 :=
      hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
    have hev : (fun t : ℝ => Φ x.1 (x.2 * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
        (fun t : ℝ => F (x.1, x.2 * NormedSpace.exp ((t : ℂ) • X))) := by
      have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((x.1, x.2 * NormedSpace.exp ((t : ℂ) • X)) : XX k r) ∈ U :=
        hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hx)
      filter_upwards [hmem] with t ht
      exact hΦ _ ht (glev_mul hxG (hX t))
    show deriv (fun t : ℝ => Φ x.1 (x.2 * NormedSpace.exp ((t : ℂ) • X))) 0 = _
    rw [hev.deriv_eq]
    exact hcomp.deriv

theorem sf_zero : SmoothFam k r i U₀ (fun _ _ => (0 : E)) :=
  fun _ _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem sf_add {Φ Ψ : Fn k r E} (h : SmoothFam k r i U₀ Φ) (h' : SmoothFam k r i U₀ Ψ) :
    SmoothFam k r i U₀ (fun c g => Φ c g + Ψ c g) := by
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x₀ hx₀ hg₀
  obtain ⟨U', F', hU', hxU', hF', hΦ'⟩ := h' x₀ hx₀ hg₀
  exact ⟨U ∩ U', fun x => F x + F' x, hU.inter hU', ⟨hxU, hxU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right),
    fun x hx hxG => by
      show Φ x.1 x.2 + Ψ x.1 x.2 = F x + F' x
      rw [hΦ x hx.1 hxG, hΦ' x hx.2 hxG]⟩

theorem sf_smul {a : Fn k r ℂ} {Φ : Fn k r E} (h : SmoothFam k r i U₀ a) (h' : SmoothFam k r i U₀ Φ) :
    SmoothFam k r i U₀ (fun c g => a c g • Φ c g) := by
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x₀ hx₀ hg₀
  obtain ⟨U', F', hU', hxU', hF', hΦ'⟩ := h' x₀ hx₀ hg₀
  exact ⟨U ∩ U', fun x => F x • F' x, hU.inter hU', ⟨hxU, hxU'⟩,
    (hF.mono Set.inter_subset_left).smul (hF'.mono Set.inter_subset_right),
    fun x hx hxG => by
      show a x.1 x.2 • Φ x.1 x.2 = F x • F' x
      rw [hΦ x hx.1 hxG, hΦ' x hx.2 hxG]⟩

theorem sf_const (s : ℂ) : SmoothFam k r i U₀ (fun _ _ => s) :=
  fun _ _ _ => ⟨Set.univ, fun _ => s, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem sf_csmul (s : ℂ) {Φ : Fn k r E} (h : SmoothFam k r i U₀ Φ) :
    SmoothFam k r i U₀ (fun c g => s • Φ c g) := sf_smul (sf_const s) h

theorem sf_mul {a b : Fn k r ℂ} (h : SmoothFam k r i U₀ a) (h' : SmoothFam k r i U₀ b) :
    SmoothFam k r i U₀ (fun c g => a c g * b c g) := sf_smul h h'

theorem sf_neg {Φ : Fn k r E} (h : SmoothFam k r i U₀ Φ) : SmoothFam k r i U₀ (fun c g => -Φ c g) := by
  have := sf_csmul (-1) h
  simpa using this

theorem sf_sub {Φ Ψ : Fn k r E} (h : SmoothFam k r i U₀ Φ) (h' : SmoothFam k r i U₀ Ψ) :
    SmoothFam k r i U₀ (fun c g => Φ c g - Ψ c g) := by
  have := sf_add h (sf_neg h')
  simpa [sub_eq_add_neg] using this

theorem sf_sum {ι : Type*} (s : Finset ι) {Φ : ι → Fn k r E} (h : ∀ j ∈ s, SmoothFam k r i U₀ (Φ j)) :
    SmoothFam k r i U₀ (fun c g => ∑ j ∈ s, Φ j c g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sf_zero
  | insert a s ha ih =>
    have := sf_add (h a (Finset.mem_insert_self a s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert ha] using this

theorem sf_lin (L : Mx k r →ₗ[ℝ] ℂ) {a : Mx k r → ℂ} (h : ∀ g ∈ Glev k r i, a g = L g) :
    SmoothFam k r i U₀ (fun _ g => a g) :=
  fun _ _ _ => ⟨Set.univ, fun x => (LinearMap.toContinuousLinearMap L) x.2, isOpen_univ, trivial,
    ((LinearMap.toContinuousLinearMap L).contDiff.comp contDiff_snd).contDiffOn, fun x _ hx => h x.2 hx⟩

def Pres (i : Fin (r + 1)) (U₀ : Set (XX k r)) (T : (Mx k r → E) → Mx k r → E) : Prop :=
  ∀ Φ : Fn k r E, SmoothFam k r i U₀ Φ → SmoothFam k r i U₀ (fun c => T (Φ c))

theorem pres_EH (a b : Fin (mdim k r i)) :
    Pres (E := E) i U₀ (EH k r (posL k r i a) (posL k r i b)) := by
  intro Φ h
  exact sf_add (sf_rdV (lieLev_of (hpart_lie i a b).1) h)
    (sf_csmul Complex.I (sf_rdV (lieLev_of (hpart_lie i a b).2) h))

theorem pres_Top (u : ℂ) (a b : Fin (mdim k r i)) :
    Pres (E := E) i U₀ (Top (EH k r) u (posL k r i a) (posL k r i b)) := by
  intro Φ h
  refine sf_add ?_ (pres_EH a b Φ h)
  by_cases hab : posL k r i a = posL k r i b
  · simpa [hab] using sf_csmul u h
  · simpa [hab] using (sf_zero (E := E))

theorem pres_foldr (L : List ((Mx k r → E) → Mx k r → E)) (hL : ∀ T ∈ L, Pres i U₀ T) :
    Pres i U₀ (fun f => L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact fun Φ h => h
  | cons T L ih =>
    intro Φ h
    exact hL T List.mem_cons_self _ (ih (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) Φ h)

theorem pres_qminor {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    Pres (E := E) i U₀ (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u) := by
  intro Φ h
  have key : ∀ σ : Equiv.Perm (Fin t), SmoothFam k r i U₀ (fun c g =>
      (((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun j : Fin t =>
        Top (E := E) (EH k r) (u - ((j : ℕ) : ℂ)) ((posL k r i ∘ a) (σ j)) ((posL k r i ∘ b) j)).foldr
          (fun T h => T h) (Φ c) g)) := by
    intro σ
    refine sf_csmul _ (pres_foldr _ ?_ Φ h)
    intro T hT
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    exact pres_Top _ _ _
  have := sf_sum Finset.univ (fun σ _ => key σ)
  convert this using 3
  simp [qminorOp, Finset.sum_apply]

end Fam

section Entries

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}

theorem uh_inv_eq {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', WeylGroupFacts.hpk_sq]

theorem sf_yv (z : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r i)) :
    SmoothFam k r i U₀ (fun _ g => yv k r z i g j) := by
  refine sf_lin
    { toFun := fun g => ((Hpk k r * gᴴ * Hpk k r) *ᵥ fvec k r z i) (posL k r i j)
      map_add' := ?_
      map_smul' := ?_ } ?_
  · intro x y
    simp [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec]
  · intro c x
    simp [Matrix.conjTranspose_smul, Matrix.smul_mulVec]
  · intro g hg
    show (g⁻¹ *ᵥ fvec k r z i) (posL k r i j) = _
    rw [uh_inv_eq hg.1]
    rfl

theorem sf_ybv (z : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r i)) :
    SmoothFam k r i U₀ (fun _ g => ybv k r z i g j) := by
  refine sf_lin
    { toFun := fun g => herm (Hpk k r) (g *ᵥ bvec (posL k r i j)) (fvec k r z i)
      map_add' := ?_
      map_smul' := ?_ } ?_
  · intro x y
    simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
  · intro c x
    simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul]
  · intro g _
    rfl

theorem pres_chatL (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ)
    (ha : ∀ j, SmoothFam k r i U₀ (fun _ g => a g j)) (hβ : ∀ j, SmoothFam k r i U₀ (fun _ g => β g j)) :
    Pres (E := E) i U₀ (chatL (EH k r) (posL k r i) u a β) := by
  intro Φ h
  unfold chatL
  exact sf_sum _ fun i' _ => sf_sum _ fun j' _ =>
    sf_smul (sf_mul (sf_mul (sf_const _) (hβ i')) (ha j')) (pres_qminor _ _ _ Φ h)

theorem pres_chat2L (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ)
    (ha : ∀ j, SmoothFam k r i U₀ (fun _ g => a g j)) (ha' : ∀ j, SmoothFam k r i U₀ (fun _ g => a' g j))
    (hβ : ∀ j, SmoothFam k r i U₀ (fun _ g => β g j)) (hβ' : ∀ j, SmoothFam k r i U₀ (fun _ g => β' g j)) :
    Pres (E := E) i U₀ (chat2L (EH k r) (posL k r i) u a a' β β') := by
  intro Φ h
  unfold chat2L
  refine sf_sum _ fun i₁ _ => sf_sum _ fun i₂ _ => sf_sum _ fun j₁ _ => sf_sum _ fun j₂ _ => ?_
  by_cases hc : i₁ < i₂ ∧ j₁ < j₂
  · simp only [if_pos hc]
    exact sf_smul (sf_mul (sf_mul (sf_const _) (sf_sub (sf_mul (hβ i₁) (hβ' i₂)) (sf_mul (hβ i₂) (hβ' i₁))))
      (sf_sub (sf_mul (ha j₁) (ha' j₂)) (sf_mul (ha j₂) (ha' j₁)))) (pres_qminor _ _ _ Φ h)
  · simp only [if_neg hc]
    exact sf_zero

theorem pres_tL (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2) :
    Pres (E := E) i U₀ (tL k r z z' i Y p q) := by
  intro Φ h
  fin_cases p <;> fin_cases q
  · show SmoothFam k r i U₀ (fun c => capL k r i (uC k r i Y) (Φ c))
    exact pres_qminor id id _ Φ h
  · show SmoothFam k r i U₀ (fun c g => -(chatL (EH k r) (posL k r i) (uC k r i Y - 1) (fun _ => xv k r z' i)
      (ybv k r z i) (Φ c) g))
    exact sf_neg (pres_chatL (uC k r i Y - 1) (fun _ => xv k r z' i) (ybv k r z i)
      (fun j => sf_const _) (fun j => sf_ybv z j) Φ h)
  · show SmoothFam k r i U₀ (fun c g => -(chatL (EH k r) (posL k r i) (uC k r i Y) (yv k r z i)
      (fun _ => xbv k r z' i) (Φ c) g))
    exact sf_neg (pres_chatL (uC k r i Y) (yv k r z i) (fun _ => xbv k r z' i)
      (fun j => sf_yv z j) (fun j => sf_const _) Φ h)
  · show SmoothFam k r i U₀ (fun c g => -(chat2L (EH k r) (posL k r i) (uC k r i Y - 1) (yv k r z i)
      (fun _ => xv k r z' i) (ybv k r z i) (fun _ => xbv k r z' i) (Φ c) g))
    exact sf_neg (pres_chat2L (uC k r i Y - 1) (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i)
      (fun _ => xbv k r z' i) (fun j => sf_yv z j) (fun j => sf_const _) (fun j => sf_ybv z j)
      (fun j => sf_const _) Φ h)

end Entries

section Ops

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}

theorem isOpen_OmX (r : ℕ) : IsOpen (OmX r) := by
  have : OmX r = ⋂ l : Fin r, {x : Fin r → ℂ | x l ≠ 0} := by
    ext x
    simp [OmX]
  rw [this]
  exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const

theorem isOpen_OmXX : IsOpen {x : XX k r | x.1 ∈ OmX r} := (isOpen_OmX r).preimage continuous_fst

theorem sf_congr_on {V : Set (XX k r)} {Φ Ψ : Fn k r E} (hV : IsOpen V) (hUV : U₀ ⊆ V)
    (heq : ∀ x ∈ V, x.2 ∈ Glev k r i → Ψ x.1 x.2 = Φ x.1 x.2) (h : SmoothFam k r i U₀ Φ) :
    SmoothFam k r i U₀ Ψ := by
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x₀ hx₀ hg₀
  exact ⟨U ∩ V, F, hU.inter hV, ⟨hxU, hUV hx₀⟩, hF.mono Set.inter_subset_left,
    fun x hx hxG => (heq x hx.2 hxG).trans (hΦ x hx.1 hxG)⟩

theorem sf_ofC {ρ : (Fin r → ℂ) → ℂ} (hρ : ContDiffOn ℝ ∞ ρ (OmX r)) (hU₀ : U₀ ⊆ {x | x.1 ∈ OmX r}) :
    SmoothFam k r i U₀ (fun c _ => ρ c) :=
  fun _ hx₀ _ => ⟨{x | x.1 ∈ OmX r}, fun x => ρ x.1, isOpen_OmXX, hU₀ hx₀,
    hρ.comp contDiff_fst.contDiffOn (fun _ hx => hx), fun _ _ _ => rfl⟩

theorem fam_hasFDerivAt {Φ : Fn k r E} {U : Set (XX k r)} {F : XX k r → E} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hΦ : ∀ x ∈ U, x.2 ∈ Glev k r i → Φ x.1 x.2 = F x) {x : XX k r} (hx : x ∈ U)
    (hxG : x.2 ∈ Glev k r i) :
    HasFDerivAt (fun c' => Φ c' x.2)
      ((fderiv ℝ F x).comp (ContinuousLinearMap.inl ℝ (Fin r → ℂ) (Mx k r))) x.1 := by
  have hFd : DifferentiableAt ℝ F x :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have h1 : HasFDerivAt (fun c' : Fin r → ℂ => ((c', x.2) : XX k r))
      (ContinuousLinearMap.inl ℝ (Fin r → ℂ) (Mx k r)) x.1 := hasFDerivAt_prodMk_left x.1 x.2
  have h2 : HasFDerivAt (fun c' : Fin r → ℂ => F (c', x.2))
      ((fderiv ℝ F x).comp (ContinuousLinearMap.inl ℝ (Fin r → ℂ) (Mx k r))) x.1 :=
    HasFDerivAt.comp x.1 (f := fun c' : Fin r → ℂ => ((c', x.2) : XX k r)) (g := F) hFd.hasFDerivAt h1
  refine h2.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ c' : Fin r → ℂ in 𝓝 x.1, ((c', x.2) : XX k r) ∈ U :=
    h1.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
  filter_upwards [hmem] with c' hc'
  exact hΦ _ hc' hxG

theorem sf_fderiv (v : Fin r → ℂ) {Φ : Fn k r E} (h : SmoothFam k r i U₀ Φ) :
    SmoothFam k r i U₀ (fun c g => fderiv ℝ (fun c' => Φ c' g) c v) := by
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x₀ hx₀ hg₀
  refine ⟨U, fun x => fderiv ℝ F x ((v, 0) : XX k r), hU, hxU, ?_, ?_⟩
  · exact (hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty).clm_apply contDiffOn_const
  · intro x hx hxG
    show fderiv ℝ (fun c' => Φ c' x.2) x.1 v = _
    rw [(fam_hasFDerivAt hU hF hΦ hx hxG).fderiv]
    rfl

theorem fam_differentiableAt {Φ : Fn k r E} (h : SmoothFam k r i U₀ Φ) {x : XX k r} (hx : x ∈ U₀)
    (hxG : x.2 ∈ Glev k r i) : DifferentiableAt ℝ (fun c' => Φ c' x.2) x.1 := by
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x hx hxG
  exact (fam_hasFDerivAt hU hF hΦ hxU hxG).differentiableAt

theorem cd_coord (a : Fin r) : ContDiff ℝ ∞ (fun c : Fin r → ℂ => c a) := contDiff_apply ℝ ℂ a

theorem cd_coordBar (a : Fin r) : ContDiff ℝ ∞ (fun c : Fin r → ℂ => star (c a)) :=
  Complex.conjCLE.contDiff.comp (cd_coord a)

theorem sf_opL (hU₀ : U₀ ⊆ {x | x.1 ∈ OmX r}) (a : Fin r) (j : Fin 6) {Φ : Fn k r E}
    (h : SmoothFam k r i U₀ Φ) : SmoothFam k r i U₀ (crd (opL a j) Φ) := by
  have hw : SmoothFam k r i U₀ (fun c g => wirt a (fun c' => Φ c' g) c) :=
    sf_csmul _ (sf_sub (sf_fderiv _ h) (sf_csmul _ (sf_fderiv _ h)))
  have hwb : SmoothFam k r i U₀ (fun c g => wirtBar a (fun c' => Φ c' g) c) :=
    sf_csmul _ (sf_add (sf_fderiv _ h) (sf_csmul _ (sf_fderiv _ h)))
  have hc : SmoothFam k r i U₀ (fun c _ => c a) := sf_ofC (cd_coord a).contDiffOn hU₀
  have hcb : SmoothFam k r i U₀ (fun c _ => star (c a)) := sf_ofC (cd_coordBar a).contDiffOn hU₀
  have hci : SmoothFam k r i U₀ (fun c _ => (c a)⁻¹) :=
    sf_ofC ((cd_coord a).contDiffOn.inv fun x hx => hx a) hU₀
  have hcbi : SmoothFam k r i U₀ (fun c _ => (star (c a))⁻¹) :=
    sf_ofC ((cd_coordBar a).contDiffOn.inv fun x hx => star_ne_zero.2 (hx a)) hU₀
  fin_cases j
  · refine sf_congr_on isOpen_OmXX hU₀ (fun x hx _ => ?_) (sf_smul hc hw)
    show pOp a (fun c' => Φ c' x.2) x.1 = _
    unfold pOp
    exact if_pos hx
  · exact sf_smul hc h
  · exact sf_smul hci h
  · refine sf_congr_on isOpen_OmXX hU₀ (fun x hx _ => ?_) (sf_smul hcb hwb)
    show pbOp a (fun c' => Φ c' x.2) x.1 = _
    unfold pbOp
    exact if_pos hx
  · exact sf_smul hcb h
  · exact sf_smul hcbi h

theorem opL_equiv (a : Fin r) (j : Fin 6) {f f' : (Fin r → ℂ) → E} (L : E →L[ℂ] E) {c : Fin r → ℂ}
    (hev : ∀ᶠ c' in 𝓝 c, f' c' = L (f c')) (hd : DifferentiableAt ℝ f c) :
    opL a j f' c = L (opL a j f c) := by
  have h0 : f' c = L (f c) := hev.self_of_nhds
  have hfd : ∀ v, fderiv ℝ f' c v = L (fderiv ℝ f c v) := by
    intro v
    have e : f' =ᶠ[𝓝 c] fun c' => (L.restrictScalars ℝ) (f c') := hev
    have e2 : HasFDerivAt (fun c' => (L.restrictScalars ℝ) (f c'))
        ((L.restrictScalars ℝ).comp (fderiv ℝ f c)) c := (L.restrictScalars ℝ).hasFDerivAt.comp c hd.hasFDerivAt
    rw [e.fderiv_eq, e2.fderiv]
    rfl
  fin_cases j
  · show pOp a f' c = L (pOp a f c)
    unfold pOp wirt
    split_ifs
    · simp only [hfd, map_smul, map_sub]
    · simp
  · show c a • f' c = L (c a • f c)
    rw [h0, map_smul]
  · show (c a)⁻¹ • f' c = L ((c a)⁻¹ • f c)
    rw [h0, map_smul]
  · show pbOp a f' c = L (pbOp a f c)
    unfold pbOp wirtBar
    split_ifs
    · simp only [hfd, map_smul, map_add]
    · simp
  · show star (c a) • f' c = L (star (c a) • f c)
    rw [h0, map_smul]
  · show (star (c a))⁻¹ • f' c = L ((star (c a))⁻¹ • f c)
    rw [h0, map_smul]

theorem sf_slice {Dc : (Fin r → ℂ) → Set (Mx k r)} {Φ : Fn k r E}
    (h : SmoothFam k r i {x | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} Φ) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    SmoothLev k r i (Dc c) (Φ c) := by
  rintro g₀ ⟨hG, hD⟩
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h (c, g₀) ⟨hc, hD⟩ hG
  exact ⟨{g | ((c, g) : XX k r) ∈ U}, fun g => F (c, g), hU.preimage (continuous_const.prodMk continuous_id),
    hxU, hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun g hg => hg),
    fun g hg hgG => hΦ (c, g) hg hgG⟩

end Ops

section W1

theorem e_ne_es (l : Fin r) : eI k r l ≠ esI k r l := by
  have := l.isLt
  simp only [eI, esI, ne_eq, Fin.ext_iff]
  omega

def sw (k : ℕ) {r : ℕ} (l : Fin r) (q : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if q = eI k r l then esI k r l else if q = esI k r l then eI k r l else q

def dd (k : ℕ) {r : ℕ} (l : Fin r) (c : ℂ) (q : Fin (2 * r + k + 1)) : ℂ :=
  if q = eI k r l then c else if q = esI k r l then (star c)⁻¹ else 1

theorem sw_e (l : Fin r) : sw k l (eI k r l) = esI k r l := by simp [sw]
theorem sw_es (l : Fin r) : sw k l (esI k r l) = eI k r l := by simp [sw, (e_ne_es l).symm]
theorem sw_o (l : Fin r) {q : Fin (2 * r + k + 1)} (h1 : q ≠ eI k r l) (h2 : q ≠ esI k r l) : sw k l q = q := by
  simp [sw, h1, h2]
theorem dd_e (l : Fin r) (c : ℂ) : dd k l c (eI k r l) = c := by simp [dd]
theorem dd_es (l : Fin r) (c : ℂ) : dd k l c (esI k r l) = (star c)⁻¹ := by simp [dd, (e_ne_es l).symm]
theorem dd_o (l : Fin r) (c : ℂ) {q : Fin (2 * r + k + 1)} (h1 : q ≠ eI k r l) (h2 : q ≠ esI k r l) :
    dd k l c q = 1 := by
  simp [dd, h1, h2]

theorem tri (l : Fin r) (q : Fin (2 * r + k + 1)) :
    q = eI k r l ∨ q = esI k r l ∨ (q ≠ eI k r l ∧ q ≠ esI k r l) := by
  by_cases h1 : q = eI k r l
  · exact Or.inl h1
  · by_cases h2 : q = esI k r l
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

theorem sw_sw (l : Fin r) (q : Fin (2 * r + k + 1)) : sw k l (sw k l q) = q := by
  rcases tri l q with h | h | ⟨h1, h2⟩
  · rw [h, sw_e, sw_es]
  · rw [h, sw_es, sw_e]
  · rw [sw_o l h1 h2, sw_o l h1 h2]

theorem w1_apply (l : Fin r) (c : ℂ) (p q : Fin (2 * r + k + 1)) :
    w1 k r l c p q = if p = sw k l q then dd k l c q else 0 := by
  have hne := e_ne_es (k := k) l
  rcases tri l q with h | h | ⟨h1, h2⟩
  · subst h
    rw [sw_e, dd_e]
    unfold w1
    by_cases hp : p = esI k r l
    · simp [hp]
    · simp [hp, hne]
  · subst h
    rw [sw_es, dd_es]
    unfold w1
    by_cases hp : p = eI k r l
    · simp [hp, hne, hne.symm]
    · simp [hp, hne.symm]
  · rw [sw_o l h1 h2, dd_o l c h1 h2]
    unfold w1
    by_cases hp : p = q
    · subst hp
      simp [h1, h2]
    · simp [hp, h1, h2]

theorem mul_weyl_cell_apply (l : Fin r) (c : ℂ) (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (M * w1 k r l c) p q = M p (sw k l q) * dd k l c q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sw k l q)]
  · rw [w1_apply, if_pos rfl]
  · intro x _ hx
    rw [w1_apply, if_neg hx, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem weyl_cell_mul_apply (l : Fin r) (c : ℂ) (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (w1 k r l c * M) p q = dd k l c (sw k l p) * M (sw k l p) q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sw k l p)]
  · rw [w1_apply, sw_sw, if_pos rfl]
  · intro x _ hx
    have : p ≠ sw k l x := fun h => hx (by rw [h, sw_sw])
    rw [w1_apply, if_neg this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem weyl_cell_conjTranspose_mul_apply (l : Fin r) (c : ℂ) (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    ((w1 k r l c)ᴴ * M) p q = star (dd k l c p) * M (sw k l p) q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sw k l p)]
  · rw [Matrix.conjTranspose_apply, w1_apply, if_pos rfl]
  · intro x _ hx
    rw [Matrix.conjTranspose_apply, w1_apply, if_neg hx, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem hpk_col_e (l : Fin r) (x : Fin (2 * r + k + 1)) :
    Hpk k r x (eI k r l) = if x = esI k r l then 1 else 0 := by
  have := congrFun (hpk_e (k := k) l) x
  simpa [bvec, Matrix.mulVec_single_one, Pi.single_apply] using this

theorem hpk_col_es (l : Fin r) (x : Fin (2 * r + k + 1)) :
    Hpk k r x (esI k r l) = if x = eI k r l then 1 else 0 := by
  have := congrFun (hpk_es (k := k) l) x
  simpa [bvec, Matrix.mulVec_single_one, Pi.single_apply] using this

theorem hpk_symm (x y : Fin (2 * r + k + 1)) : Hpk k r x y = star (Hpk k r y x) := by
  have := congrFun (congrFun (hpk_herm (k := k) (r := r)) x) y
  rw [Matrix.conjTranspose_apply] at this
  exact this.symm

theorem hpk_row_e (l : Fin r) (x : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r l) x = if x = esI k r l then 1 else 0 := by
  rw [hpk_symm, hpk_col_e]
  split_ifs <;> simp

theorem hpk_row_es (l : Fin r) (x : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r l) x = if x = eI k r l then 1 else 0 := by
  rw [hpk_symm, hpk_col_es]
  split_ifs <;> simp

theorem weyl_cell_mem_unitary (l : Fin r) {c : ℂ} (hc : c ≠ 0) : w1 k r l c ∈ UH (Hpk k r) := by
  have hne := e_ne_es (k := k) l
  have hcs : (starRingEnd ℂ) c ≠ 0 := star_ne_zero.2 hc
  show (w1 k r l c)ᴴ * Hpk k r * w1 k r l c = Hpk k r
  ext p q
  rw [mul_weyl_cell_apply, weyl_cell_conjTranspose_mul_apply]
  rcases tri l p with h | h | ⟨h1, h2⟩
  · subst h
    rw [sw_e, dd_e, hpk_row_es, hpk_row_e]
    rcases tri l q with h' | h' | ⟨h1', h2'⟩
    · subst h'
      simp [sw_e, hne, hne.symm]
    · subst h'
      simp [sw_es, dd_es, hcs]
    · simp [sw_o l h1' h2', h1', h2']
  · subst h
    rw [sw_es, dd_es, hpk_row_es, hpk_row_e]
    rcases tri l q with h' | h' | ⟨h1', h2'⟩
    · subst h'
      simp [sw_e, dd_e, hc]
    · subst h'
      simp [sw_es, hne, hne.symm]
    · simp [sw_o l h1' h2', h1', h2']
  · rw [sw_o l h1 h2, dd_o l c h1 h2]
    rcases tri l q with h' | h' | ⟨h1', h2'⟩
    · subst h'
      simp [sw_e, hpk_col_e, hpk_col_es, h1, h2]
    · subst h'
      simp [sw_es, hpk_col_e, hpk_col_es, h1, h2]
    · simp [sw_o l h1' h2', dd_o l c h1' h2']

theorem reflection_fixes_basis_vector (l : Fin r) (c : ℂ) {q : Fin (2 * r + k + 1)} (h1 : q ≠ eI k r l) (h2 : q ≠ esI k r l) :
    w1 k r l c *ᵥ bvec q = bvec q := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]
  rw [w1_apply, sw_o l h1 h2, dd_o l c h1 h2]

theorem weyl_cell_mem_level_group (l : Fin r) {c : ℂ} (hc : c ≠ 0) : w1 k r l c ∈ Glev k r l.castSucc := by
  refine ⟨weyl_cell_mem_unitary l hc, fun a ha => ?_⟩
  have ha' : a.val < l.val := ha
  have hl := l.isLt
  constructor
  · apply reflection_fixes_basis_vector <;> simp only [eI, esI, ne_eq, Fin.ext_iff] <;> omega
  · apply reflection_fixes_basis_vector <;> simp only [eI, esI, ne_eq, Fin.ext_iff] <;> omega

theorem tau_e (l : Fin r) : WeylGroupFacts.tau k r (eI k r l) = esI k r l := by
  have := l.isLt
  unfold WeylGroupFacts.tau eI esI
  apply Fin.ext
  simp only
  split_ifs <;> omega

theorem tau_es (l : Fin r) : WeylGroupFacts.tau k r (esI k r l) = eI k r l := by
  have := l.isLt
  unfold WeylGroupFacts.tau eI esI
  apply Fin.ext
  simp only
  split_ifs <;> omega

theorem w1_commute_of_mem_Glev (l : Fin r) (c : ℂ) {g : Mx k r} (hg : g ∈ Glev k r l.succ) :
    w1 k r l c * g = g * w1 k r l c := by
  have hne := e_ne_es (k := k) l
  have hl : l.val < (l.succ : Fin (r + 1)).val := by simp
  have ce : ∀ p, g p (eI k r l) = if p = eI k r l then 1 else 0 := WeylGroupFacts.col_of_fix (hg.2 l hl).1
  have ces : ∀ p, g p (esI k r l) = if p = esI k r l then 1 else 0 := WeylGroupFacts.col_of_fix (hg.2 l hl).2
  have res : ∀ j, g (esI k r l) j = if esI k r l = j then 1 else 0 := by
    have := WeylGroupFacts.row_of_fixed_col hg.1 (eI k r l) ce
    rwa [tau_e] at this
  have re : ∀ j, g (eI k r l) j = if eI k r l = j then 1 else 0 := by
    have := WeylGroupFacts.row_of_fixed_col hg.1 (esI k r l) ces
    rwa [tau_es] at this
  ext p q
  rw [mul_weyl_cell_apply, weyl_cell_mul_apply]
  rcases tri l p with h | h | ⟨h1, h2⟩
  · subst h
    rw [sw_e, dd_es, res, re]
    rcases tri l q with h' | h' | ⟨h1', h2'⟩
    · subst h'
      simp [sw_e, hne, hne.symm]
    · subst h'
      simp [sw_es, dd_es]
    · simp [sw_o l h1' h2', Ne.symm h1', Ne.symm h2']
  · subst h
    rw [sw_es, dd_e, res, re]
    rcases tri l q with h' | h' | ⟨h1', h2'⟩
    · subst h'
      simp [sw_e, dd_e]
    · subst h'
      simp [sw_es, hne, hne.symm]
    · simp [sw_o l h1' h2', Ne.symm h1', Ne.symm h2']
  · rw [sw_o l h1 h2, dd_o l c h1 h2]
    rcases tri l q with h' | h' | ⟨h1', h2'⟩
    · subst h'
      simp [sw_e, ce, ces, h1, h2]
    · subst h'
      simp [sw_es, ce, ces, h1, h2]
    · simp [sw_o l h1' h2', dd_o l c h1' h2']

end W1

section Res

theorem cdo_matrix {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X → Mx k r} {s : Set X}
    (h : ∀ p q, ContDiffOn ℝ ∞ (fun x => f x p q) s) : ContDiffOn ℝ ∞ f s :=
  contDiffOn_pi.2 fun p => contDiffOn_pi.2 fun q => h p q

theorem cdo_entry {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X → Mx k r} {s : Set X}
    (h : ContDiffOn ℝ ∞ f s) (p q : Fin (2 * r + k + 1)) : ContDiffOn ℝ ∞ (fun x => f x p q) s :=
  contDiffOn_pi.1 (contDiffOn_pi.1 h p) q

theorem cdo_mul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f g : X → Mx k r} {s : Set X}
    (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s) : ContDiffOn ℝ ∞ (fun x => f x * g x) s := by
  refine cdo_matrix fun p q => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun x _ => (cdo_entry hf p x).mul (cdo_entry hg x q)

def mulLeftL (w : Mx k r) : Mx k r →L[ℝ] Mx k r := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ w)

theorem weyl_cell_contDiffOn (l : Fin r) : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => w1 k r l (c l)) (OmX r) := by
  refine cdo_matrix fun p q => ?_
  unfold w1
  split_ifs
  · exact (cd_coord l).contDiffOn
  · exact (cd_coordBar l).contDiffOn.inv fun x hx => star_ne_zero.2 (hx l)
  · exact contDiffOn_const
  · exact contDiffOn_const

theorem slev_mono {z : Fin (2 * r + k + 1) → ℂ} {i j : Fin (r + 1)} (h : j ≤ i) : Slev k r z i ⊆ Slev k r z j := by
  rintro s ⟨u, hu, m, hm, rfl⟩
  exact ⟨u, hu, m, nlev_mono h hm, rfl⟩

theorem slev_glev {z : Fin (2 * r + k + 1) → ℂ} (i : Fin (r + 1)) : Slev k r z i ⊆ Glev k r i := by
  rintro s ⟨u, hu, m, hm, rfl⟩
  exact glev_mul (uw_glev i hu) hm.2

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
variable {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem ffl_res {j i : Fin (r + 1)} (hji : j ≤ i) {w₀ : Mx k r} (hw : w₀ ∈ Glev k r j)
    (hcomm : ∀ g ∈ Glev k r i, w₀ * g = g * w₀) {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ FFl k r z z' π π' j D) :
    (fun g => J (w₀ * g)) ∈ FFl k r z z' π π' i {g | w₀ * g ∈ D} := by
  obtain ⟨hS, hL, hR, hπ⟩ := hJ
  have hmem : ∀ g ∈ Glev k r i ∩ {g | w₀ * g ∈ D}, w₀ * g ∈ Glev k r j ∩ D :=
    fun g hg => ⟨glev_mul hw (glev_mono hji hg.1), hg.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hS _ (hmem g₀ hg₀)
    exact ⟨{g | w₀ * g ∈ U}, fun g => F (w₀ * g), hU.preimage (mulLeftL w₀).continuous, hgU,
      hF.comp (mulLeftL w₀).contDiff.contDiffOn (fun _ h => h),
      fun g hg hgG => hJF _ hg (glev_mul hw (glev_mono hji hgG))⟩
  · intro g hg n hn
    show J (w₀ * (n * g)) = _ • J (w₀ * g)
    rw [← Matrix.mul_assoc, hcomm n hn.2, Matrix.mul_assoc]
    exact hL _ (hmem g hg) n (nlev_mono hji hn)
  · intro g hg n hn
    show J (w₀ * (g * n)) = _ • J (w₀ * g)
    rw [← Matrix.mul_assoc]
    exact hR _ (hmem g hg) n (nlev_mono hji hn)
  · intro g hg h hh h' hh'
    show J (w₀ * (h * g * h')) = _
    have e : w₀ * (h * g * h') = h * (w₀ * g) * h' := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcomm h (uw_glev i hh), Matrix.mul_assoc h w₀ g]
    rw [e]
    exact hπ _ (hmem g hg) h hh h' hh'

theorem ffl_smul (s : ℂ) {i : Fin (r + 1)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ FFl k r z z' π π' i D) : (fun g => s • J g) ∈ FFl k r z z' π π' i D := by
  obtain ⟨hS, hL, hR, hπ⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hS _ hg₀
    exact ⟨U, fun g => s • F g, hU, hgU, hF.const_smul s, fun g hg hgG => by
      show s • J g = s • F g
      rw [hJF g hg hgG]⟩
  · intro g hg n hn
    show s • J (n * g) = _ • s • J g
    rw [hL g hg n hn, smul_comm]
  · intro g hg n hn
    show s • J (g * n) = _ • s • J g
    rw [hR g hg n hn, smul_comm]
  · intro g hg h hh h' hh'
    show s • J (h * g * h') = (π h).comp ((s • J g).comp (π' h'))
    rw [hπ g hg h hh h' hh']
    ext v
    simp

theorem fam_res {j i : Fin (r + 1)} (hji : j ≤ i) {w : (Fin r → ℂ) → Mx k r} {ρ : (Fin r → ℂ) → ℂ}
    (hw : ContDiffOn ℝ ∞ w (OmX r)) (hρ : ContDiffOn ℝ ∞ ρ (OmX r))
    (hwG : ∀ c ∈ OmX r, w c ∈ Glev k r j) (hcomm : ∀ c ∈ OmX r, ∀ g ∈ Glev k r i, w c * g = g * w c)
    {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' j D) :
    FamFF k r z z' π π' i (fun c => {g | w c * g ∈ D}) (fun c g => ρ c • J (w c * g)) := by
  refine ⟨?_, fun c hc => ffl_smul (ρ c) (ffl_res hji (hwG c hc) (hcomm c hc) hJ)⟩
  refine sf_smul (sf_ofC hρ (fun x hx => hx.1)) ?_
  rintro x₀ ⟨hc₀, hD₀⟩ hG₀
  obtain ⟨U, F, hU, hgU, hF, hJF⟩ :=
    hJ.1 (w x₀.1 * x₀.2) ⟨glev_mul (hwG _ hc₀) (glev_mono hji hG₀), hD₀⟩
  have hm : ContDiffOn ℝ ∞ (fun x : XX k r => w x.1 * x.2) {x | x.1 ∈ OmX r} :=
    cdo_mul (hw.comp contDiff_fst.contDiffOn (fun _ h => h)) contDiff_snd.contDiffOn
  exact ⟨{x | x.1 ∈ OmX r} ∩ (fun x : XX k r => w x.1 * x.2) ⁻¹' U, fun x => F (w x.1 * x.2),
    hm.continuousOn.isOpen_inter_preimage isOpen_OmXX hU, ⟨hc₀, hgU⟩,
    hF.comp (hm.mono Set.inter_subset_left) (fun x hx => hx.2),
    fun x hx hxG => hJF _ hx.2 (glev_mul (hwG _ hx.1) (glev_mono hji hxG))⟩

theorem cd_normPow (a : Fin r) (n : ℕ) : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => ‖c a‖ ^ n) (OmX r) :=
  (ContDiffOn.norm ℝ ((cd_coord a).contDiffOn (s := OmX r)) fun x (hx : x ∈ OmX r) => hx a).pow n

theorem wlist_glev {c : Fin r → ℂ} (hc : c ∈ OmX r) (L : List (Fin r)) :
    (L.map fun a => w1 k r a (c a)).prod ∈ Glev k r 0 := by
  induction L with
  | nil => exact glev_one 0
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons]
    exact glev_mul (glev_mono (Fin.zero_le _) (weyl_cell_mem_level_group a (hc a))) ih

theorem wlist_comm (i : Fin (r + 1)) (c : Fin r → ℂ) (L : List (Fin r)) (hL : ∀ a ∈ L, a.val < i.val)
    {g : Mx k r} (hg : g ∈ Glev k r i) :
    (L.map fun a => w1 k r a (c a)).prod * g = g * (L.map fun a => w1 k r a (c a)).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha : a.succ ≤ i := by
      rw [Fin.le_def, Fin.val_succ]
      exact hL a List.mem_cons_self
    rw [List.map_cons, List.prod_cons, Matrix.mul_assoc, ih fun b hb => hL b (List.mem_cons_of_mem _ hb),
      ← Matrix.mul_assoc, w1_commute_of_mem_Glev a (c a) (glev_mono ha hg), Matrix.mul_assoc]

theorem wlist_smooth (L : List (Fin r)) :
    ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => (L.map fun a => w1 k r a (c a)).prod) (OmX r) := by
  induction L with
  | nil => simpa using contDiffOn_const
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact cdo_mul (weyl_cell_contDiffOn a) ih

end Res

end Formalism.FourierDecayAlt.P.Qx3

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem transfer_joint_smooth : Formalism.FourierDecayAlt.Q.TJointSmooth := by
  intro E _ _ k r z z' i U₀ Φ Y p q _ h
  exact Qx3.pres_tL z z' Y p q Φ h

theorem family_operators : Formalism.FourierDecayAlt.Q.FamOps := by
  intro Wp Wq _ _ _ _ k r z z' π π' i Dc Φ _ _ hopen hΦ a j
  obtain ⟨hS, hFF⟩ := hΦ
  have hS' := Qx3.sf_opL (fun x hx => hx.1) a j hS
  refine ⟨hS', fun c hc => ?_⟩
  have hnear : ∀ g ∈ Dc c, ∀ᶠ c' in nhds c, c' ∈ OmX r ∧ g ∈ Dc c' := by
    intro g hg
    have hcont : Continuous fun c' : Fin r → ℂ => ((c', g) : Qx3.XX k r) := continuous_id.prodMk continuous_const
    exact hcont.continuousAt.preimage_mem_nhds (hopen.mem_nhds (show ((c, g) : Qx3.XX k r) ∈ _ from ⟨hc, hg⟩))
  have hdiff : ∀ g ∈ Glev k r i ∩ Dc c, DifferentiableAt ℝ (fun c' => Φ c' g) c := fun g hg =>
    Qx3.fam_differentiableAt hS (x := (c, g)) ⟨hc, hg.2⟩ hg.1
  refine ⟨Qx3.sf_slice hS' hc, ?_, ?_, ?_⟩
  · intro g hg n hn
    have := Qx3.opL_equiv a j (f := fun c' => Φ c' g) (f' := fun c' => Φ c' (n * g))
      (psi k r z cStd n • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (c := c)
      (by
        filter_upwards [hnear g hg.2] with c' hc'
        exact (hFF c' hc'.1).2.1 g ⟨hg.1, hc'.2⟩ n hn) (hdiff g hg)
    exact this
  · intro g hg n hn
    have := Qx3.opL_equiv a j (f := fun c' => Φ c' g) (f' := fun c' => Φ c' (g * n))
      (psi k r z' cStd n • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (c := c)
      (by
        filter_upwards [hnear g hg.2] with c' hc'
        exact (hFF c' hc'.1).2.2.1 g ⟨hg.1, hc'.2⟩ n hn) (hdiff g hg)
    exact this
  · intro g hg h hh h' hh'
    have := Qx3.opL_equiv a j (f := fun c' => Φ c' g) (f' := fun c' => Φ c' (h * g * h'))
      ((ContinuousLinearMap.compL ℂ Wq Wp Wp (π h)).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (π' h')))
      (c := c)
      (by
        filter_upwards [hnear g hg.2] with c' hc'
        exact (hFF c' hc'.1).2.2.2 g ⟨hg.1, hc'.2⟩ h hh h' hh') (hdiff g hg)
    exact this

theorem restriction_mem : Formalism.FourierDecayAlt.Q.ResMem := by
  intro Wp Wq _ _ _ _ k r z z' π π' l D _ _ hD J hJ
  have hle : l.castSucc ≤ l.succ := by
    rw [Fin.le_def]
    simp
  refine ⟨fun c hc => ⟨⟨hD.1.preimage (Qx3.mulLeftL (w1 k r l c)).continuous, ?_⟩,
    Qx3.ffl_res hle (Qx3.weyl_cell_mem_level_group l hc) (fun g hg => Qx3.w1_commute_of_mem_Glev l c hg) hJ⟩, ?_⟩
  · intro g hg s hs s' hs'
    show w1 k r l c * (s * g * s') ∈ D
    have e : w1 k r l c * (s * g * s') = s * (w1 k r l c * g) * s' := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Qx3.w1_commute_of_mem_Glev l c (Qx3.slev_glev _ hs),
        Matrix.mul_assoc s (w1 k r l c) g]
    rw [e]
    exact hD.2 _ ⟨Qx3.glev_mul (Qx3.weyl_cell_mem_level_group l hc) (Qx3.glev_mono hle hg.1), hg.2⟩ s (Qx3.slev_mono hle hs) s'
      (Qx3.slev_mono hle hs')
  · exact Qx3.fam_res hle (w := fun c => w1 k r l (c l))
      (ρ := fun c => ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ)) (Qx3.weyl_cell_contDiffOn l)
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (Qx3.cd_normPow l _))
      (fun c hc => Qx3.weyl_cell_mem_level_group l (hc l)) (fun c _ g hg => Qx3.w1_commute_of_mem_Glev l (c l) hg) hJ

theorem restriction_good_family : Formalism.FourierDecayAlt.Q.ResGFam := by
  intro Wp Wq _ _ _ _ k r z z' π π' D _ _ _ J hJ i
  have hρ : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ =>
      ((∏ a : Fin r, (if a.val < i.val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ)) (OmX r) := by
    have h1 : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ =>
        ∏ a : Fin r, (if a.val < i.val then ‖c a‖ ^ (Mdim k r a - 1) else 1)) (OmX r) := by
      refine contDiffOn_prod fun a _ => ?_
      split_ifs
      · exact Qx3.cd_normPow a _
      · exact contDiffOn_const
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn h1
  exact Qx3.fam_res (Fin.zero_le i) (w := fun c => wCell k r i c) (Qx3.wlist_smooth _) hρ
    (fun c hc => Qx3.wlist_glev hc _)
    (fun c _ g hg => Qx3.wlist_comm i c _ (fun a ha => by simpa using (List.mem_filter.1 ha).2) hg) hJ

end Formalism.FourierDecayAlt.P
