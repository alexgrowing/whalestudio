import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.OrbitDerMult
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.MemSpanSmoothVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult MeasureTheory
open scoped ContDiff Matrix Topology
open Asymptotics

namespace Formalism.IndefR.Tow.OrbStPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem conj_mem {n : ℕ} (J G fr g : Matrix (Fin n) (Fin n) ℂ) (hfr : IsUnit fr) (hJ : frᴴ * J * fr = G)
    (hg : gᴴ * G * g = G) : (fr * g * fr⁻¹)ᴴ * J * (fr * g * fr⁻¹) = J := by
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det fr).mp hfr
  have h1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hd
  have h2 : (fr⁻¹)ᴴ * frᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  calc (fr * g * fr⁻¹)ᴴ * J * (fr * g * fr⁻¹)
      = (fr⁻¹)ᴴ * (gᴴ * (frᴴ * J * fr) * g) * fr⁻¹ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (fr⁻¹)ᴴ * (frᴴ * J * fr) * fr⁻¹ := by rw [hJ, hg]
    _ = ((fr⁻¹)ᴴ * frᴴ) * J * (fr * fr⁻¹) := by simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem exp_form {n : ℕ} (G X : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G)
    (hX : Xᴴ * G + G * X = 0) : (NormedSpace.exp X)ᴴ * G * NormedSpace.exp X = G := by

  have hGd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hGG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hGd
  have hGG' : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hGd
  have hXc : G * (-X) * G⁻¹ = Xᴴ := by
    have h1 : Xᴴ * G = -(G * X) := eq_neg_of_add_eq_zero_left hX
    calc G * (-X) * G⁻¹ = -(G * X) * G⁻¹ := by rw [Matrix.mul_neg]
      _ = Xᴴ * G * G⁻¹ := by rw [h1]
      _ = Xᴴ := by rw [Matrix.mul_assoc, hGG', Matrix.mul_one]
  have hexpH : (NormedSpace.exp X)ᴴ = G * NormedSpace.exp (-X) * G⁻¹ := by
    rw [← Matrix.exp_conjTranspose, ← hXc, Matrix.exp_conj G (-X) hG]
  have hneg : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    rw [← Matrix.exp_add_of_commute (-X) X (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [hexpH]
  calc G * NormedSpace.exp (-X) * G⁻¹ * G * NormedSpace.exp X
      = G * (NormedSpace.exp (-X) * NormedSpace.exp X) := by
        simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc G⁻¹ G, hGG, Matrix.one_mul]
    _ = G := by rw [hneg, Matrix.mul_one]

theorem uh_mul {n : ℕ} (G g h : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH G) (hh : h ∈ Formalism.QuantumDeterminants.UH G) :
    g * h ∈ Formalism.QuantumDeterminants.UH G := by

  have h1 : gᴴ * G * g = G := hg
  have h2 : hᴴ * G * h = G := hh
  show (g * h)ᴴ * G * (g * h) = G
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * G * (g * h) = hᴴ * (gᴴ * G * g) * h := by simp only [Matrix.mul_assoc]
    _ = G := by rw [h1, h2]

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem gram_unit (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ) := by

  have hJ : Formalism.REAL.Jm (M.ε τ) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJu : IsUnit (Formalism.REAL.Jm (M.ε τ)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hJ)
  have hfr := M.fr_unit τ
  have hfrH : IsUnit (M.fr τ)ᴴ := (Matrix.isUnit_iff_isUnit_det _).2 (by
    rw [Matrix.det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hfr).star)
  rw [← M.fr_gram τ]
  exact (hfrH.mul hJu).mul hfr

theorem exp_mem_UH (M : DSModel V S) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hX : X ∈ lieAt V τ) (t : ℝ) : NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by

  have hG := gram_unit M τ
  have h1 : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  show (NormedSpace.exp (t • X))ᴴ * gramAt D V τ * NormedSpace.exp (t • X) = gramAt D V τ
  refine exp_form _ _ hG ?_
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1,
    smul_zero]

theorem rep_mul (M : DSModel V S) (τ : D.what₂.Tau) (g h : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hh : h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    M.rep τ (g * h) = (M.rep τ g).comp (M.rep τ h) := by

  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hfr' : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hd
  show M.σ τ (M.fr τ * (g * h) * (M.fr τ)⁻¹) =
    (M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)).comp (M.σ τ (M.fr τ * h * (M.fr τ)⁻¹))
  have e : M.fr τ * (g * h) * (M.fr τ)⁻¹ =
      (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * h * (M.fr τ)⁻¹) := by
    calc M.fr τ * (g * h) * (M.fr τ)⁻¹
        = M.fr τ * g * ((M.fr τ)⁻¹ * M.fr τ) * h * (M.fr τ)⁻¹ := by
          rw [hfr', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  have hmem : ∀ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * x * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := fun x hx =>
    conj_mem (Formalism.REAL.Jm (M.ε τ)) (gramAt D V τ) (M.fr τ) x (M.fr_unit τ) (M.fr_gram τ) hx
  exact (M.ds τ).2.2.1.1.2 _ (hmem g hg) _ (hmem h hh)

theorem rep_one (M : DSModel V S) (τ : D.what₂.Tau) : M.rep τ 1 = 1 := by

  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  show M.σ τ (M.fr τ * 1 * (M.fr τ)⁻¹) = 1
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]
  exact (M.ds τ).2.2.1.1.1

open Classical in

theorem orbit_eq (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M)
    (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ)
    (v : M.Vec) (t : ℝ) (hs : M.rep τ (NormedSpace.exp (t • X)) (v τ) ∈ M.sm τ) (x : GA D V) :
    T v (x * oneP θ V τ X t) = T (Function.update v τ ⟨_, hs⟩) x := by

  have h := hT.equiv τ _ (exp_mem_UH M τ X hX t) v ⟨_, hs⟩ rfl
  first
    | (rw [h]; rfl)
    | (refine Eq.trans ?_ (congrFun h x).symm; rfl)
    | (convert (congrFun h x).symm using 1)

lemma sum_isLittleO {ι F : Type*} [NormedAddCommGroup F] (L : List ι) (g : ι → ℝ → F)
    (h : ∀ l ∈ L, g l =o[𝓝 0] (fun t : ℝ => t - 0)) :
    (fun t => (L.map fun l => ‖g l t‖).sum) =o[𝓝 0] (fun t : ℝ => t - 0) := by

  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact isLittleO_zero _ _
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((h a (by simp)).norm_left).add (ih fun l hl => h l (by simp [hl]))

end Formalism.IndefR.Tow.OrbStPf

namespace Formalism.IndefR.Tow

open OrbStPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem orbitDerMult_holds (D : D7) : OrbitDerMult D := by
  classical
  intro θ _ V Ss M J χ T hT τ X hX v w hd x
  have hU1 : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    change (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ * 1 = gramAt D V τ
    simp
  have hUm : ∀ a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      a * b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun a ha b hb => uh_mul _ a b ha hb
  have hρ : ∀ a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.rep τ (a * b) = (M.rep τ a).comp (M.rep τ b) := fun a ha b hb => rep_mul M τ a b ha hb
  have hexp : ∀ Y ∈ lieAt V τ, ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
    fun Y hY t => exp_mem_UH M τ Y hY t
  have hρ1 : M.rep τ 1 = 1 := rep_one M τ
  have hsm : ∀ a, a ∈ M.sm τ ↔ SmoothVec (lieAt V τ) (M.rep τ) a := fun a => by
    unfold DSModel.sm; exact mem_span_smoothVec
  have hu : SmoothVec (lieAt V τ) (M.rep τ) (v τ) := (hsm _).1 (v τ).2
  have hw : SmoothVec (lieAt V τ) (M.rep τ) (w : M.H τ) := (hsm _).1 w.2
  obtain ⟨ℓ, hℓS, hℓ⟩ := hT.cont τ v x
  obtain ⟨SS, C, hSL, hC⟩ := hℓS
  have hut : ∀ t : ℝ, SmoothVec (lieAt V τ) (M.rep τ) (M.rep τ (NormedSpace.exp (t • X)) (v τ)) :=
    fun t => smoothVec_rep_exp hU1 hUm hρ hexp hX t hu
  have hf : ∀ t : ℝ, T v (x * oneP θ V τ X t) = ℓ (M.rep τ (NormedSpace.exp (t • X)) (v τ)) := by
    intro t
    have hs := (hsm _).2 (hut t)
    rw [orbit_eq θ M J χ T hT τ X hX v t hs x]
    exact (hℓ ⟨_, hs⟩).symm
  have hut0 : M.rep τ (NormedSpace.exp ((0 : ℝ) • X)) (v τ) = v τ := by
    simp [hρ1]
  let Dt : ℝ → M.H τ := fun t =>
    M.rep τ (NormedSpace.exp (t • X)) (v τ) + (-1 : ℝ) • (v τ : M.H τ) + (-t) • (w : M.H τ)
  have hDs : ∀ t, SmoothVec (lieAt V τ) (M.rep τ) (Dt t) := fun t =>
    smoothVec_add (smoothVec_add (hut t) (smoothVec_rsmul _ hu)) (smoothVec_rsmul _ hw)
  have hg : ∀ l ∈ SS, (fun t : ℝ => l.foldr (dRep (M.rep τ)) (Dt t)) =o[𝓝 0] (fun t : ℝ => t - 0) := by
    intro l hl
    have hL := hSL l hl
    have hder := word_deriv hU1 hUm hρ hexp hρ1 l hL hX hu hw hd
    refine (hasDerivAt_iff_isLittleO.1 hder).congr_left (fun t => ?_)
    simp only [Dt]
    rw [word_lin hU1 hUm hρ hexp hρ1 l hL hX (smoothVec_add (hut t) (smoothVec_rsmul _ hu)) hw,
      word_lin hU1 hUm hρ hexp hρ1 l hL hX (hut t) hu, hut0]
    simp only [neg_smul, one_smul, sub_eq_add_neg, neg_zero, add_zero]
  have hbig : (fun t => ℓ (Dt t)) =O[𝓝 0]
      (fun t => (SS.map fun l => ‖l.foldr (dRep (M.rep τ)) (Dt t)‖).sum) := by
    refine IsBigO.of_bound |C| (Filter.Eventually.of_forall fun t => ?_)
    have h1 := hC (Dt t) (hDs t)
    have hnn : 0 ≤ (SS.map fun l => ‖l.foldr (dRep (M.rep τ)) (Dt t)‖).sum :=
      List.sum_nonneg (fun a ha => by obtain ⟨l, -, rfl⟩ := List.mem_map.1 ha; exact norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hnn)
  have ho := hbig.trans_isLittleO (sum_isLittleO SS _ hg)
  rw [← hℓ w, hasDerivAt_iff_isLittleO]
  refine ho.congr_left (fun t => ?_)
  rw [hf t, hf 0, hut0]
  simp only [Dt, map_add, LinearMap.map_smul_of_tower, Complex.real_smul, sub_zero]
  push_cast
  ring

end Formalism.IndefR.Tow

end
