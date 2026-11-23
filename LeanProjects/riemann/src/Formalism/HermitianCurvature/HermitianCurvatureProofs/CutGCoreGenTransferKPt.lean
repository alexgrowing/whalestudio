import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GenTransferKapCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA

open Matrix Finset
open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KPt

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section refl

variable {k r : ℕ} {m : ℕ}

def reflB (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) : Q.Mx k r :=
  1 - (2 : ℂ) • ∑ a, vecMulVec (Bs a) (star (Bs a)) * Hpk k r

theorem reflB_mulVec (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    reflB (k := k) (r := r) Bs *ᵥ x = x - (2 : ℂ) • ∑ a, herm (Hpk k r) x (Bs a) • Bs a := by
  unfold reflB
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.sum_mulVec]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  congr 1

end refl

section frame

variable {k r : ℕ} {m : ℕ}

theorem hpk_herm' : (Hpk k r)ᴴ = Hpk k r := (Formalism.QuantumDeterminants.hpkFacts k r).1

theorem herm_conj (x y : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) y x = star (herm (Hpk k r) x y) :=
  (Formalism.FourierDecayAlt.P.SettingConstruction.herm_symm (Hpk k r) hpk_herm' x y).symm

theorem herm_proj {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hon : ∀ a b, herm (Hpk k r) (Bs a) (Bs b) = if a = b then 1 else 0) (x : Fin (2 * r + k + 1) → ℂ) (c : Fin m) :
    herm (Hpk k r) (∑ a, herm (Hpk k r) x (Bs a) • Bs a) (Bs c) = herm (Hpk k r) x (Bs c) := by
  have hsum : ∀ (s : Finset (Fin m)), herm (Hpk k r) (∑ a ∈ s, herm (Hpk k r) x (Bs a) • Bs a) (Bs c) =
      ∑ a ∈ s, herm (Hpk k r) x (Bs a) * herm (Hpk k r) (Bs a) (Bs c) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [herm]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Formalism.FourierDecayAlt.P.SettingConstruction.herm_add_left,
        Formalism.FourierDecayAlt.P.SettingConstruction.herm_smul_left, ih]
  rw [hsum, Finset.sum_eq_single c]
  · rw [hon, if_pos rfl, mul_one]
  · intro b _ hb; rw [hon, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ c) h

theorem reflB_unitary {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hon : ∀ a b, herm (Hpk k r) (Bs a) (Bs b) = if a = b then 1 else 0) :
    (reflB (k := k) (r := r) Bs)ᴴ * Hpk k r * reflB Bs = Hpk k r := by
  refine Formalism.FourierDecayAlt.P.SettingConstruction.unitary_of_form (Hpk k r) _ fun x y => ?_
  rw [reflB_mulVec, reflB_mulVec]
  set Px := ∑ a, herm (Hpk k r) x (Bs a) • Bs a
  set Py := ∑ a, herm (Hpk k r) y (Bs a) • Bs a

  have hPxy : herm (Hpk k r) Px y = herm (Hpk k r) Px Py := by

    have e1 : ∀ (s : Finset (Fin m)), herm (Hpk k r) (∑ a ∈ s, herm (Hpk k r) x (Bs a) • Bs a) y =
        ∑ a ∈ s, herm (Hpk k r) x (Bs a) * herm (Hpk k r) (Bs a) y := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [herm]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Formalism.FourierDecayAlt.P.SettingConstruction.herm_add_left,
          Formalism.FourierDecayAlt.P.SettingConstruction.herm_smul_left, ih]
    have e2 : ∀ (s : Finset (Fin m)), herm (Hpk k r) (∑ a ∈ s, herm (Hpk k r) x (Bs a) • Bs a) Py =
        ∑ a ∈ s, herm (Hpk k r) x (Bs a) * herm (Hpk k r) (Bs a) Py := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [herm]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Formalism.FourierDecayAlt.P.SettingConstruction.herm_add_left,
          Formalism.FourierDecayAlt.P.SettingConstruction.herm_smul_left, ih]
    rw [e1, e2]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [herm_conj y (Bs a), herm_conj Py (Bs a)]
    exact congrArg star (herm_proj hon y a).symm
  have hxPy : herm (Hpk k r) x Py = herm (Hpk k r) Px Py := by
    have h1 : herm (Hpk k r) x Py = star (herm (Hpk k r) Py x) := herm_conj Py x
    have h2 : herm (Hpk k r) Px Py = star (herm (Hpk k r) Py Px) := herm_conj Py Px

    have e1 : ∀ (s : Finset (Fin m)), herm (Hpk k r) (∑ a ∈ s, herm (Hpk k r) y (Bs a) • Bs a) x =
        ∑ a ∈ s, herm (Hpk k r) y (Bs a) * herm (Hpk k r) (Bs a) x := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [herm]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Formalism.FourierDecayAlt.P.SettingConstruction.herm_add_left,
          Formalism.FourierDecayAlt.P.SettingConstruction.herm_smul_left, ih]
    have e2 : ∀ (s : Finset (Fin m)), herm (Hpk k r) (∑ a ∈ s, herm (Hpk k r) y (Bs a) • Bs a) Px =
        ∑ a ∈ s, herm (Hpk k r) y (Bs a) * herm (Hpk k r) (Bs a) Px := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [herm]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Formalism.FourierDecayAlt.P.SettingConstruction.herm_add_left,
          Formalism.FourierDecayAlt.P.SettingConstruction.herm_smul_left, ih]
    rw [h1, h2, e1, e2]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [herm_conj x (Bs a), herm_conj Px (Bs a)]
    exact congrArg star (herm_proj hon x a).symm
  simp only [Formalism.FourierDecayAlt.P.SettingConstruction.herm_sub_left, Formalism.FourierDecayAlt.P.SettingConstruction.herm_sub_right, Formalism.FourierDecayAlt.P.SettingConstruction.herm_smul_left,
    Formalism.FourierDecayAlt.P.SettingConstruction.herm_smul_right]
  rw [hPxy, hxPy]
  have h2 : star (2 : ℂ) = 2 := by simp
  rw [h2]
  ring

end frame

section frame2

variable {k r : ℕ} {m : ℕ}

theorem reflB_fix {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} {x : Fin (2 * r + k + 1) → ℂ}
    (hx : ∀ a, herm (Hpk k r) x (Bs a) = 0) : reflB (k := k) (r := r) Bs *ᵥ x = x := by
  rw [reflB_mulVec]
  simp [hx]

theorem reflB_sq {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hon : ∀ a b, herm (Hpk k r) (Bs a) (Bs b) = if a = b then 1 else 0) :
    reflB (k := k) (r := r) Bs * reflB Bs = 1 := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  set x : Fin (2 * r + k + 1) → ℂ := Pi.single i 1
  rw [reflB_mulVec Bs x, reflB_mulVec Bs]
  have hP : ∀ c, herm (Hpk k r) (x - (2 : ℂ) • ∑ a, herm (Hpk k r) x (Bs a) • Bs a) (Bs c) =
      -herm (Hpk k r) x (Bs c) := by
    intro c
    rw [Formalism.FourierDecayAlt.P.SettingConstruction.herm_sub_left, Formalism.FourierDecayAlt.P.SettingConstruction.herm_smul_left, herm_proj hon x c]
    ring
  simp only [hP, neg_smul, Finset.sum_neg_distrib, smul_neg]
  abel

theorem reflB_mem_UWset {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} {w : Fin (2 * r + k + 1) → ℂ}
    (hB : ∀ a, inWb k r (Bs a)) (hon : ∀ a b, herm (Hpk k r) (Bs a) (Bs b) = if a = b then 1 else 0)
    (hw : ∀ a, herm (Hpk k r) (Bs a) w = 0) : reflB (k := k) (r := r) Bs ∈ UWset k r w := by
  have hout : ∀ i : Fin (2 * r + k + 1), ¬ Formalism.FourierDecayAlt.P.TwoByOneBlock.mid k r i → reflB (k := k) (r := r) Bs *ᵥ bvec i = bvec i :=
    fun i hi => reflB_fix fun a => Formalism.FourierDecayAlt.P.NFRadRedLocSec.herm_out (hB a) hi
  refine ⟨reflB_unitary hon, fun a => ⟨hout _ ?_, hout _ ?_⟩, reflB_fix fun a => ?_⟩
  · simp only [Formalism.FourierDecayAlt.P.TwoByOneBlock.mid, eI]; omega
  · simp only [Formalism.FourierDecayAlt.P.TwoByOneBlock.mid, esI]; omega
  · rw [herm_conj (Bs a) w, hw a, star_zero]

end frame2

section const

variable {k r : ℕ} {m : ℕ}

theorem frame_const {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hsec : CSec k r z z' μsec) {ζ₀ : ℂ} (hζ₀ : Tz k r z * Tz k r z' < Complex.normSq ζ₀)
    {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [(NF.muZ k r μsec ζ₀)⁻¹ *ᵥ z, z'] Bs) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    IsFrameOf k r [(NF.muZ k r μsec ζ)⁻¹ *ᵥ z, z'] Bs := by
  obtain ⟨hBw, hon, horth⟩ := hB
  set g₀ := NF.muZ k r μsec ζ₀ with hg₀def
  set g := NF.muZ k r μsec ζ with hgdef
  have hg₀ : g₀ ∈ Glev k r (Fin.last r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb hsec.1 hζ₀)
  have hg : g ∈ Glev k r (Fin.last r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb hsec.1 hζ)
  have hy₀ : ∀ a, herm (Hpk k r) (Bs a) (g₀⁻¹ *ᵥ z) = 0 := fun a => horth a _ (by simp)
  have hz'0 : ∀ a, herm (Hpk k r) (Bs a) z' = 0 := fun a => horth a _ (by simp)
  set R := reflB (k := k) (r := r) Bs with hRdef
  have hR : R ∈ UWset k r z' := reflB_mem_UWset hBw hon hz'0
  have hRR : R * R = 1 := reflB_sq hon
  have hRx₀ : R *ᵥ (g₀⁻¹ *ᵥ z) = g₀⁻¹ *ᵥ z :=
    reflB_fix fun a => by rw [herm_conj (Bs a) (g₀⁻¹ *ᵥ z), hy₀ a, star_zero]
  obtain ⟨hu₀1, hu₀2⟩ := Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.glev_unit hg₀
  obtain ⟨hu1, hu2⟩ := Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.glev_unit hg
  have hdetH : IsUnit (Hpk k r).det := by
    have := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_iff_exists_inv.2 ⟨_, this⟩
  have hG := Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) hdetH
  set h₀ := g₀ * R * g₀⁻¹ with hh₀def
  have hg₀inv : g₀⁻¹ ∈ UH (Hpk k r) := (hG.2.2 g₀ hg₀.1).2
  have hfix₀ : ∀ a : Fin r, g₀ *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g₀ *ᵥ bvec (esI k r a) = bvec (esI k r a) :=
    fun a => hg₀.2 a (by rw [Fin.val_last]; exact a.isLt)
  have hinvfix : ∀ v : Fin (2 * r + k + 1) → ℂ, g₀ *ᵥ v = v → g₀⁻¹ *ᵥ v = v := by
    intro v hv
    calc g₀⁻¹ *ᵥ v = g₀⁻¹ *ᵥ (g₀ *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hu₀1, Matrix.one_mulVec]
  have hh₀ : h₀ ∈ UWset k r z := by
    refine ⟨hG.2.1 _ (hG.2.1 _ hg₀.1 _ hR.1) _ hg₀inv, fun a => ⟨?_, ?_⟩, ?_⟩
    · rw [hh₀def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinvfix _ (hfix₀ a).1, (hR.2.1 a).1, (hfix₀ a).1]
    · rw [hh₀def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinvfix _ (hfix₀ a).2, (hR.2.1 a).2, (hfix₀ a).2]
    · rw [hh₀def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hRx₀, Matrix.mulVec_mulVec, hu₀2,
        Matrix.one_mulVec]
  have hst₀ : (h₀, R) ∈ NF.Stab k r z z' μsec ζ₀ := by
    refine ⟨hh₀, hR, ?_⟩
    show g₀ * R * g₀⁻¹ * g₀ * R = g₀
    rw [Matrix.mul_assoc (g₀ * R), hu₀1, Matrix.mul_one, Matrix.mul_assoc, hRR, Matrix.mul_one]
  have hst : (h₀, R) ∈ NF.Stab k r z z' μsec ζ := by
    rw [← hsec.2 ζ₀ ζ hζ₀ hζ]; exact hst₀
  have hrel : h₀ * g * R = g := hst.2.2
  have hh₀sq : h₀ * h₀ = 1 := by
    rw [hh₀def]
    calc g₀ * R * g₀⁻¹ * (g₀ * R * g₀⁻¹) = g₀ * (R * (g₀⁻¹ * g₀) * R) * g₀⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu₀1, Matrix.mul_one, hRR, Matrix.mul_one, hu₀2]
  set x := g⁻¹ *ᵥ z with hxdef
  have hgx : g *ᵥ x = z := by rw [hxdef, Matrix.mulVec_mulVec, hu2, Matrix.one_mulVec]
  have hRx : R *ᵥ x = x := by
    have e1 : h₀ *ᵥ (g *ᵥ (R *ᵥ x)) = z := by
      rw [Matrix.mulVec_mulVec (R *ᵥ x) h₀ g, Matrix.mulVec_mulVec x (h₀ * g) R, hrel, hgx]
    have e2 : g *ᵥ (R *ᵥ x) = z := by
      calc g *ᵥ (R *ᵥ x) = h₀ *ᵥ (h₀ *ᵥ (g *ᵥ (R *ᵥ x))) := by
            rw [Matrix.mulVec_mulVec (g *ᵥ (R *ᵥ x)) h₀ h₀, hh₀sq, Matrix.one_mulVec]
        _ = h₀ *ᵥ z := by rw [e1]
        _ = z := hh₀.2.2
    calc R *ᵥ x = g⁻¹ *ᵥ (g *ᵥ (R *ᵥ x)) := by
          rw [Matrix.mulVec_mulVec (R *ᵥ x) g⁻¹ g, hu1, Matrix.one_mulVec]
      _ = x := by rw [e2]
  have hPx : ∑ a, herm (Hpk k r) x (Bs a) • Bs a = 0 := by
    have := hRx
    rw [reflB_mulVec, sub_eq_self, smul_eq_zero] at this
    exact this.resolve_left two_ne_zero
  have hxB : ∀ a, herm (Hpk k r) (Bs a) x = 0 := by
    intro a
    have h1 := herm_proj hon x a
    rw [hPx] at h1
    have h0 : herm (Hpk k r) (0 : Fin (2 * r + k + 1) → ℂ) (Bs a) = 0 := by simp [herm]
    rw [h0] at h1
    rw [herm_conj x (Bs a), ← h1, star_zero]
  refine ⟨hBw, hon, fun a v hv => ?_⟩
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact hxB a
  · exact hz'0 a

end const

section main

open Formalism.FourierDecayAlt.P5.Kfp

variable {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def rk1 (u : Wq) : Wq →L[ℂ] Wq := (innerSL ℂ u).smulRight u

theorem rankOneInnerOperator_apply (u v : Wq) : rk1 u v = ⟪u, v⟫_ℂ • u := rfl

end main

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KPt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5.Kfp Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KPt

theorem gauge_kappa_pointwise_holds : GTKPt := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH
  obtain ⟨hPl, hk, hsec, hL, hS, hR, hQ⟩ := hH
  obtain ⟨hP, hz, hz', hTz, hTz', hπ, hπ'⟩ := hPl
  have hT : 0 < Tz P.k P.r Bs.z := by rw [hTz]; exact hP.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := by rw [hTz']; exact hP.T'_pos
  have hTT : P.TT = Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' := by rw [hTz, hTz']; rfl

  set ζ₀ : ℂ := ((Real.sqrt (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z') + 1 : ℝ) : ℂ) with hζ₀def
  have hζ₀ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ₀ := by
    rw [hζ₀def, Complex.normSq_ofReal]
    have h0 : 0 ≤ Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' := (mul_pos hT hT').le
    have hs := Real.sq_sqrt h0
    nlinarith [Real.sqrt_nonneg (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')]
  set g₀ := NF.muZ P.k P.r Bs.μsec ζ₀
  have hg₀ : g₀ ∈ Glev P.k P.r (Fin.last P.r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb hsec.1 hζ₀)
  have hGG₀ : GGl P.k P.r Bs.z Bs.z' g₀ ≠ 0 := by
    have := (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec.1 (q := ((fun _ => 1 : Fin P.r → ℂ), ζ₀))
      ⟨fun _ => one_ne_zero, hζ₀⟩).2.2
    exact this.ne'
  obtain ⟨Bs₀, -, -, hB1, -, -, -, -, -, -, -, -⟩ := Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.geom_package hz hz' hT hT' hg₀ hGG₀
  have hBz' : IsFrameOf P.k P.r [Bs.z'] Bs₀ := Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.frame_sub hB1 (by simp)
  have hπ'r := hπ'.2.1
  have hπ'c := hπ'.2.2.1
  have hu := hπ'.2.2.2.1
  obtain ⟨Y₀, hY₀⟩ := sep_real hP
  set w0 : ℝ := Y₀ + ((P.k : ℝ) - 2) / 2 with hw0
  set C : Module.End ℂ Wq := qdet (Formalism.FourierDecayAlt.Qr.EB Bs.π' Bs₀) (w0 : ℂ) with hCdef
  have hC : C.IsSymmetric := qdet_symm hπ'r hπ'c hu hBz' w0

  set n := Module.finrank ℂ Wq with hn
  set b := hC.eigenvectorBasis hn.symm with hbdef
  set lam : Fin n → ℝ := hC.eigenvalues hn.symm with hlamdef
  have hCb : ∀ i, C (b i) = (lam i : ℂ) • b i := fun i => hC.apply_eigenvectorBasis hn.symm i

  classical
  let ρ₀ : M.Ty P := Classical.arbitrary _
  let typeOf : ℂ → M.Ty P := fun μ => if h : ∃ ρ, M.xC P ρ (Y₀ : ℂ) = μ then h.choose else ρ₀
  have htype : ∀ ρ, typeOf (M.xC P ρ (Y₀ : ℂ)) = ρ := by
    intro ρ
    have h : ∃ ρ', M.xC P ρ' (Y₀ : ℂ) = M.xC P ρ (Y₀ : ℂ) := ⟨ρ, rfl⟩
    simp only [typeOf, dif_pos h]
    exact hY₀ h.choose_spec
  let QQ : M.Ty P → (Wq →L[ℂ] Wq) := fun ρ => ∑ i ∈ Finset.univ.filter (fun i => typeOf (lam i) = ρ), rk1 (b i)
  have hQapply : ∀ ρ v, QQ ρ v = ∑ i ∈ Finset.univ.filter (fun i => typeOf (lam i) = ρ), ⟪b i, v⟫_ℂ • b i := by
    intro ρ v
    simp only [QQ, ContinuousLinearMap.sum_apply, rankOneInnerOperator_apply]
  have hon : ∀ i j, ⟪b i, b j⟫_ℂ = if i = j then 1 else 0 := fun i j => by
    rw [orthonormal_iff_ite.mp b.orthonormal i j]
  have hcoef : ∀ (s : Finset (Fin n)) (v : Wq) (j : Fin n),
      ⟪b j, ∑ i ∈ s, ⟪b i, v⟫_ℂ • b i⟫_ℂ = if j ∈ s then ⟪b j, v⟫_ℂ else 0 := by
    intro s v j
    rw [inner_sum]
    simp only [inner_smul_right, hon, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  refine ⟨QQ, ?_, ?_, ?_, ?_⟩
  ·
    intro ρ σ
    ext v
    rw [ContinuousLinearMap.comp_apply, hQapply, hQapply]
    simp only [hcoef, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with hρσ
    · subst hρσ
      rw [hQapply]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_filter] at hi
      rw [if_pos hi.2]
    · simp only [ContinuousLinearMap.zero_apply]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_filter] at hi
      rw [if_neg (fun h => hρσ (hi.2.symm.trans h)), zero_smul]
  ·
    ext v
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.one_apply]
    simp only [hQapply]
    rw [Finset.sum_fiberwise (Finset.univ) (fun i => typeOf (lam i)) (fun i => ⟪b i, v⟫_ℂ • b i)]
    exact b.sum_repr' v
  ·
    intro ρ v w
    rw [hQapply, hQapply, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, inner_smul_right, inner_conj_symm]
    ring
  ·
    intro f Φ q
    have hq : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by rw [← hTT]; exact q.2.2
    set g := NF.muZ P.k P.r Bs.μsec q.1.2
    have hx : (q.1.1, g) ∈ DomR P.k P.r Bs.z Bs.z' :=
      Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec.1 (q := q.1) ⟨q.2.1, hq⟩
    have hBg : IsFrameOf P.k P.r [g⁻¹ *ᵥ Bs.z, Bs.z'] Bs₀ := frame_const hsec hζ₀ hB1 hq

    let N : Finset ℂ := Finset.univ.image (fun ρ => M.xC P ρ (Y₀ : ℂ)) ∪ Finset.univ.image (fun i => ((lam i : ℝ) : ℂ))
    let rv : ℂ → ℂ := fun μ => f (typeOf μ)
    set p := Lagrange.interpolate N id rv with hpdef
    have hpN : ∀ μ ∈ N, p.eval μ = f (typeOf μ) := by
      intro μ hμ
      have h := Lagrange.eval_interpolate_at_node rv (Set.injOn_id _) hμ
      simpa only [id] using h
    have hpx : ∀ ρ, p.eval (M.xC P ρ (Y₀ : ℂ)) = f ρ := by
      intro ρ
      rw [hpN _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ ρ))), htype]
    have hpl : ∀ i, p.eval ((lam i : ℝ) : ℂ) = f (typeOf (lam i)) :=
      fun i => hpN _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have hκ : d.κ f = Polynomial.aeval (d.x (Y₀ : ℂ)) p := kappa_aeval d (Y₀ : ℂ) p f hpx
    have hx1 : fstAlg _ (d.x (Y₀ : ℂ)) = X.fn 5 * X.t (Y₀ : ℂ) 1 1 := by
      have h : d.x (Y₀ : ℂ) = d.L.GGi * X.QQ (Y₀ : ℂ) 1 1 := by
        rw [hQ]
        simp only [NFData.QQ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val_zero]
        rw [← mul_assoc, d.L.GGi_GG, one_mul]
      rw [h, hL.2.2.2.2.2.2.2.2.2.2.2.1]
      rfl
    have hfst : (d.κ f).1 = Polynomial.aeval (X.fn 5 * X.t (Y₀ : ℂ) 1 1) p := by
      rw [← hx1, Polynomial.aeval_algHom_apply, hκ]
      rfl
    have hact : ∀ (Ψ : RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (v : Wq),
        (((X.fn 5 * X.t (Y₀ : ℂ) 1 1) Ψ : RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 g v =
          (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 g (C v) := by
      intro Ψ v
      rw [diagonal_transfer_action X hz hz' hπ'r hπ'c hx Bs₀ hBg (Y₀ : ℂ) Ψ v]
      congr 2
      rw [hCdef, hw0]
      push_cast
      ring_nf
    have haev : ∀ v : Wq, Polynomial.aeval C p v = ∑ ρ, f ρ • QQ ρ v := by
      intro v
      conv_lhs => rw [← b.sum_repr' v]
      rw [map_sum]
      have hb : ∀ i, Polynomial.aeval C p (⟪b i, v⟫_ℂ • b i) = (f (typeOf (lam i)) * ⟪b i, v⟫_ℂ) • b i := by
        intro i
        have hev : Module.End.HasEigenvector C ((lam i : ℝ) : ℂ) (b i) := hC.hasEigenvector_eigenvectorBasis hn.symm i
        rw [map_smul, Module.End.aeval_apply_of_hasEigenvector hev, hpl, smul_smul, mul_comm]
      simp only [hb, hQapply, Finset.smul_sum, smul_smul]
      rw [← Finset.sum_fiberwise (Finset.univ) (fun i => typeOf (lam i))
        (fun i => (f (typeOf (lam i)) * ⟪b i, v⟫_ℂ) • b i)]
      refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_filter] at hi
      rw [hi.2]
    refine ContinuousLinearMap.ext fun v => ?_
    rw [hfst, ContinuousLinearMap.comp_apply, aeval_act _ C hact p Φ v, haev v]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
