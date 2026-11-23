import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct ContDiff Topology

namespace UpperTheory.V.Lit.Geo.Cs

section An

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

def Sz (k : ℕ) (f : V → F) (p : V) (b : ℝ) : Prop := ∀ i ≤ k, ‖iteratedFDeriv ℝ i f p‖ ≤ b

theorem Sz.mono {k : ℕ} {f : V → F} {p : V} {b c : ℝ} (h : Sz k f p b) (hb : b ≤ c) : Sz k f p c :=
  fun i hi => (h i hi).trans hb

theorem Sz.of_le {k l : ℕ} {f : V → F} {p : V} {b : ℝ} (h : Sz k f p b) (hl : l ≤ k) : Sz l f p b :=
  fun i hi => h i (hi.trans hl)

theorem Sz.norm_le {k : ℕ} {f : V → F} {p : V} {b : ℝ} (h : Sz k f p b) : ‖f p‖ ≤ b := by
  simpa using h 0 (Nat.zero_le k)

theorem Sz.nonneg {k : ℕ} {f : V → F} {p : V} {b : ℝ} (h : Sz k f p b) : 0 ≤ b := (norm_nonneg _).trans h.norm_le

theorem Sz.congr {k : ℕ} {f g : V → F} {p : V} {b : ℝ} (h : Sz k f p b) (e : f =ᶠ[𝓝 p] g) : Sz k g p b :=
  fun i hi => by rw [← (e.iteratedFDeriv ℝ i).eq_of_nhds]; exact h i hi

theorem exists_sz (k : ℕ) (f : V → F) (p : V) : ∃ b, Sz k f p b :=
  ⟨∑ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i f p‖, fun i hi =>
    Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i f p‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))⟩

def tp (A : V →L[ℝ] V) (B : F →L[ℝ] F) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) : V [⋀^Fin q]→L[ℝ] F :=
  B.compContinuousAlternatingMap ((w (A p)).compContinuousLinearMap A)

theorem tp_apply (A : V →L[ℝ] V) (B : F →L[ℝ] F) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) (v : Fin q → V) :
    tp A B w p v = B (w (A p) fun i => A (v i)) := rfl

theorem tp_tp (A A' : V →L[ℝ] V) (B B' : F →L[ℝ] F) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) :
    tp A B (tp A' B' w) = tp (A' * A) (B * B') w := rfl

theorem tp_one {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) : tp 1 1 w = w := rfl

end An

section Geo

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Dr.Geo Γ V S d)

def Inv {q : ℕ} (w : G.Om q) : Prop := ∀ γ, G.act q γ w = w

def IsFun (Φ : S → V → ℝ) : Prop :=
  (∀ s, ContDiffOn ℝ ∞ (Φ s) G.Y) ∧ (∀ γ s, ∀ p ∈ G.Y, Φ (G.σ γ s) (G.ρ γ p) = Φ s p) ∧
    ∀ s (t : ℝ), 0 < t → ∀ p ∈ G.Y, Φ s (t • p) = Φ s p

theorem isFun_zero : IsFun G 0 := ⟨fun _ => contDiffOn_const, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

end Geo

section Ad

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def pt (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) : GA E a := infGL E a g * finGL E a x

theorem pt_mul (g h : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) : pt (g * h) x = pt g x * infGL E a h := by
  rw [pt, pt, map_mul, mul_assoc, infGL_comm, mul_assoc]

omit [IsTotallyComplex E] in

def Bnd (c : ℝ) (h : GL (Fin a) (Cinf E)) : Prop := ‖toL h.val‖ ≤ c ∧ ‖toL (h⁻¹).val‖ ≤ c

structure IsLam (lam : GA E a → ℝ) : Prop where
  add : ∀ g h, lam (g * h) = lam g + lam h
  split : ∀ g, splitCentre E a (lam g) * (retractOne g : KernelIndexFullLattice.G1 E a).1 = g
  bdd : ∀ c : ℝ, ∃ B : ℝ, ∀ h, Bnd c h → |lam (infGL E a h)| ≤ B

variable (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)

abbrev Fm (q : ℕ) : Type := (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ)

def Tw {q : ℕ} (w : Fm U Ξ q) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) :
    HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ) :=
  tp (sand g) (mulVecL (Ξ.mat g⁻¹)) (w (x : GL (Fin a) (Af E) ⧸ U))

def Dec (f lam : GA E a → ℝ) (f₀ : ℝ) (k : ℕ) (A B M : ℝ) {q : ℕ} (w : Fm U Ξ q) : Prop :=
  ∀ g x, f₀ ≤ f (pt g x) → Sz k (Tw U Ξ w g x) (hOne E a) (M * Real.exp (B * |lam (pt g x)| - A * f (pt g x)))

theorem Dec.mono {f lam : GA E a → ℝ} {f₀ f₁ : ℝ} {k : ℕ} {A B M : ℝ} {q : ℕ} {w : Fm U Ξ q}
    (h : Dec U Ξ f lam f₀ k A B M w) (hf : f₀ ≤ f₁) : Dec U Ξ f lam f₁ k A B M w := fun g x hg => h g x (hf.trans hg)

theorem Dec.of_le {f lam : GA E a → ℝ} {f₀ : ℝ} {k : ℕ} {A B M M' : ℝ} {q : ℕ} {w : Fm U Ξ q}
    (h : Dec U Ξ f lam f₀ k A B M w) (hM : M ≤ M') : Dec U Ξ f lam f₀ k A B M' w :=
  fun g x hg => (h g x hg).mono (mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le)

theorem Tw_one {q : ℕ} (w : Fm U Ξ q) (x : GL (Fin a) (Af E)) : Tw U Ξ w 1 x = w (x : GL (Fin a) (Af E) ⧸ U) := by
  funext p
  ext v j
  simp [Tw, tp_apply]

theorem Tw_eq {q : ℕ} (w : Fm U Ξ q) (g h : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) :
    Tw U Ξ w g x = tp (sand h⁻¹) (mulVecL (Ξ.mat h)) (Tw U Ξ w (g * h) x) := by
  have e : ∀ p : HV E a, sand (g * h) (sand h⁻¹ p) = sand g p := fun p => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel_right]
  funext p
  refine ContinuousAlternatingMap.ext fun v => ?_
  simp only [Tw, tp_apply, e, mulVecL_apply, Matrix.mulVec_mulVec, ← map_mul, _root_.mul_inv_rev, mul_inv_cancel_left]

def Desc (f : GA E a → ℝ) (Φ : (GL (Fin a) (Af E) ⧸ U) → HV E a → ℝ) : Prop :=
  ∀ (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)), Φ (x : GL (Fin a) (Af E) ⧸ U) (sand g (hOne E a)) = f (pt g x)

omit [IsTotallyComplex E] in

def Zw (Z : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (p : HV E a) :
    HV E a := sand g⁻¹ (Z (x : GL (Fin a) (Af E) ⧸ U) (sand g p))

end Ad

end UpperTheory.V.Lit.Geo.Cs
