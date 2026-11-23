import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchCoordinatesOfSurjectivity
import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.LocalGlobalOfBasisIndependence
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.GroupActionMulSingleEqDilation

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable {D : D7} {u : D.what₂.Word}

def RatInC (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ P ∈ RatSpan D ((D.fm u).lam 0), P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam 0)

def RatGL (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ (γ : D.what₂.Tau → GL (Fin (D.R.N 0)) D.host.E), ∀ P ∈ RatSpan D ((D.fm u).lam 0),
    MvPolynomial.C (∏ τ, (atInf (embT D) ((γ τ : GL (Fin (D.R.N 0)) D.host.E) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^ shiftOf (lamT u 0) τ) *
      subP (fun τ => atInf (embT D) ((γ τ : GL (Fin (D.R.N 0)) D.host.E) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ) P ∈ RatSpan D ((D.fm u).lam 0)

theorem intSpan_le_rat (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) :
    Formalism.L2.Forms.IntSpan D w lam ≤ RatSpan D lam := by
  apply AddSubgroup.closure_mono
  rintro p ⟨r, f, -, hf, rfl⟩
  exact ⟨r, f, hf, rfl⟩

theorem mem_intSubm (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N)
    (p : MvPolynomial (D.what₂.Tau × Fin N × Fin N) ℂ) : p ∈ intSubm D w lam → p ∈ Formalism.L2.Forms.IntSpan D w lam := by
  intro hp
  induction hp using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact (Formalism.L2.Forms.IntSpan D w lam).zero_mem
  | add x y _ _ hx hy => exact (Formalism.L2.Forms.IntSpan D w lam).add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨r, hr, hra⟩ := Subring.mem_map.mp a.2
    have ha : a • x = D.what₂.embLL r • x := by
      rw [Subring.smul_def, hra]
    rw [ha]
    exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_intSpan_smul (D := D) w lam r hr hx

theorem crd_surj (T : Forms0 D u) (hA : admS D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (Q : (D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ)
    (hQ : ∀ c, ∃ P ∈ RatSpan D ((D.fm u).lam 0), P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam 0) ∧
      ∀ y, fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0)) 1 P y =
        fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0))
          (atInf (embT D) ((B c)⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) (Q c) y) :
    ∃ x : ((D.fm u).lat 0).V, ∀ c, IsCrd T (B c) x c (Q c) := by
  let φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ := fun c z =>
    fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0))
      (atInf (embT D) ((B c)⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) (Q c) (T.val0.eY z)
  have hFi : φ ∈ (D.fm u).Fi 0 := by
    rw [(D.fm u).Fi_zero, S0.mem_forms_level_zero_iff T hA φ]
    intro c
    obtain ⟨P, -, hPC, hPe⟩ := hQ c
    refine ⟨P, hPC, ?_⟩
    funext y
    have e := hPe y
    rw [lamT_zero] at e
    simp only [φ, LinearMap.funLeft_apply]
    rw [lamT_zero, e]
    exact congrArg _ (T.val0.eY.apply_symm_apply y).symm
  obtain ⟨x, hx⟩ := (T.val0.rat φ).2 ⟨hFi, fun c => by
    obtain ⟨P, hPR, -, hPe⟩ := hQ c
    exact ⟨P, hPR, fun z => (hPe _).symm⟩⟩
  exact ⟨x, fun c z => by rw [hx]⟩

theorem fnOf_frame (B : GL (Fin (D.R.N 0)) D.host.E)
    (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ) (y) :
    fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0)) 1
        (MvPolynomial.C (∏ τ, (atInf (embT D) ((B⁻¹ : GL (Fin (D.R.N 0)) D.host.E) :
          Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^ shiftOf (lamT u 0) τ) *
          subP (fun τ => atInf (embT D) ((B⁻¹ : GL (Fin (D.R.N 0)) D.host.E) :
            Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ) Q) y =
      fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0))
        (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) Q y := by
  have key : ∀ (A z : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ)
      (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ),
      MvPolynomial.eval (fun x => z x.1 x.2.1 x.2.2) (subP A P) =
        MvPolynomial.eval (fun x => (A x.1 * z x.1) x.2.1 x.2.2) P := by
    intro A z P
    induction P using MvPolynomial.induction_on with
    | C a => simp [subP]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp [subP, Matrix.mul_apply]
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, map_mul, MvPolynomial.eval_C, Pi.one_apply, Matrix.one_mul]
  rw [key _ (fun τ => y.1 τ)]
  simp only [Matrix.det_mul, mul_zpow, mul_pow, Finset.prod_mul_distrib]
  ring

theorem onto_tL (hRC : RatInC D u) (hRG : RatGL D u) (T : Forms0 D u) (hA : admS D u) (w : D.what₂.places.Pl)
    (hw : OverT D u w) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c)) (b : ℤ) :
    (Submodule.pi Set.univ fun _ => (intSubm D w ((D.fm u).lam 0)).map
      (scO (bwA_Ow D w) _ (((D.mem u).A.T : ℂ) ^ b))) ≤ (tL D u w b ((D.fm u).S 0 w)).map (crdL T B w) := by
  intro y hy
  have hy' : ∀ c, ∃ q ∈ intSubm D w ((D.fm u).lam 0), (((D.mem u).A.T : ℂ) ^ b) • q = y c := fun c =>
    hy c (Set.mem_univ c)
  choose Q hQ hQy using hy'
  have hQI : ∀ c, Q c ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0) := fun c => mem_intSubm w _ _ (hQ c)
  obtain ⟨x₀, hx₀⟩ := crd_surj T hA B Q fun c =>
    ⟨_, hRG (fun _ => (B c)⁻¹) _ (intSpan_le_rat w _ (hQI c)), hRC _ (hRG (fun _ => (B c)⁻¹) _ (intSpan_le_rat w _ (hQI c))),
      fun y => fnOf_frame (B c) (Q c) y⟩
  have hx₀S : x₀ ∈ (D.fm u).S 0 w :=
    G0.local_global_lattice_level_zero D u T w hw 0 (Nat.zero_le _) rfl x₀ fun c => ⟨B c, hB c, Q c, hQI c, hx₀ c⟩
  let r : D.what₂.LL := ((D.mem u).A.T : D.what₂.LL) ^ b
  have hr : D.what₂.embLL r = ((D.mem u).A.T : ℂ) ^ b := by
    simp only [r, map_zpow₀, map_natCast]
  refine ⟨r • x₀, ⟨x₀, hx₀S, ?_⟩, ?_⟩
  · rw [LinearMap.map_smulₛₗ, hr]
    rfl
  · funext c
    show crd T B (r • x₀) c = y c
    rw [crd_smul T B r x₀ c, hr, crd_eq T B (hx₀ c), hQy c]

end Formalism.L2.GlobalTheoryTheory.LemB
