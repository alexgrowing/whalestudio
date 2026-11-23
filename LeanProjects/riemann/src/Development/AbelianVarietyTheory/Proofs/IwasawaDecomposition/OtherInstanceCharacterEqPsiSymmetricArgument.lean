import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

variable {D : D7}

def wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :=
  Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)
    {c | ∃ a : 𝓞 X.B.I.E, (∃ b ∈ w.asIdeal, X.ιE (a : X.B.I.E) = (b : D.host.E)) ∧
      c = Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E)}

def ModW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ}
    (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (t : ZMod g) : Prop :=
  c - ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w

def argS (X : HidaSetting D) (x : X.B.I.Gf) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F :=
  (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat x *ᵥ nxt X.e0 X.z0 a)) +
    ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0

theorem otherInstanceCharacter_eq_psi_symmetricArgument (X : HidaSetting D) (x : X.B.I.Gf) :
    X.chi2 x = X.psiEf (divN X.B.I X.B.g (argS X x)) := rfl

open Classical in

def side (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Bool := decide (GlobalTheory.Mem.SymFrame.EwAt X w)

def wtA (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 1 else if i.1 + 1 < ρ + k then (if s then 1 else 0) else 0

def wtB (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 0 else if i.1 + 1 < ρ + k then (if s then 0 else -1) else if i.1 = ρ + k then 1 else -1

theorem wt_add (ρ k : ℕ) (s : Bool) {r : ℕ} (i j : Fin r) :
    wtA ρ k s i j + wtB ρ k s i j = 1 ∨ wtA ρ k s i j + wtB ρ k s i j = -1 := by
  unfold wtA wtB
  split_ifs <;> simp

theorem hA_smul_right' (X : HidaSetting D) (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (x y : VA X.B.I) :
    hA X.B.I x (c • y) = c * hA X.B.I x y := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hA_add_right' (X : HidaSetting D) (x y z : VA X.B.I) :
    hA X.B.I x (y + z) = hA X.B.I x y + hA X.B.I x z := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hA_zero_right' (X : HidaSetting D) (x : VA X.B.I) : hA X.B.I x 0 = 0 := by
  simp [hA, Formalism.UG.hform]

theorem hA_mem_wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {x v : VA X.B.I} (hx : x ∈ X.B.I.Lf)
    (hv : v ∈ wLf X w) : hA X.B.I x v ∈ wInt X w := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨y, hy⟩, rfl⟩ := hv
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, y', hy', rfl⟩ := hy
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((a : X.B.I.E) • y') i)) =
          Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) •
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (y' i)) := by
        funext i; simp [map_mul]
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((a : X.B.I.E) • y') i)) ∈ wInt X w
      rw [e, hA_smul_right']
      have hint : hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (y' i)) ∈
          Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
        GlobalTheory.St.G.FrameClose.hA_int hx (Submodule.subset_span ⟨⟨y', hy'⟩, rfl⟩)
      rw [mul_comm]
      exact (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)
        (Submodule.subset_span ⟨a, ha, rfl⟩)
    | zero =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((0 : Fin X.B.I.n → X.B.I.E) i)) = 0 := by
        funext i; simp
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((0 : Fin X.B.I.n → X.B.I.E) i)) ∈ wInt X w
      rw [e, hA_zero_right']; exact zero_mem _
    | add a b _ _ ha hb =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((a + b) i)) =
          (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a i)) +
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (b i)) := by
        funext i; simp
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((a + b) i)) ∈ wInt X w
      rw [e, hA_add_right']; exact add_mem ha hb
    | smul c a _ ha =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((c • a) i)) =
          Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (c : X.B.I.E) •
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a i)) := by
        funext i; simp [Algebra.smul_def, map_mul]
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((c • a) i)) ∈ wInt X w
      rw [e, hA_smul_right']
      have hc : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (c : X.B.I.E) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
        Formalism.UG.P.easyc_inclE_mem _ _ _ (by first | exact ⟨c, rfl⟩ | exact c.2 | simp [Formalism.UG.intOE])
      exact (wInt X w).smul_mem (⟨_, hc⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) ha
  | zero => rw [hA_zero_right']; exact zero_mem _
  | add a b _ _ ha hb => rw [hA_add_right']; exact add_mem ha hb
  | smul c a _ ha =>
    show hA X.B.I x ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • a) ∈ wInt X w
    rw [hA_smul_right']
    exact (wInt X w).smul_mem c ha

theorem hA_sub_right' (X : HidaSetting D) (x y z : VA X.B.I) :
    hA X.B.I x (y - z) = hA X.B.I x y - hA X.B.I x z := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hA_sum_right' (X : HidaSetting D) {ι : Type} (s : Finset ι) (x : VA X.B.I) (y : ι → VA X.B.I) :
    hA X.B.I x (∑ j ∈ s, y j) = ∑ j ∈ s, hA X.B.I x (y j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact hA_zero_right' X x
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hA_add_right', ih]

theorem hA_isMatIn (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} {u : Fin D.R.r → VA X.B.I}
    {x : X.B.I.Gf} {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)} (hN : GlobalTheory.Mem.SymFrame.IsMatIn X w u x N)
    {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) (i : Fin D.R.r) :
    hA X.B.I y (X.B.I.fmat x *ᵥ u i) -
      ∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I y (u j) ∈ wInt X w := by
  have h := hA_mem_wInt X w hy (hN i)
  rw [hA_sub_right', hA_sum_right'] at h
  simpa only [hA_smul_right'] using h

theorem wInt_of_zmod (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}
    (hc : ZMod' X.B.I X.B.g c) : c ∈ wInt X w := by
  obtain ⟨t, ht, rfl⟩ := hc
  obtain ⟨m, hm⟩ : D.host.g k ∣ X.B.g := by
    rw [X.g_eq]; fin_cases k
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have hgen : ((D.host.g k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
    refine Submodule.subset_span ⟨(D.host.g k : 𝓞 X.B.I.E), ⟨_, hg, ?_⟩, ?_⟩
    · simp
    · simp
  have e : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t =
      ((m : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t) * (D.host.g k : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    rw [hm, Nat.cast_mul]; ring
  rw [e]
  exact (wInt X w).smul_mem (⟨_, mul_mem (natCast_mem _ m) ht⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hgen

end GlobalTheory.Mem.SymChar
