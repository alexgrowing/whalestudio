import Formalism.HermitianCurvature.HermitianCurvatureProofs.RootVectorActionCutoff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ResGContDiffAt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialRaisingTopOfParts

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.MC

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2

section claim

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
  (v₀ : VS k r 0 D E) (g₀ : Mx k r) (y : ℂ)

theorem torus_step (hTC : TorusCell) (hGP : GaugeP) (hg₀ : g₀ ∈ Glev k r (Fin.last r))
    (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D)
    (hdiff : ∀ x : SA E hD, ∀ c ∈ OmX r,
      DifferentiableAt ℝ (fun c' => ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) (wCell k r (Fin.last r) c' * g₀)) c)
    (l : Fin r) (x : SA E hD) (c : Fin r → ℂ) (hc : c ∈ OmX r) :
    Q.resG k r (Fin.last r) (((Tm (EA hD) ((y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ)) (eI k r l) (eI k r l) * x :
        SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ =
      y • Q.resG k r (Fin.last r) (((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E)) c g₀ +
        pOp l (fun c' => Q.resG k r (Fin.last r) (((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E)) c' g₀) c := by
  have hγ := hcell c hc
  set h : Mx k r → E := ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) with hh
  set H : (Fin r → ℂ) → E := fun c' => h (wCell k r (Fin.last r) c' * g₀) with hH
  have e1 : (((Tm (EA hD) ((y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ)) (eI k r l) (eI k r l) * x : SA E hD) :
      Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) (wCell k r (Fin.last r) c * g₀) =
      ((y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ)) • H c + pOp l H c := by
    simp only [Tm, Subalgebra.coe_mul, Subalgebra.coe_add, Module.End.mul_apply, LinearMap.add_apply, EA_val,
      Submodule.coe_add, Pi.add_apply, ite_true, if_true, Subalgebra.coe_algebraMap, Module.algebraMap_end_apply,
      Submodule.coe_smul, Pi.smul_apply]
    rw [ev_E hD _ _ _ hγ, posL_cI, hTC E k r D h hD ((x : Module.End ℂ (VS k r 0 D E)) v₀).2.1 c hc g₀ hg₀ hγ.2 l]
  rw [resG_last, e1]
  simp only [resG_last]
  rw [hGP E r (fun a => Mdim k r a - 1) H c hc (hdiff x c hc) l]
  have hw : (y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ) = y + ((Mdim k r l - 1 : ℕ) : ℂ) / 2 := by
    have hl := l.isLt
    have e : Mdim k r l - 1 = 2 * (r - l.val) + k := by simp [Mdim]
    rw [e]
    push_cast [Nat.cast_sub hl.le]
    ring
  rw [hw]
  module

end claim

theorem qminor_one {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (a b : Fin 1 → Fin n) (u : ℂ) :
    qminor E a b u = Tm E u (a 0) (b 0) := by
  unfold qminor
  rw [Fintype.sum_unique]
  simp [List.ofFn_succ]

theorem qminor_zero {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (a b : Fin 0 → Fin n) (u : ℂ) :
    qminor E a b u = 1 := by
  unfold qminor
  rw [Fintype.sum_unique]
  simp

section vab

variable {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem vAB_succ (y : ℂ) (i : ℕ) (hi : i < r) (G : (Fin r → ℂ) → V) :
    (Q.vAB r y (i + 1)).1 G = (fun c => y • (Q.vAB r y i).1 G c + pOp ⟨i, hi⟩ ((Q.vAB r y i).1 G) c -
      cOp ⟨i, hi⟩ ((Q.vAB r y i).2 G) c) ∧
    (Q.vAB r y (i + 1)).2 G = ciOp ⟨i, hi⟩ ((Q.vAB r y i).1 G) := by
  simp only [Q.vAB, dif_pos hi]
  exact ⟨funext fun c => rfl, trivial⟩

end vab

section claim2

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
  (v₀ : VS k r 0 D E) (g₀ : Mx k r) (y : ℂ)

theorem leftEq_cut (z : Fin (2 * r + k + 1) → ℂ) (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
    {f : Mx k r → E} (hLf : LeftEq k r z 0 D f) : LeftEq k r z 0 D (cut k r 0 D f) := by
  intro g hg n hn
  rw [cut_of_mem f ⟨Formalism.FourierDecayAlt.P.Qx3.glev_mul hn.2 hg.1, hN g hg n hn⟩, cut_of_mem f hg]
  exact hLf g hg n hn

theorem claim (hRR : RightRuleE) (hLR : LeftRuleCell) (hTC : TorusCell) (hGP : GaugeP)
    (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
    {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hLf : LeftEq k r z 0 D f) (hRf : RightEq k r z' 0 D f)
    (hv : v₀ = ⟨cut k r 0 D f, cut_mem hD hf⟩) (hg₀ : g₀ ∈ Glev k r (Fin.last r))
    (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D)
    (hdiff : ∀ x : SA E hD, ∀ c ∈ OmX r,
      DifferentiableAt ℝ (fun c' => ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) (wCell k r (Fin.last r) c' * g₀)) c)
    (hWS : ∀ x : SA E hD, resW ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) g₀ ∈ WSm r E) :
    ∀ (m : ℕ) (hm : m ≤ r), ∀ P ∈ Tor hD m, ∀ c ∈ OmX r,
      Q.resG k r (Fin.last r) (((qminor (EA hD) (C3.xR k r m hm) (C3.xR k r m hm) (y + ((2 * r + k : ℕ) : ℂ) / 2) * P :
          SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ =
        (Q.vAB r y m).1 (fun c' => Q.resG k r (Fin.last r) ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀) c := by
  have hLv : LeftEq k r z 0 D (v₀ : Mx k r → E) := by rw [hv]; exact leftEq_cut z hN hLf
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm P hP c hc
  rcases m with _ | _ | m
  · rw [qminor_zero, one_mul]
    rfl
  · rw [qminor_one]
    have hx0 : C3.xR k r 1 hm 0 = eI k r ⟨0, by omega⟩ := by ext; simp [C3.xR, eI]
    have hts := torus_step hD v₀ g₀ y hTC hGP hg₀ hcell hdiff ⟨0, by omega⟩ P c hc
    simp only [Fin.val_mk, Nat.cast_zero, sub_zero] at hts
    rw [hx0, hts, (vAB_succ y 0 (show 0 < r by omega) _).1]
    simp [Q.vAB, cOp]
  · have hm2 : m + 2 ≤ r := hm
    have hP1 : P ∈ Tor hD (m + 1) := Tor_mono hD (by omega) hP
    have hP0 : P ∈ Tor hD m := Tor_mono hD (by omega) hP
    set u : ℂ := y + ((2 * r + k : ℕ) : ℂ) / 2 with hu
    set LaP : SA E hD →ₗ[ℂ] E := (La hD v₀ (wCell k r (Fin.last r) c * g₀)).comp (LinearMap.mulRight ℂ P) with hLaP
    have hLaP_apply : ∀ x, LaP x = La hD v₀ (wCell k r (Fin.last r) c * g₀) (x * P) := fun x => rfl
    have hnot : ∀ (a : ℕ) (ha : a < m + 2), ∀ l' : Fin r, m + 2 ≤ l'.val → eI k r ⟨a, by omega⟩ ≠ eI k r l' := by
      intro a ha l' hl' e
      have := congrArg Fin.val e
      simp [eI] at this
      omega
    have hR0 : ∀ (x : SA E hD) (l : ℕ) (hl : l < m),
        LaP (x * EA hD (eI k r ⟨l, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = 0 := by
      intro x l hl
      rw [hLaP_apply, mul_assoc, (comm_Tor hD (m + 2) _ _ (hnot l (by omega)) (hnot (m + 1) (by omega)) P hP).eq,
        ← mul_assoc, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
      conv_lhs => rw [hv]
      rw [root_vector_action_cutoff hD z' hz' hRR hf hRf ⟨l, by omega⟩ ⟨m + 1, by omega⟩ (by simp; omega), if_neg (by simp; omega),
        zero_smul, map_zero]
      rfl
    have hR1 : ∀ x : SA E hD, LaP (x * EA hD (eI k r ⟨m, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = LaP x := by
      intro x
      rw [hLaP_apply, hLaP_apply, mul_assoc, (comm_Tor hD (m + 2) _ _ (hnot m (by omega)) (hnot (m + 1) (by omega)) P hP).eq,
        ← mul_assoc, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
      conv_lhs => rw [hv]
      rw [root_vector_action_cutoff hD z' hz' hRR hf hRf ⟨m, by omega⟩ ⟨m + 1, by omega⟩ (by simp), if_pos (by simp), one_smul, ← hv]
    have hL : ∀ (x : SA E hD) (q : ℕ) (hq : q ≤ m),
        LaP (EA hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨q, by omega⟩) * x) =
          (if q = m then c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩ else 0) • LaP x := by
      intro x q hq
      rw [hLaP_apply, hLaP_apply, mul_assoc, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply, EA_val,
        ev_E hD _ _ _ (hcell c hc), posL_cI, posL_cI]
      have hsm := (((x * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀).2.1
      have hle := leftEq_SA hD z hN (x * P) v₀ hLv
      rw [hLR E k r z D _ hz hD hN hsm hle c hc g₀ hg₀ (hcell c hc).2 ⟨m + 1, by omega⟩ ⟨q, by omega⟩ (by simp; omega)]
      congr 1
      by_cases hqm : q = m
      · subst hqm
        simp
      · rw [if_neg (by simp; omega), if_neg hqm]
    have hX := Formalism.FourierDecayAlt.P.PBN.chainX1' k r c (EA (E := E) hD) LaP (EA_gl (E := E) hD) m hm2 u hR0 hR1 hL

    set T := Tm (EA (E := E) hD) (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) with hT
    have hTmem : T ∈ Tor hD (m + 1) := by
      rw [hT]
      unfold Tm
      rw [if_pos rfl]
      exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (EA_mem_Tor hD ⟨m + 1, by omega⟩ le_rfl)
    have hTP : T * P ∈ Tor hD (m + 1) := Subalgebra.mul_mem _ hTmem hP1
    have ih1 := ih (m + 1) (by omega) (by omega) (T * P) hTP c hc
    have ih0 := ih m (by omega) (by omega) P hP0 c hc

    have eL : Q.resG k r (Fin.last r) (((qminor (EA hD) (C3.xR k r (m + 2) hm) (C3.xR k r (m + 2) hm) u * P :
        SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ =
        Q.resG k r (Fin.last r) (((qminor (EA hD) (C3.xR k r (m + 1) (by omega)) (C3.xR k r (m + 1) (by omega)) u *
          (T * P) : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ -
        (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • Q.resG k r (Fin.last r)
          (((qminor (EA hD) (C3.xR k r m (by omega)) (C3.xR k r m (by omega)) u * P : SA E hD) :
            Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ := by
      rw [resG_last, resG_last, resG_last]
      have key : ∀ (s t : ℂ) (a b d : E), a = b - t • d → s • a = s • b - t • (s • d) := by
        intro s t a b d h
        rw [h, smul_sub, smul_comm]
      apply key
      have h2 := hX
      simp only [hLaP_apply, La_apply, mul_assoc] at h2
      exact h2
    rw [eL, ih1, ih0]

    obtain ⟨G', hG'def⟩ : ∃ G' : (Fin r → ℂ) → E,
        G' = resW ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) g₀ := ⟨_, rfl⟩
    have hG' : G' ∈ WSm r E := hG'def ▸ hWS P
    have hGG' : ∀ c' ∈ OmX r,
        Q.resG k r (Fin.last r) ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀ = G' c' := by
      intro c' hc'
      rw [hG'def, wsm_resG_eq _ _ hc']
    have hTS : ∀ c' ∈ OmX r,
        Q.resG k r (Fin.last r) (((T * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀ =
          (pOp ⟨m + 1, by omega⟩ G' + y • G') c' := by
      intro c' hc'
      have hts := torus_step hD v₀ g₀ y hTC hGP hg₀ hcell hdiff ⟨m + 1, by omega⟩ P c' hc'
      rw [hT, hts, Pi.add_apply, Pi.smul_apply, hGG' c' hc',
        pOp_locO ⟨m + 1, by omega⟩ (fun c'' hc'' => hGG' c'' hc'') hc', add_comm]
    rw [(vAB_loc y (m + 1) _ _ hTS c hc).1, (vAB_loc y m _ _ hGG' c hc).1, (vAB_loc y (m + 2) _ _ hGG' c hc).1]
    have hpG : pOp ⟨m + 1, by omega⟩ G' ∈ WSm r E := opL_mem ⟨m + 1, by omega⟩ 0 hG'
    rw [(vAB_lin y (m + 1) hpG hG' y).1, (vAB_comm y ⟨m + 1, by omega⟩ (m + 1) le_rfl hG').2.2.1]
    rw [(vAB_succ y (m + 1) (by omega) G').1, (vAB_succ y m (by omega) G').2]
    simp only [Pi.add_apply, Pi.smul_apply, cOp, ciOp, div_eq_mul_inv, mul_smul]
    abel

end claim2

end Formalism.FourierDecayAlt.P.PBN.MC
