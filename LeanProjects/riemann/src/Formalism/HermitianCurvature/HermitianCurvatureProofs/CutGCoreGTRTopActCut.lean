import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCTheta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def QTop : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (h : ℂ),
    ∃ d : ℕ → A, (∀ Y : ℂ, qminor E id id (Y + h) = ∑ j ∈ Finset.range (n + 1), Y ^ j • d j) ∧
      (1 ≤ n → d (n - 1) = ∑ a, E a a + algebraMap ℂ A ((n : ℂ) * h - (n : ℂ) * ((n : ℂ) - 1) / 2))

theorem interp {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (W : Matrix (Fin N) (Fin N) ℂ)
    (hW : W * Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)) = 1) (p : ℂ → V) (a : ℕ → V)
    (ha : ∀ Y, p Y = ∑ j ∈ Finset.range N, Y ^ j • a j) (j : Fin N) :
    ∑ i : Fin N, W j i • p ((i : ℕ) : ℂ) = a j := by
  have key : ∀ l : Fin N, ∑ i : Fin N, W j i * ((i : ℕ) : ℂ) ^ (l : ℕ) = if j = l then 1 else 0 := by
    intro l
    have h := congrFun (congrFun hW j) l
    simpa [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.one_apply] using h
  simp_rw [ha, Finset.sum_range, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, key, ite_smul, one_smul, zero_smul]
  simp

theorem vdm_inv (N : ℕ) : ∃ W : Matrix (Fin N) (Fin N) ℂ,
    W * Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)) = 1 := by
  refine ⟨(Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)))⁻¹, Matrix.nonsing_inv_mul _ ?_⟩
  rw [isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
  intro a b h
  exact Fin.ext (Nat.cast_injective h)

theorem pt_poly (hQ : QTop) {k r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (D : Set (Mx k r)) (hD : IsOpen D) (f : Mx k r → V) (hf : SmoothLev k r (Fin.last r) D f)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    ∃ a : ℕ → V, (∀ Y : ℂ, capL k r (Fin.last r) (uC k r (Fin.last r) Y) f g =
        ∑ j ∈ Finset.range (mdim k r (Fin.last r) + 1), Y ^ j • a j) ∧
      a (mdim k r (Fin.last r) - 1) = ∑ b : Fin (mdim k r (Fin.last r)),
        EH k r (posL k r (Fin.last r) b) (posL k r (Fin.last r) b) f g := by
  obtain ⟨d, hd, htop⟩ := hQ (Module.End ℂ (SV k r (Fin.last r) D V)) (mdim k r (Fin.last r))
    (EV k r (Fin.last r) D V) (((mdim k r (Fin.last r) : ℂ) - 1) / 2)
  refine ⟨fun j => (d j (mkV hD f hf)).1 g, fun Y => ?_, ?_⟩
  · have h1 := (OperatorRepresentations.rep_qminor (E := V) hD (id : Fin (mdim k r (Fin.last r)) → Fin (mdim k r (Fin.last r))) id
      (uC k r (Fin.last r) Y)).mkV hD hf hg
    simp only [Function.comp_id] at h1
    have e : uC k r (Fin.last r) Y = Y + ((mdim k r (Fin.last r) : ℂ) - 1) / 2 := rfl
    unfold capL
    rw [← h1, e, hd Y, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
  · have hn1 : 1 ≤ mdim k r (Fin.last r) := by simp [mdim]
    show (d (mdim k r (Fin.last r) - 1) (mkV hD f hf)).1 g = _
    rw [htop hn1]
    have e0 : ((mdim k r (Fin.last r) : ℂ) * (((mdim k r (Fin.last r) : ℂ) - 1) / 2) -
        (mdim k r (Fin.last r) : ℂ) * ((mdim k r (Fin.last r) : ℂ) - 1) / 2) = 0 := by ring
    rw [e0, map_zero, add_zero, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun b _ => (OperatorRepresentations.rep_EV (E := V) hD b b).mkV hD hf hg

theorem mdim_last (k r : ℕ) : mdim k r (Fin.last r) = k + 1 := by
  simp [Q.mdim]

theorem gTRTopAct_of_cut (hQ : QTop) : GTRTopAct := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' hpl hk X
  obtain ⟨W, hW⟩ := vdm_inv (P.k + 2)

  have hpt : ∀ (Φ : RadSp P.k P.r z z' π π'), ∀ x ∈ DomR P.k P.r z z',
      ∃ a : ℕ → (Wq →L[ℂ] Wp), (∀ Y : ℂ, ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          ∑ j ∈ Finset.range (P.k + 2), Y ^ j • a j) ∧
        a P.k = ∑ b : Fin (mdim P.k P.r (Fin.last P.r)),
          EH P.k P.r (posL P.k P.r (Fin.last P.r) b) (posL P.k P.r (Fin.last P.r) b)
            ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2 := by
    intro Φ x hx
    have hmem := Φ.2
    obtain ⟨_, hs, _⟩ := hmem
    obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x hx
    set D : Set (Mx P.k P.r) := {g | (x.1, g) ∈ U} with hDdef
    have hc : ContDiff ℝ ∞ (fun g : Mx P.k P.r => (x.1, g)) := contDiff_prodMk_right x.1
    have hD : IsOpen D := hU.preimage hc.continuous
    have hf : SmoothLev P.k P.r (Fin.last P.r) D ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) := by
      intro g₀ hg₀
      refine ⟨D, fun g => F (x.1, g), hD, hg₀.2, ?_, fun g hgD hgG => hΦ (x.1, g) hgD hgG⟩
      exact hF.comp hc.contDiffOn (fun g hg => hg)
    have hg : x.2 ∈ Glev P.k P.r (Fin.last P.r) ∩ D := ⟨hx.2.1, by simpa [hDdef] using hxU⟩
    obtain ⟨a, ha, htop⟩ := pt_poly hQ D hD _ hf hg
    have hm : mdim P.k P.r (Fin.last P.r) + 1 = P.k + 2 := by rw [mdim_last]
    have hm1 : mdim P.k P.r (Fin.last P.r) - 1 = P.k := by rw [mdim_last]; rfl
    refine ⟨a, fun Y => ?_, ?_⟩
    · rw [X.t_apply Y 0 0 Φ x hx, ← hm]
      exact ha Y
    · rw [← htop, hm1]

  let c : ℕ → Module.End ℂ (RadSp P.k P.r z z' π π') := fun j =>
    if h : j < P.k + 2 then ∑ i : Fin (P.k + 2), W ⟨j, h⟩ i • X.t ((i : ℕ) : ℂ) 0 0 else 0
  have hval : ∀ (T : Module.End ℂ (RadSp P.k P.r z z' π π')) (Φ : RadSp P.k P.r z z' π π') x,
      x ∉ DomR P.k P.r z z' → ((T Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = 0 := by
    intro T Φ x hx
    have hmem := (T Φ).2
    obtain ⟨h0, _, _⟩ := hmem
    exact h0 x hx
  have hc : ∀ (Φ : RadSp P.k P.r z z' π π'), ∀ x ∈ DomR P.k P.r z z', ∀ (a : ℕ → (Wq →L[ℂ] Wp)),
      (∀ Y : ℂ, ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          ∑ j ∈ Finset.range (P.k + 2), Y ^ j • a j) →
      ∀ j ∈ Finset.range (P.k + 2), ((c j Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = a j := by
    intro Φ x hx a ha j hj
    have hj' : j < P.k + 2 := Finset.mem_range.1 hj
    have e1 : c j = ∑ i : Fin (P.k + 2), W ⟨j, hj'⟩ i • X.t ((i : ℕ) : ℂ) 0 0 := dif_pos hj'
    rw [e1, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    exact interp (P.k + 2) W hW (fun Y => ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
      a ha ⟨j, hj'⟩
  refine ⟨c, fun Y => ?_, 0, fun Φ x hx => ?_⟩
  · apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    funext c0 g
    by_cases hx : (c0, g) ∈ DomR P.k P.r z z'
    · obtain ⟨a, ha, -⟩ := hpt Φ (c0, g) hx
      have hL := ha Y
      simp only at hL
      rw [hL, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply]
      congr 1
      exact (hc Φ (c0, g) hx a ha j hj).symm
    · have h1 := hval (X.t Y 0 0) Φ (c0, g) hx
      have h2 := hval (∑ j ∈ Finset.range (P.k + 2), Y ^ j • c j) Φ (c0, g) hx
      simp only at h1 h2
      rw [h1, h2]
  · obtain ⟨a, ha, htop⟩ := hpt Φ x hx
    rw [hc Φ x hx a ha P.k (Finset.mem_range.2 (by omega)), htop]
    simp

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct
