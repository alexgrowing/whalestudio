import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHL2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGHeadV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeKeepsCharacter
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointCornerScaledSingleComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVOfEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHL.MPos

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.Qx5

section aux

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dzb_congr' {f g : ℂ → E} {τ : ℂ} (h : f =ᶠ[𝓝 τ] g) : PBP.dzb f τ = PBP.dzb g τ := by
  unfold PBP.dzb; rw [h.fderiv_eq]

theorem dzb_smul' (c : ℂ) (f : ℂ → E) (τ : ℂ) : PBP.dzb (fun s => c • f s) τ = c • PBP.dzb f τ := by
  have h : (fun s => c • f s) = c • f := rfl
  unfold PBP.dzb
  rw [h, fderiv_const_smul_field]
  simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_add]
  rw [smul_comm Complex.I c]
  congr 1 <;> exact smul_comm _ _ _

theorem map_qminor' {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) {n t : ℕ}
    (Eu : Fin n → Fin n → A) (a b : Fin t → Fin n) (u : ℂ) :
    φ (qminor Eu a b u) = qminor (fun p q => φ (Eu p q)) a b u := by
  unfold qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  congr 1
  funext i
  simp only [Function.comp_apply, Tm, map_add, apply_ite φ, AlgHom.commutes, map_zero]

theorem map_AAv {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) (k r : ℕ)
    (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (y : Fin r → Fin (2 * r + k + 1) → ℂ) (n : ℕ)
    (hn : n ≤ r) (ℓ : ℂ) : φ (C3.AAv k r Eu y n hn ℓ) = C3.AAv k r (fun p q => φ (Eu p q)) y n hn ℓ := by
  unfold C3.AAv
  rw [map_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  split_ifs
  · rw [map_smul, map_qminor']
  · exact map_zero φ

private theorem eventually_level_point_mem_open_lemma {k r j : ℕ} (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} (hZ : Z.det ≠ 0)
    {τ : ℂ} (hτ : τ ≠ 0) (γ : B.Mat k (r - (j + 1))) :
    ContinuousAt (fun τ' => x0 k r j hj Z τ' γ) τ := by
  have hr : (j + 1) + (r - (j + 1)) = r := by omega
  have hz : Continuous fun τ' : ℂ => zfull Z τ' := by
    unfold zfull U.blk2
    fun_prop
  have hL : Continuous fun p : Matrix (Fin (j+1)) (Fin (j+1)) ℂ × Matrix (Fin (j+1)) (Fin (j+1)) ℂ =>
      D.castM hr (U.blk3 (k := k) 0 0 (p.1 * G.wMat (j+1)) 0 γ 0 (G.wMat (j+1) * p.2) 0 0) := by
    unfold U.blk3
    have := PBH.castM_cont (k := k) hr
    fun_prop
  have hdet : (zfull Z τ)ᴴ.det ≠ 0 := by
    rw [Matrix.det_conjTranspose, zfull_det]
    exact star_ne_zero.mpr (mul_ne_zero hZ hτ)
  have h1 : ContinuousAt (Inv.inv : Matrix (Fin (j+1)) (Fin (j+1)) ℂ → _) (zfull Z τ)ᴴ := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have h2 : ContinuousAt (fun N : Matrix (Fin (j+1)) (Fin (j+1)) ℂ => Nᴴ⁻¹) (zfull Z τ) :=
    ContinuousAt.comp (g := Inv.inv) (f := fun N : Matrix (Fin (j+1)) (Fin (j+1)) ℂ => Nᴴ) h1
      continuous_id.matrix_conjTranspose.continuousAt
  have hK : ContinuousAt (fun N : Matrix (Fin (j+1)) (Fin (j+1)) ℂ =>
      D.castM hr (U.mMap k (j + 1) (r - (j + 1)) N γ)) (zfull Z τ) :=
    hL.continuousAt.comp (f := fun N : Matrix (Fin (j+1)) (Fin (j+1)) ℂ => (Nᴴ⁻¹, N))
      (h2.prodMk continuousAt_id)
  exact hK.comp (f := fun τ' => zfull Z τ') hz.continuousAt

theorem eventually_level_point_mem_open {k r j : ℕ} (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} (hZ : Z.det ≠ 0) {τ : ℂ}
    (hτ : τ ≠ 0) (γ : B.Mat k (r - (j + 1))) {Dm : Set (Q.Mx k r)} (hD : IsOpen Dm)
    (hx : x0 k r j hj Z τ γ ∈ Dm) : ∀ᶠ τ' in 𝓝 τ, τ' ≠ 0 ∧ x0 k r j hj Z τ' γ ∈ Dm := by
  have hc := eventually_level_point_mem_open_lemma hj hZ hτ γ
  exact (eventually_ne_nhds hτ).and (hc.preimage_mem_nhds (hD.mem_nhds hx))

end aux

private theorem minus_positive_of_parts_lemma {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Dm : Set (Mx k r)} (hD : IsOpen Dm) (p q : Fin (2 * r + k + 1)) (w : ↥(VS k r 0 Dm E)) {g : Mx k r}
    (hg : g ∈ Glev k r 0 ∩ Dm) :
    ((PBG.E0 hD p q w : VS k r 0 Dm E) : Mx k r → E) g = EH k r p q (w : Mx k r → E) g := by
  unfold PBG.E0 Eh hat
  rw [mkEnd_apply, cut_of_mem _ hg]
  have h1 : posL k r 0 (PBG.c0 p) = p := by ext; simp [posL, PBG.c0]
  have h2 : posL k r 0 (PBG.c0 q) = q := by ext; simp [posL, PBG.c0]
  rw [h1, h2]

private theorem minus_positive_of_parts_lemma_2 {k r : ℕ} {g : Mx k r} (hg : g ∈ B.GV k r) :
    g ∈ Glev k r 0 := by
  refine ⟨hg, ?_⟩
  intro a ha
  simp at ha

private theorem minus_positive_of_parts_lemma_3 {k r m : ℕ} (hm : m + 2 ≤ r) (z' : Fin (2 * r + k + 1) → ℂ)
    {B' M : Type} [Ring B'] [Algebra ℂ B'] [AddCommGroup M] [Module ℂ M] (S : Subalgebra ℂ B')
    (E0 : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → B')
    (hE : ∀ p q, E0 p q ∈ S) (hgl : GlRel E0) (La : B' →ₗ[ℂ] M)
    (hR : C3.RightRuleFn k r z' E0 La) (y : Fin r → Fin (2 * r + k + 1) → ℂ)
    (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (d ℓ : ℂ) (hW : W.det ≠ 0) (hd : d ≠ 0)
    (hS : ∀ (b : Fin (m + 1)) (x : B'), x ∈ S →
      La (E0 (esI k r ⟨↑b, by omega⟩) (esI k r ⟨m + 1, by omega⟩) * x) = (d * W⁻¹ b (Fin.last m)) • La x)
    (hy1 : ∀ (a : Fin (m + 1)) (q : Fin (2 * r + k + 1)),
      y ⟨↑a, by omega⟩ q = if h : r + k < ↑q ∧ 2 * r + k - ↑q < m + 1 then W a ⟨2 * r + k - ↑q, h.2⟩ else 0)
    (hy2 : ∀ (q : Fin (2 * r + k + 1)), y ⟨m + 1, by omega⟩ q = if ↑q = 2 * r + k - (m + 1) then d else 0) :
    (W.det * d)⁻¹ • La (C3.AAv k r E0 y (m + 2) hm ℓ) =
      W.det⁻¹ • La (C3.AAv k r E0 y (m + 1) (by omega) ℓ *
        ((algebraMap ℂ B') (ℓ + ↑(m + 1)) + E0 (esI k r ⟨m + 1, by omega⟩) (esI k r ⟨m + 1, by omega⟩))) -
      (d * W.det⁻¹) • La (C3.AAv k r E0 y m (by omega) ℓ) := by
  let E' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → S := fun p q => ⟨E0 p q, hE p q⟩
  let La' : S →ₗ[ℂ] M := La.comp S.val.toLinearMap
  have hgl' : GlRel E' := by
    intro a b c e
    apply Subtype.ext
    have := hgl a b c e
    simp only [E', Subalgebra.coe_sub, Subalgebra.coe_mul]
    rw [this]
    split_ifs <;> simp
  have hR' : C3.RightRuleFn k r z' E' La' := by
    intro x p q hpq
    exact hR (x : B') p q hpq
  have key := head_algebra_relations_vector S M k r m hm z' E' La' y W d ℓ hgl' hR' hW hd
    (fun b x => hS b (x : B') x.2) hy1 hy2
  have hmap : ∀ n (hn : n ≤ r), (S.val (C3.AAv k r E' y n hn ℓ)) = C3.AAv k r E0 y n hn ℓ := fun n hn =>
    map_AAv S.val k r E' y n hn ℓ
  simp only [La', LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, map_add, AlgHom.commutes] at key
  rw [hmap, hmap, hmap] at key
  rw [map_add (algebraMap ℂ B')]
  exact key

theorem _root_.Formalism.FourierDecayAlt.P.minus_positive_of_parts : MinusPosOfParts := by
  intro hNf hDm hStar hTor hFr k r j hj z z' E _ _ Dm Φ Z γ τ hj1 hH Y
  obtain ⟨hz, hz', hDo, hDsub, ⟨hsm, hright, hleft⟩, hZ, hτ, hγ, hx⟩ := hH
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  unfold Eq3
  have hG : ∀ τ', τ' ≠ 0 → x0 k r (m + 1) hj Z τ' γ ∈ Dm → x0 k r (m + 1) hj Z τ' γ ∈ Glev k r 0 ∩ Dm :=
    fun τ' h1 h2 => ⟨minus_positive_of_parts_lemma_2 (x0_GV hj hZ h1 hγ), h2⟩
  have hv : ∀ (n : ℕ) (hn : n ≤ r) (e : Fin 2) (g : Mx k r), ¬ (e = 1 ∧ n = 0) →
      D.vLet k r z z' n hn (false, Y) e Φ g = ((starRingEnd ℂ) (Dmin k r z z' g ⟨n, by omega⟩))⁻¹ •
        C3.AAvop k r (n - e) (by omega) ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) Φ g := by
    intro n hn e g hne
    simp only [D.vLet, if_neg hne]
    rfl
  set ℓ : ℂ := (Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2 with hℓ
  set x := x0 k r (m + 1) hj Z τ γ with hxd
  have hxG := hG τ hτ hx
  set La := PBG.La hDo Φ hsm x with hLad
  have hLa : ∀ n (hn : n ≤ r), C3.AAvop k r n hn ℓ Φ x = La (C3.AAv k r (PBG.E0 hDo) (PBG.y0 x) n hn ℓ) :=
    fun n hn => (PBG.La_AAv hDo Φ hsm x hxG n hn ℓ).symm
  obtain ⟨hD1, hD2⟩ := hDm k r (m + 1) hj z z' Z τ γ hZ hτ hγ
  set W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := Zᴴᵀ with hWd
  set d : ℂ := (starRingEnd ℂ) τ with hdd
  have hWdet : W.det = (starRingEnd ℂ) Z.det := by
    rw [hWd, Matrix.det_transpose, Matrix.det_conjTranspose]
    rfl
  have E1 : D.vLet k r z z' (m + 1 + 1) hj (false, Y) 0 Φ x =
      (W.det * d)⁻¹ • La (C3.AAv k r (PBG.E0 hDo) (PBG.y0 x) (m + 2) hj ℓ) := by
    rw [hv _ _ _ _ (by simp), hD2, map_mul, ← hWdet, ← hLa]
    congr 1
  have E2 : D.vLet k r z z' (m + 1) (by omega) (false, Y) 0 Φ x =
      W.det⁻¹ • La (C3.AAv k r (PBG.E0 hDo) (PBG.y0 x) (m + 1) (by omega) ℓ) := by
    rw [hv _ _ _ _ (by simp), hD1, ← hWdet, ← hLa]
    congr 1
  have E3 : D.vLet k r z z' (m + 1) (by omega) (false, Y) 1 Φ x =
      W.det⁻¹ • La (C3.AAv k r (PBG.E0 hDo) (PBG.y0 x) m (by omega) ℓ) := by
    rw [hv _ _ _ _ (by simp), hD1, ← hWdet, ← hLa]
    congr 1
  have hv0 : ∀ g, D.vLet k r z z' (m + 1) (by omega) (false, Y) 0 Φ g =
      ((starRingEnd ℂ) (Dmin k r z z' g ⟨m + 1, by omega⟩))⁻¹ • C3.AAvop k r (m + 1) (by omega) ℓ Φ g := by
    intro g
    rw [hv _ _ _ _ (by simp)]
    congr 1
  set X := C3.AAv k r (PBG.E0 (E := E) hDo) (PBG.y0 x) (m + 1) (by omega) ℓ with hXd
  set Ψ0 : Mx k r → E := ((X (PBG.vK hDo Φ hsm) : VS k r 0 Dm E) : Mx k r → E) with hΨ0
  have hev : (fun τ' => D.vLet k r z z' (m + 1) (by omega) (false, Y) 0 Φ (x0 k r (m + 1) hj Z τ' γ)) =ᶠ[𝓝 τ]
      (fun τ' => W.det⁻¹ • Ψ0 (x0 k r (m + 1) hj Z τ' γ)) := by
    filter_upwards [eventually_level_point_mem_open hj hZ hτ γ hDo hx] with τ' hτ'
    obtain ⟨h1, h2⟩ := hτ'
    obtain ⟨hD1', -⟩ := hDm k r (m + 1) hj z z' Z τ' γ hZ h1 hγ
    rw [hv0, hD1', ← hWdet, ← PBG.La_AAv hDo Φ hsm _ (hG τ' h1 h2),
      (hFr _ k r (m + 1) hj (PBG.E0 hDo) Z τ τ' ℓ γ (PBG.level_zero_derivation_relation hDo) hZ hτ h1 hγ).1]
    rfl
  have hΨsm : SmoothLev k r 0 Dm Ψ0 := (X (PBG.vK hDo Φ hsm)).2.1
  have hT := hTor E k r (m + 1) hj Dm Ψ0 Z τ γ hDo hΨsm hZ hτ hγ hx
  set Ejj := PBG.E0 (E := E) hDo (esI k r ⟨m + 1, by omega⟩) (esI k r ⟨m + 1, by omega⟩) with hEjj
  have hLaE : La (Ejj * X) = EH k r (esI k r ⟨m + 1, by omega⟩) (esI k r ⟨m + 1, by omega⟩) Ψ0 x := by
    rw [← minus_positive_of_parts_lemma hDo _ _ _ hxG]
    rfl
  have hcomm : Ejj * X = X * Ejj :=
    (hFr _ k r (m + 1) hj (PBG.E0 hDo) Z τ τ ℓ γ (PBG.level_zero_derivation_relation hDo) hZ hτ hτ hγ).2
  have E4 : d • PBP.dzb (fun τ' => D.vLet k r z z' (m + 1) (by omega) (false, Y) 0 Φ
      (x0 k r (m + 1) hj Z τ' γ)) τ = -(W.det⁻¹ • La (X * Ejj)) := by
    rw [dzb_congr' hev, dzb_smul', smul_comm, ← hcomm, hLaE, hT, smul_neg, neg_neg]
  have hrule : ∀ g ∈ Glev k r 0 ∩ Dm, ∀ (p q : Fin (2 * r + k + 1)), C3.InNp k r p q →
      EH k r p q Φ g = C3.dpsiP k r z' p q • Φ g :=
    fun g hg p q h => rule_of_eq E k r z' Φ g hz' (fun n hn => (hright g hg n hn).2) p q h
  have hR := PBG.La_rule hDo z' Φ hsm hrule x
  obtain ⟨S, hSm⟩ : ∃ S : Subalgebra ℂ (Module.End ℂ (VS k r 0 Dm E)), ∀ T, T ∈ S ↔
      ∀ w : VS k r 0 Dm E, (∀ g ∈ Glev k r 0 ∩ Dm, ∀ a : Fin (m + 1) → ℂ,
        (w : Mx k r → E) (nL k r (m + 1) hj a * g) = psi k r z cStd (nL k r (m + 1) hj a) • (w : Mx k r → E) g) →
      (∀ g ∈ Glev k r 0 ∩ Dm, ∀ a : Fin (m + 1) → ℂ,
        ((T w : VS k r 0 Dm E) : Mx k r → E) (nL k r (m + 1) hj a * g) =
          psi k r z cStd (nL k r (m + 1) hj a) • ((T w : VS k r 0 Dm E) : Mx k r → E) g) :=
    ⟨{ carrier := {T | ∀ w : VS k r 0 Dm E, (∀ g ∈ Glev k r 0 ∩ Dm, ∀ a : Fin (m + 1) → ℂ,
          (w : Mx k r → E) (nL k r (m + 1) hj a * g) = psi k r z cStd (nL k r (m + 1) hj a) • (w : Mx k r → E) g) →
        (∀ g ∈ Glev k r 0 ∩ Dm, ∀ a : Fin (m + 1) → ℂ,
          ((T w : VS k r 0 Dm E) : Mx k r → E) (nL k r (m + 1) hj a * g) =
            psi k r z cStd (nL k r (m + 1) hj a) • ((T w : VS k r 0 Dm E) : Mx k r → E) g)}
       mul_mem' := fun {T₁ T₂} h₁ h₂ w hw => h₁ _ (h₂ w hw)
       add_mem' := fun {T₁ T₂} h₁ h₂ w hw g hg a => by
         simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, smul_add]
         rw [h₁ w hw g hg a, h₂ w hw g hg a]
       algebraMap_mem' := fun c w hw g hg a => by
         simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
         rw [hw g hg a, smul_comm] }, fun _ => Iff.rfl⟩
  have hE : ∀ p q, PBG.E0 (E := E) hDo p q ∈ S := by
    intro p q
    rw [hSm]
    intro w hw
    exact HeadLetterLemmas.derivative_keeps_character hj z hDo (fun g hg a => (hleft g hg a).1) p q w hw
  have hK : ∀ g ∈ Glev k r 0 ∩ Dm, ∀ a : Fin (m + 1) → ℂ,
      ((PBG.vK hDo Φ hsm : VS k r 0 Dm E) : Mx k r → E) (nL k r (m + 1) hj a * g) =
        psi k r z cStd (nL k r (m + 1) hj a) • ((PBG.vK hDo Φ hsm : VS k r 0 Dm E) : Mx k r → E) g := by
    intro g hg a
    have hg' : nL k r (m + 1) hj a * g ∈ Glev k r 0 ∩ Dm :=
      ⟨Glev_mul (HeadLetterLemmas.nL_glev0 hj a) hg.1, (hleft g hg a).1⟩
    show cut k r 0 Dm Φ _ = _ • cut k r 0 Dm Φ _
    rw [cut_of_mem _ hg', cut_of_mem _ hg]
    exact (hleft g hg a).2
  have hSt : ∀ (b : Fin (m + 1)) (T : Module.End ℂ (VS k r 0 Dm E)), T ∈ S →
      La (PBG.E0 hDo (esI k r ⟨↑b, by omega⟩) (esI k r ⟨m + 1, by omega⟩) * T) = (d * W⁻¹ b (Fin.last m)) • La T := by
    intro b T hT
    have hTK := (hSm T).1 hT _ hK
    have hΨ : SmoothLev k r 0 Dm ((T (PBG.vK hDo Φ hsm) : VS k r 0 Dm E) : Mx k r → E) :=
      (T (PBG.vK hDo Φ hsm)).2.1
    have h1 := hStar E k r (m + 1) hj z Dm ((T (PBG.vK hDo Φ hsm) : VS k r 0 Dm E) : Mx k r → E) Z τ γ hj1 hz hDo
      hΨ hZ hτ hγ hx (fun a => hTK x hxG a) b
    have h2 : La (PBG.E0 hDo (esI k r ⟨↑b, by omega⟩) (esI k r ⟨m + 1, by omega⟩) * T) =
        EH k r (esI k r ⟨↑b, by omega⟩) (esI k r ⟨m + 1, by omega⟩)
          ((T (PBG.vK hDo Φ hsm) : VS k r 0 Dm E) : Mx k r → E) x := by
      rw [← minus_positive_of_parts_lemma hDo _ _ _ hxG]
      rfl
    have hWi : W⁻¹ b (Fin.last m) = (starRingEnd ℂ) (Z⁻¹ b (Fin.last m)) := by
      rw [hWd, ← Matrix.transpose_nonsing_inv, ← Matrix.conjTranspose_nonsing_inv]
      rfl
    rw [h2, h1, hWi]
    rfl
  have hN := (hNf k r (m + 1) hj Z τ γ hZ hτ hγ).2
  have hy1 : ∀ (a : Fin (m + 1)) (q : Fin (2 * r + k + 1)),
      PBG.y0 x ⟨↑a, by omega⟩ q = if h : r + k < ↑q ∧ 2 * r + k - ↑q < m + 1 then W a ⟨2 * r + k - ↑q, h.2⟩ else 0 := by
    intro a q
    rw [hN ⟨↑a, by omega⟩ q (by simp)]
    by_cases h : r + k < ↑q ∧ 2 * r + k - ↑q < m + 1
    · rw [dif_pos h, if_pos ⟨h.1, by omega⟩]
      simp only [C3.Zb, dif_pos a.2, dif_pos h.2, hWd]
      rfl
    · rw [dif_neg h]
      split_ifs with h'
      · have hb : 2 * r + k - ↑q = m + 1 := by omega
        simp only [C3.Zb, dif_pos a.2, hb, lt_irrefl, dif_neg (not_false), star_zero]
      · rfl
  have hy2 : ∀ q : Fin (2 * r + k + 1),
      PBG.y0 x ⟨m + 1, by omega⟩ q = if ↑q = 2 * r + k - (m + 1) then d else 0 := by
    intro q
    rw [hN ⟨m + 1, by omega⟩ q (by simp)]
    by_cases hq : (q : ℕ) = 2 * r + k - (m + 1)
    · rw [if_pos hq, if_pos ⟨by omega, by omega⟩]
      have hb : 2 * r + k - ↑q = m + 1 := by omega
      simp [C3.Zb, hb, hdd]
    · rw [if_neg hq]
      split_ifs with h'
      · have hb : 2 * r + k - ↑q < m + 1 := by omega
        simp only [C3.Zb, lt_irrefl, dif_neg (not_false)]
        rw [if_neg (by omega), star_zero]
      · rfl
  have hWne : W.det ≠ 0 := by rw [hWdet]; exact (map_ne_zero _).mpr hZ
  have hdne : d ≠ 0 := (map_ne_zero _).mpr hτ
  have key := minus_positive_of_parts_lemma_3 hj z' S (PBG.E0 hDo) hE (PBG.level_zero_derivation_relation hDo) La hR (PBG.y0 x) W d ℓ
    hWne hdne hSt hy1 hy2
  have hc : ℓ + ((m + 1 : ℕ) : ℂ) = (Y : ℂ) - levelZeroKernel k r (m + 1) := by
    simp only [hℓ, levelZeroKernel]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [E1, E2, E3, E4, key, mul_add, map_add, ← Algebra.commutes, ← Algebra.smul_def, map_smul, hc]
  module

end Formalism.FourierDecayAlt.P.CutHL.MPos
