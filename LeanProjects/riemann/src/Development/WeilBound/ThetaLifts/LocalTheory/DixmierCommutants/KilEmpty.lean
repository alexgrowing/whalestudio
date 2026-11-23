import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.ExistsInvar
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited

noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

open GlobalTheory.WeilM Filter Topology ValuativeRel Matrix PositivityTheory.KCo GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  {n d d₁ : ℕ} (e : Fin d₁ ⊕ Bool ≃ Fin d) {W : Type} [AddCommGroup W] [Module ℂ W]

def RI {m : ℕ} (Y : Matrix (Fin n) (Fin m) k) : Prop := ∃ R : Matrix (Fin m) (Fin n) k, Y * R = 1

theorem ri_iff {m : ℕ} {Y : Matrix (Fin n) (Fin m) k} : RI Y ↔ Y.rank = n := by
  constructor
  · rintro ⟨R, h⟩
    refine le_antisymm (rank_le_height Y) ?_
    have := rank_mul_le_left Y R
    rwa [h, rank_one, Fintype.card_fin] at this
  · intro h
    have hs : LinearMap.range Y.mulVecLin = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact h)
    choose u hu using fun j : Fin n => LinearMap.range_eq_top.1 hs (Pi.single j 1)
    refine ⟨Matrix.of fun i j => u j i, Matrix.ext fun i j => ?_⟩
    have := congrFun (hu j) i
    rw [Pi.single_apply] at this
    rw [Matrix.one_apply]
    exact this

theorem not_ri {m : ℕ} {Y : Matrix (Fin n) (Fin m) k} (h : ¬ RI Y) : ∃ c : Fin n → k, c ≠ 0 ∧ c ᵥ* Y = 0 := by
  by_contra h'
  push Not at h'
  have : Function.Injective Y.vecMul := fun a b hab => by
    by_contra hne
    exact h' (a - b) (sub_ne_zero.2 hne) (by rw [sub_vecMul]; exact sub_eq_zero.2 hab)
  exact h (ri_iff.2 (by rw [(vecMul_injective_iff.1 this).rank_matrix, Fintype.card_fin]))

theorem ri_of_det {m : ℕ} {Y : Matrix (Fin n) (Fin m) k} {R : Matrix (Fin m) (Fin n) k} (h : (Y * R).det ≠ 0) : RI Y :=
  ⟨R * (Y * R)⁻¹, by rw [← Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit h)]⟩

theorem det_nhds {m : ℕ} {Y : Matrix (Fin n) (Fin m) k} {R : Matrix (Fin m) (Fin n) k} (h : Y * R = 1) :
    {X : Matrix (Fin n) (Fin m) k | (X * R).det ≠ 0} ∈ 𝓝 Y :=
  (isOpen_ne_fun (continuous_id.matrix_mul continuous_const).matrix_det continuous_const).mem_nhds (by simp [h])

def mid (Y : Matrix (Fin n) (Fin d) k) : Matrix (Fin n) (Fin d₁) k := Y.submatrix id fun s => e (.inl s)

def cl (t : Bool) (Y : Matrix (Fin n) (Fin d) k) : Fin n → k := fun i => Y i (e (.inr t))

def InP (h : Matrix (Fin d) (Fin d) k) : Prop :=
  (∀ i, i ≠ e (.inr false) → h i (e (.inr false)) = 0) ∧ valuation k (h (e (.inr false)) (e (.inr false))) = 1 ∧
    valuation k (h (e (.inr true)) (e (.inr true))) = 1 ∧
    (∀ s s', h (e (.inl s)) (e (.inl s')) = (1 : Matrix (Fin d₁) (Fin d₁) k) s s') ∧ ∀ s, h (e (.inr true)) (e (.inl s)) = 0

structure Inv (ν : kˣ →* ℂˣ) (L : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] W) : Prop where
  left : ∀ g : GL (Fin n) k, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L (omB ν 1 g 1 Φ) = L Φ
  right : ∀ h, InP e h → ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), (fun Y : Matrix (Fin n) (Fin d) k => Φ (Y * h)) ∈ SB (Matrix (Fin n) (Fin d) k) ∧
    L (fun Y : Matrix (Fin n) (Fin d) k => Φ (Y * h)) = L Φ

variable {e} {ν : kˣ →* ℂˣ} {L : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] W}

theorem Inv.op (hL : Inv e ν L) {l : kˣ} (hl : valuation k (l : k) = 1) {x c : Fin n → k} (hc : c ⬝ᵥ x = 1)
    {h : Matrix (Fin d) (Fin d) k} (hh : InP e h) (Φ) (hΦ : Φ ∈ SB (Matrix (Fin n) (Fin d) k)) :
    (fun S : Matrix (Fin n) (Fin d) k => Φ (idp (vecMulVec x c) ((l⁻¹ : kˣ) - 1) * S * h)) - (ν l : ℂ) • Φ ∈ LinearMap.ker L := by
  have hd : (idp (vecMulVec x c) ((l⁻¹ : kˣ) - 1))ᵀ.det = (l⁻¹ : kˣ) := by
    rw [det_transpose, idp, ← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hc]
    simp
  let g : GL (Fin n) k := GeneralLinearGroup.mkOfDetNeZero _ (hd ▸ (l⁻¹).ne_zero)
  have hg : gdet g = l⁻¹ := Units.ext hd
  obtain ⟨s, e1⟩ := hL.right h hh Φ hΦ
  have gv : g.valᵀ = idp (vecMulVec x c) ((l⁻¹ : kˣ) - 1) := transpose_transpose _
  have e3 : omB ν 1 g 1 (fun Y : Matrix (Fin n) (Fin d) k => Φ (Y * h)) = ((ν l)⁻¹ : ℂ) • fun S : Matrix (Fin n) (Fin d) k => Φ (idp (vecMulVec x c) ((l⁻¹ : kˣ) - 1) * S * h) := by
    funext Y
    have : apow l⁻¹ ((d : ℂ) / 2) = 1 := apow_of_valuation_eq_one (by simp [hl]) _
    simp only [omB, hg, gv, Fintype.card_fin, this]
    simp
  have e2 := (congrArg L e3).symm.trans (hL.left g _ s)
  rw [map_smul, e1] at e2
  rw [LinearMap.mem_ker, map_sub, map_smul, ← e2, smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul, sub_self]

theorem idem_vmv {m : Type} [Fintype m] {x c : m → k} (hc : c ⬝ᵥ x = 1) : vecMulVec x c * vecMulVec x c = vecMulVec x c := by
  rw [vecMulVec_mul_vecMulVec, hc, one_smul]

theorem fix_col (hL : Inv e ν L) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1) {U₀} (hU : Kil (LinearMap.ker L) U₀) (t : Bool)
    {X₀ : Matrix (Fin n) (Fin d) k} {c : Matrix (Fin n) (Fin d) k → Fin n → k} (cc : ContinuousAt c X₀) (h0 : c X₀ ⬝ᵥ cl e t X₀ = 1)
    {B₀} (hB : B₀ ∈ 𝓝 X₀) (h : ∀ X ∈ B₀, X ∈ U₀ ∨ (c X ⬝ᵥ cl e t X = 1 ∧
      InP e (idp (vecMulVec (Pi.single (e (.inr t)) 1) (c X ᵥ* X)) (l - 1)))) : ∃ B ∈ 𝓝 X₀, Kil (LinearMap.ker L) B := by
  have q : ∀ X, c X ⬝ᵥ cl e t X = 1 → (c X ᵥ* X) ⬝ᵥ Pi.single (e (.inr t)) 1 = 1 := fun X hX => by
    rw [dotProduct_single, mul_one]; exact hX
  refine fixk hU (P := fun X => vecMulVec (cl e t X) (c X)) (Q := fun X => vecMulVec (Pi.single (e (.inr t)) 1) (c X ᵥ* X))
    ?_ ?_ (idem_vmv h0) (idem_vmv (q _ h0)) hl (c := ν l) (fun h => hν (Units.ext h)) hB fun X hX => (h X hX).imp_right fun ⟨h1, h2⟩ =>
      ⟨idem_vmv h1, idem_vmv (q _ h1), ?_, hL.op hl h1 h2⟩
  · refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
    exact (continuous_id.matrix_elem i _).continuousAt.mul (continuousAt_pi.1 cc j)
  · refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => continuousAt_const.mul ?_
    change ContinuousAt (fun y : Matrix (Fin n) (Fin d) k => ∑ r, c y r * y r j) X₀
    exact tendsto_finset_sum Finset.univ fun r _ => (continuousAt_pi.1 cc r).mul (continuous_id.matrix_elem r j).continuousAt
  · rw [vecMulVec_mul, mul_vecMulVec, mulVec_single_one]
    rfl

theorem kil_empty {V : Type} [TopologicalSpace V] (Z : Submodule ℂ (V → ℂ)) : Kil Z ∅ := fun Φ _ h => by
  rw [show Φ = 0 from funext fun y => by by_contra h'; exact h y h']
  exact zero_mem _

theorem kil_one (hL : Inv e ν L) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1) :
    Kil (LinearMap.ker L) {Y | cl e false Y ≠ 0} := by
  refine kil_loc hV_mat fun X₀ hX => ?_
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hX
  have ci : Continuous fun X : Matrix (Fin n) (Fin d) k => cl e false X i := continuous_id.matrix_elem i _
  have k1 : ∀ X : Matrix (Fin n) (Fin d) k, cl e false X i ≠ 0 →
      (Pi.single i (cl e false X i)⁻¹ : Fin n → k) ⬝ᵥ cl e false X = 1 := fun X h => by
    rw [single_dotProduct, inv_mul_cancel₀ h]
  refine fix_col hL hl hν (kil_empty _) false (c := fun X => Pi.single i (cl e false X i)⁻¹) ?_ (k1 _ hi)
    ((isOpen_ne_fun ci continuous_const).mem_nhds hi) fun X hX => Or.inr ⟨k1 X hX, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_single (A := fun _ : Fin n => k) i).continuousAt.comp (ci.continuousAt.inv₀ hi)
  · intro r hr
    simp [idp, vecMulVec_apply, hr]
  · have : ((Pi.single i (cl e false X i)⁻¹ : Fin n → k) ᵥ* X) (e (.inr false)) = 1 := k1 X hX
    simp only [idp, vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply, this]
    simp [hl]
  · simp [idp, vecMulVec_apply]
  · intro s s'
    simp [idp, vecMulVec_apply, Matrix.one_apply]
  · intro s
    simp [idp, vecMulVec_apply]

theorem kil_full (hL : Inv e ν L) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1)
    (h2 : Kil (LinearMap.ker L) {Y | RI (mid e Y)}) : Kil (LinearMap.ker L) {Y | RI Y} := by
  have h12 : Kil (LinearMap.ker L) {Y | cl e false Y ≠ 0 ∨ RI (mid e Y)} := by
    refine kil_loc hV_mat fun X hX => hX.elim (fun h => ⟨_, ?_, kil_one hL hl hν⟩) fun ⟨R, h⟩ => ⟨_, ?_, h2⟩
    · exact (isOpen_ne_fun (continuous_pi fun i => continuous_id.matrix_elem i _) continuous_const).mem_nhds h
    · have cm : Continuous (mid e : Matrix (Fin n) (Fin d) k → _) := continuous_id.matrix_submatrix _ _
      exact mem_of_superset (cm.continuousAt.preimage_mem_nhds (det_nhds h)) fun Y hY => ri_of_det hY
  refine kil_loc hV_mat fun X₀ ⟨R, hR⟩ => ?_
  have key : ∀ X : Matrix (Fin n) (Fin d) k, (X * R).det ≠ 0 → ¬ (cl e false X ≠ 0 ∨ RI (mid e X)) →
      (R (e (.inr true)) ᵥ* (X * R)⁻¹) ᵥ* X = Pi.single (e (.inr true)) 1 := fun X hd hX => by
    push Not at hX
    obtain ⟨c, c0, hc⟩ := not_ri hX.2
    have r : c ᵥ* X = Pi.single (e (.inr true)) ((c ᵥ* X) (e (.inr true))) := by
      funext j
      obtain ⟨j, rfl⟩ := e.surjective j
      rcases j with s | _ | _
      · rw [Pi.single_eq_of_ne (by simp)]
        exact congrFun hc s
      · have : (c ᵥ* X) (e (.inr false)) = c ⬝ᵥ cl e false X := rfl
        simp [this, hX.1]
      · simp
    set a := (c ᵥ* X) (e (.inr true))
    have e1 : c = a • (R (e (.inr true)) ᵥ* (X * R)⁻¹) := by
      conv_lhs => rw [← vecMul_one c, ← mul_nonsing_inv _ (Ne.isUnit hd), ← vecMul_vecMul, ← vecMul_vecMul, r, single_vecMul]
      rw [smul_vecMul]; rfl
    have a0 : a ≠ 0 := fun h => c0 (by rw [e1, h, zero_smul])
    apply smul_right_injective _ a0
    simp only
    rw [← smul_vecMul, ← e1, r, ← Pi.single_smul, smul_eq_mul, mul_one]
  by_cases h0 : cl e false X₀ ≠ 0 ∨ RI (mid e X₀)
  · obtain ⟨B, hB, hk⟩ : ∃ B ∈ 𝓝 X₀, B ⊆ {Y | cl e false Y ≠ 0 ∨ RI (mid e Y)} := by
      refine h0.elim (fun h => ⟨_, ?_, fun _ => Or.inl⟩) fun ⟨R, h⟩ => ⟨_, ?_, fun _ => Or.inr⟩
      · exact (isOpen_ne_fun (continuous_pi fun i => continuous_id.matrix_elem i _) continuous_const).mem_nhds h
      · have cm : Continuous (mid e : Matrix (Fin n) (Fin d) k → _) := continuous_id.matrix_submatrix _ _
        exact mem_of_superset (cm.continuousAt.preimage_mem_nhds (det_nhds h)) fun Y hY => ri_of_det hY
    exact ⟨B, hB, fun Φ hΦ hs => h12 Φ hΦ fun y hy => hk (hs y hy)⟩
  have k1 : ∀ X : Matrix (Fin n) (Fin d) k, (X * R).det ≠ 0 → ¬ (cl e false X ≠ 0 ∨ RI (mid e X)) →
      (R (e (.inr true)) ᵥ* (X * R)⁻¹) ⬝ᵥ cl e true X = 1 := fun X hd hX => by
    have := congrFun (key X hd hX) (e (.inr true))
    rwa [Pi.single_eq_same] at this
  refine fix_col hL hl hν h12 true (c := fun X => R (e (.inr true)) ᵥ* (X * R)⁻¹) ?_ (k1 _ (by simp [hR]) h0) (det_nhds hR)
    fun X hX => ?_
  · have c1 : ContinuousAt (fun X : Matrix (Fin n) (Fin d) k => (X * R)⁻¹) X₀ :=
      ContinuousAt.comp (f := fun X : Matrix (Fin n) (Fin d) k => X * R) (continuousAt_matrix_inv _ (by
        rw [hR, det_one, Ring.inverse_eq_inv']; exact continuousAt_inv₀ one_ne_zero))
        (continuous_id.matrix_mul continuous_const).continuousAt
    exact ContinuousAt.comp (f := fun X : Matrix (Fin n) (Fin d) k => (X * R)⁻¹)
      (continuous_const.matrix_vecMul continuous_id).continuousAt c1
  · by_cases h : cl e false X ≠ 0 ∨ RI (mid e X)
    · exact Or.inl h
    refine Or.inr ⟨k1 X hX h, ?_⟩
    rw [key X hX h]
    refine ⟨fun r hr => ?_, ?_, ?_, fun s s' => ?_, fun s => ?_⟩ <;> simp [idp, vecMulVec_apply, Matrix.one_apply, *]

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
