import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.GANormSqStar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.AdUnitBCtMulVec

open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}

def AdK (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (D : Set (Mx k r)) :
    Set (Mx k r → (Wq →L[ℂ] Wp)) :=
  {F | SmoothLev k r (Fin.last r) D F ∧
    ∀ x ∈ Glev k r (Fin.last r) ∩ D, ∀ h ∈ UWset k r z, F (h * x) = (π h).comp (F x)}

theorem adK_add {F G : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ AdK k r z π D) (hG : G ∈ AdK k r z π D) :
    F + G ∈ AdK k r z π D := by
  refine ⟨?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U₁, F₁, hU₁, hg₁, hF₁, hE₁⟩ := hF.1 g₀ hg₀
    obtain ⟨U₂, F₂, hU₂, hg₂, hF₂, hE₂⟩ := hG.1 g₀ hg₀
    refine ⟨U₁ ∩ U₂, F₁ + F₂, hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
      (hF₁.mono Set.inter_subset_left).add (hF₂.mono Set.inter_subset_right), ?_⟩
    intro g hg hgl
    simp [hE₁ g hg.1 hgl, hE₂ g hg.2 hgl]
  · intro x hx h hh
    simp [hF.2 x hx h hh, hG.2 x hx h hh, ContinuousLinearMap.comp_add]

theorem adK_smul {F : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ AdK k r z π D) (c : ℂ) :
    c • F ∈ AdK k r z π D := by
  refine ⟨?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U₁, F₁, hU₁, hg₁, hF₁, hE₁⟩ := hF.1 g₀ hg₀
    refine ⟨U₁, c • F₁, hU₁, hg₁, hF₁.const_smul c, ?_⟩
    intro g hg hgl
    simp [hE₁ g hg hgl]
  · intro x hx h hh
    simp [hF.2 x hx h hh, ContinuousLinearMap.comp_smul]

theorem adK_zero : (0 : Mx k r → (Wq →L[ℂ] Wp)) ∈ AdK k r z π D := by
  refine ⟨?_, ?_⟩
  · intro g₀ _
    exact ⟨Set.univ, 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
  · intro x _ h _
    simp

theorem adK_rd (hD : IsOpen D) {X : Mx k r} (hX : inLieLev k r (Fin.last r) X)
    {F : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ AdK k r z π D) : RdV X F ∈ AdK k r z π D := by
  refine ⟨rd_smooth hF.1 hX, ?_⟩
  intro x hx h hh
  have hd := rd_hasDeriv hF.1 hx hX
  have hd2 : HasDerivAt (fun t : ℝ => (π h).comp (F (x * NormedSpace.exp ((t : ℂ) • X))))
      ((π h).comp (RdV X F x)) 0 := by
    have := ((ContinuousLinearMap.compL ℂ Wq Wp Wp (π h)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) hd
    simpa [Function.comp_def] using this
  have hc : Continuous (fun t : ℝ => x * NormedSpace.exp ((t : ℂ) • X)) := by
    first
      | exact (Formalism.FourierDecayAlt.P.B5.curve_contDiff x X).continuous
      | fun_prop
  have hD0 : ∀ᶠ t : ℝ in 𝓝 0, x * NormedSpace.exp ((t : ℂ) • X) ∈ D :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hD.mem_nhds hx.2)
  have hev : (fun t : ℝ => F (h * x * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      fun t => (π h).comp (F (x * NormedSpace.exp ((t : ℂ) • X))) := by
    filter_upwards [hD0] with t ht
    rw [Matrix.mul_assoc]
    exact hF.2 _ ⟨curve_lev hx.1 hX t, ht⟩ h hh
  exact (hd2.congr_of_eventuallyEq hev).deriv

theorem adK_RZ (hD : IsOpen D) {Z : Mx k r} (h1 : inLieLev k r (Fin.last r) (hpart1 (Hpk k r) Z))
    (h2 : inLieLev k r (Fin.last r) (hpart2 (Hpk k r) Z)) {F : Mx k r → (Wq →L[ℂ] Wp)}
    (hF : F ∈ AdK k r z π D) : RZ (Hpk k r) Z F ∈ AdK k r z π D :=
  adK_add (adK_rd hD h1 hF) (adK_smul (adK_rd hD h2 hF) Complex.I)

private theorem mul_mem_uh {n : Type*} [Fintype n] [DecidableEq n] {H a b : Matrix n n ℂ}
    (ha : a ∈ UH H) (hb : b ∈ UH H) : a * b ∈ UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

theorem ad_rd_point {F : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ AdK k r z π D) {g : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hgi : g⁻¹ * g = 1) (hgi' : g * g⁻¹ = 1) (hgU : IsUnit g)
    (hginv : g⁻¹ ∈ UH (Hpk k r)) {X : Mx k r} (hX : inLieLev k r (Fin.last r) X)
    (hXz : X *ᵥ (g⁻¹ *ᵥ z) = 0) (v : Wq) :
    RdV X F g v = dRep π (g * X * g⁻¹) (F g v) := by
  have hYv : ∀ w, (g * X * g⁻¹) *ᵥ w = g *ᵥ (X *ᵥ (g⁻¹ *ᵥ w)) := fun w => by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hexp : ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) =
      NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g := by
    intro t
    have e1 : (t : ℂ) • (g * X * g⁻¹) = g * ((t : ℂ) • X) * g⁻¹ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e1]
    first
      | rw [Matrix.exp_conj g _ hgU]
      | rw [Matrix.exp_conj ℂ g _ hgU]
      | rw [Matrix.exp_conj ℝ g _ hgU]
    rw [Matrix.mul_assoc, hgi, Matrix.mul_one]
  have hginvfix : ∀ w, g *ᵥ w = w → g⁻¹ *ᵥ w = w := by
    intro w hw
    conv_lhs => rw [← hw]
    rw [Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]
  have hmem : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) ∈ UWset k r z := by
    intro t
    have hE : NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) = g * NormedSpace.exp ((t : ℂ) • X) * g⁻¹ := by
      rw [hexp t, Matrix.mul_assoc (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) g g⁻¹, hgi', Matrix.mul_one]
    refine ⟨?_, fun a => ?_, ?_⟩
    · rw [hE]
      exact mul_mem_uh (curve_lev hg.1 hX t).1 hginv
    · obtain ⟨h1, h2⟩ := hg.1.2 a a.isLt
      obtain ⟨x1, x2⟩ := hX.2 a a.isLt
      refine ⟨exp_fix ?_ t, exp_fix ?_ t⟩
      · rw [hYv, hginvfix _ h1, x1, Matrix.mulVec_zero]
      · rw [hYv, hginvfix _ h2, x2, Matrix.mulVec_zero]
    · exact exp_fix (by rw [hYv, hXz, Matrix.mulVec_zero]) t
  have heq : ∀ t : ℝ, F (g * NormedSpace.exp ((t : ℂ) • X)) =
      (π (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)))).comp (F g) := by
    intro t
    rw [hexp t]
    exact hF.2 g hg _ (hmem t)
  have hd := rd_hasDeriv hF.1 hg hX
  have hd' := ((ContinuousLinearMap.apply ℂ Wp v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.apply_apply] at hd'
  have hfun : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (F g v)) =
      fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)) v := by
    funext t
    rw [heq t]
    rfl
  rw [dRep, hfun]
  exact hd'.deriv.symm

private theorem herm_bvec_eq_zero_of_inWb {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w)
    (j : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) : herm (Hpk k r) (bvec j) w = 0 := by
  unfold herm
  have hcol : Hpk k r *ᵥ bvec j = fun i => Hpk k r i j := by
    ext i; simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
  rw [hcol]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val < r ∨ r + k < i.val
  · simp [hw i hi]
  · push_neg at hi
    have h0 : Hpk k r i j = 0 := by
      unfold Hpk
      rw [if_neg (by omega), if_neg (by omega),
        if_neg (by rintro ⟨_, _, h⟩; have := congrArg Fin.val h; omega)]
    simp [h0]

theorem ad_unitB_lie {g : Mx k r} {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hBs : IsFrameOf k r [g⁻¹ *ᵥ z] Bs) (a b : Fin m) :
    (inLieLev k r (Fin.last r) (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b)) ∧
      inLieLev k r (Fin.last r) (hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b))) ∧
    (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ (g⁻¹ *ᵥ z) = 0 ∧
      hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ (g⁻¹ *ᵥ z) = 0) := by
  obtain ⟨hW, _, hO⟩ := hBs
  have hk : ∀ v, (∀ c, herm (Hpk k r) v (Bs c) = 0) →
      hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ v = 0 ∧
        hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ v = 0 :=
    fun v hv => ad_unitB_kill Bs a b (hv a) (hv b)
  have hz : ∀ c, herm (Hpk k r) (g⁻¹ *ᵥ z) (Bs c) = 0 := by
    intro c
    rw [ad_herm_symm, hO c _ (List.mem_singleton_self _)]
    simp
  have he : ∀ a' : Fin r, (∀ c, herm (Hpk k r) (bvec (eI k r a')) (Bs c) = 0) ∧
      (∀ c, herm (Hpk k r) (bvec (esI k r a')) (Bs c) = 0) := fun a' =>
    ⟨fun c => herm_bvec_eq_zero_of_inWb (hW c) _ (Or.inl (by simp only [eI]; exact a'.isLt)),
      fun c => herm_bvec_eq_zero_of_inWb (hW c) _ (Or.inr (by simp only [esI]; have := a'.isLt; omega))⟩
  exact ⟨⟨⟨hpart1_lie _, fun a' _ => ⟨(hk _ (he a').1).1, (hk _ (he a').2).1⟩⟩,
    ⟨hpart2_lie _, fun a' _ => ⟨(hk _ (he a').1).2, (hk _ (he a').2).2⟩⟩⟩, (hk _ hz).1, (hk _ hz).2⟩

theorem ad_RZ_point {F : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ AdK k r z π D) {g : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hgi : g⁻¹ * g = 1) (hgi' : g * g⁻¹ = 1) (hgU : IsUnit g)
    (hginv : g⁻¹ ∈ UH (Hpk k r)) {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hBs : IsFrameOf k r [g⁻¹ *ᵥ z] Bs) (a b : Fin m) (v : Wq) :
    RZ (Hpk k r) (unitB (Hpk k r) Bs a b) F g v =
      EcRep (Hpk k r) π (unitB (Hpk k r) (fun c => g *ᵥ Bs c) a b) (F g v) := by
  have hH : (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r := hginv
  have hgH : gᴴ * Hpk k r * g = Hpk k r := by
    calc gᴴ * Hpk k r * g = gᴴ * ((g⁻¹)ᴴ * Hpk k r * g⁻¹) * g := by rw [hH]
      _ = (g⁻¹ * g)ᴴ * Hpk k r * (g⁻¹ * g) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hgi]; simp
  obtain ⟨⟨h1, h2⟩, hk1, hk2⟩ := ad_unitB_lie (z := z) (g := g) hBs a b
  simp only [RZ, EcRep]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ad_rd_point hF hg hgi hgi' hgU hginv h1 hk1 v, ad_rd_point hF hg hgi hgi' hgU hginv h2 hk2 v,
    ad_unitB_conj hgH hgi', (ad_hpart_conj hgH hgi' _).1, (ad_hpart_conj hgH hgi' _).2]

theorem ad_foldr {ι X Y : Type*} (K : Set X) (P : X → Y) (l : List ι) (T : ι → X → X) (T' : ι → Y → Y)
    (hK : ∀ j, ∀ x ∈ K, T j x ∈ K) (hP : ∀ j, ∀ x ∈ K, P (T j x) = T' j (P x)) (x : X) (hx : x ∈ K) :
    (l.map T).foldr (fun S h => S h) x ∈ K ∧
      P ((l.map T).foldr (fun S h => S h) x) = (l.map T').foldr (fun S h => S h) (P x) := by
  induction l with
  | nil => exact ⟨hx, rfl⟩
  | cons j l ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨hK j _ h1, ?_⟩
    simp only [List.map_cons, List.foldr_cons]
    rw [hP j _ h1, h2]

theorem left_ad (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' (Fin.last r) D) (hπ'1 : π' 1 = 1)
    {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ)
    (hBs : IsFrameOf k r [g⁻¹ *ᵥ z] Bs) (w : ℂ) (v : Wq) :
    capR k r Bs w J g v = capRep k r π (fun a => g *ᵥ Bs a) w (J g v) := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1.1
  have hLI : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc (Hpk k r * gᴴ * Hpk k r) * g = Hpk k r * (gᴴ * Hpk k r * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, hpk_sq']
  have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv hLI
  have hgi : g⁻¹ * g = 1 := by rw [hinv, hLI]
  have hgi' : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse hLI)
  have hgU : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_left_inverse hLI)
  have hginv : g⁻¹ ∈ UH (Hpk k r) := by
    show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
    calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hU]
      _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hgi']; simp
  have h1W : (1 : Mx k r) ∈ UWset k r z' := by
    refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> simp [UH]
  have hJ' : J ∈ AdK k r z π D := by
    refine ⟨hJ.1, fun x hx h hh => ?_⟩
    have e := hJ.2.2.2 x hx h hh 1 h1W
    rw [mul_one, hπ'1] at e
    simpa [ContinuousLinearMap.one_def] using e
  unfold capR capRep qmF
  simp only [Finset.sum_apply, ContinuousLinearMap.sum_apply, Pi.smul_apply,
    ContinuousLinearMap.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  refine (ad_foldr (AdK k r z π D) (fun F => F g v) _ _ _ ?_ ?_ J hJ').2
  · intro j x hx
    have hl := (ad_unitB_lie (z := z) (g := g) hBs (id (σ j)) (id j)).1
    refine adK_add ?_ (adK_RZ hD.1 hl.1 hl.2 hx)
    split_ifs
    · exact adK_smul hx _
    · exact adK_zero
  · intro j x hx
    simp only [Pi.add_apply, ContinuousLinearMap.add_apply]
    rw [ad_RZ_point hx hg hgi hgi' hgU hginv hBs _ _ v]
    split_ifs <;> simp

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
