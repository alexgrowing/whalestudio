import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric
open UpperTheory.V.Z.Desc.V0

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.V0.KC

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

private theorem colT_rel (hψ : StdPsi ψ) (X : Set (GA E a))
    (hX : ∀ γ : GL (Fin a) E, IsMir (a - 1) γ → ∀ g ∈ X, ratGL E a γ * g ∈ X)
    {m : ℕ} {f : GA E a → ℂ} (hma : m + 1 < a) (hG : Good ψ (m + 1) f)
    (h0 : ∀ g ∈ X, colT ψ (m + 1) f g = 0) : ∀ g ∈ X, f g = 0 := by
  intro g₀ hgX
  by_contra hg₀
  have hPer : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g₀)) :=
    per_blk hG.cont (fun c g => hG.left _ (isMir_blkU c) g) g₀
  have hΦ0 : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E => f (blkU x * g₀)) ≠ 0 := by
    intro h
    have h1 := congrFun h 0
    simp only [Pi.zero_apply] at h1
    apply hg₀
    have e : (blkU (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) : GA E a) = 1 := posU_zero _
    rw [e, one_mul] at h1
    exact h1
  obtain ⟨ξ, hξ⟩ : ∃ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, coefF ψ (m + 1) ξ f g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hΦ0 (GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero E _ ψ hψ _ hPer h)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    apply hξ
    have hv := hG.van (m + 1) (Nat.succ_pos m) le_rfl g₀
    have e : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E, ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1 := by
      intro x
      simp [dot]
    simp only [coefF, e, one_mul]
    exact hv
  obtain ⟨γ, hγ, hγξ⟩ := GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last E a m hma ξ hξ0
  have hγ' : IsMir (a - 1) γ := fun i k h => hγ i k (by omega)
  have h1 := h0 _ (hX γ hγ' g₀ hgX)
  simp only [colT] at h1
  rw [GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hG.cont hG.left γ hγ (eLast a (m + 1)) g₀] at h1
  have e : (fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1) = ξ :=
    funext hγξ
  rw [e] at h1
  exact hξ h1

private theorem whit_rel (hψ : StdPsi ψ) (X : Set (GA E a))
    (hX : ∀ γ : GL (Fin a) E, IsMir (a - 1) γ → ∀ g ∈ X, ratGL E a γ * g ∈ X) (m : ℕ) :
    (m < a ∨ m = 0) → ∀ {f : GA E a → ℂ}, Good ψ m f → (∀ g ∈ X, whit ψ m f g = 0) → ∀ g ∈ X, f g = 0 := by
  induction m with
  | zero => exact fun _ _ _ h => h
  | succ m ih =>
    intro h f hf h0
    have h1 : m + 1 < a := by omega
    exact colT_rel hψ X hX h1 hf (ih (Or.inl (by omega)) (GlobalTheory.CuspRep.Generic.good_colT hψ h1 hf) h0)

private theorem ker_le_of_rank {V : Type} [AddCommGroup V] [Module ℂ V] (K : Submodule ℂ V)
    (hr : Module.rank ℂ (V ⧸ K) ≤ 1) (l l' : V →ₗ[ℂ] ℂ) (hl : K ≤ LinearMap.ker l) (hl' : K ≤ LinearMap.ker l')
    {v₁ : V} (h1 : l v₁ ≠ 0) {v : V} (hv : l v = 0) : l' v = 0 := by
  obtain ⟨x, hx⟩ := rank_le_one_iff.1 hr
  obtain ⟨r₁, e₁⟩ := hx (K.mkQ v₁)
  obtain ⟨r, e⟩ := hx (K.mkQ v)
  have hr₁ : r₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at e₁
    exact h1 (hl ((Submodule.Quotient.mk_eq_zero K).1 e₁.symm))
  have e2 : K.mkQ (v - (r / r₁) • v₁) = 0 := by
    rw [map_sub, map_smul, ← e, ← e₁, smul_smul, div_mul_cancel₀ _ hr₁, sub_self]
  have hK : v - (r / r₁) • v₁ ∈ K := (Submodule.Quotient.mk_eq_zero K).1 e2
  have h2 : l (v - (r / r₁) • v₁) = 0 := hl hK
  have h3 : l' (v - (r / r₁) • v₁) = 0 := hl' hK
  rw [map_sub, map_smul, hv, zero_sub, neg_eq_zero, smul_eq_mul] at h2
  have hc : r / r₁ = 0 := (mul_eq_zero.1 h2).resolve_right h1
  rw [hc, zero_smul, sub_zero] at h3
  exact h3

private theorem denseRange_mapGL {K B : Type} [Field K] [Field B] [TopologicalSpace B] [IsTopologicalRing B]
    [ContinuousInv₀ B] [T1Space B] (j : K →+* B) (hj : DenseRange j) (a : ℕ) :
    DenseRange (GeneralLinearGroup.map j : GL (Fin a) K → GL (Fin a) B) := by
  intro M
  rw [mem_closure_iff]
  intro o ho hMo
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 ho
  let f : Matrix (Fin a) (Fin a) B → Matrix (Fin a) (Fin a) B × (Matrix (Fin a) (Fin a) B)ᵐᵒᵖ :=
    fun P => (P, MulOpposite.op P⁻¹)
  have hdet : M.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  have hinv : ContinuousAt (fun P : Matrix (Fin a) (Fin a) B => P⁻¹) M.val := by
    have e : (fun P : Matrix (Fin a) (Fin a) B => P⁻¹) = fun P => (P.det)⁻¹ • P.adjugate := by
      funext P
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [e]
    exact ((continuousAt_inv₀ hdet).comp (continuous_id.matrix_det).continuousAt).smul
      (continuous_id.matrix_adjugate).continuousAt
  have hf : ContinuousAt f M.val := continuousAt_id.prodMk (MulOpposite.continuous_op.continuousAt.comp hinv)
  have hfM : f M.val = Units.embedProduct _ M := by
    simp only [f, Units.embedProduct_apply, Matrix.coe_units_inv]
  have hN : f ⁻¹' O ∩ {P | P.det ≠ 0} ∈ nhds M.val := by
    refine Filter.inter_mem (hf.preimage_mem_nhds (hO.mem_nhds ?_)) ?_
    · rw [hfM]; exact hMo
    · exact (isOpen_ne.preimage (continuous_id.matrix_det)).mem_nhds hdet
  have hd : DenseRange fun Q : Matrix (Fin a) (Fin a) K => Q.map j :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hj
  obtain ⟨Q, hQO, hQd⟩ := hd.mem_nhds hN
  have hQ : IsUnit Q.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => hQd ?_
    have : j Q.det = 0 := by rw [h0, map_zero]
    rw [RingHom.map_det] at this
    exact this
  let γ : GL (Fin a) K := ((Matrix.isUnit_iff_isUnit_det Q).2 hQ).unit
  refine ⟨GeneralLinearGroup.map j γ, ?_, γ, rfl⟩
  change Units.embedProduct _ (GeneralLinearGroup.map j γ) ∈ O
  have e : Units.embedProduct _ (GeneralLinearGroup.map j γ) = f (Q.map j) := by
    simp only [f, Units.embedProduct_apply, Matrix.coe_units_inv]
    rfl
  rw [e]; exact hQO

variable [IsTotallyComplex E]

private noncomputable def pw (w : HeightOneSpectrum (𝓞 E)) : GA E a →* GL (Fin a) (w.adicCompletion E) :=
  (GeneralLinearGroup.map (pLoc E w)).comp (GeneralLinearGroup.map (pFin E))

private theorem pw_fl (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)) :
    pw w (finGL E a (locGL E a w u)) = u := by
  simp only [pw, MonoidHom.comp_apply, pFin_finGL, pLoc_locGL]

private theorem pw_rat (w : HeightOneSpectrum (𝓞 E)) (γ : GL (Fin a) E) :
    pw w (ratGL E a γ) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ := by
  apply Units.ext
  ext i j
  rfl

private theorem comm_of_pw (w : HeightOneSpectrum (𝓞 E)) {h : GA E a} (hk : pw w h = 1)
    (u : GL (Fin a) (w.adicCompletion E)) :
    h * finGL E a (locGL E a w u) = finGL E a (locGL E a w u) * h := by
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, pInf_finGL, one_mul, mul_one]
  · rw [map_mul, map_mul, pFin_finGL]
    exact LocUniq.comm_locGL w hk u

omit [NumberField E] [IsTotallyComplex E] in
private theorem isMirL_mul {k : Type} [Field k] {p q : GL (Fin a) k} (hp : IsMirL p) (hq : IsMirL q) : IsMirL (p * q) := by
  intro i j hi
  change (p.val * q.val) i j = _
  rw [Matrix.mul_apply]
  simp_rw [hp i _ hi]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact hq i j hi

omit [NumberField E] [IsTotallyComplex E] in
private theorem isMirL_one {k : Type} [Field k] : IsMirL (1 : GL (Fin a) k) := fun _ _ _ => rfl

private def X (w : HeightOneSpectrum (𝓞 E)) : Set (GA E a) := {g | IsMirL (pw w g)}

private theorem X_stable (w : HeightOneSpectrum (𝓞 E)) (γ : GL (Fin a) E) (hγ : IsMir (a - 1) γ) (g : GA E a)
    (hg : g ∈ X w) : ratGL E a γ * g ∈ X w := by
  change IsMirL (pw w (ratGL E a γ * g))
  rw [map_mul, pw_rat]
  refine isMirL_mul (fun i j hi => ?_) hg
  change algebraMap E (w.adicCompletion E) (γ.val i j) = _
  rw [hγ i j (Or.inl (by omega))]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

end UpperTheory.V.Z.Desc.V0.KC

open UpperTheory.V.Z.Desc.V0.KC GlobalTheory.CuspRep.Generic in
theorem UpperTheory.V.Z.Desc.V0.kirCusp :
    KirCusp := by
  intro E _ _ _ a _ P w σ hσ
  obtain ⟨f, hf0, hf⟩ := hσ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar E
  have hg : ∀ v, Good ψ (a - 1) (f v).1.1 := fun v => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ (f v).1 (P.cusp _ (f v).2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  have hv1 : (f v₀).1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h₀, gw, e, hc₀⟩ := GlobalTheory.T.exists_split_adelicMatrix_localComponent E a w g₀
  have hrt : ∀ u v x, whit ψ (a - 1) (f (σ.ρ u v)).1.1 x =
      whit ψ (a - 1) (f v).1.1 (x * finGL E a (locGL E a w u)) := fun u v x => by
    rw [hf u v]
    exact whit_rt _ _ _ _
  let L : GA E a → σ.V →ₗ[ℂ] ℂ := fun h =>
    { toFun := fun v => whit ψ (a - 1) (f v).1.1 h
      map_add' := fun v v' => by
        rw [map_add f]
        exact congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => by
        rw [map_smul f]
        exact congrFun (whit_smul (a - 1) c (f v).1.1) h }
  have hL : ∀ h v, L h v = whit ψ (a - 1) (f v).1.1 h := fun _ _ => rfl
  have hne : L h₀ (σ.ρ gw v₀) ≠ 0 := by
    rw [hL, hrt, ← e]
    exact hg₀
  have hlaw : ∀ h, (∀ u, h * finGL E a (locGL E a w u) = finGL E a (locGL E a w u) * h) →
      ∀ (u : GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) v,
      L h (σ.ρ u v) = (locPsi hψ w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin a) (w.adicCompletion E)).val p.1 p.2) : ℂ) * L h v := by
    intro h hc u v
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 u.2
    obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hL, hrt, hc, this, t3]
    rfl
  have hK : ∀ h, (∀ u, h * finGL E a (locGL E a w u) = finGL E a (locGL E a w u) * h) →
      GlobalTheory.PRep.twKer σ.ρ (GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a)) (GlobalTheory.LocGL.whitChar (locPsi hψ w) a) ≤
        LinearMap.ker (L h) := by
    intro h hc
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hlaw h hc, smul_eq_mul]
    exact sub_eq_zero.2 rfl
  have hcont : Continuous (locPsi hψ w) := by
    refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp
      (CuspSub.continuous_sLoc w)
  have hnt : locPsi hψ w ≠ 1 := fun h1 => by
    obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  have hrank := PositivityTheory.rg.gu.whit.whitLeOne (w.adicCompletion E) a (locPsi hψ w) σ.V σ.ρ σ.5 σ.6 hcont hnt
  refine ⟨locPsi hψ w, L h₀, hcont, hnt, ?_, ?_⟩
  · intro u hu v
    rw [hlaw h₀ hc₀ ⟨u, hu⟩ v]
    simp only [chr, one_mul]
  · intro v hv
    have hA : ∀ g ∈ (X w : Set (GA E a)), whit ψ (a - 1) (f v).1.1 g = 0 := by
      intro g hgX
      have hp : pw w (g * (finGL E a (locGL E a w (pw w g)))⁻¹) = 1 := by
        rw [map_mul, map_inv, pw_fl, mul_inv_cancel]
      have e1 : g = g * (finGL E a (locGL E a w (pw w g)))⁻¹ * finGL E a (locGL E a w (pw w g)) :=
        (inv_mul_cancel_right _ _).symm
      rw [e1, ← hrt, ← hL]
      exact ker_le_of_rank _ hrank (L h₀) (L _) (hK h₀ hc₀) (hK _ (comm_of_pw w hp)) hne (hv _ hgX)
    have hB := whit_rel hψ (X w) (X_stable w) (a - 1) h0 (hg v) hA
    have hC : (f v).1.1 = 0 := by
      funext g
      have hU : IsOpen {u | σ.ρ u v = v} := σ.5 v
      obtain ⟨γ, hγ⟩ := (denseRange_mapGL (algebraMap E (w.adicCompletion E))
        (HeightOneSpectrum.denseRange_algebraMap E w) a).exists_mem_open
        (hU.preimage (continuous_mul_right (pw w g))) ⟨(pw w g)⁻¹, by
          change σ.ρ ((pw w g)⁻¹ * pw w g) v = v
          rw [inv_mul_cancel, map_one]
          rfl⟩
      have hu : σ.ρ (pw w (ratGL E a γ * g)) v = v := by
        rw [map_mul, pw_rat]
        exact hγ
      have hp : pw w (ratGL E a γ * g * (finGL E a (locGL E a w (pw w (ratGL E a γ * g))))⁻¹) = 1 := by
        rw [map_mul _ _ (_)⁻¹, map_inv, pw_fl, mul_inv_cancel]
      have hX1 : ratGL E a γ * g * (finGL E a (locGL E a w (pw w (ratGL E a γ * g))))⁻¹ ∈ (X w : Set (GA E a)) := by
        change IsMirL _
        rw [hp]
        exact isMirL_one
      have h1 := hB _ hX1
      have h2 : (f (σ.ρ (pw w (ratGL E a γ * g)) v)).1.1 (ratGL E a γ * g * (finGL E a (locGL E a w (pw w (ratGL E a γ * g))))⁻¹) =
          (f v).1.1 (ratGL E a γ * g) := by
        rw [hf]
        change (f v).1.1 (_ * _) = _
        rw [inv_mul_cancel_right]
      rw [hu, h1] at h2
      rw [← (P.cusp _ (f v).2).1.left γ g]
      exact h2.symm
    have hfv : f v = 0 := Subtype.ext (Subtype.ext hC)
    obtain ⟨-, hirr⟩ := (isIrreducible_iff σ.ρ).1 σ.6
    rcases hirr (LinearMap.ker f) (fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hf, hx, map_zero]) with h | h
    · exact (Submodule.eq_bot_iff _).1 h v hfv
    · exact absurd (LinearMap.ker_eq_top.1 h) hf0
