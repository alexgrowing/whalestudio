import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.FinrankRow

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def GaussRow (B : Cd.Base D cc δ) : Prop :=
  ∀ (N : ℕ) (γ : Matrix.unitaryGroup (Fin N) D.host.E) (Ae : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1), Even N →
    (∀ x, Ae x = x - (phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1).symm x) →
    ∀ S : Finset (TaylorLogMetric.VC D N 1), IsReps (latA (La0 B N 1) (phiU γ 1) Ae) (La0 B N 1) S →
      gaussC (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) Ae S ^ 2 = 1

def Lat0IsLat (B : Cd.Base D cc δ) (N N' : ℕ) : Prop := IsLat (La0 B N N')

theorem exists_cay {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (φ : V ≃ₗ[ℂ] V)
    (h : ∀ x, φ.symm x = x → x = 0) : ∃ Ae : V ≃ₗ[ℂ] V, ∀ x, Ae x = x - φ.symm x := by
  let f : V →ₗ[ℂ] V := LinearMap.id - (φ.symm : V →ₗ[ℂ] V)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply h
    have : x - φ.symm x = 0 := hx
    exact (sub_eq_zero.mp this).symm
  exact ⟨LinearEquiv.ofInjectiveEndo f hf, fun x => rfl⟩

variable {B : Cd.Base D cc δ}

theorem line_of_spans {N N' : ℕ} (hSp : B.ThZeroSpans N N') :
    AtMostLine (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (La0 B N N') := by
  intro θ hθ hθ0 F hF
  obtain ⟨a, ha⟩ := hSp θ hθ
  obtain ⟨b, hb⟩ := hSp F hF
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hθ0 (by rw [ha, zero_smul])
  refine ⟨b / a, ?_⟩
  rw [hb, ha, smul_smul, div_mul_cancel₀ b ha0]

theorem unitaryData (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
    (Ae : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') (hA : ∀ x, Ae x = x - (phiU γ γ').symm x) :
    UnitaryData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') (La0 B N N') (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ))
      (phiU γ γ') Ae := by
  have a0 : TaylorLogMetric.admitted D N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') := admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')
  have a1 : TaylorLogMetric.admitted D N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
      (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) :=
    admissible_of_integral_conj_le hN hN' (smulSD D N _ γ (sd0 N)) (smulSD D N' _ γ' (sd0 N'))
  have hi : imgLat ((phiU γ γ' : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (La0 B N N') =
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) := la_img _ _ _ _ _ _ _ _
  exact
    { herm := formV_herm' _ _ _ _
      pos := formV_pos (area_pos' B) _ _ _
      selfDual := (hL.1 N N' _ _ a0).1
      semi := (hL.1 N N' _ _ a0).2
      isom := phiL_isom _ _ _ _ _ _ _
      semi' := by rw [hi]; exact (hL.1 N N' _ _ a1).2
      inv := fun x _ => al_phi _ _ _ _ _ _ x
      idx₁ := by rw [hi]; exact (hL.2 N N' _ _ _ _ a1 a0).1
      idx₂ := by rw [hi]; exact (hL.2 N N' _ _ _ _ a0 a1).1
      cay := hA }

private theorem eq_zero_of_phiU_symm_fixed {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (hγ : (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)).det ≠ 0) (x : TaylorLogMetric.VC D N N')
    (hx : (phiU γ (1 : Matrix.unitaryGroup (Fin N') D.host.E)).symm x = x) : x = 0 := by
  funext τ
  have h := congrFun hx τ
  change (((1 : Matrix.unitaryGroup (Fin N') D.host.E) : Matrix (Fin N') (Fin N') D.host.E).map
    (TaylorLogMetric.embT D τ))ᴴ * of (x τ) * (γ : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.embT D τ) = x τ at h
  simp only [OneMemClass.coe_one, Matrix.map_one _ (map_zero _) (map_one _), conjTranspose_one,
    Matrix.one_mul] at h
  set Γ := (γ : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.embT D τ) with hΓ
  have hdet : IsUnit (Γ - 1).det := by
    rw [isUnit_iff_ne_zero]
    have e1 : Γ - 1 = ((γ : Matrix (Fin N) (Fin N) D.host.E) - 1).map (TaylorLogMetric.embT D τ) := by
      rw [hΓ, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    have e2 : (((γ : Matrix (Fin N) (Fin N) D.host.E) - 1).map (TaylorLogMetric.embT D τ)).det =
        TaylorLogMetric.embT D τ ((γ : Matrix (Fin N) (Fin N) D.host.E) - 1).det :=
      (RingHom.map_det (TaylorLogMetric.embT D τ) _).symm
    rw [e1, e2, map_ne_zero, ← neg_sub, Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hγ
  have hX : of (x τ) * (Γ - 1) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    exact sub_eq_zero.mpr h
  have h2 := congrArg (· * (Γ - 1)⁻¹) hX
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one, Matrix.zero_mul] at h2
  exact h2

private theorem det_eq_det_pow_card_of_diagonal_copies {ι V V₁ : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁] (e : V ≃ₗ[ℂ] ι → V₁)
    (A : V →ₗ[ℂ] V) (A₁ : V₁ →ₗ[ℂ] V₁) (h : ∀ x i, e (A x) i = A₁ (e x i)) :
    LinearMap.det A = LinearMap.det A₁ ^ Fintype.card ι := by
  have hA : A = (e.symm : (ι → V₁) →ₗ[ℂ] V) ∘ₗ (LinearMap.pi fun i => A₁ ∘ₗ LinearMap.proj i) ∘ₗ
      (e.symm.symm : V →ₗ[ℂ] ι → V₁) := by
    apply LinearMap.ext
    intro x
    apply e.injective
    funext i
    simp [h]
  rw [hA, LinearMap.det_conj, LinearMap.det_pi, Finset.prod_const, Finset.card_univ]

private theorem relIdx_latA_ne_zero_of_copies {ι V V₁ : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V₁] [Module ℂ V₁] {e : V ≃ₗ[ℂ] ι → V₁} {H : Sesq V} {H₁ : Sesq V₁} {α : V → ℂ}
    {α₁ : V₁ → ℂ} {Λ : AddSubgroup V} {Λ₁ : AddSubgroup V₁} {δ Ae : V ≃ₗ[ℂ] V} {δ₁ Ae₁ : V₁ ≃ₗ[ℂ] V₁}
    (hc : Copies e H H₁ α α₁ Λ Λ₁ δ Ae δ₁ Ae₁) (i₀ : ι) {S : Finset V}
    (hS : IsReps (latA Λ δ Ae) Λ S) : relIdx (latA Λ₁ δ₁ Ae₁) Λ₁ ≠ 0 := by
  classical
  unfold relIdx AddSubgroup.relIndex
  have hfin : Finite (Λ₁ ⧸ (latA Λ₁ δ₁ Ae₁).addSubgroupOf Λ₁) := by
    let f : S → Λ₁ ⧸ (latA Λ₁ δ₁ Ae₁).addSubgroupOf Λ₁ := fun x =>
      QuotientAddGroup.mk ⟨e x.1 i₀, (hc.lat x.1).mp (hS.1 x.1 x.2) i₀⟩
    refine Finite.of_surjective f ?_
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H y₁ =>
      have hy : e.symm (fun _ => (y₁ : V₁)) ∈ Λ := (hc.lat _).mpr (fun i => by simp)
      obtain ⟨x, hx, hxy⟩ := hS.2.2 _ hy
      refine ⟨⟨x, hx⟩, ?_⟩
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have h3 := (hc.mem_latA _).mp hxy i₀
      simp only [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply] at h3
      simpa [f, neg_add_eq_sub] using h3
  exact AddSubgroup.index_ne_zero_of_finite

theorem J1at_of_ne (hS : B.StdOK) (hL : B.LatAll) (hG : GaussRow B) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (hLat : Lat0IsLat B N N') (hSp : B.ThZeroSpans N N') (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (hγ : (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)).det ≠ 0) : J1at B N N' γ := by
  classical
  have h0 := B.thZeroMem hS N N'
  unfold J1at Base.thHalf
  rcases Nat.eq_zero_or_pos N' with rfl | hpos
  · have hsub : ∀ a b : AddSubgroup (TaylorLogMetric.VC D N 0), a = b := fun a b => Subsingleton.elim a b
    rw [hsub (TaylorLogMetric.La D B.tor (SDLat.smulLat _ _) _) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D 0)),
      iopSelf D B.tor N 0 _ _ (mem_ThSp_of' D B.tor _ _ h0), Nat.zero_div, pow_zero, one_smul]
    funext z
    simp only [TaylorLogMetric.pull]
    congr 1
    exact Subsingleton.elim _ _
  · have hpull : TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) 1 (B.thZero N N') =
        pullInv (phiU γ (1 : Matrix.unitaryGroup (Fin N') D.host.E)) (B.thZero N N') := by
      unfold phiU
      exact pull_eq _ _ _ _ _ _ _
    rw [hpull]
    set δφ := phiU γ (1 : Matrix.unitaryGroup (Fin N') D.host.E) with hδφ
    set δ₁ := phiU γ (1 : Matrix.unitaryGroup (Fin 1) D.host.E) with hδ₁
    obtain ⟨Ae, hAe⟩ := exists_cay δφ (eq_zero_of_phiU_symm_fixed γ hγ)
    obtain ⟨Ae₁, hAe₁⟩ := exists_cay δ₁ (eq_zero_of_phiU_symm_fixed γ hγ)
    have hU := unitaryData hL hN hN' γ 1 Ae hAe
    have hc : Copies (rowE D N N') (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N')
        (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ))
        (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (La0 B N N') (La0 B N 1) δφ Ae δ₁ Ae₁ := by
      refine ⟨form_row _ N N', al_row B hS N N', lat_row B N N', map_row γ, ?_⟩
      intro x i
      rw [hAe, hAe₁, map_sub, Pi.sub_apply]
      congr 1
      have h5 := map_row γ (δφ.symm x) i
      rw [LinearEquiv.apply_symm_apply] at h5
      rw [h5, LinearEquiv.symm_apply_apply]
    obtain ⟨-, hidx⟩ := unitary_index _ _ _ _ _ _ hLat hU
    have hdetA0 : LinearMap.det (Ae : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') ≠ 0 :=
      (LinearEquiv.isUnit_det' Ae).ne_zero
    have hV : relIdx (latA (La0 B N N') δφ Ae) (La0 B N N') ≠ 0 := by
      intro h6
      rw [h6] at hidx
      have h7 : (relIdx (imgLat (δφ : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (La0 B N N')) (La0 B N N') : ℝ) ≠ 0 := by
        exact_mod_cast hU.idx₁
      have h8 : ‖LinearMap.det (Ae : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N')‖ ^ 2 ≠ 0 :=
        pow_ne_zero _ (norm_ne_zero_iff.mpr hdetA0)
      push_cast at hidx
      exact (mul_ne_zero h7 h8) hidx.symm
    obtain ⟨⟨SV, hSV⟩, -⟩ := repsExist _ _ _ hV
    have hidx₁ := relIdx_latA_ne_zero_of_copies hc ⟨0, hpos⟩ hSV
    obtain ⟨⟨S₁, hS₁⟩, -⟩ := repsExist _ _ _ hidx₁
    have hK := unitaryConstant _ _ _ _ δφ Ae hLat hU (line_of_spans hSp) (prodReps (rowE D N N') S₁)
      (hc.reps hS₁) _ h0
    have himg : imgLat (δφ : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (La0 B N N') =
        TaylorLogMetric.La D B.tor (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N)) (StandardLatticesGL3.stdL D N') := by
      rw [hδφ]
      unfold phiU
      rw [la_img]
      simp only [OneMemClass.coe_one, Examples₂.smulLat_one]
    rw [hK, Iop_eq, ← himg, hc.gauss hS₁.1, det_eq_det_pow_card_of_diagonal_copies (rowE D N N') _ _ hc.cay, Fintype.card_fin]
    congr 1
    have hconj := detCayley _ _ (formV_herm' _ _ N 1) (formV_pos (area_pos' B) _ N 1) δ₁ Ae₁
      (by rw [hδ₁]; unfold phiU; exact phiL_isom _ _ _ _ _ _ _) hAe₁
    rw [finrank_row, hδ₁, det_row, (hN.mul_left _).neg_one_pow, one_mul] at hconj
    have hg := hG N γ Ae₁ hN hAe₁ S₁ hS₁
    have ha0 : LinearMap.det (Ae₁ : TaylorLogMetric.VC D N 1 →ₗ[ℂ] TaylorLogMetric.VC D N 1) ≠ 0 :=
      (LinearEquiv.isUnit_det' Ae₁).ne_zero
    set a := LinearMap.det (Ae₁ : TaylorLogMetric.VC D N 1 →ₗ[ℂ] TaylorLogMetric.VC D N 1) with ha
    set g := gaussC (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) Ae₁ S₁ with hgdef
    have key : ((‖a‖ : ℂ) / a * g) ^ 2 = ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ) (star (γ : Matrix (Fin N) (Fin N) D.host.E).det) := by
      rw [mul_pow, div_pow, hg, mul_one]
      have hn : ((‖a‖ : ℂ)) ^ 2 = a * (starRingEnd ℂ) a := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        ring
      rw [hn, hconj]
      field_simp
    obtain ⟨m, hm⟩ := hN'
    subst hm
    rw [show (m + m) / 2 = m by omega, ← key, ← pow_mul, norm_pow, Complex.ofReal_pow, mul_pow, div_pow]
    ring_nf

theorem J2at_of_ne (hS : B.StdOK) (hL : B.LatAll) (hG : GaussRow B) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (hLat : Lat0IsLat B N N') (hSp : B.ThZeroSpans N N') (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
    (hγ : (1 - (γ' : Matrix (Fin N') (Fin N') D.host.E)).det ≠ 0) : J2at B N N' γ' := by
  classical
  have h0 := B.thZeroMem hS N N'
  unfold J2at
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · have hsub : ∀ a b : AddSubgroup (TaylorLogMetric.VC D 0 N'), a = b := fun a b => Subsingleton.elim a b
    rw [hsub (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D 0) (SDLat.smulLat _ _)) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D 0) (StandardLatticesGL3.stdL D N')),
      iopSelf D B.tor 0 N' _ _ (mem_ThSp_of' D B.tor _ _ h0), Nat.zero_div, pow_zero, one_smul]
    funext z
    simp only [TaylorLogMetric.pull]
    congr 1
    exact Subsingleton.elim _ _
  · have hpull : TaylorLogMetric.pull D B.tor 1 (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
        pullInv (phiU (1 : Matrix.unitaryGroup (Fin N) D.host.E) γ') (B.thZero N N') := by
      unfold phiU
      exact pull_eq _ _ _ _ _ _ _
    rw [hpull]
    set δφ := phiU (1 : Matrix.unitaryGroup (Fin N) D.host.E) γ' with hδφ
    set δ₁ := phiU (cjU γ') (1 : Matrix.unitaryGroup (Fin 1) D.host.E) with hδ₁
    have hsymm : ∀ x j, colE D N N' (δφ.symm x) j = δ₁.symm (colE D N N' x j) := by
      intro x j
      have h5 := map_col γ' (δφ.symm x) j
      rw [LinearEquiv.apply_symm_apply] at h5
      rw [h5, LinearEquiv.symm_apply_apply]
    have hfix : ∀ x, δφ.symm x = x → x = 0 := by
      intro x hx
      apply (colE D N N').injective
      rw [map_zero]
      funext j
      apply eq_zero_of_phiU_symm_fixed (cjU γ') (ne_cjU γ' hγ)
      rw [← hsymm, hx]
    obtain ⟨Ae, hAe⟩ := exists_cay δφ hfix
    obtain ⟨Ae₁, hAe₁⟩ := exists_cay δ₁ (eq_zero_of_phiU_symm_fixed (cjU γ') (ne_cjU γ' hγ))
    have hU := unitaryData hL hN hN' 1 γ' Ae hAe
    have hc : Copies (colE D N N') (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N')
        (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N' 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ))
        (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (La0 B N N') (La0 B N' 1) δφ Ae δ₁ Ae₁ := by
      refine ⟨form_col _ N N', al_col B hS N N', lat_col B N N', map_col γ', ?_⟩
      intro x j
      rw [hAe, hAe₁, map_sub, Pi.sub_apply, hsymm]
    obtain ⟨-, hidx⟩ := unitary_index _ _ _ _ _ _ hLat hU
    have hdetA0 : LinearMap.det (Ae : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') ≠ 0 :=
      (LinearEquiv.isUnit_det' Ae).ne_zero
    have hV : relIdx (latA (La0 B N N') δφ Ae) (La0 B N N') ≠ 0 := by
      intro h6
      rw [h6] at hidx
      have h7 : (relIdx (imgLat (δφ : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (La0 B N N')) (La0 B N N') : ℝ) ≠ 0 := by
        exact_mod_cast hU.idx₁
      have h8 : ‖LinearMap.det (Ae : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N')‖ ^ 2 ≠ 0 :=
        pow_ne_zero _ (norm_ne_zero_iff.mpr hdetA0)
      push_cast at hidx
      exact (mul_ne_zero h7 h8) hidx.symm
    obtain ⟨⟨SV, hSV⟩, -⟩ := repsExist _ _ _ hV
    have hidx₁ := relIdx_latA_ne_zero_of_copies hc ⟨0, hpos⟩ hSV
    obtain ⟨⟨S₁, hS₁⟩, -⟩ := repsExist _ _ _ hidx₁
    have hK := unitaryConstant _ _ _ _ δφ Ae hLat hU (line_of_spans hSp) (prodReps (colE D N N') S₁)
      (hc.reps hS₁) _ h0
    have himg : imgLat (δφ : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (La0 B N N') =
        TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) := by
      rw [hδφ]
      unfold phiU
      rw [la_img]
      simp only [OneMemClass.coe_one, Examples₂.smulLat_one]
    rw [hK, Iop_eq, ← himg, hc.gauss hS₁.1, det_eq_det_pow_card_of_diagonal_copies (colE D N N') _ _ hc.cay, Fintype.card_fin]
    congr 1
    have hconj := detCayley _ _ (formV_herm' _ _ N' 1) (formV_pos (area_pos' B) _ N' 1) δ₁ Ae₁
      (by rw [hδ₁]; unfold phiU; exact phiL_isom _ _ _ _ _ _ _) hAe₁
    rw [finrank_row, hδ₁, det_row, (hN'.mul_left _).neg_one_pow, one_mul, det_cjU] at hconj
    simp only [star_star] at hconj
    have hg := hG N' (cjU γ') Ae₁ hN' hAe₁ S₁ hS₁
    have ha0 : LinearMap.det (Ae₁ : TaylorLogMetric.VC D N' 1 →ₗ[ℂ] TaylorLogMetric.VC D N' 1) ≠ 0 :=
      (LinearEquiv.isUnit_det' Ae₁).ne_zero
    set a := LinearMap.det (Ae₁ : TaylorLogMetric.VC D N' 1 →ₗ[ℂ] TaylorLogMetric.VC D N' 1) with ha
    set g := gaussC (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N' 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) Ae₁ S₁ with hgdef
    have key : ((‖a‖ : ℂ) / a * g) ^ 2 = ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ) (γ' : Matrix (Fin N') (Fin N') D.host.E).det := by
      rw [mul_pow, div_pow, hg, mul_one]
      have hn : ((‖a‖ : ℂ)) ^ 2 = a * (starRingEnd ℂ) a := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        ring
      rw [hn, hconj]
      field_simp
    obtain ⟨m, hm⟩ := hN
    subst hm
    rw [show (m + m) / 2 = m by omega, ← key, ← pow_mul, norm_pow, Complex.ofReal_pow, mul_pow, div_pow]
    ring_nf

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
