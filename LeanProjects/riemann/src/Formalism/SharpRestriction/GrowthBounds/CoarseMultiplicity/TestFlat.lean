import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.MulMatQOne

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf.TF

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti tensor_lattice_twist_eq tens_Le edgeLat_of la_tw_mul la_tw_transpose la_tw_inv dE invT_mul_D dual_edgeBasis w_ne p_eq
  pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF edgeBasis dual_edge latDual_colSpan)
open Formalism.L2.G.Model.TS

section

variable {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jO : W →+* O} {w : O} {m : ℕ} {TT : Finset (Fin n')} {aT bT : Fin n' → ℕ}

variable (thK : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)) ≃ₗ[Kf] ↥(VHH (m := m) Kf TT aT bT))

theorem Xi_CC (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecH TT) (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) (hhDegs TT aT bT)) (e : Edge W Qq (m + 1)) (he : IsEdge p n' 1 e)
    (t c : ℕ) (v : ↥(VHH (m := m) Kf TT aT bT)) (hv : v ∈ CCe p ι σ w TT aT bT t c e.dual) :
    XiH thK (zK Kf p κ TT aT bT) v ∈ CCe' p ι σ w TT aT bT t c e := by
  have hs1 : ∀ M : Submodule O (VHH (m := m) Kf TT aT bT), scale (1 : Kf) M = M := by
    intro M
    ext x
    simp [scale, Submodule.mem_map]
  have hs1' : ∀ M : Submodule O (Module.Dual Kf (VHH (m := m) Kf TT aT bT)), scale (1 : Kf) M = M := by
    intro M
    ext x
    simp [scale, Submodule.mem_map]
  simp only [CCe, CCe', Submodule.mem_inf, Submodule.mem_iInf] at hv ⊢
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := hv
  obtain ⟨g, hg⟩ := edgeBasis hS m 1 e he
  have hpQ : ((p : ℕ) : Qq) ≠ 0 := by
    haveI := hS.frac_alt
    intro h0
    apply hS.p_unif.ne_zero
    apply IsFractionRing.injective W Qq
    rw [map_natCast, h0, map_zero]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hℓu : IsUnit (g * Matrix.diagonal fun c : Fin (m + 1) =>
        if c.val < 1 then ((p : Qq))⁻¹ else 1).det := by
      rw [Matrix.det_mul, Matrix.det_diagonal]
      refine hg.1.mul (isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun c _ => ?_))
      split_ifs
      · exact inv_ne_zero hpQ
      · exact one_ne_zero
    have htgt := hg.2.2
    have hsrc : e.dual.src = colSpan W ((g * Matrix.diagonal fun c : Fin (m + 1) =>
        if c.val < 1 then ((p : Qq))⁻¹ else 1)⁻¹).transpose := by
      show latDual e.tgt = _
      rw [htgt, latDual_colSpan _ hℓu]
    rw [hsrc] at hv1
    have h1 := FD_HL thK hS hm hthK κ hMD _ hℓu _ v hv1
    rwa [← htgt] at h1
  · have h1 := FD_edge thK hS hm hthK κ hMD 1 e g hg 1 v (by rw [hs1]; exact hv2)
    rwa [hs1'] at h1
  · intro e'' he''
    have hd := dual_edge hS m 1 e'' he''.1
    have hsrc : e''.dual.src = e.dual.src := by
      show latDual e''.tgt = latDual e.tgt
      rw [he''.2.1]
    have hne : e''.dual ≠ e.dual := fun heq =>
      he''.2.2 (by rw [← hd.2, heq, (dual_edge hS m 1 e he).2])
    have hv3' := hv3 e''.dual ⟨hd.1, hsrc, hne⟩
    obtain ⟨b, hb⟩ := edgeBasis hS m 1 e'' he''.1
    exact FD_edge thK hS hm hthK κ hMD 1 e'' b hb _ v hv3'

theorem kapR_zTen (hS : HidaSetting p n' W Qq O Kf ι σ jO w) :
    kapR hS (zTen (KK O) p m TT aT bT) = zK Kf p (kapZ p m TT aT bT) TT aT bT := by
  simp [zTen, zK, map_div₀, map_pow, map_natCast, map_prod, Nat.cast_prod]

theorem pairing (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ)
    (hthK : ∀ P, ((thK P : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecH TT) (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsUnit b.det)
    (hb' : IsUnit ((b⁻¹).transpose * dE (m + 1) 1 ((p : ℕ) : Qq)).det)
    (Θ Θ' : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
        ↥(VHH (m := m) Kf TT aT bT))
    (hΘ : ∀ F, ((Θ F : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
        thF hS m (vecH TT) (fun x => la_tw ι σ x.1.val.val b) F.1)
    (hΘ' : ∀ F, ((Θ' F : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
        thF hS m (vecH TT) (fun x => la_tw ι σ x.1.val.val ((b⁻¹).transpose * dE (m + 1) 1 ((p : ℕ) : Qq))) F.1)
    (F F' : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O)) (y : O) :
    letI : Algebra (WF p n') O := algOfIdent jO φ
    zTen (KK O) p m TT aT bT *
        fock (liftSubst p n' O w 1 (hhLetters TT) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'))
            (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)))
          (liftSubst p n' O w 1 (hhLetters TT) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'))
            (F' : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O))) = algebraMap O (KK O) y →
    beHH (m := m) p TT aT bT (Θ F) (XiH thK (zK Kf p (kapZ p m TT aT bT) TT aT bT) (Θ' F')) = algebraMap O Kf y := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  intro hy
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  have hF0 := (pol_iff hS _ _ _).1 F.2
  have hF0' := (pol_iff hS _ _ _).1 F'.2
  let P : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)) :=
    ⟨Lin (fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val b)⁻¹) (map (kapR hS) F.1), Lin_Pol _ _ hF0⟩
  let Q : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)) :=
    ⟨Lin (fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val ((b⁻¹).transpose * dE (m + 1) 1 ((p : ℕ) : Qq)))⁻¹)
      (map (kapR hS) F'.1), Lin_Pol _ _ hF0'⟩
  have hP : Θ F = thK P := Subtype.ext (by rw [hΘ, hthK]; rfl)
  have hQ : Θ' F' = thK Q := Subtype.ext (by rw [hΘ', hthK]; rfl)
  have hk := congrArg (kapR hS) hy
  rw [map_mul, kapR_alg, kapR_zTen, fock_eq_fockR, ← fockR_map,
    lift_one hS φ hφ m TT aT bT b hb F.1 F.2, lift_one hS φ hφ m TT aT bT _ hb' F'.1 F'.2,
    tsact_smul_left, tsact_smul_right] at hk
  have hdual : ∀ x : TT × Bool,
      Aa x.2 (la_tw ι σ x.1.val.val ((b⁻¹).transpose * dE (m + 1) 1 ((p : ℕ) : Qq)) * lb_D (m + 1) 1 c) *
        (Aa x.2 (la_tw ι σ x.1.val.val b * lb_D (m + 1) 1 c)).transpose = 1 := by
    intro x
    rw [hc, dualM hS x.1.val.val 1 b hb]
    exact Aa_dual' x.2 _ (by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb).mul (lb_D_det _ _ _ hw))
  rw [fockR_Lin_dual _ _ hdual] at hk
  unfold beHH
  rw [hP, hQ, map_smul, XiH_apply, smul_eq_mul, ← hk]
  have hpA : (p : Kf) ^ AHH TT aT bT = c ^ Avec (vecH TT) (hhDegs TT aT bT) * c ^ Avec (vecH TT) (hhDegs TT aT bT) := by
    rw [← Avec_eq (m := m), zpow_natCast, p_eq hS]
    ring
  rw [hpA]
  show _ = _ * (_ * (_ * fockR P.1 Q.1))
  ring

end

end Formalism.MainNotions.ColumnSystems.Pf.TF

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility TF
open Formalism.L2.G.Model (dE dual_edgeBasis pQ_ne edgeBasis dual_edge Th0)

theorem testFlatAt : TestFlatAt := by
  intro p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS φ hφ m TT aT bT hm e he
  letI : Algebra (WF p n') O := algOfIdent jO φ
  obtain ⟨b, hb⟩ := edgeBasis hS m 1 e he
  have hb' := dual_edgeBasis p 1 (pQ_ne hS) e b hb
  obtain ⟨Θ, hΘ1, hΘ2⟩ := flatTheta hS φ hφ m TT aT bT hm b hb.1
  obtain ⟨Θ', hΘ1', hΘ2'⟩ := flatTheta hS φ hφ m TT aT bT hm _ hb'.1
  obtain ⟨thK, hthK⟩ := exists_thK Kf hm (vecH TT) (hhDegs TT aT bT)
  have hpO : (p : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (settingCZ p n' W Qq O Kf ι σ jO w hS).2
  have hMD : MultDiv O p (kapZ p m TT aT bT) (k := m + 1) (hhDegs TT aT bT) :=
    multDiv_kapFl O p hpO (k := m + 1) (hhDegs TT aT bT)
  refine ⟨b, _, Θ, Θ', 1, 1, XiH thK (zK Kf p (kapZ p m TT aT bT) TT aT bT),
    ⟨hΘ1, hb.2.1, isGLW_one _, by rw [mul_matQ_one]; exact hb⟩,
    ⟨(dual_edge hS m 1 e he).1, hΘ1', hb'.2.1, isGLW_one _, by rw [mul_matQ_one]; exact hb'⟩,
    fun t c v hv => Xi_CC thK hS hm hthK _ hMD e he t c v hv,
    fun F => ⟨lift_Pol hS φ hφ m TT aT bT 1 (isGLW_one _) F.1 F.2, lift_Pol hS φ hφ m TT aT bT 1 (isGLW_one _) F.1 F.2⟩,
    fun F F' y hy => pairing thK hS φ hφ hthK b hb.1 hb'.1 Θ Θ' hΘ2 hΘ2' F F' y hy⟩

end Formalism.MainNotions.ColumnSystems.Pf
