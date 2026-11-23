import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FcCont

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace COne

theorem om_sch (d : SD σ) (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ h

theorem T_zero (d : SD σ) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.T Φ 0 = d.l Φ := by
  have := d.ok.dbl.kill 0 Φ h
  have e2 : (0 : Matrix (Fin d.m) (Fin d.n) (AE F E)) * (diagCols (Fin d.n) : Matrix _ _ (AE F E))ᵀ = 0 := Matrix.zero_mul _
  have e3 : (0 : Mx F E d.m d.n) * (incM F d.b.1.toCols₂)ᵀ = 0 := Matrix.zero_mul _
  erw [e2] at this
  show d.l (d.dd.rho d.B.ψ ((0 : Mx F E d.m d.n) * (incM F d.b.1.toCols₂)ᵀ) Φ) = _
  rw [e3]
  exact this

theorem section_eq_theta_zero (d : SD σ) {Φ : d.Fn} (h : Φ ∈ d.sch) (x : d.G) : d.sec0 Φ x = d.T (d.om x Φ) 0 :=
  (T_zero d (om_sch d x h)).symm

theorem T_smul (d : SD σ) (c : ℂ) (Φ : d.Fn) (X : Mx F E d.m d.n) : d.T (c • Φ) X = c * d.T Φ X := by
  unfold SD.T Darboux.rho
  have : schr d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ)) (c • Φ) = c • schr d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ)) Φ := by
    funext y; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
  rw [this, map_smul, smul_eq_mul]

theorem orb_smul (d : SD σ) (T : nF σ d.Y d.b) (c : ℂ) (Φ : d.Fn) : d.orb T (c • Φ) = c * d.orb T Φ := by
  unfold SD.orb
  simp only [T_smul, tsum_mul_left]
  simp only [MeasureTheory.average]
  exact integral_const_mul _ _

theorem Ln {d : SD σ} (L : LD d) : L.n + 1 = d.n := by
  have e : Fin L.n ≃ {i : Fin d.n // ¬ i = L.i₀} :=
    (Equiv.ofInjective L.em L.inj).trans (Equiv.subtypeEquivRight fun i => (L.rng i).symm)
  have h1 := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq] at h1
  have := L.i₀.isLt
  omega

theorem cosetSum_factor {G : Type} [Group G] (Pp Γ : Subgroup G) (Fn h : G → ℂ) (K : ℂ) (g₀ : G)
    (hF : ∀ g, Fn g = K * h (g * g₀)) (g : G) :
    GlobalTheory.Eis.cosetSum Pp Γ Fn g = K * GlobalTheory.Eis.cosetSum Pp Γ h (g * g₀) := by
  simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term, hF, mul_assoc]
  exact tsum_mul_left

theorem ht_cpow (r a : ℝ) (hr : 0 < r) (w : ℂ) :
    (((r * a).toNNReal : ℝ) : ℂ) ^ w = (r : ℂ) ^ w * (((a.toNNReal : ℝ) : ℂ)) ^ w := by
  rw [Real.toNNReal_mul hr.le, NNReal.coe_mul, Real.coe_toNNReal _ hr.le, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hr.le (NNReal.coe_nonneg _)]

theorem hv_shift (W : ℂ → ℂ) (s₀ a v c : ℂ) (r : ℝ) (hr : 0 < r) (hW : HolValueAt W (s₀ + a) v) :
    HolValueAt (fun z => (c * (r : ℂ) ^ (z - s₀)) * W (z + a)) s₀ (c * v) := by
  obtain ⟨H, hext, han, hval⟩ := hW
  have h1 := hext.comp_add
  have hK : AnalyticOnNhd ℂ (fun z => c * (r : ℂ) ^ (z - s₀)) Set.univ := fun z _ =>
    analyticAt_const.mul (analyticAt_const.cpow (analyticAt_id.sub analyticAt_const) (Complex.ofReal_mem_slitPlane.2 hr))
  have h2 : IsExtAt (fun z => c * (r : ℂ) ^ (z - s₀)) s₀ (fun z => c * (r : ℂ) ^ (z - s₀)) :=
    (isMerExt_self isRightDomain_univ hK.meromorphicOn).isExtAt (Set.mem_univ _)
  refine ⟨_, h2.mul h1, ?_, ?_⟩
  · exact (hK s₀ (Set.mem_univ _)).mul (han.comp_of_eq (analyticAt_id.add analyticAt_const) rfl)
  · simp [hval]

theorem fcVal (H : Hyps) {d' : SD σ} (R'' : RD d') (hMV : MainV 2 R'') {Ψ : d'.Fn} (hΨ : Ψ ∈ d'.sch)
    (hv : d'.T Ψ ∈ R''.vac) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d'.Y) d'.b nb lam 𝓖) (T : nF σ d'.Y d'.b)
    (g : d'.G) :
    HolValueAt (fun z => fc d'.B.ψ d'.b nb lam 𝓖 (d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z) T g) (s0 d'.m d'.n)
      (2 * fc d'.B.ψ d'.b nb lam 𝓖 (d'.I Ψ) T g) := by
  have hK := H.polyKFin F E σ d' R'' Ψ hΨ ((H.vacK F E σ d' R'').2.1 hv)
  have hsec := H.secK F E σ d' Ψ hK
  obtain ⟨U, p, Ê, t, hE⟩ := H.eisWk F E σ d' _ _ hsec (s0 d'.m d'.n)
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hadd, hbd⟩ := fcAll d' hc T g
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d'.Y) (fun f => fc d'.B.ψ d'.b nb lam 𝓖 f T g) hadd hbd U Ê hUo hd hcont hinv
  have hpt : ∀ g', ∀ i ≤ p.rootMultiplicity (s0 d'.m d'.n), iteratedDeriv i (Ê · g') (s0 d'.m d'.n) =
      iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * (2 * d'.I Ψ g') := fun g' =>
    ordVal U p (Ê · g') (fun z => d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z g') t _ (2 * d'.I Ψ g') hUo hR hs hp (hd g')
      (fun z hz => (hfar z hz).2 g') (hMV Ψ hΨ hv g')
  have hsm : ∀ (c : ℂ) (φ : d'.G → ℂ), fc d'.B.ψ d'.b nb lam 𝓖 (fun g' => c * φ g') T g =
      c * fc d'.B.ψ d'.b nb lam 𝓖 φ T g := by
    intro c φ; simp only [fc, mul_assoc]; exact integral_const_mul _ _
  have hder : ∀ i ≤ p.rootMultiplicity (s0 d'.m d'.n),
      iteratedDeriv i (fun z => fc d'.B.ψ d'.b nb lam 𝓖 (Ê z) T g) (s0 d'.m d'.n) =
        iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * (2 * fc d'.B.ψ d'.b nb lam 𝓖 (d'.I Ψ) T g) := by
    intro i hi
    rw [hComm _ hs i]
    have : (fun g' => iteratedDeriv i (Ê · g') (s0 d'.m d'.n)) =
        fun g' => (iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * 2) * d'.I Ψ g' :=
      funext fun g' => by rw [hpt g' i hi]; ring
    rw [this, hsm]; ring
  refine wrap U p _ _ t _ _ hUo hR hs hp hDiff (fun z hz => ?_) (fun i hi => ?_) (hder _ le_rfl)
  · have e1 : Ê z = fun g' => p.eval z * d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z g' := funext (hfar z hz).2
    rw [e1, hsm]
  · rw [hder i hi.le, pderiv_lt p _ i hi, zero_mul]

end COne

section Deg

variable (H : Hyps) {d : SD σ} (R : RD d) (L : LD d) (R' : RD L.sd) (hmn : d.m < d.n) (hIH : MainV 2 R') {Φ : d.Fn}
  (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
  (hE : EData d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t)

include H hIH hΦ hv in

theorem cOneVal_pf {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' lam' 𝓖'}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (x : d.G) :
    HolValueAt (fun z => cOne d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x) (s0 d.m d.n)
      (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x) := by
  obtain ⟨q, g₀, k, r, c, hk, hx, hr, ha, hTq⟩ := H.iwaQ F E σ d L x
  have hΦk : d.om k Φ ∈ d.sch := COne.om_sch d k hΦ
  have hvk : d.T (d.om k Φ) ∈ R.vac := (H.vacK F E σ d R).1 Φ hΦ hv k hk
  obtain ⟨Φ', hres, hv'⟩ := (H.vacK F E σ d R).2.2 L R' _ hΦk hvk
  have hΦ' : Φ' ∈ L.sd.sch := hres.1
  have hres0 : ∀ g : L.sd.G, L.sd.T (L.sd.om g Φ') 0 = d.T (d.om (L.j g) (d.om k Φ)) 0 := by
    intro g
    have := L.res _ hΦk Φ' hΦ' hres.2 g 0 (fun a => rfl)
    rwa [Matrix.submatrix_zero] at this
  have hf : ∀ g' : L.sd.G, d.sec0 Φ (L.j g' * x) = c * L.sd.sec0 Φ' (g' * g₀) := by
    intro g'
    have hΨ : d.om (L.j g₀) (d.om k Φ) ∈ d.sch := COne.om_sch d _ hΦk
    rw [COne.section_eq_theta_zero d hΦ, COne.section_eq_theta_zero L.sd hΦ', hx]
    have e : d.om (L.j g' * (q * L.j g₀ * k)) Φ = d.om (L.j g' * q) (d.om (L.j g₀) (d.om k Φ)) := by
      simp only [map_mul, mul_assoc]; rfl
    rw [e, hTq _ hΨ g' 0 (fun a => rfl), hres0 (g' * g₀)]
    congr 2
    simp only [map_mul]; rfl
  have hs' : s0 d.m L.n = s0 d.m d.n + 1 / 2 := by
    unfold s0; rw [← COne.Ln L]; push_cast; ring
  have hid : ∀ z, cOne d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x = (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
      fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.eis (L.sd.sec0 Φ') (s0 d.m L.n) (z + 1 / 2)) T' g₀ := by
    intro z
    have ex : z + 1 / 2 - s0 d.m L.n = z - s0 d.m d.n := by rw [hs']; ring
    have hF : ∀ g' : L.sd.G, ((d.Ht (L.j g' * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g' * x) =
        (c * (r : ℂ) ^ (z - s0 d.m d.n)) * (((L.sd.Ht (g' * g₀) : ℝ) : ℂ) ^ (z + 1 / 2 - s0 d.m L.n) *
          L.sd.sec0 Φ' (g' * g₀)) := by
      intro g'
      rw [hf g', ex]
      have e1 : ((d.Ht (L.j g' * x) : ℝ) : ℂ) = ((((r * L.a (g' * g₀)).toNNReal : ℝ)) : ℂ) := by
        simp only [SD.Ht, ha g']
      rw [e1, COne.ht_cpow r _ hr]
      simp only [SD.Ht]
      ring
    have hcs : GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) (fun g => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) *
        d.sec0 Φ (L.j g * x)) = fun g => (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
          L.sd.eis (L.sd.sec0 Φ') (s0 d.m L.n) (z + 1 / 2) (g * g₀) :=
      funext fun g => COne.cosetSum_factor _ _ _ _ _ g₀ hF g
    unfold cOne
    rw [hcs]
    simp only [fc, mul_one, mul_assoc, integral_const_mul]
  have hW := COne.fcVal H R' hIH hΦ' hv' hc' T' g₀
  rw [hs'] at hW
  have hsh := COne.hv_shift _ (s0 d.m d.n) (1 / 2) _ c r hr hW
  have hv1 : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = c * fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.I Φ') T' g₀ := by
    rw [H.thetaCoef F E σ d Φ hΦ nb lam 𝓖 hc T x, H.thetaCoef F E σ L.sd Φ' hΦ' nb' lam' 𝓖' hc' T' g₀]
    rw [(H.orbRes F E σ d).2 L T T' hT (d.om x Φ) (c • L.sd.om g₀ Φ') ⟨?_, ?_⟩, COne.orb_smul]
    · exact Submodule.smul_mem _ _ (COne.om_sch L.sd g₀ hΦ')
    · intro X hX
      rw [COne.T_smul]
      have h1 := L.res _ hΦk Φ' hΦ' hres.2 g₀ X hX
      have hΨ := COne.om_sch d (L.j g₀) hΦk
      have h2 := hTq _ hΨ 1 X hX
      simp only [map_one, one_mul, Module.End.one_apply] at h2
      have h1' : L.sd.T (L.sd.om g₀ Φ') (X.submatrix id L.em) = d.T (d.om (L.j g₀) (d.om k Φ)) X := h1
      rw [h1', hx]
      have e : d.om (q * L.j g₀ * k) Φ = d.om q (d.om (L.j g₀) (d.om k Φ)) := by simp only [map_mul]; rfl
      rw [e, h2]
  have hfun : (fun z => cOne d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x) = fun z => (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
      (fun z => fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.eis (L.sd.sec0 Φ') (s0 d.m d.n + 1 / 2) z) T' g₀) (z + 1 / 2) := by
    funext z; rw [hid z, hs']
  rw [hfun, hv1]
  convert hsh using 1
  ring

end Deg

end PositivityTheory.SiegelWeilFormula.AStep

end
