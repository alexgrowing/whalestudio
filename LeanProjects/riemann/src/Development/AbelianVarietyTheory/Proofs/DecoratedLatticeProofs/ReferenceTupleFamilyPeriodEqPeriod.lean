import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsIntegralPendingObjectSymmetricFormsLevel
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodZeroOfClassPeriodDecompositionAl
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.MiTop.TailColumnRecursion

open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top

variable {D : D7}

theorem chain_cast {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C C' : ColumnChain R ι hc} (hC : C = C')
    (ψ : C.cls 0 → C.Y 0 → ℂ) (φ : C'.cls 0 → C'.Y 0 → ℂ) (h : HEq ψ φ) :
    (Eq.rec (motive := fun C _ => C.cls R.m → C.Y R.m → ℂ) (C.col ψ) hC) = C'.col φ := by
  subst hC; cases h; rfl

theorem rec_chain {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)
    (ψ : C.cls 0 → C.Y 0 → ℂ) {a b : ℕ} (h : a = b) :
    Eq.rec (motive := fun n _ => C.cls n → C.Y n → ℂ) (Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap a ψ) h = Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap b ψ := by
  subst h; rfl

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word}

theorem tcol (f : FamCh W u) (t : W.P.T) (i : ℕ) (ψ : (f.t t).Col 0) :
    (f.t t).col i ψ = Formalism.ThetaLiftIndependence.chainOpM (D.chTw u (W.P.I.tup t)).wt (D.chTw u (W.P.I.tup t)).Kmap i ψ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show (f.t t).K i ((f.t t).col i ψ) = _
    rw [ih]; rfl

end GlobalTheory.MiTop.TailColumnRecursion

namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}

theorem reads_uniq {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm}
    {bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))} (K : ClassesAtPrimes M bad)
    {S : D.what₂.Tau → SPar} {MX : DSModel D.sp.X' S} (eW : Pm.Wrow ≃ₗ[ℂ] (M.clsP → FrP D → ℂ))
    (j : SmT MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') (jM : Pm.Mt →ₗ⋆[ℂ] Pm.Wrow)
    (hval : ∀ z ∈ M.ptC, ∀ c, eW z c ∈ LinearMap.range j)
    (hjM : ∀ F, jM F ∈ M.ptC) (hper : ∀ w F, Pm.period w F = M.ipP (jM F) w)
    (hpos : ∀ z ∈ M.ptC, M.ipP z z = 0 → z = 0)
    {G G' : Pm.Mt} {f : SmT MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)}
    (h1 : ReadsG K eW j x G f) (h2 : ReadsG K eW j x G' f) : ∀ w, Pm.period w G = Pm.period w G' := by
  have hcard : ∀ c, (Nat.card (M.stabilizer₂ c) : ℂ) ≠ 0 := fun c => Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsingle : ∀ c v, Pm.period (eW.symm (Pi.single c (j v))) (G - G') = 0 := by
    intro c v
    obtain ⟨h, hh⟩ := GlobalTheory.Core.Rk.Top.Model.hasMat_exists (K.y c)
    have a := (h1 c v h hh).symm.trans (h2 c v h hh)
    rw [map_sub, sub_eq_zero]
    exact mul_left_cancel₀ (hcard c) a
  have hz : ∀ z ∈ M.ptC, Pm.period z (G - G') = 0 := by
    intro z hz
    have hdec : z = ∑ c, eW.symm (Pi.single c (eW z c)) := by
      apply eW.injective
      rw [map_sum]
      simp only [LinearEquiv.apply_symm_apply]
      exact (Finset.univ_sum_single (eW z)).symm
    rw [hdec, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    obtain ⟨v, hv⟩ := hval z hz c
    rw [← hv]
    exact hsingle c v
  have hz0 : jM (G - G') = 0 := hpos _ (hjM _) (by rw [← hper]; exact hz _ (hjM _))
  intro w
  have := hper w (G - G')
  rw [hz0, map_zero, LinearMap.zero_apply, map_sub, sub_eq_zero] at this
  exact this

end GlobalTheory.MiTop.TailColumnRecursion

namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}

theorem fic_val {bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f bad) (lam : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1))
    {κ : Type} (yc : κ → Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (z : κ → FrP D → ℂ)
    (hz : z ∈ FiC S (Formalism.L2.Forms.embT D) lam yc) (c : κ) : z c ∈ ValC (gramC (gramP D) (Formalism.L2.Forms.embT D)) lam := by
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hz
  exact (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) (yc c) (Set.mem_univ _)

theorem pos_core {κ : Type} [Fintype κ] {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (N : κ → ℕ) (hN : ∀ c, N c ≠ 0)
    (P : κ → MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (h : ∑ c, ((N c : ℕ) : ℂ)⁻¹ * Formalism.MainNotions.product_first_zeroth_parts.nfAll lam (P c) (P c) = 0) : ∀ c, P c = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨c0, hc0⟩ := hne
  have hre := congrArg Complex.re h
  rw [Complex.re_sum, Complex.zero_re] at hre
  have hterm : ∀ c, (((N c : ℕ) : ℂ)⁻¹ * Formalism.MainNotions.product_first_zeroth_parts.nfAll lam (P c) (P c)).re =
      ((N c : ℝ))⁻¹ * (Formalism.MainNotions.product_first_zeroth_parts.nfAll lam (P c) (P c)).re := by
    intro c
    rw [show ((N c : ℕ) : ℂ)⁻¹ = ((((N c : ℝ))⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  simp only [hterm] at hre
  have hnn : ∀ c, 0 ≤ ((N c : ℝ))⁻¹ * (Formalism.MainNotions.product_first_zeroth_parts.nfAll lam (P c) (P c)).re := by
    intro c
    refine mul_nonneg (by positivity) ?_
    by_cases hp : P c = 0
    · rw [hp]; simp [Formalism.MainNotions.product_first_zeroth_parts.nfAll, Formalism.REAL.fockF]
    · exact (GlobalTheory.LvT.PendExample.nfAll_pos lam hp).le
  have hpos : 0 < ((N c0 : ℝ))⁻¹ * (Formalism.MainNotions.product_first_zeroth_parts.nfAll lam (P c0) (P c0)).re := by
    have : (0 : ℝ) < N c0 := by exact_mod_cast Nat.pos_of_ne_zero (hN c0)
    exact mul_pos (inv_pos.mpr this) (GlobalTheory.LvT.PendExample.nfAll_pos lam hc0)
  have := Finset.sum_pos' (fun c _ => hnn c) ⟨c0, Finset.mem_univ _, hpos⟩
  linarith

end GlobalTheory.MiTop.TailColumnRecursion

namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}

section G
variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm}
    {bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))} {K : ClassesAtPrimes M bad} {okW : D.what₂.places.Pl → Prop}

open Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw in

theorem eW_rep_G (V : ValuationAtPrimes K okW) (o : FrP D) (z : Pm.Wrow) (hz : z ∈ M.ptC) (c : M.clsP) :
    ∃ Q ∈ CSpan M.sg, V.eW z c = fnOf _ (shiftOf (sgTG M)) (fun τ => (o.1 τ)⁻¹) Q := by
  have hF := (V.ptC z).1 hz
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) (K.y c) (Set.mem_univ _)
  obtain ⟨Q0, hQ0, hfn⟩ := Submodule.mem_map.1 hval
  have hQ0' : Q0 ∈ CSpan M.sg := by
    have := CSpan_shW M.sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold sgTG at hQ0
    rw [this] at hQ0
    exact hQ0
  have he : V.eW z c = fnOf _ (shiftOf (sgTG M)) 1 Q0 := by
    rw [hfn, ← hres]; rfl
  have hM : ∀ τ, IsUnit ((o.1 τ)⁻¹).det := fun τ => by
    rw [Matrix.det_nonsing_inv]; exact (o.2 τ).ringInverse
  refine ⟨_, ?_, he.trans (fnOf_change _ _ _ _ hM Q0)⟩
  exact Submodule.smul_mem _ _ (blkRow_mem _ _ hQ0')

theorem pos_G (V : ValuationAtPrimes K okW) : ∀ z ∈ M.ptC, M.ipP z z = 0 → z = 0 := by
  intro z hz h0
  obtain ⟨o, ho⟩ := GlobalTheory.PerRed.exists_orthonormal_frame₂ D
  choose P hP hPe using eW_rep_G V o z hz
  have hN : ∀ c, Nat.card (M.stabilizer₂ c) ≠ 0 := fun c => Nat.card_pos.ne'
  have hPz := pos_core M.sg (fun c => Nat.card (M.stabilizer₂ c)) hN P ((V.ipP o ho z z P P hP hP hPe hPe).symm.trans h0)
  apply V.eW.injective
  rw [map_zero]
  funext c
  rw [hPe c, hPz c, map_zero]
  rfl

end G

theorem pos_0 {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (T : FormsTiedSym D u Ch chOf) :
    ∀ z ∈ (D.fm u).ptC, (D.fm u).ipP z z = 0 → z = 0 := by
  intro z hz h0
  obtain ⟨o, ho⟩ := GlobalTheory.PerRed.exists_orthonormal_frame₂ D
  choose P hP hPe using GlobalTheory.PerRed.eW_rep_o T o z hz
  have hN : ∀ c, Nat.card ((D.fm u).stabilizer₂ c) ≠ 0 := fun c => Nat.card_pos.ne'
  have hPz := pos_core (D.fm u).sg (fun c => Nat.card ((D.fm u).stabilizer₂ c)) hN P
    ((T.valP.ipP o ho z z P P hP hP hPe hPe).symm.trans h0)
  apply T.valP.eW.injective
  rw [map_zero]
  funext c
  rw [hPe c, hPz c, map_zero]
  rfl

end GlobalTheory.MiTop.TailColumnRecursion

namespace GlobalTheory.MiTop.TailColumnRecursion
open Classical
open Formalism.L2.Forms GlobalTheory.Core.Rk.Top Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev
variable {D : D7}

theorem domWeight_ext {n : ℕ} : ∀ a b : DomWeight n, a.w = b.w → a = b := by
  rintro ⟨a, _⟩ ⟨b, _⟩ h; cases h; rfl

theorem sg_eq {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm}
    {bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F))} {K : ClassesAtPrimes M bad} {okW : D.what₂.places.Pl → Prop}
    (V : ValuationAtPrimes K okW) {K0 : ClsPTied u} (V0 : ValPTied u K0) : sgTG M = sgT u := by
  funext τ
  unfold sgTG sgT
  congr 1
  apply domWeight_ext
  funext i
  have a := V.sg τ i
  have b := V0.sg τ i
  exact_mod_cast a.trans b.symm

theorem referenceTuple_familyPeriod_eq_period (u : D.what₂.Word) (μ : D.what₂.Tup) (h0 : μ = D.what₂.mu0)
    (ψ0 : (D.chTw u μ).cls 0 → (D.chTw u μ).Y 0 → ℂ) (φ : D.what₂.Mu u) (hφ : HEq ψ0 (D.eMu u φ).1)
    (G1 G0 : D.what₂.Amb μ)
    (hu : ∀ w, (D.mem u).P.period w ((D.eMt u).symm (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) G1 h0)) =
      (D.mem u).P.period w ((D.eMt u).symm (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) G0 h0))) :
    (D.mem u).P.Ptil (Eq.rec (motive := fun C _ => C.cls D.R.m → C.Y D.R.m → ℂ)
        (Eq.rec (motive := fun ν _ => (D.chTw u ν).cls D.R.m → (D.chTw u ν).Y D.R.m → ℂ) ((D.chTw u μ).col ψ0) h0)
        (D.memberColumns_twistedChain_base u))
      ((D.eMt u).symm (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) G1 h0)) = D.what₂.perCol u μ φ G0 := by
  subst h0
  rw [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, PeriodMap.Ptil]
  simp only at hu ⊢
  rw [hu, chain_cast (D.memberColumns_twistedChain_base u) ψ0 _ hφ]

end GlobalTheory.MiTop.TailColumnRecursion

namespace GlobalTheory.MiTop
open Classical
open GlobalTheory.MiTop.TailColumnRecursion Formalism.L2.Forms

theorem linkTail_of_topReadAt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), ∀ u (f : FamCh W u), TopReadAt W u f.j f.g.bT → (∀ t, W.P.I.tup t = D.what₂.mu0 → ∀ φ : D.what₂.Mu u, HEq (col0 f t φ) (D.eMu u φ).1) → LinkTail f := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hTR h0 n h t φ F F' hFF G hG
  obtain ⟨hJ, -, hall⟩ := hTR
  have hR := (hall t).2 F F' hFF
  have hex : ∃ G0, Reads W u f.j f.g.bT (W.P.I.tup t) G0 (topOf W t F') := ⟨_, hR⟩
  have hspec := hex.choose_spec
  show tailOf W u f.j f.g.bT (W.P.I.tup t)
    (Eq.rec (motive := fun n _ => (D.chTw u (W.P.I.tup t)).cls n → (D.chTw u (W.P.I.tup t)).Y n → ℂ)
      ((f.t t).col (2 * n) (col0 f t φ)) h) G.1 = _
  rw [hG, tcol, rec_chain]
  unfold tailOf
  rw [dif_pos hex]
  by_cases hμ : W.P.I.tup t = D.what₂.mu0
  · rw [dif_pos hμ]
    refine referenceTuple_familyPeriod_eq_period u _ hμ _ φ (h0 t hμ φ) _ _ ?_
    have hv : ∀ z ∈ (D.fm u).ptC, ∀ c, (W.R.T.cols.forms u).valP.eW z c ∈ LinearMap.range f.j := by
      intro z hz c
      rw [hJ.range]
      exact fic_val _ _ _ _ (((W.R.T.cols.forms u).valP.ptC z).1 hz) c
    exact reads_uniq _ _ _ _ (W.R.T.cols.forms u).jM hv (W.R.T.cols.forms u).per.2.1 (W.R.T.cols.forms u).per.2.2
      (pos_0 (W.R.T.cols.forms u)) (hspec.1 hμ) (hR.1 hμ)
  · rw [dif_neg hμ, D.perCol_tie u _ hμ, PeriodMap.PtilCol, PeriodMap.Ptil, PeriodMap.Ptil]
    have hv : ∀ z ∈ (ex.tw.fm u (W.P.I.tup t)).ptC, ∀ c, (W.R.T.tw.pt.val u _ hμ).eW z c ∈ LinearMap.range f.j := by
      intro z hz c
      rw [hJ.range, ← sg_eq (W.R.T.tw.pt.val u _ hμ) (W.R.T.cols.forms u).valP]
      exact fic_val _ _ _ _ (((W.R.T.tw.pt.val u _ hμ).ptC z).1 hz) c
    rw [reads_uniq _ _ _ _ (W.R.T.tw.ptE.jM u _) hv (W.R.T.tw.ptE.per u _ hμ).2.1 (W.R.T.tw.ptE.per u _ hμ).2.2
      (pos_G (W.R.T.tw.pt.val u _ hμ)) (hspec.2 hμ) (hR.2 hμ)]
    rfl

end GlobalTheory.MiTop

end
