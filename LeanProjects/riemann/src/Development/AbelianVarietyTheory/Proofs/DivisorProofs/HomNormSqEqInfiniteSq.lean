import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphismOrthogonalPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagComponentFramePointRelationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPnHodgeLwEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentsBijectModuliComponentsStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open CategoryTheory AlgebraicGeometry GlobalTheory.ShFam.DeKeyTrue GlobalTheory.TrueGeo GlobalTheory.ProjVar.Var GlobalTheory.CxPts GlobalTheory.Toroidal Formalism.L2.Geo

namespace GlobalTheory.CovHt.Link

theorem hom_norm_orthogonal_frame {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) {σ : κ.c.F →+* ℂ}
    (hσ : GoodEmb κ.c σ) {Z : Comp s.Xo κ.c} {G : WTZ D.host.E} {ξ : ℝ} {g : Rul s.Xo κ.c}
    (hg : rdU (unf s σ) g ∈ holSub (unf s σ).X (modelWt (unf s σ) G)) {z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((unf s σ).X k).Ψ N}
    (hz : z ∈ framesOn (unf s σ) Z) :
    ∃ xx : ((s.U σ).X z.1).dom, ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((s.U σ).X z.1) xx.1 ∧ LiesOn Z ((s.U σ).un z.1 xx) ∧
      homN (unf s σ) ξ G g z = lieFacZ S.Dw ξ G * ‖Formalism.L2.PjFree.toC (evR s.Xo κ.c g ((s.U σ).un z.1 xx))‖ := by
  obtain ⟨k, fr⟩ := z
  obtain ⟨hd, hon⟩ := hz
  have hU : IsUnf (unf s σ) := by
    have h1 := s.unif.law σ hσ
    have e : s.U σ = s.unif.good σ hσ := UnfFam.U_eq _ hσ
    show IsUnf (GlobalTheory.ThetaDictCompare.toU (s.U σ))
    rw [e]
    exact h1
  have hsec : ((unf s σ).X k).IsSec (modelWt (unf s σ) G k) (rdU (unf s σ) g k) := by
    clear hon
    have key : ∀ P ∈ holSub (unf s σ).X (modelWt (unf s σ) G), ((unf s σ).X k).IsSec (modelWt (unf s σ) G k) (P k) := by
      intro P hP
      induction hP using Submodule.span_induction with
      | mem P hP => exact (hP k).1.1
      | zero => exact ⟨differentiableOn_const _, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩
      | add P Q _ _ hP hQ =>
        exact ⟨hP.1.add hQ.1, fun x hx b hb => by simp only [Pi.add_apply, hP.2.1 x hx b hb, hQ.2.1 x hx b hb]; ring,
          fun γ hγ x hx => by simp only [Pi.add_apply, hP.2.2 γ hγ x hx, hQ.2.2 γ hγ x hx]; ring⟩
      | smul a P _ hP =>
        exact ⟨hP.1.const_smul a, fun x hx b hb => by simp only [Pi.smul_apply, smul_eq_mul, hP.2.1 x hx b hb]; ring,
          fun γ hγ x hx => by simp only [Pi.smul_apply, smul_eq_mul, hP.2.2 γ hγ x hx]; ring⟩
    exact key _ hg
  have hb := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem ((unf s σ).X k) hd
  have hz' := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom ((unf s σ).X k) hd hb
  have ho := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf ((unf s σ).X k) hd
  have hp := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul ((unf s σ).X k) _ _ hsec.2.1 fr hd _ hb
  obtain ⟨t₀, ht₀⟩ := (hU.2.2.2.1 k k ⟨fr, hd⟩ ⟨_, hz'⟩).2 ⟨1, one_mem _, _, hb, by
    have : ReciprocityTheory.ChartRestriction.G.FD.lact (1 : GL (Fin N) D.host.E) fr = fr := by
      funext τ
      simp only [ReciprocityTheory.ChartRestriction.G.FD.lact, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
      rfl
    rw [this]⟩
  have hinv := (GlobalTheory.Frames.frBor_calculus _ _ _ _ _ _ (CAt σ) _ _ ((unf s σ).un k ⟨fr, hd⟩)).2.2.2 t₀ ht₀
  refine ⟨⟨_, hz'⟩, fun τ => ho τ, GlobalTheory.FlatLine.liesOn_frBor hinv hon, ?_⟩
  have hrd : rdU (unf s σ) g k (ReciprocityTheory.ChartRestriction.G.FD.rmul fr (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf ((unf s σ).X k) fr)) =
      Formalism.L2.PjFree.toC (evR s.Xo κ.c g ((s.U σ).un k ⟨_, hz'⟩)) := dif_pos hz'
  show lieFacZ S.Dw ξ G * ((unf s σ).X k).pnorm _ _ fr = _
  rw [← hp, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ ho), hrd]

end GlobalTheory.CovHt.Link

namespace GlobalTheory.CovHt.Link

theorem lieFactor_sq_eq_prod {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} (la : AllWt.Weight S.Dw) :
    lieFacZ S.Dw (xiR D) (wtOf S.Dw la 0) ^ 2 =
      ∏ z : Letter S.Dw, (2 * Real.pi * xiR D) ^ (-exOf S.Dw la 0 (some z)) := by
  have hκ : 0 < 2 * Real.pi * xiR D := by have := GlobalTheory.ShFam.xiR_pos D; positivity
  have hz : ∀ e : ℤ, (2 * Real.pi * xiR D) ^ e = Real.exp (e * Real.log (2 * Real.pi * xiR D)) := fun e => by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos hκ, mul_comm]
  simp_rw [hz]
  rw [← Real.exp_sum, lieFacZ, ← Real.exp_nat_mul]
  congr 1
  rw [← Finset.sum_mul, Fintype.sum_sigma]
  simp only [Int.cast_neg, Finset.sum_neg_distrib]
  have e : ∀ (τ : D.host.E →+* ℂ) (i : Fin (S.Dw.mult τ)),
      ((exOf S.Dw la 0 (some ⟨τ, i⟩) : ℤ) : ℝ) = ((wtOf S.Dw la 0).1 (τ, i) : ℝ) := fun τ i => rfl
  simp only [e]
  push_cast
  ring

end GlobalTheory.CovHt.Link

namespace GlobalTheory.CovHt.Link

theorem mem_offBoundary_of_complex_point {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)
    {σ : D.what₂.LL →+* ℂ} (ψ : ℂ →+* ℂ) (p : Pts (Φ.C k).Y σ) {σ₁ : κ.c.F →+* ℂ} (y : FrPt s.Xo κ.c (CAt σ₁))
    (h : ((Φ.C k).down p).1 = spMap ψ ≫ (GlobalTheory.ShFam.cxPt s.T.Z y).1) : p ∈ offBd Φ k σ := by
  intro hb
  change (Φ.C k).π (under p) ∉ Set.range s.T.Z.jQ at hb
  obtain ⟨t, ht⟩ : ∃ t, (Φ.C k).π (under p) = ((Φ.C k).down p).1 t :=
    ⟨_, (Scheme.Hom.comp_apply p.1 (Φ.C k).π _).symm⟩
  rw [h] at ht
  apply hb
  rw [ht]
  exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans (Scheme.Hom.comp_apply _ _ _).symm⟩

end GlobalTheory.CovHt.Link

namespace GlobalTheory.CovHt.Link

theorem eq_of_over_of_over {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)
    {Z Z' : Comp s.Xo κ.c} (h : Over Φ k Z) (h' : Over Φ k Z') : Z = Z' := by
  by_contra hne
  let u : Sp (Φ.C k).Y.Fn := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Φ.C k).Y.Fn)
  exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ _ _ hne) (h u) (h' u)

theorem component_eq_of_complex_point {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k k' : s.Comp)
    (Z : Comp s.Xo κ.c) (hk : Over Φ k Z) {σ : D.what₂.LL →+* ℂ} (ψ : ℂ →+* ℂ) (p : Pts (Φ.C k').Y σ) {σ₁ : κ.c.F →+* ℂ}
    (y : FrPt s.Xo κ.c (CAt σ₁)) (hy : LiesOn Z y)
    (h : ((Φ.C k').down p).1 = spMap ψ ≫ (GlobalTheory.ShFam.cxPt s.T.Z y).1) : k' = k := by
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  obtain ⟨t, ht⟩ : ∃ t, (Φ.C k').π (under p) = ((Φ.C k').down p).1 t :=
    ⟨_, (Scheme.Hom.comp_apply p.1 (Φ.C k').π _).symm⟩
  rw [h] at ht
  unfold GlobalTheory.ShFam.cxPt at ht
  simp only [Scheme.Hom.comp_apply] at ht
  have hW := GlobalTheory.ShFam.PtComp.preimage_connectedComponent_mem s.T.Z hsm ((Φ.C k').π (under p))
  have eZ : (⟨_, hW⟩ : Comp s.Xo κ.c) = Z := by
    by_contra hne
    have hy1 := hy (spMap ψ t)
    refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ _ _ hne) ?_ hy1
    show s.T.Z.jQ _ ∈ connectedComponent _
    rw [ht]
    exact mem_connectedComponent
  have hO' : Over Φ k' Z := by
    intro u
    rw [← eZ]
    show s.T.Z.jQ _ ∈ connectedComponent _
    rw [← Scheme.Hom.comp_apply, (Φ.C k').y0_x, Scheme.Hom.comp_apply]
    exact (isPreconnected_range (Φ.C k').π.continuous).subset_connectedComponent ⟨_, rfl⟩ ⟨_, rfl⟩
  obtain ⟨q, hq⟩ := GlobalTheory.T.flag_components_biject_moduli_components D A N j S κ s Φ
  refine q.injective ?_
  rw [eq_of_over_of_over Φ k' (hq k') hO', eq_of_over_of_over Φ k (hq k) hk]

end GlobalTheory.CovHt.Link

theorem GlobalTheory.CovHt.Link.homN_sq_eq_infSq : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (x : ToroidalCompactificationData s) (k : s.Comp) (Z : Comp s.Xo κ.c), Over Φ k Z → ∀ (la : AllWt.Weight S.Dw), ∀ g ∈ cuspOn (unf s) Z (wtOf S.Dw la 0), ∀ σ : κ.c.F →+* ℂ, GoodEmb κ.c σ → ∀ z ∈ framesOn (unf s σ) Z, ∃ (σ' : D.what₂.LL →+* ℂ) (y : Pts (Φ.C k).Y σ'), y ∈ offBd Φ k σ' ∧ homN (unf s σ) (xiR D) (wtOf S.Dw la 0) g z ^ 2 = infSq Φ k x la σ' ((Φ.C k).val g) y := by
  intro D A N j S κ s Φ x k Z hO la g hg σ hσ z hz
  obtain ⟨hgc, hgZ⟩ := hg
  have hgW := mem_cuspW.1 hgc
  obtain ⟨xx, ho, hon, hN⟩ := hom_norm_orthogonal_frame s hσ (hgW.2 σ hσ) hz (ξ := xiR D)
  obtain ⟨σ', e1⟩ : ∃ σ' : D.what₂.LL →+* ℂ, Formalism.L2.PjFree.goodOf κ.c (GlobalTheory.ShFam.embOf κ.e σ') = σ := by
    refine ⟨σ.comp κ.e.toRingHom, ?_⟩
    have e2 : GlobalTheory.ShFam.embOf κ.e (σ.comp κ.e.toRingHom) = σ := by
      ext a; simp [GlobalTheory.ShFam.embOf]
    rw [e2]
    exact if_pos hσ
  subst e1
  obtain ⟨ψ, ⟨k', p⟩, g', hψ, hσψ, hg', hc, hd, hm⟩ := GlobalTheory.T.exists_automorphism_orthogonal_point s Φ σ' z.1 xx ho
  have hk : k' = k := component_eq_of_complex_point Φ k k' Z hO ψ p _ hon hd
  subst hk
  have hex0 : exOf S.Dw la 0 none = 0 := rfl
  have hco := GlobalTheory.T.flag_component_frame_point_relation (Φ.C k') ψ p g' ((s.U _).un z.1 xx) (exOf S.Dw la 0) g
    (by rcases hψ with rfl | rfl; exacts [rfl, RingHom.ext Complex.conj_conj]) hσψ hc hd hm hex0 hgW.1
  refine ⟨σ', p, mem_offBoundary_of_complex_point Φ k' ψ p _ hd, ?_⟩
  rw [hN]
  have hn : (fun z : Letter S.Dw => -exOf S.Dw la 0 (some z)) = fun z => -exOf S.Dw la 0 (some z) := rfl
  have hpn : (geoTrue D.what₂.LL).pn (Φ.C k').Y σ' ((Φ.C k').Lw la) (hodgeLw x Φ k' σ' la)
      ((geoTrue D.what₂.LL).cx (Φ.C k').Y σ' ((Φ.C k').val g)) p =
      ‖ψ (Formalism.L2.PjFree.toC (evR s.Xo κ.c g ((s.U _).un z.1 xx)))‖ ^ 2 *
        ∏ z : Letter S.Dw, (2 * Real.pi * xiR D) ^ (-exOf S.Dw la 0 (some z)) :=
    (pn_cast_met _ _ _ _).trans (pn_metsOf_none hg' hco)
  have hψn : ‖ψ (Formalism.L2.PjFree.toC (evR s.Xo κ.c g ((s.U _).un z.1 xx)))‖ =
      ‖Formalism.L2.PjFree.toC (evR s.Xo κ.c g ((s.U _).un z.1 xx))‖ := by
    rcases hψ with rfl | rfl
    · rfl
    · exact RCLike.norm_conj _
  show _ = (geoTrue D.what₂.LL).pn (Φ.C k').Y σ' ((Φ.C k').Lw la) (hodgeLw x Φ k' σ' la)
      ((geoTrue D.what₂.LL).cx (Φ.C k').Y σ' ((Φ.C k').val g)) p
  rw [hpn, hψn, ← lieFactor_sq_eq_prod la]
  ring
