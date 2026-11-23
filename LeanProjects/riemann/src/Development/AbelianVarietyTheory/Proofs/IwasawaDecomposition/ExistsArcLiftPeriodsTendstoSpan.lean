import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArcStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnitHmE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.PerLim

open scoped CategoryTheory.MonObj in

theorem exists_transfer {S S' S0 : Scheme.{0}} {G : Over S} {G' : Over S'} {G0 : Over S0} [GrpObj G] [GrpObj G']
    [GrpObj G0] {f : S' ⟶ S} {f0 : S' ⟶ S0} {φ : G'.left ⟶ G.left} {φ0 : G'.left ⟶ G0.left}
    (h : IsGrpPullback G' G f φ) (h0 : IsGrpPullback G' G0 f0 φ0) (q : Sp ℂ ⟶ S') {y : Sp ℂ ⟶ S} {y0 : Sp ℂ ⟶ S0}
    (hy : q ≫ f = y) (hy0 : q ≫ f0 = y0) {g : ℕ} (ex0 : (Fin g → ℂ) → (Over.mk y0 ⟶ G0))
    (hadd : ∀ z w, ex0 (z + w) = ex0 z * ex0 w)
    (hol : IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G0.left from (ex0 z).left))) :
    ∃ ex : (Fin g → ℂ) → (Over.mk y ⟶ G), (∀ z w, ex (z + w) = ex z * ex w) ∧
      IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (ex z).left)) ∧
      (∀ (d : Fin g → ℂ) (w : Sp (DualNumber ℂ) ⟶ G'.left),
        w ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ q →
        IsDerivAt0 (fun z => (ex0 z).left) d (w ≫ φ0) → IsDerivAt0 (fun z => (ex z).left) d (w ≫ φ)) ∧
      ∀ z, ex z = 1 → ex0 z = 1 := by
  subst hy hy0
  let ex' : (Fin g → ℂ) → (Over.mk q ⟶ G') := fun z =>
    Over.homMk (h0.1.lift (ex0 z).left q (Over.w (ex0 z))) (h0.1.lift_snd _ _ _)
  have e0 : ∀ z, pushHom h0 (Over.mk q) (ex' z) = ex0 z := fun z =>
    Over.OverMorphism.ext (h0.1.lift_fst _ _ _)
  have e0' : ∀ z, (ex' z).left ≫ φ0 = (ex0 z).left := fun z => h0.1.lift_fst _ _ _
  have e1 : ∀ z, (ex' z).left ≫ G'.hom = q := fun z => Over.w (ex' z)
  have inj0 : Function.Injective (pushHom h0 (Over.mk q)) := fun a b hab =>
    Over.OverMorphism.ext (h0.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))
  have inj : Function.Injective (pushHom h (Over.mk q)) := fun a b hab =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))
  have hA : ∀ t, HolHom.HolAt (fun z => (show Sp ℂ ⟶ G'.left from (ex' z).left)) t := fun t =>
    HolHom.holAt_of_isPullback h0.1
      (by simp only [e0']; exact HolHom.holAt_of_isHolTo hol (Set.mem_univ t))
      (by simp only [e1]; exact HolHom.holAt_const _ _)
  refine ⟨fun z => pushHom h (Over.mk q) (ex' z), fun z w => ?_, ?_, fun d w hw hd => ?_, fun z hz => ?_⟩
  · have : ex' (z + w) = ex' z * ex' w := inj0 (by rw [map_mul, e0, e0, e0]; exact hadd z w)
    exact (congrArg _ this).trans (map_mul _ _ _)
  · exact HolHom.isHolTo_of_holAt isOpen_univ fun t _ => (hA t).comp φ
  · obtain ⟨v, hv⟩ := (hA 0).exists_isDerivAt d
    have h1 := hv.comp φ0
    simp only [e0'] at h1
    have h2 : v = w := h0.1.hom_ext (h1.unique ((HolHom.isDerivAt0_iff _ _ _).1 hd))
      ((HolHom.IsDerivAt.over (a := ex') hv).trans hw.symm)
    subst h2
    exact (HolHom.isDerivAt0_iff _ _ _).2 (hv.comp φ)
  · have : ex' z = 1 := inj (hz.trans (map_one _).symm)
    rw [← e0, this]
    exact map_one _

theorem eventually_eq_of_lattice {B La V : Type} [TopologicalSpace B] [AddCommGroup La] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (P : B → (La →+ V)) (hP : ∀ a, Continuous fun b => P b a)
    (b₀ : B) (hinj : Function.Injective (P b₀)) (hd : DiscreteTopology (P b₀).range)
    (hs : Submodule.span ℝ (Set.range (P b₀)) = ⊤) (a : B → La) (ha : Continuous fun b => P b (a b)) :
    ∀ᶠ b in 𝓝 b₀, a b = a b₀ := by
  classical
  let L : Submodule ℤ V := (P b₀).range.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨hs⟩
  let bz := Module.Free.chooseBasis ℤ L
  let bR := bz.ofZLatticeBasis ℝ L
  have hc : ∀ i, ∃ c, P b₀ c = bR i := fun i => by
    rw [Module.Basis.ofZLatticeBasis_apply]; exact (bz i).2
  choose c hc using hc
  let T : B → V →L[ℝ] V := fun b => ∑ i, (LinearMap.toContinuousLinearMap (bR.coord i)).smulRight (P b (c i))
  have hT : ∀ b x, T b x = ∑ i, bR.repr x i • P b (c i) := fun b x => by simp [T]
  have hTc : Continuous T := continuous_finset_sum _ fun i _ =>
    (ContinuousLinearMap.smulRightL ℝ V V (LinearMap.toContinuousLinearMap (bR.coord i))).continuous.comp (hP _)
  have hT0 : T b₀ = ContinuousLinearMap.id ℝ V := by
    ext x
    rw [hT]
    simp only [hc]
    exact bR.sum_repr x
  have hTP : ∀ b x, T b (P b₀ x) = P b x := fun b x => by
    let xl : L := ⟨P b₀ x, x, rfl⟩
    have h1 : ∀ i, bR.repr (P b₀ x) i = (bz.repr xl i : ℝ) := fun i => bz.ofZLatticeBasis_repr_apply ℝ L xl i
    have h2 : x = ∑ i, bz.repr xl i • c i := hinj (by
      rw [map_sum]
      simp only [map_zsmul, hc]
      rw [← bR.sum_repr (P b₀ x)]
      exact Finset.sum_congr rfl fun i _ => by rw [h1, Int.cast_smul_eq_zsmul])
    rw [hT]
    conv_rhs => rw [h2, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [h1, Int.cast_smul_eq_zsmul, map_zsmul]
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 (isOpen_discrete ({0} : Set L)) 0 rfl
  have h1 : ∀ᶠ b in 𝓝 b₀, ‖T b - T b₀‖ < 1 / 2 := by
    have : Tendsto (fun b => ‖T b - T b₀‖) (𝓝 b₀) (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 (hTc.tendsto b₀)
    exact this.eventually (gt_mem_nhds (by norm_num))
  have h2 : ∀ᶠ b in 𝓝 b₀, ‖P b (a b) - P b (a b₀)‖ < ε / 2 := by
    have : Tendsto (fun b => ‖P b (a b) - P b (a b₀)‖) (𝓝 b₀) (𝓝 ‖P b₀ (a b₀) - P b₀ (a b₀)‖) :=
      ((ha.sub (hP _)).norm.tendsto b₀)
    rw [sub_self, norm_zero] at this
    exact this.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [h1, h2] with b h1 h2
  rw [← map_sub, ← hTP] at h2
  set x := P b₀ (a b - a b₀) with hx
  have h3 : ‖T b x - x‖ ≤ 1 / 2 * ‖x‖ := by
    have := (T b - T b₀).le_of_opNorm_le h1.le x
    rwa [hT0] at this
  have h4 : ‖x‖ ≤ ‖T b x‖ + ‖T b x - x‖ := by
    have := norm_sub_le (T b x) (T b x - x)
    rwa [sub_sub_cancel] at this
  have h5 : (⟨x, _, rfl⟩ : L) ∈ Metric.ball (0 : L) ε := by
    rw [mem_ball_zero_iff]
    show ‖x‖ < ε
    linarith
  have h6 : x = 0 := congrArg Subtype.val (hb h5)
  exact sub_eq_zero.1 (hinj (h6.trans (map_zero _).symm))

theorem tendsto_eTwoPi : Tendsto eTwoPi imTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : (fun w => ‖eTwoPi w‖) = fun w : ℂ => Real.exp (-(2 * Real.pi * w.im)) := funext fun w => by
    rw [eTwoPi, Complex.norm_exp]
    simp
  rw [h]
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_comap (f := Complex.im) (x := atTop)).const_mul_atTop (by positivity))

theorem span_proj {n g m : ℕ} (lam : Fin n → Fin g → ℂ) (h : Submodule.span ℂ (Set.range lam) = ⊤) (s : Fin m → Fin g)
    (hs : Function.Injective s) : Submodule.span ℂ (Set.range fun j i => lam j (s i)) = ⊤ := by
  have : (fun j i => lam j (s i)) = LinearMap.funLeft ℂ ℂ s ∘ lam := rfl
  rw [this, Set.range_comp, ← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top]
  exact LinearMap.funLeft_surjective_of_injective ℂ ℂ s hs

theorem continuous_perFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {B : Type}
    [TopologicalSpace B] {x : B → Frame X.Ψ r} (hx : ∀ b, x b ∈ X.dom) (hc : Continuous x) (v : Fin r → E)
    (τ : E →+* ℂ) (i : ℕ) : Continuous fun b => perFr X (x b) v τ i := by
  have hm : ∀ t, Continuous fun b => mat (x b) t := fun t => (continuous_apply t).comp hc
  unfold perFr
  split_ifs with h1 h2 h3 h4
  · refine (continuous_apply (⟨X.p0 + i, h2⟩ : Fin r)).comp
      (Continuous.matrix_mulVec (A := fun b => (mat (x b) ⟨τ, h1⟩)⁻¹) ?_ continuous_const)
    refine continuous_iff_continuousAt.2 fun b => (continuousAt_matrix_inv _ ?_).comp (hm _).continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hx b _).1
  · exact continuous_const
  · simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC]
    exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun c _ =>
      (((hm _).matrix_elem _ _).mul continuous_const).mul continuous_const
  · exact continuous_const
  · exact continuous_const

theorem exists_periods_tendsto_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∃ (n : ℕ) (v : Fin n → Fin N → E) (Lp : Fin n → (U.X k).Ψ → Fin (N - (U.X k).p0) → ℂ) (Lm : Fin n → (U.X k).Ψ → Fin (U.X k).p0 → ℂ), (∀ j (τ : (U.X k).Ψ) (i : Fin (N - (U.X k).p0)), Tendsto (fun w => perFr (U.X k) (xx w) (v j) τ.1 i) imTop (𝓝 (Lp j τ i))) ∧ (∀ j (τ : (U.X k).Ψ) (i : Fin (U.X k).p0), Tendsto (fun w => perFr (U.X k) (xx w) (v j) (conjEmb τ.1) i) imTop (𝓝 (Lm j τ i))) ∧ ∀ τ : (U.X k).Ψ, Submodule.span ℂ (Set.range fun j => Lp j τ) = ⊤ ∧ Submodule.span ℂ (Set.range fun j => Lm j τ) = ⊤ := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift
  obtain ⟨hN, hX, -, -, -, g, e, F, ik, φL, -, hfr⟩ := hU
  obtain ⟨ρ, n, lam, hρ, hρr, hcont, hspan, hker⟩ := GlobalTheory.T.exists_continuous_lattice_vectors_along_arc E H Dw l Xo c O β Z σ A φ x fr ψ r g e harc
  obtain ⟨-, -, hxd, hxm, -⟩ := horb
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : ℝ, ∀ w : ℂ, T₁ < w.im → T < w.im ∧ eTwoPi w ∈ Metric.ball (0 : ℂ) ρ := by
    have h1 : ∀ᶠ w in imTop, eTwoPi w ∈ Metric.ball (0 : ℂ) ρ := tendsto_eTwoPi.eventually (Metric.ball_mem_nhds 0 hρ)
    obtain ⟨a, ha⟩ := eventually_atTop.1 (eventually_comap.1 h1)
    exact ⟨max a T, fun w hw => ⟨(le_max_right _ _).trans_lt hw, ha _ ((le_max_left _ _).trans hw.le) w rfl⟩⟩
  let B := {w : ℂ // w ∈ {w : ℂ | T₁ < w.im}}
  haveI : PreconnectedSpace B := Subtype.preconnectedSpace (convex_halfSpace_im_gt T₁).isPreconnected
  have hdom : ∀ b : B, xx b ∈ (U.X k).dom := fun b => hxm b (hT₁ b b.2).1
  choose Pm hPm hper hpt hder hrest using fun b : B => hfr k ⟨xx b, hdom b⟩
  clear hrest
  have key : ∀ (b : B) j, lam j (eTwoPi b) ∈ (Pm b).range := fun b j => by
    have hb := (hT₁ b b.2).2
    obtain ⟨_, hx1, hx2⟩ := hlift b (hT₁ b b.2).1
    obtain ⟨hm1, hm2⟩ := hm _ (Metric.ball_subset_ball hρr hb) (Complex.exp_ne_zero _)
    have h0 : GlobalTheory.AllWt.ptF (y (eTwoPi b)) ≫ pullback.fst _ _ = (y (eTwoPi b)).x := pullback.lift_fst _ _ _
    obtain ⟨ex, a1, a2, a3, a4⟩ := exists_transfer Z.m.cart Z.m0.toSABMap.cart
      (GlobalTheory.AllWt.ptF (S := CAt σ) (y (eTwoPi b)) :)
      (y := spMap (ψ (eTwoPi b)) ≫ x ≫ genι Z) (y0 := F.u (ik k) (Pm b))
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ genι Z) hm1).trans (Category.assoc _ _ _)))
      (h0.trans (hx1.symm.trans (hpt b))) (F.ex (ik k) (Pm b)) (F.ex_add _ _ (hper b))
      (HolHom.isHolTo_ex F _ (hper b))
    refine (F.ex_ker _ _ (hper b) _).1 (a4 _ (hker _ hb ex a1 a2 (fun jj => ?_) j))
    obtain ⟨w, w1, w2, w3⟩ := hm2 (e jj).1 (e jj).2
    have hd := hder b (e jj).1 (e jj).2
    rw [hx2, ← w2, Sigma.eta, Equiv.symm_apply_apply] at hd
    exact w3 ▸ a3 _ w w1 hd
  choose a ha using key
  have hxc : Continuous fun b : B => xx b :=
    (hxd.continuousOn.mono fun w hw => (hT₁ w hw).1).restrict
  have hPc : ∀ z, Continuous fun b : B => Pm b z := fun z => continuous_pi fun jj => by
    simp only [hPm]
    exact continuous_perFr _ hdom hxc _ _ _
  have hec : Continuous eTwoPi := by unfold eTwoPi; fun_prop
  let b₀ : B := ⟨(T₁ + 1 : ℝ) * Complex.I, by simp⟩
  have hconst : ∀ j b, a b j = a b₀ j := fun j b => by
    refine IsLocallyConstant.apply_eq_of_preconnectedSpace (f := fun b => a b j)
      ((IsLocallyConstant.iff_eventually_eq _).2 fun b' => ?_) b b₀
    refine eventually_eq_of_lattice Pm hPc b' (hper b').2.1 (hper b').2.2.1 (hper b').2.2.2.1 (fun b => a b j) ?_
    simp only [ha]
    exact (hcont j).comp_continuous (hec.comp continuous_subtype_val) fun b => (hT₁ b b.2).2
  have hlim : ∀ j jj, Tendsto (fun w => perFr (U.X k) (xx w) (φL k (a b₀ j) : Fin N → E) (relab c σ (e jj).1) (e jj).2)
      imTop (𝓝 (lam j 0 jj)) := fun j jj => by
    have h1 : Tendsto (fun w => lam j (eTwoPi w) jj) imTop (𝓝 (lam j 0 jj)) :=
      ((continuous_apply jj).tendsto _).comp
        ((((hcont j).continuousAt (Metric.ball_mem_nhds 0 hρ)).tendsto).comp tendsto_eTwoPi)
    refine h1.congr' ?_
    filter_upwards [(tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T₁)] with w hw
    rw [← ha ⟨w, hw⟩ j, hconst, hPm]
  have hidx : ∀ (τ : E →+* ℂ) (m : ℕ), m = (if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q) →
      ∃ s : Fin m → Fin g, Function.Injective s ∧ ∀ i, relab c σ (e (s i)).1 = τ ∧ ((e (s i)).2 : ℕ) = i := by
    intro τ m hmτ
    obtain ⟨τ', rfl⟩ := Finite.injective_iff_surjective.1 (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_injective c σ) τ
    have h1 : m = Dw.mult τ' := by
      rw [hmτ, Datum.mult]
      exact if_congr (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_rt c σ hσ τ') rfl rfl
    subst h1
    refine ⟨fun i => e.symm ⟨τ', i⟩, fun i i' h => ?_, fun i => ?_⟩
    · exact eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2
    · rw [Equiv.apply_symm_apply]
      exact ⟨rfl, rfl⟩
  choose sp hsp hsp' using fun τ : (U.X k).Ψ => hidx τ.1 (N - (U.X k).p0) (by
    rw [if_pos (((hX k).2 _).1 τ.2), (hX k).1, hN, Nat.add_sub_cancel])
  choose sm hsm hsm' using fun τ : (U.X k).Ψ => hidx (conjEmb τ.1) (U.X k).p0 (by
    rw [if_neg fun h => ((U.X k).cmType τ.1).1 τ.2 (((hX k).2 (conjEmb τ.1)).2 h), (hX k).1])
  refine ⟨n, fun j => φL k (a b₀ j), fun j τ i => lam j 0 (sp τ i), fun j τ i => lam j 0 (sm τ i), fun j τ i => ?_,
    fun j τ i => ?_, fun τ => ⟨span_proj _ hspan _ (hsp τ), span_proj _ hspan _ (hsm τ)⟩⟩
  · have := hlim j (sp τ i)
    rwa [(hsp' τ i).1, (hsp' τ i).2] at this
  · have := hlim j (sm τ i)
    rwa [(hsm' τ i).1, (hsm' τ i).2] at this

end GlobalTheory.ShFam.PerLim
