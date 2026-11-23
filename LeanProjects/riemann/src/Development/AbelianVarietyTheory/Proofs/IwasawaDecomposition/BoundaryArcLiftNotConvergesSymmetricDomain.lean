import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open scoped CommRingCat.HomTopology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc.Leave

theorem block_of_span_le {N p : ℕ} {M M' : Matrix (Fin N) (Fin N) ℂ} (hM : M.det ≠ 0)
    (h : Submodule.span ℂ (col M' '' {a | (a : ℕ) < p}) ≤ Submodule.span ℂ (col M '' {a | (a : ℕ) < p}))
    (a b : Fin N) (ha : p ≤ a) (hb : (b : ℕ) < p) : (M⁻¹ * M') a b = 0 := by
  let L : (Fin N → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj a).comp (Matrix.mulVecLin M⁻¹)
  have hL : ∀ (P : Matrix (Fin N) (Fin N) ℂ) (d : Fin N), L (col P d) = (M⁻¹ * P) a d := fun _ _ => rfl
  have h1 : Submodule.span ℂ (col M '' {a | (a : ℕ) < p}) ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    show L (col M d) = 0
    rw [hL, Matrix.nonsing_inv_mul _ hM.isUnit]
    exact Matrix.one_apply_ne fun e => absurd (show (d : ℕ) < p from hd) (by rw [← e]; omega)
  exact (hL M' b).symm.trans (h1 (h (Submodule.subset_span ⟨b, hb, rfl⟩)))

theorem imTop_neBot : imTop.NeBot :=
  Filter.comap_neBot fun t ht => by
    obtain ⟨a, ha⟩ := Filter.nonempty_of_mem ht
    exact ⟨a * Complex.I, by simpa using ha⟩

theorem tendsto_eTwoPi : Tendsto eTwoPi imTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : Tendsto (fun w : ℂ => Real.exp (-(2 * Real.pi * w.im))) imTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop (by positivity) tendsto_comap)
  refine h.congr fun w => ?_
  simp [eTwoPi, Complex.norm_exp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {N : ℕ} {U : Unf Xo c σ N}

theorem x_eq_of_samePos (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (x x' : (U.X k).dom)
    (h : SamePos (U.X k) x.1 x'.1) : (U.un k x).x = (U.un k x').x :=
  GlobalTheory.TrueCx.PointWell.pt_eq_of_block (U := Formalism.L2.PjFree.Unf.ofPj U) hU hσ k x x'
    (fun τ => block_of_span_le (x.2 τ).1 (h τ).ge) fun τ => block_of_span_le (x'.2 τ).1 (h τ).le

theorem isHolTo_ptC (hU : IsUnf U) (k : U.Comp) (s : Frame (U.X k).Ψ N → (U.X k).dom)
    (hs : ∀ x ∈ (U.X k).dom, (s x).1 = x) : IsHolTo (U.X k).dom fun x => GlobalTheory.TrueCx.ptC (U.un k (s x)) := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hun⟩ := hU
  choose P hP hP' hx _ using hun k
  let L : Frame (U.X k).Ψ N ≃L[ℂ] (Fin (Module.finrank ℂ (Frame (U.X k).Ψ N)) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp only [Module.finrank_fin_fun])
  have ho : IsOpen (U.X k).dom := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _
  have hB := ho.preimage L.symm.continuous
  have h1 := (F.hol (ik k) _ _ (fun b => P (s (L.symm b))) hB ⟨fun b _ => hP' _, fun a =>
    differentiableOn_pi.2 fun i => by
      simp only [hP]
      refine GlobalTheory.TrueCx.TorHolo.differentiableOn_perFr _ (fun b _ => (s _).2) (fun τ a d => ?_) _ _ _
      refine (differentiable_pi.1 (differentiable_pi.1 (differentiable_pi.1 L.symm.differentiable τ) a)
        d).differentiableOn.congr fun b hb => ?_
      rw [hs _ hb]
      rfl⟩).1
  have h2 : IsHolTo (L.symm ⁻¹' (U.X k).dom) fun b => GlobalTheory.TrueCx.ptC (U.un k (s (L.symm b))) := by
    refine GlobalTheory.TrueCx.TorHolo.isHolTo_of_fst _ _ hB _ (fun b => GlobalTheory.TrueCx.ptC_snd _) ?_
    simp only [GlobalTheory.TrueCx.ptC_fst]
    exact LocLift.isHolTo_congr h1 fun b _ => hx _
  refine LocLift.isHolTo_congr (LocLift.isHolTo_comp h2 ho L.differentiableOn fun v hv => ?_) fun v _ => ?_
  · rwa [Set.mem_preimage, L.symm_apply_apply]
  · rw [L.symm_apply_apply]

theorem lift_not_converges : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsBdArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsLift U k y T xx → ∀ x₀ ∈ (U.X k).dom, ∀ x' : ℂ → Frame (U.X k).Ψ N, Tendsto x' imTop (𝓝 x₀) → ¬ ∀ᶠ w in imTop, x' w ∈ (U.X k).dom ∧ SamePos (U.X k) (xx w) (x' w) := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T xx hσ hU ⟨⟨⟨hr, hψ⟩, hxs, hφ⟩, hb0, _⟩ hm hl x₀ hx₀ x' ht hev
  have := isProper_genStr Z
  have := imTop_neBot
  let s : Frame (U.X k).Ψ N → (U.X k).dom := fun v => if h : v ∈ (U.X k).dom then ⟨v, h⟩ else ⟨x₀, hx₀⟩
  have hs : ∀ v (h : v ∈ (U.X k).dom), s v = ⟨v, h⟩ := fun v h => dif_pos h
  let pt : Frame (U.X k).Ψ N → CxPts (genStr Z) σ := fun v =>
    ⟨GlobalTheory.TrueCx.ptC (U.un k (s v)) ≫ Z.jQ, by rw [Category.assoc, Z.jQ_over, GlobalTheory.TrueCx.ptC_snd]⟩
  have hc : ContinuousOn pt (U.X k).dom := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo
    (LocLift.isHolTo_comp_hom (isHolTo_ptC hU k s fun v h => by rw [hs v h]) Z.jQ)
  have h1 : Tendsto (fun w => pt (x' w)) imTop (𝓝 (pt x₀)) :=
    (hc.continuousAt ((ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _).mem_nhds hx₀)).tendsto.comp ht
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  let q : CxPts (genStr Z) σ := ⟨spMap (ψ 0) ≫ x, by
    rw [Category.assoc, hxs, ← hφ 0 h0, ← Spec.map_comp]; rfl⟩
  have ha : ContinuousAt (fun u => spMap (ψ u) ≫ x) 0 := by
    refine ((GlobalTheory.Points.continuous_comp x).comp
      (GlobalTheory.Points.continuous_specMap (C := ℂ) (CommRingCat.of A))).continuousAt.comp
      (f := fun u => CommRingCat.ofHom (ψ u)) ?_
    refine (CommRingCat.HomTopology.isEmbedding_hom _ _).isInducing.continuousAt_iff.2 (continuousAt_pi.2 fun a => ?_)
    exact ((hψ a).differentiableAt (Metric.isOpen_ball.mem_nhds h0)).continuousAt
  have h2 : Tendsto (fun w => pt (x' w)) imTop (𝓝 q) := by
    refine tendsto_subtype_rng.2 ((ha.tendsto.comp tendsto_eTwoPi).congr' ?_)
    filter_upwards [hev, tendsto_eTwoPi.eventually (Metric.isOpen_ball.mem_nhds h0),
      (tendsto_comap (f := Complex.im)).eventually (eventually_gt_atTop T)] with w hw hb hT
    obtain ⟨hd, he, -⟩ := hl w hT
    have e1 := (hm _ hb (Complex.exp_ne_zero _)).1
    have e2 : GlobalTheory.TrueCx.ptC (U.un k (s (x' w))) = GlobalTheory.TrueCx.ptC (y (eTwoPi w)) := by
      refine pullback.hom_ext ?_ ((GlobalTheory.TrueCx.ptC_snd _).trans (GlobalTheory.TrueCx.ptC_snd _).symm)
      rw [GlobalTheory.TrueCx.ptC_fst, GlobalTheory.TrueCx.ptC_fst, hs _ hw.1]
      exact (x_eq_of_samePos hσ hU k ⟨_, hd⟩ ⟨_, hw.1⟩ hw.2).symm.trans he
    exact e1.symm.trans (congrArg (· ≫ Z.jQ) e2.symm)
  have h3 : (pt x₀).1 = q.1 := congrArg Subtype.val (tendsto_nhds_unique h1 h2)
  refine mem_genBd.1 (hb0 (IsLocalRing.closedPoint ℂ)) ⟨GlobalTheory.TrueCx.ptC (U.un k (s x₀)) (IsLocalRing.closedPoint ℂ), ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun f : Sp ℂ ⟶ gen Z => f (IsLocalRing.closedPoint ℂ)) h3)

end GlobalTheory.ShFam.BdArc.Leave
