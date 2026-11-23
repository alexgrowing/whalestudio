import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralMultipleExtensionStatement
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false
noncomputable section
open GlobalTheory.CxPts
open scoped ContDiff

namespace GlobalTheory.Mean4O.OnModelCInf

theorem cInfAt_of_manIs {F : Type} [Field F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y)
    {u : M.Fun} (hu : M.Smooth u) (a : Fin (M.n + 1)) (y : Pts Y (I.ε a)) :
    CInfAt (fun w => u a ((I.pt a).symm w)) y := by
  obtain ⟨j, hj⟩ := (M.A a).cover ((I.pt a).symm y)
  obtain ⟨c, hc⟩ := I.alg a j
  have h := hu a j
  rw [hc, Homeomorph.transOpenPartialHomeomorph_symm_apply, Homeomorph.transOpenPartialHomeomorph_target] at h
  rw [hc, Homeomorph.transOpenPartialHomeomorph_source] at hj
  have h' : ContDiffOn ℝ ∞ ((fun w => u a ((I.pt a).symm w)) ∘ c.finChart.symm)
      (c.finChart.target ∩ c.finChart.symm ⁻¹' Set.univ) := by
    simpa [Function.comp_def] using h
  refine cInfAt_of_chart isOpen_univ c ((c.contDiffOn_finChart_iff _ _ _).1 h') ?_ trivial
  simpa using hj

theorem baseChange_cInfAt : ∀ (F : Type) [Field F] [NumberField F] (X G : Scheme.{0}) (p : X ⟶ Sp (𝓞 F))
    (q : G ⟶ Sp F) (j : G ⟶ X), IsPullback j q p (spMap (algebraMap (𝓞 F) F)) →
    ∀ (τ : F →+* ℂ) (σ : 𝓞 F →+* ℂ) (m : CxPts q τ → CxPts p σ), (∀ z, (m z).1 = z.1 ≫ j) →
    ∀ (f : CxPts p σ → ℝ) (z : CxPts q τ), CInfAt (fun w => f (m w)) z → CInfAt f (m z) := by
  intro F _ _ X G p q j H τ σ m hm f z hz
  obtain ⟨W, ι, _, g, Φ, O, h₁, h₂, h₃, h₄, h₅⟩ := hz
  obtain ⟨W', hle, hx, n, g', hn, hg⟩ := GlobalTheory.T.exists_integral_multiple_extension F X G p q j H W _ (mem_ptsIn.1 h₁) ι g
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hval (w : CxPts q τ) (hw : w ∈ ptsIn q τ (j ⁻¹ᵁ W')) (a : ι) :
      ev p σ W' (g' a) (m w) = n * ev q τ W (g a) w := by
    rw [ev_of_comp hm, ← hg a, ev_mul, ev_res hle hw]
    congr 1
    rw [ev_eq hw, map_natCast]
  have hστ : spMap σ = spMap τ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← (m z).2, hm, Category.assoc, H.w, ← Category.assoc, z.2]
  let s : CxPts p σ → CxPts q τ := fun y => ⟨H.lift y.1 (spMap τ) (y.2.trans hστ), H.lift_snd _ _ _⟩
  have hms (y : CxPts p σ) : m (s y) = y := Subtype.ext ((hm _).trans (H.lift_fst _ _ _))
  have hsm : s (m z) = z := Subtype.ext (H.hom_ext ((H.lift_fst _ _ _).trans (hm z))
    ((H.lift_snd _ _ _).trans z.2.symm))
  have hs : Continuous s := by
    refine Continuous.subtype_mk ?_ _
    rw [(Points.isEmbedding_of_isPullback H).continuous_iff]
    refine (continuous_subtype_val.prodMk (continuous_const (y := spMap τ))).congr fun y => ?_
    exact (Prod.ext (H.lift_fst _ _ _) (H.lift_snd _ _ _)).symm
  have hz' : z ∈ ptsIn q τ (j ⁻¹ᵁ W') := mem_ptsIn.2 hx
  have hmW : m z ∈ ptsIn p σ W' := by
    rw [mem_ptsIn, hm]
    exact hx
  have hd : ContDiff ℝ ∞ fun v : ι → ℂ => fun a => v a / (n : ℂ) :=
    contDiff_pi.2 fun a => (contDiff_apply ℝ ℂ a).div_const _
  refine ⟨W', ι, inferInstance, g', fun v => Φ fun a => v a / n, (fun v : ι → ℂ => fun a => v a / (n : ℂ)) ⁻¹' O,
    hmW, h₂.preimage hd.continuous, ?_, h₄.comp hd.contDiffOn fun v hv => hv, ?_⟩
  · show (fun a => ev p σ W' (g' a) (m z) / n) ∈ O
    simpa only [hval z hz', mul_div_cancel_left₀ _ hn'] using h₃
  · have ht : Filter.Tendsto s (nhds (m z)) (nhds z) := by
      have := hs.continuousAt (x := m z)
      rwa [ContinuousAt, hsm] at this
    filter_upwards [ht.eventually h₅, ht.eventually ((isOpen_ptsIn _).mem_nhds hz')] with y e hy
    have hv (a : ι) : ev p σ W' (g' a) y = n * ev q τ W (g a) (s y) := by
      have := hval (s y) hy a
      rwa [hms] at this
    calc f y = f (m (s y)) := by rw [hms]
      _ = Φ (fun a => ev q τ W (g a) (s y)) := e
      _ = Φ (fun a => ev p σ W' (g' a) y / n) := by
        congr 1
        funext a
        rw [hv, mul_div_cancel_left₀ _ hn']

theorem cInfAt_pull : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), V.IsDown I ε π → ∀ u : M.Fun, M.Smooth u → ∀ σ (z : CxPts V.p σ), CxPts.CInfAt (M.pull ε π u σ) z := by
  intro F _ _ Y V e M I ε π hD u hu σ z
  obtain ⟨hσ, hw⟩ := hD σ
  have hm0 (w : CxPts (V.π ≫ Y.str) (I.ε (ε σ))) : (w.1 ≫ V.j) ≫ V.p = spMap σ := by
    rw [Category.assoc, V.pb.w, ← Category.assoc, w.2, show spMap σ = _ from congrArg spMap hσ.symm, spMap, spMap, spMap,
      ← Spec.map_comp]
    rfl
  let m : CxPts (V.π ≫ Y.str) (I.ε (ε σ)) → CxPts V.p σ := fun w => ⟨w.1 ≫ V.j, hm0 w⟩
  obtain ⟨w, hw1, hw2⟩ := hw z
  let z' : CxPts (V.π ≫ Y.str) (I.ε (ε σ)) := ⟨w, by rw [← Category.assoc, hw2]; exact (I.pt _ (π σ z)).2⟩
  have hz : m z' = z := Subtype.ext hw1
  have key (w' : CxPts (V.π ≫ Y.str) (I.ε (ε σ))) : M.pull ε π u σ (m w') =
      u (ε σ) ((I.pt (ε σ)).symm (Points.PtsOver.map V.π rfl _ w')) := by
    obtain ⟨w'', h1, h2⟩ := hw (m w')
    have e : w'' = w'.1 := V.pb.hom_ext h1 (by
      rw [← Category.assoc, h2, (I.pt _ (π σ (m w'))).2]
      exact w'.2.symm)
    show u (ε σ) (π σ (m w')) = _
    congr 1
    apply (I.pt (ε σ)).injective
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext (h2.symm.trans (by rw [e]; rfl))
  have hY := CInfAt.pull V.π rfl (cInfAt_of_manIs I hu (ε σ) (Points.PtsOver.map V.π rfl _ z'))
  rw [← hz]
  exact baseChange_cInfAt F V.X V.G V.p (V.π ≫ Y.str) V.j V.pb _ σ m (fun _ => rfl) _ z'
    (hY.congr (.of_forall key))

end GlobalTheory.Mean4O.OnModelCInf
