import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianExponentialAlongDisc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAnalyticParamInverse
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRelativeExpOfParts

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open GlobalTheory.RelExp GlobalTheory.VerticalDeriv GlobalTheory.FibreDeriv
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh.KerFam

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

theorem isOpen_ne_one [IsSeparated G.hom] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {D : Set V}
    (hD : IsOpen D) {y : V → (Sp ℂ ⟶ X)} (a : ∀ q, Over.mk (y q) ⟶ G) (hy : ∀ q ∈ D, HolAt y q)
    (ha : ∀ q ∈ D, HolAt (Z := G.left) (fun q => (a q).left) q) : IsOpen {q | q ∈ D ∧ a q ≠ 1} := by
  let c : V → (Sp ℂ ⟶ pullback G.hom G.hom) := fun q =>
    pullback.lift (a q).left (1 : Over.mk (y q) ⟶ G).left
      ((Over.w (a q)).trans (Over.w (1 : Over.mk (y q) ⟶ G)).symm)
  have hc : IsHolTo D c := isHolTo_of_holAt hD fun q hq =>
    holAt_of_isPullback (IsPullback.of_hasPullback G.hom G.hom)
      (by simpa only [c, pullback.lift_fst] using ha q hq)
      (by simpa only [c, pullback.lift_snd] using HolAt.one (G := G) (hy q hq))
  have hcont : Continuous fun q : D => c q := by
    refine Points.continuous_iff_valAt'.2 fun U => ⟨?_, fun f => ?_⟩
    · have : IsOpen ((fun q : D => (q : V)) ⁻¹' {b ∈ D | ⊤ ≤ c b ⁻¹ᵁ U}) :=
        (hc U 0).1.preimage continuous_subtype_val
      convert this using 1
      ext q
      simp [q.2]
    · have h := (hc U f).2.continuousOn.comp (f := fun q : D => (q : V)) continuous_subtype_val.continuousOn
        (t := {b ∈ D | ⊤ ≤ c b ⁻¹ᵁ U}) (s := {b : D | ⊤ ≤ c b ⁻¹ᵁ U}) fun q hq => ⟨q.2, hq⟩
      exact h
  have hR := (Points.isClosedEmbedding_comp (C := ℂ) (pullback.diagonal G.hom)).isClosed_range
  have hop : IsOpen ((fun q : D => c q) ⁻¹' (Set.range fun x : Sp ℂ ⟶ G.left => x ≫ pullback.diagonal G.hom)ᶜ) :=
    hR.isOpen_compl.preimage hcont
  have := hD.isOpenMap_subtype_val _ hop
  convert this using 1
  ext q
  constructor
  · rintro ⟨hq, hne⟩
    refine ⟨⟨q, hq⟩, ?_, rfl⟩
    rintro ⟨x, hx⟩
    refine hne (Over.OverMorphism.ext ?_)
    have h1 := congrArg (· ≫ pullback.fst G.hom G.hom) hx
    have h2 := congrArg (· ≫ pullback.snd G.hom G.hom) hx
    simp only [c, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd] at h1 h2
    exact h1.symm.trans h2
  · rintro ⟨⟨q', hq'⟩, hne, rfl⟩
    refine ⟨hq', fun h => hne ⟨(a q').left, ?_⟩⟩
    show (a q').left ≫ pullback.diagonal G.hom = c q'
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      exact (congrArg Over.Hom.left h).trans (pullback.lift_snd _ _ _).symm

theorem exists_analytic_zero_graph {m g g' : ℕ} {F : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g' → ℂ)} {b₀ : Fin m → ℂ}
    (hF : AnalyticAt ℂ F (b₀, 0)) (h0 : F (b₀, 0) = 0)
    (hT : Function.Bijective (fderiv ℂ (fun u => F (b₀, u)) 0)) :
    ∃ ξ : (Fin m → ℂ) → (Fin g → ℂ), ξ b₀ = 0 ∧ AnalyticAt ℂ ξ b₀ ∧
      ∀ᶠ p : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), F p = 0 ↔ p.2 = ξ p.1 := by
  let Φ : (Fin m → ℂ) × (Fin g → ℂ) → (Fin m → ℂ) × (Fin g' → ℂ) := fun p => (p.1, F p)
  have hΦ : AnalyticAt ℂ Φ (b₀, 0) := analyticAt_fst.prod hF
  have hD := hF.differentiableAt.hasFDerivAt
  set D := fderiv ℂ F (b₀, 0) with hDdef
  have hTD : fderiv ℂ (fun u => F (b₀, u)) 0 = D.comp (ContinuousLinearMap.inr ℂ _ _) :=
    (HasFDerivAt.comp (f := fun u : Fin g → ℂ => (b₀, u)) (0 : Fin g → ℂ) hD
      (hasFDerivAt_prodMk_right b₀ 0)).fderiv
  let Φ' : ((Fin m → ℂ) × (Fin g → ℂ)) →L[ℂ] ((Fin m → ℂ) × (Fin g' → ℂ)) :=
    (ContinuousLinearMap.fst ℂ _ _).prod D
  have hsplit : ∀ p : (Fin m → ℂ) × (Fin g → ℂ), D p = D (p.1, 0) + fderiv ℂ (fun u => F (b₀, u)) 0 p.2 := fun p => by
    rw [hTD, ContinuousLinearMap.comp_apply, ← map_add]
    simp
  have hbij : Function.Bijective Φ' := by
    constructor
    · intro p p' h
      have h1 : p.1 = p'.1 := show (Φ' p).1 = (Φ' p').1 by rw [h]
      have h2 : D p = D p' := show (Φ' p).2 = (Φ' p').2 by rw [h]
      rw [hsplit p, hsplit p', h1] at h2
      exact Prod.ext h1 (hT.1 (add_left_cancel h2))
    · rintro ⟨b, c⟩
      obtain ⟨u, hu⟩ := hT.2 (c - D (b, 0))
      refine ⟨(b, u), Prod.ext rfl ?_⟩
      show D (b, u) = c
      rw [hsplit, hu]
      simp
  let f' : ((Fin m → ℂ) × (Fin g → ℂ)) ≃L[ℂ] ((Fin m → ℂ) × (Fin g' → ℂ)) :=
    (LinearEquiv.ofBijective (Φ' : _ →ₗ[ℂ] _) hbij).toContinuousLinearEquiv
  have hd : HasFDerivAt Φ (f' : _ →L[ℂ] _) (b₀, 0) := by
    have : (f' : ((Fin m → ℂ) × (Fin g → ℂ)) →L[ℂ] _) = Φ' := ContinuousLinearMap.ext fun _ => rfl
    rw [this]
    exact hasFDerivAt_fst.prodMk hD
  have hc : ContDiffAt ℂ ⊤ Φ (b₀, 0) := hΦ.contDiffAt
  have hinv := hc.to_localInverse hd (by simp)
  have hs := hc.hasStrictFDerivAt' hd (by simp)
  set R := hc.localInverse hd (by simp) with hR
  have hΦ0 : Φ (b₀, 0) = (b₀, 0) := Prod.ext rfl h0
  have h1 : ∀ᶠ w in 𝓝 (Φ (b₀, 0)), Φ (R w) = w := hs.eventually_right_inverse
  have h2 : ∀ᶠ p in 𝓝 ((b₀, 0) : (Fin m → ℂ) × (Fin g → ℂ)), R (Φ p) = p := hs.eventually_left_inverse
  have hR0 : R (b₀, 0) = (b₀, 0) := by
    have := h2.self_of_nhds
    rwa [hΦ0] at this
  rw [hΦ0] at h1
  have hcur : Filter.Tendsto (fun b : Fin m → ℂ => (b, (0 : Fin g' → ℂ))) (𝓝 b₀) (𝓝 (b₀, 0)) :=
    (continuous_id.prodMk continuous_const).tendsto b₀
  have hcb : ∀ᶠ b in 𝓝 b₀, Φ (R (b, 0)) = (b, 0) := hcur.eventually h1
  have hRa : AnalyticAt ℂ R (b₀, 0) := by
    have := hinv.analyticAt
    rwa [hΦ0] at this
  refine ⟨fun b => (R (b, 0)).2, by simp only [hR0], ?_, ?_⟩
  · have : AnalyticAt ℂ (fun b : Fin m → ℂ => R (b, 0)) b₀ :=
      AnalyticAt.comp (g := R) (f := fun b : Fin m → ℂ => (b, (0 : Fin g' → ℂ))) hRa
        (analyticAt_id.prod analyticAt_const)
    exact AnalyticAt.comp (g := Prod.snd) analyticAt_snd this
  · have hfst : Filter.Tendsto (Prod.fst : (Fin m → ℂ) × (Fin g → ℂ) → (Fin m → ℂ)) (𝓝 (b₀, 0)) (𝓝 b₀) :=
      continuous_fst.tendsto _
    filter_upwards [h2, hfst.eventually hcb] with p hp1 hp2
    constructor
    · intro hF0
      have : Φ p = (p.1, 0) := Prod.ext rfl hF0
      rw [this] at hp1
      exact (congrArg (fun r : (Fin m → ℂ) × (Fin g → ℂ) => r.2) hp1).symm
    · intro hξ
      have h4 : (R (p.1, 0)).1 = p.1 := show (Φ (R (p.1, 0))).1 = p.1 by rw [hp2]
      have h5 : F (R (p.1, 0)) = 0 := show (Φ (R (p.1, 0))).2 = 0 by rw [hp2]
      have h6 : R (p.1, 0) = p := Prod.ext h4 hξ.symm
      rwa [h6] at h5

theorem bijective_fderiv {x : Sp ℂ ⟶ X} {g g' : ℕ} {e : (Fin g → ℂ) → (Over.mk x ⟶ G)}
    {e' : (Fin g' → ℂ) → (Over.mk x ⟶ G)} (hol : IsHolTo Set.univ fun z => (e z).left)
    (hol' : IsHolTo Set.univ fun z => (e' z).left) (h0 : e 0 = 1) (h0' : e' 0 = 1)
    (h3 : ∀ v : Sp (DualNumber ℂ) ⟶ G.left, v ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = (1 : Over.mk x ⟶ G).left →
      ∃! w, IsDerivAt0 (fun u => (e u).left) w v)
    {U : G.left.Opens} (t : Fin g' → Γ(G.left, U)) (hU : ⊤ ≤ (1 : Over.mk x ⟶ G).left ⁻¹ᵁ U)
    (hun : ∀ (v v' : Sp (DualNumber ℂ) ⟶ G.left) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ G.hom = v' ≫ G.hom →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' →
      (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v')
    (hd : HasFDerivAt (fun z i => valAt' (e' z).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g' → ℂ)) 0) :
    Function.Bijective (fderiv ℂ (fun z i => valAt' (e z).left U (t i)) 0) := by
  have he : ∀ z, (show Sp ℂ ⟶ G.left from (e z).left) ≫ G.hom = x := fun z => Over.w (e z)
  have he' : ∀ z, (show Sp ℂ ⟶ G.left from (e' z).left) ≫ G.hom = x := fun z => Over.w (e' z)
  have hU0 : ⊤ ≤ (show Sp ℂ ⟶ G.left from (e 0).left) ⁻¹ᵁ U := by rw [h0]; exact hU
  have hU0' : ⊤ ≤ (show Sp ℂ ⟶ G.left from (e' 0).left) ⁻¹ᵁ U := by rw [h0']; exact hU
  constructor
  · intro w w' hw
    obtain ⟨v, Hv⟩ := exists_isDerivAt0 hol w
    obtain ⟨v', Hv'⟩ := exists_isDerivAt0 hol w'
    have h := (top_le_preimage_eps v _ Hv.1 U).2 hU0
    have h' := (top_le_preimage_eps v' _ Hv'.1 U).2 hU0
    have hv := isDerivAt0_vertical G.hom x he Hv
    have hv' := isDerivAt0_vertical G.hom x he Hv'
    have hvv : v = v' := hun v v' h h' (hv.trans hv'.symm) (Hv.1.trans Hv'.1.symm) fun i => by
      refine TrivSqZeroExt.ext ((fst_evEps v _ Hv.1 U h _).trans (fst_evEps v' _ Hv'.1 U h' _).symm) ?_
      rw [isDerivAt0_snd hol t hU0 Hv h i, isDerivAt0_snd hol t hU0 Hv' h' i, hw]
    subst hvv
    exact (h3 v hv (Hv.1.trans (congrArg Over.Hom.left h0))).unique Hv Hv'
  · intro c
    obtain ⟨v, Hv⟩ := exists_isDerivAt0 hol' c
    have h := (top_le_preimage_eps v _ Hv.1 U).2 hU0'
    have hv := isDerivAt0_vertical G.hom x he' Hv
    obtain ⟨w, Hw, -⟩ := h3 v hv (Hv.1.trans (congrArg Over.Hom.left h0'))
    refine ⟨w, funext fun i => ?_⟩
    have h1 := isDerivAt0_snd hol t hU0 Hw h i
    have h2 := isDerivAt0_snd hol' t hU0' Hv h i
    rw [hd.fderiv] at h2
    exact h1.symm.trans h2

theorem exists_graph [IsCommMonObj G] (hsm : Smooth G.hom) (hcon : GeometricallyConnected G.hom) {m g : ℕ}
    {B : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} (ex : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G))
    (hB : IsOpen B) (hy : IsHolTo B y)
    (hex : IsHolTo (B ×ˢ (Set.univ : Set (Fin g → ℂ))) fun q : (Fin m → ℂ) × (Fin g → ℂ) => (ex q.1 q.2).left)
    {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) {w₀ : Fin g → ℂ} (hw₀ : ex b₀ w₀ = 1)
    (hadd : ∀ v w, ex b₀ (v + w) = ex b₀ v * ex b₀ w)
    (h3 : ∀ v : Sp (DualNumber ℂ) ⟶ G.left, v ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y b₀ →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = (1 : Over.mk (y b₀) ⟶ G).left →
      ∃! w, IsDerivAt0 (fun u => (ex b₀ u).left) w v) :
    ∃ ζ : (Fin m → ℂ) → Fin g → ℂ, ζ b₀ = w₀ ∧ AnalyticAt ℂ ζ b₀ ∧
      ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, w₀), ex q.1 q.2 = 1 ↔ q.2 = ζ q.1 := by
  have hy₀ : HolAt y b₀ := ⟨B, hB, hb₀, hy⟩
  obtain ⟨g', U, t, n, f, N, O, σ, hN, hO, hU, hO₀, hσ, hσN, hσinv, hunr⟩ :=
    RelExp.exists_chart_of_smooth m G.left X G.hom B y b₀ (pt (1 : Over.mk (y b₀) ⟶ G)) hB hb₀ hy (Over.w _)
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_centred_chart hy₀ hN hU hO₀ hσ hσN hσinv
  obtain ⟨B', e, r, Q, L, hB', hb', hB'B, hr, hQ, hadd', hfib, hinv⟩ :=
    exists_global_exp exists_param_exp_log_pi (hB.mem_nhds hb₀) hy₀ hO hU hO₀ hs1 hs2 hs3
  obtain ⟨k1, -, -, -, k5, -⟩ := hfib b₀ hb'
  have hzero : ex b₀ 0 = 1 := UnifPoint.map_zero_of_add hadd
  have hzero' : e b₀ 0 = 1 := UnifPoint.map_zero_of_add (hadd' b₀)
  have hD : (B ×ˢ (Set.univ : Set (Fin g → ℂ))) ∈ 𝓝 (b₀, w₀) :=
    (hB.prod isOpen_univ).mem_nhds ⟨hb₀, trivial⟩
  have holAtEx : ∀ w, HolAt (Z := G.left) (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (ex q.1 q.2).left) (b₀, w) :=
    fun w => ⟨_, hB.prod isOpen_univ, ⟨hb₀, trivial⟩, hex⟩
  have hol : IsHolTo Set.univ fun z => (ex b₀ z).left := isHolTo_of_holAt isOpen_univ fun z _ => by
    have := HolAt.comp (φ := fun z : Fin g → ℂ => (b₀, z)) (v₀ := z) (holAtEx z) (analyticAt_const.prod analyticAt_id)
    exact this
  have hol' : IsHolTo Set.univ fun z => (e b₀ z).left := isHolTo_of_holAt isOpen_univ fun z _ => by
    have := HolAt.comp (φ := fun z : Fin g' → ℂ => (b₀, z)) (v₀ := z) (k1 z) (analyticAt_const.prod analyticAt_id)
    exact this
  have hT := bijective_fderiv hol hol' hzero hzero' h3 t hU hunr k5
  let a : ∀ q : (Fin m → ℂ) × (Fin g → ℂ), Over.mk (y q.1) ⟶ G := fun q => ex q.1 (w₀ + q.2)
  have ha : HolAt (Z := G.left) (fun q => (a q).left) (b₀, 0) := by
    have := HolAt.comp (φ := fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, w₀ + q.2)) (v₀ := (b₀, 0)) (holAtEx (w₀ + 0))
      (analyticAt_fst.prod (analyticAt_const.add analyticAt_snd))
    exact this
  have ha1 : a (b₀, 0) = 1 := by
    show ex b₀ (w₀ + 0) = 1
    rw [add_zero, hw₀]
  have hF := HolAt.analyticAt_coordinate_zero (β := Prod.fst) (a := a) (t := t) ha ha1 hU
  have hF0 : crd0 t (a (b₀, 0)) = 0 := by rw [ha1]; exact sub_self _
  have hfd : fderiv ℂ (fun u => crd0 t (a (b₀, u))) 0 = fderiv ℂ (fun z i => valAt' (ex b₀ z).left U (t i)) 0 := by
    have : (fun u => crd0 t (a (b₀, u))) =
        fun u => (fun i => valAt' (ex b₀ u).left U (t i)) - crd U t (pt (1 : Over.mk (y b₀) ⟶ G)) := by
      funext u
      have : a (b₀, u) = ex b₀ u := by
        show ex b₀ (w₀ + u) = _
        rw [hadd, hw₀, _root_.one_mul]
      rw [this]
    rw [this]
    exact fderiv_sub_const _
  obtain ⟨ξ, hξ0, hξ, hev⟩ := exists_analytic_zero_graph (F := fun q => crd0 t (a q)) hF hF0 (hfd ▸ hT)
  refine ⟨fun b => w₀ + ξ b, by simp only [hξ0, add_zero], analyticAt_const.add hξ, ?_⟩
  have hP : Filter.Tendsto (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, q.2 - w₀)) (𝓝 (b₀, w₀)) (𝓝 (b₀, 0)) := by
    have : Continuous fun q : (Fin m → ℂ) × (Fin g → ℂ) => (q.1, q.2 - w₀) := by fun_prop
    simpa using this.tendsto (b₀, w₀)
  have hfst : Filter.Tendsto (Prod.fst : (Fin m → ℂ) × (Fin g → ℂ) → (Fin m → ℂ)) (𝓝 (b₀, w₀)) (𝓝 b₀) :=
    continuous_fst.tendsto _
  have hn1 := hP.eventually (HolAt.eventually_near (β := Prod.fst) (a := a) (f := f) (O := O) ha
    continuousAt_fst ha1 hO hU hO₀)
  have hn2 := hfst.eventually (HolAt.eventually_near (β := fun b => b)
    (a := fun b => (1 : Over.mk (y b) ⟶ G)) (f := f) (O := O) (HolAt.one hy₀) continuousAt_id rfl hO hU hO₀)
  filter_upwards [hP.eventually hev, hn1, hn2] with q h1 h2 h4
  have hq : a (q.1, q.2 - w₀) = ex q.1 q.2 := by
    show ex q.1 (w₀ + (q.2 - w₀)) = _
    rw [add_sub_cancel]
  simp only [hq] at h1 h2
  rw [← sub_eq_iff_eq_add', ← h1]
  constructor
  · intro h
    rw [h]
    exact sub_self _
  · intro h
    have h5 : crd U t (pt (ex q.1 q.2)) = crd U t (pt (1 : Over.mk (y q.1) ⟶ G)) := sub_eq_zero.1 h
    have h6 := (hσinv q.1 _ (Over.w (ex q.1 q.2)) h2.1 h2.2).2
    have h7 := (hσinv q.1 _ (Over.w (1 : Over.mk (y q.1) ⟶ G)) h4.1 h4.2).2
    refine Over.OverMorphism.ext (h6.symm.trans ?_)
    have h8 : (fun i => valAt' (ex q.1 q.2).left U (t i)) = fun i => valAt' (1 : Over.mk (y q.1) ⟶ G).left U (t i) := h5
    rw [h8]
    exact h7

end GlobalTheory.ShFam.Hor.LogCh.KerFam

namespace GlobalTheory.ShFam.Hor.LogCh

open KerFam

theorem isLatFam_ker : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (m g : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (ex : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ t.G)), IsOpen B → IsHolTo (B ×ˢ Set.univ) (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (ex q.1 q.2).left) → (∀ b ∈ B, IsExpAt t (y b) (ex b)) → IsLatFam B (fun b => {w | ex b w = 1}) := by
  intro E _ _ _ H X t m g B y ex hB hex hE
  have := t.semi.separated
  have hD := hB.prod (isOpen_univ (X := Fin g → ℂ))
  have holAtEx : ∀ q ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)),
      HolAt (Z := t.G.left) (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (ex q.1 q.2).left) q :=
    fun q hq => ⟨_, hD, hq, hex⟩
  have hzero : ∀ b ∈ B, ex b 0 = 1 := fun b hb => UnifPoint.map_zero_of_add (hE b hb).1
  have hy : IsHolTo B y := isHolTo_of_holAt hB fun b hb => by
    have h1 := HolAt.comp (φ := fun b : Fin m → ℂ => (b, (0 : Fin g → ℂ))) (v₀ := b)
      (holAtEx (b, 0) ⟨hb, trivial⟩) (analyticAt_id.prod analyticAt_const)
    exact (h1.post t.G.hom).congr (Filter.Eventually.of_forall fun b => Over.w (ex b 0))
  refine ⟨hB, fun b hb => ?_, ?_, fun b₀ hb₀ w₀ hw₀ => ?_⟩
  · have hadd := (hE b hb).1
    refine ⟨{ carrier := {w | ex b w = 1}, add_mem' := fun {u v} hu hv => ?_, zero_mem' := hzero b hb,
              neg_mem' := fun {u} hu => ?_ }, rfl⟩
    · show ex b (u + v) = 1
      rw [hadd, show ex b u = 1 from hu, show ex b v = 1 from hv, _root_.one_mul]
    · show ex b (-u) = 1
      have h := hadd (-u) u
      rw [neg_add_cancel, hzero b hb, show ex b u = 1 from hu, _root_.mul_one] at h
      exact h.symm
  · have h := isOpen_ne_one hD (y := fun q : (Fin m → ℂ) × (Fin g → ℂ) => y q.1) (fun q => ex q.1 q.2)
      (fun q hq => by
        have := HolAt.comp (a := y) (φ := Prod.fst) (v₀ := q) ⟨B, hB, hq.1, hy⟩ analyticAt_fst
        exact this) holAtEx
    refine (congrArg IsOpen (Set.ext fun q => ?_)).mpr h
    exact ⟨fun hq => ⟨⟨hq.1, trivial⟩, hq.2⟩, fun hq => ⟨hq.1.1, hq.2⟩⟩
  · obtain ⟨ζ, h1, h2, h3⟩ := exists_graph t.semi.smooth t.semi.geomConnected ex hB hy hex hb₀ hw₀ (hE b₀ hb₀).1
      fun v hv hv' => (hE b₀ hb₀).2.2 v ⟨hv, hv'⟩
    exact ⟨ζ, h1, h2, h3⟩

end GlobalTheory.ShFam.Hor.LogCh
