import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianExponentialAlongDiscStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
open GlobalTheory.HolHom GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.ShFam.BdArc.LatSec

theorem isDerivAt_comp_iff {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V']
    [NormedSpace ℂ V'] {X : Scheme.{0}} {c : V → (Sp ℂ ⟶ X)} (h : HolAt c 0) (L : V' →L[ℂ] V) (w : V')
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt (fun t => c (L t)) 0 w v ↔ IsDerivAt c 0 (L w) v := by
  simp only [IsDerivAt, map_zero]
  refine and_congr_right fun _ => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_
  have h1 : HasFDerivAt (fun t => valAt' (c t) U f) (fderiv ℂ (fun t => valAt' (c t) U f) 0) (L 0) := by
    rw [map_zero]; exact ((h U hU).2 f).hasFDerivAt
  have h2 : fderiv ℂ (fun t => valAt' (c (L t)) U f) 0 w = fderiv ℂ (fun t => valAt' (c t) U f) 0 (L w) :=
    congrArg (· w) (h1.comp 0 L.hasFDerivAt).fderiv
  rw [h2]

theorem isDerivAt_smul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {c : V → (Sp ℂ ⟶ X)}
    {z w : V} {v : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt c z w v) (a : ℂ) :
    IsDerivAt c z (a • w) (spMap (epsMul a) ≫ v) := by
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [← h.1, ← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun x => by simp [epsMul])
  · rw [valR_spMap _ _ _ ((le_preimage_dual_iff h.1 U).2 hU), map_smul, ← h.2 U hU f]
    simp [epsMul]

theorem isDerivAt_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S : Scheme.{0}} {G : Over S} [GrpObj G]
    {y : Sp ℂ ⟶ S} {e : V → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w)
    (hol : HolAt (fun z => (e z).left) 0) {w w' : V} {v v' : epsPt y ⟶ G}
    (hv : IsDerivAt (fun z => (e z).left) 0 w v.left) (hv' : IsDerivAt (fun z => (e z).left) 0 w' v'.left) :
    IsDerivAt (fun z => (e z).left) 0 (w + w') (v * v').left := by
  have hl : ∀ L : V × V →L[ℂ] V, HolAt (fun t => (e (L t)).left) 0 := fun L =>
    HolAt.precomp (c := fun z => (e z).left) (by rw [map_zero]; exact hol) L.differentiableAt
  have h1 := (isDerivAt_comp_iff hol (ContinuousLinearMap.fst ℂ V V) (w, w') _).2 hv
  have h2 := (isDerivAt_comp_iff hol (ContinuousLinearMap.snd ℂ V V) (w, w') _).2 hv'
  have h3 := isDerivAt_mul (hl _) (hl _) h1 h2
  simp only [← he] at h3
  exact (isDerivAt_comp_iff hol (ContinuousLinearMap.fst ℂ V V + ContinuousLinearMap.snd ℂ V V) (w, w') _).1 h3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_lieEquiv {X : Scheme.{0}} (t : SAB H X) {y : Sp ℂ ⟶ X} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)}
    (he : ∀ z w, e (z + w) = e z * e w) (hol : HolAt (fun z => (e z).left) 0)
    (hdiff : ∀ v : epsPt y ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) :
    ∃ D : (Fin g → ℂ) ≃ₗ[ℂ] TanM y t.G, ∀ w, IsDerivAt (fun z => (e z).left) 0 w (tv (D w)).left := by
  have h0 : e 0 = 1 := map_zero_eq_one he
  choose d hd using hol.exists_isDerivAt
  let D : (Fin g → ℂ) →ₗ[ℂ] TanM y t.G :=
    { toFun := fun w => tanOf (t := t) ⟨(hd w).over, (hd w).1.trans (congrArg (·.left) h0)⟩
      map_add' := fun w w' => tan_ext ((hd _).unique (isDerivAt_add he hol (hd w) (hd w')))
      map_smul' := fun a w => tan_ext ((hd _).unique (isDerivAt_smul (hd w) a)) }
  have hu := fun v : TanM y t.G => hdiff (tv v) ((isTan_tv v).2.trans (congrArg (·.left) h0.symm))
  simp only [isDerivAt0_iff] at hu
  refine ⟨LinearEquiv.ofBijective D ⟨fun w w' h => (hu (D w)).unique (hd w) (by rw [h]; exact hd w'), fun v => ?_⟩, hd⟩
  obtain ⟨w, hw, -⟩ := hu v
  exact ⟨w, tan_ext ((hd w).unique hw)⟩

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β}

theorem exists_basis {σ : c.F →+* ℂ} {y : Sp ℂ ⟶ Z.X} (f : EigFrame Z σ y) :
    ∃ b : Module.Basis (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ℂ (TanM y Z.t.G), ∀ p, b p = f.vec p.1 p.2 := by
  classical
  have hinj : Function.Injective fun τ : E →+* ℂ => σ.comp (embF c τ) := fun τ τ' h =>
    RingHom.ext fun a => congrArg Subtype.val (σ.injective (RingHom.congr_fun h a))
  let π := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
  let χ : (E →+* ℂ) → (𝓞 E →+* ℂ) := fun τ => σ.comp (embK c τ)
  obtain ⟨α, h1, ⟨p, hp, hp'⟩, h3⟩ := exists_sepElt (RingHom.id ℂ) (fun ρ : E →+* ℂ => ρ.comp (algebraMap (𝓞 E) E))
    fun _ _ => rfl
  have hα : Function.Injective fun τ => χ τ α := h1.comp π.injective
  have hp'' : p.map (Int.castRingHom ℂ) = ∏ τ, (Polynomial.X - Polynomial.C (χ τ α)) :=
    hp'.trans (π.prod_comp _).symm
  refine ⟨Module.Basis.mk (v := fun p => f.vec p.1 p.2) (Fintype.linearIndependent_iff.2 fun a ha q => ?_)
    fun w _ => ?_, fun _ => Module.Basis.mk_apply _ _ _⟩
  · have := proj_sum_eig (actR (x0 := y) Z.t.act) χ α hα (fun τ => ∑ i, a ⟨τ, i⟩ • f.vec τ i) (fun τ b => by
      simp only [map_sum, map_smul, f.act_vec, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _) q.1
    rw [← Fintype.sum_sigma (fun q : Σ τ : E →+* ℂ, Fin (Dw.mult τ) => a q • f.vec q.1 q.2), ha, map_zero] at this
    exact Fintype.linearIndependent_iff.1 (f.linearIndependent_vec q.1) _ this.symm q.2
  · have := LinearMap.congr_fun (sum_proj (actR (x0 := y) Z.t.act) χ α hα) w
    rw [LinearMap.sum_apply, Module.End.one_apply] at this
    rw [← this]
    refine Submodule.sum_mem _ fun τ _ => ?_
    obtain ⟨a, ha, -⟩ := f.existsUnique_sum τ _ (eig_of_alpha (actR (x0 := y) Z.t.act) χ α h3 τ
      (proj_eig_alpha _ χ α hα p hp hp'' τ w))
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨τ, i⟩, rfl⟩)

theorem exists_frac {B : Type} [CommRing B] {X : Scheme.{0}} (V : Sp B ⟶ X) (U : X.Opens) (f : Γ(X, U))
    (p : PrimeSpectrum B) (hp : V p ∈ U) : ∃ s a : B, s ∉ p.asIdeal ∧ ∀ (R : Type) [CommRing R] (ρ : B →+* R),
      IsUnit (ρ s) → valR (spMap ρ ≫ V) U f * ρ s = ρ a := by
  have hT := isAffineOpen_top (Sp B)
  obtain ⟨s, hsU, hs₀⟩ := hT.exists_basicOpen_le (V := V ⁻¹ᵁ U) ⟨p, hp⟩ trivial
  obtain ⟨n, g, hg⟩ := exists_eq_pow_mul_of_isAffineOpen (Sp B) ⊤ hT s
    (((Sp B).presheaf.map (homOfLE hsU).op).hom ((V.app U).hom f))
  let i := (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
  have hs : (Sp B).basicOpen s = PrimeSpectrum.basicOpen (i s) := basicOpen_eq_of_affine' s
  have hv : ∀ (R : Type) [CommRing R] (ρ : B →+* R) (k : Γ(Sp B, ⊤)), valR (spMap ρ) ⊤ k = ρ (i k) := fun R _ ρ k => by
    have := valR_spMap ρ (𝟙 (Sp B)) ⊤ le_top k
    rw [Category.comp_id] at this
    rw [this, valR_eq _ _ le_top]
    simp [evalHom, i, Scheme.Hom.appLE]
  refine ⟨i s ^ (n + 1), i g * i s, fun h => ?_, fun R _ ρ hu => ?_⟩
  · rw [hs] at hs₀
    exact hs₀ (p.2.mem_of_pow_mem _ h)
  · rw [map_pow, isUnit_pow_succ_iff] at hu
    have ht : ⊤ ≤ spMap ρ ⁻¹ᵁ (Sp B).basicOpen s := fun q _ => by
      rw [hs]
      exact fun h => q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    have h1 := valR_res (spMap ρ) ((Sp B).basicOpen_le s) g ht
    have h2 := valR_res (spMap ρ) ((Sp B).basicOpen_le s) s ht
    have h3 := valR_res (spMap ρ) hsU ((V.app U).hom f) ht
    have hg' : ((Sp B).presheaf.map (homOfLE ((Sp B).basicOpen_le s)).op).hom g =
        ((Sp B).presheaf.map (homOfLE ((Sp B).basicOpen_le s)).op).hom s ^ n *
          ((Sp B).presheaf.map (homOfLE hsU).op).hom ((V.app U).hom f) := hg
    rw [valR_comp, map_pow, map_mul, pow_succ, ← mul_assoc, ← hv R ρ g, ← h1, ← h3, hg', ← hv R ρ s, ← h2,
      valR_eq _ _ ht, valR_eq _ _ ht, valR_eq _ _ ht, map_mul, map_pow, mul_comm (_ ^ n)]

theorem isHolTo_spMap {A : Type} [CommRing A] {ψ : ℂ → (A →+* ℂ)} {r : ℝ} (h : IsHolPts ψ r) {X : Scheme.{0}}
    (x : Sp A ⟶ X) : IsHolTo (Metric.ball (0 : ℂ) r) fun u => spMap (ψ u) ≫ x := by
  refine isHolTo_of_holAt Metric.isOpen_ball fun z hz => HolAt.comp ?_ x
  refine holAt_of_affine (isAffineOpen_top _) le_top (.of_forall fun _ => le_top) fun k => ?_
  have hv : ∀ u, valAt' (spMap (ψ u)) ⊤ k = ψ u (valR (𝟙 (Sp A)) ⊤ k) := fun u => by
    have := valR_spMap (ψ u) (𝟙 (Sp A)) ⊤ le_top k
    rwa [Category.comp_id] at this
  simp only [hv]
  exact (h.2 _).differentiableAt (Metric.isOpen_ball.mem_nhds hz)

theorem continuousAt_snd {A : Type} [CommRing A] {ψ : ℂ → (A →+* ℂ)} {z : ℂ} (h : ∀ a, ContinuousAt (fun u => ψ u a) z)
    {X : Scheme.{0}} (V : Sp (DualNumber A) ⟶ X) (U : X.Opens) (hU : ⊤ ≤ (spMap (dualMap (ψ z)) ≫ V) ⁻¹ᵁ U)
    (f : Γ(X, U)) : ContinuousAt (fun u => TrivSqZeroExt.snd (valR (spMap (dualMap (ψ u)) ≫ V) U f)) z := by
  obtain ⟨s, a, hs, H⟩ := exists_frac V U f (spMap (dualMap (ψ z)) (IsLocalRing.closedPoint (DualNumber ℂ)))
    (hU (x := IsLocalRing.closedPoint (DualNumber ℂ)) trivial)
  have h0 : ψ z s.fst ≠ 0 := fun h0 => hs (by
    change dualMap (ψ z) s ∈ IsLocalRing.maximalIdeal (DualNumber ℂ)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simp [dualMap, h0])
  have key : ∀ᶠ u in 𝓝 z, TrivSqZeroExt.snd (valR (spMap (dualMap (ψ u)) ≫ V) U f) =
      (ψ u a.snd - ψ u a.fst / ψ u s.fst * ψ u s.snd) / ψ u s.fst := by
    filter_upwards [(h s.fst).eventually_ne h0] with u hu
    have := H _ (dualMap (ψ u)) (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by simpa [dualMap] using hu))
    generalize valR (spMap (dualMap (ψ u)) ≫ V) U f = q at this ⊢
    have h1 := congrArg TrivSqZeroExt.fst this
    have h2 := congrArg TrivSqZeroExt.snd this
    simp [dualMap] at h1 h2
    rw [← h1, ← h2]
    field_simp
    ring
  exact ContinuousAt.congr (((h _).sub (((h _).div (h _) h0).mul (h _))).div (h _) h0) (key.mono fun _ => Eq.symm)

theorem continuousAt_dir {S : Scheme.{0}} {G : Over S} {g : ℕ} {B : Set ℂ} {y : ℂ → (Sp ℂ ⟶ S)}
    {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)}
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : ℂ × (Fin g → ℂ) => (e bz.1 bz.2).left)) {b₀ : ℂ} (hb₀ : b₀ ∈ B)
    (hdiff : ∀ v : epsPt (y b₀) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e b₀ 0).left →
      ∃! w, IsDerivAt0 (fun z => (e b₀ z).left) w v.left)
    {w : ℂ → Fin g → ℂ} {v : ℂ → (Sp (DualNumber ℂ) ⟶ G.left)}
    (hv : ∀ b ∈ B, IsDerivAt (fun z => (e b z).left) 0 (w b) (v b))
    (hc : ∀ U, ⊤ ≤ v b₀ ⁻¹ᵁ U → ∀ f, ContinuousAt (fun b => TrivSqZeroExt.snd (valR (v b) U f)) b₀) :
    ContinuousAt w b₀ := by
  have hslice : HolAt (fun z => (e b₀ z).left) 0 :=
    (holAt_of_isHolTo hol (z := (b₀, 0)) ⟨hb₀, trivial⟩).precomp (k := fun z => (b₀, z)) (by fun_prop)
  let s : Set ((Fin g → ℂ) →ₗ[ℂ] ℂ) := {l | ∃ (U : G.left.Opens) (_ : ⊤ ≤ (e b₀ 0).left ⁻¹ᵁ U) (f : Γ(G.left, U)),
    l = (fderiv ℂ (fun z => valAt' (e b₀ z).left U f) 0).toLinearMap}
  have hs : Submodule.span ℂ s = ⊤ := Submodule.span_eq_top_of_ne_zero fun w hw => by
    by_contra hne
    refine hw (eq_of_forall_fderiv_eq hslice hdiff fun U hU f => ?_)
    rw [map_zero]
    by_contra h0
    exact hne ⟨_, ⟨U, hU, f, rfl⟩, h0⟩
  have key : ∀ l ∈ Submodule.span ℂ s, ∃ (m : ℂ → (Fin g → ℂ) →L[ℂ] ℂ) (n : ℂ → ℂ),
      ContinuousAt m b₀ ∧ ContinuousAt n b₀ ∧ (m b₀).toLinearMap = l ∧ ∀ᶠ b in 𝓝 b₀, m b (w b) = n b := by
    intro l hl
    induction hl using Submodule.span_induction with
    | mem l hl =>
      obtain ⟨U, hU, f, rfl⟩ := hl
      refine ⟨fun b => fderiv ℂ (fun z => valAt' (e b z).left U f) 0, _,
        (differentiableAt_partial (hol U f).1 (hol U f).2 ⟨⟨hb₀, trivial⟩, hU⟩).continuousAt,
        hc U ((le_preimage_dual_iff (hv b₀ hb₀).1 U).2 hU) f, rfl, ?_⟩
      have h3 : ContinuousAt (fun b : ℂ => (b, (0 : Fin g → ℂ))) b₀ := by fun_prop
      filter_upwards [h3.eventually ((hol U f).1.mem_nhds ⟨⟨hb₀, trivial⟩, hU⟩)] with b hb
      exact ((hv b hb.1.1).2 U hb.2 f).symm
    | zero => exact ⟨0, 0, continuousAt_const, continuousAt_const, rfl, .of_forall fun _ => rfl⟩
    | add l l' _ _ ih ih' =>
      obtain ⟨m, n, hm, hn, rfl, hmn⟩ := ih
      obtain ⟨m', n', hm', hn', rfl, hmn'⟩ := ih'
      refine ⟨m + m', n + n', hm.add hm', hn.add hn', rfl, ?_⟩
      filter_upwards [hmn, hmn'] with b h1 h2
      simp [h1, h2]
    | smul a l _ ih =>
      obtain ⟨m, n, hm, hn, rfl, hmn⟩ := ih
      refine ⟨a • m, a • n, hm.const_smul a, hn.const_smul a, rfl, ?_⟩
      filter_upwards [hmn] with b h1
      simp [h1]
  choose m n hm hn hm0 hmn using fun i : Fin g => key (LinearMap.proj i) (hs.ge trivial)
  let M : ℂ → (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := fun b => ContinuousLinearMap.pi fun i => m i b
  have hM : ContinuousAt M b₀ :=
    (ContinuousLinearMap.piEquivL ℂ (Fin g → ℂ) (fun _ : Fin g => ℂ)).continuousAt.comp (continuousAt_pi.2 hm)
  have hM0 : M b₀ = (ContinuousLinearEquiv.refl ℂ (Fin g → ℂ) : _ →L[ℂ] _) := by
    ext1 w
    funext i
    exact congrArg (· w) (congrArg DFunLike.coe (hm0 i))
  have hinv : ∀ᶠ b in 𝓝 b₀, (M b).IsInvertible :=
    hM.eventually (hM0 ▸ (ContinuousLinearEquiv.refl ℂ (Fin g → ℂ)).nhds :)
  have hI : ContinuousAt (fun b => (M b).inverse) b₀ :=
    (hinv.self_of_nhds.contDiffAt_map_inverse (n := 1)).continuousAt.comp hM
  refine (hI.clm_apply (continuousAt_pi.2 hn)).congr ?_
  filter_upwards [hinv, eventually_all.2 hmn] with b hb hb'
  exact hb.inverse_apply_eq.2 (funext fun i => (hb' i).symm)

end GlobalTheory.ShFam.BdArc.LatSec

namespace GlobalTheory.ShFam.BdArc

open LatSec in

theorem exists_lattice_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), IsArc Z σ φ x ψ r → ∃ (ρ : ℝ) (n : ℕ) (lam : Fin n → ℂ → (Fin g → ℂ)), 0 < ρ ∧ ρ ≤ r ∧ (∀ j, ContinuousOn (lam j) (Metric.ball 0 ρ)) ∧ Submodule.span ℂ (Set.range fun j => lam j 0) = ⊤ ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, ∀ ex : (Fin g → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G), (∀ z w, ex (z + w) = ex z * ex w) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (ex z).left)) → (∀ j, IsDerivAt0 (fun z => (ex z).left) (Pi.single j 1) (spMap (dualMap (ψ u)) ≫ fr.v (e j).1 (e j).2)) → ∀ j, ex (lam j u) = 1 := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ r g e harc
  obtain ⟨g', ρ, e', hρ, hρr, hol, hexp, hdef⟩ := GlobalTheory.T.exists_semi_abelian_exponential_along_disc Z.X Z.t.G (fun u => spMap (ψ u) ≫ x ≫ genι Z) r
    Z.t.semi harc.1.1 (isHolTo_spMap harc.1 _)
  have hA : ∀ u ∈ Metric.ball (0 : ℂ) ρ, HolAt (fun z => (e' u z).left) 0 := fun u hu =>
    holAt_of_isHolTo (hexp u hu).2.2.1 trivial
  have hh : ∀ u, ∃ h : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ), u ∈ Metric.ball (0 : ℂ) ρ → h.IsInvertible ∧
      ∀ j, IsDerivAt (fun z => (e' u z).left) 0 (h (Pi.single j 1))
        (spMap (dualMap (ψ u)) ≫ fr.v (e j).1 (e j).2) := fun u => by
    by_cases hu : u ∈ Metric.ball (0 : ℂ) ρ
    · obtain ⟨D, hD⟩ := exists_lieEquiv Z.t (hexp u hu).1 (hA u hu) (hexp u hu).2.2.2.2
      obtain ⟨f, hf⟩ := GlobalTheory.T.exists_eigFrame_baseChange' E H Dw l Xo c O β Z A ℂ φ _ fr (ψ u)
      obtain ⟨b, hb⟩ := exists_basis f
      refine ⟨((b.reindex e.symm).equivFun.symm.trans D.symm).toContinuousLinearEquiv, fun _ => ⟨⟨_, rfl⟩, fun j => ?_⟩⟩
      have h1 := hD (D.symm (f.vec (e j).1 (e j).2))
      rw [D.apply_symm_apply] at h1
      have h2 : ((b.reindex e.symm).equivFun.symm.trans D.symm).toContinuousLinearEquiv (Pi.single j 1) =
          D.symm (f.vec (e j).1 (e j).2) := by simp [hb, Pi.single_apply]
      rw [← hf, ContinuousLinearEquiv.coe_coe, h2]
      exact h1
    · exact ⟨0, fun h => absurd h hu⟩
  choose h hh using hh
  have hc : ∀ u ∈ Metric.ball (0 : ℂ) ρ, ContinuousAt (fun u => (h u).inverse) u := fun u hu => by
    refine ((hh u hu).1.contDiffAt_map_inverse (n := 1)).continuousAt.comp (continuousAt_clm_apply.2 fun z => ?_)
    have : ∀ u, h u z = ∑ j, z j • h u (Pi.single j 1) := fun u => by
      simp only [← map_smul, ← map_sum]
      exact congrArg _ (pi_eq_sum_univ' z)
    simp only [this]
    refine tendsto_finset_sum _ fun j _ => ContinuousAt.const_smul ?_ (z j)
    exact continuousAt_dir hol hu (hexp u hu).2.2.2.2 (fun b hb => (hh b hb).2 j) (continuousAt_snd (fun a =>
      ((harc.1.2 a).differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hρr hu))).continuousAt) _)
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  obtain ⟨s, hs, hfin, hspan⟩ : ∃ s ⊆ {z | e' 0 z = 1}, s.Finite ∧ Submodule.span ℂ s = ⊤ := by
    obtain ⟨s, h1, h2, h3⟩ := exists_linearIndependent ℂ {z | e' 0 z = 1}
    exact ⟨s, h1, h3.set_finite_of_isNoetherian, h2.trans (GlobalTheory.T.span_periodLattice_complexSemiAbelian_eq_top _ _ _ _ _ Z.t.semi (hexp 0 h0))⟩
  obtain ⟨n, z, -, rfl⟩ := hfin.fin_param
  choose ζ hζ0 hζa hζ using fun j => hdef (z j) (hs ⟨j, rfl⟩)
  obtain ⟨ρ', hρ', hball⟩ := Metric.eventually_nhds_iff_ball.1 ((eventually_all.2 hζ).and
    (eventually_all.2 fun j => (hζa j).eventually_analyticAt))
  have hsub : Metric.ball (0 : ℂ) (min ρ ρ') ⊆ Metric.ball 0 ρ := Metric.ball_subset_ball (min_le_left _ _)
  have hsub' : Metric.ball (0 : ℂ) (min ρ ρ') ⊆ Metric.ball 0 ρ' := Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨min ρ ρ', n, fun j u => (h u).inverse (ζ j u), lt_min hρ hρ', (min_le_left _ _).trans hρr, fun j u hu =>
    ((hc u (hsub hu)).clm_apply ((hball u (hsub' hu)).2 j).continuousAt).continuousWithinAt, ?_,
    fun u hu ex hadd hex hd j => ?_⟩
  · obtain ⟨L, hL⟩ := (hh 0 h0).1
    have : (Set.range fun j => (h 0).inverse (ζ j 0)) = L.symm.toLinearEquiv.toLinearMap '' Set.range z := by
      rw [← Set.range_comp, ← hL]
      congr 1
      funext j
      simp [hζ0]
    rw [this, ← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨hu1, -, hu2, -, hu3⟩ := hexp u (hsub hu)
    obtain ⟨k, hk, -⟩ := existsUnique_linear hadd hu1 hex hu2 hu3
    have hkh : k = (h u).toLinearMap := (Pi.basisFun ℂ (Fin g)).ext fun i => by
      have h1 := (isDerivAt0_iff _ _ _).1 (hd i)
      simp only [hk] at h1
      have h2 := (isDerivAt_comp_iff (hA u (hsub hu)) (LinearMap.toContinuousLinearMap k) _ _).1 h1
      rw [Pi.basisFun_apply]
      exact (hu3 (Over.homMk _ h2.over) h2.1).unique ((isDerivAt0_iff _ _ _).2 h2)
        ((isDerivAt0_iff _ _ _).2 ((hh u (hsub hu)).2 i))
    rw [hk, hkh, ContinuousLinearMap.coe_coe, (hh u (hsub hu)).1.self_apply_inverse]
    exact (hball u (hsub' hu)).1 j

end GlobalTheory.ShFam.BdArc
