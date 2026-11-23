import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOrbitProjectorEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIndepRangeInc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionPreservesIntegralCuspForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenImmersionOfSection
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms

noncomputable section

namespace GlobalTheory.DefPt.OrbitGeo

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

section Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ptF_eq {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : z.x = spMap φ.toRingHom ≫ y.x) :
    ptF z = spMap φ.toRingHom ≫ ptF y := by
  apply Limits.pullback.hom_ext
  · rw [ptF, ptF, Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst, h]
  · rw [ptF, ptF, Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd, ← AlgebraicGeometry.Spec.map_comp]
    exact congrArg spMap (φ.comp_algebraMap).symm

theorem framedPointLiesOnComponent_of_specMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : z.x = spMap φ.toRingHom ≫ y.x) {Z : Comp Xo c} (hy : LiesOn Z y) :
    LiesOn Z z := fun s => by
  rw [ptF_eq φ h]
  exact hy _

theorem liesOn_congr {S : Type} [CommRing S] [Algebra c.F S] {y z : FrPt Xo c S} (h : z.x = y.x) {Z : Comp Xo c}
    (hy : LiesOn Z y) : LiesOn Z z :=
  framedPointLiesOnComponent_of_specMap (AlgHom.id c.F S) (by rw [spMap_algHom_id, Category.id_comp, h]) hy

theorem exists_liesOn' {S : Type} [CommRing S] {_ : Algebra c.F S} (hs : ∀ s s' : Sp S, s = s') (s₀ : Sp S)
    (y : FrPt Xo c S) : ∃ Z : Comp Xo c, LiesOn Z y := by
  have hall : ptF y s₀ ∈ ⋃₀ irreducibleComponents (Xo.XF c) := by
    rw [sUnion_irreducibleComponents]; trivial
  obtain ⟨W, hW, hq⟩ := Set.mem_sUnion.1 hall
  exact ⟨⟨W, hW⟩, fun s => hs s₀ s ▸ hq⟩

theorem exists_liesOn {S : Type} [Field S] [Algebra c.F S] (y : FrPt Xo c S) : ∃ Z : Comp Xo c, LiesOn Z y :=
  exists_liesOn' (fun s s' => Subsingleton.elim (α := PrimeSpectrum S) s s') (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S) y

theorem comp_unique {S : Type} [Field S] [Algebra c.F S] {y : FrPt Xo c S} {Z Z' : Comp Xo c} (h : LiesOn Z y)
    (h' : LiesOn Z' y) : Z = Z' := by
  have s₀ : Sp S := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S)
  by_contra hne
  exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c Z Z' hne) (h s₀) (h' s₀)

end Points

section Act

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {G : Type} [Group G] {lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}

theorem x_of_levR (hL : ActLev (Xo := Xo) c lev) (g : G) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T]
    [Algebra c.F T] {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (hy : levR (lev g) y y') (hz : levR (lev g) z z') :
    ∃ ρ : Xo.X ⟶ Xo.X, IsIso ρ ∧ y'.x = y.x ≫ ρ ∧ z'.x = z.x ≫ ρ := by
  obtain ⟨ρ, ν, hi, hν, hm⟩ := hy
  obtain ⟨w, hw⟩ := (GlobalTheory.exists_unique_frMove _ H Dw l Xo c ρ ν hν.1 T z).1
  have h := (hL.func g T z w z' ⟨ρ, ν, hi, hν, hw⟩ hz).1
  rw [spMap_algHom_id, Category.id_comp] at h
  exact ⟨ρ, hi, hm.1, h.trans hw.1⟩

theorem exists_comp (hL : ActLev (Xo := Xo) c lev) (hq : Dw.q = 0) (hF : FnAlgClosed Xo c) (g : G) (Z : Comp Xo c) :
    ∃ Z' : Comp Xo c, ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), levR (lev g) y y' →
      (LiesOn Z y' ↔ LiesOn Z' y) := by
  obtain ⟨y₀, h₀, h₁⟩ := GlobalTheory.FlatLine.DefinitePoint.main _ H Dw l Xo c hq hF Z
  obtain ⟨w, hw⟩ := hL.total g⁻¹ c.F y₀
  obtain ⟨w', hw'⟩ := hL.total g c.F w
  have h2 := hL.mul g⁻¹ g c.F y₀ w w' hw hw'
  rw [inv_mul_cancel] at h2
  have h3 := (hL.func 1 c.F y₀ y₀ w' (hL.one c.F y₀) h2).1
  rw [spMap_algHom_id, Category.id_comp] at h3
  obtain ⟨Z', hZ'⟩ := exists_liesOn w
  obtain ⟨y₁, -, h₄⟩ := GlobalTheory.FlatLine.DefinitePoint.main _ H Dw l Xo c hq hF Z'
  refine ⟨Z', fun S _ _ y y' hy => ?_⟩
  obtain ⟨ρ, hi, e₁, e₂⟩ := x_of_levR hL g hy hw'
  constructor
  · intro h
    refine framedPointLiesOnComponent_of_specMap (Algebra.ofId c.F S) ?_ hZ'
    rw [← cancel_mono ρ, ← e₁, Category.assoc, ← e₂, h3]
    exact h₁ S y' h
  · intro h
    refine framedPointLiesOnComponent_of_specMap (Algebra.ofId c.F S) ?_ h₀
    have e₃ : w.x = y₁.x := (h₄ c.F w hZ').trans (by
      rw [show spMap (algebraMap c.F c.F) = 𝟙 _ from spMap_algHom_id c.F c.F, Category.id_comp])
    rw [e₁, h₄ S y h, ← e₃, Category.assoc, ← e₂, h3]
    rfl

theorem exists_mulAction (hL : ActLev (Xo := Xo) c lev) (hq : Dw.q = 0) (hF : FnAlgClosed Xo c) :
    ∃ _ : MulAction G (Comp Xo c), ∀ (g : G) (Z : Comp Xo c) (S : Type) [CommRing S] [Algebra c.F S]
      (y y' : FrPt Xo c S), levR (lev g) y y' → (LiesOn Z y' ↔ LiesOn (g • Z) y) := by
  choose m hm using exists_comp hL hq hF
  suffices h : (∀ Z, m 1 Z = Z) ∧ ∀ g h Z, m (g * h) Z = m g (m h Z) from
    ⟨{ smul := m, one_smul := h.1, mul_smul := h.2 }, hm⟩
  refine ⟨fun Z => ?_, fun g h Z => ?_⟩
  · obtain ⟨y₀, h₀, -⟩ := GlobalTheory.FlatLine.DefinitePoint.main _ H Dw l Xo c hq hF Z
    exact comp_unique ((hm 1 Z _ y₀ y₀ (hL.one c.F y₀)).1 h₀) h₀
  · obtain ⟨y, h₀, -⟩ := GlobalTheory.FlatLine.DefinitePoint.main _ H Dw l Xo c hq hF (m (g * h) Z)
    obtain ⟨y', hy'⟩ := hL.total g c.F y
    obtain ⟨y'', hy''⟩ := hL.total h c.F y'
    exact comp_unique h₀ ((hm g _ _ y y' hy').1 ((hm h Z _ y' y'' hy'').1
      ((hm (g * h) Z _ y y'' (hL.mul g h c.F y y' y'' hy' hy'')).2 h₀)))

theorem actLev_idem (hL : ActLev (Xo := Xo) c lev) (g : G) {Z Z' : Comp Xo c}
    (h : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), levR (lev g) y y' →
      (LiesOn Z y' ↔ LiesOn Z' y)) : actLev c lev g (idem Z) = idem Z' := by
  funext p y
  refine sub_eq_zero.1 (eq_zero_of_forall_prime fun q => ?_)
  let φ : p.R →ₐ[c.F] q.asIdeal.ResidueField := IsScalarTower.toAlgHom c.F p.R _
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ φ y
  obtain ⟨z', hz'⟩ := hL.total g _ z
  have hm := hL.nat g _ _ φ y _ z z' hz (mvPt_spec hL.total g y) hz'
  have e₁ := evR_of_frMap_test (idem_mem_secZ Z).1 hm
  have e₂ := evR_of_frMap_test (idem_mem_secZ Z').1 hz
  have e₃ : evR Xo c (idem Z) z' = evR Xo c (idem Z') z := by
    by_cases hc : LiesOn Z z'
    · rw [evR_idem hc ⟨p, φ, _, hm⟩, evR_idem ((h _ z z' hz').1 hc) ⟨p, φ, _, hz⟩]
    · rw [idem_mem_suppOn Z _ z' ((liesOff_iff Z z').2 hc),
        idem_mem_suppOn Z' _ z ((liesOff_iff Z' z).2 fun h' => hc ((h _ z z' hz').2 h'))]
  rw [← Ideal.ker_algebraMap_residueField q.asIdeal, RingHom.mem_ker, map_sub, sub_eq_zero]
  exact e₁.symm.trans (e₃.trans e₂)

theorem exists_move (hL : ActLev (Xo := Xo) c lev) (g : G) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ y' : FrPt Xo c S, levR (lev g) y y' ∧ ∀ f : Rul Xo c,
      IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f →
      evR Xo c (actLev c lev g f) y = evR Xo c f y' :=
  ⟨_, mvPt_spec hL.total g y, fun _ hf =>
    evalAt_actL hL (GlobalTheory.TransferCompare.evalWD_framed Xo c) frMap_trans_id g hf y⟩

theorem actLev_int (hL : ActLev (Xo := Xo) c lev) (g : G) {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    (h : ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v f) :
    ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (actLev c lev g f) := by
  rintro la _ ⟨⟨q, S, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  let := io.toAlgebra
  have hmv := mvPt_spec hL.total g y.1
  let y' : IntFr Xo c S io :=
    ⟨_, GlobalTheory.LevActInt.fromTest_moved hL g y.2.1,
      GlobalTheory.FormTies.LevelMove.integral_of_levR _ _ _ _ _ _ (lev g) S io y.1 _ hmv y.2.2⟩
  have h0 : 0 ≤ nval S.V e (evI y' f) := h la _ ⟨PtV.mk la ho y' hy () trivial, rfl⟩
  have e1 : evI y (actLev c lev g f) = evI y' f :=
    evalAt_actL hL (GlobalTheory.TransferCompare.evalWD_framed Xo c) frMap_trans_id g hf y.1
  show 0 ≤ nval S.V e (evI y (actLev c lev g f))
  rw [e1]
  exact h0

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {ξ : ℝ} {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ}

theorem actLev_mem_sec (hL : ActLev (Xo := Xo) c lev) (g : G) {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    actLev c lev g f ∈ sec Xo c a n := actL_mem _ _ _ _ hL.total hL.nat hL.bor _ g hf

theorem actLev_mem_cuspW (hC : DefCase U ξ) (hL : ActLev (Xo := Xo) c lev) (hD : Dom a n) (g : G) {f : Rul Xo c}
    (hf : f ∈ cuspW Xo c U (wtZ a n)) : actLev c lev g f ∈ cuspW Xo c U (wtZ a n) := by
  rw [cuspW_wtZ] at hf ⊢
  obtain ⟨hs, hc⟩ := (mem_cusp _ _ _ _ _ _).1 hf
  have hg := actLev_mem_sec hL g hs
  refine (mem_cusp _ _ _ _ _ _).2 ⟨hg, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩
  have hU := hC.unf σ hσ
  have hpq : 1 ≤ Dw.p + Dw.q := hC.p.trans (Nat.le_add_right _ _)
  refine GlobalTheory.LevelCusp.rdU_mem_SS (U := Formalism.L2.PjFree.Unf.ofPj (U σ)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (hC.xi σ hσ k τ).trans (hC.xi σ hσ k' τ).symm) hD hs hg
    (fun k => GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (hc σ hσ) k) (fun y => ?_) k
  obtain ⟨y', ⟨ρ, ν, -, -, hm⟩, hv⟩ := exists_move hL g y
  exact ⟨ρ, ν, y', hm, hv f hs.1⟩

theorem homN_actLev (hC : DefCase U ξ) (hL : ActLev (Xo := Xo) c lev) (hD : Dom a n) (g : G) {Z Z' : Comp Xo c}
    (h : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), levR (lev g) y y' →
      (LiesOn Z y' ↔ LiesOn Z' y)) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {f : Rul Xo c} (hf : f ∈ sec Xo c a n)
    {z : Σ k, Frame ((U σ).X k).Ψ r} (hz : z ∈ framesOn (U σ) Z') :
    ∃ z' ∈ framesOn (U σ) Z, homN (U σ) ξ (wtZ a n) (actLev c lev g f) z = homN (U σ) ξ (wtZ a n) f z' := by
  obtain ⟨k, x⟩ := z
  obtain ⟨hx, hZ⟩ := hz
  have hU := hC.unf σ hσ
  have hpq : 1 ≤ Dw.p + Dw.q := hC.p.trans (Nat.le_add_right _ _)
  obtain ⟨hun1, hun2⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor _ H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj (U σ)) hσ hU
  obtain ⟨x₀, hx₀, -, ⟨t₀, ht₀⟩, hn₀⟩ := hun1 k ⟨x, hx⟩
  obtain ⟨y', hy', hv⟩ := exists_move hL g ((U σ).un k x₀)
  obtain ⟨k', x', t, hx', hb⟩ := hun2 y'
  have hZ' : LiesOn Z ((U σ).un k' x') :=
    liesOn_congr hb.1.symm ((h _ _ _ hy').2 (liesOn_congr ht₀.1.symm hZ))
  obtain ⟨ρ, ν, -, -, hm⟩ := hy'
  obtain ⟨-, -, -, -, -, -, ht⟩ := GlobalTheory.LevelCusp.exists_match (U := Formalism.L2.PjFree.Unf.ofPj (U σ)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (hC.xi σ hσ k τ).trans (hC.xi σ hσ k' τ).symm) hm hb hx₀ hx'
  refine ⟨⟨k', x'.1⟩, ⟨x'.2, hZ'⟩, ?_⟩
  have hsec := hU.2.2.2.2.1 a n hD _ (actLev_mem_sec hL g hf) k
  have v1 : rdU (U σ) (actLev c lev g f) k x₀.1 = toC (evR Xo c (actLev c lev g f) ((U σ).un k x₀)) := dif_pos x₀.2
  have v2 : rdU (U σ) f k' x'.1 = toC (evR Xo c f ((U σ).un k' x')) := dif_pos x'.2
  have v3 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 _ H Dw l Xo c).2.2.2.2.2.2 (CAt σ)
    (inferInstanceAs (IsReduced ℂ)) a n f hf t _ y' hb
  have v4 : ‖toC (wchar (ex Dw a n) t : CAt σ)‖ = 1 := by
    have : toC (wchar (ex Dw a n) t : CAt σ) = ∏ j, toC (t j : CAt σ) ^ ex Dw a n j := rfl
    rw [this, norm_prod]
    exact Finset.prod_eq_one fun j _ => by
      rw [norm_pow, show ‖toC (t j : CAt σ)‖ = 1 from ht j, one_pow]
  have v5 : ‖rdU (U σ) (actLev c lev g f) k x₀.1‖ = ‖rdU (U σ) f k' x'.1‖ := by
    rw [v1, v2, hv f hf.1, v3]
    exact (norm_mul (toC (wchar (ex Dw a n) t : CAt σ)) _).trans (by rw [v4, one_mul]; rfl)
  unfold homN ptN
  rw [modelWt_wtZ]
  congr 1
  exact (hn₀ _ _ hsec).trans (v5.trans (pnorm_eq_of_unit _ _ _ _ hx').symm)

end Act

section Abstract

theorem exists_int {K G : Type} [Field K] [NumberField K] [Group G] [Finite G] (χ : G →* Kˣ) (g : G) :
    (∃ b : 𝓞 K, (b : K) = (χ g : K)) ∧ ∀ σ : K →+* ℂ, ‖σ (χ g : K)‖ = 1 := by
  have hn : 0 < Nat.card G := Nat.card_pos
  have h : (χ g : K) ^ Nat.card G = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  refine ⟨⟨⟨χ g, IsIntegral.of_pow hn (h ▸ isIntegral_one)⟩, rfl⟩, fun σ => ?_⟩
  have h2 : ‖σ (χ g : K)‖ ^ Nat.card G = 1 := by rw [← norm_pow, ← map_pow, h, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem slope_eig {K V G C : Type} [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Group G] [Fintype G] [Fintype C] [Nonempty C] [MulAction G C]
    (e : C → V →ₗ[K] V) (ρ : Representation K G V) (χ : G →* Kˣ) (Nv : (K →+* ℂ) → V → ℝ)
    (M₀ M : Submodule (𝓞 K) V) (ι : C → Type) [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)] [∀ o, Nonempty (ι o)]
    (Y : ∀ o, (K →+* ℂ) → Matrix (ι o) (ι o) ℂ) (L : ∀ o, Submodule (𝓞 K) (ι o → K))
    (φ : ∀ o, (ι o → K) →ₗ[K] V) (s : ℝ)
    (hfree : ∀ (g : G) (Z : C), g • Z = Z → g = 1) (h₁ : ∀ Z v, e Z (e Z v) = e Z v)
    (h₂ : ∀ Z Z' v, Z ≠ Z' → e Z (e Z' v) = 0) (h₃ : ∀ v, ∑ Z, e Z v = v)
    (h₄ : ∀ g Z v, ρ g (e Z v) = e (g • Z) (ρ g v)) (hG : HasGram Nv) (hM₀ : M₀.FG)
    (hM : ∀ v, v ∈ M ↔ v ∈ M₀ ∧ ∀ g, ρ g v = (χ g : K) • v) (hρ : ∀ g, ∀ v ∈ M₀, ρ g v ∈ M₀)
    (hY : ∀ o σ, (Y o σ).det ≠ 0) (hL : ∀ o, Submodule.IsLattice K (L o)) (hφ : ∀ o, Function.Injective (φ o))
    (hr : ∀ o v, v ∈ LinearMap.range (φ o) ↔ e o v = v) (hφL : ∀ o, ∀ x ∈ L o, φ o x ∈ M₀)
    (hN₀ : ∀ σ v, 0 ≤ Nv σ v)
    (hN : ∀ σ v (B : ℝ), (∀ Z, ∃ (g : G) (o : C) (x : ι o → K) (u : K), Z = g • o ∧ ‖σ u‖ = 1 ∧
      e Z v = u • ρ g (φ o x) ∧ matNorm (Y o) σ x ≤ B) → Nv σ v ≤ B)
    (hs : ∀ o, s ≤ slope_sq (matNorm (Y o)) (L o)) : M ≠ ⊥ ∧ s ≤ slope_sq Nv M := by
  obtain ⟨O, hO, hdec, hsum⟩ := GlobalTheory.freeOrbit_projector_eigen K V G C e ρ χ hfree h₁ h₂ h₃ h₄
  obtain ⟨-, o₀, ho₀, -⟩ := hO (Classical.arbitrary C)
  haveI : Nonempty O := ⟨⟨o₀, ho₀⟩⟩
  let Φ : (∀ o : O, ι o → K) →ₗ[K] V :=
    ∑ o : O, ∑ g : G, (((χ g)⁻¹ : Kˣ) : K) • (ρ g ∘ₗ φ o ∘ₗ LinearMap.proj o)
  let f : (∀ o : O, ι o → K) → C → V := fun x o => if h : o ∈ O then φ o (x ⟨o, h⟩) else 0
  have hf : ∀ x (o : O), f x o = φ o (x o) := fun x o => dif_pos o.2
  have hfe : ∀ x o, e o (f x o) = f x o := fun x o => by
    by_cases h : o ∈ O
    · rw [hf x ⟨o, h⟩]; exact (hr _ _).1 ⟨_, rfl⟩
    · rw [show f x o = 0 from dif_neg h, map_zero]
  have hΦ' : ∀ x, Φ x = ∑ o : O, ∑ g, ((χ g)⁻¹ : Kˣ) • ρ g (φ o (x o)) := fun x => by
    simp only [Φ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Units.smul_def]
  have hΦ : ∀ x, Φ x = ∑ o ∈ O, ∑ g, ((χ g)⁻¹ : Kˣ) • ρ g (f x o) := fun x => by
    rw [hΦ', ← Finset.sum_coe_sort O]
    simp only [hf]
  have hpart : ∀ x g (o : O), e (g • (o : C)) (Φ x) = ((χ g)⁻¹ : Kˣ) • ρ g (φ o (x o)) := fun x g o => by
    rw [hΦ, (hsum (f x) (hfe x)).2 g o o.2, hf]
  have hinj : Function.Injective Φ := (injective_iff_map_eq_zero Φ).2 fun x hx => funext fun o => by
    have h := hpart x 1 o
    rw [hx, map_zero, map_one, map_one, inv_one, one_smul] at h
    exact (injective_iff_map_eq_zero _).1 (hφ o) _ h.symm
  have hmem : ∀ x : ∀ o : O, ι o → K, (∀ o : O, x o ∈ L o) → Φ x ∈ M := fun x hx => (hM _).2 ⟨by
    rw [hΦ']
    refine M₀.sum_mem fun o _ => M₀.sum_mem fun g _ => ?_
    obtain ⟨b, hb⟩ := (exists_int χ g⁻¹).1
    rw [← map_inv, Units.smul_def, ← hb, show ((b : K)) = algebraMap (𝓞 K) K b from rfl, algebraMap_smul]
    exact M₀.smul_mem b (hρ g _ (hφL o _ (hx o))), fun g => by
      rw [hΦ]; exact (hsum (f x) (hfe x)).1 g⟩
  constructor
  · intro h0
    have hx : ∃ x ∈ L o₀, x ≠ 0 := by
      by_contra hc
      have hb : L o₀ = ⊥ := (Submodule.eq_bot_iff _).2 fun x hx => by_contra fun h => hc ⟨x, hx, h⟩
      have := (hL o₀).span_eq_top
      rw [hb] at this
      simp at this
    obtain ⟨x, hx, hx0⟩ := hx
    have h := hmem (Pi.single (M := fun o : O => ι o → K) ⟨o₀, ho₀⟩ x) fun o => by
      by_cases h : o = ⟨o₀, ho₀⟩
      · subst h; rw [Pi.single_eq_same]; exact hx
      · rw [Pi.single_eq_of_ne h]; exact (L o).zero_mem
    rw [h0, Submodule.mem_bot] at h
    have := congrFun ((injective_iff_map_eq_zero Φ).1 hinj _ h) ⟨o₀, ho₀⟩
    rw [Pi.single_eq_same] at this
    exact hx0 this
  · have hMle : M ≤ M₀ := fun v hv => ((hM v).1 hv).1
    have hMfg : M.FG := by
      haveI : IsNoetherian (𝓞 K) M₀ := isNoetherian_of_fg_of_noetherian M₀ hM₀
      exact isNoetherian_submodule.1 inferInstance M hMle
    refine GlobalTheory.SumSlope.le_slope_sq_of_sum K V O (fun o => ι o) Nv M (fun o => Y o) (fun o => L o) Φ s hG hMfg
      (fun o => hY o) (fun o => hL o) hinj hmem (fun v hv => ?_) (fun σ x => ?_) fun o => hs o
    · choose x hx using fun o : O => (hr o (e o v)).2 (h₁ o v)
      refine ⟨x, ?_⟩
      rw [hΦ']
      simp only [hx]
      rw [Finset.sum_coe_sort O fun o => ∑ g, ((χ g)⁻¹ : Kˣ) • ρ g (e o v)]
      exact (hdec v ((hM v).1 hv).2).symm
    · have hB : 0 ≤ ∑ o : O, matNorm (Y o) σ (x o) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      rw [← Real.sq_sqrt hB]
      refine pow_le_pow_left₀ (hN₀ _ _) (hN σ _ _ fun Z => ?_) 2
      obtain ⟨g, o, ho, rfl⟩ := hO Z
      refine ⟨g, o, x ⟨o, ho⟩, ((χ g)⁻¹ : Kˣ), rfl, ?_, hpart x g ⟨o, ho⟩, Real.le_sqrt_of_sq_le ?_⟩
      · rw [← map_inv]; exact (exists_int χ g⁻¹).2 σ
      · exact Finset.single_le_sum (f := fun o : O => matNorm (Y o) σ (x o) ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ (⟨o, ho⟩ : O))

end Abstract

section Main

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {G : Type} [Group G] {lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
  {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {ξ : ℝ} {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ}

theorem mem_sec {f : Rul Xo c} (hf : f ∈ cuspW Xo c U (wtZ a n)) : f ∈ sec Xo c a n := by
  rw [cuspW_wtZ] at hf
  exact ((mem_cusp _ _ _ _ _ _).1 hf).1

def rep (hC : DefCase U ξ) (hL : ActLev (Xo := Xo) c lev) (hD : Dom a n) :
    Representation c.F G (cuspW Xo c U (wtZ a n)) where
  toFun g := (actLev c lev g).restrict fun _ hf => actLev_mem_cuspW hC hL hD g hf
  map_one' := LinearMap.ext fun f => Subtype.ext (actL_one _ _ _ hL.total hL.func hL.one (mem_sec f.2).1)
  map_mul' g h := LinearMap.ext fun f => Subtype.ext (actL_mul _ _ _ hL.total hL.func hL.mul g h (mem_sec f.2).1)

set_option synthInstance.maxHeartbeats 400000 in
theorem mem_eigSub (χ : G →* (c.F)ˣ) (f : Rul Xo c) :
    f ∈ eigSub lev χ ↔ ∀ g, actLev c lev g f = (χ g : c.F) • f := by
  rw [eigSub, Submodule.mem_iInf]
  exact forall_congr' fun g => LinearMap.mem_ker.trans sub_eq_zero

set_option synthInstance.maxHeartbeats 400000 in
theorem mem_eigLat (hC : DefCase U ξ) (hL : ActLev (Xo := Xo) c lev) (hD : Dom a n) (χ : G →* (c.F)ˣ)
    (v : cuspW Xo c U (wtZ a n)) : v ∈ eigLat U lev χ (wtZ a n) ↔
      v ∈ latW U (wtZ a n) ∧ ∀ g, rep hC hL hD g v = (χ g : c.F) • v :=
  and_congr_right fun _ => (mem_eigSub χ v.1).trans (forall_congr' fun _ =>
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)

def proj (hC : DefCase U ξ) (W : WTZ D.host.E) (Z : Comp Xo c) : cuspW Xo c U W →ₗ[c.F] cuspW Xo c U W where
  toFun f := ⟨idem Z * f.1, GlobalTheory.CompRestr.idem_mul_mem_cuspW hC.unf Z f.2⟩
  map_add' f g := Subtype.ext (mul_add _ f.1 g.1)
  map_smul' b f := Subtype.ext (mul_smul_comm b _ f.1)

theorem homN_idem_mul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (W : WTZ D.host.E) (f : Rul Xo c) {Z : Comp Xo c}
    {z : Σ k, Frame (U.X k).Ψ r} (hz : z ∈ framesOn U Z) : homN U ξ W (idem Z * f) z = homN U ξ W f z := by
  obtain ⟨hx, hZ⟩ := hz
  have v1 : ∀ f : Rul Xo c, rdU U f z.1 z.2 = toC (evR Xo c f (U.un z.1 ⟨z.2, hx⟩)) := fun f => dif_pos hx
  have e : rdU U (idem Z * f) z.1 z.2 = rdU U f z.1 z.2 := by
    rw [v1, v1]
    congr 1
    by_cases ht : Tested (U.un z.1 ⟨z.2, hx⟩)
    · have e : evR Xo c (idem Z * f) (U.un z.1 ⟨z.2, hx⟩) = evR Xo c (idem Z) _ * evR Xo c f _ :=
        evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (idem Z) f _
      rw [e, evR_idem hZ ht, one_mul]
    · unfold evR Formalism.L2.Pj.evalAt
      rw [dif_neg ht, dif_neg ht]
  unfold homN ptN Data.pnorm
  rw [e]

theorem homN_smul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (W : WTZ D.host.E) (u : c.F) (f : Rul Xo c)
    (z : Σ k, Frame (U.X k).Ψ r) : homN U ξ W (u • f) z = ‖σ u‖ * homN U ξ W f z := by
  unfold homN
  rw [map_smulₛₗ, mul_left_comm]
  exact congrArg _ (pnorm_smul _ _ (σ u) _ _)

theorem petAt_le {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
    (W : WTZ D.host.E) (f : Rul Xo c) {B : ℝ} (h : ∀ g, homN U ξ W f (dict g) ≤ B) :
    petAt U ξ V dict (muQ1 V) W f ≤ B := by
  have hB : 0 ≤ B := (homN_nonneg U ξ W f _).trans (h 1)
  rw [petAt_eq]
  refine ENNReal.toReal_le_of_le_ofReal hB ((MeasureTheory.eLpNorm_le_of_ae_bound (C := B)
    (Filter.Eventually.of_forall fun q => ?_)).trans (by simp))
  rw [Real.norm_of_nonneg (homN_nonneg U ξ W f _)]
  exact h _

end Main

set_option synthInstance.maxHeartbeats 400000 in

theorem eigLat_slope : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : Type) [Group G] [Finite G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (χ : G →* (c.F)ˣ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : ℝ), DefCase U ξ → Finite (Comp Xo c) → Nonempty (Comp Xo c) → (∀ σ, GoodEmb c σ → ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom) → ActLev (Xo := Xo) c lev → FreePt Xo c lev → Dom a n → GoodW U ξ V dict (wtZ a n) → (∀ Z : Comp Xo c, FibreAt U ξ Z (wtZ a n) s) → eigLat U lev χ (wtZ a n) ≠ ⊥ ∧ s ≤ slope_sq (normW U ξ V dict (wtZ a n)) (eigLat U lev χ (wtZ a n)) / 2 := by
  intro D H Dw l Xo c r U ξ V dict G _ _ lev χ a n s hC _ _ hd hL hfr hD hW hF
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite (Comp Xo c)
  haveI : IsTotallyComplex c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff]
    exact fun h => conj_comp_ne v.embedding h⟩
  obtain ⟨_, hact⟩ := exists_mulAction hL hC.q hC.geo
  choose ι i₁ i₂ i₃ L Y φ hLat hY hs hφ hr hint hnorm using hF
  have hφm : ∀ o x, φ o x ∈ cuspW Xo c U (wtZ a n) := fun o x => cuspOn_le U o _ (hr o ▸ LinearMap.mem_range_self _ x)
  have key := slope_eig (proj hC (wtZ a n)) (rep hC hL hD) χ (normW U ξ V dict (wtZ a n)) (latW U (wtZ a n))
    (eigLat U lev χ (wtZ a n)) ι Y L (fun o => (φ o).codRestrict _ (hφm o)) (2 * s) (fun g Z h => ?_)
    (fun Z v => Subtype.ext ?_) (fun Z Z' v h => Subtype.ext ?_) (fun v => Subtype.ext ?_)
    (fun g Z v => Subtype.ext ?_) hW.1 hW.2.1 (fun v => ?_)
    (fun g v hv => actLev_int hL g (mem_sec v.2).1 hv) (fun o => hY o) hLat
    (fun o x y h => hφ o (congrArg Subtype.val h)) (fun o v => ?_) hint (fun σ v => petAt_nonneg _ _ _ _ _ _ _)
    (fun σ v B h => ?_) (fun o => by linarith [hs o])
  · exact ⟨key.1, by linarith [key.2]⟩
  · obtain ⟨y, h₀, h₁⟩ := GlobalTheory.FlatLine.DefinitePoint.main _ H Dw l Xo c hC.q hC.geo Z
    obtain ⟨y', hy'⟩ := hL.total g c.F y
    refine hfr g c.F y y' hy' ((h₁ _ y' ((hact g Z _ y y' hy').2 (h.symm ▸ h₀))).trans (h₁ _ y h₀).symm)
  · show idem Z * (idem Z * v.1) = idem Z * v.1
    rw [← mul_assoc, idem_mul_idem]
  · show idem Z * (idem Z' * v.1) = 0
    rw [← mul_assoc, idem_mul_idem_of_ne h, zero_mul]
  · rw [Submodule.coe_sum]
    exact sum_idem_mul v.1
  · show actLev c lev g (idem Z) * actLev c lev g v.1 = idem (g • Z) * actLev c lev g v.1
    rw [actLev_idem hL g (hact g Z)]
  · exact mem_eigLat hC hL hD χ v
  · have h1 : v ∈ LinearMap.range ((φ o).codRestrict _ (hφm o)) ↔ v.1 ∈ LinearMap.range (φ o) :=
      exists_congr fun x => Subtype.ext_iff
    rw [h1, hr, Subtype.ext_iff]
    exact (and_iff_right v.2).trans (mem_suppOn_iff_idem_mul (cuspW_le_secZ _ v.2) o)
  · have hσ := goodEmb_goodOf c σ
    refine petAt_le _ _ _ _ _ fun q => ?_
    obtain ⟨Z, hZ⟩ : ∃ Z : Comp Xo c, LiesOn Z ((U (goodOf c σ)).un _ ⟨_, hd _ hσ q⟩) := exists_liesOn' (fun s s' => Subsingleton.elim (α := PrimeSpectrum ℂ) s s')
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ) ((U (goodOf c σ)).un _ ⟨_, hd _ hσ q⟩)
    have hz : dict _ q ∈ framesOn (U (goodOf c σ)) Z := ⟨hd _ hσ q, hZ⟩
    obtain ⟨g, o, x, u, rfl, hu, e, hB⟩ := h Z
    have e' : idem (g • o) * v.1 = u • actLev c lev g (φ o x) := congrArg Subtype.val e
    obtain ⟨z', hz', e₂⟩ := homN_actLev hC hL hD g (hact g o) hσ (mem_sec (hφm o x)) hz
    rw [← homN_idem_mul _ _ _ hz, e', homN_smul, norm_goodOf, hu, one_mul, e₂]
    exact (hnorm o σ x z' hz').trans hB

end GlobalTheory.DefPt.OrbitGeo

end
