import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSectionOneClassSeriesDescends
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueLinearInPolynomial
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestRingInjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.CoverDescent
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaSumDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

def MoveInv (d : DeltaDat Xo c n) (G : Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (s : Sim Dw) (ρ : d.Xo₂.X ≅ d.Xo₂.X) (ν : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ.hom), s.InGam l d.l₂ →
    d.Xo₂.LevAut s ρ → IsLevMove ρ.hom ν (s.f d.l₂.M) (s.f d.l₂.A) →
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra d.c₂.F k] (y y' : FrPt d.Xo₂ d.c₂ k), FrMove ρ.hom ν y y' →
      evR d.Xo₂ d.c₂ G y' = evR d.Xo₂ d.c₂ G y

theorem value_descends (d : DeltaDat Xo c n) (hlev : d.IsLev) (G : Rul d.Xo₂ d.c₂)
    (hG : IsNatural (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S) (fun φ y z => FrMap φ y z) G) (hinv : MoveInv d G)
    (p : TRing c.F) (y : FrPt Xo c p.R) :
    ∃! u : p.R, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
      ∀ (χ : p.R →ₐ[c.F] k) (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap χ y z → FrOver d z₂ z →
        χ u = evR d.Xo₂ d.c₂ G z₂ := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hN := GlobalTheory.LevelMapsAnyRank.levelMaps Dw
  have hWD := (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
  have hAT := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂
  haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  have hbc := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c
  have hbc₂ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw d.l₂ d.Xo₂ d.c₂
  have hcomp := (GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1
  obtain ⟨hdvd, hM, -, -, -, hE, hlift, -, -⟩ := id hlev
  obtain ⟨r, jK, m, -, -, he, heA, -, hF⟩ := hN l d.l₂ Xo d.Xo₂ hdvd
  obtain ⟨rF, h1, h2, _, _, _, -⟩ := hF c d.c₂ d.hF.symm
  have hEta : DeltaDat.EtaOK { d with r := r, m := m } := by
    refine ⟨fun b => ?_, heA⟩
    have := he b
    rwa [hM, Nat.mul_div_cancel_left _ (by have := l.three_le; omega)] at this
  obtain ⟨hov1, hov2, -⟩ := GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n { d with r := r, m := m }
  obtain ⟨S, _, φ, j, x₂, f1, f2, f3, hj, hx, hx'⟩ :=
    exists_cover_point d.hF.symm r rF h1 h2 p.R y.x y.x_over
  letI : Algebra p.R S := φ.toAlgebra
  letI : Algebra c.F S := (φ.comp (algebraMap c.F p.R)).toAlgebra
  letI : Algebra d.c₂.F S := j.toAlgebra
  haveI : Module.Finite p.R S := f1
  haveI : Algebra.Smooth p.R S := f2
  haveI : Module.FaithfullyFlat p.R S := f3
  haveI := isReduced_of_smooth_algebra p.R S
  have hS : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a := fun a =>
    RingHom.congr_fun hj a
  let φa : p.R →ₐ[c.F] S := { φ with commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := hbc p.R S φa y
  obtain ⟨y₂, -, hy₂⟩ := hov1 S hS y' x₂ (hx.trans hy'.1.symm) hx'
  have core : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
      ∀ (χ : p.R →ₐ[c.F] k) (χ' : S →+* k), χ'.comp φ = χ.toRingHom →
      ∀ (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap χ y z → FrOver d z₂ z →
        χ' (evR d.Xo₂ d.c₂ G y₂) = evR d.Xo₂ d.c₂ G z₂ := by
    intro k _ _ _ _ hk χ χ' hχ z z₂ hz hz₂
    have c1 : ∀ a : c.F, χ' (algebraMap c.F S a) = algebraMap c.F k a := fun a =>
      (RingHom.congr_fun hχ (algebraMap c.F p.R a)).trans (χ.commutes a)
    let ψ : S →ₐ[c.F] k := { χ' with commutes' := c1 }
    let ψ₂ : S →ₐ[d.c₂.F] k := { χ' with
      commutes' := fun b => by
        obtain ⟨a, rfl⟩ := d.eF.surjective b
        exact (congrArg χ' (hS a)).trans ((c1 a).trans (hk a).symm) }
    have hψ : ψ.comp φa = χ := AlgHom.ext fun x => RingHom.congr_fun hχ x
    have hz' : FrMap ψ y' z := (hcomp _ _ _ φa ψ y y' z hy').2 (by rw [hψ]; exact hz)
    obtain ⟨w₂, hw₂⟩ := hbc₂ S k ψ₂ y₂
    have hw' := hov2 S hS k hk ψ ψ₂ rfl y' y₂ z w₂ hy₂ hz' hw₂
    obtain ⟨g, ρ, ν, hg, hρ, hmv, hfr⟩ := GlobalTheory.exists_levMove_of_frOver hL E H Dw l Xo c n d hN hdvd hM hE
      r m hEta k hk z z₂ w₂ hz₂ hw'
    rw [← hinv g ρ ν hg hρ hmv k z₂ w₂ hfr, evR_baseChange hWD hAT G hG ψ₂ y₂ w₂ hw₂]
    rfl
  have pts : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : p.R →+* k),
      ∃ (_ : Algebra c.F k) (_ : Algebra d.c₂.F k) (χa : p.R →ₐ[c.F] k) (z : FrPt Xo c k)
        (z₂ : FrPt d.Xo₂ d.c₂ k),
        (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) ∧ χa.toRingHom = χ ∧
        FrMap χa y z ∧ FrOver d z₂ z := by
    intro k _ _ χ
    letI i1 : Algebra c.F k := (χ.comp (algebraMap c.F p.R)).toAlgebra
    letI i2 : Algebra d.c₂.F k := ((algebraMap c.F k).comp d.eF.symm.toRingEquiv.toRingHom).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a =>
      congrArg (algebraMap c.F k) (d.eF.symm_apply_apply a)
    let χa : p.R →ₐ[c.F] k := { χ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := hbc p.R k χa y
    obtain ⟨z₂, hz₂⟩ := hlift k hk z
    exact ⟨i1, i2, χa, z, z₂, hk, rfl, hz, hz₂⟩
  obtain ⟨u, hu⟩ := exists_preimage_of_geometric p.R S (evR d.Xo₂ d.c₂ G y₂) (by
    intro k _ _ χ₁ χ₂ h12
    obtain ⟨_, _, χa, z, z₂, hk, hχ, hz, hz₂⟩ := pts k (χ₁.comp φ)
    exact (core k hk χa χ₁ hχ.symm z z₂ hz hz₂).trans
      (core k hk χa χ₂ (h12.symm.trans hχ.symm) z z₂ hz hz₂).symm)
  refine ExistsUnique.intro u ?_ ?_
  · intro k _ _ _ _ hk χ z z₂ hz hz₂
    obtain ⟨χ', hχ'⟩ := exists_lift_geometric p.R S k χ.toRingHom
    rw [← core k hk χ χ' hχ' z z₂ hz hz₂, ← hu]
    exact (RingHom.congr_fun hχ' u).symm
  · intro u' hu'
    refine eq_of_geometric_points _ _ fun k _ _ χ => ?_
    obtain ⟨_, _, χa, z, z₂, hk, hχ, hz, hz₂⟩ := pts k χ
    obtain ⟨χ', hχ'⟩ := exists_lift_geometric p.R S k χ
    subst hχ
    have e := core k hk χa χ' hχ' z z₂ hz hz₂
    rw [← hu] at e
    exact (hu' k hk χa z z₂ hz hz₂).trans (e.symm.trans (RingHom.congr_fun hχ' u))

theorem evR_frBor {a : (E →+* ℂ) × ℕ → ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {k : Type} [Field k] [Algebra c.F k]
    {t : Ix Dw → kˣ} {y y' : FrPt Xo c k} (h : FrBor t y y') :
    evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y := by
  have hAT := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  exact (GlobalTheory.borDesc_and_wtField E H Dw l Xo c).2 a n f hf k t y y' (hAT k y) (hAT k y') h

open GlobalTheory.ShortDescent in

theorem exists_sec_of_moveInv (d : DeltaDat Xo c n) (hlev : d.IsLev) {a : (E →+* ℂ) × ℕ → ℕ} {n' : ℕ}
    (G : Rul d.Xo₂ d.c₂) (hG : G ∈ sec d.Xo₂ d.c₂ a n') (hinv : MoveInv d G) :
    ∃ f ∈ sec Xo c a n', ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
      ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → evR Xo c f y = evR d.Xo₂ d.c₂ G y₂ := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hAll := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c
  have hd := value_descends d hlev G hG.1 hinv
  obtain ⟨hlift, -, hbor⟩ := GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n d
  refine ⟨fun p y => (hd p y).exists.choose, ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩, ?_⟩
  · refine (hd q z).unique (hd q z).exists.choose_spec ?_
    intro k _ _ _ _ hk χ w w₂ hw ho
    exact (hd p y).exists.choose_spec k hk (χ.comp φ) w w₂ (GlobalTheory.FramedBaseChange.trans φ χ h hw) ho
  · refine (hd p y').unique (hd p y').exists.choose_spec ?_
    intro k _ _ _ _ hk χ w' w₂' hw' ho'
    obtain ⟨w, hw⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c p.R k χ y
    have hb := frBorBC _ _ χ t y y' w w' h hw hw'
    obtain ⟨w₂, hx₂, ho⟩ := hlift k hk w w₂'.x (ho'.1.trans hb.1) w₂'.x_over
    have hb₂ := hbor k hk _ w w' w₂ w₂' ho ho' hx₂.symm hb
    have e := (hd p y).exists.choose_spec k hk χ w w₂ hw ho
    rw [evR_frBor hG hb₂, map_mul, map_wchar]
    exact congrArg (_ * ·) e
  · intro k _ _ _ _ hk y y₂ ho
    have hy := hAll k y
    conv_lhs => unfold evR evalAt
    rw [dif_pos hy]
    exact (hd _ _).exists.choose_spec k hk _ y y₂ hy.choose_spec.choose_spec.choose_spec ho

theorem exists_sec_theta [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) (Λ : GenLat E n) (N : ℕ)
    (hU : Λ.Unimod) (hT : Λ.TrivAt l.M) (hO : Λ.LevOK N l.M) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    (w : (Fin n → LevQ Dw l) → c.F) (β : c.F) :
    ∃ th ∈ sec Xo c a n, ∀ (k : Type) [Field k] [Algebra c.F k] (y : FrPt Xo c k),
      ShortValAt Xo c nab w Λ β N P y (evR Xo c th y) := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hC := GlobalTheory.chartIndependence_unconditional
  have hAll := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c
  obtain ⟨hex, hnat⟩ := GlobalTheory.shortThetaValue_existsUnique_natural hL hC E H Dw l Xo c nab hnab n Λ N hU hT hO a P hP w β
  refine ⟨fun p y => (hex p.R y).exists.choose, ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩, fun k _ _ y => ?_⟩
  · exact (hnat _ _ φ y z h _ _ (hex p.R y).exists.choose_spec (hex q.R z).exists.choose_spec).symm
  · exact (hex p.R y').unique (hex p.R y').exists.choose_spec
      ((GlobalTheory.thetaValue_weight hL hC E H Dw l Xo c nab hnab p.R y y' t h n a P).2 hP _ Λ _ N _
        (hex p.R y).exists.choose_spec)
  · have hy := hAll k y
    obtain ⟨v, hv, -⟩ := hex k y
    unfold evR evalAt
    rw [dif_pos hy, hnat _ _ _ _ y hy.choose_spec.choose_spec.choose_spec _ v (hex _ _).exists.choose_spec hv]
    exact hv

theorem formula_eq {V F S Qt J : Type} [Field F] [CommRing S] [Algebra F S] [Fintype Qt] [Fintype J]
    (k N : F) (w : Qt → F) (G : Qt → J → (V →₀ ℕ) → S) (d : ℕ) (P : MvPolynomial V F) (hP : P.IsHomogeneous d)
    (s : Finset (V →₀ ℕ)) (hs : P.support ⊆ s) :
    algebraMap F S (k * (N ^ P.totalDegree)⁻¹) *
        ∑ᶠ q, algebraMap F S (w q) * ∑ j, ∑ mo ∈ P.support, algebraMap F S (P.coeff mo) * G q j mo =
      ∑ q, ∑ mo ∈ s, algebraMap F S (w q * P.coeff mo) * (algebraMap F S (k * (N ^ d)⁻¹) * ∑ j, G q j mo) := by
  by_cases h0 : P = 0
  · subst h0
    simp
  rw [hP.totalDegree h0, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm, ← Finset.sum_subset hs fun mo _ hmo => by simp [MvPolynomial.notMem_support_iff.1 hmo],
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [← Finset.mul_sum, map_mul _ (w q)]
  ring

theorem sum_values_eq [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) (Λ : GenLat E n) (N : ℕ)
    (hU : Λ.Unimod) (hT : Λ.TrivAt l.M) (hO : Λ.LevOK N l.M) (a : (E →+* ℂ) × ℕ → ℕ) {T : Type} [Fintype T]
    (P : T → MvPolynomial (LtN Dw n) c.F)
    (hP : ∀ t, P t ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    (w w' : T → (Fin n → LevQ Dw l) → c.F) (β : c.F) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (x x' v v' : T → S) (hv : ∀ t, ShortValAt Xo c nab (w t) Λ β N (P t) y (v t))
    (hv' : ∀ t, ShortValAt Xo c nab (w' t) Λ β N (P t) y (v' t))
    (h : ∀ q mo, ∑ t, x' t * algebraMap c.F S (w' t q * (P t).coeff mo) =
      ∑ t, x t * algebraMap c.F S (w t q * (P t).coeff mo)) :
    ∑ t, x' t * v' t = ∑ t, x t * v t := by
  classical
  rcases isEmpty_or_nonempty T with hT0 | ⟨⟨t₀⟩⟩
  · simp
  haveI := ShortValue.finite_levelQuotient Dw l
  haveI := Fintype.ofFinite (Fin n → LevQ Dw l)
  obtain ⟨S', _, _, φ, y', z, tp, F, hf, hm, hz, hg, ht, hF, -⟩ := hv t₀
  have hid : (AlgHom.id c.F S').toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective Function.bijective_id
  have hu := fun t w₀ v₀ hv₀ =>
    ((shortThetaValue_existsUnique_natural GlobalTheory.firstFiveLaws.1 GlobalTheory.chartIndependence_unconditional E H Dw l Xo c nab hnab
      n Λ N hU hT hO a (P t) (hP t) w₀ β).2 S S' φ y y' hm v₀ _ hv₀
      ⟨S', _, _, AlgHom.id c.F S', y', z, tp, F, hid, Frames.frMapUniq_refl y', hz, hg, ht, hF, rfl⟩).trans
      (formula_eq _ _ w₀ _ _ (P t) (ShortValueLinear.isHomogeneous_of_rowDeg (hP t).2.2)
        (Finset.univ.biUnion fun t => (P t).support) (Finset.subset_biUnion_of_mem (fun t => (P t).support) (Finset.mem_univ t)))
  apply hf.injective
  change φ _ = φ _
  simp only [map_sum, map_mul φ, hu _ _ _ (hv _), hu _ _ _ (hv' _), Finset.mul_sum _ _ (φ _)]
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset T))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset T))]
  refine Finset.sum_congr rfl fun mo _ => ?_
  have e := congrArg φ (h q mo)
  simp only [map_sum, map_mul φ, φ.commutes] at e
  simp only [← _root_.mul_assoc (φ _), ← Finset.sum_mul, e]

def SumInv (d : DeltaDat Xo c n) {T : Type} [Fintype T] (cs : T → Rul d.Xo₂ d.c₂)
    (w : T → (Fin n → LevQ Dw d.l₂) → c.F) (P : T → MvPolynomial (LtN Dw n) c.F) : Prop :=
  ∀ (s : Sim Dw) (ρ : d.Xo₂.X ≅ d.Xo₂.X), s.InGam l d.l₂ → d.Xo₂.LevAut s ρ →
    ∀ σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂,
      (∀ a : Dw.La, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (s.f d.l₂.M a)) →
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra d.c₂.F k] (y y' : FrPt d.Xo₂ d.c₂ k), y'.x = y.x ≫ ρ.hom →
    ∀ q mo, ∑ t, evR d.Xo₂ d.c₂ (cs t) y' *
        algebraMap d.c₂.F k (d.eF (w t (fun b => σq.symm (q b)) * (P t).coeff mo)) =
      ∑ t, evR d.Xo₂ d.c₂ (cs t) y * algebraMap d.c₂.F k (d.eF (w t q * (P t).coeff mo))

theorem evR_sum_mul {T : Type} [Fintype T] (f g : T → Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) : evR Xo c (∑ t, f t * g t) y = ∑ t, evR Xo c (f t) y * evR Xo c (g t) y := by
  let ev : Rul Xo c →+ S :=
    { toFun := fun f => evR Xo c f y
      map_zero' := evalAt_zero _ _ y
      map_add' := fun f f' => evalAt_add _ _ f f' y }
  exact (map_sum ev _ _).trans (Finset.sum_congr rfl fun t _ => evalAt_mul _ _ _ _ y)

theorem exists_sec_thetaSum (d : DeltaDat Xo c n) (hlev : d.IsLev) [StarRing (𝓞 E)] (hnab : IsNab d.Xo₂ d.c₂ d.nab₂)
    (Λ : GenLat E n) (N : ℕ) (hU : Λ.Unimod) (hT : Λ.TrivAt d.l₂.M) (hO : Λ.LevOK N d.l₂.M) (a : (E →+* ℂ) × ℕ → ℕ)
    {T : Type} [Fintype T] (cs : T → Rul d.Xo₂ d.c₂) (w : T → (Fin n → LevQ Dw d.l₂) → c.F)
    (P : T → MvPolynomial (LtN Dw n) c.F) (hcs : ∀ t, cs t ∈ sec d.Xo₂ d.c₂ 0 0)
    (hP : ∀ t, P t ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    (hinv : SumInv d cs w P) :
    ∃ f ∈ sec Xo c a n, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
      (∀ x : c.F, algebraMap d.c₂.F k (d.eF x) = algebraMap c.F k x) →
      ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → ∃ v : T → k,
        (∀ t, thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w t q)) Λ N
          (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (P t)) y₂ (v t)) ∧
        evR Xo c f y = ∑ t, evR d.Xo₂ d.c₂ (cs t) y₂ * v t := by
  have hP₂ := fun t => (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hP t)
  choose th hth hval using fun t => exists_sec_theta d.nab₂ hnab Λ N hU hT hO a _ (hP₂ t) (fun q => d.eF (w t q)) 1
  have hG : ∑ t, cs t * th t ∈ sec d.Xo₂ d.c₂ a n := Submodule.sum_mem _ fun t _ => by
    simpa using sec_mul d.Xo₂ d.c₂ 0 a 0 n (hcs t) (hth t)
  obtain ⟨f, hf, hev⟩ := exists_sec_of_moveInv d hlev _ hG (by
    intro s ρ ν hs hρ hmv k _ _ _ y y' hfr
    have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
    have hmb : ((d.l₂.M : ℕ) : 𝓞 E) ∈ d.l₂.Mb := by
      refine (Ideal.mul_le_inf.trans inf_le_left : d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ _) ?_
      rw [d.l₂.prod]; exact Ideal.mem_span_singleton_self _
    obtain ⟨g', hg'⟩ := s.inv d.l₂.M hM₂
    obtain ⟨σ, hσ⟩ := GlobalTheory.DatumInverseCharacter.exists_quot_equiv Dw hmb _ g' hg'
    rw [evR_sum_mul, evR_sum_mul]
    refine sum_values_eq d.nab₂ hnab Λ N hU hT hO a _ hP₂ (fun t q => d.eF (w t q))
      (fun t q => d.eF (w t fun b => σ.toEquiv.symm (q b))) 1 y _ _ _ _ (fun t => hval t k y)
      (fun t => GlobalTheory.ShortValMove.shortValAt_move GlobalTheory.firstFiveLaws.1 GlobalTheory.chartIndependence_unconditional E H Dw d.l₂ d.Xo₂
        d.c₂ d.nab₂ hnab k ρ.hom ν _ _ y y' hmv hfr σ.toEquiv hσ n a _ (hP₂ t) _ Λ 1 N _ (hval t k y')) fun q mo => ?_
    have e := hinv s ρ hs hρ σ.toEquiv hσ k y y' hfr.1 q mo
    simp only [map_mul d.eF] at e
    simp only [MvPolynomial.coeff_map]
    exact e)
  exact ⟨f, hf, fun k _ _ _ _ hk y y₂ ho => ⟨_, fun t => hval t k y₂, (hev k hk y y₂ ho).trans (evR_sum_mul _ _ _)⟩⟩

end GlobalTheory.ThetaSumDescent
