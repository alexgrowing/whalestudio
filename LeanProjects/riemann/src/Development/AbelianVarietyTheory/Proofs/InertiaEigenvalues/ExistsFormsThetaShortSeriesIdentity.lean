import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqRootIdentity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddAllOfThetaSumOnCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisIntegralCoords
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefMapSmulMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PureTensorOTransSumLin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsUnf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries.SerId

set_option maxHeartbeats 4000000 in

theorem thetaSum_value_emb : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ), (∀ τ, relab c σ τ = τ) → GoodEmb c σ → ∀ (U : Unf Xo c σ r), l.A = 1 → Odd r → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW s f₀ → ∀ (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (mu : GA D W → ℂ) (cc : U.Comp → ℂ), IsDict U W hr dict ι x₀ → FrameTie U W hr x₀ s BW → CcIs θ V W hr U dict mu x₀ om f₀ cc → ∀ (d : DeltaDat Xo c V.rank), d.IsLev → d.l₂.A = 1 → (∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ e : AE D, IsHalfIdem d.l₂ e → ∀ (bad N : ℕ) (h : GA D V) (Λ : GenLat D.host.E V.rank) (e' : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), d.l₂.M ∣ bad → IsIdemSum e' Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC V → SuppAt e' V h → IsDetAt e' V h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (GlobalTheory.ExportSeries.finPt V h)) → Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (lt : LtN Dw V.rank ≃ FVar D W.rank V.rank) (a : (D.host.E →+* ℂ) × ℕ → ℕ), IsLetters Dw lt → Dom a V.rank → ∀ (T : Type) [Fintype T] (w : T → (Fin V.rank → LevQ Dw d.l₂) → c.F) (P : T → MvPolynomial (LtN Dw V.rank) c.F) (f : Rul Xo c), (∀ t, P t ∈ HHa Dw.mult V.rank c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → IsThetaSum d (fun _ => 1) w Λ N P f → ∀ g : GA D W, ∑ t, thetaKO om h g (pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) BW (transSum ψ V W d.l₂ ι e f₀ (fun q => σ (w t q))) (MvPolynomial.rename lt (MvPolynomial.map σ (P t)))) = (-1) ^ degA Dw a * clsScal χW y Λ r * ((lieFac Dw (xiR D) a : ℂ) * (cc (dict g).1 * mu g * rdU U f (dict g).1 (dict g).2)) := by
  intro D H Dw l Xo c r σ hrel hσ U hA hodd ψ θ V W χV χW om ΛV ΛW s f₀ hVP hr dict ι x₀ BW mu cc hD hF hcc d hlev hA₂
    hnab e he bad N h Λ e' Ps y hbad he' hPs hh hs hy hΛ hun hT hN lt a hlt hDom T _ w P f hPH hth g
  have := GlobalTheory.AdTh.ShortSeries.finite_levQ Dw d.l₂
  letI : Fintype (Fin V.rank → LevQ Dw d.l₂) := Fintype.ofFinite _
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI : Algebra d.c₂.F ℂ := (σ.comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  obtain ⟨hU, hiota, hMod, hX0, g0, e0, F0, ik, φ0, th0, hth0, hDL⟩ := hD
  have hrt : (H.rt : D.host.E) = D.host.sqrtMinusD := hiota.rt
  have h1 : 1 ≤ r := hodd.pos
  have hθ : IsInfFam θ := hVP.1.inf
  have hmk : ∀ (Wt : UW (Formalism.L2.PjFree.Unf.ofPj U)) (k : GA D W),
      IsONFr (U.X (dict k).1) (dict k).2 ∧
      ∃ γ, AtComp θ W hr U.X dict x₀ k γ ∧ MarkAd l W hr ι (γ * k) (Wt.mark (dict k).1) :=
    fun Wt k => by
      obtain ⟨k1, γ, k2, k3, -⟩ := GlobalTheory.AdTh.dict_atComp_markAd D H Dw l Xo c σ r U hσ hU h1 hA
        θ W hr dict ι g0 e0 F0 ik φ0 th0 x₀ hθ hMod hX0 hth0 hDL Wt k
      exact ⟨k1, γ, k2, k3⟩
  obtain ⟨hx, g', Dc, γ, mk, v, ϑ, κ', B, hat, hsd, hm, hBm, hma, hϑ, hv, hκ, hrd⟩ :=
    GlobalTheory.PtId.exists_point U hσ hU h1 hA θ V W hr dict ι x₀ hmk a hDom mu om f₀ cc hcc g
  obtain ⟨hγ, hΛk, hfr⟩ := hat

  have hrpq : r = Dw.p + Dw.q := hU.1
  have hp0 : (U.X (dict g).1).p0 = Dw.q := (hU.2.1 _).1
  have hpq : Dw.p ≠ Dw.q := fun e0 => by
    obtain ⟨m, hm'⟩ := hodd
    omega

  obtain ⟨mk₂, hm₂, ha₂, hov⟩ := GlobalTheory.AdMark.exists_marking D H Dw l d.l₂ W r hr ι hiota.emb
    (hlev.2.1 ▸ dvd_mul_right _ _) (hlev.2.2.2.1 ▸ Ideal.mul_le_left) (γ * g)
  rw [hΛk] at hm₂ hov
  have hM : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  obtain ⟨Y, hY⟩ := (GlobalTheory.Dict.DualMark.dual_marking _ _ _ d.l₂ _ _ _ mk₂ _ hsd hm₂
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 V.rank N hN.1.pos
  have halg : ∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t := fun t => by
    simp [RingHom.algebraMap_toAlgebra]
  obtain ⟨y₂, B₂, hov₂, hB₂, hrd₂⟩ := GlobalTheory.Dict.MarkLift.exists_lift_marked _ _ _ _ _ c _ d halg hlev hA hA₂
    (fun e0 => absurd e0 hpq) _ g' _ Dc.bas Dc.idx Dc.e _ _ _ B Dc.sympl hx hsd mk mk₂ hm hBm hm₂ (hov mk hm.mem hma)
  obtain ⟨vt, hvt, hev⟩ := hth ℂ halg _ y₂ hov₂

  have hrdU : rdU U f (dict g).1 (dict g).2 =
      evR Xo c f (unC (Formalism.L2.PjFree.Unf.ofPj U) (dict g).1 ⟨(dict g).2, hx⟩) := dif_pos hx

  have hcsv : evR d.Xo₂ d.c₂ 1 y₂ = 1 := evalAt_one _ _ y₂
    (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange _ H Dw d.l₂ d.Xo₂ d.c₂ ℂ y₂)
  obtain ⟨_, hnab'⟩ := id hnab
  have hVset : Λ.La ∈ Vset D.host.E V.rank d.l₂.M := (GlobalTheory.Dict.GenLatCmp.genLat_vset _ _ Λ.La).2.1 d.l₂.M N hM hun hT hN
  have hcomp : (algebraMap d.c₂.F ℂ).comp (d.eF : c.F →+* d.c₂.F) = σ := RingHom.ext fun t => halg t
  have hvtv : ∀ t, vt t = (((Λ.mIdx N r : ℂ))⁻¹ * ((Nat.card (Fin V.rank → LevQ Dw d.l₂) : ℂ))⁻¹ * (Λ.zCard N r : ℂ)) * κ' *
      thP _ Dc.hr Dc.bas Dc.idx (gphi _ Dc.bas (H.w0 : D.host.E) Λ.La (U.X (dict g).1).Λ v (fun q => σ (w t q)) Y)
        (MvPolynomial.rename Dc.eL (MvPolynomial.map σ (P t))) (dict g).2 := fun t => by
    have hP2 := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover _ H Dw l Xo c V.rank d).2 a _ (hPH t)
    have e1 := GlobalTheory.Dict.shortValAt_eq_thP GlobalTheory.ChartFree.chartIndep _ H Dw d.l₂ d.Xo₂ d.c₂ r g' _ Dc.bas Dc.idx Dc.e _ _ y₂ B₂
      Dc.sympl hx hsd Dw.p V.rank Dc.hr Dc.eL hrpq hVP.1.even Dc.dir_eq d.nab₂ hnab' ϑ v κ' (hrd₂ ϑ hϑ) hv hκ mk₂ hm₂ hB₂
      Λ.La hVset N hN Y hY a _ hP2 (fun q => d.eF (w t q)) 1 (vt t) (hvt t)
    rw [e1, MvPolynomial.map_map, hcomp]
    simp only [halg, map_mul, map_inv₀, map_natCast, map_one, inv_one, one_mul]
    rfl

  obtain ⟨vr, hvr⟩ := GlobalTheory.PtId.exists_isVarOf V W hr _ (hMod (dict g).1) Dw.p Dc.hr
  have hΨ : ∀ τ : D.host.E →+* ℂ, τ ∈ (U.X (dict g).1).Ψ ↔ τ (H.rt : D.host.E) = H.rt0 :=
    (hU.2.1 _).2
  have hne : ∀ s t : D.what₂.Tau, tauE D s ≠ conjEmb (tauE D t) := fun s t h0 => by
    have hs' := (hΨ (tauE D s)).1 (((hMod (dict g).1).psi _).2 ⟨s, rfl⟩)
    have ht' := (hΨ (tauE D t)).1 (((hMod (dict g).1).psi _).2 ⟨t, rfl⟩)
    have h1 := RingHom.congr_fun h0 (H.rt : D.host.E)
    change _ = starRingEnd ℂ (tauE D t _) at h1
    rw [hs', ht'] at h1
    have him : H.rt0.im = 0 := by
      have := congrArg Complex.im h1
      simp at this
      linarith
    have hre := congrArg Complex.re H.sqrt_neg_disc_sq
    simp [pow_two, him] at hre
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg H.rt0.re]
  have hvl : ∀ ℓ, vr (Dc.eL ℓ) = lt ℓ := fun ℓ => by
    have hm' : ∀ τ, τ ∉ (U.X (dict g).1).Ψ →
        Dw.mult τ ≤ (U.X (dict g).1).p0 := fun τ hτ => by
      unfold Datum.mult
      rw [if_neg fun h => hτ ((hΨ τ).2 h), hp0]
    obtain ⟨h1', h2'⟩ := GlobalTheory.AdTh.Dic.letter Dc hrel hm' ℓ
    obtain ⟨g1, g2, g3⟩ := hvr (Dc.eL ℓ)
    refine AddValue.fvar_eq (τ := ℓ.1) (i := ℓ.2.1) (p := Dw.p) (j := ℓ.2.2) ⟨g2.trans h1', ?_⟩ (hlt ℓ) hne
    rcases h2' with ⟨k, e1, e2, e3⟩ | ⟨k, e1, e2, e3⟩
    · rw [e1] at g3
      exact Or.inl ⟨e2.trans g1, g3.trans e3⟩
    · rw [e1] at g3
      refine Or.inr ⟨by rw [← g1]; exact e2, g3.trans ?_⟩
      show Dw.p + (k : ℕ) = _
      rw [e3]

  have hON : IsONFr (U.X (dict g).1) (fun τ => x₀ τ.1) := fun τ => hX0 _ τ.1 τ.2
  have hψ : IsStdChar D ψ (-1) := hVP.1.weil.std
  have hf₀ : IsThetaFunO ψ V W f₀ := hVP.2.2.2.2.2.2.2.2.2.theta
  have hmove : ∀ F, IsThetaFunO ψ V W F → thetaKO om h g F = thetaKO om h (γ * g) F := fun F hF' => by
    have e1 : ((h, γ * g) : GA D V × GA D W) = (1, γ) * (h, g) := by simp
    rw [thetaKO, thetaKO, e1, map_mul]
    exact (hVP.1.weil.om_aut 1 (one_mem _) γ hγ _ (hVP.1.weil.om_pres _ F hF')).symm
  have hterm : ∀ t, thetaKO om h g (pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) BW
      (transSum ψ V W d.l₂ ι e f₀ (fun q => σ (w t q))) (MvPolynomial.rename lt (MvPolynomial.map σ (P t)))) =
      (-1) ^ degA Dw a * ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ degA Dw a * (cc (dict g).1 * mu g * κ') *
        (((χW y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf
          Λ.La.toAddSubgroup).index : ℝ) ^ r) : ℂ)) * ((Nat.card (Fin V.rank → LevQ Dw d.l₂) : ℂ))⁻¹ *
        thP _ Dc.hr Dc.bas Dc.idx (gphi _ Dc.bas (H.w0 : D.host.E) Λ.La (U.X (dict g).1).Λ v (fun q => σ (w t q)) Y)
          (MvPolynomial.rename Dc.eL (MvPolynomial.map σ (P t))) (dict g).2 := fun t => by
    have hren : MvPolynomial.rename lt (MvPolynomial.map σ (P t)) =
        MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map σ (P t))) := by
      erw [MvPolynomial.rename_rename]
      exact congrArg (fun φ => MvPolynomial.rename φ _) (funext fun ℓ => (hvl ℓ).symm)
    have hH := hPH t
    have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map σ (P t))).IsHomogeneous (degA Dw a) :=
      ((GlobalTheory.PtId.isHomogeneous_of_rowDeg _ _ _ _ hH.2.2).map _).rename_isHomogeneous
    have hthF := GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ (fun _ => 1) (fun _ => 1) s BW
      (AddValue.theta_transSum hψ V W d.l₂ ι e hf₀ (fun q => σ (w t q))) (MvPolynomial.rename lt (MvPolynomial.map σ (P t)))
    rw [hmove _ hthF, hren]
    refine (GlobalTheory.T.thetaKernel_translateSum_eq_classicalShortSeries D H Dw ψ θ V W χV χW om ΛV ΛW s f₀ hVP ι hiota.emb hrt d.l₂ e he r g' Dw.p hr _
      Dc.hr Dc.bas Dc.idx (fun τ => x₀ τ.1) vr BW (hMod _) Dc.sympl hON (hF _).1 ((hF _).2 Dc.hr) hvr bad N h (γ * g) Λ mk₂
      e' Ps y hbad he' hPs hh hs hy hΛ hT hN ha₂ Y (by rw [hΛk]; exact hY) v (cc (dict g).1 * mu g * κ')
      (by rw [hΛk]; exact hv) (by rw [← hfr]; exact hrd) _ _ (degA Dw a) hhom).trans ?_
    rw [hΛk, ← hfr]

  have hxi : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hm0 : (Λ.mIdx N r : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (GlobalTheory.ClassScalarValue.mIdx_ne_zero Λ r (by have := hN.1.pos; omega))
  have hsq := Real.mul_self_sqrt (show (0 : ℝ) ≤ ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ r) by positivity)
  have hz : (Λ.zCard N r : ℂ) = (Λ.mIdx N r : ℂ) * (((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ r) : ℝ) : ℂ) * ((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ r) : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_mul, hsq, GlobalTheory.ClassScalarValue.zCard_eq Λ N r hN.2.2]
    push_cast
    rfl
  have hS := AddValue.sq_root_identity _ _ _ hm0 hz
  have hdeg : GlobalTheory.PtId.degW Dw a = degA Dw a := rfl
  rw [hrdU, hev, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hterm t, hcsv, hvtv t, GlobalTheory.AdTh.SerCore.lieFac_eq_sqrt_pow Dw hxi a, clsScal, hdeg]
  conv_lhs => rw [hS]
  push_cast
  ring

theorem exists_expansion (F : IntermediateField ℚ ℂ) [NumberField F] (σ : F →+* ℂ) (la : HeightOneSpectrum (𝓞 F))
    (O : Subring ℂ) (hO : ValRing σ la O) {T : Type} (r : T → ℕ) (n : ℕ) (cj : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    {I : Type} [Finite I] (u : I → ℂ) (hu : ∀ q, u q ∈ O) (Q : MvPolynomial (Letter T r n) ℂ) (hQ : Q ∈ HHa r n ℂ cj isX a)
    (hQO : ∀ mo, Q.coeff mo ∈ O) :
    ∃ (m : ℕ) (β : Fin m → ℂ) (P : Fin m → I → MvPolynomial (Letter T r n) F), (∀ k, β k ∈ O) ∧
      (∀ k q, P k q ∈ HHa r n F cj isX a ∧ ∀ mo, la.valuation F ((P k q).coeff mo) ≤ 1) ∧
      ∀ q, ∑ k, β k • MvPolynomial.map σ (P k q) = u q • Q := by
  haveI : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq F (algebraMap F ℂ) σ
  obtain ⟨m, β, lam, hβ, hlam⟩ := exists_basis_integral_coords F la (O.comap (τ : ℂ →+* ℂ))
    (fun x hx => by
      show τ (algebraMap F ℂ x) ∈ O
      rw [hτ]
      exact hO x hx)
    ((fun x : I × Q.support => τ.symm (u x.1 * Q.coeff x.2.1)) '' Set.univ) (Set.finite_univ.image _) (by
      rintro _ ⟨x, -, rfl⟩
      show τ (τ.symm _) ∈ O
      rw [τ.apply_symm_apply]
      exact mul_mem (hu _) (hQO _))
  have hlam' : ∀ q mo, τ.symm (u q * Q.coeff mo) = ∑ k, β k * (lam k (τ.symm (u q * Q.coeff mo)) : ℂ) ∧
      ∀ k, la.valuation F (lam k (τ.symm (u q * Q.coeff mo))) ≤ 1 := fun q mo => by
    by_cases hmo : mo ∈ Q.support
    · exact hlam _ ⟨(q, ⟨mo, hmo⟩), trivial, rfl⟩
    · simp [MvPolynomial.notMem_support_iff.1 hmo]
  choose P hP hPc using fun (k : Fin m) (q : I) => HHa_coefLin T r n cj isX a F (lam k)
    (MvPolynomial.map (τ.symm : ℂ →+* ℂ) (u q • Q)) (map_mem_HHa r n _ τ.symm.surjective cj isX a _
      (GlobalTheory.PtId.mem_HHa_of_span _ _ _ _ _ _ (Submodule.smul_mem _ _ (Submodule.subset_span hQ))))
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_smul, smul_eq_mul, RingHom.coe_coe] at hPc
  refine ⟨m, fun k => τ (β k), P, hβ, fun k q => ⟨hP k q, fun mo => by rw [hPc]; exact (hlam' q mo).2 k⟩, fun q => ?_⟩
  ext mo
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, hPc]
  have h := congrArg τ (hlam' q mo).1
  rw [τ.apply_symm_apply, map_sum] at h
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h.symm
  rw [map_mul τ (β k), ← hτ]
  rfl

theorem exists_family {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hU : IsUnf U)
    (h1 : 1 ≤ r) : ∃ U' : ∀ σ' : c.F →+* ℂ, Unf Xo c σ' r, U' σ = U ∧ ∀ σ', GoodEmb c σ' → IsUnf (U' σ') := by
  obtain rfl : r = Dw.p + Dw.q := hU.1
  have key : ∀ σ' : c.F →+* ℂ, ∃ U₁ : Unf Xo c σ' (Dw.p + Dw.q), GoodEmb c σ' → IsUnf U₁ := fun σ' => by
    by_cases hσ : GoodEmb c σ'
    · obtain ⟨U₀, hU₀⟩ := GlobalTheory.IsUnfEx.exists_isUnf GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.QNorm.hasseNormSt
        GlobalTheory.abelianSchemeLaws_all.1.secBaseChange GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c σ' h1 hσ
      exact ⟨U₀.toPj, fun _ => hU₀⟩
    · exact ⟨⟨Empty, fun k => k.elim, fun k => k.elim⟩, fun h => absurd h hσ⟩
  choose U₁ hU₁ using key
  refine ⟨Function.update U₁ σ U, Function.update_self _ _ _, fun σ' hσ' => ?_⟩
  by_cases h : σ' = σ
  · subst h
    rw [Function.update_self]
    exact hU
  · rw [Function.update_of_ne h]
    exact hU₁ σ' hσ'

set_option maxHeartbeats 2000000 in

theorem exists_forms_of_transSum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ), (∀ τ, relab c σ τ = τ) → GoodEmb c σ → ∀ (U : Unf Xo c σ r), l.A = 1 → Odd r → ∀ (hr : W.rank = r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (mu : GA D W → ℂ) (cc : U.Comp → ℂ), IsDict U W hr dict ι x₀ → FrameTie U W hr x₀ sW BW → CcIs θ V W hr U dict mu x₀ om f₀ cc → ∀ e : AE D, IsHalfIdem l e → ∀ (bad N : ℕ) (h : GA D V) (Λ : GenLat D.host.E V.rank) (e' : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), l.M ∣ bad → IsIdemSum e' Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC V → SuppAt e' V h → IsDetAt e' V h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (GlobalTheory.ExportSeries.finPt V h)) → Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (lt : LtN Dw V.rank ≃ FVar D W.rank V.rank) (wa : (D.host.E →+* ℂ) × ℕ → ℕ), IsLetters Dw lt → Dom wa V.rank → LastPos Dw wa → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ O : Subring ℂ, ValRing σ la O → ∀ u : (Fin V.rank → LevQ Dw l) → ℂ, (∀ q, u q ∈ O) → ∀ Q ∈ HHa Dw.mult V.rank ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)), (∀ mo, Q.coeff mo ∈ O) → ∃ (m : ℕ) (β : Fin m → ℂ) (f : Fin m → Rul Xo c), (∀ k, β k ∈ O ∧ f k ∈ sec Xo c wa V.rank ∧ rdU U (f k) ∈ Formalism.L2.Pj.holSub0 U.X (laU U wa V.rank) ∧ GlobalTheory.GoodPts.BddAll Xo c la (((Λ.mIdx N (Dw.p + Dw.q) * Nat.card (Fin V.rank → LevQ Dw l) : ℕ) : c.F) * ((2 * NumberField.discr D.host.E * N : ℤ) : c.F) ^ degA Dw wa) (f k)) ∧ ∀ g : GA D W, thetaKO om h g (stdF ψ θ V W sW BW (transSum ψ V W l ι e f₀ u) (MvPolynomial.rename lt Q)) = (-1) ^ degA Dw wa * clsScal χW y Λ r * ∑ k, β k * ((lieFac Dw (xiR D) wa : ℂ) * (cc (dict g).1 * mu g * rdU U (f k) (dict g).1 (dict g).2)) := by
  intro D ψ θ V W χV χW om ΛV ΛW s f₀ hP H Dw l Xo c r σ hrel hσ U hA hodd hr dict ι x₀ BW mu cc hD hF hcc e he bad N h Λ e' Ps y
    hbad he' hPs hh hs hy hΛ hun hT hN lt a hlt hDom hLast la p hp hpl hgood O hO u hu Q hQ hQO
  haveI := GlobalTheory.AdTh.ShortSeries.finite_levQ Dw l
  letI : Fintype (Fin V.rank → LevQ Dw l) := Fintype.ofFinite _
  obtain ⟨U', rfl, hU'⟩ := exists_family U hD.1 hodd.pos
  obtain ⟨d, -, -, hl, -, -, -, hlev, hnab⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev _ H Dw l Xo c (hD.1.1 ▸ hodd.pos) V.rank 1 ⊤
    l Xo c rfl ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm (top_sup_eq _)
  obtain ⟨pd, I, l₂, Xo₂, c₂, hF₂, rr, mm, nab, cδ, φδ⟩ := d
  obtain rfl : l = l₂ := hl.symm
  set d : DeltaDat Xo c V.rank := ⟨pd, I, l, Xo₂, c₂, hF₂, rr, mm, nab, cδ, φδ⟩ with hd
  obtain ⟨m, β, Pk, hβ, hPk, hsum⟩ := exists_expansion c.F σ la O hO _ _ _ _ _ u hu Q hQ hQO
  obtain ⟨_, hnab'⟩ := id hnab
  have hcs : ∀ _ : Fin V.rank → LevQ Dw l, (1 : Rul d.Xo₂ d.c₂) ∈ sec d.Xo₂ d.c₂ 0 0 ∧ (1 : Rul d.Xo₂ d.c₂) ^ (1 + 1) = 1 :=
    fun _ => ⟨(GlobalTheory.ThetaSumDescent.secZero d.Xo₂ d.c₂).one_mem, one_pow _⟩
  have hinv : ∀ k, GlobalTheory.ThetaSumDescent.SumInv d (fun _ : Fin V.rank → LevQ Dw l => 1)
      (fun t q => if q = t then 1 else 0) (Pk k) := fun k => by
    intro t ρ ht hρ σq hσq K _ _ _ z z' hz q mo
    have h1 : ∀ x, σq x = x := fun x => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hσq]
      exact (Submodule.Quotient.eq _).2 (ht.2.1 x)
    have h2 : (fun b => σq.symm (q b)) = q := funext fun b => by rw [Equiv.symm_apply_eq, h1]
    have h3 : ∀ z : FrPt d.Xo₂ d.c₂ K, evR d.Xo₂ d.c₂ 1 z = 1 := fun z => map_one (GlobalTheory.ThetaSumDescent.evHom z)
    rw [h2]
    simp only [h3]
  choose f hf hval using fun k => (GlobalTheory.ThetaSumDescent.exists_cusp_thetaSum _ H Dw l Xo c r U' hodd.pos hU' hA a
    V.rank N d Λ _ (fun _ : Fin V.rank → LevQ Dw l => 1) 1 (fun t q => if q = t then 1 else 0) (Pk k)
    hDom hLast hlev hA hnab' hun hT hN one_pos hcs (fun t => (hPk k t).1) (hinv k))
  have hval' : ∀ k, IsThetaSum d (fun _ : Fin V.rank → LevQ Dw l => 1) (fun t q => if q = t then 1 else 0) Λ N
      (Pk k) (f k) := fun k => (hval k).1
  refine ⟨m, β, f, fun k => ⟨hβ k, (hf k).1, ⟨((mem_cusp Xo c U' a _ _).1 (hf k)).2 σ hσ, rdU_mem_offZero _ _⟩, ?_⟩, fun g => ?_⟩
  · let en := (Fintype.equivFin (Fin V.rank → LevQ Dw l)).symm
    refine GlobalTheory.CoverBound.bddAll_of_theta_sum_on_cover _ H Dw l Xo c r U' hU' la p hp hpl hgood a V.rank (degA Dw a) N _ d Λ
      (fun _ => 1) 1 (fun t q => if q = en t then 1 else 0) (fun t => Pk k (en t)) (f k) hDom hlev hnab' hun hT hN
      one_pos (fun t => hcs (en t)) (fun t q => ?_) (fun t => ⟨(hPk k _).1.1, ?_, (hPk k _).2⟩) (hf k) ?_
    · split_ifs <;> simp
    · exact GlobalTheory.PtId.isHomogeneous_of_rowDeg _ _ _ _ (hPk k _).1.2.2
    · intro K _ _ _ _ hk z z₂ hz
      obtain ⟨v, h1, h2⟩ := hval' k K hk z z₂ hz
      exact ⟨fun t => v (en t), fun t => h1 (en t), h2.trans (en.sum_comp fun t => evR d.Xo₂ d.c₂ 1 z₂ * v t).symm⟩
  have hv := fun k => thetaSum_value_emb D H Dw l Xo c r σ hrel hσ (U' σ) hA hodd ψ θ V W χV χW om ΛV ΛW s f₀ hP hr dict ι x₀ BW
    mu cc hD hF hcc d hlev hA hnab e he bad N h Λ e' Ps y hbad he' hPs hh hs hy hΛ hun hT hN lt a hlt hDom _ _ (Pk k) (f k)
    (fun t => (hPk k t).1) (hval' k) g
  rw [Finset.mul_sum, Finset.sum_congr rfl fun k _ => mul_left_comm _ (β k) _,
    Finset.sum_congr rfl fun k _ => congrArg (β k * ·) (hv k).symm, stdF,
    pureTensorO_transSum_lin D H Dw ψ θ V W χV χW om ΛV ΛW s f₀ hP ι l e he]
  simp only [apply_ite σ, map_one, map_zero, Finset.mul_sum]
  rw [Finset.sum_comm, thetaKO, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← map_smul, ← map_smul, ← hsum]
  simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

end GlobalTheory.LevelSeries.SerId

end
