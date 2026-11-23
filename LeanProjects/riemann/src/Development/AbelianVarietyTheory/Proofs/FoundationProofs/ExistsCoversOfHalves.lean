import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSecCharVal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatLargeCoeff
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvdStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNthRootIdeleFinitePartOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterTrivialBaseFiniteIdelesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteIdeleCharAtDeterminantRootsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOneStatement

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TupleCover

set_option maxHeartbeats 1000000 in

theorem exists_xi (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (h : ChrEq c χ) (n : ℕ) (hn : 0 < n)
    (ho : χ.OrderDvd n) (hF : χ.TrivOn D.host.F) (ht : ∀ P, χ.TameAt P) :
    ∃ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ,
      (∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x →
        ((xi (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) = ((c x : Circle) : ℂ)) ∧
      (∀ N : ℕ, Odd N → (∀ P : HeightOneSpectrum (𝓞 D.host.E), (N : 𝓞 D.host.E) ∉ P.asIdeal → χ.UnrAt P) →
        ∀ g : GA D V, (∃ w ∈ intAE D, ((Matrix.GeneralLinearGroup.det (finHom V g) :
          (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = N • w) →
          xi (Matrix.GeneralLinearGroup.det (finHom V g)) = 1) ∧
      (∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1) ∧
      ∀ g : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V g)) ^ n = 1 := by
  have h1 : ∀ x, c x ^ n = 1 := GlobalTheory.T.heckeChar_eq_one_of_trivial_finitePartOne D (c ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (GlobalTheory.T.idelicCharacter_pow_eq_one_finiteIdeles_of_orderDvd D c χ h n ho)
  have h2 : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1 := fun x hx => by
    obtain ⟨y, rfl⟩ := GlobalTheory.T.exists_nthRoot_idele_finitePart_one D n hn x hx
    rw [map_pow, h1]
  have h3 : ∀ a, c (idF D a) = 1 := fun a => by
    let b : (AF D.host.F)ˣ := Units.map ((MonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.snd (Ainf D.host.F) (Af D.host.F))) a
    let b' : (AF D.host.F)ˣ := Units.map ((MonoidHom.inl (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.fst (Ainf D.host.F) (Af D.host.F))) a
    have e : a = b' * b := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    rw [e, map_mul, map_mul, h2 (idF D b') rfl, GlobalTheory.T.idelicCharacter_trivial_baseFiniteIdeles D c χ h hF b rfl, one_mul]
  obtain ⟨xi, hxi⟩ := GlobalTheory.T.exists_finiteIdeleChar_at_determinantRoots D V c h3 h2
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.Member.isDetRoot_laws D V
  refine ⟨xi, hxi, fun N hN hu g hg => ?_, fun γ hγ => ?_, fun g => ?_⟩
  · obtain ⟨x, hx⟩ := r1 g
    refine Units.ext ?_
    rw [hxi g x hx, GlobalTheory.T.character_at_detRoot_cong_one_odd_eq_one D V c N hN h3 h2 (GlobalTheory.T.tameHeckeChar_trivial_on_finiteUnits_cong_one D c χ h ht N hu) g x hx hg]
    rfl
  · obtain ⟨x, hx⟩ := r3 γ hγ
    refine Units.ext ?_
    rw [hxi γ _ hx, h.1.2]
    rfl
  · obtain ⟨x, hx⟩ := r1 g
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hxi g x hx, ← Circle.coe_pow, h1]
    rfl

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV

theorem exists_coeff_ge {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] : ∃ c : Coeff l, K ≤ c.F := by
  classical
  let b := Module.finBasis ℚ K
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.exists_coeff_containing E H l (Finset.univ.image fun i => (b i : ℂ)) (by
      intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
      exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom K.val)
  refine ⟨c₀, fun x hx => ?_⟩
  have e := congrArg K.val (b.sum_repr ⟨x, hx⟩)
  rw [map_sum] at e
  change _ = x at e
  rw [← e]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def, map_mul, eq_ratCast, map_ratCast]
  exact mul_mem (SubfieldClass.ratCast_mem c₀.F _) (hc₀ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))

variable {D : D7}

theorem iotaOK_and_frame (J : CoreJ D) (hJ : LawsJ J) (j : ℕ) (hj : InR D j) (σ : J.Q.c.F →+* ℂ) (hσ : GoodEmb J.Q.c σ)
    (V : HSp D) (hV : J.V j σ = V) (hr : V.rank = D.R.r) :
    IotaOK (J.Q.Dw j) V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ J.iota j) ∧
      ∀ τ : D.host.E →+* ℂ, τ (J.Q.H.rt : D.host.E) = J.Q.H.rt0 →
        gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (J.x₀ j σ τ) =
          Matrix.diagonal fun a : Fin D.R.r => ((sgn (J.Q.Dw j).q (a : ℕ) : ℝ) : ℂ) := by
  subst hV
  obtain ⟨hr₀, -, -, -, -, -, -, hemb, hisom, -⟩ := hJ.adPin j hj _ hσ
  refine ⟨GlobalTheory.XiFun.iotaOK_of_latIsom J.Q hJ.pins j hj _ (hJ.spaceW j hj _ hσ) _ hemb hisom, fun τ hτ => ?_⟩
  obtain ⟨hr', hW⟩ := hJ.modelW j hj _ hσ
  have hU := hJ.unf j hj _ hσ
  let k₀ := (J.dict j σ 1).1
  have h1 := hJ.familyUniformisationBasePointOrthogonal j hj _ hσ k₀ τ (((hU.2.1 k₀).2 τ).2 hτ)
  rwa [(hW k₀).1, (hU.2.1 k₀).1] at h1

set_option maxHeartbeats 1000000 in

theorem exists_fun {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {n r : ℕ} (d : DeltaDat Xo c n) (V : HSp D) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hio : IotaOK Dw V ι) (hpos : 1 ≤ Dw.p + Dw.q)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hlev : d.IsLev) (hA : d.l₂.A = 1) (hcl : FnAlgClosed d.Xo₂ d.c₂)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (h1 : ∀ g : GA D V, (∃ w ∈ intAE D, ((Matrix.GeneralLinearGroup.det (finHom V g) :
      (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = d.l₂.M • w) →
      xi (Matrix.GeneralLinearGroup.det (finHom V g)) = 1)
    (h2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
    (m : ℕ) (hm : 0 < m) (h3 : ∀ g : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V g)) ^ m = 1)
    (hz : zeta m ∈ c.F) :
    ∃ f : Rul d.Xo₂ d.c₂, ({ d with cδ := f } : DeltaDat Xo c n).IsLev ∧ f ^ m = 1 ∧
      ∃ (U₂ : Unf d.Xo₂ d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r),
        IsUnf U₂ ∧ (∀ k, ModelW V hr (U₂.X k)) ∧
        ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
          (F : FamilyUnif d.Xo₂ (((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)).comp
              (IntermediateField.inclusion d.c₂.le).toRingHom)
            (fun j => relab d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) (e j).1))
          (ik : U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U₂.X k).Λ)
          (th : ∀ k, (U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
          (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U₂ V hr dict₂ ι e F ik φ th x₀ ∧
          ∀ h γ : GA D V, MarkBy U₂ V hr dict₂ ι F ik φ h γ →
            rdU U₂ f (dict₂ h).1 (dict₂ h).2 =
              1 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ) := by
  have hσ : d.c₂.F.val.toRingHom = (inC c).comp (d.eF.symm : d.c₂.F →+* c.F) := RingHom.ext fun _ => rfl
  have hg₂ : GoodEmb d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) := by
    rw [← hσ]; rfl
  obtain ⟨C, hC, hCι, hCx⟩ := (exists_ctx D H Dw d.l₂ d.Xo₂ d.c₂ _ V r hr ι hio hpos hA hg₂).2.2 x₀ hx₀
  obtain ⟨Kf, hKf⟩ := (PrincLevel.exists_levelK_and_nhds D V d.l₂.M).1
  obtain ⟨un, dict, mu, -, -, hP⟩ := exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1 ⟨continuous_const, fun _ => rfl⟩
    (fun _ => rfl)
  obtain ⟨g, e, F, ik, φ, th, hth, hdu, hdl⟩ := hP.dictLaws
  obtain ⟨f, hf, hfm, -, hfx⟩ := GlobalTheory.XiFun.exists_sec_char_val D _ _ _ _ _ _ _ _ C.hr (C.unf un) dict C.ι g e F ik φ th C.x₀
    hC.iota hpos hA hg₂ hP.modelW hdl hdu.2.2.2.1 hcl xi
    (fun u _ hu => h1 u (by rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]; exact hu)) h2
    (fun h => ⟨⟨_, d.hF.symm ▸ GlobalTheory.NormOneChar.mem_of_pow_eq_one hm hz (by
      rw [← Units.val_pow_eq_pow_val, h3 h, Units.val_one])⟩, rfl⟩)
  have hfm' : f ^ m = 1 := hfm m h3
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, -, l9⟩ := hlev
  refine ⟨f, ⟨l1, l2, l3, l4, l5, l6, l7, hf, fun k _ _ _ y => ?_⟩, hfm', C.unf un, dict, hP.unf, hP.modelW,
      g, e, F, ik, φ, th, hth, ?_, fun h γ hmk => ?_⟩
  · exact GlobalTheory.XiFun.evR_ne_zero_of_pow _ _ f d.cδ m hm hfm' k y (l9 k y)
  · rw [← hCι, ← hCx]
    exact hdl
  · rw [one_mul]
    rw [← hCι] at hmk
    exact hfx h γ hmk

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem unrAt_of_not_mem {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {μ0 : T0}
    (hL : R.toLevCh.Is μ0) (t : T0) (N : ℕ) (hN : ∀ PP ∈ R.Q t, (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : (N : 𝓞 D.host.E) ∉ P.asIdeal) : (R.xiH t).UnrAt P := by
  by_contra h
  rcases (hL.Q_ram t P).1 h with h | ⟨P', hP', h⟩
  · exact hP (hN P h)
  · obtain ⟨c', hc', e⟩ := h _ (hN P' hP')
    have e' : c' = (N : 𝓞 D.host.E) := RingOfIntegers.ext (by
      rw [e]
      change star ((N : 𝓞 D.host.E) : D.host.E) = ((N : 𝓞 D.host.E) : D.host.E)
      rw [show ((N : 𝓞 D.host.E) : D.host.E) = (N : D.host.E) from map_natCast (algebraMap (𝓞 D.host.E) D.host.E) N,
        star_natCast])
    exact hP (e' ▸ hc')

def CoversAt (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (n : ℕ)
    (pd : T0 → ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H) (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) : Prop :=
  ∃ (dδ : T0 → DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ ((inC c').comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c'.F)) D.R.r)
    (dict₂ : ∀ t, GA D (Wc D i) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r)
    (xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ),
    (∀ t, (dδ t).pd = pd t ∧ (dδ t).I = I t ∧ (dδ t).l₂ = l₂ t) ∧
    CovPin (T.Q.Xo ((i : ℕ) + 1)) c' dδ ∧
    (∀ t, HalfIs R t T.Q.l.Mb (dδ t).I) ∧
    (∀ t, XiIs R i t (xi t)) ∧
    CXiVal (Wc D i) (rank_Wc i) (inC c') dδ U₂ dict₂ (iotaW T i) (T.x₀ ((i : ℕ) + 1) (sOv T.toCore c' hle)) xi ∧
    (∀ t k, ModelW (Wc D i) (rank_Wc i) ((U₂ t).X k)) ∧
    ∀ t, ∃ m : ℕ, 0 < m ∧ (dδ t).cδ ^ m = 1

set_option maxHeartbeats 1000000 in

theorem exists_covers_of_halves (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) {μ0 : T0} [Finite T0]
    (hT : LawsJ T) (hL : R.toLevCh.Is μ0) (i : Fin D.R.m) (n : ℕ)
    (pd : T0 → ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H)
    (hl : ∀ t, IsCoverLevel T.Q.l (pd t) (I t) (l₂ t)) (hH : ∀ t, HalfIs R t T.Q.l.Mb (I t)) :
    ∃ c₁ : Coeff T.Q.l, T.Q.c.F ≤ c₁.F ∧ D.what₂.embLL.toRatAlgHom.fieldRange ≤ c₁.F ∧
      ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F), c₁.F ≤ c'.F → CoversAt T R i n pd I l₂ c' hle := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by omega
  have hX : ∀ t, ∃ (Xo₂ : Moduli (T.Q.Dw ((i : ℕ) + 1)) (l₂ t)) (c₀ : Coeff (l₂ t)),
      ∀ c'' : Coeff (l₂ t), c₀.F ≤ c''.F → FnAlgClosed Xo₂ c'' := fun t => by
    obtain ⟨Xo₂⟩ := GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 _ _ (T.Q.Dw ((i : ℕ) + 1)) (l₂ t) hpos
    obtain ⟨c₀, -⟩ := exists_coeff_ge (l₂ t) ⊥
    obtain ⟨c₁, -, h⟩ := (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Xo₂ c₀ hpos).2
    exact ⟨Xo₂, c₁, h⟩
  choose Xo₂ c₀ hc₀ using hX
  choose m hm ho using hL.xi_fin
  choose xi hx1 hx2 hx3 hx4 using fun t =>
    exists_xi D (Wc D i) (R.xi t) (R.xiH t) (hL.xi t) (m t) (hm t) (ho t) (hL.xi_triv t) (hL.xi_tame t)
  have := T.Q.c.fin
  have : ∀ t, FiniteDimensional ℚ (c₀ t).F := fun t => (c₀ t).fin
  have : ∀ t, FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta (m t)}) := fun t =>
    IntermediateField.adjoin.finiteDimensional
      ((Complex.isPrimitiveRoot_exp (m t) (hm t).ne').isIntegral (hm t)).tower_top
  have : FiniteDimensional ℚ D.what₂.embLL.toRatAlgHom.fieldRange :=
    LinearEquiv.finiteDimensional (D.what₂.embLL.toRatAlgHom.equivFieldRange).toLinearEquiv
  obtain ⟨c₁, hc₁⟩ := exists_coeff_ge T.Q.l ((T.Q.c.F ⊔ D.what₂.embLL.toRatAlgHom.fieldRange) ⊔
    ⨆ t, ((c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)}))
  refine ⟨c₁, (le_sup_left.trans le_sup_left).trans hc₁, (le_sup_right.trans le_sup_left).trans hc₁, fun c' hle hc' => ?_⟩
  have hsup : ∀ t, (c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)} ≤ c'.F := fun t =>
    ((le_iSup (fun t => (c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)}) t).trans le_sup_right).trans (hc₁.trans hc')
  have hσ : GoodEmb T.Q.c (sOv T.toCore c' hle) := rfl
  obtain ⟨hio, hx₀⟩ := iotaOK_and_frame T hT _ hj _ hσ (Wc D i) (hT.spaceW _ hj _ hσ) (rank_Wc i)
  have key := fun t => by
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hl t
    have h0 : (c₀ t).F ≤ c'.F := le_sup_left.trans (hsup t)
    let c₂ : Coeff (l₂ t) := ⟨c'.F, c'.fin, c'.conj, h0 (c₀ t).zeta_mem, (c₀ t).le.trans h0⟩
    have hd := GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) c' hpos n (pd t) (I t) (l₂ t) (Xo₂ t) c₂ rfl
      l1 l2 l3 l4 l5
    have hd' : ∃ d : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n, d.pd = pd t ∧ d.I = I t ∧ d.l₂ = l₂ t ∧ d.IsLev ∧ d.l₂.A = 1 ∧
        FnAlgClosed d.Xo₂ d.c₂ ∧ ∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂ := by
      obtain ⟨⟨pd', I', l₂', Xo₂', c₂', hF, r, mm, nab, cδ, φ₀⟩, a1, a2, a3, e₁, e₂, -, a4, a5⟩ := hd
      refine ⟨_, a1, a2, a3, a4, a3 ▸ l6, ?_, a5⟩
      dsimp only at a3 e₁ e₂ ⊢
      subst a3
      obtain rfl := eq_of_heq e₁
      obtain rfl := eq_of_heq e₂
      exact hc₀ t c₂ h0
    exact hd'
  choose d a1 a2 a3 a4 a5 a6 a7 using key
  have hM : ∀ t, ∀ PP ∈ R.Q t, (((d t).l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun t PP hPP => by
    refine (hH t).2.1 PP hPP ?_
    have h1 : (((d t).l₂.M : ℕ) : 𝓞 D.host.E) ∈ (d t).l₂.Mb :=
      Ideal.mul_le_left ((d t).l₂.prod.ge (Ideal.mem_span_singleton_self _))
    rw [(a4 t).2.2.2.1, a2] at h1
    exact Ideal.mul_le_right h1
  choose f b1 b2 U₂ dict₂ b3 using fun t =>
    exists_fun (d t) (Wc D i) (rank_Wc i) (iotaW T i) _ hio hpos hx₀ (a4 t) (a5 t) (a6 t) (xi t)
      (hx2 t _ (d t).l₂.odd (unrAt_of_not_mem R hL t _ (hM t))) (hx3 t) (m t) (hm t) (hx4 t)
      (hsup t (le_sup_right (a := (c₀ t).F) (IntermediateField.mem_adjoin_simple_self ℚ _)))
  refine ⟨fun t => { d t with cδ := f t }, U₂, dict₂, xi, fun t => ⟨a1 t, a2 t, a3 t⟩, fun t => ⟨b1 t, a5 t, a7 t⟩,
    fun t => ?_, hx1, ⟨1, ⟨1, one_pos, one_pow 1⟩, b3⟩, fun t => (b3 t).2.1, fun t => ⟨m t, hm t, b2 t⟩⟩
  change HalfIs R t T.Q.l.Mb (d t).I
  rw [a2]
  exact hH t

theorem exists_covers (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) [Finite T0]
    (hT : LawsJ T) (hL : R.toLevCh.Is A.μ0) (hO : T.pb = R.C.P.pb) (hG : QGuard R) (i : Fin D.R.m) (n : ℕ) :
    ∃ (pd : T0 → ℕ) (l₂ : T0 → Level T.Q.H) (c₁ : Coeff T.Q.l),
      T.Q.c.F ≤ c₁.F ∧ D.what₂.embLL.toRatAlgHom.fieldRange ≤ c₁.F ∧
      ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F), c₁.F ≤ c'.F →
        CoversAt T R i n pd (fun t => coverHalf D (R.Q t)) l₂ c' hle := by
  choose pd l₂ h1 h2 using exists_half_of_laws T.toCore R hT.toLawsM hL hO hG
  exact ⟨pd, l₂, exists_covers_of_halves T R hT hL i n pd _ l₂ h1 h2⟩

theorem finite_tuples {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (h1 : R.tup_mu_off) (h2 : R.tup_mu_used) : Finite T0 := by
  refine Set.finite_univ_iff.1 (((R.twPl.finite_toSet.image R.mu).insert A.μ0).subset fun t _ => ?_)
  rcases h2 t with rfl | ⟨w, rfl⟩
  · exact Set.mem_insert _ _
  · by_cases hw : w ∈ R.twPl
    · exact Set.mem_insert_of_mem _ ⟨w, hw, rfl⟩
    · exact (h1 w hw).symm ▸ Set.mem_insert _ _

theorem exists_covers_of_char (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (hT : LawsJ T) (hR : R.Char F) (hO : T.pb = R.C.P.pb) (hG : QGuard R) (i : Fin D.R.m) :
    ∃ (pd : T0 → ℕ) (l₂ : T0 → Level T.Q.H) (c₁ : Coeff T.Q.l),
      T.Q.c.F ≤ c₁.F ∧ D.what₂.embLL.toRatAlgHom.fieldRange ≤ c₁.F ∧
      ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F), c₁.F ≤ c'.F →
        CoversAt T R i (Vc D i).rank pd (fun t => coverHalf D (R.Q t)) l₂ c' hle :=
  haveI := finite_tuples R hR.tup.mu_off hR.tup.mu_used
  exists_covers T R hT hR.lev hO hG i _

end GlobalTheory.TupleCover
