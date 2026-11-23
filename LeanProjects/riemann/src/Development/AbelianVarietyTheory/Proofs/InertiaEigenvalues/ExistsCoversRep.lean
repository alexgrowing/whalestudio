import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFirstOfSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneCover

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV GlobalTheory.TupleCover

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem exists_fun_cover {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {n r : ℕ} (d : DeltaDat Xo c n) (V : HSp D) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hio : IotaOK Dw V ι) (hpos : 1 ≤ Dw.p + Dw.q)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hA : d.l₂.A = 1) :
    ∃ (U₂ : Unf d.Xo₂ d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r),
      IsUnf U₂ ∧ (∀ k, ModelW V hr (U₂.X k)) ∧
      ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
        (F : FamilyUnif d.Xo₂ (((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)).comp
            (IntermediateField.inclusion d.c₂.le).toRingHom)
          (fun j => relab d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) (e j).1))
        (ik : U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U₂.X k).Λ)
        (th : ∀ k, (U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
        (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U₂ V hr dict₂ ι e F ik φ th x₀ ∧
        ∀ (_ : d.IsLev) (_ : FnAlgClosed d.Xo₂ d.c₂) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
          (_ : ∀ g : GA D V, (∃ w ∈ intAE D, ((Matrix.GeneralLinearGroup.det (finHom V g) :
            (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = d.l₂.M • w) →
            xi (Matrix.GeneralLinearGroup.det (finHom V g)) = 1)
          (_ : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
          (m : ℕ) (_ : 0 < m) (_ : ∀ g : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V g)) ^ m = 1)
          (_ : zeta m ∈ c.F),
          ∃ f : Rul d.Xo₂ d.c₂, ({ d with cδ := f } : DeltaDat Xo c n).IsLev ∧ f ^ m = 1 ∧
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
  refine ⟨C.unf un, dict, hP.unf, hP.modelW, g, e, F, ik, φ, th, hth, ?_, ?_⟩
  · rw [← hCι, ← hCx]
    exact hdl
  intro hlev hcl xi h1 h2 m hm h3 hz
  obtain ⟨f, hf, hfm, -, hfx⟩ := GlobalTheory.XiFun.exists_sec_char_val D _ _ _ _ _ _ _ _ C.hr (C.unf un) dict C.ι g e F ik φ th C.x₀
    hC.iota hpos hA hg₂ hP.modelW hdl hdu.2.2.2.1 hcl xi
    (fun u _ hu => h1 u (by rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]; exact hu)) h2
    (fun h => ⟨⟨_, d.hF.symm ▸ GlobalTheory.NormOneChar.mem_of_pow_eq_one hm hz (by
      rw [← Units.val_pow_eq_pow_val, h3 h, Units.val_one])⟩, rfl⟩)
  have hfm' : f ^ m = 1 := hfm m h3
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, -, l9⟩ := hlev
  refine ⟨f, ⟨l1, l2, l3, l4, l5, l6, l7, hf, fun k _ _ _ y => ?_⟩, hfm', fun h γ hmk => ?_⟩
  · exact GlobalTheory.XiFun.evR_ne_zero_of_pow _ _ f d.cδ m hm hfm' k y (l9 k y)
  · rw [one_mul]
    rw [← hCι] at hmk
    exact hfx h γ hmk

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem halfIs_of_eq {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {t t' : T0}
    (e : R.Q t' = R.Q t) {Mb I : Ideal (𝓞 D.host.E)} (h : HalfIs R t' Mb I) : HalfIs R t Mb I := by
  unfold HalfIs at h ⊢
  rwa [e] at h

theorem xi_pow_eq_one (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (h : ChrEq c χ) (n : ℕ)
    (ho : χ.OrderDvd n) (x : (AE D)ˣ) : c x ^ n = 1 :=
  GlobalTheory.T.heckeChar_eq_one_of_trivial_finitePartOne D (c ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (GlobalTheory.T.idelicCharacter_pow_eq_one_finiteIdeles_of_orderDvd D c χ h n ho) x

def CoversRep (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (n : ℕ)
    (pd : T0 → ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H) (rep : T0 → T0) (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) : Prop :=
  ∃ (d : T0 → DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n)
    (U : ∀ t, Unf (d t).Xo₂ (d t).c₂ ((inC c').comp ((d t).eF.symm : (d t).c₂.F →+* c'.F)) D.R.r)
    (dict : ∀ t, GA D (Wc D i) → Σ k, Frame ((U t).X k).Ψ D.R.r)
    (f : ∀ t, Rul (d (rep t)).Xo₂ (d (rep t)).c₂)
    (xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ),
    (∀ t, (d t).pd = pd t ∧ (d t).I = I t ∧ (d t).l₂ = l₂ t) ∧
    CovPin (T.Q.Xo ((i : ℕ) + 1)) c' (fun t => ({ d (rep t) with cδ := f t } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n)) ∧
    (∀ t, HalfIs R t T.Q.l.Mb (d (rep t)).I) ∧
    (∀ t, XiIs R i t (xi t)) ∧
    CXiVal (Wc D i) (rank_Wc i) (inC c') (fun t => ({ d (rep t) with cδ := f t } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n))
      (fun t => U (rep t)) (fun t => dict (rep t)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) (sOv T.toCore c' hle)) xi ∧
    (∀ t k, ModelW (Wc D i) (rank_Wc i) ((U (rep t)).X k))

set_option maxHeartbeats 2000000 in

theorem exists_covers_rep (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) {μ0 : T0} [Finite T0]
    (hT : LawsJ T) (hL : R.toLevCh.Is μ0) (i : Fin D.R.m) (n : ℕ)
    (pd : T0 → ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H)
    (hl : ∀ t, IsCoverLevel T.Q.l (pd t) (I t) (l₂ t)) (hH : ∀ t, HalfIs R t T.Q.l.Mb (I t))
    (rep : T0 → T0) (hrep : ∀ t, R.Q (rep t) = R.Q t) :
    ∃ c₁ : Coeff T.Q.l, T.Q.c.F ≤ c₁.F ∧ D.what₂.embLL.toRatAlgHom.fieldRange ≤ c₁.F ∧
      (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ c₁.F) ∧
      ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F), c₁.F ≤ c'.F → CoversRep T R i n pd I l₂ rep c' hle := by
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
  have hsup₁ : ∀ t, (c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)} ≤ c₁.F := fun t =>
    ((le_iSup (fun t => (c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)}) t).trans le_sup_right).trans hc₁
  refine ⟨c₁, (le_sup_left.trans le_sup_left).trans hc₁, (le_sup_right.trans le_sup_left).trans hc₁, fun t x => ?_, fun c' hle hc' => ?_⟩
  · refine GlobalTheory.NormOneChar.mem_of_pow_eq_one (hm t) (hsup₁ t (le_sup_right (a := (c₀ t).F) (IntermediateField.mem_adjoin_simple_self ℚ _))) ?_
    rw [← Circle.coe_pow, xi_pow_eq_one D (R.xi t) (R.xiH t) (hL.xi t) (m t) (ho t) x]
    rfl
  have hsup : ∀ t, (c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)} ≤ c'.F := fun t => (hsup₁ t).trans hc'
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
  have hM : ∀ t, ∀ PP ∈ R.Q t, (((d (rep t)).l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun t PP hPP => by
    refine (hH (rep t)).2.1 PP (by rw [hrep]; exact hPP) ?_
    have h1 : (((d (rep t)).l₂.M : ℕ) : 𝓞 D.host.E) ∈ (d (rep t)).l₂.Mb :=
      Ideal.mul_le_left ((d (rep t)).l₂.prod.ge (Ideal.mem_span_singleton_self _))
    rw [(a4 (rep t)).2.2.2.1, a2] at h1
    exact Ideal.mul_le_right h1
  choose U dict b3 using fun t => exists_fun_cover (d t) (Wc D i) (rank_Wc i) (iotaW T i) _ hio hpos hx₀ (a5 t)
  have b4 : ∀ t, ∃ f : Rul (d (rep t)).Xo₂ (d (rep t)).c₂,
      ({ d (rep t) with cδ := f } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n).IsLev ∧ f ^ m t = 1 ∧
      IsUnf (U (rep t)) ∧ (∀ k, ModelW (Wc D i) (rank_Wc i) ((U (rep t)).X k)) ∧
      ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw ((i : ℕ) + 1)).mult τ))
        (F : FamilyUnif (d (rep t)).Xo₂ (((inC c').comp ((d (rep t)).eF.symm : (d (rep t)).c₂.F →+* c'.F)).comp
            (IntermediateField.inclusion (d (rep t)).c₂.le).toRingHom)
          (fun j => relab (d (rep t)).c₂ ((inC c').comp ((d (rep t)).eF.symm : (d (rep t)).c₂.F →+* c'.F)) (e j).1))
        (ik : (U (rep t)).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((U (rep t)).X k).Λ)
        (th : ∀ k, ((U (rep t)).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
        (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
        DictLat (U (rep t)) (Wc D i) (rank_Wc i) (dict (rep t)) (iotaW T i) e F ik φ th (T.x₀ ((i : ℕ) + 1) (sOv T.toCore c' hle)) ∧
        ∀ h γ : GA D (Wc D i), MarkBy (U (rep t)) (Wc D i) (rank_Wc i) (dict (rep t)) (iotaW T i) F ik φ h γ →
          rdU (U (rep t)) f (dict (rep t) h).1 (dict (rep t) h).2 =
            1 * ((xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) (γ * h))) : ℂˣ) : ℂ) := fun t => by
    obtain ⟨u1, u2, g, e, F, ik, φ, th, v1, v2, v3⟩ := b3 (rep t)
    obtain ⟨f, f1, f2, f3⟩ := v3 (a4 (rep t)) (a6 (rep t)) (xi t)
      (hx2 t _ (d (rep t)).l₂.odd (unrAt_of_not_mem R hL t _ (hM t))) (hx3 t) (m t) (hm t) (hx4 t)
      (hsup t (le_sup_right (a := (c₀ t).F) (IntermediateField.mem_adjoin_simple_self ℚ _)))
    exact ⟨f, f1, f2, u1, u2, g, e, F, ik, φ, th, v1, v2, f3⟩
  choose f b1 b2 b5 using b4
  refine ⟨d, U, dict, f, xi, fun t => ⟨a1 t, a2 t, a3 t⟩, fun t => ⟨b1 t, a5 (rep t), a7 (rep t)⟩,
    fun t => ?_, hx1, ⟨1, ⟨1, one_pos, one_pow 1⟩, b5⟩, fun t => (b5 t).2.1⟩
  rw [a2]
  exact halfIs_of_eq R (hrep t) (hH (rep t))

end GlobalTheory.OneCover
