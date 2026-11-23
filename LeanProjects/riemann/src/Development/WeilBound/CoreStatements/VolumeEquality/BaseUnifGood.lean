import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifSig
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifUnivC
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRiemannLatticeOfPeriodStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicPeriodFamilyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainOpenConvexZeroStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CongruenceSubgroupOfFormAutomorphismsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPeriodRiemannLatticeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHolomorphic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformisationLocalPeriod
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem exists_equiv_of_det {g : ℕ} (h : Matrix (Fin g) (Fin g) ℂ) (hd : IsUnit h.det) :
    ∃ e : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e z = h *ᵥ z :=
  ⟨h.toLinearEquiv' (h.invertibleOfIsUnitDet hd), fun z => Matrix.toLin'_apply h z⟩

theorem u_eq_of_equiv {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) (i : Fin FU.n)
    {P P' Q : (FU.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (FU.Di i) ty P) (hP' : IsPeriod (FU.Di i) ty P')
    (e e' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ x, P x = e (Q x)) (he' : ∀ x, P' x = e' (Q x)) :
    FU.u i P = FU.u i P' :=
  (FU.fibre i P P' hP hP').2 ⟨LinearEquiv.refl _ _, e.symm.trans e', fun _ _ => rfl, fun a _ => ⟨0, by simp⟩,
    fun a => ⟨0, by simp⟩, fun a => by simp [he, he']⟩

theorem j_over (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (κ : c.F →+* ℂ) (x : Sp ℂ ⟶ Xo.XF c)
    (hx : x ≫ pullback.snd _ _ = spMap κ) : (x ≫ Y.j) ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) := by
  rw [Category.assoc, Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hx,
    spMap_comp]

theorem j_inj (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) {x x' : Sp ℂ ⟶ Xo.XF c}
    (hx : x ≫ pullback.snd _ _ = x' ≫ pullback.snd _ _) (h : x ≫ Y.j = x' ≫ Y.j) : x = x' := by
  have := Y.jQ_open
  rw [← cancel_mono Y.jQ]
  apply pullback.hom_ext
  · simpa [Model.j] using h
  · rw [Category.assoc, Category.assoc, Y.jQ_over, hx]

theorem j_interior (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (x : Sp ℂ ⟶ Xo.XF c) :
    centre (x ≫ Y.j) ∈ abLocus Y.t.G := by
  have h : Y.jQ (centre x) ∈ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]
    exact ⟨_, rfl⟩
  exact h

theorem exists_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Y.X)
    (hp : centre p ∈ abLocus Y.t.G) (hs : p ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))) :
    ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ Y.j = p ∧ x ≫ pullback.snd _ _ = spMap κ := by
  have hc : p ≫ Y.s = spMap κ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by rw [hs, spMap_comp]
  let w : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift p (spMap κ) hc
  have hw₁ : w ≫ pullback.fst _ _ = p := pullback.lift_fst _ _ _
  have hw₂ : w ≫ pullback.snd _ _ = spMap κ := pullback.lift_snd _ _ _
  have := Y.jQ_open
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨u, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, hw₁]
    have hu : u = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hu
    exact hp
  have hx : IsOpenImmersion.lift Y.jQ w hr ≫ Y.jQ = w := IsOpenImmersion.lift_fac _ _ _
  refine ⟨IsOpenImmersion.lift Y.jQ w hr, ?_, ?_⟩
  · rw [Model.j, ← Category.assoc, hx, hw₁]
  · rw [← Y.jQ_over, ← Category.assoc, hx, hw₂]

theorem isHolTo_of_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (κ : c.F →+* ℂ) {m : ℕ} {T : Set (Fin m → ℂ)}
    {x : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.XF c)} (hT : IsOpen T) (hs : ∀ b, x b ≫ pullback.snd _ _ = spMap κ)
    (h : IsHolTo T fun b => x b ≫ Y.j) : IsHolTo T x := by
  have := Y.jQ_open
  have he : ∀ b, (x b ≫ Y.j) ≫ Y.s = spMap κ ≫ spMap (algebraMap (𝓞 c.F) c.F) := fun b => by
    rw [j_over Y κ _ (hs b), spMap_comp]
  have hq : ∀ b, x b ≫ Y.jQ = pullback.lift (x b ≫ Y.j) (spMap κ) (he b) := fun b => by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc]
      rfl
    · rw [pullback.lift_snd, Category.assoc, Y.jQ_over, hs]
  have h₃ : IsHolTo T fun b => x b ≫ Y.jQ := by
    have := PullbackSections.holPair _ _ _ Y.s (spMap (algebraMap (𝓞 c.F) c.F)) m T (fun b => x b ≫ Y.j) (fun _ => spMap κ) he hT h
      (PullbackSections.isHolTo_spMap hT (Ψ := fun _ => κ) fun a => differentiableOn_const _)
    simpa only [hq] using this
  exact Flat.isHolTo_of_comp_openImmersion Y.jQ h₃

set_option maxHeartbeats 1600000 in
theorem kUnif_good (hV : VecOfPeriods) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H)
    (j j' n g : ℕ) (q : CMType H × Fin j × Fin j' ≃ Fin n) (κ : c.F →+* ℂ) (ty : Fin g → (E →+* ℂ))
    (hty : IsTypeFn H D.p D.q ty) (hs : sm = Sum.inr ∧ j = D.p ∧ j' = D.q ∨ sm = Sum.inl ∧ j = D.q ∧ j' = D.p)
    (ρ : c.F) (hρ : (ρ : ℂ) = H.rt0) (hκ : κ ρ = H.rt0)
    (FU : FamilyUnif Xo (κ.comp (IntermediateField.inclusion c.le).toRingHom) ty) :
    Nonempty (KUnif Y sm j j' n g q κ) := by
  classical
  let ι : Type := {i : Fin FU.n // ∃ P, IsPeriod (FU.Di i) ty P}
  have htyi : ∀ i, IsTypeFn H (FU.Di i).p (FU.Di i).q ty := fun i => by
    rw [(FU.sig i).1, (FU.sig i).2]
    exact hty
  have hsig : ∀ {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ),
      R.HasSig (fun τ => κ.comp (labelEmb c (sm τ))) j j' ↔ HasRk H D.p D.q R :=
    fun R => hasSig_iff κ ρ hρ hκ D.p D.q sm j j' hs R
  have hriem : ∀ i P, IsPeriod (FU.Di i) ty P → ∃ R : RiemLat E g (FU.Di i).La, R.P = P ∧ R.form = (FU.Di i).EF ∧
      R.HasSig (fun τ => κ.comp (labelEmb c (sm τ))) j j' := fun i P hP => by
    obtain ⟨R, h₁, h₂, -, h₄⟩ := GlobalTheory.T.exists_riemann_lattice_of_period E H (FU.Di i) g ty P (htyi i) hP
    rw [(FU.sig i).1, (FU.sig i).2] at h₄
    exact ⟨R, h₁, h₂, (hsig R).2 h₄⟩
  have hF : ∀ k : ι, ∃ F : UnivFam E (CMType H) j j' n g (FU.Di k.1).La, F.q = q ∧
      F.σ = (fun τ => κ.comp (labelEmb c (sm τ))) ∧ F.form = (FU.Di k.1).EF := fun k => by
    obtain ⟨P, hP⟩ := k.2
    obtain ⟨R, -, h₂, h₃⟩ := hriem _ P hP
    obtain ⟨F, a₁, a₂, a₃⟩ := univExists E (CMType H) j j' n g _ R _ q
      (side_cm κ sm (hs.imp (·.1) (·.1))) h₃
    exact ⟨F, a₁, a₂, a₃.trans h₂⟩
  choose F hq hσ hform using hF
  have hΓ : ∀ k : ι, ∃ Γ : Subgroup ((FU.Di k.1).La ≃ₗ[𝓞 E] (FU.Di k.1).La), (F k).IsArith Γ ∧
      ∀ γ, γ ∈ Γ ↔ InLevel l (FU.Di k.1) γ := fun k => by
    haveI := ((F k).R 0).fin
    obtain ⟨Γ, a₁, a₂, a₃⟩ := GlobalTheory.T.congruence_subgroup_of_form_automorphisms E (FU.Di k.1).La (FU.Di k.1).EF (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) l.M l.A
      (by have := l.three_le; omega) l.A_pos
    refine ⟨Γ, ?_, a₃⟩
    unfold UnivFam.IsArith
    rw [hform]
    exact ⟨a₁, a₂⟩
  choose Γ hΓa hΓm using hΓ
  have hO : IsOpen (ballDom q) := (GlobalTheory.T.ball_domain_open_convex_zero _ j j' n q).1
  have hRf : ∀ k t, ((F k).R t).form = (FU.Di k.1).EF := fun k t => ((F k).form_eq t).trans (hform k)
  have hloc : ∀ k : ι, ∀ t₀ ∈ ballDom q, ∃ (V' : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ((FU.Di k.1).La →+ (Fin g → ℂ)))
      (h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen V' ∧ t₀ ∈ V' ∧ V' ⊆ ballDom q ∧
      IsHolPeriods (FU.Di k.1) ty V' P ∧ (∀ a b, DifferentiableOn ℂ (fun t => h t a b) V') ∧
      ∀ t ∈ V', IsUnit (h t).det ∧ ∀ x, P t x = h t *ᵥ ((F k).R t).P x := fun k =>
    GlobalTheory.T.local_holomorphic_period_family E H (FU.Di k.1) g n ty (ballDom q) (F k).R (htyi _) hO (hq k ▸ (F k).hol) fun t ht => ⟨hRf k t, by
      rw [(FU.sig _).1, (FU.sig _).2]
      refine (hsig _).1 ?_
      rw [← hσ k]
      exact (F k).sig t (by rw [hq]; exact ht)⟩
  have hPt : ∀ (k : ι) (t : Fin n → ℂ), ∃ P, IsPeriod (FU.Di k.1) ty P ∧ (t ∈ ballDom q →
      ∃ e : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, P x = e (((F k).R t).P x)) := fun k t => by
    by_cases ht : t ∈ ballDom q
    · obtain ⟨V', P, h, -, hm, -, hP, -, hh⟩ := hloc k t ht
      obtain ⟨e, he⟩ := exists_equiv_of_det (h t) (hh t hm).1
      exact ⟨P t, hP.1 t hm, fun _ => ⟨e, fun x => by rw [he, (hh t hm).2]⟩⟩
    · obtain ⟨P, hP⟩ := k.2
      exact ⟨P, hP, fun h => absurd h ht⟩
  choose Pt hPt hPe using hPt
  have hu : ∀ (k : ι), ∀ t ∈ ballDom q, ∀ P, IsPeriod (FU.Di k.1) ty P → ∀ e : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ x, P x = e (((F k).R t).P x)) → FU.u k.1 (Pt k t) = FU.u k.1 P := fun k t ht P hP e he => by
    obtain ⟨e₀, he₀⟩ := hPe k t ht
    exact u_eq_of_equiv FU k.1 (hPt k t) hP e₀ e he₀ he
  have hum : ∀ (k : ι), ∀ t ∈ ballDom q, ∀ P, IsPeriod (FU.Di k.1) ty P → ∀ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h.det →
      (∀ x, P x = h *ᵥ ((F k).R t).P x) → FU.u k.1 (Pt k t) = FU.u k.1 P := fun k t ht P hP h hd hh => by
    obtain ⟨e, he⟩ := exists_equiv_of_det h hd
    exact hu k t ht P hP e fun x => by rw [he, hh]
  have hc : ∀ (k : ι) t, FU.u k.1 (Pt k t) ≫ Xo.s = spMap κ ≫ spMap (IntermediateField.inclusion c.le).toRingHom :=
    fun k t => by rw [FU.over_σ _ _ (hPt k t), spMap_comp]
  let xF : ι → (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun k t => pullback.lift _ _ (hc k t)
  have hx₁ : ∀ k t, xF k t ≫ pullback.fst _ _ = FU.u k.1 (Pt k t) := fun k t => pullback.lift_fst _ _ _
  have hx₂ : ∀ k t, xF k t ≫ pullback.snd _ _ = spMap κ := fun k t => pullback.lift_snd _ _ _
  have hxhol : ∀ k, IsHolTo (ballDom q) (xF k) := fun k => by
    refine PullbackSections.holPair _ _ _ _ _ n _ _ _ (hc k) hO ?_
      (PullbackSections.isHolTo_spMap hO (Ψ := fun _ => κ) fun a => differentiableOn_const _)
    refine GlobalTheory.HolPeriods.isHolTo_of_local fun t₀ ht₀ => ?_
    obtain ⟨V', P, h, hVo, hm, hsub, hP, -, hh⟩ := hloc k t₀ ht₀
    exact ⟨V', hm, hsub, GlobalTheory.HolPeriods.isHolTo_congr (FU.hol _ n V' P hVo hP).1 fun t ht =>
      hum k t (hsub ht) _ (hP.1 t ht) _ (hh t ht).1 (hh t ht).2⟩
  have hpt : ∀ k k' t t', xF k t ≫ Y.j = xF k' t' ≫ Y.j ↔ FU.u k.1 (Pt k t) = FU.u k'.1 (Pt k' t') := fun k k' t t' => by
    constructor
    · intro h
      rw [← hx₁, ← hx₁, j_inj Y ((hx₂ k t).trans (hx₂ k' t').symm) h]
    · intro h
      congr 1
      apply pullback.hom_ext
      · rw [hx₁, hx₁, h]
      · rw [hx₂, hx₂]
  have hmono : ∀ {X : Scheme.{0}} {B B' : Set (Fin n → ℂ)} {y : (Fin n → ℂ) → (Sp ℂ ⟶ X)}, IsHolTo B y → IsOpen B' →
      B' ⊆ B → IsHolTo B' y := fun h hB hsub => GlobalTheory.HolPeriods.isHolTo_comp (φ := id) h hB differentiableOn_id hsub
  refine ⟨{
    ι := ι
    fin := inferInstance
    Di := fun k => FU.Di k.1
    sig := fun k => FU.sig k.1
    F := F
    q_eq := hq
    form_eq := fun k => Or.inl (hform k)
    σ_eq := fun k τ => by rw [hσ]
    Γ := Γ
    mem_Γ := hΓm
    arith := hΓa
    pt := fun k t => xF k t ≫ Y.j
    hol := fun k => PullbackSections.isHolTo_comp (hxhol k) Y.j
    comp_s_eq_spMap_of_isOver := fun k t _ => j_over Y κ _ (hx₂ k t)
    interior := fun k t _ => j_interior Y _
    disj := fun k k' t _ t' _ h => Subtype.ext (FU.disj _ _ _ _ (hPt k t) (hPt k' t') ((hpt k k' t t').1 h))
    fibre := fun k t ht t' ht' => ?_
    onto := fun p hp hps => ?_
    lat := fun k t ht => ?_
    vec := fun S Ω _ K _ J _ y 𝔐 k V z hVo hVs hz hzf t₀ ht₀ => ?_
    locc := fun m T y hT hTc hy hyi hys b hb b' hb' k k' t ht t' ht' e e' => ?_ }⟩
  · rw [hpt, FU.fibre _ _ _ (hPt k t) (hPt k t')]
    obtain ⟨e, he⟩ := hPe k t ht
    obtain ⟨e', he'⟩ := hPe k t' ht'
    constructor
    · rintro ⟨γ, h, a₁, a₂, a₃, a₄⟩
      refine ⟨γ, (hΓm k γ).2 ⟨a₁, a₂, a₃⟩, (e.trans h).trans e'.symm, fun x => ?_⟩
      have := a₄ x
      rw [he', he] at this
      simp [← this]
    · rintro ⟨γ, hγ, h, hh⟩
      obtain ⟨a₁, a₂, a₃⟩ := (hΓm k γ).1 hγ
      refine ⟨γ, (e.symm.trans h).trans e', a₁, a₂, a₃, fun x => ?_⟩
      rw [he', he, hh]
      simp
  · obtain ⟨x, hx, hxs⟩ := exists_j Y κ p hp hps
    obtain ⟨i, P, hP, hui⟩ := FU.onto (x ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hxs, spMap_comp])
    obtain ⟨R, h₁, h₂, h₃⟩ := hriem i P hP
    let k : ι := ⟨i, P, hP⟩
    obtain ⟨t, ⟨ht, e, he⟩, -⟩ := (F k).univ R (h₂.trans (hform k).symm) (by rw [hσ]; exact h₃)
    rw [hq] at ht
    refine ⟨k, t, ht, ?_⟩
    rw [← hx]
    congr 1
    apply pullback.hom_ext
    · rw [hx₁, ← hui]
      exact hu k t ht P hP e fun a => by rw [← h₁]; exact he a
    · rw [hx₂, hxs]
  · obtain ⟨V', P, h, -, hm, -, hP, -, hh⟩ := hloc k t ht
    have h₁ : FibreLat Xo.univ.t (FU.u k.1 (P t)) ((F k).R t) :=
      GlobalTheory.T.family_period_riemann_lattice E H D l Xo _ g ty FU k.1 ((F k).R t) (P t) (h t) (hP.1 t hm) (hRf k t) (hh t hm).1 (hh t hm).2 Empty _ _
        fun a => a.elim
    rw [← hum k t ht _ (hP.1 t hm) _ (hh t hm).1 (hh t hm).2, ← hx₁] at h₁
    have h₂ := ((GlobalTheory.T.fibre_lattice_base_change_conj E H _ _ Xo.univ.t Y.oF.t _ g _ ((F k).R t) ((F k).R t) (xF k t)).1 ⟨Y.m0.toSABMap⟩).2 h₁
    exact ((GlobalTheory.T.fibre_lattice_base_change_conj E H _ _ Y.t Y.oF.t _ g _ ((F k).R t) ((F k).R t) (xF k t)).1 ⟨Y.m⟩).1 h₂
  · obtain ⟨V', P, h, hVo', hm, hsub, hP, hd, hh⟩ := hloc k t₀ (hVs ht₀)
    have hW : IsOpen (V ∩ V') := hVo.inter hVo'
    refine hV E H D l Xo c Y S Ω K J y 𝔐 κ _ g ty FU k.1 n (V ∩ V') z (xF k) (F k).R P h hW
      (hmono hz hW Set.inter_subset_left) (hmono (hxhol k) hW fun t ht => hsub ht.2)
      ⟨fun t ht => hP.1 t ht.2, fun x => (hP.2 x).mono Set.inter_subset_right⟩
      (fun a b => (hd a b).mono Set.inter_subset_right) (fun t ht => ?_) t₀ ⟨ht₀, hm⟩
    exact ⟨hRf k t, (hh t ht.2).1, (hh t ht.2).2, (hzf t ht.1).symm,
      (hx₁ k t).trans (hum k t (hsub ht.2) _ (hP.1 t ht.2) _ (hh t ht.2).1 (hh t ht.2).2), hx₂ k t⟩
  · have hx : ∀ a, ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap κ ∧ (a ∈ T → x ≫ Y.j = y a) := fun a => by
      by_cases ha : a ∈ T
      · obtain ⟨x, h₁, h₂⟩ := exists_j Y κ _ (hyi a ha) (hys a ha)
        exact ⟨x, h₂, fun _ => h₁⟩
      · exact ⟨xF k t, hx₂ k t, fun h => absurd h ha⟩
    choose x hxs hxj using hx
    have hol := isHolTo_of_j Y κ hT hxs (GlobalTheory.HolPeriods.isHolTo_congr hy hxj)
    obtain ⟨i, hi⟩ := Flat.exists_index_of_isPreconnected E H D l Xo _ g ty FU m T (fun a => x a ≫ pullback.fst _ _) hT hTc
      ⟨b, hb⟩ (fun a _ => by rw [Category.assoc, pullback.condition, ← Category.assoc, hxs, spMap_comp])
      (PullbackSections.isHolTo_comp hol _)
    have key : ∀ a ∈ T, ∀ (k : ι) (t : Fin n → ℂ), y a = xF k t ≫ Y.j → k.1 = i := fun a ha k t e => by
      obtain ⟨B', P, -, haB, -, hP, hu'⟩ := hi a ha
      refine FU.disj _ _ _ _ (hPt k t) (hP.1 a haB) ?_
      rw [hu' a haB, ← hx₁, j_inj Y ((hxs a).trans (hx₂ k t).symm) ((hxj a ha).trans e)]
    exact Subtype.ext ((key b hb k t e).trans (key b' hb' k' t' e').symm)

end SheetDecomposition
