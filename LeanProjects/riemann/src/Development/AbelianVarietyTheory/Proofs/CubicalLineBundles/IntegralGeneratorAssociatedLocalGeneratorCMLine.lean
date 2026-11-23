import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SecTieBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieBasisLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationEqOfIsLocGen
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTriplePullback
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LocGen

theorem fibre_ne_of_generates {R : Type} [CommRing R] [IsLocalRing R] (P : Out.PolAV (Sp R)) (θ : P.L.Sec)
    (h : ∀ σ : P.L.Sec, ∃ c : ∀ i, Γ(P.A.left, P.L.U i), ∀ i, σ.f i = c i * θ.f i) (s : Sp R) :
    ∃ q : P.A.left, P.A.hom q = s ∧ q ∈ Out.nonzeroLocus θ := by
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hp : IsPullback (𝟙 P.A.left) P.A.hom P.A.hom (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨th, hth⟩ := KeyPow.exists_sec_fibre_ne_zero hT P hp
  obtain ⟨q, hq, hz⟩ := hth s
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz
  obtain ⟨c, hc⟩ := h ⟨fun j => (P.A.left.presheaf.map (homOfLE (fun y hy => mem_pull.2 hy :
      P.L.U j ≤ (P.L.pull (𝟙 P.A.left)).U (fun _ => j))).op).hom (th.f fun _ => j), fun j j' => fn_ext fun y hy => by
    have h₁ : y ∈ (P.L.pull (𝟙 P.A.left)).U (fun _ => j) := mem_pull.2 hy.1
    have h₂ : y ∈ (P.L.pull (𝟙 P.A.left)).U (fun _ => j') := mem_pull.2 hy.2
    refine (gs_res _ y _ hy _).trans ((gs_res _ y _ hy.1 _).trans ((gs_compat th (𝟙 _) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans ?_)
        ((gs_res _ y _ hy _).trans (gs_res _ y _ hy.2 _)))))))
    rw [gm_pull_g P.L (𝟙 _) (𝟙 _) y _ _ h₁ h₂, Category.comp_id]⟩
  have hk' : q ∈ P.L.U (k PUnit.unit) := mem_pull.1 hk
  refine ⟨q, hq, (mem_nonzeroLocus _ _).2 ⟨_, hk', ?_⟩⟩
  have e := congrArg (gs (𝟙 _) q _) (hc (k PUnit.unit))
  rw [gs_mul _ q _ hk'] at e
  exact isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_res (𝟙 _) q _ hk' _).symm.trans e)).mp u)

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n k : ℕ} (e : n = k)
    {v : Fin k → (epsR R ⟶ G)} (h : IsLieBasis v) : IsLieBasis fun i : Fin n => v (i.cast e) := by
  subst e; exact h

theorem isLieComb_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n k : ℕ} (e : n = k)
    (B : Matrix (Fin k) (Fin k) R) {v w : Fin k → (epsR R ⟶ G)} (h : ∀ i, IsLieComb (B i) v (w i)) (i : Fin n) :
    IsLieComb ((Matrix.of fun i j : Fin n => B (i.cast e) (j.cast e)) i) (fun i : Fin n => v (i.cast e))
      (w (i.cast e)) := by
  subst e; exact h i

theorem det_cast {R : Type} [CommRing R] {n k : ℕ} (e : n = k) (B : Matrix (Fin k) (Fin k) R) :
    (Matrix.of fun i j : Fin n => B (i.cast e) (j.cast e)).det = B.det := by
  subst e; rfl

theorem eps_sq {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (Chart.dualMapR f) ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem stalk_of_isoMaps {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {θ : L.Sec} {θ' : (L.pull F).Sec} {σ : L'.Sec} (h : IsoMaps w σ θ') (hθ : PullSec F θ θ')
    (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs (r ≫ F) z _ (θ.f j) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  have le : (L.pull F).U (fun _ => j) ≤ F ⁻¹ᵁ L.U j := fun q hq => mem_pull.1 hq
  rw [← (TieCalc.isoMaps_iff w σ θ').1 h Z r z j k hj hk, hθ (fun _ => j) le, gs_appLE F _ _ le r z (mem_pull.2 hj)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem keyPB_of_sabMap {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {T : PAT H (Sp R)} {T' : PAT H (Sp R')}
    (m : SABMap T'.t T.t (spMap f)) {w : LB.Iso T'.t.PP.L (T.t.PP.L.pull m.φ)} (hw : RigIso m w) (hg : T'.g = T.g)
    {g₀ th hth v hv g₀' th' hth' v' hv'}
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ T'.t.G.left) (z : Z) j k, m.φ (r z) ∈ T.t.PP.L.U j → r z ∈ T'.t.PP.L.U k →
      gs (r ≫ m.φ) z _ (LB.Sec.f th j) = (gw w r z j k).val * gs r z _ (LB.Sec.f th' k))
    (hl : ∀ i, (v' i).left ≫ m.φ = spMap (Chart.dualMapR f) ≫ (v (i.cast hg)).left) :
    KeyPB ⟨T'.pol, g₀', T'.t.PP.rig, T'.t.PP.rigGen, th', hth', v', hv'⟩
      ⟨T.pol, g₀, T.t.PP.rig, T.t.PP.rigGen, th, hth, v, hv⟩ f := by
  have he : eSec T'.t.G ≫ m.φ = spMap f ≫ eSec T.t.G := PolBaseChange.eSec_comm m.cart
  have hr := (maps_iff w _ (fun _ => eSec T.t.G) _ T'.t.PP.rig T.t.PP.rig m.cm.e _
    (rigPull_le m.cm.F m.cm.e m.cm.e_comm T.t.PP.L) (fun _ => rfl)).1 hw.2
  rw [m.base] at hr
  refine ⟨m.φ, he, w, hg, Chart.dualMapR f, m.cart, hw.1,
    (maps_iff w _ (fun _ => eSec T.t.G) _ T'.t.PP.rig T.t.PP.rig _ _ (rigPull_le m.φ _ he T.t.PP.L) (fun _ => rfl)).2 hr,
    KeyPow.appLE_eq_of_stalk _ th th' (hs _ (𝟙 _)), fun a => ?_, ?_, hl⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem eq_mul_of_secTie {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {x x₀ : Sp S ⟶ Xo.X}
    {x₁ x₂ : Sp S' ⟶ Xo.X} {t : SAB H (Sp S)} {t' : SAB H (Sp S')} {m : SABMap t Xo.univ.t x}
    {m' : SABMap t' Xo.univ.t (spMap φ ≫ x)} {n : SABMap t' t (spMap φ)} (hφ : m'.φ = n.φ ≫ m.φ)
    {th : LB.Sec t.PP.L} {s₀ : LB.Sec (PPx x₀)} {s₁ : LB.Sec (PPx x₁)} {s₂ : LB.Sec (PPx x₂)} {a : S'}
    (e₀ : x₀ = x) (e₁ : x₁ = spMap φ ≫ x₀) (e₂ : x₂ = x₁) (h₀ : SecTie m th s₀) (b₁ : SecBC φ 1 x₀ x₁ s₀ s₁)
    (b₂ : SecBC (RingHom.id S') a x₁ x₂ s₁ s₂) {w : LB.Iso t'.PP.L (t.PP.L.pull n.φ)} (hw : RigIso n w)
    {th' σ : LB.Sec t'.PP.L}
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ t'.G.left) (z : Z) j k, n.φ (r z) ∈ t.PP.L.U j → r z ∈ t'.PP.L.U k →
      gs (r ≫ n.φ) z _ (th.f j) = (gw w r z j k).val * gs r z _ (th'.f k))
    (h₂ : SecTie m' σ s₂) : ∀ i, σ.f i = constFn t'.G.hom _ a * th'.f i := by
  subst e₀ e₁
  have h₁ : SecTie m' th' s₁ :=
    (TieCalc.secTie_baseChange m h₀ φ m' n s₁ w (thfPull _ n.φ th) th' rfl hφ b₁ hw (fun _ _ => rfl)).2
      ((TieCalc.isoMaps_iff w _ _).2 fun Z r z j k hj hk =>
        (gs_appLE n.φ _ _ _ r z (mem_pull.2 hj) _).trans (hs Z r z j k hj hk))
  exact ((TieCalc.secTie_calc E H Dw l Xo S' _ t' m' th' s₁ h₁).1 a x₂ s₂ σ e₂ b₂).1 h₂

theorem integral_generator_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → letI := (iK.comp (algebraMap c.F z.K)).toAlgebra; ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr) (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (a : T.Fr), φ.toRingHom = iK → FrMap φ z.y yT → FrChg g a yT y' → SecInt T M.m1 M.m2 y'.s → ∀ ca : z.K, IsLocGen p ca z.Tl.I → ∃ u : T.Vˣ, a = iK ca * algebraMap T.V T.Fr u := by
  intro E _ _ _ H Dw l Xo c _ z f La hz p T iK M hT φ yT y' g a hφ hmap hchg hint ca hca
  obtain ⟨hobj, -, -, hx, htie, -⟩ := hz
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hloc, -, hmod⟩ := hobj
  obtain ⟨A, hA, hdet⟩ := hmod p
  obtain ⟨θ, hθ, w2, σ, θ2, r2, i2, p2, hσ⟩ := hint
  obtain ⟨vV, bV, hV⟩ := exists_isLieBasis_locMod E H Dw l Xo c z p T iK M hT A hA
  obtain ⟨g1, -, w1, r1⟩ := (pat_pullback E H _ _ iK z.Φ.T).2 M.t' M.n' inferInstance
  obtain ⟨g2, -⟩ := (pat_pullback E H _ _ (algebraMap T.V T.Fr) M.G).2 M.t' M.m2 inferInstance
  have g3 : M.G.g = z.Φ.T.g := g2.symm.trans g1
  obtain ⟨th', hth'⟩ := sec_pull_down ((isGen_iff _).1 r1.1) z.Φ.T.t.PP.isLB M.t'.t.PP.isLB z.Φ.th
  have nz' := SectionBaseChange.fibre_nonzero_of_pull M.t'.t.PP.isLB hth' M.n'.cart.1 z.Φ.th_ne
  have nzθ := fibre_ne_of_generates M.G.pol θ fun τ => (hθ τ).exists.elim fun b hb => ⟨_, hb⟩
  have hσθ := stalk_of_isoMaps i2 p2
  have nzσ := SectionBaseChange.fibre_nonzero_of_pull M.t'.t.PP.isLB hσθ M.m2.cart.1 nzθ
  obtain ⟨v0, b0, h0⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ iK _ _ _ M.n'.cart z.Φ.T.ab.smooth _ z.Φ.v z.Φ.basis
  obtain ⟨v1, b1, h1⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ (algebraMap T.V T.Fr) _ _ _ M.m2.cart M.G.ab.smooth _ vV bV
  have hc : ∀ k, IsLieComb (iK.mapMatrix A k) v0 (v1 k) := fun k => by
    show IsLieComb (fun j => iK (A k j)) v0 (v1 k)
    obtain ⟨wK, hw, hw'⟩ := hV k
    refine Chart.comb_baseChange iK M.n'.cart hw h0 (z.m'.cart.1.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ← M.h2, ← Category.assoc, h1, Category.assoc]
      exact hw'
    · rw [Category.assoc, Category.assoc, M.n'.cart.1.w, ← Category.assoc, Over.w, Over.w, eps_sq]
  have hσa : ∀ i, σ.f i = constFn M.t'.t.G.hom _ a * th'.f i := by
    obtain ⟨e₁, -, pm, ps, pf, hp⟩ := hmap
    rw [hφ] at e₁ pf
    refine eq_mul_of_secTie iK M.h1 hx e₁ hchg.1 htie ⟨pm, ps, pf, fun i h => ?_⟩ hchg.2.2 r1 hth' hσ
    rw [SecCalc.scal_one' z.y.x i, _root_.one_mul]
    exact hp i h
  have gp : 1 ≤ M.t'.g := g1 ▸ z.Φ.g_pos
  let x' : KeyIn T.Fr := ⟨M.t'.pol, gp, M.t'.t.PP.rig, M.t'.t.PP.rigGen, th', nz', _, isLieBasis_cast g1 b0⟩
  let xR : KeyIn T.V := ⟨M.G.pol, gp.trans g2.le, M.G.t.PP.rig, M.G.t.PP.rigGen, θ, nzθ, _, isLieBasis_cast g3 bV⟩
  have k1 : KeyPB x' z.Φ.key iK := keyPB_of_sabMap M.n' r1 g1 hth' fun i => h0 _
  have k2 : KeyPB ⟨M.t'.pol, gp, M.t'.t.PP.rig, M.t'.t.PP.rigGen, σ, nzσ, _, isLieBasis_cast g1 b1⟩ xR
      (algebraMap T.V T.Fr) := keyPB_of_sabMap M.m2 r2 g2 hσθ fun i => h1 _
  have k3 : KeyIntegral T.V x' a (iK A.det) :=
    ⟨σ, nzσ, _, isLieBasis_cast g1 b1, Matrix.of fun i j => iK.mapMatrix A (i.cast g1) (j.cast g1), xR, hσa,
      isLieComb_cast g1 (iK.mapMatrix A) hc, (det_cast g1 _).trans (RingHom.map_det iK A).symm, k2⟩
  exact KeyVal.integral_section_unit z.K z.Φ.key z.Tl z.LamL p (hloc p) T.V T.Fr iK x' a (iK A.det) ca A.det 1 hT
    k1 k3 hdet (by rw [Units.val_one, map_one, _root_.mul_one]) hca

end GlobalTheory.LamT.LocGen
