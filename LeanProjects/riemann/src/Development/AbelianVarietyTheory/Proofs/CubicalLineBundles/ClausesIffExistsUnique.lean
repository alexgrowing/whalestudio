import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Development.AbelianVarietyTheory.BlockTheory.EvidentLattices.LatticeLetterSources
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedSectionCorrespondenceExistsUniqueNonva
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeEqSpanHostIdealSmul

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.abelian₂ Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.FD (Data DataX Frame LamBasis fdeg)
open GlobalTheory.SecTransport GlobalTheory.SecTieEx

namespace GlobalTheory.FramedCMPointCompare

section Bundles

variable {X X' Y : Scheme.{0}}

theorem reading_iff {L : LB X} (hL : L.IsLB) {L' : LB X'} (g : X' ⟶ Y) (φ : Y ⟶ X)
    (wP : LB.Iso L' (L.pull (g ≫ φ))) (hw : wP.IsGen) (hL' : L'.IsLB) (th : LB.Sec L')
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1))) :
    (∃ (w : LB.Iso L' ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)).pull g))
      (s' : LB.Sec ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)).pull g)),
      w.IsGen ∧ PullSec g s s' ∧ IsoMaps w th s' ∧
      ∀ (a : (L.pull (g ≫ φ)).ι) (b : ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)).pull g).ι)
        (i : L'.ι) (pt : X'), pt ∈ (L.pull (g ≫ φ)).U a →
        pt ∈ ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)).pull g).U b → pt ∈ L'.U i →
        gm (𝟙 _) pt _ (wP.s (a, i)) = gm (g ≫ φ) pt _ (L.g (a ⟨⟩) (b ⟨⟩ 0)) * gm (𝟙 _) pt _ (w.s (b, i))) ↔
    ∃ s₁ : LB.Sec (L.pull (g ≫ φ)), IsoMaps wP th s₁ ∧
      ∀ j, ∃ h : (L.pull (g ≫ φ)).U j ≤
          g ⁻¹ᵁ (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)).U (fun _ => j PUnit.unit),
        s₁.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit)) := by
  let M : LB Y := LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)
  have mem : ∀ (j : Fin 1 → L.ι) (y : X'), g y ∈ M.U j → (g ≫ φ) y ∈ L.U (j 0) := fun j y hy =>
    LB.wchart_le L _ j 0 hy
  have le' : ∀ J : PUnit → Fin 1 → L.ι, (M.pull g).U J ≤ g ⁻¹ᵁ M.U (J PUnit.unit) := fun J y hy => mem_pull.1 hy
  constructor
  · rintro ⟨w, s', -, hp, hi, hc⟩
    refine ⟨secPullBack L g rfl s, fun J k => fn_ext fun y hy => ?_, fun j => ⟨chart_le_preimage' L g rfl j, rfl⟩⟩
    have hb : y ∈ (M.pull g).U (fun _ _ => J PUnit.unit) := mem_pull.2 (chart_le_preimage' L g rfl J hy.1)
    have e₁ := (isoMaps_iff _ _ _).1 hi _ (𝟙 X') y (fun _ _ => J PUnit.unit) k hb hy.2
    rw [hp _ (le' _)] at e₁
    replace e₁ := (gs_appLE g _ _ _ (𝟙 X') y hb _).symm.trans e₁
    have e₂ := hc J (fun _ _ => J PUnit.unit) k y hy.1 hb hy.2
    replace e₂ := e₂.trans ((congrArg (· * _) (gm_self hL (g ≫ φ) y (mem_pull.1 hy.1))).trans (_root_.one_mul _))
    refine (gs_res _ y inf_le_left hy _).trans ((gs_appLE g _ _ _ (𝟙 X') y hy.1 _).trans (e₁.trans (Eq.symm ?_)))
    exact (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val e₂))
      (gs_res _ y _ hy _))
  · rintro ⟨s₁, hi, hs⟩
    have le : ∀ p : (PUnit → Fin 1 → L.ι) × L'.ι, (M.pull g).U p.1 ⊓ L'.U p.2 ≤
        (L.pull (g ≫ φ)).U (fun _ => p.1 PUnit.unit 0) ⊓ L'.U p.2 := fun p y hy =>
      ⟨mem_pull.2 (mem _ y (mem_pull.1 hy.1)), hy.2⟩
    let w' : LB.Iso L' (M.pull g) := ⟨fun p => res (le p) (wP.s (fun _ => p.1 PUnit.unit 0, p.2))⟩
    have hw' : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : Fin 1 → L.ι) (k : L'.ι), g (r z) ∈ M.U j →
        r z ∈ L'.U k → gw w' r z j k = gw wP r z (j 0) k := fun Z r z j k hj hk =>
      gm_res r z (le (fun _ => j, k)) ⟨mem_pull.2 hj, hk⟩ _
    let s' : LB.Sec (M.pull g) :=
      ⟨fun J => (g.appLE _ _ (le' J)).hom (s.f (J PUnit.unit)), fun J J' => fn_ext fun y hy =>
        (gs_res _ y _ hy _).trans ((gs_appLE g _ _ _ (𝟙 _) y hy.1 _).trans
          ((gs_compat s (𝟙 X' ≫ g) y (le' J hy.1) (le' J' hy.2)).trans
            (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
              ((gs_unit _ y _ hy _).trans (congrArg Units.val (gm_pull_g M g (𝟙 X') y J J' hy.1 hy.2)))
              ((gs_res _ y _ hy _).trans (gs_appLE g _ _ _ (𝟙 _) y hy.2 _)))))))⟩
    refine ⟨w', s', (isGen_iff w').2 fun Z r z j j' k k' hj hj' hk hk' => ?_, fun _ _ => rfl,
      (isoMaps_iff _ _ _).2 fun Z r z J k hJ hk => ?_, fun a b i pt ha hb hk => ?_⟩
    · have e : gm (r ≫ g) z _ (M.g j j') = gm (r ≫ g ≫ φ) z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) :=
        (gm_linComb L (K := Fin 1) (fun _ => φ) (fun _ => 1) (r ≫ g) z j j' hj hj').trans
          (by rw [Fin.prod_univ_one, zpow_one, Category.assoc])
      rw [hw' Z r z j k hj hk, hw' Z r z j' k' hj' hk', e]
      exact (isGen_iff wP).1 hw Z r z _ _ k k' (mem j _ hj) (mem j' _ hj') hk hk'
    · have hj := le' J hJ
      have h₁ : r z ∈ (L.pull (g ≫ φ)).U (fun _ => J PUnit.unit 0) := mem_pull.2 (mem _ _ hj)
      have e := (isoMaps_iff _ _ _).1 hi Z r z (fun _ => J PUnit.unit 0) k h₁ hk
      obtain ⟨h, hs⟩ := hs (fun _ => J PUnit.unit 0)
      rw [hs] at e
      replace e := (gs_appLE g _ _ _ r z h₁ _).symm.trans e
      rw [hw' Z r z _ k hj hk]
      refine (gs_appLE g _ _ _ r z hJ _).trans (Eq.trans ?_ e)
      obtain ⟨j, hj⟩ : ∃ j, J PUnit.unit = fun _ => j :=
        ⟨J PUnit.unit 0, funext fun a => congrArg (J PUnit.unit) (Subsingleton.elim _ _)⟩
      rw [hj]
    · have e := (isGen_iff wP).1 hw _ (𝟙 X') pt (a ⟨⟩) (b ⟨⟩ 0) i i (mem_pull.1 ha) (mem _ _ (le' b hb)) hk hk
      rw [gm_self hL' (𝟙 X') pt hk, inv_one, _root_.mul_one, ← hw' _ (𝟙 X') pt (b ⟨⟩) i (le' b hb) hk] at e
      exact e

end Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {c : Coeff l}

section Letters

variable [StarRing (𝓞 E)] {nΨ n' : ℕ}

def srcEquiv (o : LamObj c nΨ n') :
    (Fin nΨ × Fin o.xΨ.P.g) ⊕ (Fin n' × Fin o.x'.P.g) ≃ IndefiniteRowSideFullHecke.LatticeLetterSources.FinalTheorems o :=
  Equiv.sumCongr (Equiv.prodComm _ _) (Equiv.prodComm _ _)

def lettersEquiv (o : LamObj c nΨ n') : LamLetters o ≃ IndefiniteRowSideFullHecke.LatticeLetterSources.LamLetters o where
  toFun L := ⟨L.m, L.e, fun k => srcEquiv o (L.src k), L.U, L.ℓ⟩
  invFun L := ⟨L.m, L.e, fun k => (srcEquiv o).symm (L.src k), L.U, L.ℓ⟩
  left_inv L := by simp only [Equiv.symm_apply_apply]
  right_inv L := by simp only [Equiv.apply_symm_apply]

variable {o : LamObj c nΨ n'}

theorem lettersEquiv_fields (L : LamLetters o) :
    (lettersEquiv o L).m = L.m ∧ HEq (lettersEquiv o L).e L.e ∧
      (∀ k, (lettersEquiv o L).src k = srcEquiv o (L.src k)) ∧ (lettersEquiv o L).U = L.U ∧
      (lettersEquiv o L).ℓ = L.ℓ :=
  ⟨rfl, HEq.rfl, fun _ => rfl, rfl, rfl⟩

theorem isLetter_iff (L : LamLetters o) (k : Fin o.xB.P.g) (w : epsR o.K₁ ⟶ o.xB.P.A) :
    L.IsLetter k w ↔ (lettersEquiv o L).IsLetter k w := by
  show _ ↔ w.left ≫ o.φB = (srcEquiv o (L.src k)).img
  unfold LamLetters.IsLetter
  rcases L.src k with ⟨_, _⟩ | ⟨_, _⟩ <;> exact Iff.rfl

theorem isGood_iff (L : LamLetters o) : L.IsGood ↔ (lettersEquiv o L).IsGood := by
  have h₁ : Function.Bijective L.src ↔ Function.Bijective (lettersEquiv o L).src :=
    (Equiv.comp_bijective L.src (srcEquiv o)).symm
  have h₄ : (∀ k, ∃ w, L.IsLetter k w ∧ IsLieComb (L.U k) o.xB.v w) ↔
      ∀ k, ∃ w, (lettersEquiv o L).IsLetter k w ∧ IsLieComb (L.U k) o.xB.v w :=
    forall_congr' fun k => exists_congr fun w => and_congr_left' (isLetter_iff L k w)
  refine (and_congr h₁ (and_congr (forall_congr' fun b => forall_congr' fun i => ?_)
    ((and_congr h₄ (forall_congr' fun k => ?_)).trans and_comm))).trans
    ((and_congr_right fun _ => and_assoc.symm).trans and_assoc.symm)
  · show _ ↔ (srcEquiv o (L.src (L.e ⟨b, i⟩))).chr = b ∧ (srcEquiv o (L.src (L.e ⟨b, i⟩))).copy = (i : ℕ)
    rcases L.src (L.e ⟨b, i⟩) with ⟨_, _⟩ | ⟨_, _⟩ <;> exact Iff.rfl
  · show _ ↔ L.ℓ k = (srcEquiv o (L.src k)).line
    rcases L.src k with ⟨_, _⟩ | ⟨_, _⟩ <;> exact Iff.rfl

end Letters

section Data

variable {Dw : Datum H} {Xo : Moduli Dw l}

theorem gx_isPullback {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) :
    IsPullback (gxFst x) (gxSnd x) Xo.univ.t.G.hom x :=
  (IsPullback.of_hasPullback x Xo.univ.t.G.hom).flip

theorem toFibre_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} {g g' : A.left ⟶ Gx x}
    (h : g ≫ gxFst x = g' ≫ gxFst x) (h₁ : g ≫ gxSnd x = A.hom) (h₂ : g' ≫ gxSnd x = A.hom) : g = g' :=
  (gx_isPullback x).hom_ext h (h₁.trans h₂.symm)

theorem existsUnique_iso {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)}
    {ψ : A.left ⟶ Xo.univ.t.G.left} (hp : IsPullback ψ A.hom Xo.univ.t.G.hom x) :
    ∃! eY : A ≅ Over.mk (gxSnd x), eY.hom.left ≫ gxFst x = ψ := by
  have hx := gx_isPullback x
  refine ⟨Over.isoMk (hp.isoIsPullback _ _ hx) (hp.isoIsPullback_hom_snd _ _ hx),
    hp.isoIsPullback_hom_fst _ _ hx, fun e he => Iso.ext (Over.OverMorphism.ext ?_)⟩
  exact toFibre_ext (he.trans (hp.isoIsPullback_hom_fst _ _ hx).symm) (Over.w e.hom)
    (hp.isoIsPullback_hom_snd _ _ hx)

def embEquiv {F : Type} [Field F] (σ₀ : F →+* ℂ) (K : Type) [Field K] [Algebra F K] :
    (K →ₐ[F] CAt σ₀) ≃ {σ : K →+* ℂ // σ.comp (algebraMap F K) = σ₀} where
  toFun σ := ⟨σ.toRingHom, RingHom.ext fun a => σ.commutes a⟩
  invFun σ := ⟨σ.1, fun a => RingHom.congr_fun σ.2 a⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tie_iff (o : IndefiniteRowSideFullHecke.LatticeLetterSources.CMObj Dw c) :
    letI := H.starRing
    ∀ (y : FrPt Xo c o.K₁) (eY : o.xB.P.A ≅ Over.mk (gxSnd y.x)),
    (IsGrpPullback o.xB.P.A Xo.univ.t.G y.x (eY.hom.left ≫ gxFst y.x) ∧
    (∃ (he : eSec o.xB.P.A ≫ eY.hom.left ≫ gxFst y.x = y.x ≫ eSec Xo.univ.t.G)
      (wP : LB.Iso o.xB.P.L (Xo.univ.t.PP.L.pull (eY.hom.left ≫ gxFst y.x)))
      (w : LB.Iso o.xB.P.L ((PPx y.x).pull eY.hom.left)) (s' : LB.Sec ((PPx y.x).pull eY.hom.left)),
      wP.IsGen ∧ LB.Gen.Maps (LB.linCombIso wP (K := PUnit) (fun _ => eSec o.xB.P.A) (fun _ => 1)) o.xB.rig
        (rigPullOf (eY.hom.left ≫ gxFst y.x) y.x he Xo.univ.t.PP.L Xo.univ.t.PP.rig) ∧
      w.IsGen ∧ PullSec eY.hom.left y.s s' ∧ IsoMaps w o.xB.th s' ∧
      ∀ (a : (Xo.univ.t.PP.L.pull (eY.hom.left ≫ gxFst y.x)).ι) (b : ((PPx y.x).pull eY.hom.left).ι)
        (i : o.xB.P.L.ι) (pt : o.xB.P.A.left),
        pt ∈ (Xo.univ.t.PP.L.pull (eY.hom.left ≫ gxFst y.x)).U a → pt ∈ ((PPx y.x).pull eY.hom.left).U b →
        pt ∈ o.xB.P.L.U i →
        gm (𝟙 _) pt _ (wP.s (a, i)) =
          gm (eY.hom.left ≫ gxFst y.x) pt _ (Xo.univ.t.PP.L.g (a ⟨⟩) (b ⟨⟩ 0)) * gm (𝟙 _) pt _ (w.s (b, i))) ∧
    (∀ a : 𝓞 E, ∃ α : o.xB.P.A ⟶ o.xB.P.A, α.left ≫ o.φB = o.φB ≫ (o.oa.act a).left ∧
      (α ≫ eY.hom).left ≫ gxFst y.x = eY.hom.left ≫ gxFst y.x ≫ (Xo.univ.t.act.act a).left)) ↔
    IndefiniteRowSideFullHecke.LatticeLetterSources.IsTie o y (eY.hom.left ≫ gxFst y.x) := by
  letI := H.starRing
  intro y eY
  refine and_congr_right fun _ => and_comm.trans (and_congr (forall_congr' fun a => exists_congr fun α =>
    and_congr_right fun _ => ?_) (exists_congr fun he => exists_congr fun wP => ?_))
  · simp only [Over.comp_left, Category.assoc]
  · constructor
    · rintro ⟨w, s', h₁, h₂, h⟩
      obtain ⟨s₁, h₃, h₄⟩ := (reading_iff Xo.univ.t.PP.isLB eY.hom.left (gxFst y.x) wP h₁ o.xB.P.isLB o.xB.th y.s).1
        ⟨w, s', h⟩
      exact ⟨s₁, eY.hom.left, h₁, h₂, h₃, rfl, Over.w eY.hom, h₄⟩
    · rintro ⟨s₁, g, h₁, h₂, h₃, g₁, g₂, h₄⟩
      obtain rfl : g = eY.hom.left := toFibre_ext g₁ g₂ (Over.w eY.hom)
      obtain ⟨w, s', h⟩ := (reading_iff Xo.univ.t.PP.isLB eY.hom.left (gxFst y.x) wP h₁ o.xB.P.isLB o.xB.th y.s).2
        ⟨s₁, h₃, h₄⟩
      exact ⟨w, s', h₁, h₂, h⟩

end Data

variable {D : D7}

theorem fdeg_host (D : D7) : fdeg D.host.E = D.R.f := by
  unfold fdeg
  rw [hostSize_finrank]
  omega

theorem clauses_iff (T : Core D) (j : ℕ) (La : ℝ) (k : (T.U j T.σ₀).Comp) (x₀ : ((T.U j T.σ₀).X k).dom) :
    letI := T.Q.H.starRing
    ∀ (o : LamObj T.Q.c (T.Q.Dw j).p (T.Q.Dw j).q) (L : LamLetters o) (σ₁ : o.K₁ →ₐ[T.Q.c.F] CAt T.σ₀)
      (y : FrPt (T.Q.Xo j) T.Q.c o.K₁) (eY : o.xB.P.A ≅ Over.mk (gxSnd y.x)),
      LamPtClauses T j La k x₀ o L σ₁ y eY ↔
        IndefiniteRowSideFullHecke.LatticeLetterSources.LamPtClauses (T.U j T.σ₀) k x₀ La o (lettersEquiv o L) (embEquiv T.σ₀ o.K₁ σ₁).1 y
          (eY.hom.left ≫ gxFst y.x) := by
  letI := T.Q.H.starRing
  intro o L σ₁ y eY
  have hu : ∀ (τ : D.host.E →+* ℂ) (i : Fin ((T.Q.Dw j).mult τ)),
      (∃ (kk : Fin o.xB.P.g) (w : epsR o.K₁ ⟶ o.xB.P.A),
        (∃ (b : D.host.E →+* ℂ) (i' : Fin (L.m b)), b = τ ∧ (i' : ℕ) = i ∧ L.e ⟨b, i'⟩ = kk) ∧
        L.IsLetter kk w ∧ y.u τ i = (w ≫ eY.hom).left ≫ gxFst y.x) ↔
      ∃ (i' : Fin (L.m τ)) (w : epsR o.K₁ ⟶ o.xB.P.A), (i' : ℕ) = (i : ℕ) ∧
        (lettersEquiv o L).IsLetter (L.e ⟨τ, i'⟩) w ∧ w.left ≫ eY.hom.left ≫ gxFst y.x = y.u τ i := by
    intro τ i
    constructor
    · rintro ⟨_, w, ⟨b, i', rfl, hi, rfl⟩, h₁, h₂⟩
      exact ⟨i', w, hi, (isLetter_iff L _ w).1 h₁, (h₂.trans (Category.assoc _ _ _)).symm⟩
    · rintro ⟨i', w, hi, h₁, h₂⟩
      exact ⟨_, w, ⟨τ, i', rfl, hi, rfl⟩, (isLetter_iff L _ w).2 h₁, h₂.symm.trans (Category.assoc _ _ _).symm⟩
  constructor
  · rintro ⟨hG, hL, hm, hp, hpol, hl, hv, hx⟩
    exact ⟨fdeg_host D ▸ hG, (isGood_iff L).1 hL, hm, (embEquiv T.σ₀ o.K₁ σ₁).2, (tie_iff o y eY).1 ⟨hp, hpol, hl⟩,
      fun τ i => (hu τ i).1 (hv τ i), hx⟩
  · rintro ⟨hG, hL, hm, -, ht, hv, hx⟩
    obtain ⟨hp, hpol, hl⟩ := (tie_iff o y eY).2 ht
    exact ⟨fdeg_host D ▸ hG, (isGood_iff L).2 hL, hm, hp, hpol, hl, fun τ i => (hu τ i).2 (hv τ i), hx⟩

theorem clauses_iff_existsUnique (T : Core D) (j : ℕ) (La : ℝ) (k : (T.U j T.σ₀).Comp)
    (x₀ : ((T.U j T.σ₀).X k).dom) :
    letI := T.Q.H.starRing
    ∀ (o : LamObj T.Q.c (T.Q.Dw j).p (T.Q.Dw j).q) (L : IndefiniteRowSideFullHecke.LatticeLetterSources.LamLetters o) (σ : o.K₁ →+* ℂ)
      (y : FrPt (T.Q.Xo j) T.Q.c o.K₁) (ψ : o.xB.P.A.left ⟶ (T.Q.Xo j).univ.t.G.left),
      IndefiniteRowSideFullHecke.LatticeLetterSources.LamPtClauses (T.U j T.σ₀) k x₀ La o L σ y ψ ↔
        ∃! p : (o.K₁ →ₐ[T.Q.c.F] CAt T.σ₀) × (o.xB.P.A ≅ Over.mk (gxSnd y.x)),
          (embEquiv T.σ₀ o.K₁ p.1).1 = σ ∧ p.2.hom.left ≫ gxFst y.x = ψ ∧
            LamPtClauses T j La k x₀ o ((lettersEquiv o).symm L) p.1 y p.2 := by
  letI := T.Q.H.starRing
  intro o L σ y ψ
  obtain ⟨L, rfl⟩ := (lettersEquiv o).surjective L
  rw [Equiv.symm_apply_apply]
  constructor
  · intro h
    obtain ⟨eY, rfl, hu⟩ := existsUnique_iso h.2.2.2.2.1.1.1
    refine ⟨((embEquiv T.σ₀ o.K₁).symm ⟨σ, h.2.2.2.1⟩, eY), ⟨rfl, rfl, (clauses_iff T j La k x₀ o L _ y eY).2 h⟩, ?_⟩
    rintro ⟨σ', e'⟩ ⟨h₁, h₂, -⟩
    exact Prod.ext ((Equiv.eq_symm_apply _).2 (Subtype.ext h₁)) (hu e' h₂)
  · rintro ⟨⟨σ₁, eY⟩, ⟨rfl, rfl, h⟩, -⟩
    exact (clauses_iff T j La k x₀ o L σ₁ y eY).1 h

theorem conclusion_iff (T : Core D) (j : ℕ) (La : ℝ) (k : (T.U j T.σ₀).Comp) (x₀ : ((T.U j T.σ₀).X k).dom) :
    letI := T.Q.H.starRing
    (∃ (o : LamObj T.Q.c (T.Q.Dw j).p (T.Q.Dw j).q) (L : LamLetters o) (σ₁ : o.K₁ →ₐ[T.Q.c.F] CAt T.σ₀)
      (y : FrPt (T.Q.Xo j) T.Q.c o.K₁) (eY : o.xB.P.A ≅ Over.mk (gxSnd y.x)),
      LamPtClauses T j La k x₀ o L σ₁ y eY) ↔
    ∃ (o : IndefiniteRowSideFullHecke.LatticeLetterSources.CMObj (T.Q.Dw j) T.Q.c) (L : IndefiniteRowSideFullHecke.LatticeLetterSources.LamLetters o) (σ₁ : o.K₁ →+* ℂ)
      (y : FrPt (T.Q.Xo j) T.Q.c o.K₁) (eY : o.xB.P.A.left ⟶ (T.Q.Xo j).univ.t.G.left),
      IndefiniteRowSideFullHecke.LatticeLetterSources.LamPtClauses (T.U j T.σ₀) k x₀ La o L σ₁ y eY := by
  letI := T.Q.H.starRing
  constructor
  · rintro ⟨o, L, σ₁, y, eY, h⟩
    exact ⟨o, _, _, y, _, (clauses_iff T j La k x₀ o L σ₁ y eY).1 h⟩
  · rintro ⟨o, L, σ, y, ψ, h⟩
    obtain ⟨p, ⟨-, -, h'⟩, -⟩ := (clauses_iff_existsUnique T j La k x₀ o L σ y ψ).1 h
    exact ⟨o, _, p.1, y, p.2, h'⟩

theorem lattice_iff {T : Core D} (h : LawsCore T) {j : ℕ} (hj : InR D j) (k : (T.U j T.σ₀).Comp)
    (Xx : DataX D.host.E D.R.r) (hX : Xx.toData = (T.U j T.σ₀).X k) :
    (∀ a ∈ D.host.AA, ∀ v ∈ Xx.L', a • v ∈ Xx.Λ) ↔
      Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} :=
  ⟨lattice_eq_span_hostIdeal_smul D T h j hj k Xx hX, fun e a ha v hv => by
    rw [e]; exact Submodule.subset_span ⟨a, ha, v, hv, rfl⟩⟩

theorem frame_eq {r : ℕ} (Xx : DataX E r) {X : Data E r} (hX : Xx.toData = X) (x : Frame X.Ψ r) :
    (hX ▸ x : Frame Xx.Ψ r) = IndefiniteRowSideFullHecke.LatticeLetterSources.frameOf Xx hX x := by
  subst hX; rfl

theorem lamPtSt_at_iff (T : Core D) (j : ℕ) (La : ℝ) :
    LamPtSt T j La ↔ (LawsCore T → InR D j →
      ∀ (k : (T.U j T.σ₀).Comp) (Xx : DataX D.host.E D.R.r) (hX : Xx.toData = (T.U j T.σ₀).X k),
        Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} →
        ∀ (x₀ : ((T.U j T.σ₀).X k).dom) (lam : Fin D.R.r → Fin D.R.r → D.host.E),
          LamBasis Xx La (IndefiniteRowSideFullHecke.LatticeLetterSources.frameOf Xx hX x₀.1) lam →
          letI := T.Q.H.starRing
          ∃ (o : IndefiniteRowSideFullHecke.LatticeLetterSources.CMObj (T.Q.Dw j) T.Q.c) (L : IndefiniteRowSideFullHecke.LatticeLetterSources.LamLetters o) (σ₁ : o.K₁ →+* ℂ)
            (y : FrPt (T.Q.Xo j) T.Q.c o.K₁) (eY : o.xB.P.A.left ⟶ (T.Q.Xo j).univ.t.G.left),
            IndefiniteRowSideFullHecke.LatticeLetterSources.LamPtClauses (T.U j T.σ₀) k x₀ La o L σ₁ y eY) :=
  ⟨fun h hT hj k Xx hX hL x₀ lam hb => (conclusion_iff T j La k x₀).1
      (h hT hj k x₀ Xx hX ((lattice_iff hT hj k Xx hX).2 hL) lam ((frame_eq Xx hX x₀.1).symm ▸ hb)),
    fun h hT hj k x₀ Xx hX hL lam hb => (conclusion_iff T j La k x₀).2
      (h hT hj k Xx hX ((lattice_iff hT hj k Xx hX).1 hL) x₀ lam (frame_eq Xx hX x₀.1 ▸ hb))⟩

theorem lamPtSt_iff (T : Core D) (j : ℕ) : (∀ La, LamPtSt T j La) ↔ IndefiniteRowSideFullHecke.LatticeLetterSources.LamPtSt T j :=
  ⟨fun h hT hj k Xx hX hL x₀ lam La => (lamPtSt_at_iff T j La).1 (h La) hT hj k Xx hX hL x₀ lam,
    fun h La => (lamPtSt_at_iff T j La).2 fun hT hj k Xx hX hL x₀ lam => h hT hj k Xx hX hL x₀ lam La⟩

theorem comparison :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l)
      (nΨ n' : ℕ) (o : LamObj c nΨ n') (L : LamLetters o),
      (∀ k w, L.IsLetter k w ↔ (lettersEquiv o L).IsLetter k w) ∧ (L.IsGood ↔ (lettersEquiv o L).IsGood)) ∧
    (∀ (D : D7) (T : Core D) (j : ℕ) (La : ℝ) (k : (T.U j T.σ₀).Comp) (x₀ : ((T.U j T.σ₀).X k).dom),
      letI := T.Q.H.starRing
      (∀ (o : LamObj T.Q.c (T.Q.Dw j).p (T.Q.Dw j).q) (L : LamLetters o) (σ₁ : o.K₁ →ₐ[T.Q.c.F] CAt T.σ₀)
        (y : FrPt (T.Q.Xo j) T.Q.c o.K₁) (eY : o.xB.P.A ≅ Over.mk (gxSnd y.x)),
        LamPtClauses T j La k x₀ o L σ₁ y eY ↔
          IndefiniteRowSideFullHecke.LatticeLetterSources.LamPtClauses (T.U j T.σ₀) k x₀ La o (lettersEquiv o L) (embEquiv T.σ₀ o.K₁ σ₁).1 y
            (eY.hom.left ≫ gxFst y.x)) ∧
      ∀ (o : LamObj T.Q.c (T.Q.Dw j).p (T.Q.Dw j).q) (L : IndefiniteRowSideFullHecke.LatticeLetterSources.LamLetters o) (σ : o.K₁ →+* ℂ)
        (y : FrPt (T.Q.Xo j) T.Q.c o.K₁) (ψ : o.xB.P.A.left ⟶ (T.Q.Xo j).univ.t.G.left),
        IndefiniteRowSideFullHecke.LatticeLetterSources.LamPtClauses (T.U j T.σ₀) k x₀ La o L σ y ψ ↔
          ∃! p : (o.K₁ →ₐ[T.Q.c.F] CAt T.σ₀) × (o.xB.P.A ≅ Over.mk (gxSnd y.x)),
            (embEquiv T.σ₀ o.K₁ p.1).1 = σ ∧ p.2.hom.left ≫ gxFst y.x = ψ ∧
              LamPtClauses T j La k x₀ o ((lettersEquiv o).symm L) p.1 y p.2) ∧
    (∀ (D : D7) (T : Core D), LawsCore T → ∀ j, InR D j → ∀ (k : (T.U j T.σ₀).Comp) (Xx : DataX D.host.E D.R.r),
      Xx.toData = (T.U j T.σ₀).X k → ((∀ a ∈ D.host.AA, ∀ v ∈ Xx.L', a • v ∈ Xx.Λ) ↔
        Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u})) ∧
    ∀ (D : D7) (T : Core D) (j : ℕ), (∀ La, LamPtSt T j La) ↔ IndefiniteRowSideFullHecke.LatticeLetterSources.LamPtSt T j :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ L => ⟨isLetter_iff L, isGood_iff L⟩,
    fun _ T j La k x₀ => ⟨clauses_iff T j La k x₀, clauses_iff_existsUnique T j La k x₀⟩,
    fun _ _ h _ hj k Xx hX => lattice_iff h hj k Xx hX, fun _ => lamPtSt_iff⟩

end GlobalTheory.FramedCMPointCompare
