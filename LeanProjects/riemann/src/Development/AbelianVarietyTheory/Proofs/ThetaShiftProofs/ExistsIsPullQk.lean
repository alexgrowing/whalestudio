import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsFibreIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

noncomputable section

namespace GlobalTheory.ArcPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PsiEvenPull (proj)
open scoped CategoryTheory.Obj

open NumberField GlobalTheory.TorusExt

section Qk

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

def IsPullQk (hD : IsPullDeg φ D D') {k : ℕ} (p : QkPt D (FractionRing R) k) (p' : QkPt D' (FractionRing R') k) : Prop :=
  ∃ _ : Algebra (FractionRing R) (FractionRing R'), Compat φ (FractionRing R') ∧
    ∃ q : QkPt D (FractionRing R') k, QkExt (algebraMap (FractionRing R) (FractionRing R')) p q ∧
      p'.y = hD.xe.symm q.y ∧ IsPullGtF φ hD (FractionRing R') q.g p'.g

theorem IsPullQk.ext {hD : IsPullDeg φ D D'} {k : ℕ} {p : QkPt D (FractionRing R) k} {p' : QkPt D' (FractionRing R') k}
    (h : IsPullQk hD p p') {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
    (hF : Compat φ F) {q : QkPt D F k} {q' : QkPt D' F k} (hq : QkExt (algebraMap _ F) p q)
    (hq' : QkExt (algebraMap _ F) p' q') : q'.y = hD.xe.symm q.y ∧ IsPullGtF φ hD F q.g q'.g := by
  obtain ⟨_, hK, q₀, e₀, hy, hg⟩ := h
  have hc : (algebraMap (FractionRing R') F).comp (algebraMap (FractionRing R) (FractionRing R')) =
      algebraMap (FractionRing R) F := IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r =>
    (congrArg (algebraMap (FractionRing R') F) (hK r)).trans (hF r).symm)
  have hs : spMap (algebraMap (FractionRing R) F) =
      spMap (algebraMap (FractionRing R') F) ≫ spMap (algebraMap (FractionRing R) (FractionRing R')) := by
    rw [← hc, spMap_comp]
  have e₁ : QkExt (algebraMap (FractionRing R') F) q₀ q := by
    refine ⟨hq.1.trans e₀.1.symm, ?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · rw [hq.2.1, e₀.2.1, hs, Category.assoc]
    · refine (val_corr hJ (hq.2.2 χ) _).trans ((val_pull hJ _ _ _).trans (Eq.trans ?_
        ((val_pull hJ _ _ _).trans ((val_corr hJ (e₀.2.2 χ) _).trans (val_pull hJ _ _ _))).symm))
      exact congrArg (fun r => val (p.g.s χ) r y J) ((congrArg (𝟙 _ ≫ ·) hs).trans (Category.assoc _ _ _).symm)
  exact ⟨by rw [hq'.1, hy, e₁.1], isPullGtF_ext hD hF _ (RingHom.comp_id _) hg e₁ hq'⟩

theorem exists_isPullQk (hG : GlobalFnsSt) (hφ : Function.Injective φ) (hD : IsPullDeg φ D D') (hB : D.TauBimult)
    {k : ℕ} (p : QkPt D (FractionRing R) k) : ∃ p', IsPullQk hD p p' := by
  letI : Algebra (FractionRing R) (FractionRing R') := (fracMap hφ).toAlgebra
  have hK : Compat φ (FractionRing R') := fracMap_algebraMap hφ
  have hB' := TauPull.tauBimult_pull hG hD hB
  obtain ⟨q, hq, -⟩ := existsUnique_qkExt (F' := FractionRing R') hB (algebraMap (FractionRing R) (FractionRing R'))
    (RingHom.comp_id _) p
  exact ⟨pullQk hD hG hK hB hB' q, _, hK, q, hq, rfl, isPullGtF_pullGt hD hG hK _⟩

end Qk

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

def pullTate (hG : GlobalFnsSt) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D₀ : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D₀ D') [Module (𝓞 E) D₀.X] [Module (𝓞 E) D'.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {oa' : letI := H.starRing; D'.OAct (𝓞 E)}
    (hx : ∀ (a : 𝓞 E) y, hD.xe (a • y) = a • hD.xe y)
    (ho : letI := H.starRing; ∀ a, (oa'.onB.act a).left ≫ proj hD = proj hD ≫ (oa.onB.act a).left)
    (hB : D₀.TauBimult) (hB' : D'.TauBimult) {F : Type} [Field F] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F] (hF : Compat φ F) (I : TateIsoQ D D₀ oa F) : TateIsoQ D D' oa' F :=
  letI := H.starRing
  { ζ := I.ζ
    ζ_prim := I.ζ_prim
    ζ_pow := I.ζ_pow
    ev := fun n a => pullQk hD hG hF hB hB' (I.ev n a)
    add := fun n hn a b => qkAdd_pullQk hD hG hF hB hB' (I.add n hn a b)
    lin := fun n hn x a => qkAct_pullQk hD hG hF hB hB' hx ho (I.lin n hn x a)
    ker := fun n hn a b => (equiv_pullQk hD hG hF hB hB' _ _).trans (I.ker n hn a b)
    onto := fun n hn p' => by
      obtain ⟨p, rfl⟩ := pullQk_surjective hD hG hF hB hB' p'
      obtain ⟨a, ha⟩ := I.onto n hn p
      exact ⟨a, (equiv_pullQk hD hG hF hB hB' _ _).2 ha⟩
    tower := fun n m hn hm a => by
      obtain ⟨q, h₁, h₂, h₃⟩ := I.tower n m hn hm a
      exact ⟨pullQk hD hG hF hB hB' q, congrArg hD.xe.symm h₁, isNsmul_pullGt hD hG hF h₂,
        (equiv_pullQk hD hG hF hB hB' _ _).2 h₃⟩
    isom := fun n hn a b => weilQkIs_pull hD hF rfl (isPullGtF_pullGt hD hG hF _) rfl (isPullGtF_pullGt hD hG hF _)
      (I.isom n hn a b) }

variable {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' O'' : Type} [CommRing O'] [IsDomain O']
  [CommRing O''] [IsDomain O''] {b : O →+* O'}

structure IsBC (f : O' →+* O'') (a : ArcIn D l β O' b) (a' : ArcIn D l β O'' (f.comp b))
    (hD : IsPullDeg f a.D₀ a'.D₀) : Prop where
  xe_smul : ∀ (x : 𝓞 E) (y : a'.D₀.X), hD.xe (x • y) = x • hD.xe y
  be_eq : ∀ y z : a'.D₀.X, a'.be y z = a.be (hD.xe y) (hD.xe z)
  act : letI := H.starRing
    ∀ x : 𝓞 E, (a'.oa.onB.act x).left ≫ hD.e.hom.left ≫ pullback.fst a.D₀.P.A.hom (specOf f) =
      (hD.e.hom.left ≫ pullback.fst a.D₀.P.A.hom (specOf f)) ≫ (a.oa.onB.act x).left
  eta : ∀ v, IsPullQk hD (a.eta v) (a'.eta v)
  etaA : ∀ v, IsPullQk hD (a.etaA v) (a'.etaA v)

def IsBC.xeL {f : O' →+* O''} {a : ArcIn D l β O' b} {a' : ArcIn D l β O'' (f.comp b)} {hD : IsPullDeg f a.D₀ a'.D₀}
    (h : IsBC f a a' hD) : a'.D₀.X ≃ₗ[𝓞 E] a.D₀.X := { hD.xe with map_smul' := h.xe_smul }

variable (hG : GlobalFnsSt) {f : O' →+* O''} (hf : Function.Injective f) (a : ArcIn D l β O' b) {D' : DegPre O''}
  (hD : IsPullDeg f a.D₀ D')

@[reducible] def pullModule : Module (𝓞 E) D'.X := hD.xe.module (𝓞 E)

theorem pullModule_smul (x : 𝓞 E) (y : D'.X) : letI := pullModule a hD; hD.xe (x • y) = x • hD.xe y :=
  hD.xe.apply_symm_apply _

def pullArc : ArcIn D l β O'' (f.comp b) :=
  letI := H.starRing
  letI := pullModule a hD
  have hx := pullModule_smul a hD
  have hB' := TauPull.tauBimult_pull hG hD a.bimult
  have ho := (exists_oAct hD hG hf a.oa hx).choose_spec
  { D₀ := D'
    mod := pullModule a hD
    oa := (exists_oAct hD hG hf a.oa hx).choose
    nontriv := have := a.nontriv; hD.xe.toEquiv.nontrivial
    even := PsiEvenPull.psiEven_pull hG _ _ f _ _ hD a.even
    bimult := hB'
    gen := fun y => psiUnitOn_pull hD hf y (a.gen _)
    w0 := traceFormTwistIso_of_pullback hD hf hx ho a.w0
    be := a.be.comp hD.xe.toAddMonoidHom.toIntLinearMap hD.xe.toAddMonoidHom.toIntLinearMap
    be_symm := fun y z => a.be_symm (hD.xe y) (hD.xe z)
    be_pos := fun y hy => a.be_pos (hD.xe y) (hD.xe.map_ne_zero_iff.2 hy)
    be_adj := fun x y z => by
      show a.be (hD.xe (x • y)) (hD.xe z) = a.be (hD.xe y) (hD.xe (H.bar x • z))
      rw [hx, hx, a.be_adj]
    be_dvd := fun y z => a.be_dvd (hD.xe y) (hD.xe z)
    eta := fun v => (exists_isPullQk hG hf hD a.bimult (a.eta v)).choose
    etaA := fun v => (exists_isPullQk hG hf hD a.bimult (a.etaA v)).choose
    geom := fun F _ _ _ r z hr hz f' hf' => by
      letI : Algebra (FractionRing O') F := ((algebraMap (FractionRing O'') F).comp (fracMap hf)).toAlgebra
      have hF : Compat f F := fun x => congrArg (algebraMap (FractionRing O'') F) (fracMap_algebraMap hf x)
      obtain ⟨h₁, I, h₂, h₃, h₄⟩ := a.geom F r z hr hz (f'.comp f) (RingHom.ext fun x => by
        rw [hf']; exact (hF x).symm)
      have lev : ∀ {k : ℕ} (p : QkPt a.D₀ (FractionRing O') k) (p' : QkPt D' (FractionRing O'') k) (e : QkPt a.D₀ F k),
          IsPullQk hD p p' → (∀ q, QkExt (algebraMap _ F) p q → QkPt.Equiv a.D₀ F q e) →
          ∀ q', QkExt (algebraMap _ F) p' q' → QkPt.Equiv D' F q' (pullQk hD hG hF a.bimult hB' e) := by
        intro k p p' e hp he q' hq'
        obtain ⟨q, hq, -⟩ := existsUnique_qkExt (F' := F) a.bimult (algebraMap (FractionRing O') F) (RingHom.comp_id _) p
        rw [(eq_pullQk_iff hD hG hF a.bimult hB' q q').2 (hp.ext hF hq hq'), equiv_pullQk]
        exact he q hq
      refine ⟨fun τ => ?_, pullTate hG hD hx ho a.bimult hB' hF I, h₂,
        fun v => lev _ _ _ (exists_isPullQk hG hf hD a.bimult (a.etaA v)).choose_spec (h₃ v),
        fun v hv => lev _ _ _ (exists_isPullQk hG hf hD a.bimult (a.eta v)).choose_spec (h₄ v hv)⟩
      obtain ⟨n, hn, hn'⟩ := h₁ τ
      refine ⟨n, (LiePull.lieMult_pull _ _ _ _ _ _ _ (ofRingAct a.oa.onB.toRingAct) _ (pull_grp hD) ho F _ τ n).2 ?_, ?_⟩
      · rw [← spMap_comp]; exact hn
      · rw [(({ hD.xe with map_smul' := hx } : D'.X ≃ₗ[𝓞 E] a.D₀.X)).finrank_eq]
        exact hn' }

theorem pullArc_D₀ : (pullArc hG hf a hD).D₀ = D' := rfl

theorem isBC_pullArc : IsBC f a (pullArc hG hf a hD) hD :=
  letI := H.starRing
  letI := pullModule a hD
  { xe_smul := pullModule_smul a hD
    be_eq := fun _ _ => rfl
    act := (exists_oAct hD hG hf a.oa (pullModule_smul a hD)).choose_spec
    eta := fun v => (exists_isPullQk hG hf hD a.bimult (a.eta v)).choose_spec
    etaA := fun v => (exists_isPullQk hG hf hD a.bimult (a.etaA v)).choose_spec }

theorem exists_isBC (hP : PolBaseChangeSt) (hG : GlobalFnsSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' O'' : Type}
    [CommRing O'] [IsDomain O'] [CommRing O''] [IsDomain O''] {b : O →+* O'} (a : ArcIn D l β O' b) (f : O' →+* O'')
    (hf : Function.Injective f) :
    ∃ (a' : ArcIn D l β O'' (f.comp b)) (hD : IsPullDeg f a.D₀ a'.D₀), IsBC f a a' hD ∧ a'.D₀.P.g = a.D₀.P.g := by
  obtain ⟨D', hD, -, hg⟩ := DegPull.exists_isPullDeg hP O' O'' f a.D₀ ⊤ (nonempty_psiOn_top _ a.gen) trivial
  exact ⟨pullArc hG hf a hD, hD, isBC_pullArc hG hf a hD, hg⟩

end GlobalTheory.ArcPull
