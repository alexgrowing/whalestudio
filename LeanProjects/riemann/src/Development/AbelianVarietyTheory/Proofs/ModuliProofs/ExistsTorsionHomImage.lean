import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionDescentFiniteEtaleCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionToG
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtOfIsFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAdicColimitOfIsFiniteNoetherian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartImageGenericStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartImagePullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionRepresentableFiniteEtaleStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPtsEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsRepMap

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorsionFormCompare GlobalTheory.TorusModel GlobalTheory.FieldRestrictionTest

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem isIota_zero {F : Type} [Field F] [Algebra (FractionRing R) F] (hB : D.TauBimult) {h : GtPtF D F}
    (hh : h.IsZero) : GtPtF.IsIota 0 h := by
  obtain ⟨hb, hv⟩ := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isZero_iff h).1 hh
  refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  have t := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
  exact (hv χ y J hJ).trans (mul_eq_left.1 t.symm).symm

variable {Gt : Over (Sp R)} [GrpObj Gt] {Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T}

theorem nsmul_eq (hΦ : Represents Φ) (k : ℕ) {T : Over (Sp R)} (x : T ⟶ Gt) {h : GtPt D T}
    (H : GtPt.IsNsmul k (Φ T x) h) : h = Φ T (x ^ k) := by
  obtain ⟨u, u0, us, rfl⟩ := H
  have : ∀ i : Fin (k + 1), u i = Φ T (x ^ (i : ℕ)) := fun i => by
    induction i using Fin.induction with
    | zero => exact isZero_unique u0 (by simpa using isZero_one hΦ T)
    | succ i ih =>
      have h := us i
      rw [ih] at h
      rw [Fin.val_succ, pow_succ]
      exact isAdd_unique h (hΦ.2 T _ _)
  exact this (Fin.last k)

theorem iota_pull_eq {W : (Sp R).Opens} {ψW : PsiOn D W} {T T' : Over W.toScheme} (h₁ h₂ : T' ⟶ T) {y : D.X}
    {g : GtPt D (overW W T)} (hg : GtPt.IsIotaW ψW y g) {g₁ g₂ : GtPt D (overW W T')}
    (H₁ : GtPt.IsPull ((Over.map W.ι).map h₁).left g g₁) (H₂ : GtPt.IsPull ((Over.map W.ι).map h₂).left g g₂) :
    g₁ = g₂ := by
  have key : ∀ (h : T' ⟶ T) (g' : GtPt D (overW W T')), GtPt.IsPull ((Over.map W.ι).map h).left g g' →
      g'.b = DegPre.cT D _ y ∧ ∀ χ z J, Good D.P.L z J →
        val (g'.s χ) (𝟙 _) z J = val (ψW.tau y χ) T'.hom z J := fun h g' H => by
    refine ⟨?_, fun χ z J hJ => ?_⟩
    · have : g'.b = (Over.map W.ι).map h ≫ g.b := Over.OverMorphism.ext H.1
      rw [this, hg.1, DegPre.cT, comp_toUnit_assoc]
    · refine (val_corr hJ (H.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (hg.2 χ) _).trans
        ((val_pull hJ _ _ _).trans ?_)))
      rw [Category.id_comp]
      exact congrArg (fun m => val (ψW.tau y χ) m z J) (Over.w h)
  obtain ⟨a₁, b₁⟩ := key h₁ g₁ H₁
  obtain ⟨a₂, b₂⟩ := key h₂ g₂ H₂
  exact pt_ext (a₁.trans a₂.symm) fun χ z J hJ => (b₁ χ z J hJ).trans (b₂ χ z J hJ).symm

theorem isPullF_iff_eq (hΦ : Represents Φ) {F : Type} [Field F] [Algebra (FractionRing R) F] {T : Over (Sp R)}
    (σ : TF (R := R) F ⟶ T) (x : T ⟶ Gt) (g : GtPtF D F) :
    GtPt.IsPullF F σ.left (Φ T x) g ↔ toT g = Φ _ (σ ≫ x) :=
  ⟨fun H => isPull_unique (k := σ) H (hΦ.1 _ _ σ x), fun H => (isPullF_iff_isPull _ _ _).2 (H ▸ hΦ.1 _ _ σ x)⟩

end Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

theorem isImage_mul {P : PELUnif I t} (hP : P.TorsionIso) {F : Type} [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] {k : ℕ} (hk : 1 ≤ k) {q q' q'' : QkPt P.D.toPre F k} (hq : QkAdd q q' q'')
    {v v' v'' : TF (R := R) F ⟶ t.G} (h : IsImage P F k q v.left) (h' : IsImage P F k q' v'.left)
    (h'' : IsImage P F k q'' v''.left) : v'' = v * v' := by
  obtain ⟨f, f1, -, -, f4, -⟩ := hP F k hk
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.LevelRatio.exists_ptsEquiv P.U.toUnifPre F
  have key : ∀ {q : QkPt P.D.toPre F k} {v : TF (R := R) F ⟶ t.G}, IsImage P F k q v.left → v = Ψ (f q) := by
    rintro q v ⟨a, e, ha⟩
    obtain rfl := (f1 _ _).1 ha
    exact Over.OverMorphism.ext (e.symm.trans (hΨ _).symm)
  rw [key h, key h', key h'', f4 _ _ _ hq, map_mul]

theorem exists_repMap : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ y N p₀, PairRep ψW k y N p₀ → ∃ v : overW W N ⟶ t.G, v ^ k = 1 ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left), OverGen F (overW W N) x → ∀ q : QkPt P.D.toPre F k, QkPtW.IsPullF F x p₀ q → IsImage P F k q (x ≫ v.left) := by
  intro E _ _ _ H R _ _ _ _ hR t P W hW hp ψW k hk y N p₀ hN
  have := hR.1
  have := hR.2.2.1
  have hP := GlobalTheory.FlatTors.torsionIso_holds E H R _ hR t P
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.generic_part_image_pullback E H R hR t P W hW hp ψW k hk y N p₀ hN
  obtain ⟨Z, g₀, x₀, z1, z2, -, z3, z4, z5, z6⟩ := GlobalTheory.FlatTors.exists_torsion_toG E H R hR t P W hW hp ψW k hk
  have hZ : IsFinitePart P.U.toUnifPre k Z g₀ x₀ :=
    ⟨z1, z2, z3, z4, z5, GlobalTheory.TorsMono.mono_torsion E H R hR t P W hW hp ψW k hk Z g₀ x₀ z1 z3 z4 z6,
      GlobalTheory.FiniteTorsLift.main E H R hR t P W hW hp ψW k hk Z g₀ x₀ z1 z3 z4 z6, z6⟩
  have hgen := GlobalTheory.T.finite_part_image_generic E H R hR t P W hW hp ψW k hk Z g₀ x₀ hZ
  obtain ⟨Gt, _, _, Φ, hΦ, -⟩ := exists_represents P.D.toPre
  obtain ⟨c₀, rfl⟩ := (Φ Z).surjective g₀
  have hc₀ := (tors_iff hΦ k c₀).1 z3
  obtain ⟨c, hc⟩ := (Φ (overW W N)).surjective p₀.g
  let n₁ : overW W (N ⊗ N) ⟶ overW W N := (Over.map W.ι).map (fst N N)
  let n₂ : overW W (N ⊗ N) ⟶ overW W N := (Over.map W.ι).map (snd N N)
  have hk₀ : GtPt.IsIotaW ψW p₀.y (Φ _ (c ^ k)) := by
    obtain ⟨h, h1, h2⟩ := p₀.eq
    rw [← hc] at h1
    rwa [nsmul_eq hΦ k c h1] at h2
  have hpow : n₁ ≫ c ^ k = n₂ ≫ c ^ k :=
    (Φ _).injective (iota_pull_eq (fst N N) (snd N N) hk₀ (hΦ.1 _ _ _ _) (hΦ.1 _ _ _ _))
  have hδ : ((n₂ ≫ c)⁻¹ * (n₁ ≫ c)) ^ k = 1 := by
    rw [mul_pow, inv_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, hpow, inv_mul_cancel]
  obtain ⟨e, he, -⟩ := z4 _ _ ((tors_iff hΦ k _).2 hδ)
  have he' : e ≫ c₀ = (n₂ ≫ c)⁻¹ * (n₁ ≫ c) := (isPull_iff_comp hΦ _ _ _).1 he
  obtain ⟨v, hv, hv'⟩ := GlobalTheory.T.torsion_descent_finite_etale_cover R W t.G k t.semi.separated
    (GlobalTheory.T.torsion_representable_finite_etale E H R hR t P W hW hp ψW k hk).2.1 N hN.1 hN.2.1 u (e ≫ x₀) hu
    (by rw [← MonObj.comp_pow, z5, MonObj.comp_one]) (fun F _ _ _ a b s ha hb => by
      obtain ⟨qa, hqa, -⟩ := (existsUnique_pair_iff (F := F) (a ≫ genι (overW W N)).left p₀).2
        (Over.w (a ≫ genι (overW W N)))
      obtain ⟨qb, hqb, -⟩ := (existsUnique_pair_iff (F := F) (b ≫ genι (overW W N)).left p₀).2
        (Over.w (b ≫ genι (overW W N)))
      obtain ⟨g, hg⟩ := exists_isPullF (s ≫ e) (Φ Z c₀)
      obtain ⟨h, h1, h2⟩ := z3
      obtain ⟨h', hh⟩ := exists_isPullF (s ≫ e) h
      let qd : QkPt P.D.toPre F k := ⟨0, g, h', isNsmul_restrict hg hh h1,
        isIota_zero P.D.tau_bimult (isZero_restrict hh h2)⟩
      have ia : IsImage P F k qa (a ≫ u).left := hu' F a.left (Over.w a) qa hqa
      have ib : IsImage P F k qb (b ≫ u).left := hu' F b.left (Over.w b) qb hqb
      have id : IsImage P F k qd (s ≫ e ≫ x₀).left := by
        rw [← Category.assoc]
        exact hgen F (s ≫ e).left (Over.w _) qd rfl hg
      refine isImage_mul hP hk ⟨qa, ?_, ?_, qk_equiv_refl P.D.tau_bimult qa⟩ ib id ia
      · exact hqa.1.trans (hqb.1.symm.trans (add_zero _).symm)
      · have ea := hqa.2
        have eb := hqb.2
        rw [← hc] at ea eb
        rw [isPullF_iff_eq hΦ] at ea eb hg
        have add := hΦ.2 _ ((b ≫ genι (overW W N)) ≫ c) ((s ≫ e) ≫ c₀)
        have em : ((b ≫ genι (overW W N)) ≫ c) * ((s ≫ e) ≫ c₀) = (a ≫ genι (overW W N)) ≫ c := by
          rw [← ha, ← hb, Category.assoc, Category.assoc, Category.assoc, he', ← MonObj.comp_mul,
            mul_inv_cancel_left]
        rw [em, ← ea, ← eb, ← hg] at add
        exact add)
  refine ⟨v, hv, fun F _ _ _ x hx q hq => ?_⟩
  let x' : Sp F ⟶ (genPart (overW W N)).left := pullback.lift x (jFK (R := R) F) hx
  have e₁ : x' ≫ (genι (overW W N)).left = x := pullback.lift_fst _ _ _
  have := hu' F x' (by
    show x' ≫ (genι (overW W N)).left ≫ _ = _
    rw [← Category.assoc, e₁]
    exact hx) q (e₁.symm ▸ hq)
  rwa [← hv', Over.comp_left, ← Category.assoc, e₁] at this

end GlobalTheory.TorsRepMap
