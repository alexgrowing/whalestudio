import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasing
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZPartEig

theorem heckePolyOf_coeff {L : Type} [Field L] (n q : ℕ) (a : ℕ → L) {k : ℕ} (hk : k ≤ n) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff k = (-1) ^ k * (q : L) ^ (k * (k - 1) / 2) * a k := by
  classical
  simp only [Formalism.L2.Col.heckePolyOf, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_range.2 (Nat.lt_succ_of_le hk))]

theorem heckePolyOf_val_eq {L : Type} [Field L] [CharZero L] (n q : ℕ) (hq : q ≠ 0) (a b : ℕ → L)
    (h : Formalism.L2.Col.heckePolyOf n q a = Formalism.L2.Col.heckePolyOf n q b) {k : ℕ} (hk : k ≤ n) : a k = b k := by
  have e := congrArg (fun p => Polynomial.coeff p k) h
  simp only [heckePolyOf_coeff n q _ hk] at e
  have hne : ((-1 : L) ^ k * (q : L) ^ (k * (k - 1) / 2)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq))
  exact mul_left_cancel₀ hne e

theorem apply_of_mem_maxGen {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : K →+* ℂ) (j : V →ₛₗ[σ] H) (T : Module.End K V)
    (N : Module.End ℂ H) (hN : Commute N (LinearMap.adjoint N)) (hj : ∀ f, j (T f) = N (j f)) (c : K) (f : V)
    (hf : f ∈ T.maxGenEigenspace c) : N (j f) = σ c • j f := by
  have key : ∀ (k : ℕ) (g : V), j (((T - c • (1 : Module.End K V)) ^ k : Module.End K V) g) =
      (((N - σ c • (1 : Module.End ℂ H)) ^ k : Module.End ℂ H) (j g)) := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
      simp [hj, map_smulₛₗ]
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hf
  have h0 : (((N - σ c • (1 : Module.End ℂ H)) ^ k : Module.End ℂ H) (j f)) = 0 := by rw [← key, hk, map_zero]
  have hmem : j f ∈ N.maxGenEigenspace (σ c) := (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, h0⟩
  rw [GlobalTheory.NormalFamily.maxGenEigenspace_eq hN] at hmem
  exact Module.End.mem_eigenspace_iff.1 hmem

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

open GlobalTheory.ConjScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def OpLab (R : RealDat3 D A3 Ks) (i : Fin D.R.m) : (A3.liftI i A3.A.μ0).OpIx → Pl D.host.E → List ℤ → Prop :=
  Sum.elim
    (fun k P d => R.pl ((A3.A.fam.L i A3.A.μ0).pl k.1) = P ∧ k.2 ≤ (Vc D i).rank ∧ d = splitLab (Vc D i).rank k.2)
    (fun k P d => R.plI ((A3.liftI i A3.A.μ0).plI k.1) = P ∧ Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2 ∧
      d = GlobalTheory.Hk3.labIn (Vc D i).rank k.2)

theorem opLab_ops (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i A3.A.μ0).H) (hh : GlobalTheory.Hk3.IsOpsV R.toRealDat i A3.A.μ0 h) :
    ∀ idx P d, OpLab R i idx P d → GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧
      ∀ f, R.jV i A3.A.μ0 ((A3.liftI i A3.A.μ0).opAll idx f) = h P (Finsupp.single d 1) (R.jV i A3.A.μ0 f) := by
  have hlev := hC.base.lev
  have hfam := hC.base.fam
  have hmod := hC.base.models
  have c3 := (GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC).2.2.1
  rintro (⟨⟨P', hP'⟩, k⟩ | ⟨⟨Q, hQ⟩, s'⟩) P d hc
  · obtain ⟨rfl, hk, rfl⟩ := hc
    refine ⟨((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hlev).2.2.2 hfam A3.A.μ0 P' hP').1, fun f => ?_⟩
    exact (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hlev hfam hmod).2 i A3.A.μ0 h hh ⟨P', hP'⟩ k hk f
  · obtain ⟨rfl, hs, rfl⟩ := hc
    have hty : ∀ k : A3.okI A3.A.μ0 × List ℕ, Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2 →
        GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 (R.plI k.1) ∧ Formalism.DivisionValues.conjPl (R.plI k.1) = R.plI k.1 ∧
          (GlobalTheory.Hk3.labIn (Vc D i).rank k.2).Pairwise (fun a b => b ≤ a) := fun k hk =>
      ⟨(c3 A3.A.μ0 k.1 k.1.2).1, (c3 A3.A.μ0 k.1 k.1.2).2,
        ((GlobalTheory.Hk3.labIn_selfDual_iff (Vc D i).rank _).2 ⟨k.2, hk.2.2, hk.1, hk.2.1, rfl⟩).2.1⟩
    refine ⟨(c3 A3.A.μ0 Q hQ).1, fun f => ?_⟩
    exact (GlobalTheory.InertHeckeLift.inert_lifts R.toRealDat F.lv2 hlev hfam hmod i A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
      (fun k => R.plI k.1) (fun k => GlobalTheory.Hk3.labIn (Vc D i).rank k.2) (A3.heckeLI i A3.A.μ0)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2) hty (hC.inert.hL i A3.A.μ0).some (⟨Q, hQ⟩, s') hs).2.2.2 h hh f

theorem exists_opLab (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m) :
    ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → RelLab (Vc D i) P d → ∃ idx, OpLab R i idx P d := by
  have c3 := (GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC).2.2.2.1
  intro P d hg hr
  rcases hr with ⟨hc, k, hk, rfl⟩ | ⟨hc, hl⟩
  · obtain ⟨P0, hP0, rfl⟩ := (c3 P hg).2 hc
    exact ⟨Sum.inl (⟨P0, hP0⟩, k), rfl, hk, rfl⟩
  · obtain ⟨Q, hQ, rfl⟩ := (c3 P hg).1 hc
    obtain ⟨hlen, hpw, hdual⟩ := (GlobalTheory.LabChar.labels_char (Vc D i) _ d).1 hl
    obtain ⟨s', h1, h2, h3, rfl⟩ := (GlobalTheory.Hk3.labIn_selfDual_iff (Vc D i).rank d).1 ⟨hlen, hpw, hdual hc⟩
    exact ⟨Sum.inr (⟨Q, hQ⟩, s'), rfl, ⟨h2, h3, h1⟩, rfl⟩

theorem opLab_val_eq (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ)) :
    ∀ idx P d, OpLab R i idx P d → ∀ y y', (A3.liftI i A3.A.μ0).HasRes3 q y → (A3.liftI i A3.A.μ0).HasRes3 q y' →
      y idx = y' idx := by
  rintro (⟨⟨P', hP'⟩, k⟩ | ⟨Q, s'⟩) P d hc y y' hy hy'
  · obtain ⟨-, hk, -⟩ := hc
    have hq : (A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩ ≠ 0 := by
      show A3.A.q P' ≠ 0
      rw [((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.base.lev).2.2.2 hC.base.fam A3.A.μ0 P' hP').2.2]
      exact fun h0 => (R.pl P').ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have e : Formalism.L2.Col.heckePolyOf (A3.A.fam.L i A3.A.μ0).n ((A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩)
          (fun j => y (Sum.inl (⟨P', hP'⟩, j))) =
        Formalism.L2.Col.heckePolyOf (A3.A.fam.L i A3.A.μ0).n ((A3.A.fam.L i A3.A.μ0).q ⟨P', hP'⟩)
          (fun j => y' (Sum.inl (⟨P', hP'⟩, j))) :=
      (hy.1 ⟨P', hP'⟩).trans (hy'.1 ⟨P', hP'⟩).symm
    have hk' : k ≤ (A3.A.fam.L i A3.A.μ0).n := by
      have e2 : (A3.A.fam.L i A3.A.μ0).n = A3.A.r + A3.A.t := rfl
      rw [e2, ← R.B.rankL i]; exact hk
    exact heckePolyOf_val_eq _ _ hq _ _ e hk'
  · exact (hy.2 (Q, s')).trans (hy'.2 (Q, s')).symm

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem thetaLiftPoint_mem_jointEigenspace_of_part (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : (R.toCx3 F).H3W F.cr false) (i : Fin D.R.m)
    (p : A3.fam3.base3.Ix) (x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL)
    (hx : (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p) :
    F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x ∈ (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum (A3.fam3.tr3 i p.1) := by
  have hZ := (hW i p x).2 hx
  have h2 : (A3.A.fam.L i A3.A.μ0).vE (A3.A.fam.lvlA F.P0 F.ψ0) *ᵥ
      ((A3.A.fam.L i A3.A.μ0).zE (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).zs.Zl i A3.A.μ0) *ᵥ x) ∈
      ((A3.liftI i A3.A.μ0).inertTypeEigenspaceSum (A3.fam3.tr3 i p.1)).map
        ((A3.A.fam.L i A3.A.μ0).S.basis.equivFun : (A3.A.fam.L i A3.A.μ0).S.Forms →ₗ[D.what₂.LL] _) := hZ
  obtain ⟨g, hg, hge⟩ := Submodule.mem_map.1 h2
  convert hg using 1
  rw [← LinearEquiv.symm_apply_apply (A3.A.fam.L i A3.A.μ0).S.basis.equivFun g]
  erw [hge]
  rfl

end GlobalTheory.ZPartEig

namespace GlobalTheory.ZPartEig

open GlobalTheory.ConjScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

def eigVal (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ)) (P : Pl D.host.E) (d : List ℤ) :
    D.what₂.LL :=
  if hx : (∃ y, (A3.liftI i A3.A.μ0).HasRes3 q y) ∧ ∃ idx, OpLab R i idx P d then hx.1.choose hx.2.choose else 0

theorem eig_of_mem (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (i : Fin D.R.m)
    (q : Typ3 D.what₂.LL Pl0 I0 (List ℕ))
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i A3.A.μ0).H) (hh : GlobalTheory.Hk3.IsOpsV R.toRealDat i A3.A.μ0 h)
    (hn : GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0) h) (f : (A3.A.fam.L i A3.A.μ0).S.Forms)
    (hf : f ∈ (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum q) :
    ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → RelLab (Vc D i) P d →
      h P (Finsupp.single d 1) (R.jV i A3.A.μ0 f) = D.what₂.embLL (eigVal R i q P d) • R.jV i A3.A.μ0 f := by
  let E : Submodule ℂ (R.HV i A3.A.μ0).H :=
    ⨅ (P : Pl D.host.E) (d : List ℤ) (_ : GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P ∧ RelLab (Vc D i) P d),
      (h P (Finsupp.single d 1)).eigenspace (D.what₂.embLL (eigVal R i q P d))
  have hle : (A3.liftI i A3.A.μ0).inertTypeEigenspaceSum q ≤ E.comap (R.jV i A3.A.μ0) := by
    unfold InertDat3.inertTypeEigenspaceSum Formalism.L2.Col.eigSum
    refine iSup₂_le fun y hy g hg => ?_
    rw [Submodule.mem_comap]
    simp only [E, Submodule.mem_iInf]
    rintro P d ⟨hgd, hr⟩
    have hex : (∃ y, (A3.liftI i A3.A.μ0).HasRes3 q y) ∧ ∃ idx, OpLab R i idx P d :=
      ⟨⟨y, hy⟩, exists_opLab R F hC i P d hgd hr⟩
    have ha : eigVal R i q P d = hex.1.choose hex.2.choose := by
      unfold eigVal
      rw [dif_pos hex]
    have ha' : eigVal R i q P d = y hex.2.choose :=
      ha.trans (opLab_val_eq R F hC i q _ P d hex.2.choose_spec _ _ hex.1.choose_spec hy)
    have hop := opLab_ops R F hC i h hh _ P d hex.2.choose_spec
    have hN : Commute (h P (Finsupp.single d 1)) (LinearMap.adjoint (h P (Finsupp.single d 1))) :=
      (congrArg (Commute (h P (Finsupp.single d 1))) (hn.2 P hop.1 (Finsupp.single d 1))).mpr (hn.1 P P hop.1 hop.1 _ _)
    have key := apply_of_mem_maxGen D.what₂.embLL (R.jV i A3.A.μ0) ((A3.liftI i A3.A.μ0).opAll hex.2.choose) _ hN hop.2
      (y hex.2.choose) g (Formalism.L2.Col.eigAt_le (A3.liftI i A3.A.μ0).opAll y hex.2.choose hg)
    exact Module.End.mem_eigenspace_iff.2 (key.trans (congrArg (fun c => D.what₂.embLL c • R.jV i A3.A.μ0 g) ha'.symm))
  intro P d hg hr
  have e1 := hle hf
  rw [Submodule.mem_comap] at e1
  simp only [E, Submodule.mem_iInf] at e1
  exact Module.End.mem_eigenspace_iff.1 (e1 P d ⟨hg, hr⟩)

theorem points_eig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → (R.toCx3 F).H3W F.cr false → ∀ i p, ∃ a, ∀ x, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p → GlobalTheory.ConjScalar.EigK R.toRealDat i a (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F s _hOk hC hW i p
  obtain ⟨h, hh, hn⟩ :=
    (GlobalTheory.DefiniteOps.definite_ops R.toRealDat F.lv2 hC.base.lev hC.base.fam hC.base.models).2 i A3.A.μ0
  refine ⟨eigVal R i (A3.fam3.tr3 i p.1), fun x hx => ?_⟩
  have hm := thetaLiftPoint_mem_jointEigenspace_of_part R F hW i p x hx
  intro P d hg hr
  have e1 := eig_of_mem R F hC i _ h hh hn _ hm P d hg hr
  have e2 := hh P hg (Finsupp.single d 1) (R.jV i A3.A.μ0 (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x))
  exact e2.symm.trans ((congrArg (R.HV i A3.A.μ0).e e1).trans (map_smul _ _ _))

end GlobalTheory.ZPartEig
