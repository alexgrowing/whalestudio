import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfGenerization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ActCommOfClosure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectFibreFromComplexCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.TripleTheta

open CharZeroPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ} {J : Type}

theorem map_bas {A : Type} [CommGroup A] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (u : D.La → A)
    (hu : ∀ x y, u (x + y) = u x * u y) (v : Fin (2 * g) → ℤ) :
    u (bas v) = ∏ i, u (bas (Pi.single i 1)) ^ v i := by
  rw [LatticeTorsion.eq_prod_zpow ((Pi.basisFun ℤ (Fin (2 * g))).map bas) u hu]
  simp

theorem map_nsmul' {A : Type} [Group A] (u : D.La → A) (hu : ∀ x y, u (x + y) = u x * u y) (n : ℕ) (x : D.La) :
    u (n • x) = u x ^ n :=
  (MonoidHom.mk' (fun x : Multiplicative D.La => u x.toAdd) fun _ _ => hu _ _).map_pow (Multiplicative.ofAdd x) n

theorem existsUnique_coeff {A : Type} [CommGroup A] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (u : D.La → A)
    (hu : ∀ x y, u (x + y) = u x * u y) {N : ℕ} (hN : 0 < N) (hk : ∀ x, u x = 1 ↔ ∃ y, x = N • y) (x : D.La) :
    ∃! c : Fin (2 * g) → ZMod N, ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u x := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨v, rfl⟩ := bas.surjective x
  have key : ∀ c : Fin (2 * g) → ZMod N,
      ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u (bas v) ↔ c = fun i => (v i : ZMod N) := fun c => by
    have e₁ : ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u (bas fun i => ((c i).val : ℤ)) := by
      rw [map_bas bas u hu]; simp only [zpow_natCast]
    have e₂ := hu (bas (v - fun i => ((c i).val : ℤ))) (bas fun i => ((c i).val : ℤ))
    rw [← map_add, sub_add_cancel] at e₂
    rw [e₁, e₂, right_eq_mul, hk]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨w, rfl⟩ := bas.surjective y
      rw [← map_nsmul] at hy
      funext i
      have := congrArg (fun z : ℤ => (z : ZMod N)) (congrFun (bas.injective hy) i)
      simp at this
      exact (sub_eq_zero.1 this).symm
    · intro hc
      have : ∀ i, ∃ w : ℤ, v i - ((c i).val : ℤ) = N * w := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (by simp [hc])
      choose w hw using this
      refine ⟨bas w, ?_⟩
      rw [← map_nsmul]
      congr 1
      funext i
      simpa using hw i
  simp only [key]
  exact existsUnique_eq

theorem coe_rt (n N : ℕ) : ((RZ.rt H n N : RZ H n N) : ℂ) = H.rt0 := by
  show ((2 : RZ H n N) : ℂ) * ((1 + H.rt0) / 2) - 1 = H.rt0
  have : ((2 : RZ H n N) : ℂ) = 2 := map_ofNat (RZ H n N).subtype 2
  rw [this]; ring

theorem rt_sq (n N : ℕ) : RZ.rt H n N ^ 2 = -(H.d : RZ H n N) := by
  apply Subtype.ext
  push_cast
  rw [coe_rt, H.sqrt_neg_disc_sq]

theorem map_unitS {o K : Type} [CommRing o] [CommRing K] {S : Scheme.{0}} (s : S ⟶ Sp o) (x : Sp K ⟶ S) (β : o →+* K)
    (h : x ≫ s = spMap β) (u : oˣ) (v : Kˣ) (hv : (v : K) = β u) :
    Units.map x.appTop.hom.toMonoidHom (unitS s u) = unitOn v := by
  apply Units.ext
  show x.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u)) =
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom v
  have e := congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))
  have e' := congrArg (fun q : Sp K ⟶ Sp o => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u)) h
  rw [hv]
  exact e'.trans e.symm

set_option maxHeartbeats 800000 in

theorem exists_under (hL : Out.Laws) {n N : ℕ} (hN : 0 < N) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La)
    (hbas : IsSympBasis D bas) (b : TBase (RZ H n N) N) (hb : (b.ζ : RZ H n N) = RZ.ze H n N) {S : Scheme.{0}}
    {s : S ⟶ Sp (RZ H n N)} [Flat s] {t : SAB H S} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)} (h : FullObj D s t lv) :
    ∃ T : TObj g N J b s, Under t lv a bas T ∧ IsPEL D a bas (RZ.rt H n N) T t := by
  have hab : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, h.proper, t.semi.geomConnected⟩
  have hg : Module.finrank ℚ E / 2 * (D.p + D.q) = g := by
    have := bas.finrank_eq
    rw [datum_finrank_int, Module.finrank_fin_fun] at this
    omega
  have hdim : SmoothOfRelativeDimension g t.G.hom := by
    have := t.semi.smooth
    have := t.semi.geomConnected
    refine smoothOfRelativeDimension_of_generization _ g fun y => ?_
    obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization (t.G.hom ≫ s) y
    refine ⟨K, inferInstance, z, hz, fun m hm => ?_⟩
    refine (ObjDim.dim_eq_of_detCond D t.act (z ≫ t.G.hom) ?_
      (h.geom K _ β ((Category.assoc _ _ _).trans hβ)).1 hm).trans hg
    rw [← map_pow, rt_sq, map_neg, map_natCast]
  let pt : Fin (2 * g) → (Out.baseOver S ⟶ t.G) := fun i => toUnit _ ≫ lv (bas (Pi.single i 1))
  have hpt : ∀ i, pt i ^ N = 1 := fun i => by
    rw [← MonObj.comp_pow, ← map_nsmul' lv h.add, h.ker, MonObj.comp_one]
  have hptx : ∀ {X : Scheme.{0}} (x : X ⟶ S) (i), toB x ≫ pt i = toUnit _ ≫ lv (bas (Pi.single i 1)) := fun x i => by
    rw [← Category.assoc, toUnit_unique (toB x ≫ toUnit _) (toUnit _)]
  have hu : IsUnit (N : Γ(S, ⊤)) := by
    have := b.unit.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (RZ H n N))).inv.hom)
    rwa [map_natCast] at this
  have hζ : b.ζ ^ N = 1 := by
    apply Units.ext
    apply Subtype.val_injective
    exact (b.prim ℂ (RZ H n N).subtype).pow_eq_one
  let P : Out.PolAV S :=
    { A := t.G, isAb := hab, g := g, smoothDim := hdim, L := t.PP.L, isLB := t.PP.isLB, rigid := ObjDim.rigidified,
      sym := ObjDim.sym, ample := h.ample, ktriv := h.ktriv }
  have : IsMonHom (Iso.refl t.G).hom := inferInstanceAs (IsMonHom (𝟙 t.G))
  have hid : LBIso t.PP.L (t.PP.L.pull (Iso.refl t.G).hom.left) :=
    LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ (𝟙 _) (Category.id_comp _).symm)
      (PolBaseChange.lbIso_refl t.PP.isLB)
  have hpl : ∀ i, (lv (bas (Pi.single i 1))).left ≫ (Iso.refl t.G).hom.left = (pt i).left := fun i => by
    have e : (toUnit (Out.baseOver S)).left = 𝟙 S := ObjPull.toUnit_left' _
    rw [Iso.refl_hom, Over.id_left, Category.comp_id, Over.comp_left, e]
    exact (Category.id_comp (X := S) _).symm
  refine ⟨{ A := t.G, ab := hab, dim := hdim, L := t.PP.L, isLB := t.PP.isLB, rigid := ObjDim.rigidified,
            sym := ObjDim.sym, ample := h.ample, ktriv := h.ktriv, pt := pt, torsion := hpt,
            bij := torsion_basis_of_generization t.G N _ pt hab hN hu hpt fun p => ?_,
            pairing := fun i j => weilIs_of_generization hL P N _ _ _ hN hu (hpt i) (hpt j) ?_ fun p => ?_,
            act := fun j => t.act.act (a j), hom := fun j => t.act.hom _ },
    ⟨Iso.refl _, this, hid, fun j => by simp, hpl⟩,
    ⟨Iso.refl _, this, hid, fun j => by simp, fun K _ _ _ x β hx => ?_⟩⟩
  · obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization s p
    obtain ⟨-, I, -, hI⟩ := h.geom K z β hβ
    refine ⟨K, inferInstance, inferInstance, z, hz, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := (I.onto N hN y).1 hy
    simp only [hptx, hI, Out.linComb, List.prod_ofFn]
    exact existsUnique_coeff bas (I.ev N) (I.add N) hN (I.ker N hN) x
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, unitS, unitOn, ← map_pow, ← map_pow, hζ, map_one,
      map_one, one_zpow]
  · obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization s p
    obtain ⟨-, I, hIζ, hI⟩ := h.geom K z β hβ
    refine ⟨K, inferInstance, z, hz, ?_⟩
    have hc : Units.map z.appTop.hom.toMonoidHom (unitS s b.ζ ^ Out.stdSymp g i j) =
        unitOn (I.ζ N ^ Out.stdSymp g i j) := by
      rw [map_zpow, map_unitS s z β hβ b.ζ (I.ζ N) (by rw [hIζ, hb]), unitOn, unitOn, map_zpow]
    have e : Out.WeilIs t.G t.PP.L N (toB z ≫ pt i) (toB z ≫ pt j)
        (Units.map z.appTop.hom.toMonoidHom (unitS s b.ζ ^ Out.stdSymp g i j)) := by
      rw [hc, hptx z i, hptx z j, hI, hI, ← hbas i j]
      exact I.isom N hN _ _
    exact e
  · obtain ⟨hd, I, hIζ, hI⟩ := h.geom K x β hx
    refine ⟨hd, I, by rw [hIζ, hb], fun i => ?_⟩
    have e : I.ev N (bas (Pi.single i 1)) ≫ 𝟙 t.G = toB x ≫ pt i := by rw [hptx, hI, Category.comp_id]
    exact e

theorem exists_level {n N : ℕ} {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La}
    {b : TBase (RZ H n N) N} (hb : (b.ζ : RZ H n N) = RZ.ze H n N) {S : Scheme.{0}}
    {s : S ⟶ Sp (RZ H n N)} {t : SAB H S} {T : TObj g N J b s} (h : IsPEL D a bas (RZ.rt H n N) T t) :
    ∃ lv : D.La → (𝟙_ (Over S) ⟶ t.G), Under t lv a bas T ∧ FullObj D s t lv := by
  obtain ⟨φ, hφ, hφL, hφa, hgeom⟩ := h
  let j : 𝟙_ (Over S) ⟶ Out.baseOver S := Over.homMk (𝟙 S) (Category.id_comp _)
  let q : Fin (2 * g) → (𝟙_ (Over S) ⟶ t.G) := fun i => j ≫ T.pt i ≫ φ.inv
  have hq : ∀ i, q i ^ N = 1 := fun i => by
    rw [← MonObj.comp_pow, ← MonObj.pow_comp, T.torsion, MonObj.one_comp, MonObj.comp_one]
  let lv : D.La → (𝟙_ (Over S) ⟶ t.G) := fun x => ∏ i, q i ^ bas.symm x i
  have hadd : ∀ x y, lv (x + y) = lv x * lv y := fun x y => by
    simp only [lv, map_add, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hlv : ∀ i, lv (bas (Pi.single i 1)) = q i := fun i => by
    simp only [lv, LinearEquiv.symm_apply_apply]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp
  obtain ⟨hab, hA, hK⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally S S T.A t.G _ _ T.L t.PP.L
    T.isLB t.PP.isLB T.ab (isGrpPullback_of_iso φ) hφL
  refine ⟨lv, ⟨φ, hφ, hφL, hφa, fun i => ?_⟩, hab.proper, hA T.ample, hK T.ktriv, hadd, fun x => ?_,
    fun K _ _ _ x β hx => ?_⟩
  · rw [hlv]
    show (𝟙 S ≫ (T.pt i).left ≫ φ.inv.left) ≫ _ = _
    rw [Category.assoc, Category.assoc, inv_hom_left]
    exact (Category.id_comp _).trans (Category.comp_id _)
  · rw [map_nsmul' lv hadd, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hq, one_zpow]
  · obtain ⟨hd, I, hIζ, hI⟩ := hgeom K x β hx
    refine ⟨hd, I, by rw [hIζ, hb], eq_of_basis bas (fun y => toUnit _ ≫ lv y) (I.ev N)
      (fun y y' => by rw [hadd, MonObj.comp_mul]) (I.add N) fun i => ?_⟩
    have e : toUnit (Over.mk x) ≫ j = toB x := Over.OverMorphism.ext
      ((Category.comp_id _).trans (ObjPull.toUnit_left' _))
    rw [hlv, ← Category.assoc, e, ← Category.assoc, Iso.comp_inv_eq]
    exact (hI i).symm

theorem arBase_RZ (H : Host E) {n N e : ℕ} (hn : 0 < n) (hN : 0 < N) (h : N ∣ n ^ e) : ArBase (RZ H n N).subtype := by
  obtain ⟨l⟩ : Nonempty (Level H) := HostModel.instNonemptyLevel H
  exact ⟨BaseRing.isDedekindDomain_RZ { l with A := N, A_pos := hN } hn h, BaseRing.finiteType_RZ H n N,
    Subtype.val_injective⟩

end GlobalTheory.TripleTheta

namespace GlobalTheory

open TripleTheta CharZeroPts in

theorem exists_famCore_of_thetaFam : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N' : ℕ) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N' = n ^ j) → ∃ lev : D.La → (𝟙_ (Over F.MM) ⟶ τ.G), FamCore D F.s τ lev := by
  intro hL hL2 E _ _ _ H D n N' g J _ a bas b F τ hbas ha ⟨w, w', hw, hw'⟩ hb hP hsm hpq hn _ ⟨j, _, hj⟩
  have hN : 0 < N' ^ 2 := by rw [hj]; exact pow_pos (pow_pos hn.pos _) _
  have hbase : ArBase (RZ H n (N' ^ 2)).subtype := arBase_RZ H (e := j * 2) hn.pos hN (by rw [hj, pow_mul])
  obtain ⟨lev, hU, hF⟩ := exists_level hb hP
  refine ⟨lev, F.reduced, F.flat, F.qproj, SmoothOfRelativeDimension.smooth D.dim _, hF,
    fun S s t lv hS _ hs ho => ?_, fun k _ x t lv ν ν' hx hν hν' => ?_⟩
  · obtain ⟨T, hT, hTP⟩ := exists_under hL hN a bas hbas b hb ho
    obtain ⟨f, ⟨hf, hm⟩, huniq⟩ := F.rep S s T hS fun p => by
      obtain ⟨K, _, _, _, z, β, -, hz⟩ := exists_generization s p
      exact (hz (default : PrimeSpectrum K)).mem_closed isClosed_closure (subset_closure ⟨K, inferInstance, z, ⟨_, rfl⟩,
        PELFrom.fromC_of_isPEL hL hL2 E H D g J a w w' bas hpq hbas hw hw' ha N' _ b _ _ (coe_rt n _) hbase S s T t hTP K z⟩)
    exact ⟨f, ⟨hf, sabMap_of_tmap hU hT hF.add ho.add ha hS ho.proper hm⟩,
      fun f' ⟨hf', ν, hν⟩ => huniq f' ⟨hf', tmap_of_sabMap hU hT ν hν⟩⟩
  · obtain ⟨T, hT⟩ := tObj_pull _ g _ J b _ _ F.s (x ≫ F.s) x F.univ rfl
    exact F.unram k x T hx hT (tmap_of_sabMap hU (under_of_tmap hU hT ν hν) ν' hν')

end GlobalTheory
