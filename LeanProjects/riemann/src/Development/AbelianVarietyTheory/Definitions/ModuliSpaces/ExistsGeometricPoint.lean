import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArcBaseExamples
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseTorsionAndEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models.FamTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem coe_rt (S A : ℕ) : (RZ.rt H S A : ℂ) = H.rt0 := by
  show 2 * ((1 + H.rt0) / 2) - 1 = H.rt0
  ring

theorem coe_ze (S A : ℕ) : (RZ.ze H S A : ℂ) = zeta A := rfl

theorem rt_sq (S A : ℕ) : RZ.rt H S A ^ 2 = -(H.d : RZ H S A) :=
  Subtype.ext (by simpa [coe_rt] using H.sqrt_neg_disc_sq)

theorem fullObj_of_obj {D : Datum H} {l : Level H} {n : ℕ} (β : RZ H n l.A →+* KA l)
    (hβ : IsInc (RZ H n l.A).subtype (KA l).val.toRingHom β) {S : Scheme.{0}} {s : S ⟶ Sp (KA l)}
    (o : Obj D l (baseKA l) s) : FullObj D (s ≫ spMap β) o.t o.etaA := by
  refine ⟨o.proper, o.ample, o.ktriv, o.etaA_add, o.etaA_ker, fun k _ _ _ x gam hx => ?_⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ s)
  have e : φ.hom.comp β = gam := by
    have h : spMap (φ.hom.comp β) = spMap gam := by
      rw [← hx, ← Category.assoc, ← hφ]
      exact Spec.map_comp (CommRingCat.ofHom β) φ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  have e₁ : β (RZ.rt H n l.A) = (baseKA l).ρ := Subtype.ext ((hβ _).trans (coe_rt _ _))
  have e₂ : β (RZ.ze H n l.A) = (baseKA l).ζ := Subtype.ext (hβ _)
  obtain ⟨h₁, I, h₂, h₃, -⟩ := o.geom k x φ.hom hφ.symm
  subst e
  exact ⟨by rw [RingHom.comp_apply, e₁]; exact h₁, I, by rw [RingHom.comp_apply, e₂]; exact h₂, h₃⟩

theorem exists_roots {n N : ℕ} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] (β : RZ H n N →+* k) :
    ∃ ζ : ℕ → kˣ, (∀ m, 0 < m → IsPrimitiveRoot (ζ m) m) ∧ (∀ a b, 0 < a → 0 < b → ζ (a * b) ^ b = ζ a) ∧
      (ζ N : k) = β (RZ.ze H n N) := by
  let B : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  let R : Subring ℂ := RZ H n N ⊓ B
  have hz : ∀ m, zeta m ∈ B := fun m => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : zeta 0 = 1 := by simp [zeta]
      rw [this]; exact one_mem _
    · exact (Complex.isPrimitiveRoot_exp m hm.ne').isIntegral hm
  letI : Algebra R B := (Subring.inclusion inf_le_right).toAlgebra
  haveI : Algebra.IsIntegral ℤ B := inferInstanceAs (Algebra.IsIntegral ℤ (integralClosure ℤ ℂ))
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.tower_top (R := ℤ)
  haveI : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective _ _).2 (Subring.inclusion_injective _)
  obtain ⟨ψ, hψ⟩ := exists_ringHom_extend_of_isIntegral_of_injective (B := B)
    (β.comp (Subring.inclusion (inf_le_left : R ≤ RZ H n N)))
  have hp : ∀ m, 0 < m → IsPrimitiveRoot (ψ ⟨zeta m, hz m⟩) m := fun m hm => by
    have h₀ : IsPrimitiveRoot (⟨zeta m, hz m⟩ : B) m :=
      IsPrimitiveRoot.of_map_of_injective (f := B.subtype) (Complex.isPrimitiveRoot_exp m hm.ne') Subtype.val_injective
    rw [← Polynomial.isRoot_cyclotomic_iff_charZero hm, ← Polynomial.map_cyclotomic m ψ]
    exact (h₀.isRoot_cyclotomic hm).map
  have hne : ∀ m, ψ ⟨zeta m, hz m⟩ ≠ 0 := fun m => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : (⟨zeta 0, hz 0⟩ : B) = 1 := Subtype.ext (by simp [zeta])
      rw [this, map_one]; exact one_ne_zero
    · exact (hp m hm).ne_zero hm.ne'
  refine ⟨fun m => Units.mk0 _ (hne m), fun m hm => IsPrimitiveRoot.coe_units_iff.1 (hp m hm), fun a b ha hb => ?_, ?_⟩
  · ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow]
    congr 1
    ext
    have : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
    have : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
    simp only [SubmonoidClass.mk_pow, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  · exact DFunLike.congr_fun hψ ⟨zeta N, (RZ.ze H n N).2, hz N⟩

theorem weilIs_zero {S : Scheme.{0}} (T : Over S) (m : ℕ) :
    Out.WeilIs (𝟙_ (Over S)) (UU.trivRig (𝟙_ (Over S))).L m (1 : T ⟶ _) 1 1 :=
  (UU.cubWeil_iff_weilIs (c := UU.trivCub (𝟙_ (Over S))) globalFns_holds (UU.isAbelianScheme_unit S)
      (one_pow _) (one_pow _) 1).1 (UU.cubWeil_triv (one_pow _) (one_pow _))

theorem fullObj_zero {n N : ℕ} {S : Scheme.{0}} (s : S ⟶ Sp (RZ H n N)) :
    FullObj (Test.zeroDatum H) s (Inhab.zeroTriple H S) (fun _ => 1) := by
  refine ⟨Inhab.isProper_zeroTriple S, (Out.Inh.zeroPolAV S).ample, (Out.Inh.zeroPolAV S).ktriv,
    fun _ _ => (_root_.mul_one _).symm, fun _ => rfl, fun k _ _ _ x β _ => ⟨fun τ => ?_, ?_⟩⟩
  · have h : LieMult (Inhab.zeroTriple H S).act x τ 0 :=
      ⟨Fin.elim0, fun i => i.elim0, fun w _ => ⟨Fin.elim0, ⟨Fin.elim0, fun i => i.elim0, toUnit_unique _ _⟩,
        fun _ _ => Subsingleton.elim _ _⟩⟩
    exact ⟨fun _ => h, fun _ => h⟩
  · obtain ⟨ζ, h₁, h₂, h₃⟩ := exists_roots β
    refine ⟨⟨ζ, h₁, h₂, fun _ _ => 1, fun _ _ _ => toUnit_unique _ _, fun _ _ _ => toUnit_unique _ _,
      fun _ _ a => ⟨fun _ => ⟨a, rfl⟩, fun _ => rfl⟩, fun _ _ _ => ⟨fun _ => ⟨PUnit.unit, toUnit_unique _ _⟩,
        fun _ => toUnit_unique _ _⟩, fun _ _ _ _ _ => toUnit_unique _ _, fun m _ a b => ?_⟩, h₃,
      fun _ => toUnit_unique _ _⟩
    have e : unitOn (ζ m ^ (Test.zeroDatum H).EF a b) = 1 := by
      show unitOn (ζ m ^ (0 : ℤ)) = 1
      rw [zpow_zero]; exact map_one _
    exact e ▸ weilIs_zero (Over.mk x) m

theorem not_fullObj_zero {D : Datum H} [Nontrivial D.La] {n N : ℕ} {S : Scheme.{0}} (s : S ⟶ Sp (RZ H n N)) (lev)
    (x : Sp ℂ ⟶ S) : ¬ FullObj D s (Inhab.zeroTriple H S) lev := by
  intro h
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨-, I, -⟩ := h.geom ℂ x φ.hom hφ.symm
  obtain ⟨a, ha⟩ := exists_ne (0 : D.La)
  have h₁ : D.EF a ≠ 0 := fun e => ha (D.unimod.1 (e.trans (map_zero _).symm))
  obtain ⟨b, hb⟩ : ∃ b, D.EF a b ≠ 0 := by
    by_contra hc
    exact h₁ (LinearMap.ext fun b => by simpa using not_exists.1 hc b)
  obtain ⟨c, hc⟩ := (I.ker ((D.EF a b).natAbs + 1) (Nat.succ_pos _) a).1 (toUnit_unique _ _)
  have hd : (((D.EF a b).natAbs + 1 : ℕ) : ℤ) ∣ D.EF a b := ⟨D.EF c b, by
    conv_lhs => rw [hc]
    rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]⟩
  have := Nat.le_of_dvd (Int.natAbs_pos.2 hb) (Int.natCast_dvd.1 hd)
  omega

variable {D : Datum H} {Xo : ∀ l : Level H, Moduli D l} {n N : ℕ}

theorem siegClause_of_top (T : Top Xo n N) : SiegClause D T.sM T.tM T.lev := T.sieg

section Frames
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.LN

variable {Z : Scheme.{0}} (G : Over Z) (N : ℕ)

def oneSec {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    LB.Sec (LB.LinComb (Inh.trivLB X) φ ε) :=
  ⟨fun _ => 1, fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm⟩

theorem gs_one {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : gs f y U 1 = 1 := by
  rw [gs_eq _ _ _ h, map_one, map_one]

theorem mem_wchart_triv {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j) (y : Y) :
    y ∈ LB.wchart (Inh.trivLB X) φ j := Set.mem_iInter.2 fun _ => trivial

theorem lin_one {T T' : Over Z} (h : T' ⟶ T) :
    Lin G (Inh.trivLB G.left) N h (fun _ : Fin 1 => oneSec _ _) (fun _ => 1) (oneSec _ _) := by
  intro z J hJ
  rw [Fin.sum_univ_one]
  exact (gs_one _ _ _ (hJ.mem _ _)).trans ((congrArg₂ (· * ·) (gs_one _ _ ⊤ trivial)
    (gs_one _ _ _ (mem_wchart_triv _ _ _))).trans (_root_.one_mul _)).symm

theorem basisAlong_one {T T' : Over Z} (h : T' ⟶ T) (hb : Function.Bijective (fst T' G).left.appTop.hom) :
    BasisAlong G (Inh.trivLB G.left) N h (fun _ : Fin 1 => oneSec _ _) := by
  intro s
  have le : (⊤ : (T' ⊗ G).left.Opens) ≤
      LB.wchart (Inh.trivLB G.left) (fun _ : Fin 1 => (snd T' G).left) (fun _ => PUnit.unit) := fun y _ =>
    Set.mem_iInter.2 fun _ => trivial
  have gv : ∀ (c : Γ(T'.left, ⊤)) (y : (T' ⊗ G).left),
      gs (fst T' G).left y ⊤ c = gs (𝟙 _) y ⊤ ((fst T' G).left.appTop.hom c) := fun c y =>
    ((gs_pull (𝟙 _) (fst T' G).left y ⊤ trivial c).trans (by rw [Category.id_comp])).symm
  have o : ∀ (y : (T' ⊗ G).left) J, sval (L := Inh.trivLB G.left) (φ := fun _ : Fin 1 => (snd T G).left)
      (ε := fun _ => (N : ℤ)) (oneSec _ _) (h ▷ G).left y J = 1 := fun y J =>
    gs_one _ _ _ (Set.mem_iInter.2 fun _ => trivial)
  obtain ⟨c, hc⟩ := hb.2 (((T' ⊗ G).left.presheaf.map (homOfLE le).op).hom (s.f (fun _ => PUnit.unit)))
  have H : Lin G (Inh.trivLB G.left) N h (fun _ : Fin 1 => oneSec _ _) (fun _ => c) s := by
    intro y J hJ
    rw [Fin.sum_univ_one, o, _root_.mul_one, gv, hc]
    exact (gs_res (𝟙 _) y le trivial _).symm
  refine ⟨fun _ => c, H, fun c' H' => funext fun k => ?_⟩
  obtain rfl : k = 0 := Subsingleton.elim _ _
  refine hb.1 (fn_ext fun y _ => ?_)
  have e1 := (H' y (fun _ => PUnit.unit) (fun _ => trivial)).symm.trans (H y (fun _ => PUnit.unit) (fun _ => trivial))
  rw [Fin.sum_univ_one, Fin.sum_univ_one] at e1
  have e2 := ((congrArg (_ * ·) (o y _)).symm.trans e1).trans (congrArg (_ * ·) (o y _))
  rw [_root_.mul_one, _root_.mul_one, gv, gv] at e2
  exact e2

theorem ampFrames_triv [IsAffine Z] [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom] :
    Nonempty (AmpFrames G (Inh.trivLB G.left) N) := by
  refine ⟨⟨Inh.trivLB Z, Inh.trivLB_isLB Z, fun z => ?_, 1, fun _ => oneSec _ _, fun _ _ => oneSec _ _, 0, 0,
    fun i j => ⟨1, 1, ⟨oneSec _ _, lin_one G 1 _, lin_one G 1 _⟩, fun k => ⟨oneSec _ _, lin_one G N _, ?_⟩, ?_⟩,
    fun i V _ _ _ hV χ _ => ?_⟩⟩
  · have hD : nonzeroLocus (oneSec (fun _ : Fin 1 => 𝟙 Z) (fun _ => ((1 : ℕ) : ℤ))) = ⊤ := by
      apply top_unique
      intro x _
      simp only [nonzeroLocus, oneSec, Scheme.basicOpen_one]
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => PUnit.unit, Set.mem_iInter.2 fun _ => trivial⟩
    exact ⟨1, oneSec _ _, le_rfl, hD ▸ trivial, hD ▸ isAffineOpen_top Z⟩
  · obtain rfl : k = 0 := Subsingleton.elim _ _
    have e : ∀ {R : Type} [CommRing R], (fun k' : Fin 1 => (1 : GL (Fin 1) R).val 0 k') = fun _ => 1 := by
      intro R _
      funext k'
      obtain rfl : k' = 0 := Subsingleton.elim _ _
      simp
    rw [e]
    exact lin_one G N _
  · rw [zpow_zero, zpow_zero, _root_.one_mul]
    exact map_one _
  · have := hV.1
    exact ⟨basisAlong_one G 1 _ (GlobalTheory.LN.Model.bijective_fst G _), basisAlong_one G N _ (GlobalTheory.LN.Model.bijective_fst G _)⟩

end Frames

theorem zOn_self {O : Type} [CommRing O] {Z : Scheme.{0}} (s : Z ⟶ Sp O) (t : SAB H Z) (m : ℕ)
    (hn : Geo.Tor.IsNormalScheme Z) (hp : IsProjOver s) (hf : Flat s) (hq : IsQProjOver (t.G.hom ≫ s)) (hg : Good t)
    (W : Z.Opens) (hW : Dense (W : Set Z)) (ha : Nonempty (GlobalTheory.LN.AmpFrames t.G t.PP.L (m ^ 2))) :
    ∃ X : ZOn s t m, X.Z = Z ∧ X.W = W := by
  obtain ⟨tW, ⟨m₁⟩⟩ := Inhab.exists_pull W.ι t
  obtain ⟨a⟩ := ha
  exact ⟨⟨Z, s, hn, hp, hf, t, hq, hg, W, hW, W.ι, inferInstance,
    ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩, rfl, tW, m₁, m₁, a⟩, rfl, rfl⟩

theorem zOn_zero (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O] (m : ℕ) (W : (Sp O).Opens)
    (hW : (W : Set (Sp O)).Nonempty) :
    ∃ X : ZOn (𝟙 (Sp O)) (Inhab.zeroTriple H (Sp O)) m, X.Z = Sp O ∧ X.W = W := by
  have hq : IsQProjOver ((Inhab.zeroTriple H (Sp O)).G.hom ≫ 𝟙 _) := by
    obtain ⟨M, i, h₁, h₂⟩ := Inhab.isProjOver_id O
    have := h₁
    exact ⟨M, i, (inferInstance : IsImmersion i), (inferInstance : QuasiCompact i), h₂.trans (Category.id_comp _).symm⟩
  have : IsProper (𝟙_ (Over (Sp O))).hom := inferInstanceAs (IsProper (𝟙 _))
  have : Flat (𝟙_ (Over (Sp O))).hom := inferInstanceAs (Flat (𝟙 _))
  have : Smooth (𝟙_ (Over (Sp O))).hom := inferInstanceAs (Smooth (𝟙 _))
  have : GeometricallyConnected (𝟙_ (Over (Sp O))).hom := (Out.Inh.zeroPolAV _).isAb.geomConnected
  have : GeometricallyIntegral (𝟙_ (Over (Sp O))).hom :=
    geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _
  exact zOn_self _ _ m (ZJ.isNormalScheme_sp O) (Inhab.isProjOver_id O) inferInstance hq (Inhab.good_zeroTriple _) W
    (W.isOpen.dense hW) (ampFrames_triv (𝟙_ (Over (Sp O))) _)

theorem range_j_subset {O : Type} [CommRing O] {MM : Scheme.{0}} {sM : MM ⟶ Sp O} {tM : SAB H MM} {m : ℕ}
    (X : ZOn sM tM m) (h : IsProper tM.G.hom) : Set.range X.j ⊆ abLocus X.t.G := by
  rintro _ ⟨x, rfl⟩
  have : IsProper X.tW.G.hom := MorphismProperty.of_isPullback (P := @IsProper) X.m₁.cart.1 h
  refine (abLocus_pullback abLocusOne X.t.semi X.m₂.cart.1 x).2 ?_
  rw [Inhab.abLocus_eq_univ _ this]; trivial

theorem exists_map_of_famCore {l : Level H} (Xo : Moduli D l) {MM : Scheme.{0}} {sM : MM ⟶ Sp (RZ H n l.A)}
    {tM : SAB H MM} {lev} (F : FamCore D sM tM lev) (β : RZ H n l.A →+* KA l)
    (hβ : IsInc (RZ H n l.A).subtype (KA l).val.toRingHom β) (hf : Flat (spMap β)) (hr : IsReduced Xo.X) :
    ∃! f : Xo.X ⟶ MM, f ≫ sM = Xo.s ≫ spMap β ∧
      ∃ ν : SABMap Xo.univ.t tM f, ∀ a, (Xo.univ.etaA a).left ≫ ν.φ = f ≫ (lev a).left := by
  have := Xo.smooth.smooth
  exact F.rep _ _ _ _ hr (LocallyOfFiniteType.isLocallyNoetherian Xo.s) inferInstance (fullObj_of_obj β hβ Xo.univ)

theorem nonempty_of_famCore_zero [IsNoetherianRing (RZ H n N)] {MM : Scheme.{0}} {sM : MM ⟶ Sp (RZ H n N)}
    {tM : SAB H MM} {lev} (F : FamCore (Test.zeroDatum H) sM tM lev) : ∃ f : Sp (RZ H n N) ⟶ MM, f ≫ sM = 𝟙 _ :=
  let ⟨f, hf, _⟩ := F.rep _ (𝟙 _) _ _ inferInstance inferInstance inferInstance (fullObj_zero _)
  ⟨f, hf.1⟩

section RankZero

variable {S : Scheme.{0}} {s : S ⟶ Sp (RZ H n N)} {t : SAB H S} {lv}

theorem torsion_eq_one (h : FullObj (Test.zeroDatum H) s t lv) {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    (x : Sp k ⟶ S) {m : ℕ} (hm : 0 < m) (g : Over.mk x ⟶ t.G) (hg : g ^ m = 1) : g = 1 := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨-, I, -⟩ := h.geom k x φ.hom hφ.symm
  obtain ⟨a, rfl⟩ := (I.onto m hm g).1 hg
  exact (I.ker m hm a).2 ⟨a, rfl⟩

theorem point_eq_one (h₁ : Out.Laws) (h₂ : Out.Laws2) (h : FullObj (Test.zeroDatum H) s t lv) {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] (z : Sp k ⟶ t.G.left) : z = z ≫ t.G.hom ≫ eSec t.G := by
  obtain ⟨t', ⟨m⟩⟩ := Inhab.exists_pull (z ≫ t.G.hom) t
  obtain ⟨i, -⟩ := ObjMaps.exists_sab_id t
  obtain ⟨hp, hA, hK⟩ := GenericPol.proper_ample_kTriv i h.proper h.ample h.ktriv m (by simp)
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  have : ConnectedSpace ↥t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t'.G.hom (Classical.arbitrary _)
  have inj : ∀ {x y : 𝟙_ _ ⟶ t'.G}, pushHom m.cart _ x = pushHom m.cart _ y → x = y := fun {x y} e =>
    Over.OverMorphism.ext (m.cart.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))
  have key : (𝟙 t'.G : t'.G ⟶ t'.G) = 1 :=
    (PrimePowerTorsion.dense_torsion_and_eq_one h₁ h₂ k (GenericPol.toPolAV t' g hg hp hA hK) 2 Nat.prime_two
      (by simp)).2 (𝟙 _) fun j x hx => (Category.comp_id x).trans (inj
        ((torsion_eq_one h _ (pow_pos two_pos j) _ ((map_pow _ _ _).symm.trans
          ((congrArg _ hx).trans (map_one _)))).trans (map_one _).symm))
  let y : 𝟙_ _ ⟶ t'.G := Over.homMk (m.cart.1.lift z (𝟙 _) (Category.id_comp _).symm) (m.cart.1.lift_snd _ _ _)
  have hy : y = 1 := by rw [← Category.comp_id y, key, MonObj.comp_one]
  have e : z = (pushHom m.cart _ y).left := (m.cart.1.lift_fst _ _ _).symm
  rw [hy, map_one, UU.one_left] at e
  exact e.trans ((congrArg (· ≫ eSec t.G) (Category.id_comp _)).trans (Category.assoc _ _ _))

theorem exists_geometric_point_over {X : Scheme.{0}} (K : Type) [Field K] (u : Sp K ⟶ X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (z : Sp k ⟶ X) (q : Sp k) (q' : Sp K), z q = u q' :=
  ⟨AlgebraicClosure K, inferInstance, inferInstance, spMap (algebraMap K _) ≫ u, IsLocalRing.closedPoint _, _,
    Scheme.Hom.comp_apply _ _ _⟩

theorem exists_geom {X : Scheme.{0}} (y : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (z : Sp k ⟶ X) (q : Sp k), z q = y := by
  obtain ⟨k, _, _, z, q, q', h⟩ := exists_geometric_point_over (X.residueField y) (X.fromSpecResidueField y)
  exact ⟨k, inferInstance, inferInstance, z, q, h.trans (Scheme.fromSpecResidueField_apply y q')⟩

theorem exists_geom_specializes {X : Scheme.{0}} {R : Type} [CommRing R] [IsDomain R] [CharZero R] (f : X ⟶ Sp R)
    [Flat f] (y : X) : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharZero k) (z : Sp k ⟶ X) (q : Sp k),
      z q ⤳ y := by
  obtain ⟨y', hy', hb⟩ := Flat.generalizingMap f
    (show (⊥ : PrimeSpectrum R) ⤳ f y from (PrimeSpectrum.le_iff_specializes _ _).1 bot_le)
  obtain ⟨k, _, _, z, q, hz⟩ := exists_geom y'
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (z ≫ f)
  have hinj : Function.Injective φ.hom := by
    have e : Spec.map φ q = (⊥ : PrimeSpectrum R) := by
      rw [hφ, Scheme.Hom.comp_apply, hz]; exact hb
    have e' : Ideal.comap φ.hom q.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal e
    rw [RingHom.injective_iff_ker_eq_bot, ← le_bot_iff, ← e']
    exact Ideal.comap_mono bot_le
  exact ⟨k, inferInstance, inferInstance, charZero_of_injective_ringHom (R := R) hinj, z, q, hz ▸ hy'⟩

theorem hom_comp_eSec (h₁ : Out.Laws) (h₂ : Out.Laws2) (h : FullObj (Test.zeroDatum H) s t lv) [IsReduced S] [Flat s] :
    t.G.hom ≫ eSec t.G = 𝟙 _ := by
  have := t.semi.smooth
  have := t.semi.separated
  have : IsReduced t.G.left := isReduced_of_smooth_of_isReduced t.G.hom
  have he : eSec t.G ≫ t.G.hom = 𝟙 S := Over.w η[t.G]
  suffices IsDominant (equalizer.ι (t.G.hom ≫ eSec t.G) (𝟙 _)) from
    ext_of_isDominant_of_isSeparated t.G.hom (by rw [Category.assoc, he]; simp) _ (equalizer.condition _ _)
  refine ⟨fun y => ?_⟩
  obtain ⟨k, _, _, _, z, q, hz⟩ := exists_geom_specializes (t.G.hom ≫ s) y
  have e := (point_eq_one h₁ h₂ h z).symm.trans (Category.comp_id z).symm
  refine closure_mono (Set.singleton_subset_iff.2 ?_) hz.mem_closure
  refine ⟨equalizer.lift z e q, ?_⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]

theorem lbIso_triv {X Y : Scheme.{0}} (L : LB X) (φ : X ⟶ Y) (c : LB.Gen L) (hc : c.IsGen) :
    LBIso L ((Out.Inh.trivLB Y).pull φ) := by
  refine ⟨⟨fun p => (res inf_le_right (c.s p.2))⁻¹⟩, fun p q => unit_ext fun y hy => ?_⟩
  have e := congrArg (gm (𝟙 X) y _) (hc p.2 q.2)
  have m : (𝟙 X : X ⟶ X) y ∈ L.U p.2 ⊓ L.U q.2 := ⟨hy.1.2, hy.2.2⟩
  rw [map_mul, gm_res _ _ _ m, gm_res _ _ _ m] at e
  refine ((gm_res (𝟙 X) y _ hy _).trans ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res (𝟙 X) y _ hy.1 _)))).trans
    (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div _ _ (𝟙 X) y p q hy)
      ((gm_res (𝟙 X) y _ hy _).trans ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res (𝟙 X) y _ hy.2 _)))))).symm)
  rw [e, Out.Inh.linComb_triv_g, map_one, _root_.one_mul, mul_inv]

theorem famCore_zero (h₁ : Out.Laws) (h₂ : Out.Laws2) (H : Host E) (n N : ℕ) :
    FamCore (Test.zeroDatum H) (𝟙 (Sp (RZ H n N))) (Inhab.zeroTriple H _) (fun _ => 1) := by
  refine ⟨inferInstance, inferInstance, ?_, inferInstance, fullObj_zero _, fun S s t lv hr _ hf h => ?_,
    fun k _ x _ _ _ _ e _ _ => by simpa using e⟩
  · obtain ⟨M, i, a, b⟩ := Inhab.isProjOver_id (RZ H n N)
    exact ⟨M, i, inferInstance, inferInstance, b⟩
  refine ⟨s, ⟨Category.comp_id _, ?_⟩, fun f hf => (Category.comp_id f).symm.trans hf.1⟩
  have e := hom_comp_eSec h₁ h₂ h
  have he : eSec t.G ≫ t.G.hom = 𝟙 S := Over.w η[t.G]
  have : IsIso t.G.hom := ⟨eSec t.G, e, he⟩
  have gp : IsGrpPullback t.G (Inhab.zeroTriple H (Sp (RZ H n N))).G s (t.G.hom ≫ s) := by
    have : IsIso (Inhab.zeroTriple H (Sp (RZ H n N))).G.hom := inferInstanceAs (IsIso (𝟙 _))
    refine ⟨IsPullback.of_vert_isIso ⟨Category.comp_id _⟩, fun T x y x₀ y₀ _ _ => ?_⟩
    exact (Category.comp_id _).symm.trans ((Over.w (x₀ * y₀)).trans (Over.w_assoc (x * y) s).symm)
  obtain ⟨c, hc⟩ := gen_chartPull (chartPullSec t.PP.L (eSec t.G) t.G.hom e) t.PP.rig t.PP.rigGen
  obtain ⟨ν, hν⟩ := exists_sabMap_of_lbIso E H _ _ (Inhab.zeroTriple H _) t s (t.G.hom ≫ s)
    ⟨hr, by rw [Inhab.abLocus_eq_univ _ h.proper]; exact Set.subset_univ _⟩ gp
    (fun a => (Over.w_assoc (t.act.act a) s).trans (Category.comp_id _).symm) (lbIso_triv _ _ c hc)
  refine ⟨ν, fun a => ?_⟩
  rw [hν]
  exact (Over.w_assoc (lv a) s).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
    (congrArg (s ≫ ·) ((Over.w (1 : 𝟙_ (Over (Sp (RZ H n N))) ⟶ 𝟙_ _)).symm.trans (Category.comp_id _)))))

end RankZero

theorem zOn_of_top (T : Top Xo n N) (m : ℕ) (a : GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L (m ^ 2)) :
    ∃ X : ZOn T.sM T.tM m, X.Z = T.Z := by
  obtain ⟨W, hW, hiso⟩ := T.u_gen
  have := T.MM_flat
  have := T.flat
  have gen : ∀ {X : Scheme.{0}} (f : X ⟶ Sp (RZ H n N)) [Flat f] (y : X), ∃ y', y' ⤳ y ∧ (f y').asIdeal = ⊥ :=
    fun f _ y => by
      obtain ⟨y', hy', hb⟩ := Flat.generalizingMap f
        (show (⊥ : PrimeSpectrum (RZ H n N)) ⤳ f y from (PrimeSpectrum.le_iff_specializes _ _).1 bot_le)
      exact ⟨y', hy', congrArg PrimeSpectrum.asIdeal hb⟩
  let i : W.toScheme ⟶ T.U.toScheme := inv (T.u ∣_ W) ≫ (T.u ⁻¹ᵁ W).ι
  have hi : i ≫ T.u = W.ι := by
    simp only [i, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  obtain ⟨tW, ⟨mu⟩⟩ := Inhab.exists_pull i T.tU
  obtain ⟨m₁, -⟩ := ObjMaps.exists_sab_comp T.mM mu
  obtain ⟨m₂, -⟩ := ObjMaps.exists_sab_comp T.mU mu
  have hU : Dense (T.U : Set T.Z) := by
    rw [T.U_eq]
    exact Dense.mono T.ga (fun y => by
      obtain ⟨C, hC, hy⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y} isIrreducible_singleton
      have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
      have hm : hC.1.genericPoint ∈ genericPoints T.Z := by
        show closure _ ∈ irreducibleComponents _
        rw [hg.def]; exact hC
      exact closure_mono (Set.singleton_subset_iff.2 hm) (hg.specializes (hy rfl)).mem_closure)
  have hdom : IsDominant (T.u ⁻¹ᵁ W).ι := ⟨fun y => by
    obtain ⟨y', hy', hb⟩ := gen (T.U.ι ≫ T.s) y
    refine closure_mono (Set.singleton_subset_iff.2 ?_) hy'.mem_closure
    rw [Scheme.Opens.range_ι]
    refine hW _ ?_
    rw [← Scheme.Hom.comp_apply, T.u_over]; exact hb⟩
  have : IsDominant T.U.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  refine ⟨⟨T.Z, T.s, T.normal, T.proj, T.flat, T.t, T.qproj, T.good, W, fun y => ?_, i ≫ T.U.ι, inferInstance,
    inferInstance, by rw [Category.assoc, ← T.u_over, ← Category.assoc, hi], tW, hi ▸ m₁, m₂, a⟩, rfl⟩
  obtain ⟨y', hy', hb⟩ := gen T.sM y
  exact closure_mono (Set.singleton_subset_iff.2 (hW _ hb)) hy'.mem_closure

theorem zOn_int (m : ℕ) : ∃ X : ZOn (𝟙 (Sp ℤ)) (Inhab.zeroTriple HostModel.host (Sp ℤ)) m,
    X.W = PrimeSpectrum.basicOpen (2 : ℤ) :=
  let ⟨X, _, h⟩ := zOn_zero (H := HostModel.host) ℤ m (PrimeSpectrum.basicOpen (2 : ℤ))
    ⟨(⊥ : PrimeSpectrum ℤ), (PrimeSpectrum.mem_basicOpen _ _).2 (by simp)⟩
  ⟨X, h⟩

end GlobalTheory.Models.FamTest

end
