import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSymLiftCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

theorem isOpen_component {X : Type} [TopologicalSpace X] [NoetherianSpace X] (x : X) : IsOpen (connectedComponent x) := by
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have key : (connectedComponent x)ᶜ =
      ⋃₀ {Z | Z ∈ irreducibleComponents X ∧ Disjoint Z (connectedComponent x)} := by
    ext y
    constructor
    · intro hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩,
        mem_irreducibleComponent⟩
      rw [Set.disjoint_left]
      intro z hz hzx
      apply hy
      have hirr : IsIrreducible (irreducibleComponent y) := isIrreducible_irreducibleComponent
      have hsub : irreducibleComponent y ⊆ connectedComponent z :=
        IsPreconnected.subset_connectedComponent (IsPreirreducible.isPreconnected hirr.2) hz
      rw [connectedComponent_eq hzx]
      exact hsub mem_irreducibleComponent
    · rintro ⟨Z, ⟨_, hdisj⟩, hyZ⟩ hyx
      exact Set.disjoint_left.mp hdisj hyZ hyx
  have hcl : IsClosed (connectedComponent x)ᶜ := by
    rw [key, Set.sUnion_eq_biUnion]
    exact Set.Finite.isClosed_biUnion (hfin.subset fun Z hZ => hZ.1)
      fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  exact isClosed_compl_iff.mp hcl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} (Xo : Moduli D l)

theorem moduli_noeth : IsLocallyNoetherian Xo.X := by
  obtain ⟨N, i, hi, -, hs⟩ := Xo.qproj
  haveI := hi
  haveI := isProper_str (KA l) N
  haveI : LocallyOfFiniteType Xo.s := by
    rw [← hs]
    infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian Xo.s

theorem univ_isAb : IsAbelianScheme Xo.univ.t.G :=
  ⟨Xo.univ.t.semi.comm, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩

set_option backward.isDefEq.respectTransparency false in
theorem mulNFin (hM : MulNSt) {N : ℕ} (hN : 1 ≤ N) :
    IsFinite (mulA Xo.univ.t.G N).left ∧ Flat (mulA Xo.univ.t.G N).left ∧ Surjective (mulA Xo.univ.t.G N).left := by
  have := moduli_noeth Xo
  have loc : ∀ y : Xo.univ.t.G.left, ∃ (Y : Scheme.{0}) (φ : Y ⟶ Xo.univ.t.G.left) (m : Y ⟶ Y), IsOpenImmersion φ ∧ (∃ z : Y, φ z = y) ∧
      IsPullback φ m (mulA Xo.univ.t.G N).left φ ∧ IsFinite m ∧ Flat m ∧ Surjective m := fun y => by
    obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := Xo.X) (U := ⊤) (x := Xo.univ.t.G.hom y) trivial
    have : IsAffine U := hU
    have : IsNoetherian U.toScheme := {}
    have : NoetherianSpace U.toScheme := inferInstance
    let V : U.toScheme.Opens := ⟨_, isOpen_component (X := U.toScheme) ⟨_, hy⟩⟩
    have : ConnectedSpace V.toScheme := isConnected_iff_connectedSpace.1 isConnected_connectedComponent
    obtain ⟨t, ⟨m⟩⟩ := exists_sab (V.ι ≫ U.ι) Xo.univ.t
    have := t.semi.smooth
    have := t.semi.geomConnected
    obtain ⟨w, gw', -⟩ := m.lin
    have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 y ⟨⟨_, hy⟩, mem_connectedComponent⟩ rfl
    obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom z
    obtain ⟨-, ws, gs', -⟩ := t.sym
    obtain ⟨a, b, c, -⟩ := hM _
      { A := t.G, g := d, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB
        ample := relAmple_pull m.cart.1 Xo.univ.t.PP.isLB t.PP.isLB ((isGen_iff w).1 gw') U hU (fun y => (V.ι y).2) Xo.univ.ample
        ktriv := kTriv_pull m.cart Xo.univ.t.PP.isLB t.PP.isLB ((isGen_iff w).1 gw') Xo.univ.ktriv
        isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper, ‹_›⟩
        rigid := ⟨t.PP.rig, t.PP.rigGen⟩
        sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ } N hN
    have sq : m.φ ≫ (mulA Xo.univ.t.G N).left = (mulA t.G N).left ≫ m.φ := by
      have e := congrArg (fun q => q.left) (map_pow (pushHom m.cart t.G) (𝟙 t.G) N)
      have e' := congrArg (fun q => q.left) (MonObj.comp_pow (𝟙 Xo.univ.t.G) N (pushHom m.cart t.G (𝟙 t.G)))
      rw [Category.comp_id] at e'
      exact (congrArg (· ≫ _) (Category.id_comp m.φ).symm).trans (e'.trans e.symm)
    exact ⟨_, m.φ, _, MorphismProperty.of_isPullback (P := @IsOpenImmersion) m.cart.1.flip inferInstance, ⟨z, hz⟩,
      (IsPullback.of_bot (by rw [Over.w, Over.w]; exact m.cart.1) sq m.cart.1), a, b, c⟩
  choose Y φ m o c H a b s using loc
  let 𝒰 : Xo.univ.t.G.left.OpenCover := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) _ Y φ (fun y => ⟨y, c y⟩) o
  have key : ∀ (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P], (∀ y, P (m y)) → P (mulA Xo.univ.t.G N).left :=
    fun P _ h => IsZariskiLocalAtTarget.of_openCover (𝒰 := 𝒰) fun y =>
      show P (pullback.snd (mulA Xo.univ.t.G N).left (φ y)) from
        (H y).isoPullback_inv_snd ▸ (P.cancel_left_of_respectsIso (H y).isoPullback.inv (m y)).2 (h y)
  exact ⟨key @IsFinite.{0} a, key @Flat.{0} b, key @Surjective.{0} s⟩

theorem symLiftN (hG : GlobalFnsSt) {N : ℕ} (hN : Odd N) {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G) (ht : t ^ (N ^ 2) = 1) :
    ∃ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T, SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) t U :=
  exists_symLift_odd Xo.univ.t.cub hG (univ_isAb Xo) Xo.univ.t.sym t (k := N ^ 2) (by push_cast; rfl) hN.pow hN.pow ht ht

theorem normMulN (N : ℕ) : ∃ α₀ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2)
    ![𝟙 Xo.univ.t.G.left, (mulA Xo.univ.t.G N).left] ![(N : ℤ) ^ 2, -1]), α₀.IsGen ∧
      IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₀ := by
  have : IsMonHom (mulA Xo.univ.t.G N) := isMonHom_of_mul _ fun _ x y => by
    simp only [mulA, MonObj.comp_pow, Category.comp_id, mul_pow]
  obtain ⟨α, hα, v⟩ := exists_norm (L := Xo.univ.t.PP) (mulA Xo.univ.t.G N) (a := N ^ 2) (b := 1) (a' := (N : ℤ) ^ 2) (b' := 1)
    (by push_cast; rfl) rfl ((genOf_pow Xo.univ.t.cub Xo.univ.t.sym (𝟙 _) N).congr fun _ _ h => by rw [pow_one]; rfl)
  exact ⟨α, hα, corr_of_val Xo.univ.t.PP.isLB fun y I hI => ((val_pull hI _ _ _).trans (v y I hI)).trans
    (((val_mul hI _ _ _).trans (congrArg₂ (· * ·) (map_zpow _ _ _) (val_inv _ _))).trans (by rw [zpow_sub, zpow_one]; rfl)).symm⟩

theorem etaKill (a : D.La) (r : 𝓞 E) (hr : r ∈ l.Mb) : Xo.univ.eta a ≫ Xo.univ.t.act.act r = 1 := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : IsReduced Xo.X := isReduced_of_smooth Xo.s
  have := Xo.univ.proper
  have : IsReduced (𝟙_ (Over Xo.X)).left := ‹IsReduced Xo.X›
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) from
    l.coprime ▸ Submodule.mem_top)
  have ea : Xo.univ.eta a = Xo.univ.eta (v • a) := by
    conv_lhs => rw [← one_smul (𝓞 E) a, ← huv, add_smul, Xo.univ.eta_add,
      Xo.univ.eta_ker _ (Submodule.smul_mem_smul hu Submodule.mem_top), _root_.one_mul]
  obtain ⟨q, hq⟩ : ∃ q : 𝓞 E, r * v = q * l.M := by
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 (l.prod ▸ Ideal.mul_mem_mul hr hv)
    exact ⟨q, hq.symm⟩
  refine Over.OverMorphism.ext (ext_of_fromSpecResidueField_eq _ _ Xo.univ.t.G.hom Set.univ dense_univ (fun x _ => ?_)
    ((Over.w _).trans (Over.w _).symm))
  let k := AlgebraicClosure (Xo.X.residueField x)
  let i : Sp k ⟶ Spec (Xo.X.residueField x) := Spec.map (CommRingCat.ofHom (algebraMap (Xo.X.residueField x) k))
  have : Flat i := (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective i := ⟨fun z => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim (α := PrimeSpectrum _) _ _⟩⟩
  have : Epi i := Flat.epi_of_flat_of_surjective _
  obtain ⟨-, I, -, -, hη⟩ := Xo.univ.geom k (i ≫ Xo.X.fromSpecResidueField x)
    (Spec.preimage ((i ≫ Xo.X.fromSpecResidueField x) ≫ Xo.s)).hom (Spec.map_preimage _).symm
  have e : (toUnit (Over.mk (i ≫ Xo.X.fromSpecResidueField x)) ≫ Xo.univ.eta a) ≫ Xo.univ.t.act.act r = 1 := by
    rw [ea, hη _ (Submodule.smul_mem_smul hv Submodule.mem_top), ← I.lin, smul_smul, hq]
    exact (I.ker _ (by have := l.three_le; omega) _).2 ⟨q • a, by rw [mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]⟩
  rw [← cancel_epi i, ← Category.assoc, ← Category.assoc]
  exact (congrArg (fun q => q.left) ((Category.assoc _ _ _).symm.trans (e.trans (MonObj.comp_one (toUnit _)).symm)))

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
