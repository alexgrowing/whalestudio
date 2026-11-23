import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenOfIsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.FullSiegel

open CechPic

section Bundle

theorem pull_eq_zero_of_chart {X Y : Scheme.{0}} {D : LB X} (hD : D.IsLB) (f : Y ⟶ X) (i : D.ι)
    (hf : ∀ y, f y ∈ D.U i) : pull f (cls D hD) = 0 := by
  rw [← cls_pull hD f (pull_isLB hD f), cls_eq_zero_iff]
  have le : ∀ J : PUnit → D.ι, (D.pull f).U J ≤ f ⁻¹ᵁ (D.U (J PUnit.unit) ⊓ D.U i) :=
    fun J y hy => ⟨mem_pull.1 hy, hf y⟩
  refine ⟨⟨fun J => res (le J) (pullU f _ (D.g (J PUnit.unit) i))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  have val : ∀ J, y ∈ (D.pull f).U J → gm (𝟙 Y) y _ (res (le J) (pullU f _ (D.g (J PUnit.unit) i))) =
      gm (𝟙 Y ≫ f) y _ (D.g (J PUnit.unit) i) := fun J hJ =>
    (gm_res (𝟙 Y) y (le J) hJ _).trans (gm_pull (𝟙 Y) f y _ (le J hJ) _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (val J hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g D f (𝟙 Y) y J J' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (val J' hy.2)))).trans ?_
  exact gm_cocycle hD (𝟙 Y ≫ f) y (mem_pull.1 hy.1) (mem_pull.1 hy.2) (hf y)

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem isLB_lam (hL : L.IsLB) : (abelian₂ G L).IsLB := LB.isLB_linComb hL _ _

theorem cls_lam_pull (hL : L.IsLB) {T : Over S} (x y : T ⟶ G) :
    cls _ (pull_isLB (isLB_lam hL) (lift x y).left) = lam (cls L hL) x y := by
  rw [cls_pull (isLB_lam hL), show cls (abelian₂ G L) (isLB_lam hL) = lam (cls L hL) (fst G G) (snd G G) from
    cls_cube_two hL _ _ _, pull_lam, lift_fst, lift_snd]

theorem lam_symm [IsCommMonObj G] (hL : L.IsLB) :
    LBIso (abelian₂ G L) ((abelian₂ G L).pull (lift (snd G G) (fst G G)).left) := by
  rw [← cls_eq_iff (isLB_lam hL) (pull_isLB (isLB_lam hL) _), cls_lam_pull hL, lam_comm]
  exact cls_cube_two hL _ _ _

theorem pull_one (hL : L.IsLB) (hr : Out.Rigidified G L) (T : Over S) :
    pull (1 : T ⟶ G).left (cls L hL) = 0 := by
  have e := (cls_eq_zero_iff (pull_isLB hL _)).2 hr
  rw [cls_pull hL] at e
  have e' := congrArg (pull (toUnit T).left) e
  rwa [map_zero, ← pull_comp] at e'

theorem eq_one_of_lam_triv (hL : L.IsLB) (hr : Out.Rigidified G L) (hK : Out.KTriv G L) (T : Over S) (x : T ⟶ G)
    (h : ∃ t : ((abelian₂ G L).pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) : x = 1 := by
  have e := (cls_eq_zero_iff (pull_isLB (isLB_lam hL) _)).2 h
  rw [cls_lam_pull hL] at e
  have e' := congrArg (pull (lift (snd T G) (fst T G)).left) e
  rw [map_zero, pull_lam, lift_fst, lift_snd_assoc, lam, pull_one hL hr, add_zero] at e'
  refine KerPow.eq_one_of_locGen hK x fun p => ?_
  obtain ⟨i, hi⟩ := exists_chart hL (x.left p)
  refine ⟨x.left ⁻¹ᵁ L.U i, hi, (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_⟩
  have z := pull_eq_zero_of_chart hL (((fst T G).left ⁻¹ᵁ (x.left ⁻¹ᵁ L.U i)).ι ≫ (fst T G ≫ x).left) i
    fun y => y.2
  have e'' := congrArg (pull ((fst T G).left ⁻¹ᵁ (x.left ⁻¹ᵁ L.U i)).ι) e'
  rw [map_zero, map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, z, sub_zero] at e''
  rw [cls_linComb hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg]
  exact e''

theorem cls_diag (hM : Out.MulPullSt) [IsLocallyNoetherian S] (P : Out.PolAV S) :
    cls _ (pull_isLB (isLB_lam P.isLB) (lift (𝟙 P.A) (𝟙 P.A)).left) = 2 • cls P.L P.isLB := by
  have e := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 (hM S P 2)
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, neg_smul, one_smul, Out.mulA, pow_two] at e
  rw [cls_lam_pull P.isLB, lam, pull_one P.isLB P.rigid, Over.id_left, pull_id, ← add_neg_eq_zero.1 e]
  norm_num
  abel

theorem weilIs_sq (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G) (hL : L.IsLB) {M : LB G.left} (hM : M.IsLB)
    (e : cls M hM = 2 • cls L hL) {n : ℤ} {T : Over S} {x y : T ⟶ G} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs G L n x y c) : Out.WeilIs G M n x y (c ^ 2) := by
  have up : ∀ (T' : Over S) (θ : Out.ThetaGrp G L n T'), ∃ θ' : Out.ThetaGrp G M n T', θ'.pt = θ.pt := by
    intro T' θ
    have z := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨θ.φ, θ.isGen⟩
    obtain ⟨φ, hφ⟩ : ∃ t : LB.Gen (Out.thetaLB G M n θ.pt), t.IsGen := by
      refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_
      rw [cls_linComb hL] at z
      rw [cls_linComb hM, e]
      simp only [map_nsmul, smul_comm _ (2 : ℕ), ← Finset.smul_sum, z, smul_zero]
    exact ⟨⟨θ.pt, φ, hφ⟩, rfl⟩
  obtain ⟨c', hc'⟩ := CommutatorPairing.exists_weilIs (k := n) (x := x) (y := y) hG hA hM
    (fun p => by
      obtain ⟨V, hV, ⟨θ, -, hθ, -⟩, -⟩ := h p
      obtain ⟨θ', h'⟩ := up _ θ
      exact ⟨V, hV, θ', h'.trans hθ⟩)
    (fun p => by
      obtain ⟨V, hV, ⟨-, θ, -, hθ⟩, -⟩ := h p
      obtain ⟨θ', h'⟩ := up _ θ
      exact ⟨V, hV, θ', h'.trans hθ⟩)
  have w : LBIso (lbPow L 2) (M.pull (𝟙 G : G ⟶ G).left) := by
    rw [← cls_eq_iff (isLB_lbPow hL 2) (pull_isLB hM _), cls_lbPow hL, cls_pull hM, Over.id_left, pull_id, e]
  rw [← (weilIs_along_hom hG S G G (𝟙 G) L M 2 n T x y c c' hA hA hL hM inferInstance w (by simpa using hc')).2 h]
  exact hc'

end Bundle

section Points

theorem exists_geomPt {X : Scheme.{0}} (y : X) (hy : CharZero (X.residueField y)) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharZero k) (z : Sp k ⟶ X), ∀ u, z u = y :=
  ⟨AlgebraicClosure (X.residueField y), inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField y) _)) ≫ X.fromSpecResidueField y,
    fun _ => Scheme.fromSpecResidueField_apply y _⟩

theorem smoothOfRelativeDimension_of_charZero {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f]
    (d : ℕ) (hS : ∀ x : S, ∃ ξ : S, ξ ⤳ x ∧ CharZero (S.residueField ξ))
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (m : ℕ),
      SmoothOfRelativeDimension m (pullback.snd f x) → m = d) : SmoothOfRelativeDimension d f := by
  choose n W hW hd using H1.exists_dim f
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  obtain ⟨ξ, hξ, h0⟩ := hS (f y)
  obtain ⟨y', hy', rfl⟩ := hξ.mem_open (f.isOpenMap _ (W y).isOpen) ⟨y, hW y, rfl⟩
  obtain ⟨k, _, _, _, z, hz⟩ := exists_geomPt y'
    (charZero_of_injective_ringHom (f.residueFieldMap y').hom.injective)
  let x : Sp k ⟶ S := z ≫ f
  have : ConnectedSpace ↥(pullback f x) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) x _ _ (IsPullback.of_hasPullback _ _)
  let z' : Sp k ⟶ pullback f x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected (pullback.snd f x) (z' (default : PrimeSpectrum k))
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst f x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ X => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr hy')
  rw [← h k x m hm, ← e₁]
  exact hd y

theorem unitOn_pull {O k : Type} [CommRing O] [CommRing k] {T : Scheme.{0}} (s : T ⟶ Sp O) (x : Sp k ⟶ T)
    (w : O →+* k) (h : x ≫ s = spMap w) (u : Oˣ) :
    Units.map x.appTop.hom.toMonoidHom (Units.map s.appTop.hom.toMonoidHom (unitOn u)) =
      unitOn (Units.map w.toMonoidHom u) := by
  ext
  change (s.appTop ≫ x.appTop).hom _ = _
  rw [← Scheme.Hom.comp_appTop, h]
  exact congrArg (fun q => q.hom (u : O)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom w)).symm

theorem unitOn_injective {k : Type} [CommRing k] : Function.Injective (unitOn (R := k)) :=
  Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1

end Points

section Algebra

theorem onto_of_card {La Q Q' : Type} [AddCommGroup La] [Group Q] [Group Q'] {N m : ℕ} (hm : m ≠ 0) {l : La → Q}
    {l' : La → Q'} (hl : ∀ a c, l (a + c) = l a * l c) (hl' : ∀ a c, l' (a + c) = l' a * l' c)
    (hk : ∀ a, l a = 1 ↔ l' a = 1) (ht : ∀ a, l' a ^ N = 1) (onto : ∀ x, x ^ N = 1 ↔ ∃ a, l a = x)
    (c : Nat.card {x : Q // x ^ N = 1} = m) (c' : Nat.card {x : Q' // x ^ N = 1} = m) (y : Q') (hy : y ^ N = 1) :
    ∃ a, l' a = y := by
  let φ : Multiplicative La →* Q := MonoidHom.mk' (fun x => l x.toAdd) fun x y => hl _ _
  let φ' : Multiplicative La →* Q' := MonoidHom.mk' (fun x => l' x.toAdd) fun x y => hl' _ _
  have e : φ.ker = φ'.ker := Subgroup.ext fun a => hk _
  have r : (φ.range : Set Q) = {x | x ^ N = 1} := Set.ext fun x => (onto x).symm
  have e₁ : Nat.card φ'.range = m := by
    rw [← Subgroup.index_ker, ← e, Subgroup.index_ker, ← c]
    exact congrArg (fun s : Set Q => Nat.card s) r
  have fin : ({x | x ^ N = 1} : Set Q').Finite := Nat.finite_of_card_ne_zero (c'.trans_ne hm)
  have r' : (φ'.range : Set Q') = {x | x ^ N = 1} :=
    Set.eq_of_subset_of_ncard_le (by rintro _ ⟨a, rfl⟩; exact ht _) (c'.trans e₁.symm).le fin
  exact r'.ge hy

theorem exists_eq_smul_of_dvd {g N : ℕ} {a : Fin g ⊕ Fin g → ℤ} (h : ∀ b, (N : ℤ) ∣ omegaStd a b) :
    ∃ b, a = N • b := by
  have d : ∀ i, (N : ℤ) ∣ a i := by
    rintro (i | i)
    · simpa [omegaStd, Pi.single_apply] using h (Pi.single (.inr i) 1)
    · simpa [omegaStd, Pi.single_apply] using h (Pi.single (.inl i) 1)
  choose b hb using d
  exact ⟨b, funext fun i => by simpa using hb i⟩

theorem isPrimitiveRoot_zeta {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (zeta N) N := Complex.isPrimitiveRoot_exp N hN

theorem isPrimitiveRoot_map {p N : ℕ} {k : Type} [Field k] (hk : (N : k) ≠ 0) (β : ZP p N →+* k) :
    IsPrimitiveRoot (β (zetaZP p N)) N := by
  have hN : N ≠ 0 := by rintro rfl; exact hk Nat.cast_zero
  have : NeZero (N : k) := ⟨hk⟩
  have e : (Polynomial.cyclotomic N (ZP p N)).eval (zetaZP p N) = 0 := by
    apply (ZP p N).subtype_injective
    rw [← Polynomial.eval_map_apply, Polynomial.map_cyclotomic, map_zero]
    exact (isPrimitiveRoot_zeta hN).isRoot_cyclotomic (Nat.pos_of_ne_zero hN)
  rw [← Polynomial.isRoot_cyclotomic_iff, Polynomial.IsRoot.def, ← Polynomial.map_cyclotomic N β,
    Polynomial.eval_map_apply, e, map_zero]

theorem rt_sq {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (n N : ℕ) :
    RZ.rt H n N ^ 2 = -(H.d : RZ H n N) := by
  apply Subtype.ext
  have e : ((RZ.rt H n N : RZ H n N) : ℂ) = H.rt0 := by
    change 2 * ((1 + H.rt0) / 2) - 1 = H.rt0
    ring
  simp [e, H.sqrt_neg_disc_sq]

end Algebra

theorem isGrpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul]
  simp [j]

end GlobalTheory.FullSiegel

namespace GlobalTheory

open CechPic FullSiegel

theorem exists_siegPre_of_fullObj : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N p : ℕ) (O : Type) [CommRing O] (b : RZ H n N →+* O) (z : ZP p N →+* O) (T : Scheme.{0}) (sT : T ⟶ Sp O) (t : SAB H T) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), Odd N → IsUnit (N : O) → z (zetaZP p N) = b (RZ.ze H n N) → IsLocallyNoetherian T → (∀ x : T, ∃ ξ : T, ξ ⤳ x ∧ CharZero (T.residueField ξ)) → (∀ x y, D.EF (bas x) (bas y) = omegaStd x y) → FullObj D (sT ≫ spMap b) t lev → ∃ (o : SiegPre g N (zetaZP p N) (sT ≫ spMap z)) (φ : o.A.left ⟶ t.G.left) (φ₂ : (G2 o.A).left ⟶ (G2 t.G).left), o.Principal ∧ IsGrpPullback o.A t.G (𝟙 T) φ ∧ IsSquare φ φ₂ ∧ LBIso o.P ((abelian₂ t.G t.PP.L).pull φ₂) ∧ ∀ u, (o.lev u).left ≫ φ = (lev (bas u)).left := by
  intro hL _ E _ _ _ H D n N p O _ b z T sT t lev g bas hodd hNO hz _ hgen hbas F
  have hN : N ≠ 0 := hodd.pos.ne'
  have hA : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, F.proper, t.semi.geomConnected⟩
  have hLB := t.PP.isLB
  have pt : ∀ {k : Type} [Field k] (x : Sp k ⟶ T), ∃ w : O →+* k, x ≫ sT = spMap w := fun x =>
    ⟨(Spec.preimage (x ≫ sT)).hom, (Spec.map_preimage (x ≫ sT)).symm⟩
  have geo := fun (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ T) (w : O →+* k)
    (hw : x ≫ sT = spMap w) => F.geom k x (w.comp b) (by rw [spMap_comp, reassoc_of% hw])
  have hd : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) t.G.hom := by
    have := hA.smooth
    have := hA.geomConnected
    refine smoothOfRelativeDimension_of_charZero _ _ hgen fun k _ _ _ x m hm => ?_
    obtain ⟨w, hw⟩ := pt x
    exact ObjDim.dim_eq_of_detCond D t.act x (by rw [← map_pow, rt_sq, map_neg, map_natCast]) (geo k x w hw).1 hm
  let P : Out.PolAV T :=
    { A := t.G, isAb := hA, g := _, smoothDim := hd, L := t.PP.L, isLB := hLB, rigid := ObjDim.rigidified,
      sym := ObjDim.sym, ample := F.ample, ktriv := F.ktriv }
  let Φ : Multiplicative D.La →* (𝟙_ (Over T) ⟶ t.G) := MonoidHom.mk' (fun a => lev a.toAdd) fun a c => F.add _ _
  have tors : ∀ a, lev a ^ N = 1 := fun a => (map_pow Φ (Multiplicative.ofAdd a) N).symm.trans (F.ker a)

  have ζN : zetaZP p N ^ N = 1 := Subtype.ext (isPrimitiveRoot_zeta hN).pow_eq_one
  let u : Oˣ := Units.ofPowEqOne (z (zetaZP p N)) N (by rw [← map_pow, ζN, map_one]) hN
  have uN : u ^ N = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val]
    change z (zetaZP p N) ^ N = 1
    rw [← map_pow, ζN, map_one])
  have hNT : IsUnit (N : Γ(T, ⊤)) := by
    have := (hNO.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom).map sT.appTop.hom
    rwa [map_natCast, map_natCast] at this

  have weil : ∀ (k : Type) [Field k] (x : Sp k ⟶ T) (w : O →+* k), x ≫ sT = spMap w → ∀ a c,
      Out.WeilIs t.G t.PP.L N (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev c)
        (unitOn (Units.map w.toMonoidHom u ^ D.EF a c)) := by
    intro k _ x w hw a c
    obtain ⟨U, hU, H'⟩ := PairingLocus.exists_clopen_of_isLocallyNoetherian hL T P N (𝟙_ _) (lev a) (lev c)
      (Units.map sT.appTop.hom.toMonoidHom (unitOn (u ^ D.EF a c))) hNT (tors a) (tors c) (by
        rw [← map_pow, unitOn, ← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, uN,
          one_zpow, map_one, map_one])
    have all : ∀ y, y ∈ U := fun y => by
      obtain ⟨ξ, hξ, h0⟩ := hgen y
      obtain ⟨k', _, _, _, x', hx'⟩ := exists_geomPt ξ h0
      obtain ⟨w', hw'⟩ := pt x'
      obtain ⟨-, I, hζ, hev⟩ := geo k' x' w' hw'
      have e : I.ζ N = Units.map w'.toMonoidHom u := Units.ext (hζ.trans (congrArg w' hz.symm))
      have i := I.isom N (Nat.pos_of_ne_zero hN) a c
      rw [← hev, ← hev, e, ← map_zpow, ← unitOn_pull sT x' w' hw'] at i
      exact hξ.mem_closed hU ((H' _ (toUnit (Over.mk x'))).1 i ⟨(default : PrimeSpectrum k'), hx' _⟩)
    rw [← map_zpow, ← unitOn_pull sT x w hw]
    exact (H' _ (toUnit (Over.mk x))).2 fun y _ => all y
  have hΔ := cls_diag hL.mulPull P
  have hΔ' := pull_isLB (isLB_lam hLB) (lift (𝟙 t.G) (𝟙 t.G)).left

  have ker : ∀ (k : Type) [Field k] (x : Sp k ⟶ T) (a : Fin g ⊕ Fin g → ℤ),
      toUnit (Over.mk x) ≫ lev (bas a) = 1 ↔ ∃ c, a = N • c := by
    intro k _ x a
    refine ⟨fun h => exists_eq_smul_of_dvd fun c => ?_, ?_⟩
    · obtain ⟨w, hw⟩ := pt x
      have i := weil k x w hw (bas a) (bas c)
      rw [h, hbas] at i
      have i₂ := (hL.weil T P N (Over.mk x)).2.1 _ _ _ _ _ i i
      rw [_root_.mul_one] at i₂
      have e := unitOn_injective ((mul_eq_left.1
        (CommutatorPairing.weilIs_unique hL.globalFns hA hLB i₂ i)).trans (map_one _).symm)
      have hk : (N : k) ≠ 0 := by simpa using (hNO.map w).ne_zero
      have pr : IsPrimitiveRoot (Units.map w.toMonoidHom u) N :=
        IsPrimitiveRoot.coe_units_iff.1 (isPrimitiveRoot_map hk (w.comp z))
      exact (pr.zpow_eq_one_iff_dvd _).1 e
    · rintro ⟨c, rfl⟩
      rw [map_nsmul, F.ker, MonObj.comp_one]
  refine ⟨{ A := t.G, ab := hA, P := abelian₂ t.G t.PP.L, isLB := isLB_lam hLB
            rig₁ := (cls_eq_zero_iff (pull_isLB (isLB_lam hLB) _)).1 ((cls_lam_pull hLB _ _).trans (lam_one_left _ _))
            rig₂ := (cls_eq_zero_iff (pull_isLB (isLB_lam hLB) _)).1 ((cls_lam_pull hLB _ _).trans (lam_one_right _ _))
            symm := lam_symm hLB
            lev := fun a => lev (bas a)
            lev_add := fun a c => by rw [map_add, F.add]
            lev_tors := fun a => tors _
            geom := ?_ }, 𝟙 _, 𝟙 _, ⟨?_, eq_one_of_lam_triv hLB P.rigid F.ktriv⟩, isGrpPullback_id _,
    ⟨by simp, by simp⟩, ?_, fun a => Category.comp_id _⟩
  · intro k _ _ x β v hx hv
    obtain ⟨w, hw⟩ := pt x
    obtain rfl : β = w.comp z := by
      rw [reassoc_of% hw, ← spMap_comp] at hx
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective hx.symm)
    obtain rfl : v = Units.map w.toMonoidHom u := Units.ext hv
    refine ⟨ker k x, ?_, fun a c => ?_⟩
    · obtain ⟨ξ, -, h0⟩ := hgen (x (default : PrimeSpectrum k))
      obtain ⟨k', _, _, _, x', -⟩ := exists_geomPt ξ h0
      obtain ⟨w', hw'⟩ := pt x'
      obtain ⟨-, I, -, hev⟩ := geo k' x' w' hw'
      have card := (hL.mulN T P N hodd.pos).2.2.2.2
      refine onto_of_card (pow_ne_zero _ hN) (l := fun a => toUnit (Over.mk x') ≫ lev (bas a))
        (fun a c => by rw [map_add, F.add, MonObj.comp_mul]) (fun a c => by rw [map_add, F.add, MonObj.comp_mul])
        (fun a => (ker k' x' a).trans (ker k x a).symm)
        (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one]) (fun y => ?_)
        (card k' x' (Nat.cast_ne_zero.2 hN)) (card k x (by simpa using (hNO.map w).ne_zero))
      rw [I.onto N hodd.pos, bas.surjective.exists]
      simp only [hev]
    · have i := weilIs_sq hL.globalFns hA hLB hΔ' hΔ (weil k x w hw (bas a) (bas c))
      rwa [unitOn, ← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, hbas] at i
  · have R := relAmple_finite_pow_iso T t.G t.G (𝟙 _) t.PP.L 2 two_pos hA hA hLB (inferInstanceAs (IsFinite (𝟙 _)))
    have R' := relAmple_finite_pow_iso T t.G t.G (𝟙 _) (lbPow t.PP.L 2) 2 two_pos hA hA (isLB_lbPow hLB 2)
      (inferInstanceAs (IsFinite (𝟙 _)))
    exact R'.2.2.2 _ hΔ' ((cls_eq_iff (isLB_lbPow hLB 2) hΔ').1 ((cls_lbPow hLB 2 _).trans hΔ.symm))
      (R.2.1.2 F.ample)
  · exact (cls_eq_iff (isLB_lam hLB) (pull_isLB (isLB_lam hLB) _)).1 (pull_id _).symm

end GlobalTheory
