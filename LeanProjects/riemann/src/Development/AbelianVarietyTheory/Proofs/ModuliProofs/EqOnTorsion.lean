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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabMapCubical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FixTorsionOfForallGeometric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FullRigid

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_of_field (hS : Out.SerreSt) {S : Scheme.{0}} {t : SAB H S} (hp : IsProper t.G.hom)
    (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L) {K : Type} [Field K] [CharZero K] {z : Sp K ⟶ S}
    {t' : SAB H (Sp K)} (m m' : SABMap t' t z) {N : ℕ} (hN : 3 ≤ N)
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ Sp K) (y : Over.mk x ⟶ t'.G),
      y ^ N = 1 → y.left ≫ m.φ = y.left ≫ m'.φ) : m.φ = m'.φ := by
  obtain ⟨θ, hθ, hφ, -, -, w, hw, -⟩ := sabMap_iso m m' rfl rfl
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  obtain ⟨w₁, g₁, -⟩ := m.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := z (IsLocalRing.closedPoint K)) trivial
  have hy : ∀ y, z y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem z hc)).mpr trivial
  have : ConnectedSpace t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t'.G.hom (eSec t'.G (default : PrimeSpectrum K))
  obtain ⟨-, ws, gs', -⟩ := t'.sym
  let P : Out.PolAV (Sp K) :=
    { A := t'.G, g := d, smoothDim := hd, L := t'.PP.L, isLB := t'.PP.isLB
      ample := relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB ((isGen_iff w₁).1 g₁) U hU hy hA
      ktriv := kTriv_pull m.cart t.PP.isLB t'.PP.isLB ((isGen_iff w₁).1 g₁) hK
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp, ‹_›⟩
      rigid := ⟨t'.PP.rig, t'.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  have hNK : IsUnit (N : K) := (Nat.cast_ne_zero.2 (by omega)).isUnit
  have hMu : IsUnit (N : Γ(Sp K, ⊤)) := by
    simpa using hNK.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have : Etale (Out.mulA t'.G N).left := GrpTangent.etale_id_pow t'.G hMu
  have h : θ.hom = 𝟙 _ := by
    refine hS (Sp K) P N hN θ hθ (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_forall_geometric t'.G N θ.hom fun k _ _ x y hy => ?_)
    · obtain ⟨t, ht⟩ := gen_of_iso ((isGen_iff w).1 hw) (t'.G.hom ⁻¹ᵁ ⊤).ι
      refine gen_chartPull (chartPullOut t'.PP.L _ _ _ _ fun n => ?_) t ht
      fin_cases n
      exacts [rfl, (Category.comp_id _).symm]
    · let β : K →+* k := (Spec.preimage x).hom
      have : CharZero k := (RingHom.charZero_iff β.injective).1 inferInstance
      apply Over.OverMorphism.ext
      apply m'.cart.1.hom_ext
      · rw [Over.comp_left, Category.assoc]
        exact (congrArg _ hφ).trans (hfix k x y hy)
      · rw [Over.w, Over.w]
  rw [← hφ, h, Over.id_left, Category.id_comp]

theorem eq_on_torsion {D : Datum H} {n N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp (RZ H n N)} {t : SAB H S}
    {lev : D.La → (𝟙_ (Over S) ⟶ t.G)} {t' : SAB H S'} {f : S' ⟶ S} (ν ν' : SABMap t' t f)
    (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)) (hN : 0 < N) (o : FullObj D s t lev)
    (h : ∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) (h' : ∀ a, (lv a).left ≫ ν'.φ = f ≫ (lev a).left)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S') (y : Over.mk x ⟶ t'.G) (hy : y ^ N = 1) :
    y.left ≫ ν.φ = y.left ≫ ν'.φ := by
  obtain ⟨-, I, -, hI⟩ := o.geom k (x ≫ f) (Spec.preimage ((x ≫ f) ≫ s)).hom (Spec.map_preimage _).symm
  have hy₁ : pushHom ν.cart (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨a, ha⟩ := (I.onto N hN _).1 hy₁
  have e : (x ≫ f) ≫ (lev a).left = y.left ≫ ν.φ := congrArg (fun q => q.left) ((hI a).trans ha)
  have e₁ : y.left = x ≫ (lv a).left := by
    apply ν.cart.1.hom_ext
    · rw [Category.assoc]
      exact e.symm.trans ((Category.assoc _ _ _).trans (congrArg (x ≫ ·) (h a).symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁, Category.assoc, Category.assoc]
  exact congrArg (x ≫ ·) ((h a).trans (h' a).symm)

end GlobalTheory.FullRigid

theorem GlobalTheory.fullObj_rigid : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (t' : SAB H S') (f : S' ⟶ S) (ν ν' : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), 3 ≤ N → Odd N → FullObj D s t lev → IsReduced S' → (∀ x : S', CharZero (S'.residueField x)) → (∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) → (∀ a, (lv a).left ≫ ν'.φ = f ≫ (lev a).left) → ν.φ = ν'.φ := by
  intro hL E _ _ _ H D n N S S' s t lev t' f ν ν' lv hN _ o _ hc h h'
  obtain ⟨θ, hθ, hφ, -⟩ := sabMap_iso ν ν' rfl rfl
  have hA : IsAbelianScheme t'.G := ⟨t'.semi.comm, t'.semi.smooth,
    MorphismProperty.of_isPullback (P := @IsProper) ν.cart.1 o.proper, t'.semi.geomConnected⟩
  have key : θ.hom = 𝟙 _ := by
    refine GlobalTheory.eq_id_of_forall_geometric_fibre hL.globalFns t'.G hA θ.hom (IsMonHom.one_hom θ.hom) fun p => ?_
    have := hc p
    let j : Sp (S'.residueField p) ⟶ S' := S'.fromSpecResidueField p
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull j t'
    generalize (⟨(Over.pullback j).obj t'.G, IsSemiAbelian.pullback _ t'.G t'.semi,
      OAct.pullback _ t'.G t'.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t'' at m
    obtain ⟨a, ha⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν m
    obtain ⟨b, hb⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν' m
    have e : a.φ = b.φ := GlobalTheory.FullRigid.eq_of_field hL.serre o.proper o.ample o.ktriv a b hN fun k _ _ _ x y hy => by
      have hy₁ : pushHom m.cart (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
      have e₁ := GlobalTheory.FullRigid.eq_on_torsion ν ν' lv (by omega) o h h' k (x ≫ j) _ hy₁
      rw [ha, hb, ← Category.assoc, ← Category.assoc]
      exact e₁
    refine ⟨_, _, j, m.φ, _, (default : PrimeSpectrum (S'.residueField p)),
      Scheme.fromSpecResidueField_apply p _, m.cart.1, ?_⟩
    apply ν'.cart.1.hom_ext
    · rw [Category.assoc]
      exact (congrArg (m.φ ≫ ·) hφ).trans (ha.symm.trans (e.trans hb))
    · rw [Category.assoc, Over.w]
  rw [← hφ, key, Over.id_left, Category.id_comp]
