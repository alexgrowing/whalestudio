import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem TQ.exists_affine_weight_units [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    (b : Q.B.left) : ∃ V : Q.B.left.Opens, IsAffineOpen V ∧ b ∈ V ∧
      ∃ u : Multiplicative X →* Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ, ∀ χ : X, IsWt Q.i _ (u (Multiplicative.ofAdd χ)).val χ := by
  let e := Module.Free.chooseBasis ℤ X
  choose W hW v hv using fun k => Q.loc b (e k)
  have ho : IsOpen (⋂ k, (W k : Set Q.B.left)) := isOpen_iInter_of_finite fun k => (W k).isOpen
  obtain ⟨V, hV, hbV, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Q.B.left.isBasis_affineOpens
    (show b ∈ (⟨_, ho⟩ : Q.B.left.Opens) from Set.mem_iInter.2 hW)
  have hk : ∀ k, Q.q.left ⁻¹ᵁ V ≤ Q.q.left ⁻¹ᵁ W k := fun k =>
    Q.q.left.preimage_mono fun x hx => Set.mem_iInter.1 (hle hx) k
  let w : _ → Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ := fun k =>
    Units.map (G.left.presheaf.map (homOfLE (hk k)).op).hom.toMonoidHom (v k)
  let l : X →ₗ[ℤ] Additive Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ := e.constr ℤ fun k => Additive.ofMul (w k)
  let H : AddSubgroup X :=
    { carrier := {χ | IsWt Q.i _ (Additive.toMul (l χ)).val χ}
      zero_mem' := by
        show IsWt Q.i _ (Additive.toMul (l 0)).val 0
        rw [map_zero]; exact isWt_one
      add_mem' := fun {a c} ha hc => by
        show IsWt Q.i _ (Additive.toMul (l (a + c))).val (a + c)
        rw [map_add]; exact IsWt.mul ha hc
      neg_mem' := fun {a} ha => by
        show IsWt Q.i _ (Additive.toMul (l (-a))).val (-a)
        rw [map_neg]; exact IsWt.inv ha }
  have hH : Submodule.span ℤ (Set.range e) ≤ H.toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show IsWt Q.i _ (Additive.toMul (l (e k))).val (e k)
    rw [Module.Basis.constr_basis]
    exact (hv k).res (hk k)
  refine ⟨V, hV, hbV, AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom, fun χ => ?_⟩
  exact hH (e.mem_span χ)

theorem TQ.exists_local_section [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    (b : Q.B.left) : ∃ (V : Q.B.left.Opens) (hV : IsAffineOpen V), b ∈ V ∧
      ∃ s : Spec Γ(Q.B.left, V) ⟶ G.left, s ≫ Q.q.left = hV.fromSpec := by
  obtain ⟨V, hV, hb, u, hu⟩ := Q.exists_affine_weight_units b
  have := Q.q_affine
  obtain ⟨hU, hbij⟩ := isAffineOpen_and_bijective_of_weight_units S X G Q.B Q.q Q.i Q.q_hom Q.i_hom Q.q_flat Q.q_surj
    inferInstance Q.isKernel V hV u hu
  let φ := RingEquiv.ofBijective _ hbij
  let ε : AddMonoidAlgebra Γ(Q.B.left, V) X →+* Γ(Q.B.left, V) :=
    (AddMonoidAlgebra.lift Γ(Q.B.left, V) Γ(Q.B.left, V) X 1).toRingHom
  let r : Γ(G.left, Q.q.left ⁻¹ᵁ V) ⟶ Γ(Q.B.left, V) := CommRingCat.ofHom (ε.comp φ.symm.toRingHom)
  have hr : Q.q.left.appLE V _ le_rfl ≫ r = 𝟙 _ := by
    rw [← Scheme.Hom.app_eq_appLE]
    ext a
    have h : φ (AddMonoidAlgebra.single 0 a) = (Q.q.left.app V).hom a :=
      (AddMonoidAlgebra.liftNC_single _ _ 0 a).trans
        ((congrArg (_ * ·) (((Units.coeHom _).comp u).map_one)).trans (_root_.mul_one _))
    change ε (φ.symm ((Q.q.left.app V).hom a)) = a
    rw [← h, RingEquiv.symm_apply_apply]
    simp [ε]
  refine ⟨V, hV, hb, Spec.map r ≫ hU.fromSpec, ?_⟩
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec Q.q.left hV hU le_rfl, ← Category.assoc,
    ← Spec.map_comp, hr, Spec.map_id, Category.id_comp]

theorem TQ.exists_lift [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    {A : Type} [CommRing A] [IsLocalRing A] {p : Spec (CommRingCat.of A) ⟶ S} (b : Over.mk p ⟶ Q.B) :
    ∃ g : Over.mk p ⟶ G, g ≫ Q.q = b := by
  let b' : Spec (CommRingCat.of A) ⟶ Q.B.left := b.left
  obtain ⟨V, hV, hb, s, hs⟩ := Q.exists_local_section (b' (IsLocalRing.closedPoint A))
  have hr : Set.range b' ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of A) b' hb).ge (Set.mem_univ y)
  have h : (IsOpenImmersion.lift hV.fromSpec b' hr ≫ s) ≫ Q.q.left = b' := by
    rw [Category.assoc, hs, IsOpenImmersion.lift_fac]
  refine ⟨Over.homMk (IsOpenImmersion.lift hV.fromSpec b' hr ≫ s) ?_, Over.OverMorphism.ext h⟩
  rw [← Over.w Q.q, ← Category.assoc]
  exact (congrArg (· ≫ Q.B.hom) h).trans (Over.w b)

theorem exists_pow_eq_splitTorus [Module.Free ℤ X] {Z : Over S} {N : ℕ}
    (h : ∀ a : Γ(Z.left, ⊤)ˣ, ∃ r, r ^ N = a) (t : Z ⟶ splitTorus S X) : ∃ t' : Z ⟶ splitTorus S X, t' ^ N = t := by
  let e := Module.Free.chooseBasis ℤ X
  let E := splitTorusPointsEquiv S X Z
  choose r hr using h
  let l : X →ₗ[ℤ] Additive Γ(Z.left, ⊤)ˣ := e.constr ℤ fun k => Additive.ofMul (r (chV t (e k)))
  let m : X →ₗ[ℤ] Additive Γ(Z.left, ⊤)ˣ := (MonoidHom.toAdditiveRight (E t)).toIntLinearMap
  have hl : N • l = m := e.ext fun k => by
    rw [LinearMap.smul_apply, Module.Basis.constr_basis]
    exact congrArg Additive.ofMul (hr _)
  refine ⟨E.symm (AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom), E.injective ?_⟩
  rw [map_pow, MulEquiv.apply_symm_apply]
  exact MonoidHom.ext fun χ => congrArg Additive.toMul (LinearMap.congr_fun hl (Multiplicative.toAdd χ))

theorem torusQuotient_points_lift :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G]
      [IsCommMonObj G] (Q : TQ G X) (A : Type) [CommRing A] [IsLocalRing A] (p : Spec (CommRingCat.of A) ⟶ S),
      (∀ b : Over.mk p ⟶ Q.B, ∃ g : Over.mk p ⟶ G, g ≫ Q.q = b) ∧
      ∀ N : ℕ, (∀ a : Aˣ, ∃ r : Aˣ, r ^ N = a) → ∀ b : Over.mk p ⟶ Q.B, b ^ N = 1 →
        ∃ g : Over.mk p ⟶ G, g ^ N = 1 ∧ g ≫ Q.q = b := by
  intro S X _ _ _ G _ _ Q A _ _ p
  refine ⟨Q.exists_lift, fun N hN b hb => ?_⟩
  have := Q.q_hom
  have := Q.i_hom
  obtain ⟨g, rfl⟩ := Q.exists_lift b
  have h₁ : (g ^ N) ≫ Q.q = toUnit _ ≫ η[Q.B] := by rw [MonObj.pow_comp, hb, Hom.one_def]
  let e : Aˣ ≃* Γ(Spec (CommRingCat.of A), ⊤)ˣ :=
    Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨t, ht⟩ := exists_pow_eq_splitTorus (Z := Over.mk p) (N := N) (fun a => by
    obtain ⟨r, hr⟩ := hN (e.symm a)
    exact ⟨e r, (map_pow e r N).symm.trans ((congrArg e hr).trans (e.apply_symm_apply a))⟩)
    (Q.isKernel.lift _ _ h₁)
  have h₂ : (t ≫ Q.i) ^ N = g ^ N := by rw [← MonObj.pow_comp, ht, IsPullback.lift_fst]
  have h₃ : (t ≫ Q.i) ≫ Q.q = 1 := by
    rw [Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (t ≫ toUnit _) (toUnit _)]
  refine ⟨(t ≫ Q.i)⁻¹ * g, ?_, ?_⟩
  · rw [mul_pow, inv_pow, h₂, inv_mul_cancel]
  · rw [MonObj.mul_comp, GrpObj.inv_comp, h₃, inv_one, _root_.one_mul]

end GlobalTheory.UU
