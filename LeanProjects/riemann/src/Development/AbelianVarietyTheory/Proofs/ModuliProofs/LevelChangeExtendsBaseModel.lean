import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescOfIsFiniteOfDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleMapExtendingModelMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelChangeLiftKeepingEtaAStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {U U' : Scheme.{0}} {F F' : Type} [Field F] [Field F'] {c : U ⟶ Sp F} {c' : U' ⟶ Sp F'} {t₀ : SAB H U}
  {t₀' : SAB H U'} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* F} {β' : O' →+* F'}

theorem Cpt.basic_of_isDedFrac (C : Cpt c t₀ β) (hβ : IsDedFrac β) :
    IsLocallyNoetherian C.X ∧ IsReduced C.X ∧ IsProper C.s ∧ IsPreimmersion C.j ∧ Flat C.j ∧ IsDominant C.j ∧
      QuasiCompact C.j ∧ C.j ≫ C.s = c ≫ spMap β := by
  obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ
  letI := β.toAlgebra
  obtain ⟨h1, -, -, h2, h3, h4, h5⟩ :=
    GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  refine ⟨h1, ?_, ?_, h2, h3, h4, h5, ?_⟩
  · have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
      have := (C.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  · obtain ⟨N, i, hi, e⟩ := C.proj
    have := isProper_str O N
    rw [← e]; infer_instance
  · rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

theorem Cpt.exists_extension_of_above (C : Cpt c t₀ β) (C' : Cpt c' t₀' β') (hβ : IsDedFrac β) (hβ' : IsDedFrac β')
    {b : O →+* O'} {r : U' ⟶ U} {ν : SABMap t₀' t₀ r} (A : C'.Above C b r ν) (hb : IsFinite (spMap b))
    (hr : Surjective r) {R : Type} [CommRing R] {Z : Scheme.{0}} (sZ : Z ⟶ Sp R) (b' : R →+* O') (q : C'.X ⟶ Z)
    (hq : q ≫ sZ = C'.s ≫ spMap b') (hfin : IsFinite (pullback.lift q C'.s hq))
    (e : U ⟶ U) (e' : U' ⟶ U') (he : e ≫ c = c) (he' : e' ≫ c' = c') (hee : e' ≫ r = r ≫ e)
    (hqe : e' ≫ C'.j ≫ q = C'.j ≫ q) :
    ∃ ρ : C.X ⟶ C.X, ρ ≫ C.s = C.s ∧ C.j ≫ ρ = e ≫ C.j := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := C.basic_of_isDedFrac hβ
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := C'.basic_of_isDedFrac hβ'
  obtain ⟨ρ', ⟨h1, h2⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart C'.X U' _ C'.X C'.j C'.normal m4 m5 m6 m7
    (pullback.lift q C'.s hq) (pullback.lift q C'.s hq) (e' ≫ C'.j) inferInstance (by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, hqe]
      · simp only [Category.assoc, pullback.lift_snd, m8, reassoc_of% he'])
  have h3 : ρ' ≫ C'.s = C'.s := by
    have := congrArg (· ≫ pullback.snd sZ (spMap b')) h2
    simpa only [Category.assoc, pullback.lift_snd] using this
  have hπf : IsFinite A.π := by
    have h4 := A.fin
    have h5 : IsFinite (pullback.fst C.s (spMap b)) := inferInstance
    have h6 : A.π = pullback.lift A.π C'.s A.π_over ≫ pullback.fst C.s (spMap b) := (pullback.lift_fst _ _ _).symm
    rw [h6]; infer_instance
  have hπd : IsDominant A.π := by
    have : IsDominant (C'.j ≫ A.π) := by rw [A.j_comm]; infer_instance
    exact IsDominant.of_comp C'.j A.π
  have hπs : Surjective A.π := surjective_of_isDominant_of_isClosed_range A.π A.π.isClosedMap.isClosed_range
  obtain ⟨ρ, h7, h8⟩ := GlobalTheory.exists_desc_of_isFinite_of_densePart (Sp O) C'.X C.X U' U C.X A.π C'.j C.j r C.s C.s
    (ρ' ≫ A.π) (e ≫ C.j) C.normal m2 hπf hπs hr m6 m7 n4 n5 n6 n7 inferInstance inferInstance A.j_comm
    (by rw [reassoc_of% h1, A.j_comm, reassoc_of% hee])
    (by rw [Category.assoc, A.π_over, reassoc_of% h3])
    (by rw [Category.assoc, n8, reassoc_of% he])
  refine ⟨ρ, ext_of_isDominant C.j ?_, h7⟩
  rw [reassoc_of% h7, n8, reassoc_of% he]

end

theorem extendsAut_of_above : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), 1 ≤ D.p + D.q → ∀ (l₀ l₁ : Level H) (h : l₁.A = N) (O₀ O₁ : Type) [CommRing O₀] [CommRing O₁] (β₀ : O₀ →+* KA l₀) (β₁ : O₁ →+* KA l₁) (C : Cpt (Xo l₀).s (Xo l₀).univ.t β₀) (C₁ : Cpt (Xo l₁).s (Xo l₁).univ.t β₁) (b : O₀ →+* O₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (_ : C₁.Above C b r ν) (b' : RZ H n N →+* O₁) (q : C₁.X ⟶ T.Z) (hq : q ≫ T.s = C₁.s ≫ spMap b'), IsDedFrac β₀ → IsDedFrac β₁ → Algebra.FiniteType ℤ O₀ → IsFinite (spMap b) → IsFinite (pullback.lift q C₁.s hq) → C₁.j ≫ q = T.a l₁ h → l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → N.Coprime l₁.M → LevComp (Xo l₁).univ (Xo l₀).univ r ν → Surjective r → (∃ k : KA l₀ →+* KA l₁, IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k ∧ β₁.comp b = k.comp β₀) → ∀ (r₀ : (Xo l₀).X ≅ (Xo l₀).X) (ν₀ : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r₀.hom) (g : D.La →ₗ[𝓞 E] D.La), r₀.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν₀.φ = r₀.hom ≫ ((Xo l₀).univ.eta x).left) → C.ExtendsAut r₀ ν₀ := by
  intro hext L1 L2 L3 E _ _ _ H D Xo n N T hpq l₀ l₁ h O₀ O₁ _ _ β₀ β₁ C C₁ b r ν A b' q hq hβ₀ hβ₁ hft hb hfin hjq
    hA hM hMb hcop hlev hr hk r₀ ν₀ g hr₀ hη
  obtain ⟨k, hk1, hk2, -⟩ := hk
  obtain ⟨r₁, ν₁, h1, h2, -, h4⟩ := GlobalTheory.T.exists_level_change_lift_keeping_etaA L1 L2 L3 E H D Xo hpq l₀ l₁ r ν r₀ ν₀ g hA hM hMb (h ▸ hcop) hlev
    ⟨k, hk1, hk2⟩ hr₀ hη
  have h5 : r₁.hom ≫ T.a l₁ h = T.a l₁ h := (T.compat l₁ l₁ h h r₁.hom ν₁ (RingHom.id _) (fun _ => rfl) (by
    rw [h1]
    exact (Category.comp_id _).symm.trans (congrArg _ (Spec.map_id (CommRingCat.of (KA l₁))).symm)) h4).1
  obtain ⟨ρ, hρ1, hρ2⟩ := C.exists_extension_of_above C₁ hβ₀ hβ₁ A hb hr T.s b' q hq hfin r₀.hom r₁.hom hr₀ h1 h2
    (by rw [hjq, h5])
  obtain ⟨ρ', hρ1', hρ2'⟩ := C.exists_extension_of_above C₁ hβ₀ hβ₁ A hb hr T.s b' q hq hfin r₀.inv r₁.inv
    (by rw [Iso.inv_comp_eq, hr₀]) (by rw [Iso.inv_comp_eq, h1])
    (by rw [Iso.inv_comp_eq, reassoc_of% h2, Iso.hom_inv_id, Category.comp_id])
    (by rw [hjq, Iso.inv_comp_eq, h5])
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := C.basic_of_isDedFrac hβ₀
  let σ : C.X ≅ C.X :=
    { hom := ρ
      inv := ρ'
      hom_inv_id := ext_of_isDominant_of_isSeparated C.s (by rw [Category.assoc, hρ1', hρ1, Category.id_comp]) C.j
        (by rw [reassoc_of% hρ2, hρ2', Iso.hom_inv_id_assoc, Category.comp_id])
      inv_hom_id := ext_of_isDominant_of_isSeparated C.s (by rw [Category.assoc, hρ1, hρ1', Category.id_comp]) C.j
        (by rw [reassoc_of% hρ2', hρ2, Iso.inv_hom_id_assoc, Category.comp_id]) }
  obtain ⟨mu, hmu⟩ := exists_sabMap_extending hext E H _ _ _ _ _ β₀ _ _ _ _ _ β₀ C C r₀.hom ν₀ ρ hβ₀ hft
    (Xo l₀).univ.proper hρ2
  exact ⟨σ, mu, hρ1, hρ2, hmu⟩

end GlobalTheory.Models
