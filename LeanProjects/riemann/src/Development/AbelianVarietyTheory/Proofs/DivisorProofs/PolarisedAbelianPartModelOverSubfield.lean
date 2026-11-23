import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyFromVeryDensePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymplecticSystem
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureOpenFamilyQprojFlatReducedExt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaSchemeSectionsGoodFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenericObjectMinimalPrimeModuliChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFibreThetaConstantsRatiosMemSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep.DescentBaseChange

theorem unitS_subfield {K : Type} [Field K] (k₀ : Subfield K) (u : k₀ˣ) :
    ZM.unitS (spMap k₀.subtype ≫ spMap (RingHom.id k₀)) u = unitOn (Units.map k₀.subtype.toMonoidHom u) := by
  ext
  simp only [ZM.unitS, unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (k₀.subtype.comp (RingHom.id k₀)))
  exact (congrArg (fun f => f.hom (u : k₀)) this).symm

theorem tObj_of_baseChange : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K) (N : ℕ), (N : K) ≠ 0 → ∀ (J : Type) (b : ZM.TBase k₀ N), ∃ (t : ZM.TObj D.P.g N J b (spMap k₀.subtype ≫ spMap (RingHom.id k₀))) (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ ∧ LBIso t.L (D.P.L.pull π₁) := by
  intro V₁ _ _ D K _ _ ev k₀ N hN J b
  obtain ⟨L1, -⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨P, φ, hφ, hg, hm, w, hw⟩ := L1.polBaseChange _ _ (spMap ev) D.P
  have hpb : IsGrpPullback P.A D.P.A (spMap ev) φ := by
    refine ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ.w y), ← hm]
    rfl
  let ze : Kˣ := Units.map k₀.subtype.toMonoidHom b.ζ
  have hze : IsPrimitiveRoot ze N := IsPrimitiveRoot.coe_units_iff.1 (b.prim K k₀.subtype)
  obtain ⟨pt, hpt, hpw⟩ := GlobalTheory.EllipticLevel.exists_symplectic_system L1 P N hN ze hze
  have hu := unitS_subfield k₀ b.ζ
  have key : ∀ g', P.g = g' → ∃ (t : ZM.TObj g' N J b (spMap k₀.subtype ≫ spMap (RingHom.id k₀)))
      (π₁ : t.A.left ⟶ D.P.A.left), IsGrpPullback t.A D.P.A (spMap ev) π₁ ∧ LBIso t.L (D.P.L.pull π₁) := by
    rintro _ rfl
    exact ⟨{ A := P.A, ab := P.isAb, dim := P.smoothDim, L := P.L, isLB := P.isLB, rigid := P.rigid, sym := P.sym
             ample := P.ample, ktriv := P.ktriv, pt := pt, torsion := hpt
             bij := GlobalTheory.symplectic_system_torsion_basis L1 K P N ze pt hN hze hpt hpw
             pairing := hu ▸ hpw
             act := fun _ => 𝟙 _, hom := fun _ => inferInstance }, φ, hpb, LBIso.symm ⟨w, hw⟩⟩
  exact key _ hg

theorem tBase_of_isAlgClosed (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharZero k₀] (N : ℕ) (hN : N ≠ 0) : Nonempty (ZM.TBase k₀ N) := by
  haveI : NeZero (N : k₀) := ⟨Nat.cast_ne_zero.2 hN⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N k₀)
    (Polynomial.degree_cyclotomic_pos N k₀ (Nat.pos_of_ne_zero hN)).ne'
  have hp : IsPrimitiveRoot z N := (Polynomial.isRoot_cyclotomic_iff).1 hz
  exact ⟨⟨(hp.isUnit (Nat.pos_of_ne_zero hN).ne').unit, (Nat.cast_ne_zero.2 hN : (N : k₀) ≠ 0).isUnit,
    fun K _ β => hp.map_of_injective β.injective⟩⟩

theorem polarised_part_model : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' D.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧ w.IsGen := by
  intro g n hn hodd
  obtain ⟨L1, L2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_theta_family_from_very_dense_points L1 L2 g Empty (fun x => x.elim) 0 n hn hodd
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.geometric_fibre_thetaConstants_ratios_mem_subfield g n hn hodd
  refine ⟨max (max j₁ j₂) 1, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hDg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hu
  have hj1 : j₁ ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hj
  have hj2 : j₂ ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hj
  have hj3 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hK : ∀ m : ℕ, m ≠ 0 → (m : K) ≠ 0 := fun m hm => by
    rw [← map_natCast ev]; exact ((hunit m hm).map ev).ne_zero
  haveI : CharZero k₀ := charZero_of_inj_zero fun m hm => by
    by_contra h
    exact hK m h (by simpa using congrArg k₀.subtype hm)
  have hN0 : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  obtain ⟨b⟩ := tBase_of_isAlgClosed k₀ ((n ^ j) ^ 2) hN0
  obtain ⟨t, π₁, hπ, hL⟩ := tObj_of_baseChange V₁ D K ev k₀ ((n ^ j) ^ 2) (hK _ hN0) Empty b
  subst hDg
  obtain ⟨v, hv⟩ := ZM.TObj.exists_hasTh_of_isLocalRing L1 L2 (hodd.pow) t
  have hspan := ZM.FamilyScheme.span_theta L1 L2 t n v hn.two_le (dvd_pow_self n (by omega)) hv
  obtain ⟨a', ha'⟩ : ∃ a', v a' ≠ 0 := by
    by_contra h
    push_neg at h
    have : Set.range v ⊆ {0} := by rintro _ ⟨a, rfl⟩; exact h a
    rw [Ideal.span_eq_bot.2 (fun x hx => this hx)] at hspan
    exact bot_ne_top hspan
  have hr := hj₂ j hj2 V₁ hCN hunit D rfl X C e u mo hmo hT K ev k₀ hk₀ hu k₀ Empty b _ t π₁ hπ hL v hv
  choose r hrk hr using fun a => hr a a' ha'
  let w : ZM.Ix D.P.g ((n ^ j) ^ 2) → k₀ := fun a => ⟨r a, hrk a⟩
  have hw : t.HasTh (𝟙 _) (fun a => k₀.subtype (w a)) :=
    GlobalTheory.GenericObject.hasTh_unit_mul t _ v _ (v a')⁻¹ (isUnit_iff_ne_zero.2 (inv_ne_zero ha')) (fun a => by
      show r a = (v a')⁻¹ * v a
      rw [hr a, mul_comm (r a), ← _root_.mul_assoc, inv_mul_cancel₀ ha', _root_.one_mul]) hv
  have hd : ZM.VeryDense (ZM.objPrimes b (fun x : Empty => x.elim) 0 (RingHom.id k₀) w) := by
    intro q f hq hf
    have hq0 : q = ⊥ := by
      rcases Ideal.eq_bot_or_top q with h | h
      · exact h
      · exact absurd h hq.ne_top
    subst hq0
    exact ⟨⊥, ⟨K, inferInstance, inferInstance, k₀.subtype, t, (RingHom.injective_iff_ker_eq_bot _).1 k₀.subtype_injective,
      fun x => x.elim, hw⟩, hq, le_rfl, hf⟩
  obtain ⟨t₀, -, hmap⟩ := hj₁ j hj1 k₀ b k₀ (RingHom.id k₀) w hd
  obtain ⟨φ, hφ, hφL, -, -⟩ := hmap K k₀.subtype t (fun x => x.elim) hw
  obtain ⟨w', hw'⟩ := LBIso.trans (pull_isLB D.P.isLB π₁) t.isLB (pull_isLB t₀.isLB φ) (LBIso.symm hL) hφL
  exact ⟨t₀.A, inferInstance, t₀.ab.comm, t₀.L, t.A, inferInstance, π₁, φ, w', t₀.ab, t₀.isLB, hπ, hφ, hw'⟩

end GlobalTheory.USep.DescentBaseChange
