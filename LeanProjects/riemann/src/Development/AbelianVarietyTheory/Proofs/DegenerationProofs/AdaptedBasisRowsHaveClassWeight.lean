import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KfBijective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearIndependentThetaBasisGeometricFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricLiftActionGeometricFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomogeneousCoordinatesOfGeometricFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSectionsFromIntegralModelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSectionsProportionalOfCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusTorsionPointStandardAlternatingFormStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelLabelledTorsionPointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisSeparatesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricLiftOddOrderActsAsExpansionOperatorStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameOfOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClassWeight
open GlobalTheory.UT

theorem proj_mulVec {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) {T : AddSubgroup S.Gam}
    (hT : S.IsoFree T) (c : T →+ ZMod S.N) {K : Type} [CommRing K] (y : o →+* K) (v : S.J → K)
    (h : ∀ t : T, ((S.ρ t).map y).mulVec v = y S.ζN ^ (c t).val • v) : ((S.proj T c).map y).mulVec v = v := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have := Fintype.ofFinite T
  obtain ⟨d, ⟨e⟩⟩ := hT.2
  have hu : IsUnit (Nat.card T : o) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  have hζ : S.ζN ^ S.N = 1 := (S.prim.pow (pow_pos (NeZero.pos _) 2) (by ring) : IsPrimitiveRoot S.ζN S.N).pow_eq_one
  have h1 : ∀ a : ZMod S.N, S.ζN ^ (-a).val * S.ζN ^ a.val = 1 := fun a => by
    have := (AddChar.zmodChar S.N hζ).map_add_eq_mul (-a) a
    rw [neg_add_cancel, AddChar.map_zero_eq_one] at this
    exact this.symm
  let φ : Matrix S.J S.J o →+ (S.J → K) :=
    { toFun := fun M => (M.map y).mulVec v
      map_zero' := by simp
      map_add' := fun M M' => by rw [Matrix.map_add _ (map_add y), Matrix.add_mulVec] }
  have hφ : ∀ (a : o) M, φ (a • M) = y a • φ M := fun a M => by
    funext i
    simp [φ, Matrix.mulVec, dotProduct, Finset.mul_sum, _root_.mul_assoc]
  show φ _ = v
  rw [ThetaSys.proj, finsum_eq_sum_of_fintype, hφ, map_sum]
  have h2 : ∀ t : T, φ (S.ζN ^ (-(c t)).val • S.ρ t) = v := fun t => by
    rw [hφ]
    refine (congrArg _ (h t)).trans ?_
    rw [smul_smul, ← map_pow, ← map_mul, h1, map_one, one_smul]
  simp only [h2, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, ← map_natCast y, ← map_mul, ← Nat.card_eq_fintype_card,
    Ring.inverse_mul_cancel _ hu, map_one, one_smul]

theorem mulVec_eq_of_eigen {K B M J : Type} [CommRing K] [CommRing B] [AddCommGroup M] [Module B M] [Fintype J]
    (κ : K →+* B) (hκ : Function.Injective κ) (E : M →ₗ[B] M) {s : J → M} (hs : LinearIndependent B s)
    (m : Matrix J J K) (h₁ : ∀ j, E (s j) = ∑ l, κ (m l j) • s l) {t : M} {z c : K} (h₂ : E t = κ z • t)
    {v : J → K} (h₃ : ∑ j, κ (v j) • s j = κ c • t) : m.mulVec v = z • v := by
  have h₄ := congrArg E h₃
  rw [map_smul, h₂, smul_comm, ← h₃, map_sum] at h₄
  simp only [map_smul, h₁, Finset.smul_sum, smul_smul] at h₄
  rw [Finset.sum_comm] at h₄
  simp only [← Finset.sum_smul] at h₄
  funext l
  apply hκ
  have h₅ := Fintype.linearIndependent_iffₛ.1 hs _ _ h₄ l
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul]
  rw [← h₅]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

section
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.FieldBaseChange
attribute [local instance] gtGroup
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {F : Type} [Field F]
  [Algebra (FractionRing R) F]

theorem isTor_nsmul {τ : Multiplicative D.toPre.X →* Fˣ} {g : GtPtF D.toPre F} (h : IsTor τ g) (n : ℕ) :
    IsTor (τ ^ n) (n • g) := by
  rw [isTor_iff, isTorusPtF_iff_eq] at h ⊢
  rw [h, ← map_nsmul]
  rfl

theorem exists_qkPt_tor {τ : Multiplicative D.toPre.X →* Fˣ} {g : GtPtF D.toPre F} (h : IsTor τ g) {n : ℕ}
    (hn : τ ^ n = 1) : ∃ q : QkPt D.toPre F n, q.y = 0 ∧ q.g = g := by
  refine ⟨⟨0, g, n • g, (isNsmul_iff_eq _ _ _).2 rfl, (isIota_iff_eq D.tau_bimult _ _).2 ?_⟩, rfl, rfl⟩
  have := isTor_nsmul h n
  rw [hn, isTor_iff, isTorusPtF_iff_eq] at this
  rw [this, map_zero]
  exact map_zero _

variable [CharZero R] [IsAlgClosed F] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem act_of_class (hL : LL) (hA : AdmBase R I) (hG : IsSemiAbelian G) (U : Unif I D A G) {N : ℕ} (hN : Odd N)
    (q : QkPt D.toPre F N) {τ : Multiplicative D.toPre.X →* Fˣ} (hy : q.y = 0) (hτ : IsTor τ q.g) (hτN : τ ^ N = 1)
    {x : TFK (R := R) F ⟶ A.A} (hx : QkToAkU U.toUnifPre F N q x)
    {θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)} (hθ : SymLift A.A A.L N N x θ) {w₀ : W0 U.toUnifPre}
    (hw₀ : w₀.IsGen) {t t' : SecA A F N} {s : Fam D.toPre F N} (hs : U.ExpandsF F N w₀ t s) (c : D.toPre.X)
    (hc : ∀ α, (∀ m, α ≠ c + N • m) → ∀ j, (s.s α).f j = 0) (ha : IsActOf A.A A.L N θ t t') :
    SecM.ofSec A.A t' = kf R F (τ (Multiplicative.ofAdd c)).val • SecM.ofSec A.A t := by
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL R I hA D F N hN q).1
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F hN.pos w₀ hw₀
  have hΦ := GlobalTheory.T.symmetricLift_oddOrder_acts_as_expansionOperator hL R I hA D A G hG U F N hN q x hx θ hθ w₀ hw₀ w hw t t' s (e t') hs ((he _ _).2 rfl) ha
  have h₁ := ((TorusWeight.torus_weight hL R I hA D A G hG U F N hN q τ hy hτ w hw).2 _ _).1 hΦ
  have h₂ : e t' = (τ (Multiplicative.ofAdd c)).val • s := fam_ext fun α j => by
    refine (h₁ α j).trans ?_
    by_cases h : ∃ m, α = c + N • m
    · obtain ⟨m, rfl⟩ := h
      have : τ (Multiplicative.ofAdd (c + N • m)) = τ (Multiplicative.ofAdd c) := by
        rw [ofAdd_add, map_mul, ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, hτN, MonoidHom.one_apply, _root_.mul_one]
      rw [this]
      rfl
    · have h0 := hc α (fun m hm => h ⟨m, hm⟩) j
      rw [DVR.smul_f, h0, mul_zero, mul_zero]
  have h₃ := e.injective (h₂.trans ((congrArg _ ((he _ _).1 hs).symm).trans (e.map_smul _ _).symm))
  exact Subtype.ext (funext fun j => congrArg (fun z : LB.Sec _ => z.f j) h₃)
end

theorem exists_torus_point (hL : LL) (hT : UTorsSt) {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} {u : ρ.UTest p y₀} (l : u.Lab)
    (a : S.perp l.yy.ker) : ∃ (q : QkPt u.D.toPre (PadicAlgCl p) S.N) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
      (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), q.y = 0 ∧ IsTor τ q.g ∧ τ ^ S.N = 1 ∧
      QkToAkU u.U.toUnifPre (PadicAlgCl p) S.N q x ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt (S.r • a.1)).left ∧
      ∀ α, (τ (Multiplicative.ofAdd α)).val = y₀ (algebraMap o S.R S.ζN) ^ (l.wt α a).val := by
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hr := S.r_pos
  have hN₂ := S.N_ge
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨x, hx, hadd, -, honto⟩ := GlobalTheory.T.uniformised_model_labelled_torsion_points o Ω S ρ p y₀ u
  let y : o →+* PadicAlgCl p := y₀.comp (algebraMap o S.R)
  obtain ⟨pk, τ, hy, hτ, hq, hval⟩ := GlobalTheory.T.exists_torus_torsionPoint_standardAlternatingForm hL hT o Ω S ρ p y₀ u l x hx hadd honto a.1 a.2
  have hζ : y S.ζN ^ S.N = 1 := by
    have h : IsPrimitiveRoot S.ζN S.N := S.prim.pow (pow_pos (NeZero.pos _) 2) (by ring)
    rw [← map_pow, h.pow_eq_one, map_one]
  have hwt : ∀ α, ((τ ^ S.r) (Multiplicative.ofAdd α)).val = y S.ζN ^ (l.wt α a).val := fun α => by
    obtain ⟨a', ha'⟩ := l.yy_onto (QuotientAddGroup.mk α)
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hval a' α ha', l.wt_eq a' α ha' a, ZMod.castHom_apply,
      ZMod.cast_eq_val, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ, ← map_pow y, ThetaSys.ζN, ← pow_mul]
    refine (map_pow y _ _).symm.trans (congrArg y ?_)
    rw [← pow_mul]
    congr 1
    ring
  have hτN : (τ ^ S.r) ^ S.N = 1 := MonoidHom.ext fun α => Units.ext (by
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, ← ofAdd_toAdd α, hwt, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rfl)
  let _ := TorusExt.gtGroup u.D.toPre (PadicAlgCl p)
  have hτ' := isTor_nsmul hτ S.r
  obtain ⟨q, hq₀, hq₁⟩ := exists_qkPt_tor hτ' hτN
  have hxr : x a ^ S.r = x (S.r • a) := by
    have h0 : x 0 = 1 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    exact (map_pow (⟨⟨fun z => x z.toAdd, h0⟩, fun z z' => hadd _ _⟩ : Multiplicative S.Gam →* _)
      (Multiplicative.ofAdd a.1) S.r).symm
  have hq' := (GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N S.r (S.r * S.N) (by omega) hr
    (mul_comm _ _) q pk (x a)).2 (hq₀.trans hy.symm) ((TorusExt.isNsmul_iff_eq _ _ _).2 hq₁) hq
  rw [hxr] at hq'
  exact ⟨q, _, _, hq₀, hq₁ ▸ hτ', hτN, hq', hx _, hwt⟩

theorem row_weight : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → ∀ b : Matrix S.J S.J (FractionRing u.V), u.Link σ b → ∀ i, ((S.proj _ (l.wt (cls i))).map fun a => y₀ (algebraMap o S.R a)).mulVec (b.map (algebraMap _ (PadicAlgCl p)) i) = b.map (algebraMap _ (PadicAlgCl p)) i := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l σ cls f hB b hb i
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hodd : Odd S.N := by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow
  have hN₄ : 4 ≤ S.N := by
    have h₁ : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]
    exact Nat.pow_le_pow_left h₁ 2
  obtain ⟨w, hw⟩ := u.lb
  obtain ⟨w₀, hw₀⟩ := u.U.toUnifPre.ext
  choose s hs using fun j => exists_moved u hw (ρ.s j)
  obtain ⟨t, e, ht, he, hcrd⟩ := GlobalTheory.T.exists_generic_sections_from_integral_model hL o Ω S ρ p y₀ u S.N S.J σ f hB.2.2.2.1 hB.2.2.2.2.1 w₀ hw₀
  obtain ⟨c, hc⟩ := GlobalTheory.T.abelianSections_proportional_of_coordinates hL.1.globalFns u.V u.A (PadicAlgCl p) S.N S.J S.J t s
    (b.map (algebraMap _ (PadicAlgCl p))) fun z => by
      obtain ⟨a, rfl⟩ : ∃ a : u.PtC, z = a ≫ u.U.gen.hom := ⟨z ≫ u.U.gen.inv, by simp⟩
      obtain ⟨v, hv⟩ := ((CrdCalc.crd_calculus _ (LPow u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))) _ s
        (DVR.linComb_isLB _ u.A.isLB _ _)).1 (PadicAlgCl p) (ptSecT u.A.A (a ≫ u.U.gen.hom)).left).1
      have h₁ := hb a v (GlobalTheory.T.homogeneousCoordinates_of_geometricFibre o Ω S ρ p y₀ u w hw s hs a v hv)
      exact ⟨v, (GlobalTheory.T.crd_ne_zero_injective_surjective_of_basis hL o Ω S ρ p y₀ u l S.N hN₄ S.J σ cls f hB).1 a _ h₁, hv, hcrd a _ h₁⟩
  let y : o →+* PadicAlgCl p := y₀.comp (algebraMap o S.R)
  refine proj_mulVec S l.isoFree _ y _ fun a => ?_
  obtain ⟨q, x, τ, hq₀, hτ, hτN, hq, hx, hwt⟩ := exists_torus_point hL hT l a
  obtain ⟨θ, hθ, hact⟩ := GlobalTheory.T.exists_symmetricLift_action_geometricFibre o Ω S ρ p y₀ u w hw s hs a.1 _ hx (hq w₀ hw₀).1
  obtain ⟨E, hE, -⟩ := GlobalTheory.thetaGrp_acts_linearly hL.1.globalFns _ u.A (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))
  have h₁ : ∀ j, E θ (SecM.ofSec u.A.A (s j)) =
      ∑ m, kf u.V (PadicAlgCl p) (y (S.ρ a m j)) • SecM.ofSec u.A.A (s m) := fun j =>
    hact j (SecM.toSec u.A.A (E θ (SecM.ofSec u.A.A (s j)))) ((hE _ _ _).2 rfl)
  have h₂ : E θ (SecM.ofSec u.A.A (t i)) =
      kf u.V (PadicAlgCl p) (y S.ζN ^ (l.wt (cls i) a).val) • SecM.ofSec u.A.A (t i) := by
    have h₃ := act_of_class hL hA u.semi u.U hodd q hq₀ hτ hτN hq hθ hw₀ (ht i) (cls i)
      (fun α hα => he i α (hB.2.2.2.2.2.1 i α hα)) (t' := SecM.toSec u.A.A (E θ (SecM.ofSec u.A.A (t i))))
      ((hE _ _ _).2 rfl)
    exact h₃.trans (congrArg (fun z => kf u.V (PadicAlgCl p) z • SecM.ofSec u.A.A (t i)) (hwt (cls i)))
  exact mulVec_eq_of_eigen (kf u.V (PadicAlgCl p)) (kf_bijective _ _).1 (E θ).toLinearMap
    (GlobalTheory.T.linearIndependent_thetaBasis_geometric_fibre hL o Ω S ρ p y₀ u w hw s hs) ((S.ρ a).map y) h₁ h₂ (hc i)

end GlobalTheory.ZH.ClassWeight
end
