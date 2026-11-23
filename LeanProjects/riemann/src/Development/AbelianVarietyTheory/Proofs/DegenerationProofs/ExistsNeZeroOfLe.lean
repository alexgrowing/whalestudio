import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueIsRatio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemNormWeightSumLeExpOfTest
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.OpenPart

theorem le_nonzeroLocus_iff {k K : Type} [CommRing k] [Field K] {X : Scheme.{0}} {p : X ⟶ Sp k} {H : LB X}
    {J : Type} [Fintype J] {s : J → H.Sec} {a : J → k} {φ : H.Sec} (hφ : IsLin p s a φ)
    {x : Sp K ⟶ X} {ψ : k →+* K} (hx : x ≫ p = spMap ψ) {v : J → K} (hv : Crd H s x v) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus φ ↔ ∑ j, ψ (a j) * v j ≠ 0 := by
  have h : Crd H (fun _ : Unit => φ) x (fun _ => ∑ j, ψ (a j) * v j) := by
    obtain ⟨l, c, hl, hv⟩ := hv
    refine ⟨l, c, hl, fun _ => ?_⟩
    beta_reduce
    rw [hφ l, CrdCalc.valR_eq x _ hl, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq,
      GlobalTheory.Points.valR_constFn_of_over p ψ x hx _ hl, hv, mul_left_comm]
  exact (CrdCalc.crd_isUnit_iff () h).symm.trans isUnit_iff_ne_zero

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω}

theorem TT_le_TT {z z' : M.Z} (h : S.supI M z' ⊆ S.supI M z) : S.TT M z ≤ S.TT M z' :=
  fun _ ha b hb => ha b (AddSubgroup.closure_mono h hb)

theorem isOpen_supI_subset (z : M.Z) : IsOpen {z' | S.supI M z ⊆ S.supI M z'} := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : {z' | S.supI M z ⊆ S.supI M z'} = ⋂ a ∈ S.supI M z, {z' | M.Div S.th a z'} := by
    ext z'
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [this]
  exact (Set.toFinite _).isOpen_biInter fun a _ => M.isOpen_setOf_div _ _

theorem supI_subset {U₀ : M.Z.Opens} (h : S.Over₀ M U₀) (z : M.Z) {z' : M.Z} (hz' : z' ∈ U₀) :
    S.supI M z ⊆ S.supI M z' := fun a ha => ⟨ha.1, fun j => by
  rw [div_eq_mul_inv]
  exact RatModel.ringOn_le_O hz' (mul_mem (h.le (S.th_mem j)) (h.th_unit a ha.1))⟩

theorem exists_ne_zero_of_le {T T' : AddSubgroup S.Gam} (h : T' ≤ T) (hT : S.IsoFree T) (hT' : S.IsoFree T')
    {K : Type} [Field K] (ψ : o →+* K) (v : S.J → K) {i : S.J} (hi : ∑ j, ψ (S.proj T 0 j i) * v j ≠ 0) :
    ∃ i, ∑ j, ψ (S.proj T' 0 j i) * v j ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply hi
  rw [← GlobalTheory.ThetaBound.proj_mul_proj S T T' h hT.1 hT' 0 0 fun _ => rfl]
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := congrArg (ψ (S.proj T 0 k i) * ·) (hn k)
  simp only [Finset.mul_sum, mul_zero] at this
  rw [← this]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem le_preimage_G_iff : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (K : Type) [Field K] (x : Sp K ⟶ Q.P.left) (z : M.Z) (ψ : o →+* K) (v : S.J → K), Set.range (x ≫ Q.P.hom) = {z} → (IsClosed ({z} : Set M.Z) ∨ z ∈ U₀) → x ≫ Q.P.hom ≫ M.s = spMap ψ → Crd Q.O1 Q.st x v → (⊤ ≤ x ⁻¹ᵁ Q.G ↔ ∃ i, ∑ j, ψ (S.proj (S.TT M z) 0 j i) * v j ≠ 0) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE hB Q K _ x z ψ v hz hc hψ hv
  have hψ' : x ≫ (Q.P.hom ≫ M.s) = spMap ψ := hψ
  have hxz : Q.P.hom (x (IsLocalRing.closedPoint K)) = z := by
    have : (x ≫ Q.P.hom) (IsLocalRing.closedPoint K) ∈ Set.range (x ≫ Q.P.hom) := ⟨_, rfl⟩
    rw [hz] at this
    exact this
  rw [CrdCalc.top_le_iff]
  simp only [Clos.G, TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨z', -, W, hW, i, φ, hφ, h1, h2⟩
    have h1' : z ∈ W := hxz ▸ h1
    exact exists_ne_zero_of_le (TT_le_TT (hW z h1')) (hB.free _).1 (hB.free _).1 ψ v
      ((le_nonzeroLocus_iff hφ hψ' hv).1 ((CrdCalc.top_le_iff x _).2 h2))
  · intro hi
    obtain ⟨z', hz', hs, hs'⟩ : ∃ z' : M.Z, IsClosed ({z'} : Set M.Z) ∧ S.supI M z' ⊆ S.supI M z ∧
        S.supI M z ⊆ S.supI M z' := by
      rcases hc with hc | hc
      · exact ⟨z, hc, le_rfl, le_rfl⟩
      · have := hB.jac
        obtain ⟨z', h1, h2⟩ := nonempty_inter_closedPoints (Z := (U₀ : Set M.Z)) ⟨z, hc⟩
          U₀.isOpen.isLocallyClosed
        exact ⟨z', h2, supI_subset hB.ov _ hc, supI_subset hB.ov _ h1⟩
    obtain ⟨i, hi⟩ := hi
    obtain ⟨i, hi⟩ := exists_ne_zero_of_le (TT_le_TT hs') (hB.free _).1 (hB.free _).1 ψ v hi
    obtain ⟨φ, hφ, -⟩ := GlobalTheory.SecRatio.existsUnique_isLin (Q.P.hom ≫ M.s) Q.st
      (fun j => S.proj (S.TT M z') 0 j i)
    refine ⟨z', hz', ⟨_, isOpen_supI_subset z'⟩, fun _ h => h, i, φ, hφ, ?_,
      (CrdCalc.top_le_iff x _).1 ((le_nonzeroLocus_iff hφ hψ' hv).2 hi)⟩
    change S.supI M z' ⊆ S.supI M (Q.P.hom (x (IsLocalRing.closedPoint K)))
    rw [hxz]
    exact hs

end GlobalTheory.ZH.OpenPart
