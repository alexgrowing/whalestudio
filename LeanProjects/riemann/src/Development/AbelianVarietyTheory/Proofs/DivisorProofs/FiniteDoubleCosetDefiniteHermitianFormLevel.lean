import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultLabelRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCentralizerOfCommutePadicPointsSpliStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionModuleStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BorelFiniteClassNumberCentraliserTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialZeroLocusCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteHolds
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

open scoped Pointwise

namespace GlobalTheory.DefClassFin

def CCF : Prop :=
  ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime],
    letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D)
    letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D)
    ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)),
      (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧
        ∀ z ∈ O, TC D σ β y (AfP p) z.1 → TC D σ β y ℚ_[p] z.2 → z ∈ U) →
      ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z, TC D σ β y (AfP p) z.1 →
        TC D σ β y ℚ_[p] z.2 →
        ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ γ.1).unop = algebraMap ℚ D γ.2 * β ∧ Commute (γ.1 : D) y ∧
          ∃ s ∈ S, ∃ u ∈ U, z = dg D p γ * s * u

theorem ccf_holds : CCF :=
  GlobalTheory.T.borel_finite_classNumber_centraliserTorus GlobalTheory.T.exists_polynomialLocus_similitudeCentralizerTorus GlobalTheory.classNumberFinite_holds

theorem finite_of_cover {H : Type} [Group H] (Γ K : Subgroup H) (S : Set H) (hS : S.Finite)
    (h : ∀ g : H, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ k ∈ K, g = γ * s * k) :
    Finite (DoubleCoset.Quotient (Γ : Set H) (K : Set H)) := by
  haveI : Finite S := hS.to_subtype
  refine Finite.of_surjective (fun s : S => DoubleCoset.mk Γ K (s : H)) fun q => ?_
  obtain ⟨γ, hγ, s, hs, k, hk, e⟩ := h q.out
  refine ⟨⟨s, hs⟩, ?_⟩
  change DoubleCoset.mk Γ K s = q
  conv_rhs => rw [← DoubleCoset.out_eq' Γ K q]
  exact (DoubleCoset.eq Γ K _ _).2 ⟨γ, hγ, k, hk, e⟩

theorem cover_of_relIndex {A B : Type} [Group A] [Group B] (Γ : Subgroup (A × B)) (K₁ : Subgroup A)
    (K₂ K' : Subgroup B) (hK : K'.relIndex K₂ ≠ 0) (S : Set (A × B)) (hS : S.Finite)
    (h : ∀ g, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ k ∈ K₁.prod K₂, g = γ * s * k) :
    ∃ S' : Set (A × B), S'.Finite ∧ ∀ g, ∃ γ ∈ Γ, ∃ s ∈ S', ∃ k ∈ K₁.prod K', g = γ * s * k := by
  haveI : (K'.subgroupOf K₂).FiniteIndex := ⟨hK⟩
  let T : Set (A × B) := Set.range (fun c : K₂ ⧸ K'.subgroupOf K₂ => ((1 : A), ((c.out : K₂) : B)))
  have hT : T.Finite := Set.finite_range _
  refine ⟨S * T, hS.mul hT, fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, k, hk, rfl⟩ := h g
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (K'.subgroupOf K₂) (⟨k.2, hk2⟩ : K₂)
  refine ⟨γ, hγ, s * (1, ((((⟨k.2, hk2⟩ : K₂) : K₂ ⧸ K'.subgroupOf K₂).out : K₂) : B)),
    Set.mul_mem_mul hs ⟨_, rfl⟩, (k.1, ((u : K₂) : B)⁻¹),
    Subgroup.mem_prod.2 ⟨hk1, K'.inv_mem (Subgroup.mem_subgroupOf.1 u.2)⟩, ?_⟩
  rw [hu]
  ext <;> simp [mul_assoc]

end GlobalTheory.DefClassFin

namespace GlobalTheory.DefClassFin

variable {p : ℕ} [Fact p.Prime]

theorem inT_of_TC (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C)
    (z : (R ⊗[ℚ] G.C)ˣ × Rˣ) (h : TC G.C G.star β 1 R z) : InT G R β 1 z :=
  ⟨h.1, by rw [map_one]; exact Commute.one_right _⟩

theorem TC_of_inT (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C)
    (z : (R ⊗[ℚ] G.C)ˣ × Rˣ) (h : InT G R β 1 z) : TC G.C G.star β 1 R z :=
  ⟨h.1, by rw [← Algebra.TensorProduct.one_def]; exact Commute.one_right _⟩

theorem psiAway_psiAway_inv (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (w : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) : psiAway G x (psiAway G x⁻¹ w) = w := by
  simp only [psiAway_apply, inv_inv]
  exact Prod.ext (by group) rfl

theorem cover_KHT (P : CCF) (G : HTGroup p) (L : G.Level) (B : GlobalTheory.LKDef.DForm G) :
    ∃ S : Set (G.GAf × Gr G 1), S.Finite ∧ ∀ g : G.GAf × Gr G 1, ∃ γ ∈ B.emb.range, ∃ s ∈ S,
      ∃ k ∈ L.K.toSubgroup.prod (KHT p G.m G.n 1 G.Fw), g = γ * s * k := by
  set x := B.trivAf.choose with hxdef
  set t := B.trivAf.choose_spec.choose with htdef
  have hx : Triv G (AfP p) B.β x t := B.trivAf.choose_spec.choose_spec
  have hemb : ∀ y, B.emb y = (toAfF G B.β x t hx y, toP1 G B.β y) := fun y => rfl
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C)
  let U : Subgroup (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)) :=
    (Subgroup.comap (psiAway G x) (L.K.toSubgroup.map (UPts G.star (AfP p)).subtype)).prod
      (Subgroup.comap (psiP G) (KHT p G.m G.n 1 G.Fw))
  obtain ⟨O₁, hO₁, h1O₁, hO₁U⟩ := exists_open_psiAway_mem_conj_level p G L B.β x t hx 1 1
  obtain ⟨O₂, hO₂, h1O₂, hO₂U⟩ := GlobalTheory.TorCls.OpenP.openp p G 1
  have hO : ∃ O : Set (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧
      ∀ z ∈ O, TC G.C G.star (B.β : G.C) 1 (AfP p) z.1 → TC G.C G.star (B.β : G.C) 1 ℚ_[p] z.2 → z ∈ U := by
    refine ⟨O₁ ×ˢ O₂, hO₁.prod hO₂, ⟨h1O₁, h1O₂⟩, fun z hz h1 _ => Subgroup.mem_prod.2 ⟨?_, ?_⟩⟩
    · obtain ⟨k, hk, e⟩ := hO₁U z.1 hz.1 (inT_of_TC G _ _ _ h1)
      exact ⟨k, hk, by simpa using e⟩
    · have := hO₂U z.2 hz.2
      simpa using this
  obtain ⟨S, hS⟩ := P G.C G.star (B.β : G.C) 1 p U hO

  let Neg : Prop := ∃ γ : G.Cˣ × ℚˣ, (γ.1 : G.C) * (B.β : G.C) * (G.star γ.1).unop =
    algebraMap ℚ G.C γ.2 * (B.β : G.C) ∧ (γ.2 : ℚ) < 0
  let gm : G.Cˣ × ℚˣ := if h : Neg then h.choose else 1
  let S₂ : Set (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)) :=
    (S : Set _) ∪ (fun s => dg G.C p gm * s) '' (S : Set _)
  have hS₂ : S₂.Finite := S.finite_toSet.union (S.finite_toSet.image _)
  let Ψ : (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)) →*
      ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × Gr G 1 := (psiAway G x).prodMap (psiP G)
  let fH : G.GAf × Gr G 1 →* ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × Gr G 1 :=
    (UPts G.star (AfP p)).subtype.prodMap (MonoidHom.id _)
  have hfH : Function.Injective fH := Prod.map_injective.2 ⟨Subtype.val_injective, Function.injective_id⟩
  refine ⟨fH ⁻¹' (Ψ '' S₂), (hS₂.image Ψ).preimage hfH.injOn, fun g => ?_⟩

  have hz₁ := inT_psiAway_inv_of_commute p G B.β x t hx 1 g.1 (by simp)
  simp only [OneMemClass.coe_one, Prod.fst_one, Units.val_one] at hz₁
  obtain ⟨z₂, hz₂, hψ₂⟩ := GlobalTheory.T.exists_unitaryCentralizer_of_commute_padicPoints_split p G B.β B.sym 1 g.2 (by simp)
  simp only [OneMemClass.coe_one, Prod.fst_one, Units.val_one] at hz₂
  set z₁ := psiAway G x⁻¹ (g.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) with hz₁def
  obtain ⟨γ, hγ, -, s, hs, u, hu, hz⟩ := hS (z₁, z₂) (TC_of_inT G _ _ _ hz₁) (TC_of_inT G _ _ _ hz₂)

  have key : ∃ δ : grp G B.β, ∃ s' ∈ S₂, (z₁, z₂) = dg G.C p (δ : G.Cˣ × ℚˣ) * s' * u := by
    rcases lt_or_gt_of_ne (Units.ne_zero γ.2) with hneg | hpos
    · have hN : Neg := ⟨γ, hγ, hneg⟩
      have hgm : gm = hN.choose := dif_pos hN
      obtain ⟨hgmf, hgmn⟩ := hN.choose_spec
      rw [← hgm] at hgmf hgmn
      have hδ := form_mul_inv G.star (B.β : G.C) γ.1 gm.1 γ.2 gm.2 hγ hgmf
      have hδpos : (0 : ℚ) < ((γ.2 * gm.2⁻¹ : ℚˣ) : ℚ) := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val]
        exact mul_pos_of_neg_of_neg hneg (inv_lt_zero.2 hgmn)
      refine ⟨⟨γ * gm⁻¹, hδ, hδpos⟩, dg G.C p gm * s, Or.inr ⟨s, hs, rfl⟩, ?_⟩
      rw [hz]
      simp only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
    · exact ⟨⟨γ, hγ, hpos⟩, s, Or.inl hs, hz⟩
  obtain ⟨δ, s', hs', hz'⟩ := key
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_prod.1 hu
  obtain ⟨k₁, hk₁, ek₁⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hu1)
  have hk₂ : psiP G u.2 ∈ KHT p G.m G.n 1 G.Fw := Subgroup.mem_comap.1 hu2
  let k : G.GAf × Gr G 1 := (k₁, psiP G u.2)
  have hk : k ∈ L.K.toSubgroup.prod (KHT p G.m G.n 1 G.Fw) := Subgroup.mem_prod.2 ⟨hk₁, hk₂⟩
  refine ⟨B.emb δ, ⟨δ, rfl⟩, (B.emb δ)⁻¹ * g * k⁻¹, ⟨s', hs', ?_⟩, k, hk, by group⟩
  have hΨz : Ψ (z₁, z₂) = fH g := by
    refine Prod.ext ?_ hψ₂
    exact psiAway_psiAway_inv G x _
  have hΨd : Ψ (dg G.C p (δ : G.Cˣ × ℚˣ)) = fH (B.emb δ) := by
    refine Prod.ext ?_ ?_
    · exact (toAfF_eq_psiAway G B.β x t hx δ).symm
    · exact (formGroupToPadicPointsDegreeOne_eq_unitaryPoints G B.β δ).symm
  have hΨu : Ψ u = fH k := Prod.ext ek₁.symm rfl
  have e := congrArg Ψ hz'
  rw [map_mul, map_mul, hΨz, hΨd, hΨu] at e
  rw [map_mul, map_mul, map_inv, map_inv, e]
  group

end GlobalTheory.DefClassFin

namespace GlobalTheory.DefClassFin

theorem finite_doubleCoset : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level)
    (K' : Subgroup (Gr G 1)), Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ B : GlobalTheory.LKDef.DForm G,
    Finite (DoubleCoset.Quotient (B.emb.range : Set (G.GAf × Gr G 1))
      ((L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) : Set (G.GAf × Gr G 1))) := by
  intro p _ G _ L K' hK B
  obtain ⟨S, hS, hcov⟩ := cover_KHT ccf_holds G L B
  obtain ⟨S', hS', hcov'⟩ := cover_of_relIndex B.emb.range L.K.toSubgroup _ K' hK.1 S hS hcov
  exact finite_of_cover _ _ S' hS' hcov'

end GlobalTheory.DefClassFin
