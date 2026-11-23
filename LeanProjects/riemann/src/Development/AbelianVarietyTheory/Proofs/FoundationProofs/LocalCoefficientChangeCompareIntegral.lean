import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompatibleCoboundaries

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions
open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.TwistedSelmerCompare

namespace GlobalTheory.BlochKatoBaseChange

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem mem_HfD_iff (L : Lattice (O := O) ρ) (c : G → V ⧸ L.T) :
    c ∈ HfD PD L ↔ ∃ z ∈ finiteCocycles PD ρ, ∃ v : V, ∀ g, c g = Submodule.Quotient.mk (z g + (ρ g v - v)) := by
  constructor
  · intro hc
    obtain ⟨_, ⟨z, hz1, rfl⟩, _, ⟨v, rfl⟩, h⟩ := Submodule.mem_sup.1 hc
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact ⟨z, hz1, v, fun g => (congrFun h g).symm⟩
  · rintro ⟨z, hz, v, h⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨z, hz, rfl⟩, _, ⟨Submodule.Quotient.mk v, rfl⟩, funext fun g => (h g).symm⟩

end Gen

section Coord

variable {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [CommRing O] [IsDomain O]
  {f : O₀ →+* O} {hf : Function.Injective f} (p : FractionRing O →+ FractionRing O₀)
  (hp : ∀ y x, p (fracMap f hf y * x) = y * p x)
  (hi : ∀ c : O, ∃ d : O₀, p (algebraMap O _ c) = algebraMap O₀ _ d)

def coordQ (k : ℕ) : KOG O k →+ KOG O₀ k :=
  QuotientAddGroup.map (stdG O (FractionRing O) k).toAddSubgroup (stdG O₀ (FractionRing O₀) k).toAddSubgroup
    (AddMonoidHom.compLeft p (Fin k)) (by
      rintro _ ⟨u, rfl⟩
      choose d hd using hi
      exact ⟨fun j => d (u j), funext fun j => (hd (u j)).symm⟩)

theorem coordQ_mk {k : ℕ} (x : Fin k → FractionRing O) :
    coordQ p hi k (Submodule.Quotient.mk x) = Submodule.Quotient.mk (fun j => p (x j)) := rfl

include hp in
theorem coordQ_act {Γ : Type} [Group Γ] {k : ℕ} (M₀ : Γ →* Matrix (Fin k) (Fin k) O₀) (g : Γ) (x : KOG O k) :
    coordQ p hi k (WKG (mapM f M₀) g x) = WKG M₀ g (coordQ p hi k x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change coordQ p hi k (Submodule.Quotient.mk
      ((((M₀ g).map f).map (algebraMap O (FractionRing O))).mulVec x)) =
    Submodule.Quotient.mk (((M₀ g).map (algebraMap O₀ (FractionRing O₀))).mulVec fun j => p (x j))
  rw [coordQ_mk]
  congr 1
  funext j
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, ← fracMap_alg f hf, hp]

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  [Algebra ℤ_[l] O₀] [TopologicalSpace O₀] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O)

include hp in
theorem exists_coordLL (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) :
    ∃ q : ↥B.LL.1 →ₗ[ℚ_[l]] ↥B₀.LL.1, ∀ x, q (Br.toLLK B x) = Br.toLLK B₀ (p x) := by
  obtain ⟨φ, hφ⟩ := exists_coefMap B₀ B f hf hz
  let e := RingEquiv.ofBijective _ (toLLK_bijective B)
  let q : ↥B.LL.1 →+ ↥B₀.LL.1 := (Br.toLLK B₀).toAddMonoidHom.comp (p.comp e.symm.toAddMonoidHom)
  have hq : ∀ x, q (Br.toLLK B x) = Br.toLLK B₀ (p x) := fun x =>
    congrArg (fun y => Br.toLLK B₀ (p y)) (e.symm_apply_apply x)
  refine ⟨{ q with map_smul' := fun r x => ?_ }, hq⟩
  obtain ⟨x, rfl⟩ := (toLLK_bijective B).2 x
  obtain ⟨y, hy⟩ := (toLLK_bijective B₀).2 (algebraMap ℚ_[l] _ r)
  change q (r • Br.toLLK B x) = r • q (Br.toLLK B x)
  rw [Algebra.smul_def, Algebra.smul_def, ← φ.commutes, ← hy, hφ, ← map_mul, hq, hq, hp, map_mul]

set_option synthInstance.maxHeartbeats 400000 in
theorem phi_coordQ {k : ℕ} (q : ↥B.LL.1 →ₗ[ℚ_[l]] ↥B₀.LL.1)
    (hq : ∀ x, q (Br.toLLK B x) = Br.toLLK B₀ (p x)) (x : KOG O k) (w : Fin k → Br.LLw B)
    (h : Br.phi B k x = Submodule.Quotient.mk w) :
    Br.phi B₀ k (coordQ p hi k x) = Submodule.Quotient.mk (fun j => q (w j)) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : (Submodule.Quotient.mk (fun j => Br.toLLK B (x j)) :
      (Fin k → Br.LLw B) ⧸ stdG (Br.Ow B) (Br.LLw B) k) = Submodule.Quotient.mk w := h
  change (Submodule.Quotient.mk (fun j => Br.toLLK B₀ (p (x j))) :
      (Fin k → Br.LLw B₀) ⧸ stdG (Br.Ow B₀) (Br.LLw B₀) k) = _
  rw [Submodule.Quotient.eq] at h1 ⊢
  obtain ⟨u, hu⟩ := h1
  choose d hd using id hi
  refine ⟨fun j => B₀.eO (d (B.eO.symm (u j))), funext fun j => ?_⟩
  have h2 : algebraMap (Br.Ow B) (Br.LLw B) (u j) = Br.toLLK B (x j) - w j := congrFun hu j
  change algebraMap (Br.Ow B₀) (Br.LLw B₀) _ = Br.toLLK B₀ (p (x j)) - q (w j)
  rw [← Br.toLLK_alg, ← hd, ← hq, ← hq, ← map_sub, ← h2, Br.toLLK_alg, RingEquiv.apply_symm_apply]

include hp in
theorem coordLL_mulVec {k : ℕ} (q : ↥B.LL.1 →ₗ[ℚ_[l]] ↥B₀.LL.1)
    (hq : ∀ x, q (Br.toLLK B x) = Br.toLLK B₀ (p x)) (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀)
    (g : ↥(GK B₀.Kw)) (v : Fin k → Br.LLw B) :
    (fun j => q ((Br.locM B (mapM f M₀) (B.e (B₀.e.symm g))).mulVec v j)) =
      (Br.locM B₀ M₀ g).mulVec fun j => q (v j) := by
  choose x hx using fun j => (toLLK_bijective B).2 (v j)
  funext j
  have h1 : ∀ i, Br.locM B (mapM f M₀) (B.e (B₀.e.symm g)) j i =
      Br.toLLK B (fracMap f hf (algebraMap O₀ _ (M₀ (B₀.e.symm g) j i))) := by
    intro i
    rw [fracMap_alg, Br.toLLK_alg]
    change algebraMap (Br.Ow B) (Br.LLw B) (B.eO (f (M₀ (B.e.symm (B.e (B₀.e.symm g))) j i))) = _
    rw [MulEquiv.symm_apply_apply]
  have h2 : ∀ i, Br.locM B₀ M₀ g j i = Br.toLLK B₀ (algebraMap O₀ _ (M₀ (B₀.e.symm g) j i)) := by
    intro i
    rw [Br.toLLK_alg]
    rfl
  simp only [Matrix.mulVec, dotProduct, map_sum, h1, h2, ← hx, ← map_mul, hq, hp]

include hp in
set_option synthInstance.maxHeartbeats 400000 in
theorem coordQ_mem_HfD (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z)
    (P : LocPrime l) (σ : GQ l)
    (hσ : ∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l) * σ⁻¹)
    {k : ℕ} (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀) (c : ↥Gw → KOG O k)
    (hc : (fun g => Br.phi B k (c (Br.ι B g))) ∈ HfD (P.PD B.Kw) (Br.lat B (mapM f M₀))) :
    (fun g => Br.phi B₀ k (coordQ p hi k (c (Br.ι B₀ g)))) ∈ HfD (P.PD B₀.Kw) (Br.lat B₀ M₀) := by
  obtain ⟨q, hq⟩ := exists_coordLL p hp B₀ B hz
  obtain ⟨z, hz1, v, h⟩ := (mem_HfD_iff _ _ _).1 hc
  let θ : ↥(GK B₀.Kw) →* ↥(GK B.Kw) := B.e.toMonoidHom.comp B₀.e.symm.toMonoidHom
  have hθ : Continuous θ := B.e_cont.comp B₀.e_symm_cont
  have hσ' : ∀ g : ↥(GK B₀.Kw), (g : GQ l) = σ⁻¹ * (θ g : GQ l) * σ⁻¹⁻¹ := by
    intro g
    change _ = σ⁻¹ * (B.e (B₀.e.symm g) : GQ l) * σ⁻¹⁻¹
    rw [hσ, MulEquiv.apply_symm_apply]
    group
  have hm := coordLL_mulVec p hp B₀ B q hq M₀
  have hz2 := crystallineCocycle_transport_conjugation P B.Kw B₀.Kw B.LL B₀.LL θ hθ σ⁻¹ hσ' (Br.locM B (mapM f M₀)) (Br.locM B₀ M₀) q hm z hz1
  refine (mem_HfD_iff _ _ _).2 ⟨_, hz2, fun j => q (v j), fun g => ?_⟩
  have h3 : Br.phi B k (c (Br.ι B₀ g)) = Submodule.Quotient.mk
      (z (θ g) + ((Br.locM B (mapM f M₀) (θ g)).mulVec v - v)) := by
    have h4 : Br.ι B (θ g) = Br.ι B₀ g := B.e.symm_apply_apply _
    rw [← h4]
    exact h (θ g)
  refine (phi_coordQ p hi B₀ B q hq _ _ h3).trans ?_
  change _ = (Submodule.Quotient.mk ((fun j => q (z (θ g) j)) +
    ((Br.locM B₀ M₀ g).mulVec (fun j => q (v j)) - fun j => q (v j))) :
      (Fin k → Br.LLw B₀) ⧸ stdG (Br.Ow B₀) (Br.LLw B₀) k)
  rw [← hm]
  congr 1
  funext j
  simp only [Pi.add_apply, Pi.sub_apply, map_add, map_sub]
  rfl

end Coord

theorem exists_coords {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [CommRing O]
    [IsDomain O] (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O₀] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (f : O₀ →+* O) (hf : Function.Injective f)
    (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → O) (p : ι → FractionRing O →+ FractionRing O₀),
      (∀ a y x, p a (fracMap f hf y * x) = y * p a x) ∧
      (∀ a (c : O), ∃ d : O₀, p a (algebraMap O _ c) = algebraMap O₀ _ d) ∧
      ∀ x, ∑ a, b a • fracMap f hf (p a x) = x := by
  letI := f.toAlgebra
  haveI : IsScalarTower ℤ_[l] O₀ O := IsScalarTower.of_algebraMap_eq fun z => (hz z).symm
  haveI : Module.Finite O₀ O := Module.Finite.of_restrictScalars_finite ℤ_[l] O₀ O
  haveI : FaithfulSMul O₀ O := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  letI := FractionRing.liftAlgebra O₀ (FractionRing O)
  let b := Module.Free.chooseBasis O₀ O
  have he : ∀ y, fracMap f hf y = algebraMap (FractionRing O₀) (FractionRing O) y := by
    intro y
    refine DFunLike.congr_fun (IsFractionRing.ringHom_ext (A := O₀) fun z => ?_ :
      fracMap f hf = algebraMap (FractionRing O₀) (FractionRing O)) y
    rw [fracMap_alg, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply O₀ O (FractionRing O)]
    rfl
  refine ⟨_, inferInstance, b, (SelmerLevel.fracComp b).p, fun a y x => ?_, fun a c => ?_, fun x => ?_⟩
  · rw [he, ← Algebra.smul_def]
    exact ((SelmerLevel.fracBasis b).coord a).map_smul y x
  · obtain ⟨d, hd⟩ := (SelmerLevel.frac_compat b _).1 ⟨c, rfl⟩ a
    exact ⟨d, hd.symm⟩
  · simp only [he]
    exact (SelmerLevel.fracComp b).sum_p x

set_option synthInstance.maxHeartbeats 400000 in

theorem bkG_le_extCond (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω]
    (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O₀ O : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [Algebra ℤ_[l] O₀] [Module.Finite ℤ_[l] O₀] [TopologicalSpace O₀] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O]
    (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (σ : GQ l)
    (hσ : ∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l) * σ⁻¹)
    (f : O₀ →+* O) (hf : Function.Injective f)
    (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z)
    (k : ℕ) (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀) :
    Br.bkG B P (WKG (mapM f M₀)) (mapM f M₀) ≤
      extCond f hf (WKG M₀) (Br.bkG B₀ P (WKG M₀) M₀) (WKG (mapM f M₀)) := by
  obtain ⟨ι, _, b, p, hp, hi, hs⟩ := exists_coords l f hf hz
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨c, ?_, rfl⟩
  have hsum : (c : ↥Gw → KOG O k) =
      ∑ a, b a • fun g => pushKO f hf k (coordQ (p a) (hi a) k ((c : ↥Gw → KOG O k) g)) := by
    funext g
    rw [Finset.sum_apply]
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ ((c : ↥Gw → KOG O k) g)
    have : x = ∑ a, b a • fun j => fracMap f hf (p a (x j)) := by
      funext j
      rw [Finset.sum_apply]
      exact (hs (x j)).symm
    simp only [Pi.smul_apply, ← hx]
    conv_lhs => rw [this, map_sum]
    rfl
  change (c : ↥Gw → KOG O k) ∈ Submodule.span O _
  rw [hsum]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  have hZ : (fun g => coordQ (p a) (hi a) k ((c : ↥Gw → KOG O k) g)) ∈ Z1 (WKG M₀) :=
    ⟨(continuous_of_discreteTopology (f := coordQ (p a) (hi a) k)).comp c.2.1, fun g h => by
      beta_reduce
      rw [c.2.2, map_add, coordQ_act (p a) (hp a)]⟩
  exact ⟨⟨_, hZ⟩, ⟨⟨_, hZ⟩, coordQ_mem_HfD (p a) (hp a) (hi a) B₀ B hz P σ hσ M₀ c hc, rfl⟩, rfl⟩

end GlobalTheory.BlochKatoBaseChange

end
