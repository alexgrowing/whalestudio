import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.BlochKatoBaseChangeLe

open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.TwistedSelmerCompare

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem mem_HfD_gen {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
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
    (L : Lattice (O := O) ρ) (w : G → V ⧸ L.T) :
    w ∈ HfD PD L ↔ ∃ z ∈ finiteCocycles PD ρ, ∃ m : V, ∀ g, w g = Submodule.Quotient.mk (z g + (ρ g m - m)) := by
  constructor
  · intro h
    obtain ⟨_, ⟨z, hz, rfl⟩, _, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨z, hz, m, fun g => rfl⟩
  · rintro ⟨z, hz, m, h⟩
    refine Submodule.mem_sup.2 ⟨_, ⟨z, hz, rfl⟩, _, ⟨Submodule.Quotient.mk m, rfl⟩, ?_⟩
    funext g
    exact (h g).symm

set_option synthInstance.maxHeartbeats 400000 in
omit [IsDomain O] in

theorem mem_HfD_iff (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (w : ↥(GK B.Kw) → (Fin k → Br.LLw B) ⧸ stdG (Br.Ow B) (Br.LLw B) k) :
    w ∈ HfD (P.PD B.Kw) (Br.lat B M) ↔
      ∃ z ∈ finiteCocycles (P.PD B.Kw) (matRep (Br.locM B M)), ∃ m : Fin k → Br.LLw B, ∀ g,
        w g = Submodule.Quotient.mk (z g + ((Br.locM B M g).mulVec m - m)) :=
  mem_HfD_gen (P.PD B.Kw) (Br.lat B M) w

set_option synthInstance.maxHeartbeats 400000 in

def transport (B : LocBridge l E Ω Gw O) (k : ℕ) :
    (↥Gw → KOG O k) →ₛₗ[B.eO.toRingHom]
      (↥(GK B.Kw) → (Fin k → Br.LLw B) ⧸ stdG (Br.Ow B) (Br.LLw B) k) where
  toFun c g := Br.phi B k (c (Br.ι B g))
  map_add' a b := by
    funext g
    exact (Br.phi B k).map_add _ _
  map_smul' c a := by
    funext g
    exact (Br.phi B k).map_smulₛₗ c _

theorem locM_apply (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK B.Kw)) (i j : Fin k) :
    Br.locM B M g i j = Br.toLLK B (algebraMap O (FractionRing O) (M (Br.ι B g) i j)) := by
  rw [Br.toLLK_alg]; rfl

theorem vecS_mulVec (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK B.Kw)) (u : Fin k → FractionRing O) :
    Br.vecS B k ((mapM (algebraMap O (FractionRing O)) M (Br.ι B g)).mulVec u) =
      (Br.locM B M g).mulVec (Br.vecS B k u) := by
  funext i
  change Br.toLLK B (∑ j, algebraMap O (FractionRing O) (M (Br.ι B g) i j) * u j) =
    ∑ j, Br.locM B M g i j * Br.toLLK B (u j)
  simp only [map_sum, map_mul, locM_apply]

set_option synthInstance.maxHeartbeats 400000 in

theorem phi_mem_of_mem_bkG (B : LocBridge l E Ω Gw O) {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (c : ↥(Z1 (WKG M))) (hc : Submodule.Quotient.mk c ∈ Br.bkG B P (WKG M) M) :
    Br.Phi B (WKG M) c ∈ HfD (P.PD B.Kw) (Br.lat B M) := by
  obtain ⟨c₁, h₁, he⟩ := hc
  have he' : c₁ - c ∈ (ReciprocityTheory.Gal.B1 (WKG M)).comap (Z1 (WKG M)).subtype :=
    (Submodule.Quotient.eq _).1 he
  obtain ⟨x, hx⟩ := (mem_coboundaries1 _ _).1 he'
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hB : Br.Phi B (WKG M) (c₁ - c) ∈ HfD (P.PD B.Kw) (Br.lat B M) := by
    refine (mem_HfD_iff P B M _).2 ⟨0, Submodule.zero_mem _, Br.vecS B k u, fun g => ?_⟩
    have := congrArg (Br.phi B k) (hx (Br.ι B g))
    refine this.trans ?_
    rw [Pi.zero_apply, zero_add, ← vecS_mulVec, ← map_sub]
    rfl
  have h2 : c = c₁ - (c₁ - c) := by abel
  rw [h2, map_sub]
  exact Submodule.sub_mem _ h₁ hB

set_option synthInstance.maxHeartbeats 400000 in

theorem push_mem (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (σ : GQ l)
    (hσ : ∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l) * σ⁻¹)
    (f : O₀ →+* O) (hf : Function.Injective f)
    (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) {k : ℕ}
    (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀) (c₀ : ↥Gw → KOG O₀ k)
    (hc : (fun g => Br.phi B₀ k (c₀ (Br.ι B₀ g))) ∈ HfD (P.PD B₀.Kw) (Br.lat B₀ M₀)) :
    (fun g => Br.phi B k (pushKO f hf k (c₀ (Br.ι B g)))) ∈ HfD (P.PD B.Kw) (Br.lat B (mapM f M₀)) := by
  obtain ⟨φ, hφ⟩ := exists_coefMap B₀ B f hf hz
  obtain ⟨z, hzf, m, h⟩ := (mem_HfD_iff P B₀ M₀ _).1 hc
  let θ : ↥(GK B.Kw) →* ↥(GK B₀.Kw) := B₀.e.toMonoidHom.comp (Br.ι B)
  have hθι : ∀ g, Br.ι B₀ (θ g) = Br.ι B g := fun g => B₀.e.symm_apply_apply _
  have hθ : Continuous θ := B₀.e_cont.comp (Br.ι_cont B)
  have hσ' : ∀ g : ↥(GK B.Kw), (g : GQ l) = σ * (θ g : GQ l) * σ⁻¹ := fun g => by
    have := hσ (Br.ι B g)
    rwa [show B.e (Br.ι B g) = g from B.e.apply_symm_apply g] at this
  have hp : ∀ g (v : Fin k → ↥B₀.LL.1), (fun j => φ ((Br.locM B₀ M₀ (θ g)).mulVec v j)) =
      (Br.locM B (mapM f M₀) g).mulVec fun j => φ (v j) := by
    intro g v
    funext i
    change φ (∑ j, Br.locM B₀ M₀ (θ g) i j * v j) = ∑ j, Br.locM B (mapM f M₀) g i j * φ (v j)
    simp only [map_sum, map_mul, locM_apply, hφ, fracMap_alg, hθι]
    rfl
  refine (mem_HfD_iff P B _ _).2 ⟨_, crystallineCocycle_transport_conjugation P B₀.Kw B.Kw B₀.LL B.LL θ hθ σ hσ' _ _ φ.toLinearMap hp z hzf,
    fun j => φ (m j), fun g => ?_⟩
  have hg := h (θ g)
  simp only [hθι] at hg
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (c₀ (Br.ι B g))
  rw [← hu] at hg ⊢
  obtain ⟨n, hn⟩ : Br.vecS B₀ k u - (z (θ g) + ((Br.locM B₀ M₀ (θ g)).mulVec m - m)) ∈
      stdG (Br.Ow B₀) (Br.LLw B₀) k := (Submodule.Quotient.eq _).1 hg
  refine (Submodule.Quotient.eq (stdG (Br.Ow B) (Br.LLw B) k)).2
    ⟨fun j => B.eO (f (B₀.eO.symm (n j))), ?_⟩
  funext j
  have h1 := congrArg φ (congrFun hn j)
  have h2 : algebraMap (Br.Ow B₀) (Br.LLw B₀) (n j) =
      Br.toLLK B₀ (algebraMap O₀ (FractionRing O₀) (B₀.eO.symm (n j))) := by
    rw [Br.toLLK_alg, RingEquiv.apply_symm_apply]
  change φ (algebraMap (Br.Ow B₀) (Br.LLw B₀) (n j)) =
    φ (Br.toLLK B₀ (u j) - (z (θ g) j + ((Br.locM B₀ M₀ (θ g)).mulVec m j - m j))) at h1
  rw [h2, hφ, fracMap_alg, Br.toLLK_alg, map_sub, map_add, map_sub, hφ, congrFun (hp g m) j] at h1
  exact h1

set_option synthInstance.maxHeartbeats 400000 in

theorem extCond_le_bkG : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O₀ O : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra ℤ_[l] O₀] [Module.Finite ℤ_[l] O₀] [TopologicalSpace O₀] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (σ : GQ l), (∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l) * σ⁻¹) → ∀ (f : O₀ →+* O) (hf : Function.Injective f), (∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) → ∀ (k : ℕ) (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀), extCond f hf (WKG M₀) (Br.bkG B₀ P (WKG M₀) M₀) (WKG (mapM f M₀)) ≤ Br.bkG B P (WKG (mapM f M₀)) (mapM f M₀) := by
  intro l _ P E Ω _ _ _ Gw O₀ O _ _ _ _ _ _ _ _ _ _ _ _ B₀ B σ hσ f hf hz k M₀
  refine Submodule.map_mono ?_
  intro c hc
  have key : Submodule.span O {c : ↥Gw → KOG O k | ∃ c₀ : Z1 (WKG M₀),
      Submodule.Quotient.mk c₀ ∈ Br.bkG B₀ P (WKG M₀) M₀ ∧
      c = fun g => pushKO f hf k ((c₀ : ↥Gw → KOG O₀ k) g)} ≤
      (HfD (P.PD B.Kw) (Br.lat B (mapM f M₀))).comap (transport B k) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c₀, h₀, rfl⟩
    exact push_mem P B₀ B σ hσ f hf hz M₀ c₀ (phi_mem_of_mem_bkG P B₀ M₀ c₀ h₀)
  exact key hc

end GlobalTheory.BlochKatoBaseChangeLe

end
