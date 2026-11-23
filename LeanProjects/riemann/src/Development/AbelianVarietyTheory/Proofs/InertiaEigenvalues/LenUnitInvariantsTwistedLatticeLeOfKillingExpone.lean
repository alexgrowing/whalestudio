import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseLen
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInvariantsLtTop
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.LengthH0Bound

theorem toNat_div_le (A B : ℕ∞) (r c : ℕ) (h : A ≤ (r : ℕ∞) * (c : ℕ∞) * B) :
    ((A.toNat : ℚ) / (B.toNat : ℚ)) ≤ (r : ℚ) * c := by
  rcases eq_or_ne B ⊤ with hB | hB
  · rw [hB, ENat.toNat_top, Nat.cast_zero, div_zero]; positivity
  obtain ⟨b, rfl⟩ := ENat.ne_top_iff_exists.mp hB
  have h' : A ≤ ((r * c * b : ℕ) : ℕ∞) := by push_cast; exact h
  obtain ⟨a, ha, hle⟩ := ENat.le_natCast_iff.mp h'
  subst ha
  rw [ENat.toNat_coe, ENat.toNat_coe]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [Nat.cast_zero, div_zero]; positivity
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast hle

theorem lenUnit_le_of_kill {O : Type} [CommRing O] [IsDomain O] (k p c : ℕ)
    (hp : algebraMap O (FractionRing O) (p : O) ≠ 0) (W : Submodule O (KOG O k))
    (hW : ∀ x ∈ W, (p : O) ^ c • x = 0) :
    lenUnit (O := O) p ↥W ≤ (k : ℚ) * c := by
  have hlen := length_le_of_killed (LL := FractionRing O) (stdG O (FractionRing O) k) _
    (GlobalTheory.FiniteTwistInvariants.stdG_eq_span k) (p : O) hp c W hW
  exact toNat_div_le _ _ k c hlen

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem locM_entry {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK Bw.Kw)) (i j : Fin k) :
    Br.locM Bw M g i j = Br.toLLK Bw (algebraMap O (FractionRing O) (M (Br.ι Bw g) i j)) := by
  rw [Br.toLLK_alg]; rfl

theorem vecS_mulVec' {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK Bw.Kw)) (u : Fin k → FractionRing O) :
    Br.vecS Bw k ((mapM (algebraMap O (FractionRing O)) M (Br.ι Bw g)).mulVec u) =
      (Br.locM Bw M g).mulVec (Br.vecS Bw k u) := by
  funext i
  change Br.toLLK Bw (∑ j, algebraMap O (FractionRing O) (M (Br.ι Bw g) i j) * u j) =
    ∑ j, Br.locM Bw M g i j * Br.toLLK Bw (u j)
  simp only [map_sum, map_mul, locM_entry]

set_option synthInstance.maxHeartbeats 400000 in

theorem phi_eq_zero {k : ℕ} (z : KOG O k) (hz : Br.phi Bw k z = 0) : z = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change (Submodule.Quotient.mk (Br.vecS Bw k y) :
    (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k) = 0 at hz
  rw [Submodule.Quotient.mk_eq_zero] at hz
  obtain ⟨b, hb⟩ := hz
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨fun j => Bw.eO.symm (b j), funext fun j => ?_⟩
  apply (Br.toLLK Bw).injective
  have hbj := congrFun hb j
  simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply] at hbj ⊢
  rw [Br.toLLK_alg, RingEquiv.apply_symm_apply]
  exact hbj

set_option synthInstance.maxHeartbeats 400000 in

theorem actD_phi {Γ : Type} [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) O) (f : ↥Gw →* Γ)
    (gK : ↥(GK Bw.Kw)) (x : KOG O k) :
    actD (Br.lat Bw (M.comp f)) gK (Br.phi Bw k x) = Br.phi Bw k ((WKG M).comp f (Br.ι Bw gK) x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h := vecS_mulVec' Bw (M.comp f) gK y
  change (Submodule.Quotient.mk (((Br.locM Bw (M.comp f)) gK).mulVec (Br.vecS Bw k y)) :
      (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k) =
    Submodule.Quotient.mk (Br.vecS Bw k
      (((mapM (algebraMap O (FractionRing O)) (M.comp f)) (Br.ι Bw gK)).mulVec y))
  rw [h]

set_option synthInstance.maxHeartbeats 400000 in

theorem inv_killed {Γ : Type} [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) O) (f : ↥Gw →* Γ) (p c : ℕ)
    (h : ∀ y : (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k,
      (∀ gK, actD (Br.lat Bw (M.comp f)) gK y = y) → ((p : Br.Ow Bw) ^ c) • y = 0) :
    ∀ x ∈ Representation.invariants ((WKG M).comp f), (p : O) ^ c • x = 0 := by
  intro x hx
  have hfix : ∀ gK, actD (Br.lat Bw (M.comp f)) gK (Br.phi Bw k x) = Br.phi Bw k x := by
    intro gK
    rw [actD_phi, hx (Br.ι Bw gK)]
  have hk := h _ hfix
  apply phi_eq_zero Bw
  rw [LinearMap.map_smulₛₗ]
  simp only [map_pow, map_natCast]
  exact hk

include Bw in

theorem natCast_ne_zero : algebraMap O (FractionRing O) ((l : ℕ) : O) ≠ 0 := by
  intro h
  have h2 := congrArg (Br.toLLK Bw) h
  rw [map_natCast, map_natCast, map_zero] at h2
  have hQ : ((l : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  apply hQ
  apply (algebraMap ℚ_[l] (Br.LLw Bw)).injective
  rw [map_natCast, map_zero]
  exact h2

end Bridge

set_option synthInstance.maxHeartbeats 400000 in

theorem main : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i)) (s : ℕ)
    (hs : Good (D.nbr i u hu).Kw s (D.nbr i u hu).LL)
    (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))) g v) (c : ℕ),
    let S := LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i u hu).Kw s (D.nbr i u hu).LL hs;
    ∀ T : LocLat S.G S.Qp S.LL S.O, T = GlobalTheory.HubX.wLat D i ρ π u hu hc →
    (∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ c) • x = 0) →
    (Br.h0W i u ρ π : ℝ) ≤ (D.R.r : ℝ) * c := by
  intro D HW i ρ π u hu s hs hc c S T hT hkill
  subst hT
  have hp : LocalSituation.ell S = D.nd.l i := (D.loc (D.nd.l i)).PD_p _
  have hK := inv_killed (D.nbr i u hu) (WpO D.nd i ρ π) (decS D.nd u) (D.nd.l i) c (fun y hy => by
    have := hkill y hy
    rwa [hp] at this)
  have hq := lenUnit_le_of_kill D.R.r (D.nd.l i) c (natCast_ne_zero (D.nbr i u hu)) _ hK
  exact_mod_cast hq

end GlobalTheory.LengthH0Bound
