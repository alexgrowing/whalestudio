import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineCyclotomicLevelOfFinrankInvariants
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.WeakIdealLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoRightExactStatement

noncomputable section

namespace GlobalTheory.NL.RightExactKs

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.NL

section Generic

theorem dvd_pow_of_not_isUnit {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {p : O} (hp : ¬ IsUnit p) {a : O} (ha : a ≠ 0) : ∃ n : ℕ, a ∣ p ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  have h1 : ϖ ∣ p := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hp
  exact ⟨n, hn.dvd.trans (pow_dvd_pow_of_dvd h1 n)⟩

variable {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {LL : Type} [Field LL]
  {O : Type} [CommRing O] [Algebra O LL] [IsDomain O] [IsDiscreteValuationRing O]
  [IsFractionRing O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] {ρ : Representation LL G V}
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
  {ρ' : Representation LL G V'}

theorem lift_integral {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L')
    (hT : IsOpen (L.T : Set V)) {p : ℕ} (hp : ¬ IsUnit (p : O)) (c' : ↥(latticeCocycles L')) (c : G → V)
    (hc : c ∈ continuousCocycles ρ) (v : V') (hv : ∀ g, F.f (c g) - (c' : G → V') g = ρ' g v - v) :
    ∃ (n : ℕ) (c₁ : ↥(latticeCocycles L)), (∀ g, (c₁ : G → V) g = ((p : LL) ^ n) • c g) ∧
      F.H1map (Submodule.Quotient.mk c₁) = (p ^ n : ℕ) • (Submodule.Quotient.mk c' : LatticeCohomology L') := by
  obtain ⟨a, ha, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_fun_mem L hT c hc.1
  obtain ⟨b, hb, h'⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L' v
  obtain ⟨n, d, hd⟩ := dvd_pow_of_not_isUnit hp (mul_ne_zero ha hb)
  have h1 : (p : O) ^ n • c ∈ latticeCocycles L := by
    refine ⟨Submodule.smul_mem ((continuousCocycles ρ).restrictScalars O) _ hc, fun g _ => ?_⟩
    change (p : O) ^ n • c g ∈ L.T
    rw [hd, mul_assoc, mul_comm, mul_smul]
    exact L.T.smul_mem _ (h g)
  have h2 : (p : O) ^ n • v ∈ L'.T := by
    rw [hd, mul_comm, ← mul_assoc, mul_smul]
    exact L'.T.smul_mem _ h'
  refine ⟨n, ⟨_, h1⟩, fun g => ?_, ?_⟩
  · change (p : O) ^ n • c g = _
    rw [← algebraMap_smul LL, map_pow, map_natCast]
  · rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul]
    refine (Submodule.Quotient.eq _).2 ⟨_, h2, ?_⟩
    funext g
    change ρ' g ((p : O) ^ n • v) - (p : O) ^ n • v =
      F.f ((p : O) ^ n • c g) - ((p ^ n : ℕ) : O) • (c' : G → V') g
    rw [Nat.cast_pow, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, ← smul_sub,
      ← smul_sub, hv]

end Generic

theorem lift_integral_res {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [TopologicalSpace Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
    [TopologicalSpace LL] (hO : GoodO (Qp := Qp) LL O) (H : Subgroup G) [CompactSpace ↥H]
    (T₁ T₂ : LocLat G Qp LL O) (π : LatHom T₁.L T₂.L) {p : ℕ} (hp : ¬ IsUnit (p : O))
    (c₂ : ↥(latticeCocycles (resLat T₂ H))) (κ₂ : LatticeCohomology (resLat T₂ H)) (hκ : Submodule.Quotient.mk c₂ = κ₂)
    (c : ↥H → T₁.V) (hc : c ∈ continuousCocycles (T₁.ρ.comp H.subtype)) (v : T₂.V)
    (hv : ∀ g : ↥H, π.f (c g) - (c₂ : ↥H → T₂.V) g = T₂.ρ (g : G) v - v) :
    ∃ (n : ℕ) (c₁ : ↥(latticeCocycles (resLat T₁ H))) (κ₁ : LatticeCohomology (resLat T₁ H)),
      Submodule.Quotient.mk c₁ = κ₁ ∧ (∀ g, (c₁ : ↥H → T₁.V) g = ((p : LL) ^ n) • c g) ∧
      (resHom π H).H1map κ₁ = (p ^ n : ℕ) • κ₂ := by
  obtain ⟨hD, hDVR, hF⟩ := hO.1
  obtain ⟨n, c₁, h1, h2⟩ := lift_integral (resHom π H) (GlobalTheory.Cyc.locLat_isOpen hO T₁) hp c₂ c hc v hv
  exact ⟨n, c₁, _, rfl, h1, hκ ▸ h2⟩

theorem mem_continuousCocycles_restrictLattice {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) (H : Subgroup G) (c : ↥(latticeCocycles (resLat T H))) :
    (c : ↥H → T.V) ∈ continuousCocycles (T.ρ.comp H.subtype) := c.2.1

theorem smul_coboundary {Qp LL V B : Type} [Field Qp] [Field LL] [Algebra Qp LL] [AddCommGroup V]
    [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [CommRing B] [Algebra Qp B]
    (f : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B) (a : LL) {y y' : V} {x : V ⊗[Qp] B} (h : y' = a • y)
    (hx : y ⊗ₜ[Qp] (1 : B) = f x - x) : y' ⊗ₜ[Qp] (1 : B) = f (a • x) - a • x := by
  rw [h, map_smul, ← smul_sub, ← hx]
  rfl

variable {l : ℕ} [Fact l.Prime]

theorem not_isUnit_l (P : LocPrime l) (LL : FinExt l) : ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro hu
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  have h1 : ((l : ℕ) : ↥LL.1) * (u : ↥LL.1) = 1 := by
    have := congrArg (algebraMap ↥(OL LL) ↥LL.1) hu
    rwa [map_mul, map_natCast, map_one] at this
  have h2 := congrArg (P.v LL) h1
  rw [AddValuation.map_mul, AddValuation.map_one, P.v_l] at h2
  have h3 : 0 ≤ P.v LL (u : ↥LL.1) := (P.v_O LL _).2 u.2
  have h4 : (1 : WithTop ℚ) ≤ 0 := h2 ▸ le_add_of_nonneg_right h3
  exact absurd h4 (by simp)

theorem continuous_incl {K E : FinExt l} (hle : K.1 ≤ E.1) :
    Continuous (Subgroup.inclusion (GK_le hle)) :=
  continuous_subtype_val.subtype_mk _

def resRep {K LL : FinExt l} (E : FinExt l) (hle : K.1 ≤ E.1) (T : Lt K LL) :
    GRep ↥(GK E) ℚ_[l] ↥LL.1 ↥(OL LL) where
  V := T.V
  ρ := T.ρ.comp (Subgroup.inclusion (GK_le hle))
  cont x := (T.cont x).comp (continuous_incl hle)

set_option maxHeartbeats 1600000 in

theorem lift_rational (P : LocPrime l) (AI : LocAinf l P) (hP : LocTied l P AI) {K LL : FinExt l}
    (E : FinExt l) (hle : K.1 ≤ E.1) (H : Subgroup ↥(GK K))
    (hH : ∀ x : ↥(GK K), x ∈ H ↔ (x : GQ l) ∈ GK E) (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L)
    (hπ : Function.Surjective π.f) (h₁ : IsCrys (P.PD K) T₁.ρ) (h₂ : IsCrys (P.PD K) T₂.ρ)
    (c₂ : ↥H → T₂.V) (hc₂ : c₂ ∈ continuousCocycles (T₂.ρ.comp H.subtype))
    (x₂ : T₂.V ⊗[ℚ_[l]] P.R.B)
    (hx₂ : ∀ g : ↥H, c₂ g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) T₂.ρ (g : ↥(GK K)) x₂ - x₂) :
    ∃ c₁ ∈ continuousCocycles (T₁.ρ.comp H.subtype),
      (∃ x₁ : T₁.V ⊗[ℚ_[l]] P.R.B,
        ∀ g : ↥H, c₁ g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) T₁.ρ (g : ↥(GK K)) x₁ - x₁) ∧
      ∃ v : T₂.V, ∀ g : ↥H, π.f (c₁ g) - c₂ g = T₂.ρ (g : ↥(GK K)) v - v := by
  let a : ↥(GK E) → ↥H := fun g => ⟨Subgroup.inclusion (GK_le hle) g, (hH _).2 g.2⟩
  let b : ↥H → ↥(GK E) := fun g => ⟨((g : ↥(GK K)) : GQ l), (hH _).1 g.2⟩
  have ha : Continuous a := (continuous_incl hle).subtype_mk _
  have hb : Continuous b := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hres := fun (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) =>
    (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l P AI hP K E LL hle T.V T.ρ).1 hT
  have hc' : c₂ ∘ a ∈ finiteCocycles (P.PD E) (resRep E hle T₂).ρ := by
    refine ⟨⟨hc₂.1.comp ha, fun g h => hc₂.2 (a g) (a h)⟩, x₂, fun g => ?_⟩
    exact (hx₂ (a g)).trans (congrArg (fun f : T₂.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T₂.V ⊗[ℚ_[l]] P.R.B => f x₂ - x₂)
      (GlobalTheory.Cyc.actVB_inclusion P K E LL hle T₂ g).symm)
  obtain ⟨c, ⟨hc, x, hx⟩, v, hv⟩ := GlobalTheory.T.bloch_kato_right_exact l P AI hP E ↥LL.1 ↥(OL LL)
    (GlobalTheory.LocalIntegers.good_integers l LL).1 (resRep E hle T₁) (resRep E hle T₂) π.f
    (fun g y => π.equiv _ y) hπ (hres T₁ h₁) (hres T₂ h₂) _ hc'
  refine ⟨c ∘ b, ⟨hc.1.comp hb, fun g h => hc.2 (b g) (b h)⟩, ⟨x, fun g => ?_⟩, v, fun g => ?_⟩
  · let x' : T₁.V ⊗[ℚ_[l]] P.R.B := x
    exact (hx (b g)).trans (congrArg (fun f : T₁.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T₁.V ⊗[ℚ_[l]] P.R.B => f x' - x')
      (GlobalTheory.Cyc.actVB_inclusion P K E LL hle T₁ (b g)))
  · exact (congrFun hv (b g)).symm

theorem compactSpace_sub {K E : FinExt l} (hle : K.1 ≤ E.1) (H : Subgroup ↥(GK K))
    (hH : ∀ x : ↥(GK K), x ∈ H ↔ (x : GQ l) ∈ GK E) : CompactSpace ↥H := by
  have := GlobalTheory.H1fGeneratorBoundAlt.compactSpace_GK E
  let a : ↥(GK E) → ↥H := fun g => ⟨Subgroup.inclusion (GK_le hle) g, (hH _).2 g.2⟩
  have ha : Continuous a := (continuous_incl hle).subtype_mk _
  have hs : Function.Surjective a := fun g => ⟨⟨((g : ↥(GK K)) : GQ l), (hH _).1 g.2⟩, rfl⟩
  exact hs.compactSpace ha

theorem mem_GKs_iff (P : LocPrime l) {K LL : FinExt l} {s m : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) m) (hs : W.s = s) (x : ↥(GK K)) :
    x ∈ W.GKs ↔ (x : GQ l) ∈ GK (GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants.KsFin K s) := by
  rw [GlobalTheory.Cyc.mem_GKs_iff_mem_Gj, hs]
  rfl

set_option maxHeartbeats 1600000 in

theorem lift_cocycle (P : LocPrime l) (AI : LocAinf l P) (hP : LocTied l P AI) {K LL : FinExt l}
    {s m : ℕ} (hK : K.1 ≤ Ks K s) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) m) (hs : W.s = s)
    (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L)
    (hπ : Function.Surjective π.f) (h₁ : IsCrys (P.PD K) T₁.ρ) (h₂ : IsCrys (P.PD K) T₂.ρ)
    (c₂ : ↥(latticeCocycles (resLat T₂ W.GKs))) (κ₂ : LatticeCohomology (resLat T₂ W.GKs))
    (hκ : Submodule.Quotient.mk c₂ = κ₂) (x₂ : T₂.V ⊗[ℚ_[l]] P.R.B)
    (hx₂ : ∀ g : ↥W.GKs, (c₂ : ↥W.GKs → T₂.V) g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      actVB (P.PD K) T₂.ρ (g : ↥(GK K)) x₂ - x₂) :
    ∃ (n : ℕ) (c₁ : ↥(latticeCocycles (resLat T₁ W.GKs))) (κ₁ : LatticeCohomology (resLat T₁ W.GKs)),
      Submodule.Quotient.mk c₁ = κ₁ ∧
      (∃ x₁ : T₁.V ⊗[ℚ_[l]] P.R.B, ∀ g : ↥W.GKs, (c₁ : ↥W.GKs → T₁.V) g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
        actVB (P.PD K) T₁.ρ (g : ↥(GK K)) x₁ - x₁) ∧
      (resHom π W.GKs).H1map κ₁ = (l ^ n : ℕ) • κ₂ := by
  have hH := mem_GKs_iff P W hs
  have := compactSpace_sub (E := GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants.KsFin K s) hK W.GKs hH
  refine (lift_rational P AI hP (GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants.KsFin K s) hK W.GKs hH T₁ T₂ π hπ h₁ h₂ _
    (mem_continuousCocycles_restrictLattice T₂ W.GKs c₂) x₂ hx₂).elim fun c hc => hc.2.1.elim fun x hx =>
      hc.2.2.elim fun v hv => ?_
  refine (lift_integral_res (GlobalTheory.LocalIntegers.good_integers l LL).1
    W.GKs T₁ T₂ π (not_isUnit_l P LL) c₂ κ₂ hκ c hc.1 v hv).elim fun n h => h.elim fun c₁ h =>
      h.elim fun κ₁ h => ?_
  exact ⟨n, c₁, κ₁, h.1, ⟨((l : ↥LL.1) ^ n) • x, fun g => smul_coboundary _ _ (h.2.1 g) (hx g)⟩,
    h.2.2⟩

end GlobalTheory.NL.RightExactKs
