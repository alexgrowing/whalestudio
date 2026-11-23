import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualPairingCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2PeriodDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeQuotientsNondegenerate

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateLevel

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (I : Submodule O ↥LA.T) (I' : Submodule O ↥LA'.T) (s : LL)
    (hsI : ∀ t ∈ I, ∀ y ∈ LA'.T, s * m (t : A.V) y ∈ L1.T)
    (hsI' : ∀ x ∈ LA.T, ∀ t ∈ I', s * m x (t : A'.V) ∈ L1.T)

def qpair : (↥LA.T ⧸ I) →ₗ[O] (↥LA'.T ⧸ I') →ₗ[O] (LL ⧸ L1.T) :=
  LinearMap.liftQ₂ I I'
    (LinearMap.mk₂ O
      (fun (t : ↥LA.T) (t' : ↥LA'.T) =>
        (Submodule.Quotient.mk (s * m (t : A.V) (t' : A'.V)) : LL ⧸ L1.T))
      (fun t u t' => by
        simp only [Submodule.coe_add, map_add, LinearMap.add_apply, mul_add,
          Submodule.Quotient.mk_add])
      (fun c t t' => by
        rw [Submodule.coe_smul, ← algebraMap_smul LL c (t : A.V), map_smul, LinearMap.smul_apply,
          smul_eq_mul, mul_left_comm, ← Algebra.smul_def, Submodule.Quotient.mk_smul])
      (fun t t' u' => by
        simp only [Submodule.coe_add, map_add, mul_add, Submodule.Quotient.mk_add])
      (fun c t t' => by
        rw [Submodule.coe_smul, ← algebraMap_smul LL c (t' : A'.V), map_smul, smul_eq_mul,
          mul_left_comm, ← Algebra.smul_def, Submodule.Quotient.mk_smul]))
    (fun t ht => LinearMap.mem_ker.2 (LinearMap.ext fun t' => by
      show (Submodule.Quotient.mk (s * m (t : A.V) (t' : A'.V)) : LL ⧸ L1.T) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 (hsI t ht t' t'.2)))
    (fun t' ht' => LinearMap.mem_ker.2 (LinearMap.ext fun t => by
      show (Submodule.Quotient.mk (s * m (t : A.V) (t' : A'.V)) : LL ⧸ L1.T) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 (hsI' t t.2 t' ht')))

theorem qpair_equiv (hI : StableSub LA I) (hI' : StableSub LA' I')
    (hm : ∀ g x y, m (A.ρ g x) (A'.ρ g y) = ((cycLL PD LL g : LLˣ) : LL) * m x y) (g : G)
    (x : ↥LA.T ⧸ I) (y : ↥LA'.T ⧸ I') :
    qpair m L1 I I' s hsI hsI' (actQ LA I hI g x) (actQ LA' I' hI' g y) =
      repD L1 g (qpair m L1 I I' s hsI hsI' x y) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  show (Submodule.Quotient.mk (s * m (A.ρ g (x : A.V)) (A'.ρ g (y : A'.V))) : LL ⧸ L1.T) =
    Submodule.Quotient.mk (charRep (cycLL PD LL) g (s * m (x : A.V) (y : A'.V)))
  rw [hm, mul_left_comm]
  rfl

def zq (hI' : StableSub LA' I') (c : G → ↥LA.T ⧸ I) (c' : G → ↥LA'.T ⧸ I') :
    G × G → LL ⧸ L1.T :=
  fun x => qpair m L1 I I' s hsI hsI' (c x.1) (actQ LA' I' hI' x.1 (c' x.2))

theorem zq_eq (hI' : StableSub LA' I') (c : G → ↥LA.T ⧸ I) (c' : G → ↥LA'.T ⧸ I') (x : G × G) :
    zq m L1 I I' s hsI hsI' hI' c c' x = Submodule.Quotient.mk
      (s * m (Formalism.MainNotions.LocalSituation.liftQ LA I (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' I' (c' x.2)))) := by
  obtain ⟨g, h⟩ := x
  have e1 := (Submodule.Quotient.mk_surjective I (c g)).choose_spec
  have e2 := (Submodule.Quotient.mk_surjective I' (c' h)).choose_spec
  show qpair m L1 I I' s hsI hsI' (c g) (actQ LA' I' hI' g (c' h)) = _
  conv_lhs => rw [← e1, ← e2]
  rfl

theorem cup_cocycle_d2_eq_zero (hI : StableSub LA I) (hI' : StableSub LA' I')
    (hm : ∀ g x y, m (A.ρ g x) (A'.ρ g y) = ((cycLL PD LL g : LLˣ) : LL) * m x y)
    {c : G → ↥LA.T ⧸ I} {c' : G → ↥LA'.T ⧸ I'} (hc : c ∈ quotientCocycles LA I hI) (hc' : c' ∈ quotientCocycles LA' I' hI') :
    ReciprocityTheory.Def.d2 (repD L1) (zq m L1 I I' s hsI hsI' hI' c c') = 0 := by
  funext x
  obtain ⟨g, h, k⟩ := x
  show repD L1 g (zq m L1 I I' s hsI hsI' hI' c c' (h, k)) - zq m L1 I I' s hsI hsI' hI' c c' (g * h, k)
    + zq m L1 I I' s hsI hsI' hI' c c' (g, h * k) - zq m L1 I I' s hsI hsI' hI' c c' (g, h) = 0
  simp only [zq]
  rw [← qpair_equiv m L1 I I' s hsI hsI' hI hI' hm, hc.2 g h, hc'.2 h k, GlobalTheory.TateFin.actQ_mul]
  simp only [map_add, LinearMap.add_apply]
  abel

theorem lc_act (hI' : StableSub LA' I') (hlc' : ∀ y, IsLocallyConstant fun g => actQ LA' I' hI' g y)
    (c' : G → ↥LA'.T ⧸ I') (hc' : IsLocallyConstant c') :
    IsLocallyConstant fun x : G × G => actQ LA' I' hI' x.1 (c' x.2) := by
  rw [IsLocallyConstant.iff_exists_open]
  rintro ⟨g₀, h₀⟩
  obtain ⟨U₂, hU₂, hh₀, hc⟩ := (IsLocallyConstant.iff_exists_open _).1 hc' h₀
  obtain ⟨U₁, hU₁, hg₀, ha⟩ := (IsLocallyConstant.iff_exists_open _).1 (hlc' (c' h₀)) g₀
  refine ⟨U₁ ×ˢ U₂, hU₁.prod hU₂, ⟨hg₀, hh₀⟩, ?_⟩
  rintro ⟨g, h⟩ ⟨hg, hh⟩
  show actQ LA' I' hI' g (c' h) = actQ LA' I' hI' g₀ (c' h₀)
  rw [hc h hh]
  exact ha g hg

theorem cup_cocycle_mem_Z2 (hI : StableSub LA I) (hI' : StableSub LA' I')
    (hm : ∀ g x y, m (A.ρ g x) (A'.ρ g y) = ((cycLL PD LL g : LLˣ) : LL) * m x y)
    (hlc' : ∀ y, IsLocallyConstant fun g => actQ LA' I' hI' g y)
    {c : G → ↥LA.T ⧸ I} {c' : G → ↥LA'.T ⧸ I'} (hc : c ∈ quotientCocycles LA I hI) (hc' : c' ∈ quotientCocycles LA' I' hI') :
    zq m L1 I I' s hsI hsI' hI' c c' ∈ ReciprocityTheory.Def.Z2 (repD L1) ⊤ :=
  ⟨⟨(hc.1.comp_continuous continuous_fst).comp₂ (lc_act I' hI' hlc' c' hc'.1)
      (fun a b => qpair m L1 I I' s hsI hsI' a b), fun _ => Submodule.mem_top⟩,
    LinearMap.mem_ker.2 (cup_cocycle_d2_eq_zero m L1 I I' s hsI hsI' hI hI' hm hc hc')⟩

theorem cup_coboundary_left_mem_B2 (hI : StableSub LA I) (hI' : StableSub LA' I')
    (hm : ∀ g x y, m (A.ρ g x) (A'.ρ g y) = ((cycLL PD LL g : LLˣ) : LL) * m x y)
    {c : G → ↥LA.T ⧸ I} {c' : G → ↥LA'.T ⧸ I'} (hcB : c ∈ BQ LA I hI) (hc' : c' ∈ quotientCocycles LA' I' hI') :
    zq m L1 I I' s hsI hsI' hI' c c' ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ := by
  obtain ⟨x, hx⟩ := hcB
  have hcg : ∀ g, c g = actQ LA I hI g x - x := fun g => (congrFun hx g).symm
  refine ⟨fun h => qpair m L1 I I' s hsI hsI' x (c' h),
    ⟨hc'.1.comp _, fun _ => Submodule.mem_top⟩, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  show repD L1 g (qpair m L1 I I' s hsI hsI' x (c' h)) - qpair m L1 I I' s hsI hsI' x (c' (g * h))
      + qpair m L1 I I' s hsI hsI' x (c' g) =
    qpair m L1 I I' s hsI hsI' (c g) (actQ LA' I' hI' g (c' h))
  rw [hcg, ← qpair_equiv m L1 I I' s hsI hsI' hI hI' hm, hc'.2 g h]
  simp only [map_add, map_sub, LinearMap.sub_apply]
  abel

theorem cup_coboundary_right_mem_B2 (hI : StableSub LA I) (hI' : StableSub LA' I')
    (hm : ∀ g x y, m (A.ρ g x) (A'.ρ g y) = ((cycLL PD LL g : LLˣ) : LL) * m x y)
    (hlc' : ∀ y, IsLocallyConstant fun g => actQ LA' I' hI' g y)
    {c : G → ↥LA.T ⧸ I} {c' : G → ↥LA'.T ⧸ I'} (hc : c ∈ quotientCocycles LA I hI) (hcB : c' ∈ BQ LA' I' hI') :
    zq m L1 I I' s hsI hsI' hI' c c' ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ := by
  obtain ⟨y, hy⟩ := hcB
  have hcg : ∀ h, c' h = actQ LA' I' hI' h y - y := fun h => (congrFun hy h).symm
  refine ⟨fun g => -qpair m L1 I I' s hsI hsI' (c g) (actQ LA' I' hI' g y),
    ⟨hc.1.comp₂ (hlc' y) (fun a b => -qpair m L1 I I' s hsI hsI' a b), fun _ => Submodule.mem_top⟩, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  show repD L1 g (-qpair m L1 I I' s hsI hsI' (c h) (actQ LA' I' hI' h y))
      - -qpair m L1 I I' s hsI hsI' (c (g * h)) (actQ LA' I' hI' (g * h) y)
      + -qpair m L1 I I' s hsI hsI' (c g) (actQ LA' I' hI' g y) =
    qpair m L1 I I' s hsI hsI' (c g) (actQ LA' I' hI' g (c' h))
  rw [hcg, map_neg, ← qpair_equiv m L1 I I' s hsI hsI' hI hI' hm, hc.2 g h, GlobalTheory.TateFin.actQ_mul]
  simp only [map_add, map_sub, LinearMap.add_apply]
  abel

end Gen

section Gen2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (I : Submodule O ↥LA.T) (I' : Submodule O ↥LA'.T) (s : LL)
    (hsI : ∀ t ∈ I, ∀ y ∈ LA'.T, s * m (t : A.V) y ∈ L1.T)
    (hsI' : ∀ x ∈ LA.T, ∀ t ∈ I', s * m x (t : A'.V) ∈ L1.T)
    (hI : StableSub LA I) (hI' : StableSub LA' I')
    (hm : ∀ g x y, m (A.ρ g x) (A'.ρ g y) = ((cycLL PD LL g : LLˣ) : LL) * m x y)
    (hlc' : ∀ y, IsLocallyConstant fun g => actQ LA' I' hI' g y)

def cupH2Level : ↥(quotientCocycles LA' I' hI') →ₗ[O] ↥(quotientCocycles LA I hI) →ₗ[O]
    ReciprocityTheory.Def.H2 (repD L1) (⊤ : Submodule O (LL ⧸ L1.T)) :=
  LinearMap.mk₂ O
    (fun c' c => Submodule.Quotient.mk
      ⟨zq m L1 I I' s hsI hsI' hI' c.1 c'.1, cup_cocycle_mem_Z2 m L1 I I' s hsI hsI' hI hI' hm hlc' c.2 c'.2⟩)
    (fun a b c => by
      rw [← Submodule.Quotient.mk_add]
      congr 1
      apply Subtype.ext
      funext x
      simp [zq, map_add])
    (fun r a c => by
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      apply Subtype.ext
      funext x
      simp [zq, map_smul])
    (fun c' a b => by
      rw [← Submodule.Quotient.mk_add]
      congr 1
      apply Subtype.ext
      funext x
      simp [zq, map_add])
    (fun r c' a => by
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      apply Subtype.ext
      funext x
      simp [zq, map_smul])

include hsI hsI' hm hlc' in

theorem exists_level_pairing {S : Submodule O LL}
    (e : ReciprocityTheory.Def.H2 (repD L1) (⊤ : Submodule O (LL ⧸ L1.T)) ≃ₗ[O] (LL ⧸ S)) :
    ∃ β : QuotientCohomology LA' I' hI' →ₗ[O] QuotientCohomology LA I hI →ₗ[O] (LL ⧸ S),
      ∀ (c : ↥(quotientCocycles LA I hI)) (c' : ↥(quotientCocycles LA' I' hI')),
        β (Submodule.Quotient.mk c') (Submodule.Quotient.mk c) = 0 ↔
          CobO PD L1 (fun x => s * m (Formalism.MainNotions.LocalSituation.liftQ LA I ((c : G → ↥LA.T ⧸ I) x.1))
            (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' I' ((c' : G → ↥LA'.T ⧸ I') x.2)))) := by
  refine ⟨(LinearMap.liftQ₂ _ _ (cupH2Level m L1 I I' s hsI hsI' hI hI' hm hlc') ?_ ?_).compr₂
    e.toLinearMap, fun c c' => ?_⟩
  · intro c' hc'
    refine LinearMap.mem_ker.2 (LinearMap.ext fun c => ?_)
    show (Submodule.Quotient.mk _ : ReciprocityTheory.Def.H2 (repD L1) (⊤ : Submodule O (LL ⧸ L1.T))) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact cup_coboundary_right_mem_B2 m L1 I I' s hsI hsI' hI hI' hm hlc' c.2 hc'
  · intro c hc
    refine LinearMap.mem_ker.2 (LinearMap.ext fun c' => ?_)
    show (Submodule.Quotient.mk _ : ReciprocityTheory.Def.H2 (repD L1) (⊤ : Submodule O (LL ⧸ L1.T))) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact cup_coboundary_left_mem_B2 m L1 I I' s hsI hsI' hI hI' hm hc c'.2
  · show e (Submodule.Quotient.mk ⟨zq m L1 I I' s hsI hsI' hI' c.1 c'.1, _⟩) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
    show zq m L1 I I' s hsI hsI' hI' c.1 c'.1 ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ ↔ _
    unfold CobO
    rw [funext (zq_eq m L1 I I' s hsI hsI' hI' c.1 c'.1)]

omit [TopologicalSpace LL] in

theorem cobO_smul (a : O) {z : G × G → LL} (h : CobO PD L1 z) :
    CobO PD L1 (fun x => algebraMap O LL a * z x) := by
  unfold CobO at *
  have h2 := (ReciprocityTheory.Def.B2 (repD L1) ⊤).smul_mem a h
  convert h2 using 1
  funext x
  rw [Pi.smul_apply, ← Submodule.Quotient.mk_smul, Algebra.smul_def]

end Gen2

theorem exists_level_pow {LL O : Type} [Field LL] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra O LL] [IsFractionRing O LL] {a : O} (ha : a ≠ 0) :
    ∃ (ϖ : O) (n : ℕ) (u : O), Irreducible ϖ ∧ Ideal.span {a} = Ideal.span {ϖ ^ n} ∧
      (algebraMap O LL ϖ)⁻¹ ^ n = algebraMap O LL u * (algebraMap O LL a)⁻¹ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  refine ⟨ϖ, n, u, hϖ, by rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit], ?_⟩
  have hu0 : algebraMap O LL (u : O) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 u.ne_zero
  rw [hu, map_mul, map_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ hu0, one_mul, inv_pow]

section Gen3

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

open Formalism.MainNotions.BlochKatoDuality.Br in

theorem cobO_red [IsTopologicalRing LL] [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
    (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL))
    {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    {m : A.V →ₗ[LL] A'.V →ₗ[LL] LL} (hd : IsDualLat1 PD LA LA' m)
    (I : Submodule O ↥LA.T) (I' : Submodule O ↥LA'.T) (s : LL)
    (hsI : ∀ t ∈ I, ∀ y ∈ LA'.T, s * m (t : A.V) y ∈ L1.T)
    (d : ↥(latticeCocycles LA)) (c' : G → ↥LA'.T ⧸ I')
    (h1 : CobO PD L1 (fun x => s * m (Formalism.MainNotions.LocalSituation.liftQ LA I (redT LA I d x.1))
      (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' I' (c' x.2))))) :
    CobO PD L1 (cupLD LA' m (d : G → A.V) (fun g => (Submodule.Quotient.mk
      (s • Formalism.MainNotions.LocalSituation.liftQ LA' I' (c' g)) : A'.V ⧸ LA'.T))) := by
  refine (cobO_congr PD L1 _ _ fun x => ?_).1 h1
  obtain ⟨g, k⟩ := x
  have hw : Formalism.MainNotions.LocalSituation.liftQ LA' I' (c' k) ∈ LA'.T :=
    (Submodule.Quotient.mk_surjective I' (c' k)).choose.2
  rw [cup_lift PD hd L1 hL1 _ _ g k (d.2.2 g (Set.mem_univ g))
    (s • Formalism.MainNotions.LocalSituation.liftQ LA' I' (c' k)) rfl]
  rw [map_smul, map_smul, smul_eq_mul, Submodule.Quotient.eq, ← mul_sub, ← LinearMap.sub_apply,
    ← map_sub]
  have e0 := (Submodule.Quotient.mk_surjective I (redT LA I d g)).choose_spec
  have e1 := (Submodule.Quotient.eq I).1 (e0.trans
    (rfl : redT LA I d g = Submodule.Quotient.mk (evT LA g d)))
  have h2 := hsI _ e1 _ (LA'.stable g _ hw)
  rw [Submodule.coe_sub] at h2
  exact h2

theorem level_pairing_abstract [IsTopologicalRing LL] [IsDomain O] [IsDiscreteValuationRing O]
    [IsFractionRing O LL]
    (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL))
    {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    {m : A.V →ₗ[LL] A'.V →ₗ[LL] LL} (hd : IsDualLat1 PD LA LA' m)
    (I : Submodule O ↥LA.T) (I' : Submodule O ↥LA'.T) (s : LL)
    (hsI : ∀ t ∈ I, ∀ y ∈ LA'.T, s * m (t : A.V) y ∈ L1.T)
    (hsI' : ∀ x ∈ LA.T, ∀ t ∈ I', s * m x (t : A'.V) ∈ L1.T)
    (hI : StableSub LA I) (hI' : StableSub LA' I')
    (hlc' : ∀ y, IsLocallyConstant fun g => actQ LA' I' hI' g y)
    {S : Submodule O LL}
    (e : ReciprocityTheory.Def.H2 (repD L1) (⊤ : Submodule O (LL ⧸ L1.T)) ≃ₗ[O] (LL ⧸ S))
    (nondeg : ∀ c ∈ quotientCocycles LA I hI, (∀ c' ∈ quotientCocycles LA' I' hI', CobO PD L1 (fun x => s *
        m (Formalism.MainNotions.LocalSituation.liftQ LA I (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' I' (c' x.2))))) →
        c ∈ BQ LA I hI) :
    ∃ β : QuotientCohomology LA' I' hI' →ₗ[O] QuotientCohomology LA I hI →ₗ[O] (LL ⧸ S),
      (∀ c, (∀ y, β y c = 0) → c = 0) ∧
      ∀ (d : ↥(latticeCocycles LA)) (h : redT LA I d ∈ quotientCocycles LA I hI) (c' : ↥(quotientCocycles LA' I' hI')),
        β (Submodule.Quotient.mk c') (Submodule.Quotient.mk ⟨redT LA I d, h⟩) = 0 →
        CobO PD L1 (cupLD LA' m (d : G → A.V) (fun g => (Submodule.Quotient.mk
          (s • Formalism.MainNotions.LocalSituation.liftQ LA' I' ((c' : G → ↥LA'.T ⧸ I') g)) : A'.V ⧸ LA'.T))) := by
  refine (exists_level_pairing m L1 I I' s hsI hsI' hI hI' hd.1.1 hlc' e).elim fun β hβ => ?_
  refine ⟨β, fun c hc => ?_, fun d h c' hb => ?_⟩
  · refine (Submodule.Quotient.mk_surjective _ c).elim fun c₀ hc₀ => ?_
    subst hc₀
    exact (Submodule.Quotient.mk_eq_zero _).2
      (nondeg c₀.1 c₀.2 fun c' hc' => (hβ c₀ ⟨c', hc'⟩).1 (hc _))
  · exact cobO_red L1 hL1 hd I I' s hsI d c'.1 ((hβ ⟨_, h⟩ c').1 hb)

theorem nondeg_transfer
    (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (J J' : Ideal O) (hJJ : J = J') (s t : LL) (u : O)
    (hst : t = algebraMap O LL u * s)
    (hnd : ∀ (hI : StableSub LA (J' • ⊤ : Submodule O ↥LA.T))
      (hI' : StableSub LA' (J' • ⊤ : Submodule O ↥LA'.T)),
      ∀ c ∈ quotientCocycles LA _ hI, (∀ c' ∈ quotientCocycles LA' _ hI', CobO PD L1 (fun x => t *
        m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' x.2))))) →
        c ∈ BQ LA _ hI)
    (hI : StableSub LA (J • ⊤ : Submodule O ↥LA.T))
    (hI' : StableSub LA' (J • ⊤ : Submodule O ↥LA'.T)) :
    ∀ c ∈ quotientCocycles LA _ hI, (∀ c' ∈ quotientCocycles LA' _ hI', CobO PD L1 (fun x => s *
        m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' x.2))))) →
        c ∈ BQ LA _ hI := by
  subst hJJ
  intro c hc H
  refine hnd hI hI' c hc fun c' hc' => ?_
  have h3 := cobO_smul L1 u (H c' hc')
  simp only [hst, mul_assoc]
  simpa only [mul_assoc] using h3

theorem level_pairing_of (hG : GoodO (Qp := Qp) LL O)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL))
    (A A' : GRep G Qp LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ)
    (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (hd : IsDualLat1 PD LA LA' m)
    (e0 : Nonempty (ReciprocityTheory.Def.H2 (repD L1) (⊤ : Submodule O (LL ⧸ L1.T)) ≃ₗ[O] (LL ⧸ L1.T)))
    (hnd : ∀ (ϖ : O), Irreducible ϖ → ∀ (n : ℕ)
      (hI : StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))
      (hI' : StableSub LA' (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T)),
      ∀ c ∈ quotientCocycles LA _ hI, (∀ c' ∈ quotientCocycles LA' _ hI', CobO PD L1 (fun x => (algebraMap O LL ϖ)⁻¹ ^ n *
        m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c x.1)) (A'.ρ x.1 (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' x.2))))) →
        c ∈ BQ LA _ hI)
    (l : ℕ) (hlL : ((l : ℕ) : LL) ≠ 0) (r : ℕ)
    (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T))
    (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) :
    ∃ β : QuotientCohomology LA' _ hI' →ₗ[O] QuotientCohomology LA _ hI →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)),
      (∀ c, (∀ y, β y c = 0) → c = 0) ∧
      ∀ (d : ↥(latticeCocycles LA)) (h : redT LA _ d ∈ quotientCocycles LA _ hI) (c' : ↥(quotientCocycles LA' _ hI')),
        β (Submodule.Quotient.mk c') (Submodule.Quotient.mk ⟨redT LA _ d, h⟩) = 0 →
        CobO PD L1 (cupLD LA' m (d : G → A.V) (fun g => (Submodule.Quotient.mk
          ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : G → ↥LA'.T ⧸
            (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T))) := by
  obtain ⟨⟨hO, hDVR, hFr⟩, -, -, htr, hopen⟩ := hG
  haveI := hO
  haveI := hDVR
  haveI := hFr
  haveI := htr
  have hlm : algebraMap O LL ((l : ℕ) : O) = ((l : ℕ) : LL) := map_natCast _ _
  have hl0 : ((l : ℕ) : O) ≠ 0 := fun h => hlL (by rw [← hlm, h, map_zero])
  have hsinv : (algebraMap O LL ((l : ℕ) : O))⁻¹ ^ r = (((l : ℕ) : LL) ^ r)⁻¹ := by
    rw [hlm, inv_pow]
  have hTT : ∀ x ∈ LA.T, ∀ y ∈ LA'.T, m x y ∈ L1.T := fun x hx y hy => by
    obtain ⟨a, ha⟩ := (hd.2 y).1 hy x hx
    rw [hL1, ha]
    exact ⟨a, rfl⟩
  have hsI : ∀ t ∈ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T), ∀ y ∈ LA'.T,
      (((l : ℕ) : LL) ^ r)⁻¹ * m (t : A.V) y ∈ L1.T := by
    intro t ht y hy
    have h1 := (GlobalTheory.TateFin.mem_pow_smul_top (LL := LL) LA.T hl0 r t).1 ht
    rw [hsinv] at h1
    have h2 := hTT _ h1 y hy
    rwa [map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  have hsI' : ∀ x ∈ LA.T, ∀ t ∈ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T),
      (((l : ℕ) : LL) ^ r)⁻¹ * m x (t : A'.V) ∈ L1.T := by
    intro x hx t ht
    have h1 := (GlobalTheory.TateFin.mem_pow_smul_top (LL := LL) LA'.T hl0 r t).1 ht
    rw [hsinv] at h1
    have h2 := hTT x hx _ h1
    rwa [map_smul, smul_eq_mul] at h2
  have hlc' := fun y => GlobalTheory.TateFin.actQ_locallyConstant hopen A' LA' hl0 r hI' y
  refine (exists_level_pow (LL := LL) (pow_ne_zero r hl0)).elim fun ϖ h1 => h1.elim fun n h2 =>
    h2.elim fun u h3 => ?_
  have hsu := h3.2.2
  rw [map_pow, hlm] at hsu
  exact level_pairing_abstract L1 hL1 hd _ _ _ hsI hsI' hI hI' hlc'
    (e0.some.trans (Submodule.quotEquivOfEq _ _ hL1))
    (nondeg_transfer L1 m _ _ h3.2.1 _ _ u hsu (hnd ϖ h3.1 n) hI hI')

end Gen3

theorem tate_pairing_level : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), ∃ β : QuotientCohomology LA' _ hI' →ₗ[O] QuotientCohomology LA _ hI →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)), (∀ c, (∀ y, β y c = 0) → c = 0) ∧ ∀ (d : ↥(latticeCocycles LA)) (h : redT LA _ d ∈ quotientCocycles LA _ hI) (c' : ↥(quotientCocycles LA' _ hI')), β (Submodule.Quotient.mk c') (Submodule.Quotient.mk ⟨redT LA _ d, h⟩) = 0 → CobO (P.PD K) L1 (cupLD LA' m (d : ↥(GK K) → A.V) (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T))) := by
  intro hT l _ P K LL _ _ _ O _ _ hG L1 hL1 A A' LA LA' m hd r hI hI'
  have hlQ : ((l : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlL : ((l : ℕ) : LL) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] LL)]
    exact (map_ne_zero _).2 hlQ
  exact level_pairing_of hG L1 hL1 A A' LA LA' m hd
    (GlobalTheory.TateTop.tateH2_of_duality_loc hT l P K LL O hG L1 hL1)
    (fun ϖ hϖ n hJ hJ' => (GlobalTheory.TateFin.tate_pairing_nondegenerate hT l P K LL O hG L1 hL1 A A' LA LA'
      m hd ϖ hϖ n hJ hJ').1) l hlL r hI hI'

end GlobalTheory.TateLevel
