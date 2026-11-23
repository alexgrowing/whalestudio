import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeVariant
import Formalism.SharpRestriction.LevelLetterCocycles.CurveIdealTorusProperties
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
import Formalism.PadicSubsetSums.StableGradedCounts.TWReuse
import Formalism.PadicSubsetSums.StableGradedCounts.TWHeckeDetFactors
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleySignature
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonEigenvectorBis
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfMonicRoot

noncomputable section

namespace Formalism.MainNotions.LatticeVariant

open Formalism.IrreducibleCountingLemmas.TW

private theorem lb_ofFn (lb : (m : ℕ) → (Fin m → ℕ) → ℕ) (n : ℕ) (f : Fin n → ℕ) :
    lb (List.ofFn f).length (fun t => (List.ofFn f).get t) = lb n f := by
  have key : ∀ (m : ℕ) (h : m = n) (g : Fin m → ℕ), (∀ t, g t = f (Fin.cast h t)) → lb m g = lb n f := by
    intro m h g hg
    subst h
    congr 1
    funext t
    exact hg t
  refine key _ (List.length_ofFn) _ ?_
  intro t
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  rfl

theorem subgroup_lemma : PowerSeriesPrimePowerSubstNeZero := by
  intro k _ l hl ρ F hF lb
  obtain ⟨e, he, hlb, hne⟩ := substitution_SUB k l ρ 1 (fun _ => F)
    (fun L => lb L.length (fun t => L.get t)) hl.two_le (fun _ => hF)
  refine ⟨e, he, ?_, hne 0⟩
  intro m
  have := hlb m
  rw [lb_ofFn lb] at this
  exact this

theorem subgroup_admissible_holds (D : Formalism.BasicNotions.D7) : adm3 D := subgroup_lemma

theorem low_degree_lemma : PowerSeriesProductNotMemPowerIdeal := by
  intro R _ _ _ Dd g m0 n hD hg hn
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hord : (PowerSeries.map (IsLocalRing.residue R) Dd).order ≤ (m0 : ℕ∞) := by
    obtain ⟨a, ha, hc⟩ := hD
    refine le_trans (PowerSeries.order_le a ?_) (by exact_mod_cast ha)
    rw [PowerSeries.coeff_map]
    intro h0
    exact hc ((IsLocalRing.residue_eq_zero_iff _).1 h0)
  have hg0 : PowerSeries.constantCoeff g ∉ Ideal.span {ϖ ^ n} := by
    rw [Ideal.mem_span_singleton, ← IsDiscreteValuationRing.addVal_le_iff_dvd,
      IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    have htop : IsDiscreteValuationRing.addVal R (PowerSeries.constantCoeff g) ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hg
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 htop
    rw [← hc] at hn ⊢
    simp only [ENat.toNat_natCast] at hn
    subst hn
    simp only [nsmul_eq_mul, mul_one, not_le]
    exact_mod_cast Nat.lt_succ_self c
  have := low_power_series_LOW R ϖ n m0 Dd g hϖ hord hg0
  rw [hmax, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, ← Ideal.span_union]
  rw [Set.singleton_union]
  exact this

theorem low_degree_admissible_holds (D : Formalism.BasicNotions.D7) : ArchimedeanSignatureMatching D := low_degree_lemma

section GT

open Formalism.CyclotomicNorms (vl)
open Formalism.MainNotions.BlochKatoReduction.Gen (nval)

theorem vl_eq_nval {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [NormedField L]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (φ : R →+* L) (hφ : ∀ a, ‖φ a‖ ≤ 1) (hl : ‖(ℓ : L)‖ = (ℓ : ℝ)⁻¹) :
    0 < (IsDiscreteValuationRing.addVal R (ℓ : R)).toNat ∧
    ∀ x : R, x ≠ 0 → φ x ≠ 0 ∧ vl ℓ (φ x) = nval R ℓ x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hunit : ∀ u : Rˣ, ‖φ u‖ = 1 := by
    intro u
    refine le_antisymm (hφ _) ?_
    have h1 : ‖φ u‖ * ‖φ ((u⁻¹ : Rˣ) : R)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    nlinarith [hφ ((u⁻¹ : Rˣ) : R), norm_nonneg (φ u), norm_nonneg (φ ((u⁻¹ : Rˣ) : R))]
  have hl0 : (ℓ : R) ≠ 0 := by
    intro h0
    have : (ℓ : L) = 0 := by rw [← map_natCast φ, h0, map_zero]
    rw [this, norm_zero] at hl
    exact absurd hl (by positivity : (0 : ℝ) < (ℓ : ℝ)⁻¹).ne
  have hrep : ∀ x : R, x ≠ 0 → ∃ n : ℕ, IsDiscreteValuationRing.addVal R x = n ∧ ‖φ x‖ = ‖φ ϖ‖ ^ n := by
    intro x hx
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hϖ
    refine ⟨n, ?_, ?_⟩
    · apply IsDiscreteValuationRing.addVal_def x u⁻¹ hϖ n
      rw [← hu]; simp [mul_comm]
    · rw [← norm_pow, ← map_pow, ← hu, map_mul, norm_mul, hunit, mul_one]
  obtain ⟨m, hm, hmn⟩ := hrep _ hl0
  rw [map_natCast, hl] at hmn
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hmn
    have : (ℓ : ℝ) = 1 := by field_simp at hmn; linarith
    linarith
  have ht : 0 < ‖φ ϖ‖ := by
    rcases (norm_nonneg (φ ϖ)).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_pow hm0] at hmn
      exact absurd hmn (by positivity : (0 : ℝ) < (ℓ : ℝ)⁻¹).ne'
  have hlog : (m : ℝ) * Real.logb ℓ ‖φ ϖ‖ = -1 := by
    rw [← Real.logb_pow, ← hmn, Real.logb_inv, Real.logb_self_eq_one hℓ1]
  refine ⟨by rw [hm]; simpa using Nat.pos_of_ne_zero hm0, ?_⟩
  intro x hx
  obtain ⟨n, hn, hnn⟩ := hrep x hx
  refine ⟨?_, ?_⟩
  · rw [← norm_pos_iff, hnn]; positivity
  · unfold vl nval
    rw [hnn, hn, hm, Real.logb_pow]
    simp only [ENat.toNat_natCast]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    field_simp
    nlinarith [hlog]

theorem norm_natCast_self_padicComplex (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [map_natCast, PadicComplex.coe_natCast, Padic.norm_p] at h
  exact h

end GT

section Cons

open Formalism.MainNotions.IntegralHeckeForms (IsLatIn)
open scoped TensorProduct

theorem isLatIn_spanK {O K V : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] {N : Submodule O V} (hN : N.FG) :
    IsLatIn N ((Submodule.span K (N : Set V)).restrictScalars O) :=
  _root_.UpperTheory.Reformulated.B.CayleySignature.isLatIn_spanK hN

variable {D : Formalism.BasicNotions.D7} {N : Formalism.BasicNotions.NData D.R D.host D.what₂}
  {X : Formalism.BasicNotions.NTw D.R D.host D.what₂ D.LL0 N} {Y : Formalism.BasicNotions.NExp D.R D.host D.what₂ D.LL0 N X}

theorem IdxM_of {i : X.Tw} {F : RFam Y i} {j : ℕ} {b : Bool} (hR : RHyp Y i F j b) {k : ℕ}
    {Q : Finset (Formalism.BasicNotions.PlE D.host)} {ψ : Formalism.ConjugateSelfDual.G D.host.E N.Om →* (X.Ok i k)ˣ} {e : ℝ}
    (hlat : IsLatIn (F.ThPsi j b k Q ψ) (F.VKk j b k))
    (h : Formalism.MainNotions.IntegralHeckeForms.sIdx (X.l i) ((F.B j b).baseChange (X.Ok i k)) (F.ThPsi j b k Q ψ) ≤
      Formalism.MainNotions.IntegralHeckeForms.sIdx (X.l i) (F.B j b) (F.Th j b) + e) :
    IdxM Y i F j b k Q ψ e := by
  intro O' _ _ _ _ _ _ hinj hfin M hM
  have hB : IsLatIn (F.B j b) ((F.VK j b).restrictScalars (X.O i)) := isLatIn_spanK hR.1
  have hTfg : (F.Th j b).FG := by
    rw [← hR.2.2.2.2.2.2.1]
    exact Submodule.fg_span ((F.S j b).finite_toSet.image _)
  have hT : IsLatIn (F.Th j b) ((F.VK j b).restrictScalars (X.O i)) := by
    rw [← hR.2.2.2.2.2.2.2.1]
    exact isLatIn_spanK hTfg
  have := X.Ok_fin i k
  exact Formalism.MainNotions.IntegralHeckeForms.Idx.transfer (X.Ok_inj i k) hinj (X.l i) hB hT hlat e h hM

theorem partBM_of_partBR {i : X.Tw} {F : RFam Y i}
    (hR : ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, RHyp Y i F j b) {Q : Finset (Formalism.BasicNotions.PlE D.host)} {k' : ℕ}
    {ψ' : X.RCG i Q →* (X.Ok i k')ˣ} {eps' : ℝ} (h : partBR Y i F Q k' ψ' eps') :
    partBM Y i F Q k' ψ' eps' := by
  obtain ⟨epsB, h0, hs, hb⟩ := h
  exact ⟨epsB, h0, hs, fun j hj b => ⟨(hb j hj b).1, IdxM_of (hR j hj b) (hb j hj b).1 (hb j hj b).2⟩⟩

theorem arbitrary_lattice_of_twist_theorem (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ)
    (h : aux₃ D bkP N0) : ArbitraryLatticeAtNonzeroIndexPlaces D bkP N0 := by
  intro i hi hS eps' he F hF A0
  obtain ⟨Q, k', ψ', h1, h2, h3, h4, h5, h6⟩ := h i hi hS eps' he F hF A0
  exact ⟨Q, k', ψ', h1, h2, h3, partBM_of_partBR hF h4, h5, h6⟩

theorem arbitrary_lattice_of_statement (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (h : Stmt D bkP) : ArbitraryLatticeOfAdmissible D bkP :=
  fun N0 hA => arbitrary_lattice_of_twist_theorem D bkP N0 (h N0 hA)

end Cons

section Open

open Formalism.MainNotions.BlochKatoReduction.Gen (SetHyp PsiOk partAT partC partD)

variable (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ)

def AdmR : Prop :=
  adm1 D bkP N0 ∧ adm2 D bkP N0 ∧ adm6 D ∧ adm7 D ∧ adm8 D N0 ∧ adm9 D ∧ adm10 D ∧ adm11 D ∧ adm12 D ∧
    adm13 D

def CurveIdealTorusProperties : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → SetHyp (Formalism.MainNotions.BlochKatoReduction.pin bkP) i → ∀ eps' : ℝ, 0 < eps' → ∀ F : RFam D.nexp i,
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, RHyp D.nexp i F j b) →
    ∀ A0 : Finset (Formalism.BasicNotions.PlE D.host),
    ∃ (Q : Finset (Formalism.BasicNotions.PlE D.host)) (k' : ℕ) (ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ),
      PsiOk i A0 Q k' ψ' ∧ partAT (Formalism.MainNotions.BlochKatoReduction.pin bkP) i Q k' ψ' eps' ∧
      partBR D.nexp i F Q k' ψ' eps' ∧ partC N0 i Q k' ψ' eps' ∧ partD i Q k' ψ' eps'

theorem conclusion_iff_withoutFirstConjunct : aux₃ D bkP N0 ↔ CurveIdealTorusProperties D bkP N0 := by
  constructor
  · intro h i hi hS eps' he F hF A0
    obtain ⟨Q, k', ψ', h1, _, h3, h4, h5, h6⟩ := h i hi hS eps' he F hF A0
    exact ⟨Q, k', ψ', h1, h3, h4, h5, h6⟩
  · intro h i hi hS eps' he F hF A0
    obtain ⟨Q, k', ψ', h1, h3, h4, h5, h6⟩ := h i hi hS eps' he F hF A0
    exact ⟨Q, k', ψ', h1, Formalism.MainNotions.BlochKatoReduction.Gen.partA_of_partAT (Formalism.MainNotions.BlochKatoReduction.pin bkP) i Q k' ψ' eps' h3, h3, h4, h5, h6⟩

end Open

section Lattice

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (nval)
open scoped TensorProduct

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

def FrobEx (N : NData D.R D.host D.what₂) : Prop :=
  ∀ P : PlE D.host, ∃ σ : G D.host.E N.Om, IsFrob (N.plOm.1 P) (normV P) σ

def AdmQ (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : Prop :=
  (∀ P ∈ Q, IsSplitPl D.host P) ∧ Disjoint Q (X.S0 i) ∧ ConjCl Q ∧ DelOn Y i Q M ∧ Formalism.MainNotions.IntegralHeckeForms.ClsQ (D := D) Q

structure Pack (i : X.Tw) (j : ℕ) (b : Bool) where
  B : Submodule (X.O i) (Y.Fm i j b)
  A : Module.End (X.O i) (Y.Fm i j b)
  S : Finset (Y.Dat i j b)
  c : ℕ
  fg : B.FG
  hkB : ∀ k P, HkIdx i k P → B.map (hkO Y i j b k P) ≤ B
  comm : ∀ k P, HkIdx i k P → A ∘ₗ hkO Y i j b k P = hkO Y i j b k P ∘ₗ A
  li : LinearIndependent (X.O i) (fun a : ↥S => A (Y.th i j b a))
  spn : Submodule.span (FractionRing (X.O i)) ((fun a => A (Y.th i j b a)) '' ↑S) =
    Submodule.span (FractionRing (X.O i)) (B : Set (Y.Fm i j b))
  t2 : ∀ Q M, AdmQ Y i Q M → ∀ a ∈ S, Disjoint Q (Y.lev i j b a) →
    ((X.l i : X.O i) ^ c) • (A.rTensor (LamO X i Q M)) (Y.thU i j b Q M a) ∈
      LinearMap.range (B.subtype.rTensor (LamO X i Q M))
  t3 : T3 Y i j b B

variable {Y} {i : X.Tw} {j : ℕ} {b : Bool} (p : Pack Y i j b)

def Pack.Th : Submodule (X.O i) (Y.Fm i j b) :=
  Submodule.span (X.O i) ((fun a => p.A (Y.th i j b a)) '' ↑p.S)

def Pack.y (Q : Finset (PlE D.host)) (M k : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (a : Y.Dat i j b) :
    X.Ok i k ⊗[X.O i] Y.Fm i j b :=
  (p.A.baseChange (X.Ok i k)) (specU Y i j b Q M k χ (Y.thU i j b Q M a))

def Pack.Yl (Q : Finset (PlE D.host)) (M k : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) :
    Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) :=
  Submodule.span (X.Ok i k) (p.y Q M k χ '' ↑p.S)

def Pack.VKk (k : ℕ) : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) :=
  ((Submodule.span (FractionRing (X.O i)) (p.B : Set (Y.Fm i j b))).restrictScalars (X.O i)).baseChange
    (X.Ok i k)

def Pack.v : ℝ := sIdx (X.l i) p.B p.Th + (p.c : ℝ) * p.S.card

def Pack.Main : Prop :=
  ∃ f : ∀ Q M, LamO X i Q M, 0 ≤ p.v ∧
    (∀ A0 : Finset (PlE D.host), (∀ a ∈ p.S, Y.lev i j b a ⊆ A0) → Good Y i A0 f p.v) ∧
    ∀ (Q : Finset (PlE D.host)) (M k : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
      evA i Q M k χ (f Q M) ≠ 0 →
      IsLatIn (p.Yl Q M k χ) (p.VKk k) ∧
      sIdx (X.l i) (p.B.baseChange (X.Ok i k)) (p.Yl Q M k χ) =
        nval (X.Ok i k) (X.l i) (evA i Q M k χ (f Q M)) - (p.c : ℝ) * p.S.card

end Lattice

section Asm0

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (nval)
open scoped TensorProduct

theorem list_prod_congr {R ι : Type} [CommRing R] (I : Ideal R) (l : List ι) (f g : ι → R)
    (h : ∀ x ∈ l, f x - g x ∈ I) : (l.map f).prod - (l.map g).prod ∈ I := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons]
    have h1 := h x (List.mem_cons_self)
    have h2 := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    have : f x * (l.map f).prod - g x * (l.map g).prod =
        (f x - g x) * (l.map f).prod + g x * ((l.map f).prod - (l.map g).prod) := by ring
    rw [this]
    exact I.add_mem (I.mul_mem_right _ h1) (I.mul_mem_left _ h2)

theorem nval_nonneg (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ) (x : R) :
    0 ≤ nval R l x := by
  unfold nval
  positivity

theorem nval_unit_mul (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ) {u : R}
    (hu : IsUnit u) (x : R) : nval R l (u * x) = nval R l x := by
  unfold nval
  have h0 : IsDiscreteValuationRing.addVal R u = 0 := by
    have := IsDiscreteValuationRing.addVal_eq_zero_of_unit hu.unit
    simpa using this
  rw [IsDiscreteValuationRing.addVal_mul, h0, zero_add]

theorem nval_pow_self (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ)
    (h : 0 < (IsDiscreteValuationRing.addVal R (l : R)).toNat) (c : ℕ) :
    nval R l ((l : R) ^ c) = c := by
  unfold nval
  have htop : IsDiscreteValuationRing.addVal R (l : R) ≠ ⊤ := by
    intro h0; rw [h0] at h; simp at h
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 htop
  rw [← ha, ENat.toNat_natCast] at h
  rw [IsDiscreteValuationRing.addVal_pow, ← ha]
  have : (c • (a : ℕ∞)).toNat = c * a := by
    rw [nsmul_eq_mul]; exact_mod_cast ENat.toNat_natCast (c * a)
  rw [this, ENat.toNat_natCast]
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast h.ne'
  push_cast
  field_simp

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}

theorem admissible_empty_places (i : X.Tw) (M : ℕ) : AdmQ Y i ∅ M :=
  ⟨by simp, by simp, fun P hP => by simp at hP, fun P hP => by simp at hP, fun P hP => by simp at hP⟩

theorem specU_eq (i : X.Tw) (j : ℕ) (b : Bool) (Q : Finset (PlE D.host)) (M k : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (w : Y.Fm i j b ⊗[X.O i] LamO X i Q M) :
    specU Y i j b Q M k χ w =
      (TensorProduct.comm (X.O i) (Y.Fm i j b) (X.Ok i k))
        ((evA i Q M k χ).toLinearMap.lTensor (Y.Fm i j b) w) := rfl

theorem baseChange_comm {O Fm R' : Type} [CommRing O] [CommRing R'] [Algebra O R'] [AddCommGroup Fm]
    [Module O Fm] (A : Module.End O Fm) (x : Fm ⊗[O] R') :
    (A.baseChange R') (TensorProduct.comm O Fm R' x) = TensorProduct.comm O Fm R' (A.rTensor R' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rTensor_lTensor_comm {O Fm L L' : Type} [CommRing O] [AddCommGroup Fm] [Module O Fm]
    [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (A : Module.End O Fm) (φ : L →ₗ[O] L')
    (x : Fm ⊗[O] L) : φ.lTensor Fm (A.rTensor L x) = A.rTensor L' (φ.lTensor Fm x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rTensor_PqTw (i : X.Tw) (j : ℕ) (b : Bool) (Q : Finset (PlE D.host)) (M : ℕ) (P : PlE D.host)
    (γ : DelQM D.host (X.l i) Q M) (A : Module.End (X.O i) (Y.Fm i j b))
    (hA : ∀ k ∈ Finset.Icc 1 D.R.r, A ∘ₗ hkO Y i j b k P = hkO Y i j b k P ∘ₗ A)
    (x : Y.Fm i j b ⊗[X.O i] LamO X i Q M) :
    A.rTensor _ (PqTw Y i j b Q M P γ x) = PqTw Y i j b Q M P γ (A.rTensor _ x) := by
  unfold PqTw
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add,
    map_sum, map_smul]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f a =>
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul]
    congr 1
    exact LinearMap.congr_fun (hA k hk) f
  | add x y hx hy => simp only [map_add, hx, hy]

end Asm0

section Chain

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO)
open scoped TensorProduct

theorem conj_conj (D : Formalism.BasicNotions.D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  have h := D.host.conjE_apply D.host.φ₀
  show D.host.φ₀ (D.host.conj
    (D.host.conj x)) = _
  rw [h, h]
  simp

variable {D : Formalism.BasicNotions.D7}

theorem IsConjPl.symm' {P P' : PlE D.host} (h : IsConjPl D.host P P') : IsConjPl D.host P' P := by
  intro x y hxy
  have : (x : D.host.E) = D.host.conj (y : D.host.E) := by rw [hxy, conj_conj]
  exact (h y x this).symm

theorem exists_conjPl (P : PlE D.host) : ∃ P' : PlE D.host, IsConjPl D.host P P' := by
  let e : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
  have he : ∀ x : 𝓞 D.host.E, ((e x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    intro x
    rw [RingOfIntegers.mapRingEquiv_apply]; rfl
  have := P.isPrime
  refine ⟨⟨P.asIdeal.comap (e.symm : 𝓞 D.host.E →+* 𝓞 D.host.E), Ideal.comap_isPrime _ _, ?_⟩, ?_⟩
  · intro hbot
    apply P.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have h1 : e x ∈ P.asIdeal.comap (e.symm : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
      rw [Ideal.mem_comap]
      simpa using hx
    rw [hbot, Ideal.mem_bot] at h1
    rw [Ideal.mem_bot]
    exact (map_eq_zero_iff e e.injective).1 h1
  · intro x y hxy
    have hy : y = e x := by
      apply RingOfIntegers.ext
      rw [hxy, he]
    subst hy
    show x ∈ P.asIdeal ↔ e.symm (e x) ∈ P.asIdeal
    rw [RingEquiv.symm_apply_apply]

theorem ne_of_split {P Pb : PlE D.host} (hP : IsSplitPl D.host P) (h : IsConjPl D.host P Pb) : P ≠ Pb := by
  rintro rfl
  obtain ⟨x, hx, hy⟩ := hP
  obtain ⟨y, hxy⟩ := Formalism.MainNotions.ExistsIdealDenominator.exists_conj' D x
  exact hy y hxy ((h x y hxy).1 hx)

theorem IsConjPl.inj' {P P' P'' : PlE D.host} (h : IsConjPl D.host P P') (h' : IsConjPl D.host P'' P') :
    P = P'' :=
  Formalism.MainNotions.ExistsIdealDenominator.ConjPl.inj (D := D) h h'

variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem projA_single (i : X.Tw) {Q' Q : Finset (PlE D.host)} (h : Q' ⊆ Q) (M : ℕ)
    (γ : DelQM D.host (X.l i) Q M) (c : X.O i) :
    projA i h M (AddMonoidAlgebra.single γ c) = AddMonoidAlgebra.single (resD (X.l i) h M γ) c := by
  unfold projA
  rw [AddMonoidAlgebra.mapDomainAlgHom_apply]
  exact AddMonoidAlgebra.mapDomain_single

theorem projA_grp (i : X.Tw) {Q' Q : Finset (PlE D.host)} (h : Q' ⊆ Q) (M : ℕ)
    (γ : DelQM D.host (X.l i) Q M) : projA i h M (grp i Q M γ) = grp i Q' M (resD (X.l i) h M γ) :=
  projA_single i h M γ 1

theorem projA_comp (i : X.Tw) {Q'' Q' Q : Finset (PlE D.host)} (h1 : Q'' ⊆ Q') (h2 : Q' ⊆ Q) (M : ℕ) :
    (projA i h1 M).comp (projA i h2 M) = projA i (h1.trans h2) M := by
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro γ
  rw [AlgHom.comp_apply, projA_single, projA_single, projA_single]
  rfl

theorem projA_refl (i : X.Tw) {Q : Finset (PlE D.host)} (h : Q ⊆ Q) (M : ℕ) :
    projA i h M = AlgHom.id (X.O i) (LamO X i Q M) := by
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro γ
  rw [projA_single]
  rfl

theorem grp_nsmul (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) (γ : DelQM D.host (X.l i) Q M) (k : ℕ) :
    grp i Q M (k • γ) = grp i Q M γ ^ k := by
  unfold grp
  rw [AddMonoidAlgebra.single_pow, one_pow]

theorem grp_mul_neg (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) (γ : DelQM D.host (X.l i) Q M) :
    grp i Q M γ * grp i Q M (-γ) = 1 := by
  unfold grp
  rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul]
  rfl

theorem augA_grp (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) (γ : DelQM D.host (X.l i) Q M) :
    augA i Q M (grp i Q M γ) = 1 := by
  unfold augA grp
  rw [AddMonoidAlgebra.lift_single]
  simp

theorem augA_comp (i : X.Tw) {Q' Q : Finset (PlE D.host)} (h : Q' ⊆ Q) (M : ℕ) :
    augA i Q M = (augA i Q' M).comp (projA i h M) := by
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro γ
  rw [AlgHom.comp_apply, projA_single]
  exact (augA_grp i Q M γ).trans (augA_grp i Q' M _).symm

variable (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem lTensor_projA_comp (i : X.Tw) (j : ℕ) (b : Bool) {Q'' Q' Q : Finset (PlE D.host)} (h1 : Q'' ⊆ Q')
    (h2 : Q' ⊆ Q) (h3 : Q'' ⊆ Q) (M : ℕ) (w : Y.Fm i j b ⊗[X.O i] LamO X i Q M) :
    (projA i h1 M).toLinearMap.lTensor (Y.Fm i j b) ((projA i h2 M).toLinearMap.lTensor (Y.Fm i j b) w) =
      (projA i h3 M).toLinearMap.lTensor (Y.Fm i j b) w := by
  rw [← LinearMap.lTensor_comp_apply]
  congr 2
  rw [← projA_comp i h1 h2 M]
  rfl

theorem proj_PqTw (i : X.Tw) (j : ℕ) (b : Bool) {Q' Q : Finset (PlE D.host)} (h : Q' ⊆ Q) (M : ℕ)
    (P : PlE D.host) (γ : DelQM D.host (X.l i) Q M) (w : Y.Fm i j b ⊗[X.O i] LamO X i Q M) :
    (projA i h M).toLinearMap.lTensor (Y.Fm i j b) (PqTw Y i j b Q M P γ w) =
      PqTw Y i j b Q' M P (resD (X.l i) h M γ) ((projA i h M).toLinearMap.lTensor (Y.Fm i j b) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x lam =>
    unfold PqTw
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      TensorProduct.map_tmul, LinearMap.mulLeft_apply, map_add, map_sum, map_smul,
      LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_mul, projA_grp, map_nsmul]

variable {Y}

theorem AdmQ.sub (h12 : AugmentationCompatibility Y) {i : X.Tw} {M : ℕ} {Q' Q : Finset (PlE D.host)} (hi : X.NonzeroIndexPlace i) (hs : Q' ⊆ Q)
    (hQ : AdmQ Y i Q M) (hQ' : ConjCl Q') : AdmQ Y i Q' M := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hQ
  refine ⟨fun P hP => h1 P (hs hP), Finset.disjoint_of_subset_left hs h2, hQ', ?_, fun P hP => h5 P (hs hP)⟩
  intro P hP A' hA'
  obtain ⟨σ, hσ, hv⟩ := h4 P (hs hP) A' hA'
  refine ⟨σ, hσ, ?_⟩
  rw [← (h12 i hi M).1 Q' Q hs h3 hQ' h4 σ]
  exact hv

open Classical in
theorem quantumMinor_row_removal_chain (hF : FrobEx N) (h12 : AugmentationCompatibility Y) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (M : ℕ) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool)
    (Q'' : Finset (PlE D.host)) (hQ'' : ConjCl Q'') :
    ∀ (n : ℕ) (Q : Finset (PlE D.host)) (hs : Q'' ⊆ Q), AdmQ Y i Q M → (Q \ Q'').card = n →
    ∃ ops : List (PlE D.host × ℤ × G D.host.E N.Om), 2 * ops.length = n ∧
      (∀ o ∈ ops, o.1 ∈ Q \ Q'' ∧ (o.2.1 = 1 ∨ o.2.1 = -1) ∧ IsFrob (N.plOm.1 o.1) (normV o.1) o.2.2) ∧
      ∀ a : Y.Dat i j b, Disjoint Q (Y.lev i j b a) →
        (projA i hs M).toLinearMap.lTensor (Y.Fm i j b) (Y.thU i j b Q M a) =
          (ops.map fun o => PqTw Y i j b Q'' M o.1
            (o.2.1 • Multiplicative.toAdd (Y.delU i Q'' M o.2.2))).prod (Y.thU i j b Q'' M a) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q hs hQ hn
  rcases (Q \ Q'').eq_empty_or_nonempty with hem | ⟨P, hP⟩
  · have hQQ : Q = Q'' := Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.1 hem) hs
    subst hQQ
    refine ⟨[], ?_, ?_, ?_⟩
    · rw [← hn, hem]; rfl
    · intro o ho; simp at ho
    · intro a _
      rw [projA_refl]
      simp
  · obtain ⟨hPQ, hPQ''⟩ := Finset.mem_sdiff.1 hP
    obtain ⟨Pb, hc⟩ := exists_conjPl P
    have hne : P ≠ Pb := ne_of_split (hQ.1 P hPQ) hc
    have hPbQ : Pb ∈ Q := hQ.2.2.1 P hPQ Pb hc
    have hPbQ'' : Pb ∉ Q'' := fun h => hPQ'' (hQ'' Pb h P (IsConjPl.symm' hc))
    set Q1 := (Q.erase P).erase Pb with hQ1
    have hs2 : Q1 ⊆ Q := (Finset.erase_subset Pb (Q.erase P)).trans (Finset.erase_subset P Q)
    have hs1 : Q'' ⊆ Q1 := by
      intro R hR
      rw [hQ1, Finset.mem_erase, Finset.mem_erase]
      exact ⟨fun h => hPbQ'' (h ▸ hR), fun h => hPQ'' (h ▸ hR), hs hR⟩
    have hcQ1 : ConjCl Q1 := by
      intro R hR R' hRR'
      rw [hQ1, Finset.mem_erase, Finset.mem_erase] at hR ⊢
      refine ⟨?_, ?_, hQ.2.2.1 R hR.2.2 R' hRR'⟩
      · rintro rfl
        exact hR.2.1 (IsConjPl.inj' hRR' hc)
      · rintro rfl
        exact hR.1 (IsConjPl.inj' hRR' (IsConjPl.symm' hc))
    have hA1 : AdmQ Y i Q1 M := AdmQ.sub h12 hi hs2 hQ hcQ1
    have hcard : (Q1 \ Q'').card + 2 = n := by
      rw [hQ1, Finset.erase_sdiff_comm, Finset.erase_sdiff_comm, Finset.card_erase_of_mem,
        Finset.card_erase_of_mem hP, hn]
      · have h2 : 2 ≤ n := by
          rw [← hn]
          have : ({P, Pb} : Finset (PlE D.host)) ⊆ Q \ Q'' := by
            intro R hR
            rw [Finset.mem_insert, Finset.mem_singleton] at hR
            rcases hR with rfl | rfl
            · exact hP
            · exact Finset.mem_sdiff.2 ⟨hPbQ, hPbQ''⟩
          calc 2 = ({P, Pb} : Finset (PlE D.host)).card := (Finset.card_pair hne).symm
            _ ≤ _ := Finset.card_le_card this
        omega
      · exact Finset.mem_erase.2 ⟨hne.symm, Finset.mem_sdiff.2 ⟨hPbQ, hPbQ''⟩⟩
    obtain ⟨ops1, hl1, ho1, ha1⟩ := ih (Q1 \ Q'').card (by omega) Q1 hs1 hA1 rfl
    obtain ⟨P0, hP0, sg, hsg, hstep⟩ :=
      ((h12 i hi M).2 j hj b).2 Q hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2.1 hQ.2.2.2.2 P hPQ Pb hPbQ hne hc
    obtain ⟨σ, hσ⟩ := hF P0
    refine ⟨(P0, sg, σ) :: ops1, ?_, ?_, ?_⟩
    · rw [List.length_cons]; omega
    · intro o ho
      rcases List.mem_cons.1 ho with rfl | ho
      · refine ⟨?_, hsg, hσ⟩
        rcases hP0 with rfl | rfl
        · exact hP
        · exact Finset.mem_sdiff.2 ⟨hPbQ, hPbQ''⟩
      · obtain ⟨h1, h2⟩ := ho1 o ho
        exact ⟨Finset.sdiff_subset_sdiff hs2 (Finset.Subset.refl _) h1, h2⟩
    · intro a ha
      have ha' : Disjoint Q1 (Y.lev i j b a) := Finset.disjoint_of_subset_left hs2 ha
      rw [← lTensor_projA_comp Y i j b hs1 hs2 hs M, hstep a ha σ hσ, proj_PqTw, ha1 a ha', map_zsmul,
        (h12 i hi M).1 Q'' Q1 hs1 hcQ1 hQ'' hA1.2.2.2.1 σ, List.map_cons, List.prod_cons]
      rfl

open Classical in

theorem chain (hF : FrobEx N) (h12 : AugmentationCompatibility Y) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (M : ℕ) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool)
    (Q'' Q : Finset (PlE D.host)) (hs : Q'' ⊆ Q) (hQ : AdmQ Y i Q M) (hQ'' : ConjCl Q'') :
    AdmQ Y i Q'' M ∧
    ∃ ops : List (PlE D.host × ℤ × G D.host.E N.Om), 2 * ops.length = (Q \ Q'').card ∧
      (∀ o ∈ ops, o.1 ∈ Q \ Q'' ∧ (o.2.1 = 1 ∨ o.2.1 = -1) ∧ IsFrob (N.plOm.1 o.1) (normV o.1) o.2.2) ∧
      ∀ a : Y.Dat i j b, Disjoint Q (Y.lev i j b a) →
        (projA i hs M).toLinearMap.lTensor (Y.Fm i j b) (Y.thU i j b Q M a) =
          (ops.map fun o => PqTw Y i j b Q'' M o.1
            (o.2.1 • Multiplicative.toAdd (Y.delU i Q'' M o.2.2))).prod (Y.thU i j b Q'' M a) :=
  ⟨AdmQ.sub h12 hi hs hQ hQ'', quantumMinor_row_removal_chain hF h12 i hi M j hj b Q'' hQ'' _ Q hs hQ rfl⟩

end Chain

section CrdAll

open scoped TensorProduct

section Coord

variable {O Fm : Type} [CommRing O] [AddCommGroup Fm] [Module O Fm]

def IntIn (B : Submodule O Fm) (Λ : Type) [CommRing Λ] [Algebra O Λ] (w : Fm ⊗[O] Λ) : Prop :=
  w ∈ LinearMap.range (B.subtype.rTensor Λ)

variable {B : Submodule O Fm} {d : ℕ} (β : Module.Basis (Fin d) O B)
  (Λ : Type) [CommRing Λ] [Algebra O Λ]

def crdB : (B ⊗[O] Λ) →ₗ[O] (Fin d → Λ) :=
  LinearMap.pi fun t => (TensorProduct.lid O Λ).toLinearMap ∘ₗ (β.coord t).rTensor Λ

theorem crdB_tmul (x : B) (lam : Λ) (t : Fin d) : crdB β Λ (x ⊗ₜ lam) t = β.repr x t • lam := by
  simp [crdB]

open Classical in

def crd (w : Fm ⊗[O] Λ) : Fin d → Λ :=
  if h : IntIn B Λ w then crdB β Λ h.choose else 0

theorem rTensor_injective [Module.Flat O Λ] : Function.Injective (B.subtype.rTensor Λ) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := Λ) B.subtype B.injective_subtype

theorem intIn_rTensor (W : B ⊗[O] Λ) : IntIn B Λ (B.subtype.rTensor Λ W) := ⟨W, rfl⟩

theorem crd_rTensor [Module.Flat O Λ] (W : B ⊗[O] Λ) :
    crd β Λ (B.subtype.rTensor Λ W) = crdB β Λ W := by
  have h : IntIn B Λ (B.subtype.rTensor Λ W) := ⟨W, rfl⟩
  unfold crd
  rw [dif_pos h, rTensor_injective Λ h.choose_spec]

variable {Λ}

theorem IntIn.add {w w' : Fm ⊗[O] Λ} (h : IntIn B Λ w) (h' : IntIn B Λ w') : IntIn B Λ (w + w') :=
  Submodule.add_mem _ h h'

theorem IntIn.smul (c : O) {w : Fm ⊗[O] Λ} (h : IntIn B Λ w) : IntIn B Λ (c • w) :=
  Submodule.smul_mem _ c h

theorem IntIn.zero : IntIn B Λ (0 : Fm ⊗[O] Λ) := Submodule.zero_mem _

theorem IntIn.sum {ι : Type} (s : Finset ι) {w : ι → Fm ⊗[O] Λ} (h : ∀ a ∈ s, IntIn B Λ (w a)) :
    IntIn B Λ (∑ a ∈ s, w a) :=
  Submodule.sum_mem _ h

theorem crd_add [Module.Flat O Λ] {w w' : Fm ⊗[O] Λ} (h : IntIn B Λ w) (h' : IntIn B Λ w') :
    crd β Λ (w + w') = crd β Λ w + crd β Λ w' := by
  obtain ⟨W, rfl⟩ := h
  obtain ⟨W', rfl⟩ := h'
  rw [← map_add, crd_rTensor, crd_rTensor, crd_rTensor, map_add]

theorem crd_smul [Module.Flat O Λ] (c : O) {w : Fm ⊗[O] Λ} (h : IntIn B Λ w) :
    crd β Λ (c • w) = c • crd β Λ w := by
  obtain ⟨W, rfl⟩ := h
  rw [← map_smul, crd_rTensor, crd_rTensor, map_smul]

theorem crd_zero [Module.Flat O Λ] : crd β Λ (0 : Fm ⊗[O] Λ) = 0 := by
  have := crd_rTensor β Λ (0 : B ⊗[O] Λ)
  simpa using this

theorem crd_sum [Module.Flat O Λ] {ι : Type} (s : Finset ι) {w : ι → Fm ⊗[O] Λ}
    (h : ∀ a ∈ s, IntIn B Λ (w a)) : crd β Λ (∑ a ∈ s, w a) = ∑ a ∈ s, crd β Λ (w a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [crd_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      crd_add β (h a (Finset.mem_insert_self a s))
        (IntIn.sum s fun x hx => h x (Finset.mem_insert_of_mem hx)),
      ih fun x hx => h x (Finset.mem_insert_of_mem hx)]

theorem eq_sum_crdB (W : B ⊗[O] Λ) : W = ∑ t, β t ⊗ₜ[O] crdB β Λ W t := by
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul x lam =>
    simp only [crdB_tmul, TensorProduct.tmul_smul]
    conv_lhs => rw [← β.sum_repr x, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [TensorProduct.smul_tmul']
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_add, Pi.add_apply, TensorProduct.tmul_add]

theorem crd_lTensor [Module.Flat O Λ] {Λ' : Type} [CommRing Λ'] [Algebra O Λ'] [Module.Flat O Λ']
    (φ : Λ →ₐ[O] Λ') {w : Fm ⊗[O] Λ} (h : IntIn B Λ w) :
    IntIn B Λ' (φ.toLinearMap.lTensor Fm w) ∧
      crd β Λ' (φ.toLinearMap.lTensor Fm w) = fun t => φ (crd β Λ w t) := by
  obtain ⟨W, rfl⟩ := h
  have e : φ.toLinearMap.lTensor Fm (B.subtype.rTensor Λ W) =
      B.subtype.rTensor Λ' (φ.toLinearMap.lTensor B W) := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [e, crd_rTensor, crd_rTensor]
  refine ⟨⟨_, rfl⟩, ?_⟩
  clear e
  funext t
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul x lam => simp [crdB_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

def matB (T : Module.End O Fm) (hT : B.map T ≤ B) : Matrix (Fin d) (Fin d) O :=
  LinearMap.toMatrix β β (T.restrict fun x hx => hT ⟨x, hx, rfl⟩)

theorem crd_map [Module.Flat O Λ] (T : Module.End O Fm) (hT : B.map T ≤ B) (lam : Λ) {w : Fm ⊗[O] Λ}
    (h : IntIn B Λ w) :
    IntIn B Λ (TensorProduct.map T (LinearMap.mulLeft O lam) w) ∧
      crd β Λ (TensorProduct.map T (LinearMap.mulLeft O lam) w) =
        (lam • (matB β T hT).map (algebraMap O Λ)).mulVec (crd β Λ w) := by
  obtain ⟨W, rfl⟩ := h
  set TB : B →ₗ[O] B := T.restrict fun x hx => hT ⟨x, hx, rfl⟩ with hTB
  have e : TensorProduct.map T (LinearMap.mulLeft O lam) (B.subtype.rTensor Λ W) =
      B.subtype.rTensor Λ (TensorProduct.map TB (LinearMap.mulLeft O lam) W) := by
    induction W using TensorProduct.induction_on with
    | zero => simp
    | tmul x mu => simp [hTB]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [e, crd_rTensor, crd_rTensor]
  refine ⟨⟨_, rfl⟩, ?_⟩
  clear e
  funext t
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul x mu =>
    rw [TensorProduct.map_tmul, crdB_tmul, LinearMap.mulLeft_apply]
    have h1 : β.repr (TB x) t = ∑ s, matB β T hT t s * β.repr x s := by
      have := congrFun (LinearMap.toMatrix_mulVec_repr β β TB x) t
      rw [← this]
      rfl
    rw [h1, Matrix.mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [crdB_tmul, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    simp only [Algebra.smul_def, map_mul]
    ring
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy, Matrix.mulVec_add]

theorem crd_poly [Module.Flat O Λ] (s : Finset ℕ) (c : ℕ → O) (T : ℕ → Module.End O Fm)
    (hT : ∀ k, B.map (T k) ≤ B) (lam : ℕ → Λ) {w : Fm ⊗[O] Λ} (h : IntIn B Λ w) :
    IntIn B Λ ((1 + ∑ k ∈ s, c k • TensorProduct.map (T k) (LinearMap.mulLeft O (lam k)) :
        Module.End O (Fm ⊗[O] Λ)) w) ∧
      crd β Λ ((1 + ∑ k ∈ s, c k • TensorProduct.map (T k) (LinearMap.mulLeft O (lam k)) :
        Module.End O (Fm ⊗[O] Λ)) w) =
        (1 + ∑ k ∈ s, (algebraMap O Λ (c k) * lam k) • (matB β (T k) (hT k)).map (algebraMap O Λ)).mulVec
          (crd β Λ w) := by
  have h1 : ∀ k ∈ s, IntIn B Λ (c k • TensorProduct.map (T k) (LinearMap.mulLeft O (lam k)) w) :=
    fun k _ => (crd_map β (T k) (hT k) (lam k) h).1.smul (c k)
  have e : (1 + ∑ k ∈ s, c k • TensorProduct.map (T k) (LinearMap.mulLeft O (lam k)) :
      Module.End O (Fm ⊗[O] Λ)) w =
      w + ∑ k ∈ s, c k • TensorProduct.map (T k) (LinearMap.mulLeft O (lam k)) w := by
    simp [LinearMap.add_apply, LinearMap.sum_apply]
  rw [e]
  refine ⟨h.add (IntIn.sum s h1), ?_⟩
  rw [crd_add β h (IntIn.sum s h1), crd_sum β s h1, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.sum_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [crd_smul β (c k) (crd_map β (T k) (hT k) (lam k) h).1, (crd_map β (T k) (hT k) (lam k) h).2,
    mul_smul, Matrix.smul_mulVec, algebraMap_smul, Matrix.smul_mulVec, Matrix.smul_mulVec]

theorem crd_tmul_one [Module.Flat O Λ] {x : Fm} (hx : x ∈ B) :
    IntIn B Λ (x ⊗ₜ[O] (1 : Λ)) ∧
      crd β Λ (x ⊗ₜ[O] (1 : Λ)) = fun t => algebraMap O Λ (β.repr ⟨x, hx⟩ t) := by
  have e : x ⊗ₜ[O] (1 : Λ) = B.subtype.rTensor Λ ((⟨x, hx⟩ : B) ⊗ₜ[O] (1 : Λ)) := by simp
  rw [e, crd_rTensor]
  refine ⟨⟨_, rfl⟩, ?_⟩
  funext t
  rw [crdB_tmul, Algebra.algebraMap_eq_smul_one]

theorem comm_lTensor_eq [Module.Flat O Λ] {R' : Type} [CommRing R'] [Algebra O R'] (ev : Λ →ₐ[O] R')
    {w : Fm ⊗[O] Λ} (h : IntIn B Λ w) :
    (TensorProduct.comm O Fm R') (ev.toLinearMap.lTensor Fm w) =
      ∑ t, ev (crd β Λ w t) ⊗ₜ[O] (β t : Fm) := by
  obtain ⟨W, rfl⟩ := h
  rw [crd_rTensor]
  conv_lhs => rw [eq_sum_crdB β W]
  simp [map_sum]

end Coord

section Free

open Formalism.IrreducibleCountingLemmas.TW (relLen)
open Formalism.MainNotions.IntegralHeckeForms (IsLatIn)
open Formalism.MainNotions.BlochKatoReduction.Gen (nval)

variable {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W] [Module R W]

theorem ord_eq_addVal {x : R} (hx : x ≠ 0) : Ring.ord R x = IsDiscreteValuationRing.addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [Formalism.IrreducibleCountingLemmas.TW.Idx.ord_unit_mul_pow hϖ, IsDiscreteValuationRing.addVal_def _ u hϖ n rfl]

theorem sIdx_add_real (l : ℕ) {M N P V : Submodule R W} (hM : IsLatIn M V) (hN : IsLatIn N V)
    (hP : IsLatIn P V) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l M N + Formalism.MainNotions.IntegralHeckeForms.sIdx l N P = Formalism.MainNotions.IntegralHeckeForms.sIdx l M P := by
  have a := Formalism.MainNotions.IntegralHeckeForms.Idx.sIdx_add hM hN hP
  simp only [Formalism.MainNotions.IntegralHeckeForms.Idx.sIdx_eq, ← add_div]
  congr 1
  exact_mod_cast a

theorem sIdx_of_le (l : ℕ) {M N : Submodule R W} (h : N ≤ M) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l M N =
      ((relLen M N).toNat : ℝ) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ) := by
  rw [Formalism.MainNotions.IntegralHeckeForms.Idx.sIdx_eq]
  unfold Formalism.IrreducibleCountingLemmas.TW.sIdx
  rw [Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_of_le h]
  simp

theorem sIdx_mono (l : ℕ) {B0 Y T V : Submodule R W} (hB : IsLatIn B0 V) (hY : IsLatIn Y V)
    (hT : IsLatIn T V) (h : Y ≤ T) : Formalism.MainNotions.IntegralHeckeForms.sIdx l B0 T ≤ Formalism.MainNotions.IntegralHeckeForms.sIdx l B0 Y := by
  have a := sIdx_add_real l hB hT hY
  have b : 0 ≤ Formalism.MainNotions.IntegralHeckeForms.sIdx l T Y := by
    rw [sIdx_of_le l h]
    positivity
  linarith

variable {d : ℕ} {e : Fin d → W}

def vecOf (e : Fin d → W) (Mx : Matrix (Fin d) (Fin d) R) (a : Fin d) : W := ∑ t, Mx t a • e t

theorem span_vecOf_le (e : Fin d → W) (Mx : Matrix (Fin d) (Fin d) R) :
    Submodule.span R (Set.range (vecOf e Mx)) ≤ Submodule.span R (Set.range e) := by
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

theorem det_smul_mem (e : Fin d → W) (Mx : Matrix (Fin d) (Fin d) R) {x : W}
    (hx : x ∈ Submodule.span R (Set.range e)) :
    Mx.det • x ∈ Submodule.span R (Set.range (vecOf e Mx)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    have : Mx.det • e t = ∑ a, Mx.adjugate a t • vecOf e Mx a := by
      unfold vecOf
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have h1 : ∀ s : Fin d, ∑ a, (Mx.adjugate a t * Mx s a) • e s = ((Mx * Mx.adjugate) s t) • e s := by
        intro s
        rw [← Finset.sum_smul, Matrix.mul_apply]
        congr 1
        exact Finset.sum_congr rfl fun a _ => mul_comm _ _
      simp only [h1, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero, ite_smul, zero_smul]
      simp
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem isLatIn_vecOf {V : Submodule R W} (hV : IsLatIn (Submodule.span R (Set.range e)) V)
    {Mx : Matrix (Fin d) (Fin d) R} (hdet : Mx.det ≠ 0) :
    IsLatIn (Submodule.span R (Set.range (vecOf e Mx))) V := by
  refine ⟨Submodule.fg_span (Set.finite_range _), (span_vecOf_le e Mx).trans hV.2.1, ?_⟩
  intro x hx
  obtain ⟨c, hc, h⟩ := hV.2.2 x hx
  exact ⟨Mx.det * c, mul_ne_zero hdet hc, by rw [mul_smul]; exact det_smul_mem e Mx h⟩

theorem linearIndependent_vecOf (he : LinearIndependent R e) {Mx : Matrix (Fin d) (Fin d) R}
    (hdet : Mx.det ≠ 0) : LinearIndependent R (vecOf e Mx) := by
  rw [Fintype.linearIndependent_iff] at he ⊢
  intro g hg
  have h1 : ∑ t, (Mx.mulVec g t) • e t = 0 := by
    rw [← hg]
    unfold vecOf
    simp only [Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun t _ => by rw [mul_comm]
  have h2 : Mx.mulVec g = 0 := funext fun t => he _ h1 t
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hdet h2
  exact fun a => congrFun h3 a

theorem relLen_vecOf (he : LinearIndependent R e) {Mx : Matrix (Fin d) (Fin d) R} (hdet : Mx.det ≠ 0) :
    relLen (Submodule.span R (Set.range e)) (Submodule.span R (Set.range (vecOf e Mx))) =
      IsDiscreteValuationRing.addVal R Mx.det := by
  set E := Submodule.span R (Set.range e) with hE
  let bE : Module.Basis (Fin d) R E := Module.Basis.span he
  have hbE : ∀ t, (bE t : W) = e t := fun t => congrArg Subtype.val (Module.Basis.span_apply he t)
  let f : E →ₗ[R] E := Matrix.toLin bE bE Mx
  have hf : ∀ a, (f (bE a) : W) = vecOf e Mx a := by
    intro a
    show ((Matrix.toLin bE bE Mx (bE a) : E) : W) = _
    rw [Matrix.toLin_self]
    unfold vecOf
    simp [hbE]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : Mx.mulVec (bE.repr x) = 0 := by
      have := LinearMap.toMatrix_mulVec_repr bE bE f x
      rw [LinearMap.toMatrix_toLin, hx] at this
      simpa using this
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet h1
    apply bE.repr.injective
    rw [map_zero]
    exact DFunLike.coe_injective h2
  have hrange : (Submodule.span R (Set.range (vecOf e Mx))).comap E.subtype = LinearMap.range f := by
    apply Submodule.map_injective_of_injective E.injective_subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.2 (span_vecOf_le e Mx), LinearMap.range_eq_map,
      ← bE.span_eq, Submodule.map_span, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨f (bE a), ⟨bE a, ⟨a, rfl⟩, rfl⟩, hf a⟩
    · rintro ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, rfl⟩
      exact ⟨a, (hf a).symm⟩
  unfold relLen
  rw [hrange, Formalism.IrreducibleCountingLemmas.TW.Idx.length_quot_range bE f hinj, LinearMap.det_toLin, ord_eq_addVal hdet]

theorem sIdx_vecOf (l : ℕ) (he : LinearIndependent R e) {Mx : Matrix (Fin d) (Fin d) R}
    (hdet : Mx.det ≠ 0) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l (Submodule.span R (Set.range e)) (Submodule.span R (Set.range (vecOf e Mx))) =
      nval R l Mx.det := by
  rw [sIdx_of_le l (span_vecOf_le e Mx), relLen_vecOf he hdet]
  rfl

theorem nval_pow (l : ℕ) (x : R) (n : ℕ) : nval R l (x ^ n) = n * nval R l x := by
  unfold nval
  rw [IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul, ENat.toNat_mul, ENat.toNat_natCast]
  push_cast
  ring

theorem isLatIn_of_smul {V : Submodule R W} {y z : Fin d → W} {c' : R} (hyz : ∀ a, c' • y a = z a)
    (hzV : IsLatIn (Submodule.span R (Set.range z)) V) (hy : ∀ a, y a ∈ V) :
    IsLatIn (Submodule.span R (Set.range y)) V := by
  refine Formalism.MainNotions.IntegralHeckeForms.Idx.isLatIn_of_le hzV (Submodule.fg_span (Set.finite_range _)) ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [← hyz a]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact hy a

theorem sIdx_of_smul (l : ℕ) {V B0 : Submodule R W} {y z : Fin d → W} {c' : R} (hc : c' ≠ 0)
    (hyz : ∀ a, c' • y a = z a) (hz : LinearIndependent R z)
    (hzV : IsLatIn (Submodule.span R (Set.range z)) V) (hy : ∀ a, y a ∈ V) (hB : IsLatIn B0 V) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l B0 (Submodule.span R (Set.range y)) =
      Formalism.MainNotions.IntegralHeckeForms.sIdx l B0 (Submodule.span R (Set.range z)) - d * nval R l c' := by
  have hyl : LinearIndependent R y := by
    rw [Fintype.linearIndependent_iff] at hz ⊢
    intro g hg
    apply hz g
    simp only [← hyz, smul_comm _ c']
    rw [← Finset.smul_sum, hg, smul_zero]
  have hzv : z = vecOf y (c' • (1 : Matrix (Fin d) (Fin d) R)) := by
    funext a
    unfold vecOf
    simp [Matrix.one_apply, ← hyz a]
  have hdet : (c' • (1 : Matrix (Fin d) (Fin d) R)).det = c' ^ d := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have h1 := sIdx_add_real l hB (isLatIn_of_smul hyz hzV hy) hzV
  have h2 : Formalism.MainNotions.IntegralHeckeForms.sIdx l (Submodule.span R (Set.range y)) (Submodule.span R (Set.range z)) =
      d * nval R l c' := by
    rw [hzv, sIdx_vecOf l hyl (by rw [hdet]; exact pow_ne_zero _ hc), hdet, nval_pow]
  linarith

end Free

section BaseCh

variable {O Fm : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup Fm] [Module O Fm]
  {B : Submodule O Fm} {d : ℕ} (β : Module.Basis (Fin d) O B)
  (R' : Type) [CommRing R'] [IsDomain R'] [Algebra O R']

theorem span_one_tmul :
    Submodule.span R' (Set.range fun t => (1 : R') ⊗ₜ[O] (β t : Fm)) = B.baseChange R' := by
  have hB : B = Submodule.span O (Set.range fun t => (β t : Fm)) := by
    have h1 := congrArg (Submodule.map B.subtype) β.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h1
    exact h1.symm
  conv_rhs => rw [hB, Submodule.baseChange_span, ← Set.range_comp]
  rfl

theorem linearIndependent_one_tmul (hinj : Function.Injective (algebraMap O R')) :
    LinearIndependent R' fun t => (1 : R') ⊗ₜ[O] (β t : Fm) := by
  have : FaithfulSMul O R' := (faithfulSMul_iff_algebraMap_injective O R').mpr hinj
  have : Module.IsTorsionFree O R' := inferInstance
  have : Module.Flat O R' := inferInstance
  have h1 := (Algebra.TensorProduct.basis R' β).linearIndependent
  have h2 : Function.Injective (B.subtype.baseChange R') := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := R') B.subtype B.injective_subtype
  have h3 := h1.map' (B.subtype.baseChange R') (LinearMap.ker_eq_bot.2 h2)
  have h4 : (fun t => (1 : R') ⊗ₜ[O] (β t : Fm)) =
      (B.subtype.baseChange R') ∘ (Algebra.TensorProduct.basis R' β) := by
    funext t
    simp
  rw [h4]
  exact h3

end BaseCh

section Det

open Formalism.MainNotions.IntegralHeckeForms (IsLatIn)
open Formalism.MainNotions.BlochKatoReduction.Gen (nval)

variable {O Fm : Type} [CommRing O] [AddCommGroup Fm] [Module O Fm]
  {B : Submodule O Fm} {d : ℕ} (β : Module.Basis (Fin d) O B)

def mxOf (Λ : Type) [CommRing Λ] [Algebra O Λ] (w : Fin d → Fm ⊗[O] Λ) : Matrix (Fin d) (Fin d) Λ :=
  Matrix.of fun t a => crd β Λ (w a) t

variable {Λ : Type} [CommRing Λ] [Algebra O Λ] [Module.Flat O Λ]

theorem mxOf_lTensor {Λ' : Type} [CommRing Λ'] [Algebra O Λ'] [Module.Flat O Λ'] (φ : Λ →ₐ[O] Λ')
    {w : Fin d → Fm ⊗[O] Λ} (h : ∀ a, IntIn B Λ (w a)) :
    mxOf β Λ' (fun a => φ.toLinearMap.lTensor Fm (w a)) = (mxOf β Λ w).map φ := by
  ext t a
  simp only [mxOf, Matrix.of_apply, Matrix.map_apply]
  rw [(crd_lTensor β φ (h a)).2]

theorem det_mxOf_lTensor {Λ' : Type} [CommRing Λ'] [Algebra O Λ'] [Module.Flat O Λ'] (φ : Λ →ₐ[O] Λ')
    {w : Fin d → Fm ⊗[O] Λ} (h : ∀ a, IntIn B Λ (w a)) :
    (mxOf β Λ' (fun a => φ.toLinearMap.lTensor Fm (w a))).det = φ (mxOf β Λ w).det := by
  rw [mxOf_lTensor β φ h, AlgHom.map_det]
  rfl

theorem mxOf_op (Op : Module.End O (Fm ⊗[O] Λ)) (Pm : Matrix (Fin d) (Fin d) Λ) {w : Fin d → Fm ⊗[O] Λ}
    (h : ∀ a, crd β Λ (Op (w a)) = Pm.mulVec (crd β Λ (w a))) :
    mxOf β Λ (fun a => Op (w a)) = Pm * mxOf β Λ w := by
  ext t a
  simp only [mxOf, Matrix.of_apply, Matrix.mul_apply]
  rw [h a]
  rfl

theorem det_mxOf_op (Op : Module.End O (Fm ⊗[O] Λ)) (Pm : Matrix (Fin d) (Fin d) Λ)
    {w : Fin d → Fm ⊗[O] Λ} (h : ∀ a, crd β Λ (Op (w a)) = Pm.mulVec (crd β Λ (w a))) :
    (mxOf β Λ (fun a => Op (w a))).det = Pm.det * (mxOf β Λ w).det := by
  rw [mxOf_op β Op Pm h, Matrix.det_mul]

theorem comm_lTensor_eq_vecOf {R' : Type} [CommRing R'] [Algebra O R'] (ev : Λ →ₐ[O] R')
    {w : Fin d → Fm ⊗[O] Λ} (h : ∀ a, IntIn B Λ (w a)) (a : Fin d) :
    (TensorProduct.comm O Fm R') (ev.toLinearMap.lTensor Fm (w a)) =
      vecOf (fun t => (1 : R') ⊗ₜ[O] (β t : Fm)) ((mxOf β Λ w).map ev) a := by
  rw [comm_lTensor_eq β ev (h a)]
  unfold vecOf
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

end Det

section Det2

open Formalism.MainNotions.IntegralHeckeForms (IsLatIn)
open Formalism.MainNotions.BlochKatoReduction.Gen (nval)

variable {O Fm : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup Fm] [Module O Fm]
  {B : Submodule O Fm} {d : ℕ} (β : Module.Basis (Fin d) O B)

theorem sIdx_spec {Λ : Type} [CommRing Λ] [Algebra O Λ] [Module.Flat O Λ]
    {R' : Type} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra O R']
    (hinj : Function.Injective (algebraMap O R')) (l : ℕ) (ev : Λ →ₐ[O] R')
    {w : Fin d → Fm ⊗[O] Λ} (h : ∀ a, IntIn B Λ (w a)) (hdet : ev (mxOf β Λ w).det ≠ 0)
    {V' : Submodule R' (R' ⊗[O] Fm)} (hV : IsLatIn (B.baseChange R') V') :
    LinearIndependent R' (fun a => (TensorProduct.comm O Fm R') (ev.toLinearMap.lTensor Fm (w a))) ∧
    IsLatIn (Submodule.span R'
      (Set.range fun a => (TensorProduct.comm O Fm R') (ev.toLinearMap.lTensor Fm (w a)))) V' ∧
    Formalism.MainNotions.IntegralHeckeForms.sIdx l (B.baseChange R') (Submodule.span R'
      (Set.range fun a => (TensorProduct.comm O Fm R') (ev.toLinearMap.lTensor Fm (w a)))) =
        nval R' l (ev (mxOf β Λ w).det) := by
  have hz : (fun a => (TensorProduct.comm O Fm R') (ev.toLinearMap.lTensor Fm (w a))) =
      vecOf (fun t => (1 : R') ⊗ₜ[O] (β t : Fm)) ((mxOf β Λ w).map ev) :=
    funext fun a => comm_lTensor_eq_vecOf β ev h a
  have hd : ((mxOf β Λ w).map ev).det = ev (mxOf β Λ w).det := by
    rw [AlgHom.map_det]
    rfl
  have hd0 : ((mxOf β Λ w).map ev).det ≠ 0 := by rw [hd]; exact hdet
  have he := linearIndependent_one_tmul β R' hinj
  rw [hz, ← span_one_tmul β R', ← hd]
  rw [← span_one_tmul β R'] at hV
  exact ⟨linearIndependent_vecOf he hd0, isLatIn_vecOf hV hd0, sIdx_vecOf l he hd0⟩

def mxB (x : Fin d → Fm) (hx : ∀ a, x a ∈ B) : Matrix (Fin d) (Fin d) O :=
  Matrix.of fun t a => β.repr ⟨x a, hx a⟩ t

theorem eq_vecOf_mxB (x : Fin d → Fm) (hx : ∀ a, x a ∈ B) :
    x = vecOf (fun t => (β t : Fm)) (mxB β x hx) := by
  funext a
  unfold vecOf mxB
  have h := congrArg B.subtype (β.sum_repr ⟨x a, hx a⟩)
  rw [map_sum] at h
  simp only [map_smul, Submodule.subtype_apply] at h
  exact h.symm

theorem span_basis_eq : Submodule.span O (Set.range fun t => (β t : Fm)) = B := by
  have h1 := congrArg (Submodule.map B.subtype) β.span_eq
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h1
  exact h1

theorem linearIndependent_basis_coe : LinearIndependent O fun t => (β t : Fm) :=
  β.linearIndependent.map' B.subtype (LinearMap.ker_eq_bot.2 B.injective_subtype)

theorem det_mxB_ne_zero (x : Fin d → Fm) (hx : ∀ a, x a ∈ B) (hli : LinearIndependent O x) :
    (mxB β x hx).det ≠ 0 := by
  intro h0
  obtain ⟨g, hg, hg0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hg
  rw [Fintype.linearIndependent_iff] at hli
  funext a
  refine hli g ?_ a
  conv_lhs => rw [eq_vecOf_mxB β x hx]
  unfold vecOf
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have : ∀ t, ∑ a, (g a * mxB β x hx t a) • (β t : Fm) = ((mxB β x hx).mulVec g t) • (β t : Fm) := by
    intro t
    rw [← Finset.sum_smul]
    congr 1
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  simp only [this, hg0, Pi.zero_apply, zero_smul, Finset.sum_const_zero]

theorem sIdx_mxB (l : ℕ) (x : Fin d → Fm) (hx : ∀ a, x a ∈ B) (hli : LinearIndependent O x) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l B (Submodule.span O (Set.range x)) = nval O l (mxB β x hx).det := by
  have h := sIdx_vecOf l (linearIndependent_basis_coe β) (det_mxB_ne_zero β x hx hli)
  rw [← eq_vecOf_mxB β x hx, span_basis_eq β] at h
  exact h

end Det2

end CrdAll

section Alg

open Polynomial

def Pmat {O Λ : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] {d : ℕ} (r : ℕ) (c : ℕ → O)
    (T : ℕ → Matrix (Fin d) (Fin d) O) (u : Λ) : Matrix (Fin d) (Fin d) Λ :=
  1 + ∑ k ∈ Finset.Icc 1 r, (algebraMap O Λ (c k) * u ^ k) • (T k).map (algebraMap O Λ)

theorem Pmat_map {O Λ Λ' : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [CommRing Λ'] [Algebra O Λ'] {d : ℕ}
    (r : ℕ) (c : ℕ → O) (T : ℕ → Matrix (Fin d) (Fin d) O) (u : Λ) (φ : Λ →ₐ[O] Λ') :
    (Pmat r c T u).map φ = Pmat r c T (φ u) := by
  ext a b
  simp only [Pmat, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    map_add, map_sum, map_mul, map_pow, AlgHom.commutes, Matrix.one_apply]
  congr 1
  split_ifs <;> simp

theorem det_Pmat_map {O Λ Λ' : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] [CommRing Λ'] [Algebra O Λ']
    {d : ℕ} (r : ℕ) (c : ℕ → O) (T : ℕ → Matrix (Fin d) (Fin d) O) (u : Λ) (φ : Λ →ₐ[O] Λ') :
    φ (Pmat r c T u).det = (Pmat r c T (φ u)).det := by
  rw [← Pmat_map, AlgHom.map_det]
  rfl

theorem sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (r : ℕ) :
    ∑ k ∈ Finset.Icc 1 r, g k = ∑ i ∈ Finset.range r, g (i + 1) := by
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem aeval_mem_map {O Λ : Type} [CommRing O] [CommRing Λ] [Algebra O Λ] (I : Ideal O) (u : Λ) (f : O[X])
    (hf : ∀ n, f.coeff n ∈ I) : aeval u f ∈ Ideal.map (algebraMap O Λ) I := by
  rw [aeval_eq_sum_range]
  refine Ideal.sum_mem _ fun n _ => ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hf n))

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAlgClosed (IsLocalRing.ResidueField O)]

theorem det_Pmat_factor (Λ : Type) [CommRing Λ] [Algebra O Λ] {d : ℕ} (r : ℕ) (c : ℕ → O)
    (T : ℕ → Matrix (Fin d) (Fin d) O) (u : Λ) :
    ∃ L : List O, L.length ≤ r * d ∧
      (Pmat r c T u).det - (L.map fun α => 1 - α • u).prod ∈
        Ideal.map (algebraMap O Λ) (IsLocalRing.maximalIdeal O) := by
  set res := IsLocalRing.residue O with hres
  let A : Fin (r + 1) → Matrix (Fin d) (Fin d) (IsLocalRing.ResidueField O) := fun j =>
    if (j : ℕ) = 0 then 1 else res (c j) • (T j).map res
  obtain ⟨n, α, hn, hα⟩ := Formalism.IrreducibleCountingLemmas.TW.hecke_determinant_factors (IsLocalRing.ResidueField O) d r A (by simp [A])
  choose α' hα' using fun i => IsLocalRing.residue_surjective (α i)
  set p : O[X] := (Pmat r c T (X : O[X])).det with hp
  set q : O[X] := ((List.ofFn α').map fun a => 1 - a • (X : O[X])).prod with hq
  have hmat : (Pmat r c T (X : O[X])).map (Polynomial.mapRingHom res) =
      ∑ j : Fin (r + 1), (X : (IsLocalRing.ResidueField O)[X]) ^ (j : ℕ) • (A j).map Polynomial.C := by
    have h1 : ∑ j : Fin (r + 1), (X : (IsLocalRing.ResidueField O)[X]) ^ (j : ℕ) • (A j).map Polynomial.C =
        ∑ j ∈ Finset.range (r + 1), (X : (IsLocalRing.ResidueField O)[X]) ^ j •
          (if j = 0 then (1 : Matrix (Fin d) (Fin d) (IsLocalRing.ResidueField O))
            else res (c j) • (T j).map res).map Polynomial.C :=
      Fin.sum_univ_eq_sum_range (fun j => (X : (IsLocalRing.ResidueField O)[X]) ^ j •
          (if j = 0 then (1 : Matrix (Fin d) (Fin d) (IsLocalRing.ResidueField O))
            else res (c j) • (T j).map res).map Polynomial.C) (r + 1)
    rw [h1, Finset.sum_range_succ', Pmat, sum_Icc_one_eq_range]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.algebraMap_eq, Polynomial.map_C, if_true,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, pow_zero, one_mul, Matrix.one_apply, map_mul]
    rw [add_comm]
    have e1 : ∀ x, C (res (c (x + 1))) * X ^ (x + 1) * C (res (T (x + 1) a b)) =
        X ^ (x + 1) * (C (res (c (x + 1))) * C (res (T (x + 1) a b))) := fun x => by ring
    have e2 : Polynomial.map res (if a = b then 1 else 0) =
        C (if a = b then (1 : IsLocalRing.ResidueField O) else 0) := by split_ifs <;> simp
    rw [e2, Finset.sum_congr rfl fun x _ => e1 x]
  have hpm : p.map res = ∏ i, (1 - Polynomial.C (α i) * X) := by
    rw [← hα, ← hmat, hp, ← Polynomial.coe_mapRingHom, RingHom.map_det]
    rfl
  have hqm : q.map res = ∏ i, (1 - Polynomial.C (α i) * X) := by
    rw [hq, ← Polynomial.coe_mapRingHom, map_list_prod, List.map_map, List.map_ofFn, List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Polynomial.smul_eq_C_mul, hα', hres]
  have hcoef : ∀ m, (p - q).coeff m ∈ IsLocalRing.maximalIdeal O := by
    intro m
    rw [← IsLocalRing.residue_eq_zero_iff, ← Polynomial.coeff_map, Polynomial.map_sub, hpm, hqm, sub_self,
      Polynomial.coeff_zero]
  refine ⟨List.ofFn α', by rw [List.length_ofFn]; exact hn, ?_⟩
  have h2 := aeval_mem_map (Λ := Λ) _ u (p - q) hcoef
  rw [map_sub, hp, det_Pmat_map, aeval_X, hq, map_list_prod, List.map_map] at h2
  have e : List.map (⇑(aeval u) ∘ fun a => 1 - a • (X : O[X])) (List.ofFn α') =
      List.map (fun α => 1 - α • u) (List.ofFn α') := List.map_congr_left fun a _ => by simp
  rw [e] at h2
  exact h2

theorem det_Pmat_factor_inv (Λ : Type) [CommRing Λ] [Algebra O Λ] {d : ℕ} (r : ℕ) (c : ℕ → O)
    (T : ℕ → Matrix (Fin d) (Fin d) O) (u u' : Λ) (h : u * u' = 1) :
    ∃ (L : List O) (ε : Oˣ) (m : ℕ), L.length ≤ r * d ∧
      (Pmat r c T u').det - ((ε : O) • u' ^ m) * (L.map fun α => 1 - α • u).prod ∈
        Ideal.map (algebraMap O Λ) (IsLocalRing.maximalIdeal O) := by
  obtain ⟨L', hL', hd⟩ := det_Pmat_factor Λ r c T u'
  set I := Ideal.map (algebraMap O Λ) (IsLocalRing.maximalIdeal O) with hI
  have key : ∀ L' : List O, ∃ (L : List O) (ε : Oˣ) (m : ℕ), L.length ≤ L'.length ∧
      (L'.map fun α => 1 - α • u').prod - ((ε : O) • u' ^ m) * (L.map fun α => 1 - α • u).prod ∈ I := by
    intro L'
    induction L' with
    | nil => exact ⟨[], 1, 0, le_rfl, by simp⟩
    | cons α L' ih =>
      obtain ⟨L, ε, m, hl, hm⟩ := ih
      by_cases hα : α ∈ IsLocalRing.maximalIdeal O
      · refine ⟨L, ε, m, hl.trans (by simp), ?_⟩
        rw [List.map_cons, List.prod_cons]
        have h1 : algebraMap O Λ α * (u' * (L'.map fun α => 1 - α • u').prod) ∈ I :=
          Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hα)
        have h2 := I.sub_mem hm h1
        convert h2 using 1
        rw [Algebra.smul_def]
        ring
      · have hu : IsUnit α := by
          by_contra hn
          exact hα ((IsLocalRing.mem_maximalIdeal α).2 hn)
        obtain ⟨a, rfl⟩ := hu
        refine ⟨((a⁻¹ : Oˣ) : O) :: L, -a * ε, m + 1, by simpa using hl, ?_⟩
        rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
        have h1 : algebraMap O Λ (a : O) * algebraMap O Λ ((a⁻¹ : Oˣ) : O) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        have h2 := I.mul_mem_left (1 - (a : O) • u') hm
        convert h2 using 1
        simp only [Algebra.smul_def, Units.val_mul, Units.val_neg, map_mul, map_neg]
        linear_combination (-(algebraMap O Λ (ε : O)) * u' ^ m * (L.map fun α => 1 - algebraMap O Λ α * u).prod
          * u' * u) * h1 + (-(algebraMap O Λ (ε : O)) * u' ^ m *
            (L.map fun α => 1 - algebraMap O Λ α * u).prod) * h
  obtain ⟨L, ε, m, hl, hm⟩ := key L'
  refine ⟨L, ε, m, hl.trans hL', ?_⟩
  have := I.add_mem hd hm
  convert this using 1
  ring

theorem exists_common_eigenvector {k V ι : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (f : ι → Module.End k V) (hc : ∀ a b, Commute (f a) (f b))
    (W : Submodule k V) (hW : W ≠ ⊥) (hst : ∀ i, ∀ v ∈ W, f i v ∈ W) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ μ : k, f i v = μ • v :=
  _root_.UpperTheory.Reformulated.B.CommonEigenvectorInInvariantSubmodule.exists_common_eigenvector f hc W hW hst

theorem det_isUnit_of_eigen {d : ℕ} {ι : Type} (Tm : ι → Matrix (Fin d) (Fin d) O)
    (hc : ∀ a b, Commute (Tm a) (Tm b)) (s : Finset ι) (c : ι → O)
    (h : ∀ x : Fin d → O, (∃ t, x t ∉ IsLocalRing.maximalIdeal O) → ∀ ev : ι → O,
      (∀ a t, ((Tm a).mulVec x - ev a • x) t ∈ IsLocalRing.maximalIdeal O) →
      IsUnit (1 + ∑ a ∈ s, c a * ev a)) :
    IsUnit (1 + ∑ a ∈ s, c a • Tm a).det := by
  set res := IsLocalRing.residue O with hres
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hres, RingHom.map_det]
  intro hdet
  set Pb : Matrix (Fin d) (Fin d) (IsLocalRing.ResidueField O) :=
    res.mapMatrix (1 + ∑ a ∈ s, c a • Tm a) with hPb
  have hPb' : Pb = 1 + ∑ a ∈ s, res (c a) • res.mapMatrix (Tm a) := by
    rw [hPb, map_add, map_one, map_sum]
    refine congrArg (1 + ·) (Finset.sum_congr rfl fun a _ => ?_)
    ext x y
    simp [RingHom.mapMatrix_apply]
  obtain ⟨v0, hv0, hPv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  let f : ι → Module.End (IsLocalRing.ResidueField O) (Fin d → IsLocalRing.ResidueField O) :=
    fun a => Matrix.toLin' (res.mapMatrix (Tm a))
  have hcb : ∀ a b, Commute (res.mapMatrix (Tm a)) (res.mapMatrix (Tm b)) := fun a b => (hc a b).map _
  have hfc : ∀ a b, Commute (f a) (f b) := by
    intro a b
    show Matrix.toLin' _ * Matrix.toLin' _ = Matrix.toLin' _ * Matrix.toLin' _
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, (hcb a b).eq]
  have hPc : ∀ a, Commute Pb (res.mapMatrix (Tm a)) := by
    intro a
    rw [hPb']
    refine (Commute.one_left _).add_left (Commute.sum_left _ _ _ fun b _ => ?_)
    exact (hcb b a).smul_left _
  let W : Submodule (IsLocalRing.ResidueField O) (Fin d → IsLocalRing.ResidueField O) :=
    LinearMap.ker (Matrix.toLin' Pb)
  have hW : W ≠ ⊥ := by
    intro hb
    have : v0 ∈ W := by
      show Matrix.toLin' Pb v0 = 0
      rw [Matrix.toLin'_apply]; exact hPv0
    rw [hb, Submodule.mem_bot] at this
    exact hv0 this
  have hst : ∀ a, ∀ v ∈ W, f a v ∈ W := by
    intro a v hv
    have hv' : Pb.mulVec v = 0 := by
      have : Matrix.toLin' Pb v = 0 := hv
      rwa [Matrix.toLin'_apply] at this
    show Matrix.toLin' Pb (Matrix.toLin' (res.mapMatrix (Tm a)) v) = 0
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, (hPc a).eq, ← Matrix.mulVec_mulVec, hv',
      Matrix.mulVec_zero]
  obtain ⟨v, hvW, hv, hev⟩ := exists_common_eigenvector f hfc W hW hst
  choose μ hμ using hev
  choose x hx using fun t => IsLocalRing.residue_surjective (v t)
  choose ev hevl using fun a => IsLocalRing.residue_surjective (μ a)
  have hxv : (fun t => res (x t)) = v := funext hx
  have hx0 : ∃ t, x t ∉ IsLocalRing.maximalIdeal O := by
    by_contra hn
    simp only [not_exists, not_not] at hn
    apply hv
    funext t
    rw [← hx t]
    exact (IsLocalRing.residue_eq_zero_iff _).2 (hn t)
  have hTv : ∀ a, (res.mapMatrix (Tm a)).mulVec v = μ a • v := by
    intro a
    have := hμ a
    simpa only [f, Matrix.toLin'_apply] using this
  have heig : ∀ a t, ((Tm a).mulVec x - ev a • x) t ∈ IsLocalRing.maximalIdeal O := by
    intro a t
    rw [← IsLocalRing.residue_eq_zero_iff, Pi.sub_apply, map_sub, ← hres, RingHom.map_mulVec, Pi.smul_apply,
      smul_eq_mul, map_mul]
    have h1 : (res ∘ x) = v := hxv
    have h2 := congrFun (hTv a) t
    rw [h1]
    show ((res.mapMatrix (Tm a)).mulVec v) t - res (ev a) * res (x t) = 0
    rw [h2, hx t, hres, hevl a]
    simp
  have hunit := h x hx0 ev heig
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit] at hunit
  apply hunit
  have hPv : Pb.mulVec v = 0 := by
    have : Matrix.toLin' Pb v = 0 := hvW
    rwa [Matrix.toLin'_apply] at this
  have hsc : Pb.mulVec v = (1 + ∑ a ∈ s, res (c a) * μ a) • v := by
    rw [hPb', Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec, add_smul, one_smul, Finset.sum_smul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.smul_mulVec, hTv a, smul_smul]
  rw [hPv] at hsc
  have h0 := (smul_eq_zero.1 hsc.symm).resolve_right hv
  rw [map_add, map_one, map_sum]
  rw [← h0]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, hevl a]

end Alg

section Asm1

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (nval)
open scoped TensorProduct
open Classical

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}
  {i : X.Tw} {j : ℕ} {b : Bool} (p : Pack Y i j b)

def Pack.w (Q : Finset (PlE D.host)) (M : ℕ) (a : Y.Dat i j b) : Y.Fm i j b ⊗[X.O i] LamO X i Q M :=
  ((X.l i : X.O i) ^ p.c) • (p.A.rTensor (LamO X i Q M)) (Y.thU i j b Q M a)

def Pack.IntQ (Q : Finset (PlE D.host)) (M : ℕ) : Prop :=
  ∀ a ∈ p.S, IntIn p.B (LamO X i Q M) (p.w Q M a)

def Pack.Tk (_p : Pack Y i j b) (P : PlE D.host) (k : ℕ) : Module.End (X.O i) (Y.Fm i j b) :=
  if HkIdx i k P then hkO Y i j b k P else 0

theorem Pack.Tk_stable (P : PlE D.host) (k : ℕ) : p.B.map (p.Tk P k) ≤ p.B := by
  unfold Pack.Tk
  split_ifs with h
  · exact p.hkB k P h
  · rintro _ ⟨x, _, rfl⟩
    simp

def ck (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (P : PlE D.host) (k : ℕ) : X.O i :=
  (-1 : X.O i) ^ k * ((normV P : ℕ) : X.O i) ^ (k * (k - 1) / 2)

variable {n : ℕ} (β : Module.Basis (Fin n) (X.O i) p.B)

def Pack.Pm (Λ : Type) [CommRing Λ] [Algebra (X.O i) Λ] (P : PlE D.host) (u : Λ) : Matrix (Fin n) (Fin n) Λ :=
  Pmat D.R.r (ck X i P) (fun k => matB β (p.Tk P k) (p.Tk_stable P k)) u

theorem PqTw_eq {P : PlE D.host} (hP : IsSplitPl D.host P ∧ P ∉ X.S0 i) (Q : Finset (PlE D.host)) (M : ℕ)
    (γ : DelQM D.host (X.l i) Q M) :
    PqTw Y i j b Q M P γ = 1 + ∑ k ∈ Finset.Icc 1 D.R.r, ck X i P k •
      TensorProduct.map (p.Tk P k) (LinearMap.mulLeft (X.O i) (grp i Q M γ ^ k)) := by
  unfold PqTw
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Icc.1 hk
  have : HkIdx i k P := ⟨hk'.1, hk'.2, hP.1, hP.2⟩
  rw [grp_nsmul, Pack.Tk, if_pos this]
  rfl

theorem Pack.crd_PqTw {P : PlE D.host} (hP : IsSplitPl D.host P ∧ P ∉ X.S0 i) (Q : Finset (PlE D.host)) (M : ℕ)
    (γ : DelQM D.host (X.l i) Q M) {w : Y.Fm i j b ⊗[X.O i] LamO X i Q M}
    (h : IntIn p.B (LamO X i Q M) w) :
    IntIn p.B (LamO X i Q M) (PqTw Y i j b Q M P γ w) ∧
      crd β (LamO X i Q M) (PqTw Y i j b Q M P γ w) =
        (p.Pm β (LamO X i Q M) P (grp i Q M γ)).mulVec (crd β (LamO X i Q M) w) := by
  rw [PqTw_eq p hP]
  exact crd_poly β (Finset.Icc 1 D.R.r) (ck X i P) (p.Tk P) (p.Tk_stable P) (fun k => grp i Q M γ ^ k) h

abbrev Op (N : NData D.R D.host D.what₂) : Type := PlE D.host × ℤ × G D.host.E N.Om

def gam (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) (o : Op N) :
    DelQM D.host (X.l i) Q M :=
  o.2.1 • Multiplicative.toAdd (Y.delU i Q M o.2.2)

theorem Pack.crd_ops (Q : Finset (PlE D.host)) (M : ℕ) (ops : List (Op N))
    (hops : ∀ o ∈ ops, IsSplitPl D.host o.1 ∧ o.1 ∉ X.S0 i) {w : Y.Fm i j b ⊗[X.O i] LamO X i Q M}
    (h : IntIn p.B (LamO X i Q M) w) :
    IntIn p.B (LamO X i Q M) ((ops.map fun o => PqTw Y i j b Q M o.1 (gam Y i Q M o)).prod w) ∧
      crd β (LamO X i Q M) ((ops.map fun o => PqTw Y i j b Q M o.1 (gam Y i Q M o)).prod w) =
        ((ops.map fun o => p.Pm β (LamO X i Q M) o.1 (grp i Q M (gam Y i Q M o))).prod).mulVec
          (crd β (LamO X i Q M) w) := by
  induction ops with
  | nil => simpa using h
  | cons o ops ih =>
    have ih' := ih fun o' ho' => hops o' (List.mem_cons_of_mem _ ho')
    have h1 := p.crd_PqTw β (hops o List.mem_cons_self) Q M (gam Y i Q M o) ih'.1
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    refine ⟨h1.1, ?_⟩
    rw [h1.2, ih'.2, Matrix.mulVec_mulVec]

theorem Pack.rTensor_ops (Q : Finset (PlE D.host)) (M : ℕ) (ops : List (Op N))
    (hops : ∀ o ∈ ops, IsSplitPl D.host o.1 ∧ o.1 ∉ X.S0 i) (x : Y.Fm i j b ⊗[X.O i] LamO X i Q M) :
    p.A.rTensor _ ((ops.map fun o => PqTw Y i j b Q M o.1 (gam Y i Q M o)).prod x) =
      (ops.map fun o => PqTw Y i j b Q M o.1 (gam Y i Q M o)).prod (p.A.rTensor _ x) := by
  induction ops with
  | nil => simp
  | cons o ops ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [rTensor_PqTw i j b Q M o.1 _ p.A (fun k hk => p.comm k o.1
      ⟨(Finset.mem_Icc.1 hk).1, (Finset.mem_Icc.1 hk).2, (hops o List.mem_cons_self).1,
        (hops o List.mem_cons_self).2⟩), ih fun o' ho' => hops o' (List.mem_cons_of_mem _ ho')]

variable (es : Fin n ≃ ↥p.S)

def Pack.f (Q : Finset (PlE D.host)) (M : ℕ) : LamO X i Q M :=
  if p.IntQ Q M then (mxOf β (LamO X i Q M) fun a' => p.w Q M (es a')).det else 0

theorem Pack.intQ_of (Q : Finset (PlE D.host)) (M : ℕ) (hQ : AdmQ Y i Q M)
    (hl : ∀ a ∈ p.S, Disjoint Q (Y.lev i j b a)) : p.IntQ Q M :=
  fun a ha => p.t2 Q M hQ a ha (hl a ha)

theorem Pack.proj_f (hF : FrobEx N) (h12 : AugmentationCompatibility Y) (hi : X.NonzeroIndexPlace i) (hj : j ∈ Finset.Icc 1 D.R.m) (M : ℕ) (Q'' Q : Finset (PlE D.host)) (hs : Q'' ⊆ Q)
    (hQ : AdmQ Y i Q M) (hQ'' : ConjCl Q'') (hl : ∀ a ∈ p.S, Disjoint Q (Y.lev i j b a)) :
    AdmQ Y i Q'' M ∧ ∃ ops : List (Op N), 2 * ops.length = (Q \ Q'').card ∧
      (∀ o ∈ ops, o.1 ∈ Q \ Q'' ∧ (o.2.1 = 1 ∨ o.2.1 = -1) ∧ IsFrob (N.plOm.1 o.1) (normV o.1) o.2.2) ∧
      projA i hs M (p.f β es Q M) =
        (ops.map fun o => (p.Pm β (LamO X i Q'' M) o.1 (grp i Q'' M (gam Y i Q'' M o))).det).prod *
          p.f β es Q'' M := by
  obtain ⟨hA'', ops, hlen, hops, hch⟩ := chain hF h12 i hi M j hj b Q'' Q hs hQ hQ''
  refine ⟨hA'', ops, hlen, hops, ?_⟩
  have hl'' : ∀ a ∈ p.S, Disjoint Q'' (Y.lev i j b a) := fun a ha => Disjoint.mono_left hs (hl a ha)
  have hI := p.intQ_of Q M hQ hl
  have hI'' := p.intQ_of Q'' M hA'' hl''
  have hsp : ∀ o ∈ ops, IsSplitPl D.host o.1 ∧ o.1 ∉ X.S0 i := by
    intro o ho
    have h1 := (Finset.mem_sdiff.1 (hops o ho).1).1
    exact ⟨hQ.1 _ h1, fun h2 => (Finset.disjoint_left.1 hQ.2.1) h1 h2⟩
  rw [Pack.f, if_pos hI, Pack.f, if_pos hI'',
    ← det_mxOf_lTensor β (projA i hs M) (fun a' => hI (es a') (es a').2)]
  have hw : ∀ a ∈ p.S, (projA i hs M).toLinearMap.lTensor (Y.Fm i j b) (p.w Q M a) =
      (ops.map fun o => PqTw Y i j b Q'' M o.1 (gam Y i Q'' M o)).prod (p.w Q'' M a) := by
    intro a ha
    unfold Pack.w
    rw [map_smul, rTensor_lTensor_comm, hch a (hl a ha), map_smul]
    congr 1
    exact p.rTensor_ops Q'' M ops hsp _
  have hfun : (fun a' : Fin n => (projA i hs M).toLinearMap.lTensor (Y.Fm i j b) (p.w Q M (es a'))) =
      fun a' => (ops.map fun o => PqTw Y i j b Q'' M o.1 (gam Y i Q'' M o)).prod (p.w Q'' M (es a')) :=
    funext fun a' => hw (es a') (es a').2
  rw [hfun, det_mxOf_op β _ _ (fun a' => (p.crd_ops β Q'' M ops hsp (hI'' (es a') (es a').2)).2)]
  congr 1
  rw [← Matrix.coe_detMonoidHom, map_list_prod, List.map_map]
  rfl

end Asm1

section K4

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (nval)
open scoped TensorProduct
open Classical

theorem mem_smul_iff_repr {O Fm : Type} [CommRing O] [AddCommGroup Fm] [Module O Fm] {B : Submodule O Fm}
    {d : ℕ} (β : Module.Basis (Fin d) O B) (I : Ideal O) (y : B) :
    (y : Fm) ∈ I • B ↔ ∀ t, β.repr y t ∈ I := by
  constructor
  · intro h
    have key : ∃ hz : (y : Fm) ∈ B, ∀ t, β.repr ⟨(y : Fm), hz⟩ t ∈ I := by
      refine Submodule.smul_induction_on (p := fun z => ∃ hz : z ∈ B, ∀ t, β.repr ⟨z, hz⟩ t ∈ I) h ?_ ?_
      · intro r hr m hm
        refine ⟨B.smul_mem r hm, fun t => ?_⟩
        have : (⟨r • m, B.smul_mem r hm⟩ : B) = r • ⟨m, hm⟩ := rfl
        rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact I.mul_mem_right _ hr
      · rintro x z ⟨hx, h1⟩ ⟨hz, h2⟩
        refine ⟨B.add_mem hx hz, fun t => ?_⟩
        have : (⟨x + z, B.add_mem hx hz⟩ : B) = ⟨x, hx⟩ + ⟨z, hz⟩ := rfl
        rw [this, map_add, Finsupp.add_apply]
        exact I.add_mem (h1 t) (h2 t)
    obtain ⟨_, h1⟩ := key
    exact h1
  · intro h
    have h1 := congrArg B.subtype (β.sum_repr y)
    rw [map_sum] at h1
    rw [show (y : Fm) = B.subtype y from rfl, ← h1]
    refine Submodule.sum_mem _ fun t _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem_smul (h t) (β t).2

theorem matB_commute {O Fm : Type} [CommRing O] [AddCommGroup Fm] [Module O Fm] {B : Submodule O Fm}
    {d : ℕ} (β : Module.Basis (Fin d) O B) (T T' : Module.End O Fm) (hT : B.map T ≤ B) (hT' : B.map T' ≤ B)
    (h : Commute T T') : Commute (matB β T hT) (matB β T' hT') := by
  unfold Commute SemiconjBy matB
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  congr 1
  ext x
  exact LinearMap.congr_fun h.eq x

theorem repr_matB {O Fm : Type} [CommRing O] [AddCommGroup Fm] [Module O Fm] {B : Submodule O Fm}
    {d : ℕ} (β : Module.Basis (Fin d) O B) (T : Module.End O Fm) (hT : B.map T ≤ B) (y : B) (t : Fin d) :
    β.repr ⟨T y, hT ⟨y, y.2, rfl⟩⟩ t = (matB β T hT).mulVec (β.repr y) t := by
  unfold matB
  rw [LinearMap.toMatrix_mulVec_repr]
  rfl

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}
  {i : X.Tw} {j : ℕ} {b : Bool} (p : Pack Y i j b)

theorem Pack.Tk_commute (h13 : HeckeOperatorsCommute Y) (hi : X.NonzeroIndexPlace i) (P P' : PlE D.host) (k k' : ℕ) :
    Commute (p.Tk P k) (p.Tk P' k') := by
  unfold Pack.Tk
  by_cases h : HkIdx i k P
  · by_cases h' : HkIdx i k' P'
    · rw [if_pos h, if_pos h']
      have h0 := h13 i hi j b k k' P P' h h'
      unfold Commute SemiconjBy
      ext x
      exact LinearMap.congr_fun h0.eq x
    · rw [if_neg h']
      exact Commute.zero_right _
  · rw [if_neg h]
    exact Commute.zero_left _

variable {n : ℕ} (β : Module.Basis (Fin n) (X.O i) p.B)

theorem Pack.det_unit (h13 : HeckeOperatorsCommute Y) (hi : X.NonzeroIndexPlace i) {P0 : PlE D.host} (hP0 : IsSplitPl D.host P0 ∧ P0 ∉ X.S0 i)
    (hu : ∀ s : X.Sig i, IsUnit (Pq1 X i s P0)) : IsUnit (p.Pm β (X.O i) P0 1).det := by
  have := X.resO_ac i
  let Tm : ℕ × PlE D.host → Matrix (Fin n) (Fin n) (X.O i) :=
    fun a => matB β (p.Tk a.2 a.1) (p.Tk_stable a.2 a.1)
  let s : Finset (ℕ × PlE D.host) :=
    (Finset.Icc 1 D.R.r).map ⟨fun k => (k, P0), fun a b h => (Prod.ext_iff.1 h).1⟩
  let c : ℕ × PlE D.host → X.O i := fun a => ck X i a.2 a.1
  have hPm : p.Pm β (X.O i) P0 1 = 1 + ∑ a ∈ s, c a • Tm a := by
    unfold Pack.Pm Pmat
    rw [Finset.sum_map]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Algebra.algebraMap_self, RingHom.id_apply, one_pow, mul_one, Tm, c]
    congr 1
  rw [hPm]
  refine det_isUnit_of_eigen Tm (fun a a' => matB_commute β _ _ _ _ (p.Tk_commute h13 hi _ _ _ _)) s c ?_
  rintro x ⟨t0, ht0⟩ ev hev
  let xB : p.B := β.equivFun.symm x
  have hrepr : (β.repr xB : Fin n → X.O i) = x := by
    have := β.equivFun.apply_symm_apply x
    rwa [Module.Basis.equivFun_apply] at this
  have h1 : (xB : Y.Fm i j b) ∉ IsLocalRing.maximalIdeal (X.O i) • p.B := by
    rw [mem_smul_iff_repr β]
    intro h
    exact ht0 (by have := h t0; rwa [hrepr] at this)
  have h2 : ∀ k P, HkIdx i k P → hkO Y i j b k P (xB : Y.Fm i j b) - ev (k, P) • (xB : Y.Fm i j b) ∈
      IsLocalRing.maximalIdeal (X.O i) • p.B := by
    intro k P hk
    have hT : p.Tk P k = hkO Y i j b k P := if_pos hk
    have hmem : p.Tk P k (xB : Y.Fm i j b) ∈ p.B := p.Tk_stable P k ⟨xB, xB.2, rfl⟩
    have he : hkO Y i j b k P (xB : Y.Fm i j b) - ev (k, P) • (xB : Y.Fm i j b) =
        (((⟨p.Tk P k (xB : Y.Fm i j b), hmem⟩ : p.B) - ev (k, P) • xB : p.B) : Y.Fm i j b) := by
      rw [← hT]; rfl
    rw [he, mem_smul_iff_repr β]
    intro t
    have h3 := hev (k, P) t
    rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, repr_matB β (p.Tk P k) (p.Tk_stable P k) xB t,
      hrepr]
    exact h3
  obtain ⟨sg, _, _, hsg⟩ := p.t3 xB xB.2 h1 (fun k P => ev (k, P)) h2
  have hdiff : (1 + ∑ a ∈ s, c a * ev a) - Pq1 X i sg P0 ∈ IsLocalRing.maximalIdeal (X.O i) := by
    unfold Pq1
    rw [Finset.sum_map, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun k hk => ?_
    have hk' := Finset.mem_Icc.1 hk
    have h4 := hsg k P0 ⟨hk'.1, hk'.2, hP0.1, hP0.2⟩
    have : c ((⟨fun k => (k, P0), fun a b h => (Prod.ext_iff.1 h).1⟩ : ℕ ↪ ℕ × PlE D.host) k) *
        ev ((⟨fun k => (k, P0), fun a b h => (Prod.ext_iff.1 h).1⟩ : ℕ ↪ ℕ × PlE D.host) k) -
        (-1 : X.O i) ^ k * ((normV P0 : ℕ) : X.O i) ^ (k * (k - 1) / 2) * X.hEig i sg k P0 =
        ck X i P0 k * (ev (k, P0) - X.hEig i sg k P0) := by
      show ck X i P0 k * ev (k, P0) -
        (-1 : X.O i) ^ k * ((normV P0 : ℕ) : X.O i) ^ (k * (k - 1) / 2) * X.hEig i sg k P0 = _
      unfold ck
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ h4
  by_contra hnu
  have h5 : (1 + ∑ a ∈ s, c a * ev a) ∈ IsLocalRing.maximalIdeal (X.O i) :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  have h6 : Pq1 X i sg P0 ∈ IsLocalRing.maximalIdeal (X.O i) := by
    have := (IsLocalRing.maximalIdeal (X.O i)).sub_mem h5 hdiff
    rwa [sub_sub_cancel] at this
  exact (IsLocalRing.mem_maximalIdeal _).1 h6 (hu sg)

end K4

section Asm2

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (nval)
open scoped TensorProduct
open Classical

theorem mem_baseChange_of_smul {O K Fm R' : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm] [CommRing R']
    [Algebra O R'] (V : Submodule K Fm) (c0 : O) (hc : c0 ≠ 0) (t : R' ⊗[O] Fm)
    (h : c0 • t ∈ (V.restrictScalars O).baseChange R') : t ∈ (V.restrictScalars O).baseChange R' := by
  let μ : Fm →ₗ[O] Fm := ((algebraMap O K c0)⁻¹ • (LinearMap.id : Fm →ₗ[K] Fm)).restrictScalars O
  have h1 : (V.restrictScalars O).map μ ≤ V.restrictScalars O := by
    rintro _ ⟨x, hx, rfl⟩
    exact V.smul_mem _ hx
  have h2 := Formalism.MainNotions.IntegralHeckeForms.map_baseChange_le R' μ h1 ⟨c0 • t, h, rfl⟩
  have hc' : algebraMap O K c0 ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
  have h3 : ∀ t : R' ⊗[O] Fm, (μ.baseChange R') (c0 • t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a f =>
      rw [← TensorProduct.tmul_smul, LinearMap.baseChange_tmul]
      congr 1
      show (algebraMap O K c0)⁻¹ • (c0 • f) = f
      rw [← algebraMap_smul K c0 f, smul_smul, inv_mul_cancel₀ hc', one_smul]
    | add x y hx hy => rw [smul_add, map_add, hx, hy]
  rwa [h3 t] at h2

theorem mem_of_intIn_tmul_one {O Fm Λ : Type} [CommRing O] [AddCommGroup Fm] [Module O Fm] [CommRing Λ]
    [Algebra O Λ] {B : Submodule O Fm} (φ : Λ →ₐ[O] O) {x : Fm} (h : IntIn B Λ (x ⊗ₜ[O] (1 : Λ))) : x ∈ B := by
  obtain ⟨W, hW⟩ := h
  let ρ : Fm ⊗[O] Λ →ₗ[O] Fm := (TensorProduct.rid O Fm).toLinearMap ∘ₗ φ.toLinearMap.lTensor Fm
  have h1 : ρ (x ⊗ₜ[O] (1 : Λ)) = x := by simp [ρ]
  have h2 : ∀ W : B ⊗[O] Λ, ρ (B.subtype.rTensor Λ W) ∈ B := by
    intro W
    induction W using TensorProduct.induction_on with
    | zero => simp
    | tmul y lam =>
      have : ρ (B.subtype.rTensor Λ (y ⊗ₜ lam)) = φ lam • (y : Fm) := by simp [ρ]
      rw [this]
      exact B.smul_mem _ y.2
    | add a b ha hb => rw [map_add, map_add]; exact B.add_mem ha hb
  rw [← h1, ← hW]
  exact h2 W

theorem linearIndependent_smul_of_ne_zero {R W ι : Type} [CommRing R] [IsDomain R] [AddCommGroup W] [Module R W]
    {v : ι → W} (hv : LinearIndependent R v) {c : R} (hc : c ≠ 0) : LinearIndependent R (fun a => c • v a) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg a ha
  have := hv s (fun a => g a * c) (by simpa [mul_smul] using hg) a ha
  exact (mul_eq_zero.1 this).resolve_right hc

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}
  {i : X.Tw} {j : ℕ} {b : Bool} (p : Pack Y i j b)

theorem l_ne_zero (i : X.Tw) [CharZero (FractionRing (X.O i))] : ((X.l i : ℕ) : X.O i) ≠ 0 := by
  intro h
  have h1 : ((X.l i : ℕ) : FractionRing (X.O i)) = 0 := by
    rw [← map_natCast (algebraMap (X.O i) (FractionRing (X.O i))), h, map_zero]
  exact (X.lPrime i).out.ne_zero (by exact_mod_cast h1)

theorem addVal_l_pos_O (i : X.Tw) [CharZero (FractionRing (X.O i))] :
    0 < (IsDiscreteValuationRing.addVal (X.O i) ((X.l i : ℕ) : X.O i)).toNat := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.O i)
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (l_ne_zero i) hϖ
  rw [IsDiscreteValuationRing.addVal_def _ u hϖ m hu, ENat.toNat_natCast]
  rcases Nat.eq_zero_or_pos m with rfl | h
  · exfalso
    have h1 := X.O_l i
    rw [hu, pow_zero, mul_one] at h1
    exact (IsLocalRing.mem_maximalIdeal _).1 h1 u.isUnit
  · exact h

theorem Pack.exists_basis : ∃ (n : ℕ) (_ : Module.Basis (Fin n) (X.O i) p.B), Nonempty (Fin n ≃ ↥p.S) := by
  have : Module.Finite (X.O i) p.B := Module.Finite.iff_fg.2 p.fg
  have : Module.IsTorsionFree (X.O i) (Y.Fm i j b) :=
    Module.IsTorsionFree.trans_faithfulSMul (X.O i) (FractionRing (X.O i)) (Y.Fm i j b)
  obtain ⟨n, β⟩ := Module.basisOfFiniteTypeTorsionFree' (R := X.O i) (M := p.B)
  refine ⟨n, β, ?_⟩
  have h1 : LinearIndependent (FractionRing (X.O i)) (fun t => (β t : Y.Fm i j b)) :=
    (LinearIndependent.iff_fractionRing (X.O i) (FractionRing (X.O i))).1 (linearIndependent_basis_coe β)
  have h2 : LinearIndependent (FractionRing (X.O i)) (fun a : ↥p.S => p.A (Y.th i j b a)) :=
    (LinearIndependent.iff_fractionRing (X.O i) (FractionRing (X.O i))).1 p.li
  have e1 := finrank_span_eq_card h1
  have e2 := finrank_span_eq_card h2
  have hs : Submodule.span (FractionRing (X.O i)) (Set.range fun t => (β t : Y.Fm i j b)) =
      Submodule.span (FractionRing (X.O i)) (Set.range fun a : ↥p.S => p.A (Y.th i j b a)) := by
    rw [← Submodule.span_span_of_tower (X.O i), span_basis_eq β, ← p.spn, Set.image_eq_range]
    rfl
  exact ⟨Fintype.equivOfCardEq (by rw [← e1, hs, e2])⟩

variable {n : ℕ} (β : Module.Basis (Fin n) (X.O i) p.B) (es : Fin n ≃ ↥p.S)

include es in
theorem Pack.card_eq : (n : ℝ) = p.S.card := by
  have := Fintype.card_congr es
  rw [Fintype.card_fin, Fintype.card_coe] at this
  exact_mod_cast this

theorem Pack.range_es {T : Type} (g : Y.Dat i j b → T) : Set.range (fun a' => g (es a')) = g '' ↑p.S := by
  ext x
  constructor
  · rintro ⟨a', rfl⟩
    exact ⟨es a', (es a').2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨es.symm ⟨a, ha⟩, by simp⟩

theorem Pack.isLatIn_Bk (k : ℕ) : IsLatIn (p.B.baseChange (X.Ok i k)) (p.VKk k) :=
  Formalism.MainNotions.IntegralHeckeForms.isLatIn_baseChange (X.Ok i k) (X.Ok_inj i k) _ _ (isLatIn_spanK p.fg)

theorem Pack.eval [CharZero (FractionRing (X.O i))] (Q : Finset (PlE D.host)) (M k : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (h : evA i Q M k χ (p.f β es Q M) ≠ 0) :
    IsLatIn (p.Yl Q M k χ) (p.VKk k) ∧
      sIdx (X.l i) (p.B.baseChange (X.Ok i k)) (p.Yl Q M k χ) =
        nval (X.Ok i k) (X.l i) (evA i Q M k χ (p.f β es Q M)) - (p.c : ℝ) * p.S.card := by
  have hI : p.IntQ Q M := by
    by_contra hI
    apply h
    rw [Pack.f, if_neg hI, map_zero]
  rw [Pack.f, if_pos hI] at h ⊢
  have hV := p.isLatIn_Bk k
  obtain ⟨hli, hlat, hidx⟩ := sIdx_spec β (X.Ok_inj i k) (X.l i) (evA i Q M k χ)
    (fun a' => hI (es a') (es a').2) h hV
  have hpos := Formalism.MainNotions.IntegralHeckeForms.addVal_l_pos (X := X) i k
  have hl0 : ((X.l i : ℕ) : X.Ok i k) ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hz : ∀ a', (TensorProduct.comm (X.O i) (Y.Fm i j b) (X.Ok i k))
      ((evA i Q M k χ).toLinearMap.lTensor (Y.Fm i j b) (p.w Q M (es a'))) =
        ((X.l i : X.O i) ^ p.c) • p.y Q M k χ (es a') := by
    intro a'
    unfold Pack.w Pack.y
    rw [map_smul, map_smul, rTensor_lTensor_comm, ← baseChange_comm, ← specU_eq]
  have hyz : ∀ a', (((X.l i : ℕ) : X.Ok i k) ^ p.c) • p.y Q M k χ (es a') =
      (TensorProduct.comm (X.O i) (Y.Fm i j b) (X.Ok i k))
        ((evA i Q M k χ).toLinearMap.lTensor (Y.Fm i j b) (p.w Q M (es a'))) := by
    intro a'
    rw [hz, ← algebraMap_smul (X.Ok i k) ((X.l i : X.O i) ^ p.c), map_pow, map_natCast]
  have hy : ∀ a', p.y Q M k χ (es a') ∈ p.VKk k := by
    intro a'
    refine mem_baseChange_of_smul _ ((X.l i : X.O i) ^ p.c) (pow_ne_zero _ (l_ne_zero i)) _ ?_
    rw [← hz]
    exact hlat.2.1 (Submodule.subset_span ⟨a', rfl⟩)
  have hs := sIdx_of_smul (X.l i) (pow_ne_zero p.c hl0) hyz hli hlat hy hV
  have hr := p.range_es es (p.y Q M k χ)
  unfold Pack.Yl
  rw [← hr]
  refine ⟨isLatIn_of_smul hyz hlat hy, ?_⟩
  rw [hs, hidx, nval_pow_self _ _ hpos, p.card_eq es, mul_comm]

def Pack.x (a : Y.Dat i j b) : Y.Fm i j b := ((X.l i : X.O i) ^ p.c) • p.A (Y.th i j b a)

theorem Pack.w_empty (h12 : AugmentationCompatibility Y) (hi : X.NonzeroIndexPlace i) (hj : j ∈ Finset.Icc 1 D.R.m) (M : ℕ) (a : Y.Dat i j b) :
    p.w ∅ M a = p.x a ⊗ₜ[X.O i] (1 : LamO X i ∅ M) := by
  unfold Pack.w Pack.x
  rw [((h12 i hi M).2 j hj b).1 a, LinearMap.rTensor_tmul, TensorProduct.smul_tmul']

theorem Pack.x_mem (h12 : AugmentationCompatibility Y) (hi : X.NonzeroIndexPlace i) (hj : j ∈ Finset.Icc 1 D.R.m) (a : Y.Dat i j b) (ha : a ∈ p.S) : p.x a ∈ p.B := by
  refine mem_of_intIn_tmul_one (augA i ∅ 0) ?_
  rw [← p.w_empty h12 hi hj]
  exact p.t2 ∅ 0 (admissible_empty_places i 0) a ha (Finset.disjoint_empty_left _)

theorem Pack.x_li [CharZero (FractionRing (X.O i))] :
    LinearIndependent (X.O i) (fun a' : Fin n => p.x (es a')) :=
  linearIndependent_smul_of_ne_zero (p.li.comp es es.injective) (pow_ne_zero _ (l_ne_zero i))

theorem Pack.aug_f_empty (h12 : AugmentationCompatibility Y) (hi : X.NonzeroIndexPlace i) (hj : j ∈ Finset.Icc 1 D.R.m) (M : ℕ) :
    augA i ∅ M (p.f β es ∅ M) =
      (mxB β (fun a' => p.x (es a')) (fun a' => p.x_mem h12 hi hj _ (es a').2)).det := by
  have hI : p.IntQ ∅ M := p.intQ_of ∅ M (admissible_empty_places i M) fun a _ => Finset.disjoint_empty_left _
  rw [Pack.f, if_pos hI]
  have : mxOf β (LamO X i ∅ M) (fun a' => p.w ∅ M (es a')) =
      (mxB β (fun a' => p.x (es a')) (fun a' => p.x_mem h12 hi hj _ (es a').2)).map
        (algebraMap (X.O i) (LamO X i ∅ M)) := by
    refine Matrix.ext fun t a' => ?_
    show crd β (LamO X i ∅ M) (p.w ∅ M (es a')) t = _
    rw [p.w_empty h12 hi hj, (crd_tmul_one β (p.x_mem h12 hi hj _ (es a').2)).2]
    rfl
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det, AlgHom.commutes]
  rfl

theorem Pack.v_eq [CharZero (FractionRing (X.O i))] (h12 : AugmentationCompatibility Y) (hi : X.NonzeroIndexPlace i) (hj : j ∈ Finset.Icc 1 D.R.m) :
    p.v = nval (X.O i) (X.l i)
      (mxB β (fun a' => p.x (es a')) (fun a' => p.x_mem h12 hi hj _ (es a').2)).det := by
  have hx := fun a' : Fin n => p.x_mem h12 hi hj _ (es a').2
  have hli := p.x_li es
  have hB : IsLatIn p.B ((Submodule.span (FractionRing (X.O i)) (p.B : Set (Y.Fm i j b))).restrictScalars
      (X.O i)) := isLatIn_spanK p.fg
  have h1 := sIdx_mxB β (X.l i) (fun a' => p.x (es a')) hx hli
  have hzV : IsLatIn (Submodule.span (X.O i) (Set.range fun a' => p.x (es a')))
      ((Submodule.span (FractionRing (X.O i)) (p.B : Set (Y.Fm i j b))).restrictScalars (X.O i)) := by
    rw [eq_vecOf_mxB β (fun a' => p.x (es a')) hx]
    refine isLatIn_vecOf ?_ (det_mxB_ne_zero β _ hx hli)
    rw [span_basis_eq β]
    exact hB
  have hy : ∀ a' : Fin n, p.A (Y.th i j b (es a')) ∈
      (Submodule.span (FractionRing (X.O i)) (p.B : Set (Y.Fm i j b))).restrictScalars (X.O i) := by
    intro a'
    show _ ∈ Submodule.span (FractionRing (X.O i)) (p.B : Set (Y.Fm i j b))
    rw [← p.spn]
    exact Submodule.subset_span ⟨es a', (es a').2, rfl⟩
  have h2 := sIdx_of_smul (y := fun a' : Fin n => p.A (Y.th i j b (es a'))) (z := fun a' => p.x (es a'))
    (X.l i) (pow_ne_zero p.c (l_ne_zero i)) (fun a' => rfl) hli hzV hy hB
  rw [p.range_es es (fun a => p.A (Y.th i j b a))] at h2
  unfold Pack.v Pack.Th
  rw [h2, h1, nval_pow_self _ _ (addVal_l_pos_O i), p.card_eq es]
  ring

end Asm2

section Asm3

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (nval)
open scoped TensorProduct
open Classical

theorem list_prod_cancel {R ι : Type} [CommRing R] (l : List ι) (d U U' : ι → R)
    (h : ∀ o ∈ l, U o * U' o = 1) :
    (l.map fun o => d o * U' o).prod * (l.map U).prod = (l.map d).prod := by
  induction l with
  | nil => simp
  | cons o l ih =>
    simp only [List.map_cons, List.prod_cons]
    have h1 := h o List.mem_cons_self
    have h2 := ih fun o' ho' => h o' (List.mem_cons_of_mem _ ho')
    calc d o * U' o * (l.map fun o => d o * U' o).prod * (U o * (l.map U).prod)
        = d o * (U o * U' o) * ((l.map fun o => d o * U' o).prod * (l.map U).prod) := by ring
      _ = _ := by rw [h1, h2, mul_one]

theorem length_flatMap_le {ι κ : Type} (l : List ι) (f : ι → List κ) (c : ℕ) (h : ∀ o ∈ l, (f o).length ≤ c) :
    (l.flatMap f).length ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons o l ih =>
    have h1 := h o List.mem_cons_self
    have h2 := ih fun o' ho' => h o' (List.mem_cons_of_mem _ ho')
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

theorem prod_flatMap_map {R ι κ : Type} [CommRing R] (l : List ι) (f : ι → List κ) (F : κ → R) :
    ((l.flatMap f).map F).prod = (l.map fun o => ((f o).map F).prod).prod := by
  induction l with
  | nil => simp
  | cons o l ih => simp only [List.flatMap_cons, List.map_append, List.prod_append, List.map_cons,
      List.prod_cons, ih]

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}
  {i : X.Tw} {j : ℕ} {b : Bool} (p : Pack Y i j b) {n : ℕ} (β : Module.Basis (Fin n) (X.O i) p.B)
  (es : Fin n ≃ ↥p.S)

theorem Pack.factor_op [IsAlgClosed (IsLocalRing.ResidueField (X.O i))] (Q : Finset (PlE D.host)) (M : ℕ)
    (o : Op N) (ho : o.2.1 = 1 ∨ o.2.1 = -1) :
    ∃ (L : List (X.O i)) (U U' : LamO X i Q M), L.length ≤ D.R.r * n ∧ U * U' = 1 ∧
      IsUnit (augA i Q M U) ∧
      (p.Pm β (LamO X i Q M) o.1 (grp i Q M (gam Y i Q M o))).det * U' -
        (L.map fun α => 1 - α • grp i Q M (Multiplicative.toAdd (Y.delU i Q M o.2.2))).prod ∈
        Ideal.map (algebraMap (X.O i) (LamO X i Q M)) (IsLocalRing.maximalIdeal (X.O i)) := by
  set γ := Multiplicative.toAdd (Y.delU i Q M o.2.2) with hγ
  rcases ho with h | h
  · obtain ⟨L, hL, hd⟩ := det_Pmat_factor (LamO X i Q M) D.R.r (ck X i o.1)
      (fun k => matB β (p.Tk o.1 k) (p.Tk_stable o.1 k)) (grp i Q M γ)
    refine ⟨L, 1, 1, hL, one_mul 1, by simp, ?_⟩
    have : gam Y i Q M o = γ := by unfold gam; rw [h, one_smul]
    rw [this, mul_one]
    exact hd
  · obtain ⟨L, ε, m, hL, hd⟩ := det_Pmat_factor_inv (LamO X i Q M) D.R.r (ck X i o.1)
      (fun k => matB β (p.Tk o.1 k) (p.Tk_stable o.1 k)) (grp i Q M γ) (grp i Q M (-γ)) (grp_mul_neg i Q M γ)
    have hUU : ((ε : X.O i) • grp i Q M (-γ) ^ m) * (((ε⁻¹ : (X.O i)ˣ) : X.O i) • grp i Q M γ ^ m) = 1 := by
      rw [smul_mul_smul_comm, ← mul_pow, mul_comm (grp i Q M (-γ)), grp_mul_neg, one_pow, Units.mul_inv,
        one_smul]
    refine ⟨L, (ε : X.O i) • grp i Q M (-γ) ^ m, ((ε⁻¹ : (X.O i)ˣ) : X.O i) • grp i Q M γ ^ m, hL, hUU, ?_, ?_⟩
    · rw [map_smul, map_pow, augA_grp, one_pow, smul_eq_mul, mul_one]
      exact ε.isUnit
    · have : gam Y i Q M o = -γ := by unfold gam; rw [h, neg_smul, one_smul]
      rw [this]
      set dd := (p.Pm β (LamO X i Q M) o.1 (grp i Q M (-γ))).det with hdd
      set U := (ε : X.O i) • grp i Q M (-γ) ^ m with hU
      set U' := ((ε⁻¹ : (X.O i)ˣ) : X.O i) • grp i Q M γ ^ m with hU'
      set pr := (L.map fun α => 1 - α • grp i Q M γ).prod with hpr
      have e : dd * U' - pr = U' * (dd - U * pr) + (U * U' - 1) * pr := by ring
      rw [e, hUU, sub_self, zero_mul, add_zero]
      exact Ideal.mul_mem_left _ _ hd

theorem Pack.good [CharZero (FractionRing (X.O i))] (hF : FrobEx N) (h12 : AugmentationCompatibility Y) (hi : X.NonzeroIndexPlace i)
    (hj : j ∈ Finset.Icc 1 D.R.m)
    (hK4 : ∀ P0 : PlE D.host, IsSplitPl D.host P0 ∧ P0 ∉ X.S0 i → (∀ s : X.Sig i, IsUnit (Pq1 X i s P0)) →
      IsUnit (p.Pm β (X.O i) P0 1).det)
    (A0 : Finset (PlE D.host)) (hA0 : ∀ a ∈ p.S, Y.lev i j b a ⊆ A0) : Good Y i A0 (p.f β es) p.v := by
  have := X.resO_ac i
  refine ⟨D.R.r * n, fun M Q'' Q hs hStep => ?_⟩
  obtain ⟨hsp, hdis, hcQ, hcQ'', hdel, hun, hcls⟩ := hStep
  have hd1 : Disjoint Q (X.S0 i) := Disjoint.mono_right Finset.subset_union_left hdis
  have hl : ∀ a ∈ p.S, Disjoint Q (Y.lev i j b a) := fun a ha =>
    Disjoint.mono_right ((hA0 a ha).trans Finset.subset_union_right) hdis
  have hQ : AdmQ Y i Q M := ⟨hsp, hd1, hcQ, hdel, hcls⟩
  obtain ⟨hA'', ops, hlen, hops, hproj⟩ := p.proj_f β es hF h12 hi hj M Q'' Q hs hQ hcQ'' hl
  have hfac := fun o (ho : o ∈ ops) => p.factor_op β Q'' M o (hops o ho).2.1
  choose! Lf Uf Uf' hL hUU hUa hcong using hfac
  have hl'' : ∀ a ∈ p.S, Disjoint Q'' (Y.lev i j b a) := fun a ha => Disjoint.mono_left hs (hl a ha)
  obtain ⟨_, ops0, _, hops0, hproj0⟩ := p.proj_f β es hF h12 hi hj M ∅ Q'' (Finset.empty_subset _) hA''
    (fun P hP => by simp at hP) hl''
  set M0 := mxB β (fun a' => p.x (es a')) (fun a' => p.x_mem h12 hi hj _ (es a').2) with hM0
  have haug : augA i Q'' M (p.f β es Q'' M) =
      (ops0.map fun o => (p.Pm β (X.O i) o.1 1).det).prod * M0.det := by
    rw [augA_comp i (Finset.empty_subset Q'') M, AlgHom.comp_apply, hproj0, map_mul,
      p.aug_f_empty β es h12 hi hj, map_list_prod, List.map_map]
    congr 2
    refine List.map_congr_left fun o _ => ?_
    show augA i ∅ M (Pmat _ _ _ _).det = (Pmat _ _ _ _).det
    rw [det_Pmat_map, augA_grp]
  have hu0 : IsUnit (ops0.map fun o => (p.Pm β (X.O i) o.1 1).det).prod := by
    refine List.prod_isUnit fun m hm => ?_
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hm
    have hoQ := (Finset.mem_sdiff.1 (hops0 o ho).1).1
    exact hK4 o.1 ⟨hA''.1 _ hoQ, fun h2 => (Finset.disjoint_left.1 hA''.2.1) hoQ h2⟩ (hun o.1 hoQ)
  have hu1 : IsUnit (ops.map fun o => augA i Q'' M (Uf o)).prod := by
    refine List.prod_isUnit fun m hm => ?_
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hm
    exact hUa o ho
  have haugg : augA i Q'' M ((ops.map Uf).prod * p.f β es Q'' M) =
      (ops.map fun o => augA i Q'' M (Uf o)).prod *
        ((ops0.map fun o => (p.Pm β (X.O i) o.1 1).det).prod * M0.det) := by
    rw [map_mul, haug, map_list_prod, List.map_map]
    rfl
  have hdet0 : M0.det ≠ 0 := det_mxB_ne_zero β _ _ (p.x_li es)
  refine ⟨(ops.map fun o => (p.Pm β (LamO X i Q'' M) o.1 (grp i Q'' M (gam Y i Q'' M o))).det * Uf' o).prod,
    (ops.map Uf).prod * p.f β es Q'' M, ?_, ?_, ?_,
    ops.flatMap fun o => (Lf o).map fun α => (α, Multiplicative.toAdd (Y.delU i Q'' M o.2.2)), ?_, ?_, ?_⟩
  · rw [hproj, ← mul_assoc, list_prod_cancel ops _ Uf Uf' hUU]
  · rw [haugg]
    exact mul_ne_zero hu1.ne_zero (mul_ne_zero hu0.ne_zero hdet0)
  · rw [haugg, nval_unit_mul _ _ hu1, nval_unit_mul _ _ hu0, p.v_eq β es h12 hi hj]
  · refine (length_flatMap_le ops _ (D.R.r * n) fun o ho => ?_).trans ?_
    · rw [List.length_map]
      exact hL o ho
    · rw [mul_comm]
      exact Nat.mul_le_mul_left _ (by omega)
  · intro q hq
    obtain ⟨o, ho, hq'⟩ := List.mem_flatMap.1 hq
    obtain ⟨α, _, rfl⟩ := List.mem_map.1 hq'
    exact ⟨o.1, (hops o ho).1, o.2.2, (hops o ho).2.2, rfl⟩
  · rw [prod_flatMap_map]
    refine list_prod_congr _ ops _ _ fun o ho => ?_
    rw [List.map_map]
    exact hcong o ho

end Asm3

section Fin

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt nval SetHyp PsiOk partA partAT partC partD)
open scoped TensorProduct

theorem sIdx_mono' {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W]
    [Module R W] (l : ℕ) {B0 Y T V : Submodule R W} (hB : IsLatIn B0 V) (hY : IsLatIn Y V)
    (hT : IsLatIn T V) (h : Y ≤ T) : sIdx l B0 T ≤ sIdx l B0 Y := by
  have a := Formalism.MainNotions.IntegralHeckeForms.Idx.sIdx_add hB hT hY
  have h0 : Formalism.IrreducibleCountingLemmas.TW.relLen Y T = 0 := Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_of_le h
  have h1 : 0 ≤ Formalism.IrreducibleCountingLemmas.TW.sIdx T Y := by
    unfold Formalism.IrreducibleCountingLemmas.TW.sIdx
    rw [h0]
    simp
  have h2 : Formalism.IrreducibleCountingLemmas.TW.sIdx B0 T ≤ Formalism.IrreducibleCountingLemmas.TW.sIdx B0 Y := by omega
  rw [Formalism.MainNotions.IntegralHeckeForms.Idx.sIdx_eq, Formalism.MainNotions.IntegralHeckeForms.Idx.sIdx_eq]
  exact div_le_div_of_nonneg_right (by exact_mod_cast h2) (Nat.cast_nonneg _)

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}

abbrev JB (D : Formalism.BasicNotions.D7) : Type := ↥(Finset.Icc 1 D.R.m) × Bool

theorem Pack.isLatIn_B {i : X.Tw} {j : ℕ} {b : Bool} (p : Pack Y i j b) (k : ℕ) :
    IsLatIn (p.B.baseChange (X.Ok i k)) (p.VKk k) := by
  unfold Pack.VKk
  rw [Formalism.MainNotions.IntegralHeckeForms.Idx.baseChange_eq_ext, Formalism.MainNotions.IntegralHeckeForms.Idx.baseChange_eq_ext]
  exact Formalism.MainNotions.IntegralHeckeForms.Idx.isLatIn_ext (X.Ok_inj i k) _ (isLatIn_spanK p.fg)

open Classical in

theorem run_packs (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (N0 : X.Tw → ℕ) (h2 : SelmerSeriesChoice Y bkP N0) (i : X.Tw) (hi : X.NonzeroIndexPlace i)
    (hS : SetHyp bkP i) (eps' : ℝ) (he : 0 < eps') (A0 : Finset (PlE D.host))
    (pk : ∀ x : JB D, Pack Y i x.1.1 x.2) (hmain : ∀ x, (pk x).Main) :
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (M : ℕ)
      (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k')ˣ),
      PsiOk i A0 Q k' ψ' ∧ (∀ x, ∀ a ∈ (pk x).S, Disjoint Q (Y.lev i x.1.1 x.2 a)) ∧
      ψ'.comp (X.art i Q) = χ.comp (Y.delU i Q M) ∧
      partA bkP i Q k' ψ' eps' ∧ partAT bkP i Q k' ψ' eps' ∧
      partC N0 i Q k' ψ' eps' ∧ partD i Q k' ψ' eps' ∧
      ∃ epsB : ℕ → Bool → ℝ, (∀ j b, 0 ≤ epsB j b) ∧
        ∑ j ∈ Finset.Icc 1 D.R.m, ∑ b : Bool, epsB j b ≤ eps' ∧
        ∀ x : JB D, IsLatIn ((pk x).Yl Q M k' (psiAt x.2 χ)) ((pk x).VKk k') ∧
          sIdx (X.l i) ((pk x).B.baseChange (X.Ok i k')) ((pk x).Yl Q M k' (psiAt x.2 χ)) ≤
            sIdx (X.l i) (pk x).B (pk x).Th + epsB x.1.1 x.2 := by
  choose f hv hGood hEv using hmain
  let e : JB D ≃ Fin (Fintype.card (JB D)) := Fintype.equivFin (JB D)
  let A0' : Finset (PlE D.host) :=
    A0 ∪ (Finset.univ : Finset (JB D)).biUnion fun x => (pk x).S.biUnion (Y.lev i x.1.1 x.2)
  let vv : JB D → ℝ := fun x => (pk x).v
  have hlev : ∀ x, ∀ a ∈ (pk x).S, Y.lev i x.1.1 x.2 a ⊆ A0' := by
    intro x a ha P hP
    refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, ?_⟩)
    exact Finset.mem_biUnion.2 ⟨a, ha, hP⟩
  obtain ⟨Q, k', ψ', M, χ, hPsi, hχ, hA, hAT, hC, hD, ep, hep0, hepS, hlast⟩ :=
    h2 i hi hS eps' he A0' (Fintype.card (JB D)) (fun y => (e.symm y).2) (fun y => f (e.symm y))
      (fun y => vv (e.symm y)) (fun y => hv (e.symm y)) (fun y => hGood (e.symm y) A0' (hlev (e.symm y)))
  have hdisj : Disjoint Q A0' := (Finset.disjoint_union_right.1 hPsi.2.1).2
  have hPsi0 : PsiOk i A0 Q k' ψ' := by
    refine ⟨hPsi.1, ?_, hPsi.2.2⟩
    refine Finset.disjoint_union_right.2 ⟨(Finset.disjoint_union_right.1 hPsi.2.1).1, ?_⟩
    exact Finset.disjoint_of_subset_right Finset.subset_union_left hdisj
  refine ⟨Q, k', ψ', M, χ, hPsi0, fun x a ha => Finset.disjoint_of_subset_right (hlev x a ha) hdisj, hχ,
    hA, hAT, hC, hD, fun j b => if h : j ∈ Finset.Icc 1 D.R.m then ep (e (⟨j, h⟩, b)) else 0, ?_, ?_, ?_⟩
  · intro j b
    dsimp only
    split_ifs
    · exact hep0 _
    · exact le_rfl
  · have h1 : ∑ j ∈ Finset.Icc 1 D.R.m, ∑ b : Bool,
        (if h : j ∈ Finset.Icc 1 D.R.m then ep (e (⟨j, h⟩, b)) else 0) = ∑ y, ep y := by
      rw [← Finset.sum_coe_sort (Finset.Icc 1 D.R.m)
        (fun j => ∑ b : Bool, (if h : j ∈ Finset.Icc 1 D.R.m then ep (e (⟨j, h⟩, b)) else 0)),
        ← e.sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
      rw [dif_pos j.2]
    rw [h1]
    exact hepS
  · intro x
    have h3 := hlast (e x)
    simp only [Equiv.symm_apply_apply] at h3
    obtain ⟨hl, hi⟩ := hEv x Q M k' (psiAt x.2 χ) h3.1
    refine ⟨hl, ?_⟩
    rw [hi]
    show _ ≤ _ + (if h : x.1.1 ∈ Finset.Icc 1 D.R.m then ep (e (⟨x.1.1, h⟩, x.2)) else 0)
    rw [dif_pos x.1.2]
    have h4 : vv x = sIdx (X.l i) (pk x).B (pk x).Th + ((pk x).c : ℝ) * (pk x).S.card := rfl
    have h5 := h3.2
    rw [h4] at h5
    have h6 : ((⟨x.1.1, x.1.2⟩ : ↥(Finset.Icc 1 D.R.m)), x.2) = x := rfl
    rw [h6]
    linarith

def packR {i : X.Tw} (F : RFam Y i) (j : ℕ) (b : Bool) (h : RHyp Y i F j b) : Pack Y i j b where
  B := F.B j b
  A := F.A j b
  S := F.S j b
  c := h.2.2.2.2.2.2.2.2.1.choose
  fg := h.1
  hkB := h.2.1
  comm := h.2.2.2.1
  li := h.2.2.2.2.2.1
  spn := by
    rw [← Submodule.span_span_of_tower (X.O i) (FractionRing (X.O i)), h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1]
    rfl
  t2 := fun Q M hQ a ha hd => h.2.2.2.2.2.2.2.2.1.choose_spec Q M hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2.1 a ha hd
  t3 := h.2.2.2.2.2.2.2.2.2.1

theorem general_bound_of_lattice_pack (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (N0 : X.Tw → ℕ)
    (hmain : ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b (p : Pack Y i j b), p.Main) (h2 : SelmerSeriesChoice Y bkP N0) (h11 : Formalism.MainNotions.IntegralHeckeForms.TwistedSeriesSpecialisation Y)
    (i : X.Tw) (hiW : X.NonzeroIndexPlace i) : TwistTheoremAtIndex Y bkP N0 i := by
  intro hS eps' he F hF A0
  obtain ⟨Q, k', ψ', M, χ, hPsi, hdis, hχ, hA, hAT, hC, hD, epsB, h0, hs, hb⟩ :=
    run_packs bkP N0 h2 i hiW hS eps' he A0 (fun x => packR F x.1.1 x.2 (hF x.1.1 x.1.2 x.2))
      (fun x => hmain i hiW x.1.1 x.1.2 x.2 _)
  refine ⟨Q, k', ψ', hPsi, hA, hAT, ⟨epsB, h0, hs, ?_⟩, hC, hD⟩
  intro j hj b
  have hR := hF j hj b
  obtain ⟨hl, hi⟩ := hb (⟨j, hj⟩, b)
  have hTw : TwOK i k' Q (psiAt b (ψ'.comp (X.art i Q))) :=
    Formalism.MainNotions.IntegralHeckeForms.TwOK_psiAt b (Formalism.MainNotions.IntegralHeckeForms.TwOK_of_PsiOk hPsi)
  have hψ : psiAt b (ψ'.comp (X.art i Q)) = (psiAt b χ).comp (Y.delU i Q M) := by
    rw [hχ, Formalism.MainNotions.IntegralHeckeForms.psiAt_comp]

  have hfg : (F.ThPsi j b k' Q (psiAt b (ψ'.comp (X.art i Q)))).FG := by
    have hle := hR.2.2.2.2.2.2.2.2.2.2.1 k' Q _ hTw
    have hfg0 := ((Y.MtLat_fg i j b k' Q (psiAt b (ψ'.comp (X.art i Q)))).map
      (Y.thP i j b k' Q (psiAt b (ψ'.comp (X.art i Q))))).map ((F.kap j b).baseChange (X.Ok i k'))
    have := isNoetherian_of_fg_of_noetherian _ hfg0
    exact (isNoetherian_submodule.1 this) _ hle

  have hle : (packR F j b hR).Yl Q M k' (psiAt b χ) ≤ F.ThPsi j b k' Q (psiAt b (ψ'.comp (X.art i Q))) := by
    unfold Pack.Yl
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a ∈ F.S j b := ha
    have h3 := h11 i hiW j hj b k' Q M (psiAt b χ) (hψ ▸ hTw) a (hdis (⟨j, hj⟩, b) a ha')
    rw [hψ]
    refine ⟨_, ?_, rfl⟩
    refine Submodule.span_mono ?_ h3
    intro z hz
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hz ⊢
    obtain ⟨a', rfl, hz⟩ := hz
    exact ⟨a', hR.2.2.2.2.1 ha', hz⟩
  have hlat : IsLatIn (F.ThPsi j b k' Q (psiAt b (ψ'.comp (X.art i Q)))) (F.VKk j b k') :=
    Formalism.MainNotions.IntegralHeckeForms.Idx.isLatIn_of_le hl hfg hle (hR.2.2.2.2.2.2.2.2.2.2.2 k' Q _ hTw)
  refine ⟨hlat, ?_⟩
  have hmono := sIdx_mono' (X.l i) ((packR F j b hR).isLatIn_B k') hl hlat hle
  have hTh : (packR F j b hR).Th = F.Th j b := hR.2.2.2.2.2.2.1
  rw [hTh] at hi
  exact hmono.trans hi

def packAB {i : X.Tw} (F : Formalism.MainNotions.IntegralHeckeForms.RFam Y i) (j : ℕ) (b : Bool) (h : Formalism.MainNotions.IntegralHeckeForms.ABHyp Y i F j b) :
    Pack Y i j b where
  B := F.B j b
  A := F.A j b
  S := F.S j b
  c := h.2.2.2.2.2.2.2.2.2.2.1.choose
  fg := h.2.2.2.1.1
  hkB := h.2.2.2.2.2.1
  comm := h.2.2.2.2.2.2.2.2.2.1
  li := h.2.2.2.2.2.2.1
  spn := h.2.2.2.2.2.2.2.1
  t2 := by
    intro Q M hQ a ha hd
    obtain ⟨w, hw⟩ := h.2.2.2.2.2.2.2.2.2.2.1.choose_spec Q M hQ.1 hQ.2.2.2.2 hQ.2.1 a ha hd
    let A' : ↥(F.Ball j b) →ₗ[X.O i] ↥(F.B j b) :=
      ((F.A j b).domRestrict (F.Ball j b)).codRestrict (F.B j b)
        (fun x => h.2.2.2.2.1 ⟨x, x.2, rfl⟩)
    refine ⟨A'.rTensor _ w, ?_⟩
    rw [← map_smul, ← hw, ← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply]
    rfl
  t3 := h.2.2.2.2.2.2.2.2.2.2.2

theorem abstract_form_of_lattice_run (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (N0 : X.Tw → ℕ)
    (hmain : ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b (p : Pack Y i j b), p.Main) (h2 : SelmerSeriesChoice Y bkP N0) :
    Formalism.MainNotions.IntegralHeckeForms.TwistingCharacterExistence Y bkP N0 := by
  intro i hi hS eps' he F hF A0
  obtain ⟨Q, k', ψ', M, χ, hPsi, _, hχ, _, hAT, hC, hD, epsB, h0, hs, hb⟩ :=
    run_packs bkP N0 h2 i hi hS eps' he A0 (fun x => packAB F x.1.1 x.2 (hF x.1.1 x.1.2 x.2))
      (fun x => hmain i hi x.1.1 x.1.2 x.2 _)
  refine ⟨Q, k', ψ', hPsi, hAT, hC, hD, M, χ, hχ, epsB, h0, hs, ?_⟩
  intro j hj b Tψ hT hmem
  obtain ⟨hl, hi⟩ := hb (⟨j, hj⟩, b)
  have hle : (packAB F j b (hF j hj b)).Yl Q M k' (psiAt b χ) ≤ Tψ := by
    unfold Pack.Yl
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact hmem a ha
  exact (sIdx_mono' (X.l i) ((packAB F j b (hF j hj b)).isLatIn_B k') hl hT hle).trans hi

theorem conclusion_of_lattice_pack (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ)
    (hmain : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b (p : Pack D.nexp i j b), p.Main) (h2 : adm2 D bkP N0) (h11 : adm11 D) :
    aux₃ D bkP N0 :=
  fun i hi => general_bound_of_lattice_pack (Formalism.MainNotions.BlochKatoReduction.pin bkP) N0 hmain h2 h11 i hi

theorem abstract_form_of_lattice_pack (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ)
    (hmain : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b (p : Pack D.nexp i j b), p.Main) (h2 : adm2 D bkP N0) : AbstractTwistPinned D bkP N0 :=
  abstract_form_of_lattice_run (Formalism.MainNotions.BlochKatoReduction.pin bkP) N0 hmain h2

end Fin

section Asm4

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}
  {i : X.Tw} {j : ℕ} {b : Bool} (p : Pack Y i j b)

theorem Pack.main [CharZero (FractionRing (X.O i))] (hF : FrobEx N) (h12 : AugmentationCompatibility Y) (h13 : HeckeOperatorsCommute Y)
    (hi : X.NonzeroIndexPlace i) (hj : j ∈ Finset.Icc 1 D.R.m) :
    p.Main := by
  obtain ⟨n, β, ⟨es⟩⟩ := p.exists_basis
  refine ⟨p.f β es, ?_, fun A0 hA0 => p.good β es hF h12 hi hj (fun P0 hP0 hu => p.det_unit β h13 hi hP0 hu) A0 hA0,
    fun Q M k χ h => p.eval β es Q M k χ h⟩
  rw [p.v_eq β es h12 hi hj]
  exact nval_nonneg _ _ _

theorem conclusion_of_hecke_commutation (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ) (hF : FrobEx D.nd)
    (h2 : adm2 D bkP N0) (h11 : adm11 D) (h12 : adm12 D) (h13 : adm13 D) : aux₃ D bkP N0 :=
  conclusion_of_lattice_pack D bkP N0 (fun _ hi _ hj _ p => p.main hF h12 h13 hi hj) h2 h11

theorem abstract_form_of_hecke (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ) (hF : FrobEx D.nd)
    (h2 : adm2 D bkP N0) (h12 : adm12 D) (h13 : adm13 D) : AbstractTwistPinned D bkP N0 :=
  abstract_form_of_lattice_pack D bkP N0 (fun _ hi _ hj _ p => p.main hF h12 h13 hi hj) h2

theorem stmt_of_frobenius (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (hF : FrobEx D.nd) : Stmt D bkP := by
  rintro N0 ⟨_, h2, _, _, _, _, _, _, _, _, h11, h12, h13⟩
  exact conclusion_of_hecke_commutation D bkP N0 hF h2 h11 h12 h13

theorem arbitrary_lattice_of_frobenius (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (hF : FrobEx D.nd) : ArbitraryLatticeOfAdmissible D bkP :=
  arbitrary_lattice_of_statement D bkP (stmt_of_frobenius D bkP hF)

theorem abstract_form_of_frobenius (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (hF : FrobEx D.nd) : AbstractTwistOfAdmissible D bkP := by
  rintro N0 ⟨_, h2, _, _, _, _, _, _, _, _, _, h12, h13⟩
  exact abstract_form_of_hecke D bkP N0 hF h2 h12 h13

end Asm4

section FrobAll

section Frob

open Polynomial

theorem val_le_one_of_isIntegral {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω] (A : ValuationSubring Ω)
    (hR : ∀ r : R, A.valuation (algebraMap R Ω r) ≤ 1) {y : Ω} (hy : IsIntegral R y) :
    A.valuation y ≤ 1 := by
  let φ : R →+* A := (algebraMap R Ω).codRestrict A.toSubring
    (fun r => (A.valuation_le_one_iff _).1 (hR r))
  obtain ⟨p, hpm, hp⟩ := hy
  have h1 : IsIntegral A y := by
    refine ⟨p.map φ, hpm.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h1
  rw [← ha]
  exact A.valuation_le_one a

theorem exists_primitive_at {R Ω : Type} (F : Type) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field Ω] [Algebra F Ω] [Algebra R Ω] [IsScalarTower R F Ω]
    [Algebra.IsAlgebraic F Ω] (P : Ideal R) [P.IsPrime] (x : Ω) :
    ∃ g : R[X], aeval x g = 0 ∧ ∃ j, g.coeff j ∉ P := by
  have hx : IsAlgebraic R x :=
    (IsFractionRing.isAlgebraic_iff R F Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨p, hp0, hpx⟩ := hx
  set I : Ideal R := Ideal.span (Set.range p.coeff) with hI
  have hI0 : I ≠ ⊥ := by
    intro h
    apply hp0
    ext k
    have : p.coeff k ∈ I := Ideal.subset_span ⟨k, rfl⟩
    rw [h] at this
    simpa using this
  have hinv : (I : FractionalIdeal (nonZeroDivisors R) F) * (I : FractionalIdeal (nonZeroDivisors R) F)⁻¹ = 1 :=
    FractionalIdeal.coe_ideal_mul_inv I hI0
  have hint : ∀ t ∈ (I : FractionalIdeal (nonZeroDivisors R) F)⁻¹, ∀ a ∈ I,
      ∃ c : R, algebraMap R F c = algebraMap R F a * t := by
    intro t ht a ha
    have h1 : algebraMap R F a * t ∈
        (I : FractionalIdeal (nonZeroDivisors R) F) * (I : FractionalIdeal (nonZeroDivisors R) F)⁻¹ :=
      FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨a, ha, rfl⟩) ht
    rw [hinv] at h1
    exact (FractionalIdeal.mem_one_iff _).1 h1
  have hex : ∃ t ∈ (I : FractionalIdeal (nonZeroDivisors R) F)⁻¹, ∃ k, ∀ c : R,
      algebraMap R F c = algebraMap R F (p.coeff k) * t → c ∉ P := by
    by_contra hcon
    push Not at hcon
    have hle : (I : FractionalIdeal (nonZeroDivisors R) F) * (I : FractionalIdeal (nonZeroDivisors R) F)⁻¹ ≤
        (P : FractionalIdeal (nonZeroDivisors R) F) := by
      rw [FractionalIdeal.mul_le]
      intro a' ha' t ht
      obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha'
      clear ha'
      rw [hI] at ha
      induction ha using Submodule.span_induction with
      | mem a h =>
        obtain ⟨k, rfl⟩ := h
        obtain ⟨c, hc, hcP⟩ := hcon t ht k
        rw [← hc]
        exact (FractionalIdeal.mem_coeIdeal _).2 ⟨c, hcP, rfl⟩
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, add_mul]; exact Submodule.add_mem _ ha hb
      | smul r a _ ha =>
        rw [smul_eq_mul, map_mul, mul_assoc, ← Algebra.smul_def]
        exact Submodule.smul_mem _ r ha
    rw [hinv] at hle
    have h1 : (1 : F) ∈ (P : FractionalIdeal (nonZeroDivisors R) F) := hle (FractionalIdeal.one_mem_one _)
    obtain ⟨c, hc, hc1⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
    have : c = 1 := IsFractionRing.injective R F (by rw [hc1, map_one])
    rw [this] at hc
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one P).2 hc)
  obtain ⟨t, ht, k0, hk0⟩ := hex
  choose c hc using fun k => hint t ht (p.coeff k) (Ideal.subset_span ⟨k, rfl⟩)
  refine ⟨∑ k ∈ Finset.range (p.natDegree + 1), C (c k) * X ^ k, ?_, k0, ?_⟩
  · have h2 : aeval x p = ∑ k ∈ Finset.range (p.natDegree + 1), algebraMap R Ω (p.coeff k) * x ^ k := by
      rw [aeval_eq_sum_range]
      simp [Algebra.smul_def]
    have h3 : ∀ k, algebraMap R Ω (c k) = algebraMap R Ω (p.coeff k) * algebraMap F Ω t := by
      intro k
      rw [IsScalarTower.algebraMap_apply R F Ω, hc k, map_mul, ← IsScalarTower.algebraMap_apply R F Ω]
    simp only [map_sum, map_mul, aeval_C, map_pow, aeval_X, h3]
    have : ∑ k ∈ Finset.range (p.natDegree + 1), algebraMap R Ω (p.coeff k) * algebraMap F Ω t * x ^ k =
        algebraMap F Ω t * ∑ k ∈ Finset.range (p.natDegree + 1), algebraMap R Ω (p.coeff k) * x ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, ← h2, hpx, mul_zero]
  · have h4 : (∑ k ∈ Finset.range (p.natDegree + 1), C (c k) * X ^ k).coeff k0 =
        if k0 ∈ Finset.range (p.natDegree + 1) then c k0 else 0 := by
      simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
    rw [h4]
    split_ifs with h5
    · exact hk0 _ (hc k0)
    · exfalso
      have h6 : p.coeff k0 = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        simp only [Finset.mem_range, not_lt] at h5
        omega
      exact hk0 0 (by rw [h6]; simp) (zero_mem P)

end Frob

section Frob2

open Polynomial

variable {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω] (A : ValuationSubring Ω)

theorem not_lt_one_add {a y : Ω} (ha : ¬ A.valuation a < 1) (hy : A.valuation y < 1) :
    ¬ A.valuation (a + y) < 1 := by
  intro h
  apply ha
  have : a = (a + y) - y := by ring
  rw [this]
  exact Valuation.map_sub_lt _ h hy

theorem exists_mul_integral {x : Ω} (hx : A.valuation x ≤ 1) :
    ∀ (n : ℕ) (g : (integralClosure R Ω)[X]), g.natDegree ≤ n → aeval x g = 0 →
      (∃ j, ¬ A.valuation ((g.coeff j : integralClosure R Ω) : Ω) < 1) →
      ∃ s : integralClosure R Ω, ¬ A.valuation (s : Ω) < 1 ∧ IsIntegral R ((s : Ω) * x) := by
  intro n
  induction n with
  | zero =>
    intro g hd hg ⟨j, hj⟩
    exfalso
    have h0 : g = C (g.coeff 0) := eq_C_of_natDegree_le_zero hd
    rw [h0, aeval_C] at hg
    have h1 : g.coeff 0 = 0 := by
      have : ((g.coeff 0 : integralClosure R Ω) : Ω) = 0 := hg
      exact Subtype.ext this
    rw [h1, map_zero] at h0
    rw [h0] at hj
    simp at hj
  | succ n ih =>
    intro g hd hg ⟨j, hj⟩
    set c := g.leadingCoeff with hc
    have hint : IsIntegral R ((c : Ω) * x) := by
      have h1 : IsIntegral (integralClosure R Ω) (c • x) := isIntegral_leadingCoeff_smul g x hg
      have h2 : IsIntegral R (c • x) := isIntegral_trans _ h1
      exact h2
    by_cases hcv : A.valuation (c : Ω) < 1
    · set d := g.natDegree with hdd
      have hjd : j ≠ d := by
        rintro rfl
        exact hj hcv
      have hd0 : d ≠ 0 := by
        intro h0
        have h1 : g = C (g.coeff 0) := eq_C_of_natDegree_le_zero (le_of_eq h0)
        have h2 : g.coeff j = 0 := by
          rw [h1, coeff_C, if_neg (by rw [h0] at hjd; exact hjd)]
        rw [h2] at hj
        simp at hj
      let y : integralClosure R Ω := ⟨(c : Ω) * x, hint⟩
      have hy : A.valuation (y : Ω) < 1 := by
        show A.valuation ((c : Ω) * x) < 1
        rw [map_mul]
        exact mul_lt_one_of_lt_of_le hcv hx
      refine ih (g.eraseLead + C y * X ^ (d - 1)) ?_ ?_ ⟨j, ?_⟩
      · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact (eraseLead_natDegree_le g).trans (by omega)
        · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      · have h1 : aeval x g = aeval x g.eraseLead + (c : Ω) * x ^ d := by
          conv_lhs => rw [← eraseLead_add_C_mul_X_pow g]
          rw [map_add, map_mul, aeval_C, map_pow, aeval_X]
          rfl
        rw [map_add, map_mul, aeval_C, map_pow, aeval_X]
        have h2 : (algebraMap (integralClosure R Ω) Ω) y * x ^ (d - 1) = (c : Ω) * x ^ d := by
          show (c : Ω) * x * x ^ (d - 1) = (c : Ω) * x ^ d
          rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hd0)]
        rw [h2, ← h1, hg]
      · rw [coeff_add, eraseLead_coeff_of_ne _ hjd, coeff_C_mul, coeff_X_pow]
        split_ifs with h
        · rw [mul_one]
          exact not_lt_one_add A hj hy
        · rw [mul_zero, add_zero]
          exact hj
    · exact ⟨c, hcv, hint⟩

end Frob2

section Frob3

open Polynomial Pointwise

variable {R F Ω : Type} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
  [Field Ω] [Algebra F Ω] [Algebra R Ω] [IsScalarTower R F Ω]

theorem exists_rep (F : Type) [Field F] [Algebra R F] [IsFractionRing R F] [Algebra F Ω] [IsScalarTower R F Ω]
    [Algebra.IsAlgebraic F Ω] (A : ValuationSubring Ω) (P : Ideal R) [P.IsPrime]
    (hP : ∀ r : R, A.valuation (algebraMap R Ω r) < 1 ↔ r ∈ P) {x : Ω} (hx : A.valuation x ≤ 1) :
    ∃ b s : integralClosure R Ω, ¬ A.valuation (s : Ω) < 1 ∧ (s : Ω) * x = b := by
  obtain ⟨g, hg, j, hj⟩ := exists_primitive_at F P x
  obtain ⟨s, hs, hi⟩ := exists_mul_integral A hx (g.map (algebraMap R (integralClosure R Ω))).natDegree
    (g.map (algebraMap R (integralClosure R Ω))) le_rfl (by rw [aeval_map_algebraMap]; exact hg)
    ⟨j, by
      rw [coeff_map]
      intro h
      exact hj ((hP _).1 h)⟩
  exact ⟨⟨_, hi⟩, s, hs, rfl⟩

@[reducible] def actB (R F Ω : Type) [CommRing R] [Field F] [Algebra R F] [Field Ω] [Algebra F Ω] [Algebra R Ω]
    [IsScalarTower R F Ω] : MulSemiringAction (Ω ≃ₐ[F] Ω) (integralClosure R Ω) where
  smul g b := ⟨g b, (b.2 : IsIntegral R (b : Ω)).map (g.toAlgHom.restrictScalars R)⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl
  smul_zero g := Subtype.ext (map_zero g)
  smul_add g _ _ := Subtype.ext (map_add g _ _)
  smul_one g := Subtype.ext (map_one g)
  smul_mul g _ _ := Subtype.ext (map_mul g _ _)

theorem val_le_one_map [Algebra.IsAlgebraic F Ω] (A : ValuationSubring Ω) (P : Ideal R) [P.IsPrime]
    (hR : ∀ r : R, A.valuation (algebraMap R Ω r) ≤ 1)
    (hP : ∀ r : R, A.valuation (algebraMap R Ω r) < 1 ↔ r ∈ P) (τ : Ω ≃ₐ[F] Ω)
    (hτ : ∀ b : integralClosure R Ω, A.valuation (τ (b : Ω)) < 1 ↔ A.valuation (b : Ω) < 1)
    {x : Ω} (hx : A.valuation x ≤ 1) : A.valuation (τ x) ≤ 1 := by
  obtain ⟨b, s, hs, hsx⟩ := exists_rep F A P hP hx
  have hi : ∀ b : integralClosure R Ω, A.valuation (τ (b : Ω)) ≤ 1 := fun b =>
    val_le_one_of_isIntegral A hR ((b.2 : IsIntegral R (b : Ω)).map (τ.toAlgHom.restrictScalars R))
  have h1 : A.valuation (τ (s : Ω)) = 1 :=
    le_antisymm (hi s) (not_lt.1 fun h => hs ((hτ s).1 h))
  have h2 : τ (s : Ω) * τ x = τ (b : Ω) := by rw [← map_mul, hsx]
  have h3 := congrArg A.valuation h2
  rw [map_mul, h1, one_mul] at h3
  rw [h3]
  exact hi b

end Frob3

section Frob4

open Polynomial Pointwise

variable {R F Ω : Type} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
  [Field Ω] [Algebra F Ω] [Algebra R Ω] [IsScalarTower R F Ω]

theorem exists_frob_generic [IsGalois F Ω] (A : ValuationSubring Ω) (P : Ideal R) [P.IsMaximal] [Finite (R ⧸ P)]
    (hR : ∀ r : R, A.valuation (algebraMap R Ω r) ≤ 1)
    (hP : ∀ r : R, A.valuation (algebraMap R Ω r) < 1 ↔ r ∈ P) :
    ∃ σ : Ω ≃ₐ[F] Ω, σ ∈ A.decompositionSubgroup F ∧
      ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ Nat.card (R ⧸ P)) < 1 := by
  let _ := actB R F Ω
  have hsm : ∀ (g : Ω ≃ₐ[F] Ω) (b : integralClosure R Ω), ((g • b : integralClosure R Ω) : Ω) = g (b : Ω) :=
    fun _ _ => rfl
  have : SMulCommClass (Ω ≃ₐ[F] Ω) R (integralClosure R Ω) := ⟨fun g r b => Subtype.ext (by
    show g (r • (b : Ω)) = r • g (b : Ω)
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply R F Ω, g.commutes])⟩
  let _ : TopologicalSpace (integralClosure R Ω) := ⊥
  have : DiscreteTopology (integralClosure R Ω) := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[F] Ω) (integralClosure R Ω) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro b
    have h := stabilizer_isOpen_of_isIntegral (K := F) (L := Ω) (b : Ω)
    have he : (MulAction.stabilizer (Ω ≃ₐ[F] Ω) b : Set (Ω ≃ₐ[F] Ω)) =
        (MulAction.stabilizer (Ω ≃ₐ[F] Ω) (b : Ω) : Set (Ω ≃ₐ[F] Ω)) := by
      ext g
      simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      exact Subtype.ext_iff
    rw [he]
    exact h
  have : Algebra.IsInvariant R (integralClosure R Ω) (Ω ≃ₐ[F] Ω) := ⟨fun b hb => by
    have h1 : (b : Ω) ∈ Set.range (algebraMap F Ω) :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F) (K := Ω) (b : Ω)).2
        fun g => congrArg Subtype.val (hb g)
    obtain ⟨k, hk⟩ := h1
    have h2 : IsIntegral R k := by
      have h3 : IsIntegral R (algebraMap F Ω k) := hk ▸ b.2
      exact (isIntegral_algebraMap_iff (algebraMap F Ω).injective).1 h3
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h2
    refine ⟨a, Subtype.ext ?_⟩
    show algebraMap R Ω a = (b : Ω)
    rw [IsScalarTower.algebraMap_apply R F Ω, ha, hk]⟩
  let ψ : integralClosure R Ω →+* A := (algebraMap (integralClosure R Ω) Ω).codRestrict A.toSubring
    (fun b => (A.valuation_le_one_iff _).1 (val_le_one_of_isIntegral A hR b.2))
  let Q : Ideal (integralClosure R Ω) := (IsLocalRing.maximalIdeal A).comap ψ
  have : Q.IsPrime := Ideal.comap_isPrime ψ _
  have hQ : ∀ b : integralClosure R Ω, b ∈ Q ↔ A.valuation (b : Ω) < 1 := fun b => by
    show ψ b ∈ IsLocalRing.maximalIdeal A ↔ _
    rw [A.valuation_lt_one_iff]
    rfl
  have : Q.LiesOver P := ⟨by
    ext r
    rw [Ideal.under, Ideal.mem_comap, hQ, ← hP]
    rfl⟩
  have hsurj := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[F] Ω) P Q
  have : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q P
  let _ : Field (R ⧸ P) := Ideal.Quotient.field P
  let _ : Field (integralClosure R Ω ⧸ Q) := Ideal.Quotient.field Q
  let _ : Fintype (R ⧸ P) := Fintype.ofFinite _
  have : Algebra.IsAlgebraic (R ⧸ P) (integralClosure R Ω ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  obtain ⟨⟨σ, hσ⟩, hσF⟩ := hsurj (FiniteField.frobeniusAlgEquivOfAlgebraic (R ⧸ P) (integralClosure R Ω ⧸ Q))
  have hq : Fintype.card (R ⧸ P) = Nat.card (R ⧸ P) := (Nat.card_eq_fintype_card).symm
  have h1 : ∀ b : integralClosure R Ω, A.valuation (σ (b : Ω) - (b : Ω) ^ Nat.card (R ⧸ P)) < 1 := by
    intro b
    have h := DFunLike.congr_fun hσF (Ideal.Quotient.mk Q b)
    rw [Ideal.Quotient.stabilizerHom_apply, FiniteField.coe_frobeniusAlgEquivOfAlgebraic] at h
    have h' : Ideal.Quotient.mk Q (σ • b) = Ideal.Quotient.mk Q (b ^ Fintype.card (R ⧸ P)) := by
      rw [map_pow]; exact h
    rw [Ideal.Quotient.eq, hQ, hq] at h'
    exact h'
  have h2 : ∀ b : integralClosure R Ω, A.valuation (σ (b : Ω)) < 1 ↔ A.valuation (b : Ω) < 1 := by
    intro b
    have hσ' : σ • Q = Q := hσ
    rw [← hQ b, ← hsm, ← hQ (σ • b)]
    conv_lhs => rw [← hσ']
    exact Ideal.smul_mem_pointwise_smul_iff
  have h3 : ∀ b : integralClosure R Ω, A.valuation (σ⁻¹ (b : Ω)) < 1 ↔ A.valuation (b : Ω) < 1 := by
    intro b
    have := h2 (σ⁻¹ • b)
    rw [hsm] at this
    rw [← this]
    have e : σ (σ⁻¹ (b : Ω)) = (b : Ω) := by
      show (σ * σ⁻¹) (b : Ω) = b
      rw [mul_inv_cancel]; rfl
    rw [e]
  have hst : ∀ x, A.valuation x ≤ 1 → A.valuation (σ x) ≤ 1 := fun x hx =>
    val_le_one_map A P hR hP σ h2 hx
  have hst' : ∀ x, A.valuation x ≤ 1 → A.valuation (σ⁻¹ x) ≤ 1 := fun x hx =>
    val_le_one_map A P hR hP σ⁻¹ h3 hx
  refine ⟨σ, ?_, ?_⟩
  · show σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← A.valuation_le_one_iff, ← A.valuation_le_one_iff]
    constructor
    · intro h
      have := hst _ h
      have e : σ (σ⁻¹ • x) = x := by
        show (σ * σ⁻¹) x = x
        rw [mul_inv_cancel]; rfl
      rwa [e] at this
    · intro h
      exact hst' x h
  · intro x hx
    obtain ⟨b, s, hs, hsx⟩ := exists_rep F A P hP hx
    set q := Nat.card (R ⧸ P) with hqq
    have hi : ∀ b : integralClosure R Ω, A.valuation (b : Ω) ≤ 1 := fun b => val_le_one_of_isIntegral A hR b.2
    have hs1 : A.valuation (s : Ω) = 1 := le_antisymm (hi s) (not_lt.1 hs)
    have hσs1 : A.valuation (σ (s : Ω)) = 1 :=
      le_antisymm (hst _ (hi s)) (not_lt.1 fun h => hs ((h2 s).1 h))
    have key : (σ (s : Ω) * (s : Ω) ^ q) * (σ x - x ^ q) =
        (σ (b : Ω) - (b : Ω) ^ q) * (s : Ω) ^ q - (b : Ω) ^ q * (σ (s : Ω) - (s : Ω) ^ q) := by
      have e1 : σ (b : Ω) = σ (s : Ω) * σ x := by rw [← hsx, map_mul]
      have e2 : (b : Ω) ^ q = (s : Ω) ^ q * x ^ q := by rw [← hsx, mul_pow]
      rw [e1, e2]
      ring
    have hv := congrArg A.valuation key
    rw [map_mul, map_mul, map_pow, hσs1, hs1, one_pow, one_mul, one_mul] at hv
    rw [hv]
    refine Valuation.map_sub_lt _ ?_ ?_
    · rw [map_mul, map_pow, hs1, one_pow, mul_one]
      exact h1 b
    · rw [map_mul, map_pow]
      rw [mul_comm]
      exact mul_lt_one_of_lt_of_le (h1 s) (pow_le_one₀ zero_le (hi b))

end Frob4

section Frob5

open NumberField IsDedekindDomain

theorem exists_isFrob {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : Formalism.ConjugateSelfDual.IsPlaceOver A v) :
    ∃ σ : Formalism.ConjugateSelfDual.G F Ω, Formalism.ConjugateSelfDual.IsFrob A (Formalism.ConjugateSelfDual.normV v) σ := by
  have : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : IsGalois F Ω := ⟨⟩
  have : v.asIdeal.IsMaximal := v.isMaximal
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  have hR : ∀ r : 𝓞 F, A.valuation (algebraMap (𝓞 F) Ω r) ≤ 1 := by
    intro r
    have h1 : IsIntegral ℤ (algebraMap (𝓞 F) Ω r) := (RingOfIntegers.isIntegral r).map
      ((IsScalarTower.toAlgHom ℤ (𝓞 F) Ω))
    refine val_le_one_of_isIntegral A (R := ℤ) (fun n => ?_) h1
    rw [A.valuation_le_one_iff]
    rw [eq_intCast]
    exact intCast_mem A n
  exact exists_frob_generic (R := 𝓞 F) (F := F) A v.asIdeal hR h

end Frob5

end FrobAll

section Final

open Formalism.BasicNotions

theorem frobEx_holds {D : Formalism.BasicNotions.D7} (N : NData D.R D.host D.what₂) : FrobEx N :=
  fun P => exists_isFrob (N.plOm.1 P) P (N.plOm.2 P)

theorem frobenius_lifting (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) : Stmt D bkP :=
  stmt_of_frobenius D bkP (frobEx_holds D.nd)

theorem arbitrary_lattice_holds (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) : ArbitraryLatticeOfAdmissible D bkP :=
  arbitrary_lattice_of_frobenius D bkP (frobEx_holds D.nd)

theorem abstract_form_holds (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) : AbstractTwistOfAdmissible D bkP :=
  abstract_form_of_frobenius D bkP (frobEx_holds D.nd)

end Final

end Formalism.MainNotions.LatticeVariant

end
