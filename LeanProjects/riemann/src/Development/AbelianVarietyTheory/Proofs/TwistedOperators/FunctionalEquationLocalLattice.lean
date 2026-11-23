import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralBasisCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselSecondBasePointCharacterTrivialDepthLattic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrime
import GroundTheory.GlobalFields.TateThesis.AdelePoisson
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section

namespace GlobalTheory.ConjClause

open GlobalTheory.FinPl (SplitPt Frame)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_int (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w) {a : AE D}
    (ha : finPart D a ∈ intAE D) : p.pr a ∈ 𝒪[k] := by
  have h := p.val_prF_le_one he ⟨_, GlobalTheory.IdemRes.toEAf_mem_of_finPart ha⟩
  rw [p.prF_toEAf] at h
  exact h

theorem pr_tmul_int (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w)
    {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (b : 𝓞 D.host.E) :
    p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (b : D.host.E)) ∈ 𝒪[k] :=
  pr_int p he (AddSubgroup.subset_closure ⟨α, hα, b, rfl⟩)

def prInt (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w) :
    𝓞 D.host.E →+* 𝒪[k] :=
  ((p.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict 𝒪[k] fun z => by
    have h := p.val_prF_le_one he (Formalism.L2.DIV.oToS D.host.F D.host.E z)
    have e : p.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E z : EAf D) = p.pr (incA D (z : D.host.E)) :=
      p.prF_toEAf he (incA D (z : D.host.E))
    rw [e] at h
    exact h

theorem mem_iff_prInt (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w)
    (z : 𝓞 D.host.E) : z ∈ w.asIdeal ↔ prInt p he z ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
  have e : p.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E z : EAf D) = p.pr (incA D (z : D.host.E)) :=
    p.prF_toEAf he (incA D (z : D.host.E))
  rw [p.mem_iff_val_lt he, e, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  rfl

theorem exists_mem_pow (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w)
    {x : D.host.E} {n : ℕ} (hx : w.valuation D.host.E x ≤ WithZero.exp (-(n : ℤ))) :
    ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n, (z : k) = p.pr (incA D x) := by
  have h1 : w.valuation D.host.E x ≤ 1 := hx.trans (by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  obtain ⟨a, s, has⟩ := w.exists_primeCompl_mul_eq_of_integer x h1
  have hs : w.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E s) = 1 := by
    rw [w.valuation_of_algebraMap, w.intValuation_eq_one_iff]; exact s.2
  have ha : a ∈ w.asIdeal ^ n := by
    have h2 := congrArg (w.valuation D.host.E) has
    rw [map_mul, hs, mul_one, w.valuation_of_algebraMap] at h2
    rw [← w.intValuation_le_pow_iff_mem, ← h2]
    exact hx
  have hu : IsUnit (prInt p he s) := by
    by_contra h
    exact s.2 ((mem_iff_prInt p he s).2 h)
  obtain ⟨u, hu⟩ := hu
  have hle : Ideal.map (prInt p he) (w.asIdeal ^ n) ≤ IsLocalRing.maximalIdeal 𝒪[k] ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun z hz => Ideal.mem_comap.2 ((mem_iff_prInt p he z).1 hz)) n
  refine ⟨prInt p he a * ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]), Ideal.mul_mem_right _ _ (hle (Ideal.mem_map_of_mem _ ha)), ?_⟩
  have e1 : ((prInt p he a : 𝒪[k]) : k) = p.pr (incA D x) * ((u : 𝒪[k]) : k) := by
    rw [hu]
    change (p.pr.comp (incA D)) (algebraMap _ _ a) = (p.pr.comp (incA D)) x * (p.pr.comp (incA D)) (algebraMap _ _ s.1)
    rw [← map_mul, has]
  have e2 : ((u : 𝒪[k]) : k) * (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  rw [Subring.coe_mul, e1, mul_assoc, e2, mul_one]

theorem tmul_eq' (α : AF D.host.F) (x : D.host.E) :
    (α ⊗ₜ[D.host.F] x : AE D) = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D x := by
  change _ = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem pair_int (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w)
    {S : HSp D} {Λ : Lat S} (hΛ : IsSelfDualC S Λ) {t : Fin S.rank → D.host.E} (ht : t ∈ Λ) {P : GlobalTheory.FinPl.Pl D → Prop}
    {y : Fin S.rank → AE D} (hy : y ∈ latV S Λ P) :
    (∑ l, ∑ j, p.pr (incA D (star (t j))) * p.pr (incA D (S.gram j l)) * p.pr (y l)) ∈ 𝒪[k] := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, x, hx, rfl⟩ := hy
    obtain rfl : a = 1 := ha
    obtain ⟨b, hb⟩ := (hΛ.2 x).1 hx t ht
    convert pr_tmul_int p he hα b using 1
    rw [hb, tmul_eq', Finset.sum_comm]
    simp only [one_mul, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    rw [tmul_eq' _ (x _), map_mul]
    ring
  | zero => simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  | neg x _ hx =>
    convert neg_mem hx using 1
    simp only [Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]

theorem pair_col_int (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w)
    {S : HSp D} {Λ : Lat S} (hΛ : IsSelfDualC S Λ) {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n)
    (hβ : β.IsLat Λ (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k))) {t : Fin S.rank → D.host.E} (ht : t ∈ Λ) (i : n) :
    ((fun j => p.pr (incA D (star (t j)))) ᵥ* (S.gram.map (fun c => p.pr (incA D c)) * β.b)) i ∈ 𝒪[k] := by
  have h1 := (hβ (Pi.single i 1)).1 fun l _ => by
    by_cases h : l = i
    · subst h; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  convert pair_int p he hΛ ht h1 using 1
  rw [Finset.sum_comm]
  simp only [p.pr_sec, mulVec_single_one, vecMul, dotProduct, Matrix.mul_apply, map_apply, Finset.mul_sum, mul_assoc]
  rfl

def rowVal {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {a b : ℕ} {n : Type} (ε : Fin b → A) (M : Matrix (Fin a) n R)
    (i : n) : Matrix (Fin a) (Fin b) A →+ R where
  toFun u := ((fun j => f (∑ m, u j m * ε m)) ᵥ* M) i
  map_zero' := by simp [vecMul, dotProduct]
  map_add' x y := by
    simp only [vecMul, dotProduct, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add]

theorem vecMul_const_mul {R : Type} [CommRing R] {a : ℕ} {n : Type} (x : R) (g : Fin a → R) (M : Matrix (Fin a) n R) (i : n) :
    ((fun j => x * g j) ᵥ* M) i = x * (g ᵥ* M) i := by
  simp only [vecMul, dotProduct, Finset.mul_sum, mul_assoc]

theorem comp_mul_three {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (g : A →+* A) {x y t x' y' t' : A}
    (hx : g x = x') (hy : g y = y') (ht : g t = t') : f x' * f y' * f t' = (f.comp g) (x * (y * t)) := by
  rw [RingHom.comp_apply, g.map_mul, g.map_mul, hx, hy, ht, f.map_mul, f.map_mul, mul_assoc]

theorem rowVal_rank_one {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (g : A →+* A) {a b : ℕ} {n : Type}
    {u : Matrix (Fin a) (Fin b) A} {ε : Fin b → A} {x y x' y' : A} {t t' : Fin a → A}
    (hu : ∀ j, ∑ m, u j m * ε m = x * (y * t j)) (hx : g x = x') (hy : g y = y') (ht : ∀ j, g (t j) = t' j)
    (M : Matrix (Fin a) n R) (i : n) :
    f x' * f y' * ((fun j => f (t' j)) ᵥ* M) i = rowVal (f.comp g) ε M i u := by
  rw [← vecMul_const_mul]
  refine congrArg (fun g => (g ᵥ* M) i) (funext fun j => ?_)
  rw [hu]
  exact comp_mul_three f g hx hy (ht j)

theorem rowVal_col {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (g : A →+* A) {a b ρ : ℕ} {n : Type}
    {u : Matrix (Fin a) (Fin b) A} {j : Matrix (Fin b) (Fin ρ) A} {y : Matrix (Fin a) (Fin ρ) A} (hy : y = u * j) {q : Fin ρ}
    {x x' : A} {N : ℕ} {ε : Fin b → A} (hj : ∀ m, j m q = x ^ N * ε m) (hx : g x = x') (M : Matrix (Fin a) n R) (i : n) :
    ((fun l => f (g (∑ m, u l m * ε m))) ᵥ* M) i * f x' ^ N = ((fun l => f (g (y l q))) ᵥ* M) i := by
  rw [mul_comm, ← vecMul_const_mul]
  refine congrArg (fun g => (g ᵥ* M) i) (funext fun l => ?_)
  rw [← hx, ← map_pow, ← map_pow, ← map_mul, ← map_mul, hy, Matrix.mul_apply, Finset.mul_sum]
  simp only [hj, mul_left_comm]

set_option maxHeartbeats 1000000 in

theorem functional_mem (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w)
    {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {Λ : Lat T} (hΛ : IsSelfDualC T Λ) {n : Type} [Fintype n] [DecidableEq n]
    (β : Frame p T n) (hβ : β.IsLat Λ (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)))
    (ε : Fin S.rank → D.host.E) (J : Ideal 𝒪[k])
    (hJ : ∀ c ∈ D.host.AA, ∀ s ∈ LS, ∃ z ∈ J, (z : k) = p.pr (incA D (star (c * ∑ m, (∑ l, star (s l) * S.gram l m) * ε m))))
    {P : GlobalTheory.FinPl.Pl D → Prop} {u : WO S T} (hu : u ∈ latO S T LS (Λ : Set _) P) (i : n) :
    ∃ z ∈ J, (z : k) = ((fun j => p.pr (cA D (∑ m, u j m * incA D (ε m)))) ᵥ*
      (T.gram.map (fun c => p.pr (incA D c)) * β.b)) i := by
  change ∃ z ∈ J, (z : k) = rowVal (p.pr.comp (cA D)) (fun m => incA D (ε m))
    (T.gram.map (fun c => p.pr (incA D c)) * β.b) i u
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, c, hc, s, hs, t, ht, rfl⟩ := hu
    obtain ⟨z, hz, hz'⟩ := hJ c hc s hs
    have h1 : p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ 𝒪[k] := by
      have h := pr_tmul_int p he hα 1
      rwa [RingOfIntegers.coe_eq_algebraMap, map_one] at h
    refine ⟨⟨_, h1⟩ * z * ⟨_, pair_col_int p he hΛ β hβ ht i⟩,
      J.mul_mem_right _ (J.mul_mem_left _ hz), ?_⟩
    have e : ∀ j, (∑ m, (pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t j * ∑ l, star (s l) * S.gram l m) : AE D) * incA D (ε m)) =
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) *
          (incA D (c * ∑ m, (∑ l, star (s l) * S.gram l m) * ε m) * incA D (t j)) := fun j => by
      rw [← map_mul, Finset.mul_sum, Finset.sum_mul, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [tmul_eq', mul_assoc, ← map_mul]
      congr 2
      ring
    have e1 : cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) := by
      change pairA D.host.F 0 α ⊗ₜ[D.host.F] (star (1 : D.host.E)) = _
      rw [star_one]
    have e2 : ∀ x, cA D (incA D x) = incA D (star x) := fun _ => rfl
    rw [Subring.coe_mul, Subring.coe_mul, hz']
    exact rowVal_rank_one p.pr (cA D) (ε := fun m => incA D (ε m))
      (u := Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ l, star (s l) * S.gram l j)) (t := fun j => incA D (t j)) (t' := fun j => incA D (star (t j))) e e1
      (e2 (c * ∑ m, (∑ l, star (s l) * S.gram l m) * ε m)) (fun j => e2 (t j)) _ i
  | zero => exact ⟨0, zero_mem _, (map_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, hz'⟩ := hx
    obtain ⟨z', hy, hy'⟩ := hy
    refine ⟨z + z', add_mem hz hy, ?_⟩
    rw [Subring.coe_add, hz', hy']
    exact (AddMonoidHom.map_add _ _ _).symm
  | neg x _ hx =>
    obtain ⟨z, hz, hz'⟩ := hx
    refine ⟨-z, neg_mem hz, ?_⟩
    rw [Subring.coe_neg, hz']
    exact (AddMonoidHom.map_neg _ _).symm

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem valuation_stair {μ₀ : T} (hL : L.Is μ₀) (hq : OffQ D) (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0)
    {c : ℕ} (r : Fin c) {a x : D.host.E} (ha : a ∈ D.host.AA) (hx : x ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) c r) :
    (G.pl.w v).valuation D.host.E (star a * x) ≤ WithZero.exp (-((G.pl.depth sc v * (r.1 + 1) : ℕ) : ℤ)) := by
  classical
  have hw : G.pl.w v ∈ G.pl.W0 := by
    unfold Places.W0
    convert Finset.mem_image_of_mem G.pl.w hv
  have hloc : G.pl.w v ∈ locPl G μ₀ := Finset.mem_union_left _ hw
  have hb := Good.badInt_notMem hL (G := G) (t := μ₀) hq (fun P hP => absurd
    (show (L.xiH μ₀).UnrAt P by rw [hL.xi_base]; exact fun x _ => rfl) ((hL.Q_ram μ₀ P).2 (Or.inl hP))) hloc
  obtain ⟨c1, c2⟩ := count_AA_AAbar _ hb
  obtain ⟨n1, n2⟩ := GlobalTheory.SecondBaseChar.st_ne (sc := sc) G.pl
  obtain ⟨-, m1, m2⟩ := GlobalTheory.SecondBaseChar.ideals_ne D
  have d1 : FractionalIdeal.count D.host.E (G.pl.w v) (G.pl.stA sc) = 0 := by
    rw [Places.stA, FractionalIdeal.count_mul _ _ m1 (right_ne_zero_of_mul n1), FractionalIdeal.count_inv, c1,
      count_modulBar G hloc, neg_zero, add_zero]
  have d2 : FractionalIdeal.count D.host.E (G.pl.w v) (G.pl.stAbar sc) = -(G.pl.depth sc v : ℤ) := by
    rw [Places.stAbar, FractionalIdeal.count_mul _ _ m2 (right_ne_zero_of_mul n2), FractionalIdeal.count_inv, c2,
      count_modul, cosExp, if_pos hw, G.pl.under_w hv, zero_add]
  have h1 := GroundTheory.Global.valuation_le_of_mem_fractionalIdeal (G.pl.w v) hx
  rw [count_stairId n1 n2, d1, d2] at h1
  have h2 := GroundTheory.Global.valuation_le_of_mem_fractionalIdeal (G.pl.w v)
    (((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1.2 (star a)).2 (by rwa [star_star]))
  rw [c2, neg_zero, WithZero.exp_zero] at h2
  rw [map_mul]
  refine (mul_le_mul' h2 h1).trans_eq ?_
  rw [one_mul]
  congr 1
  push_cast
  ring

theorem star_pair {B : HSp D} {c : ℕ} (a : Matrix (Fin B.rank) (Fin c) D.host.E) (s : Fin B.rank → D.host.E) (q : Fin c) :
    star (∑ m, (∑ l, star (s l) * (negSp B).gram l m) * a m q) = -((aᴴ * B.gram) *ᵥ s) q := by
  have hG : ∀ l m, star (B.gram l m) = B.gram m l := fun l m => congrFun (congrFun (gram_conjTranspose B) m) l
  simp only [negSp_gram, Matrix.neg_apply, star_sum, star_mul', star_star, star_neg, hG, mulVec, dotProduct, Matrix.mul_apply,
    conjTranspose_apply, Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem functional_col {μ₀ : T} (hL : L.Is μ₀) (hq : OffQ D) (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0)
    (p : SplitPt D k) (he : Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v)) {A B B₀ S : HSp D} {c ρ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1))
    (Λ₀ : Lat A) (y : HypDec B B₀ ρ) (hy : IsAuxiliaryVectorWittDec d y) {LB : Lat B}
    (hB : LB = d.lat Λ₀ (stairId (G.pl.stA sc) (G.pl.stAbar sc) c)) {Λ : Lat S} (hΛ : IsSelfDualC S Λ)
    {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n)
    (hβ : β.IsLat Λ (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k))) {a : Mx D S.rank ρ}
    (ha : y.extX S a ∈ latO (negSp B) S (LB : Set _) (Λ : Set _) fun _ => True) (q : Fin ρ) (i : n) :
    ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ (G.pl.depth sc v * (c - q.1)),
      (z : k) * p.pr (incA D (star (-D.host.xi0))) ^ (q.1 + 1) =
        ((fun j => p.pr (cA D (a j q))) ᵥ* (S.gram.map (fun c => p.pr (incA D c)) * β.b)) i := by
  obtain ⟨hc, hE, -⟩ := hy
  subst hB
  have hq1 := q.2
  let r : Fin c := ⟨q.1, by omega⟩
  have hr : r.rev.1 + 1 = c - q.1 := by rw [Fin.val_rev]; change _ - (q.1 + 1) + 1 = _; omega
  have hrev : r.rev.rev ≠ r.rev := fun e => by
    have := congrArg (fun t : Fin c => t.1 + 1) e
    simp only [Fin.rev_rev] at this
    rw [hr] at this
    change q.1 + 1 = _ at this
    omega
  obtain ⟨z, hz, hz'⟩ := functional_mem p he hΛ β hβ (S := negSp B) (fun m => d.a m r)
    (IsLocalRing.maximalIdeal 𝒪[k] ^ (G.pl.depth sc v * (c - q.1))) (fun a ha s hs => by
      have h1 := GlobalTheory.SecondBaseChar.coef_mem d _ _ r.rev hrev hs
      rw [Fin.rev_rev] at h1
      have h2 := valuation_stair hL hq G hv r.rev ha h1
      rw [hr, ← Valuation.map_neg, ← mul_neg, ← star_pair d.a s r, ← star_mul'] at h2
      exact exists_mem_pow p he h2) ha i
  refine ⟨z, hz, ?_⟩
  have e1 : a = (y.extX S a : Mx D _ _) ⬝ y.jX := by
    rw [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]
  have e2 : ∀ m, y.jX m q = incA D (-D.host.xi0) ^ (q.1 + 1) * incA D (d.a m r) := fun m => by
    rw [← (incA D).map_pow, ← (incA D).map_mul]
    exact congrArg (incA D) (congrFun (congrFun hE m) q)
  have e3 : cA D (incA D (-D.host.xi0)) = incA D (star (-D.host.xi0)) := rfl
  exact (congrArg (· * _) hz').trans (rowVal_col p.pr (cA D) e1 e2 e3 _ i)

theorem functional_equation_local_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k)
    (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank)) (ϖ : 𝒪[k]),
  p.v = v → Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} →
  ∀ a ∈ (pcFB W F σ h h').A₁, ∀ (q : Fin (σ + 1)) i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v,
    (z : k) * (ϖ : k) ^ (G.pl.depth sc v * (2 * σ + 1 - q.1)) * p.pr (incA D (star (-D.host.xi0))) ^ (q.1 + 1) =
      ((fun j => p.pr (cA D (a j q))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) i := by
  intro D hq T L μ₀ hL sc G W M _ F hF σ h h' v hv k _ _ _ _ p β ϖ _ he hβ hϖ a ha q i
  have hsd : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) h' (Nat.zero_le _)).sd
  obtain ⟨z, hz, hz'⟩ := functional_col hL hq G hv p he _ _ _ (hF.hJ (σ + 1) h)
    (G.sp.colLat (2 * (σ + 1) + 1) (by omega) (by omega)) hsd β hβ (a := a) ha.1 q i
  have hq1 := q.2
  have e : 2 * (σ + 1) + 1 - 1 - q.1 = 2 * σ + 1 - q.1 + 1 := by omega
  rw [e, mul_add, mul_one, pow_add, hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton_mul] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  refine ⟨y, hϖ ▸ hy, Eq.trans ?_ hz'⟩
  rw [Subring.coe_mul, SubmonoidClass.coe_pow, mul_comm (y : k)]

end GlobalTheory.ConjClause

end
