import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelTor

def cycAway (n : ℕ) : Subring ℂ := Subring.closure {zeta n, (n : ℂ)⁻¹}

def zetaAway (n : ℕ) : cycAway n := ⟨zeta n, Subring.subset_closure (Or.inl rfl)⟩

theorem isUnit_natCast {n : ℕ} (hn : n ≠ 0) : IsUnit (n : cycAway n) :=
  IsUnit.of_mul_eq_one ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
    (Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0)))

theorem isPrimitiveRoot_map {n : ℕ} (hn : n ≠ 0) {K : Type} [Field K] (β : cycAway n →+* K) :
    IsPrimitiveRoot (β (zetaAway n)) n := by
  have h₁ : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn) Subtype.val_injective
  have : NeZero (n : K) := ⟨by simpa using ((isUnit_natCast hn).map β).ne_zero⟩
  have h₂ := (h₁.isRoot_cyclotomic (Nat.pos_of_ne_zero hn)).map (f := β)
  rwa [Polynomial.map_cyclotomic, Polynomial.isRoot_cyclotomic_iff] at h₂

def cycBase {n : ℕ} (hn : n ≠ 0) : TBase (cycAway n) n where
  ζ := Units.ofPowEqOne (zetaAway n) n (Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one) hn
  unit := isUnit_natCast hn
  prim _ _ β := isPrimitiveRoot_map hn β

theorem cycBase_ζ {n : ℕ} (hn : n ≠ 0) : ((cycBase hn).ζ : cycAway n) = zetaAway n := rfl

section Param

variable {o R : Type} [CommRing o] [CommRing R] [IsLocalRing R] {m : ℕ}

def IsRelParam (b : o →+* R) (t : Fin m → R) : Prop :=
  (∀ i, t i ∈ maximalIdeal R) ∧ ∀ c : Fin m → R,
    ∑ i, c i * t i ∈ maximalIdeal R ^ 2 ⊔ ((maximalIdeal R).comap b).map b → ∀ i, c i ∈ maximalIdeal R

theorem IsRelParam.mem_of_mem_sq {b : o →+* R} {t : Fin m → R} (h : IsRelParam b t) (c : Fin m → R)
    (hc : ∑ i, c i * t i ∈ maximalIdeal R ^ 2) (i : Fin m) : c i ∈ maximalIdeal R :=
  h.2 c (Ideal.mem_sup_left hc) i

example (b : o →+* R) (p : o) : ¬ IsRelParam b ![b p] := fun h =>
  (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 (h.2 ![1] (Ideal.mem_sup_right (by
    simpa using Ideal.mem_map_of_mem b (show p ∈ (maximalIdeal R).comap b from h.1 0))) 0))

theorem isRelParam_X (o : Type) [CommRing o] [IsLocalRing o] :
    IsRelParam (PowerSeries.C (R := o)) ![(PowerSeries.X : PowerSeries o)] := by
  have hm : ∀ f : PowerSeries o, f ∈ maximalIdeal (PowerSeries o) ↔ PowerSeries.coeff 0 f ∈ maximalIdeal o := fun f => by
    simp [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  refine ⟨fun i => by simp [hm], fun c hc i => ?_⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have h0 : ∀ f g : PowerSeries o, PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by simp
  have h1 : ∀ f g : PowerSeries o, PowerSeries.coeff 1 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 1 g + PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := fun f g => by
    rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]; simp
  let J : Ideal (PowerSeries o) :=
    { carrier := {f | PowerSeries.coeff 0 f ∈ maximalIdeal o ∧ PowerSeries.coeff 1 f ∈ maximalIdeal o}
      add_mem' := fun h h' => ⟨by simpa using add_mem h.1 h'.1, by simpa using add_mem h.2 h'.2⟩
      zero_mem' := by simp
      smul_mem' := fun f g h => ⟨h0 f g ▸ Ideal.mul_mem_left _ _ h.1,
        h1 f g ▸ add_mem (Ideal.mul_mem_left _ _ h.2) (Ideal.mul_mem_left _ _ h.1)⟩ }
  have hJ : maximalIdeal (PowerSeries o) ^ 2 ⊔ ((maximalIdeal (PowerSeries o)).comap PowerSeries.C).map PowerSeries.C ≤ J := by
    refine sup_le ?_ (Ideal.map_le_iff_le_comap.2 fun a ha => ⟨by simpa [hm] using ha, by simp [PowerSeries.coeff_C]⟩)
    rw [sq]
    refine Ideal.mul_le.2 fun f hf g hg => ?_
    rw [hm] at hf hg
    exact ⟨h0 f g ▸ Ideal.mul_mem_left _ _ hg, h1 f g ▸ add_mem (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ hg)⟩
  have := (hJ hc).2
  simpa [hm, PowerSeries.coeff_succ_mul_X] using this

end Param

section Charts

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S)
  {G : Over S} [GrpObj G] (e : F.univ.A.left ⟶ G.left)

def IsUnifOf {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (ξ : Sp R ⟶ S) {G' : Over (Sp R)} [GrpObj G']
    [IsCommMonObj G'] (π : G'.left ⟶ G.left) {D : DegData R I} {A : PolAV (Sp (FractionRing R))} (U : Unif I D A G') : Prop :=
  IsGrpPullback G' G ξ π ∧
    ∃ (y : Sp (FractionRing R) ⟶ F.X) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
      y ≫ j = jK R ≫ ξ ∧ IsGrpPullback A.A F.univ.A y α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
        U.gen.hom.left ≫ α ≫ e = pullback.fst G'.hom (jK R) ≫ π

def HasChart [IsOpenImmersion j] (φ : InvFun ℤ) (BD : EffCartierData S) (d : ℕ) (x : S) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : IsRegularLocalRing R) (b : o →+* R) (ξ : Sp R ⟶ S) (m : ℕ) (t : Fin m → R)
    (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : Fin m → R')
    (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (D : DegData R' (maximalIdeal R'))
    (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G') (γ : Fin m → LinearMap.BilinForm ℤ D.toPre.X)
    (a : Fin m → ℕ),
    (IsAdicComplete (maximalIdeal R) R ∧ ξ ≫ s = spMap b ∧ ξ (closedPoint R) = x ∧
      IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified) ∧
    (IsRelParam b t ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, t i} ∧
      ∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ i, t i ∉ p.asIdeal) ∧
    (AdmBase R' (maximalIdeal R') ∧ CharZero R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ i, r i ^ 2 = ρ (t i)) ∧
    (IsUnifOf F j e (spMap ρ ≫ ξ) π U ∧ Module.finrank ℤ D.toPre.X ≤ g ∧ IsCone id φ γ ∧
      IsMonomial D.toPre r fun i => (2 * n : ℤ) • γ i) ∧
    (∀ i, (a i : ℝ) = d * φ.evalZ ((n : ℤ) • γ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, t i ^ a i}

variable {F s j e}

theorem HasChart.idl_eq_top_iff [IsOpenImmersion j] {φ : InvFun ℤ} (hφ : IsPolFan id g φ) (hn : n ≠ 0) {BD : EffCartierData S}
    {d : ℕ} (hd : d ≠ 0) {x : S} (h : HasChart F s j e φ BD d x) :
    ReciprocityTheory.AnForm.R.FinalTheorems.stalkId BD.idealSheaf x = ⊤ ↔ x ∈ Set.range j := by
  obtain ⟨R, _, _, b, ξ, m, t, R', _, _, _, ρ, r, G', _, _, π, D, A, U, γ, a, ⟨-, -, rfl, -, -⟩, ⟨ht, -, hj⟩, -,
    ⟨-, hX, hγ, -⟩, ha, hD⟩ := h
  have pos : ∀ i, a i ≠ 0 := fun i h0 => by
    have h₁ := (hφ _ hX).pos _ (hγ.mem i) (hγ.nonneg i) (hγ.linearIndependent.ne_zero i)
    have h₂ := ha i
    rw [h0, hγ.evalZ_smul] at h₂
    have : (0 : ℝ) < d * (n * φ.evalZ (γ i)) := by positivity
    simp [← h₂] at this
  have e₁ : ReciprocityTheory.AnForm.R.FinalTheorems.stalkId BD.idealSheaf (ξ (closedPoint R)) = ⊤ ↔ idlAlong BD.idealSheaf ξ = ⊤ := by
    refine ⟨fun h => by rw [idlAlong, h, Ideal.map_top], fun h => by_contra fun h' => ?_⟩
    refine (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h.ge.trans (Ideal.map_le_iff_le_comap.2 fun c hc => ?_)))
    exact (map_mem_nonunits_iff (Scheme.stalkClosedPointTo ξ).hom c).2 (le_maximalIdeal h' hc)
  refine e₁.trans (Iff.trans ?_ (hj _).symm)
  change _ ↔ ∏ i, t i ∉ maximalIdeal R
  rw [hD, Ideal.span_singleton_eq_top, notMem_maximalIdeal, IsUnit.prod_univ_iff, IsUnit.prod_univ_iff]
  exact forall_congr' fun i => isUnit_pow_iff (pos i)

end Charts

abbrev hodge {S : Scheme.{0}} (G : Over S) [GrpObj G] (g : ℕ) : LB S := GlobalTheory.VB.det (GlobalTheory.LieVB.omega G) g

theorem isLB_hodge {S : Scheme.{0}} (G : Over S) [GrpObj G] (g : ℕ) [QuasiSeparated G.hom]
    [SmoothOfRelativeDimension g G.hom] : (hodge G g).IsLB := (GlobalTheory.LieVB.isVB_omega G g).isLB_det

end GlobalTheory.SiegelTor

namespace GlobalTheory.Published

open GlobalTheory.SiegelTor

def SiegelToroidalIntegral : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∃ φ : InvFun ℤ, IsPolFan id g φ ∧ ∀ n : ℕ, 3 ≤ n → Odd n →
    ∃ (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) (_ : IsOpenImmersion j)
      (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ),
      IsProjOver s ∧ SmoothOfRelativeDimension (g * (g + 1) / 2) s ∧ j ≫ s = F.s ∧
      (∀ x : S, x ∈ closure (Set.range j ∩ s ⁻¹' {s x})) ∧
      IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j ∧
      1 ≤ d ∧ (∀ x : S, HasChart F s j e φ BD d x) ∧
      1 ≤ N ∧ IsGenerated (lbPow (hodge G g) N) ∧
      ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (hodge G g) (N * k)) (CechPic.dual BD.lb))

end GlobalTheory.Published
