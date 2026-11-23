import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc.LatBasis

theorem exists_basis_of_full {R F N V ι : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup N] [Module R N] [AddCommGroup V] [Module F V]
    (f : N →+ V) (hf : Function.Injective f)
    (hs : ∀ (c : R) (x : N), f (c • x) = algebraMap R F c • f x)
    (hfull : ∀ v : V, ∃ c : R, c ≠ 0 ∧ ∃ x : N, algebraMap R F c • v = f x)
    (b : Module.Basis ι R N) :
    ∃ bV : Module.Basis ι F V, (∀ j, bV j = f (b j)) ∧
      ∀ x i, bV.repr (f x) i = algebraMap R F (b.repr x i) := by
  letI : Module R V := Module.compHom V (algebraMap R F)
  have hsm : ∀ (c : R) (v : V), c • v = algebraMap R F c • v := fun _ _ => rfl
  haveI : IsScalarTower R F V := ⟨fun c a v => by rw [hsm, Algebra.smul_def, mul_smul]⟩
  let f' : N →ₗ[R] V := { toFun := f, map_add' := map_add f, map_smul' := hs }
  haveI : IsLocalizedModule (nonZeroDivisors R) f' :=
    { map_units := fun s => by
        rw [Module.End.isUnit_iff]
        have h0 : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
        have : ⇑(algebraMap R (Module.End R V) s) = fun v => algebraMap R F s • v := by
          ext v; rfl
        rw [this]
        exact (MulAction.toPerm (Units.mk0 _ h0) : Equiv.Perm V).bijective
      surj := fun v => by
        obtain ⟨c, hc, x, hx⟩ := hfull v
        exact ⟨(x, ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩), hx⟩
      exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }
  exact ⟨b.ofIsLocalizedModule F (nonZeroDivisors R) f',
    fun j => b.ofIsLocalizedModule_apply F _ f' j,
    fun x i => b.ofIsLocalizedModule_repr_apply F _ f' x i⟩

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {R Qp LL O : Type} [CommRing R] [IsDomain R]
  [Field Qp] [Algebra R Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
  [TopologicalSpace LL] (T : LocLat G Qp LL O) (φ : R →+* O)
  (hφ : ∀ c, algebraMap O LL (φ c) = algebraMap Qp LL (algebraMap R Qp c))
  (hint : ∀ a : LL, ∃ c : R, c ≠ 0 ∧ ∃ o : O, algebraMap O LL o = algebraMap R Qp c • a)

include hφ in
omit [IsDomain R] in

theorem smul_eq (c : R) (v : T.V) : φ c • v = algebraMap R Qp c • v := by
  rw [← algebraMap_smul LL (φ c) v, ← algebraMap_smul LL (algebraMap R Qp c) v, hφ]

include hφ hint in

theorem exists_smul_mem (v : T.V) : ∃ c : R, c ≠ 0 ∧ algebraMap R Qp c • v ∈ T.L.T := by
  have kl : ∀ (c : R) (x : T.V), x ∈ T.L.T → algebraMap R Qp c • x ∈ T.L.T := by
    intro c x hx
    rw [← smul_eq T φ hφ]
    exact T.L.T.smul_mem _ hx
  have hv : v ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, kl _ _ hx⟩
  | zero => exact ⟨1, one_ne_zero, kl _ _ T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn0, hn⟩ := hx
    obtain ⟨m, hm0, hm⟩ := hy
    refine ⟨n * m, mul_ne_zero hn0 hm0, ?_⟩
    rw [smul_add]
    refine T.L.T.add_mem ?_ ?_
    · rw [mul_comm, map_mul, mul_smul]; exact kl m _ hn
    · rw [map_mul, mul_smul]; exact kl n _ hm
  | smul a x _ hx =>
    obtain ⟨n, hn0, hn⟩ := hx
    obtain ⟨y, hy, o, ho⟩ := hint a
    refine ⟨y * n, mul_ne_zero hy hn0, ?_⟩
    have h3 := T.L.T.smul_mem o hn
    rw [← algebraMap_smul LL o, ho, smul_assoc, smul_comm a] at h3
    rw [map_mul, mul_smul]
    exact h3

include hφ hint in

theorem exists_basis_compHom [IsFractionRing R Qp] {ι : Type} :
    letI : Module R ↥T.L.T := Module.compHom ↥T.L.T φ
    ∀ b : Module.Basis ι R ↥T.L.T, ∃ bV : Module.Basis ι Qp T.V, ∀ g i j,
      algebraMap R Qp (b.repr (actT T.L g (b j)) i) = bV.repr (T.ρ g (bV j)) i := by
  letI : Module R ↥T.L.T := Module.compHom ↥T.L.T φ
  intro b
  obtain ⟨bV, h1, h2⟩ := exists_basis_of_full (F := Qp) (V := T.V) T.L.T.subtype.toAddMonoidHom
    Subtype.val_injective (fun c x => smul_eq T φ hφ c (x : T.V))
    (fun v => by
      obtain ⟨c, hc, h⟩ := exists_smul_mem T φ hφ hint v
      exact ⟨c, hc, ⟨_, h⟩, rfl⟩) b
  refine ⟨bV, fun g i j => ?_⟩
  rw [h1]
  exact (h2 (actT T.L g (b j)) i).symm

end Generic

theorem algebraMap_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (c : ℤ_[l]) :
    algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c) =
      algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] c) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem exists_multiple_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (a : ↥LL.1) :
    ∃ c : ℤ_[l], c ≠ 0 ∧ ∃ o : ↥(OL LL),
      algebraMap ↥(OL LL) ↥LL.1 o = algebraMap ℤ_[l] ℚ_[l] c • a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h2 : IsAlgebraic ℤ_[l] a :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  exact ⟨y, hy, ⟨y • a, hi⟩, (algebraMap_smul ℚ_[l] y a).symm⟩

theorem exists_basis_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ bV : Module.Basis (Fin d) ℚ_[l] T.V, ∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (bV.repr (T.ρ g (bV j)) i) := by
  intro l _ K LL T d M A hM
  obtain ⟨b, hb, -⟩ := hM
  have H := exists_basis_compHom (ι := Fin d) T (algebraMap ℤ_[l] ↥(OL LL)) (algebraMap_OL LL)
    (exists_multiple_OL LL)
  obtain ⟨bV, h⟩ := H b
  refine ⟨bV, fun g i j => ?_⟩
  exact (hb g i j).trans (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (h g i j))

end GlobalTheory.Cyc.LatBasis
