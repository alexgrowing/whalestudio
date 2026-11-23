import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LemmaBTHoldsStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAtOneCompOfIsDiffOf
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FunctionFamilyIdempotent
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FunctionFamilyChartFacts
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestCharacterExists
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TeichmullerTest

theorem sep {B Ix : Type} [CommRing B] [Fintype Ix] [DecidableEq Ix] (b : Module.Basis Ix ℤ B) :
    ∃ y : Ix → B, (∀ {V : Type} [AddCommGroup V] (β : B →+ B →+ V) (a : B),
      Algebra.discr ℤ b • ∑ k, β (a * b k) (y k) = Algebra.discr ℤ b • ∑ k, β (b k) (a * y k)) ∧
      Algebra.discr ℤ b • ∑ k, b k * y k = Algebra.discr ℤ b • ((Algebra.discr ℤ b : ℤ) : B) := by
  set M := Algebra.traceMatrix ℤ b with hM
  set d := Algebra.discr ℤ b with hd
  have hdet : d = M.det := Algebra.discr_def ℤ b
  have hMa : ∀ i j, M i j = Algebra.trace ℤ B (b i * b j) := fun i j => by
    rw [hM, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  let y : Ix → B := fun k => ∑ l, M.adjugate k l • b l
  have h0 : ∀ j k, Algebra.trace ℤ B (b j * y k) = if k = j then d else 0 := fun j k => by
    have := congrFun (congrFun (Matrix.adjugate_mul M) k) j
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, ← hdet] at this
    simp only [y, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
    simp only [mul_comm (b j), ← hMa, this]
    simp
  have hr : ∀ x k, Algebra.trace ℤ B (x * y k) = d * b.repr x k := fun x k => by
    conv_lhs => rw [← b.sum_repr x]
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, h0, smul_eq_mul]
    simp [mul_comm]
  have h1 : ∀ x, d • x = ∑ k, Algebra.trace ℤ B (x * y k) • b k := fun x => by
    conv_lhs => rw [← b.sum_repr x]
    simp only [hr, Finset.smul_sum, mul_smul]
  have h2' : ∀ j, d • b j = ∑ k, Algebra.trace ℤ B (b j * b k) • y k := fun j => by
    simp only [y, Finset.smul_sum, smul_smul, ← hMa]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.mul_adjugate, ← hdet, Matrix.smul_apply,
      Matrix.one_apply]
    simp
  have h2 : ∀ x, d • x = ∑ k, Algebra.trace ℤ B (x * b k) • y k := fun x => by
    conv_lhs => rw [← b.sum_repr x]
    conv_rhs => rw [← b.sum_repr x]
    simp only [Finset.smul_sum, smul_comm d, h2', Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
      Finset.sum_smul, smul_assoc]
    rw [Finset.sum_comm]
  refine ⟨y, fun β a => ?_, ?_⟩
  · have e1 : ∀ k, d • β (a * b k) (y k) = ∑ l, Algebra.trace ℤ B (a * b k * y l) • β (b l) (y k) := fun k => by
      rw [← AddMonoidHom.smul_apply, ← map_zsmul, h1, map_sum β, AddMonoidHom.finsetSum_apply]
      simp only [map_zsmul, AddMonoidHom.smul_apply]
    have e2 : ∀ l, d • β (b l) (a * y l) = ∑ k, Algebra.trace ℤ B (a * y l * b k) • β (b l) (y k) := fun l => by
      rw [← map_zsmul, h2, map_sum (β (b l))]
      simp only [map_zsmul]
    simp only [Finset.smul_sum, e1, e2]
    rw [Finset.sum_comm]
    simp only [mul_right_comm a]
  · have e : ∀ a, Algebra.trace ℤ B ((∑ k, b k * y k) * a) = d * Algebra.trace ℤ B a := fun a => by
      rw [Algebra.trace_eq_matrix_trace b a, Matrix.trace, Finset.mul_sum, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, ← hr]
      congr 1
      ring
    rw [h1]
    simp only [e, mul_smul, ← Finset.smul_sum]
    have := h1 1
    simp only [_root_.one_mul] at this
    rw [← this]
    simp

theorem teich {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) {x z : R}
    (hx : x ^ p ^ n = x) (hz : z ^ p ^ n - z ∈ Ideal.span {(p : R)})
    (h : ∀ k, IsUnit (1 - (z - x) ^ (k + 1))) : z - x ∈ Ideal.span {(p : R)} := by
  set d := z - x with hd
  have hz' : z = x + d := by rw [hd]; ring
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp x d n
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hz
  rw [← hz', hx] at hr
  obtain ⟨m, hm⟩ : ∃ m, p ^ n = m + 2 := by
    have := Nat.one_lt_pow hn hp.one_lt
    exact ⟨p ^ n - 2, by omega⟩
  have h1 : d * (1 - d ^ (m + 1)) ∈ Ideal.span {(p : R)} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨x * d * r - s, ?_⟩
    rw [hm] at hr hs
    linear_combination hd - hr - hs
  exact (Ideal.mul_unit_mem_iff_mem _ (h m)).1 h1

section Abstract

variable {R : Type} [CommRing R] {O C : Type} [CommRing O] [Field C] [Algebra O C] (RC : Subalgebra O C)
  (κ : R →+* C) {T : Type} [CommGroup T] (A : Subalgebra R (T → R)) {X : Type} [AddCommGroup X]
  (s : X → T) (π : T → X) {L : Type} [AddCommGroup L] [Module R L] (θ : Module.Dual R L →ₗ[R] omega A)
  {r : ℕ} (ev : Module.Dual R L →+ (Fin r → C))

def res : (T → R) →+* (X → C) := RingHom.pi fun x => κ.comp (Pi.evalRingHom (fun _ : T => R) (s x))

omit [CommGroup T] [AddCommGroup X] in
theorem res_apply (f : T → R) (x : X) : res κ s f x = κ (f (s x)) := rfl

def WW : Submodule RC (X → C) := Submodule.span RC {g | ∃ f ∈ A, g = res κ s f}

def TH : Submodule RC ((X → C) × (Fin r → C)) :=
  Submodule.span RC {z | ∃ (f : augIdeal A) (u : Module.Dual R L), (∀ t, f.1.1 (s (π t)) = f.1.1 t) ∧
    θ u = (augIdeal A).toCotangent f ∧ z = (res κ s f.1.1, ev u)}

variable {RC κ A s π θ ev}

theorem part1 (hs0 : s 0 = 1) (hπ1 : π 1 = 0) (hπs : ∀ x, π (s x) = x)
    (hid : ∀ f ∈ A, (fun t => f (s (π t))) ∈ A) (g : X → C)
    (hg : g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (WW RC κ A s))) :
    (g, 0) ∈ TH RC κ A s π θ ev := by
  let N : Submodule RC (X → C) := Submodule.span RC
    {g | ∃ f : augIdeal A, (∀ t, f.1.1 (s (π t)) = f.1.1 t) ∧ g = res κ s f.1.1}
  have h1 : ∀ g ∈ WW RC κ A s, (fun x => g x - g 0) ∈ N := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f, hf, rfl⟩ := hg
      refine Submodule.subset_span ⟨⟨⟨fun t => f (s (π t)), hid f hf⟩ - algebraMap R A (f 1), ?_⟩, ?_, ?_⟩
      · change f (s (π 1)) - f 1 = 0
        rw [hπ1, hs0, sub_self]
      · intro t
        change f (s (π (s (π t)))) - f 1 = f (s (π t)) - f 1
        rw [hπs]
      · funext x
        change κ (f (s x)) - κ (f (s 0)) = κ (f (s (π (s x))) - f 1)
        rw [hπs, hs0, map_sub]
    | zero => convert N.zero_mem using 1; funext x; simp
    | add a b _ _ ha hb => convert N.add_mem ha hb using 1; funext x; simp only [Pi.add_apply]; ring
    | smul c a _ ha => convert N.smul_mem c ha using 1; funext x; simp only [Pi.smul_apply, smul_sub]
  have h2 : ∀ g ∈ ReciprocityTheory.PGsh.L2.augIdeal (WW RC κ A s), g ∈ N := by
    intro g hg
    have h0 : g 0 = 0 := hg.2
    have := h1 g hg.1
    simpa only [h0, sub_zero] using this
  have h3 : ∀ a ∈ N, ∀ b ∈ N, (a * b, 0) ∈ TH RC κ A s π θ ev := by
    intro a ha b hb
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨f, hf, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨f', hf', rfl⟩ := hb
        refine Submodule.subset_span ⟨⟨f.1 * f'.1, Ideal.mul_mem_left _ _ f'.2⟩, 0, fun t => ?_, ?_, ?_⟩
        · change f.1.1 (s (π t)) * f'.1.1 (s (π t)) = f.1.1 t * f'.1.1 t
          rw [hf, hf']
        · rw [map_zero, eq_comm, Ideal.toCotangent_eq_zero, sq]
          exact Ideal.mul_mem_mul f.2 f'.2
        · rw [map_zero, ← map_mul]; rfl
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => convert Submodule.add_mem _ ha hb using 1; simp [mul_add]
      | smul c a _ ha => convert Submodule.smul_mem _ c ha using 1; simp
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => convert Submodule.add_mem _ ha hb using 1; simp [add_mul]
    | smul c a _ ha => convert Submodule.smul_mem _ c ha using 1; simp
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    exact h3 a (h2 a ha) b (h2 b hb)
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => convert Submodule.add_mem _ ha hb using 1; simp
  | smul c a _ ha => convert Submodule.smul_mem _ c ha using 1; simp

theorem part2 (p : ℕ) (hθp : ∀ u, θ (p • u) = 0) (m : X → X) (α : T → T) (ρ : L →ₗ[R] L)
    (hαs : ∀ x, α (s x) = s (m x)) (hπα : ∀ t, π (α t) = m (π t))
    (hder : ∀ (f : augIdeal A) u, θ u = (augIdeal A).toCotangent f → ∃ f' : augIdeal A,
      (∀ t, f'.1.1 t = f.1.1 (α t)) ∧ θ (u ∘ₗ ρ) = (augIdeal A).toCotangent f')
    (z x : C) (hev : ∀ u, ev (u ∘ₗ ρ) = z • ev u) (c : RC) (hc : x = z + c * p)
    (g : X → C) (w : Fin r → C) (h : (g, w) ∈ TH RC κ A s π θ ev) :
    ((fun y => g (m y)), x • w) ∈ TH RC κ A s π θ ev := by
  have key : ∀ q ∈ TH RC κ A s π θ ev, ((fun y => q.1 (m y)), x • q.2) ∈ TH RC κ A s π θ ev := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨f, u, hf, hu, rfl⟩ := hq
      obtain ⟨f', hf', hu'⟩ := hder f u hu
      have a1 : (res κ s f'.1.1, ev (u ∘ₗ ρ)) ∈ TH RC κ A s π θ ev :=
        Submodule.subset_span ⟨f', _, fun t => by rw [hf', hf', hαs, ← hπα, hf], hu', rfl⟩
      have a2 : (res κ s 0, ev (p • u)) ∈ TH RC κ A s π θ ev :=
        Submodule.subset_span ⟨0, _, fun t => rfl, by rw [hθp, map_zero], rfl⟩
      convert Submodule.add_mem _ a1 (Submodule.smul_mem _ c a2) using 1
      refine Prod.ext ?_ ?_
      · funext y
        simp [res_apply, hf', hαs]
      · funext k
        simp [hev, hc, Subalgebra.smul_def]
        ring
    | zero => convert Submodule.zero_mem _ using 1; simp; rfl
    | add a b _ _ ha hb => convert Submodule.add_mem _ ha hb using 1; simp; rfl
    | smul c a _ ha =>
      convert Submodule.smul_mem _ c ha using 1
      refine Prod.ext rfl ?_
      exact smul_comm x c a.2
  exact key _ h

theorem res_sq (hs0 : s 0 = 1) (f : A) (hf : f ∈ augIdeal A ^ 2) :
    res κ s f.1 ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (WW RC κ A s)) := by
  have h : ∀ f ∈ augIdeal A, res κ s f.1 ∈ ReciprocityTheory.PGsh.L2.augIdeal (WW RC κ A s) := fun f hf =>
    ⟨Submodule.subset_span ⟨f.1, f.2, rfl⟩, by
      change κ (f.1 (s 0)) = 0
      have : f.1 1 = 0 := hf
      rw [hs0, this, map_zero]⟩
  rw [sq] at hf
  refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · exact Submodule.subset_span ⟨_, h a ha, _, h b hb, map_mul (res κ s) a.1 b.1⟩
  · exact (map_add (res κ s) a.1 b.1).symm ▸ Submodule.add_mem _ ha hb

theorem exists_dual_family [Module.Finite R L] [Module.Projective R L] :
    ∃ (n : ℕ) (v : Fin n → L) (lam : Fin n → Module.Dual R L), ∀ u : Module.Dual R L, u = ∑ l, u (v l) • lam l := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R L
  refine ⟨n, fun l => f (Pi.single l 1), fun l => (LinearMap.proj l).comp g, fun u => ?_⟩
  ext x
  have h1 : x = f (g x) := (LinearMap.congr_fun hfg x).symm
  conv_lhs => rw [h1, ← Finset.univ_sum_single (g x)]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, ← Pi.single_smul', smul_eq_mul, _root_.mul_one]

theorem part3 [Module.Finite R L] [Module.Projective R L] (hκ : ∀ a, κ a ∈ RC) (hs0 : s 0 = 1)
    {Ix : Type} [Fintype Ix] (m : Ix → X → X) (α : Ix → T → T)
    (ρ : Ix → L →ₗ[R] L) (hαs : ∀ k x, α k (s x) = s (m k x))
    (hder : ∀ k (f : augIdeal A) u, θ u = (augIdeal A).toCotangent f → ∃ f' : augIdeal A,
      (∀ t, f'.1.1 t = f.1.1 (α k t)) ∧ θ (u ∘ₗ ρ k) = (augIdeal A).toCotangent f')
    (y : Ix → R) (hv : ∀ v : L, ∃ a : Fin r → C, ∀ u : Module.Dual R L,
      κ (u (∑ k, y k • ρ k v)) = ∑ j, a j * ev u j)
    (x : Ix → RC) (c : RC) (hc : c * ∑ k, (⟨κ (y k), hκ _⟩ : RC) * x k = 1)
    (g : X → C) (hg : ∀ k z, g (m k z) = x k * g z) (h : (g, 0) ∈ TH RC κ A s π θ ev) :
    g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (WW RC κ A s)) := by
  obtain ⟨n, v, lam, hlam⟩ := exists_dual_family (R := R) (L := L)
  choose fl hfl using fun l => (augIdeal A).toCotangent_surjective (θ (lam l))
  choose a ha using fun l => hv (v l)
  set Q := ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (WW RC κ A s)) with hQ
  have key : ∀ q ∈ TH RC κ A s π θ ev,
      (fun z => ∑ k, κ (y k) * q.1 (m k z) - ∑ l, (∑ j, a l j * q.2 j) * res κ s (fl l).1.1 z) ∈ Q := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨f, u, -, hu, rfl⟩ := hq
      choose f' hf' hu' using fun k => hder k f u hu
      have e1 : (augIdeal A).toCotangent (∑ k, y k • f' k) =
          (augIdeal A).toCotangent (∑ l, u (∑ k, y k • ρ k (v l)) • fl l) := by
        have e2 := hlam (∑ k, y k • u ∘ₗ ρ k)
        have e3 := congrArg θ e2
        simp only [map_sum, map_smul, hu', ← hfl] at e3
        simp only [map_sum, LinearMap.map_smul_of_tower, e3, map_smul]
        simp
      rw [Ideal.toCotangent_eq] at e1
      convert res_sq (RC := RC) (κ := κ) hs0 _ e1 using 1
      funext z
      simp only [← ha, res_apply]
      simp [hf', hαs, map_sum]
    | zero => convert Q.zero_mem using 1; funext z; simp
    | add a b _ _ ha hb =>
      convert Q.add_mem ha hb using 1
      funext z
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
      ring
    | smul c a _ ha =>
      convert Q.smul_mem c ha using 1
      funext z
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul, mul_sub,
        Finset.mul_sum, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun _ _ => by ring
      · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  convert Q.smul_mem c (key _ h) using 1
  funext z
  have hc' : (c : C) * ∑ k, κ (y k) * (x k : C) = 1 := by
    have := congrArg (fun t : RC => (t : C)) hc
    simpa using this
  simp only [hg, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_mul, sub_zero, Pi.smul_apply,
    Subalgebra.smul_def, smul_eq_mul, ← _root_.mul_assoc, ← Finset.sum_mul]
  rw [hc', _root_.one_mul]

end Abstract

theorem mem_spanOver {O C V : Type} [CommRing O] [Field C] [Algebra O C] (RC : Subalgebra O C) [AddCommGroup V]
    [Module C V] (S : Set V) (z : V) : z ∈ spanOver RC S ↔ z ∈ Submodule.span RC S := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, e, he, rfl⟩ := hx
      exact Submodule.smul_mem _ (⟨a, ha⟩ : RC) (Submodule.subset_span he)
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | neg a _ ha => exact Submodule.neg_mem _ ha
  · intro h
    have key : ∀ c : RC, c • z ∈ spanOver RC S := by
      induction h using Submodule.span_induction with
      | mem x hx => exact fun c => AddSubgroup.subset_closure ⟨c, c.2, x, hx, rfl⟩
      | zero => intro c; rw [smul_zero]; exact AddSubgroup.zero_mem _
      | add a b _ _ ha hb => intro c; rw [smul_add]; exact AddSubgroup.add_mem _ (ha c) (hb c)
      | smul a x _ ha => intro c; rw [smul_smul]; exact ha _
    simpa using key 1

theorem unit_one_sub {O C : Type} [CommRing O] [Field C] [Algebra O C] (RC : Subalgebra O C)
    (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (a : RC) (ha : v (a : C) < 1) : IsUnit (1 - a) := by
  have h1 : v (1 - (a : C)) = 1 := v.map_one_sub_of_lt ha
  have h0 : (1 - (a : C)) ≠ 0 := by
    intro h; rw [h, map_zero] at h1; exact zero_ne_one h1
  refine IsUnit.of_mul_eq_one ⟨(1 - (a : C))⁻¹, (hv _).2 (by rw [map_inv₀, h1, inv_one])⟩ ?_
  exact Subtype.ext (mul_inv_cancel₀ h0)

theorem chi_cong (p : ℕ) [Fact p.Prime] {O C : Type} [CommRing O] [IsLocalRing O] [Field C] [Algebra O C]
    (RC : Subalgebra O C) (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1)
    {F : Type} [Field F] [Fintype F] [CharP F p] {B : Type} [CommRing B]
    (pq : (B ⧸ Ideal.span {(p : B)}) →+* F) (sc : F →+ (B ⧸ Ideal.span {(p : B)}))
    (h1 : ∀ a, pq (sc a) = a) (h2 : ∀ u a, pq u = 0 → u * sc a = 0)
    (σ : F →+* IsLocalRing.ResidueField O) (g : B →+* O)
    (hg : ∀ a, IsLocalRing.residue O (g a) = σ (pq (Ideal.Quotient.mk _ a))) (χ : F →*₀ C)
    (hχ : ∀ a (o : O), IsLocalRing.residue O o = σ a →
      χ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ a - algebraMap O C o) ≠ 1) (a : B) :
    ∃ c : RC, χ (pq (Ideal.Quotient.mk _ a)) = algebraMap O C (g a) + c * p := by
  have hpp : p.Prime := Fact.out
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  obtain ⟨hm, hnu⟩ := hχ _ _ (hg a)
  set t := pq (Ideal.Quotient.mk _ a) with ht
  have hx : χ t ∈ RC := by simpa using RC.add_mem hm (RC.algebraMap_mem (g a))
  have hlt : v (χ t - algebraMap O C (g a)) < 1 := by
    refine lt_of_le_of_ne ((hv _).1 hm) fun h => ?_
    have h0 : χ t - algebraMap O C (g a) ≠ 0 := by
      intro h'; rw [h', map_zero] at h; exact zero_ne_one h
    exact hnu _ ((hv _).2 (by rw [map_inv₀, h, inv_one])) (inv_mul_cancel₀ h0)
  obtain ⟨ε, hε⟩ := Ideal.Quotient.mk_surjective (sc 1)
  have hu : IsUnit (g ε) := by
    by_contra hnu
    have h0 : IsLocalRing.residue O (g ε) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hnu
    rw [hg, hε, h1, map_one] at h0
    exact one_ne_zero h0
  have hk : g a ^ p ^ (n : ℕ) - g a ∈ Ideal.span {(p : O)} := by
    have e1 := h2 (Ideal.Quotient.mk _ (a ^ p ^ (n : ℕ) - a)) 1 (by
      rw [map_sub, map_pow, map_sub, map_pow, ← hn, FiniteField.pow_card, sub_self])
    rw [← hε, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at e1
    obtain ⟨w, hw⟩ := e1
    have e2 := congrArg g hw
    rw [map_mul, map_mul, map_natCast, map_sub, map_pow] at e2
    exact (Ideal.mul_unit_mem_iff_mem _ hu).1 (Ideal.mem_span_singleton'.2 ⟨_, e2⟩)
  have h := teich (R := RC) hpp n.ne_zero (x := ⟨χ t, hx⟩) (z := algebraMap O RC (g a))
    (Subtype.ext (by
      change χ t ^ p ^ (n : ℕ) = χ t
      rw [← map_pow, ← hn, FiniteField.pow_card])) (by
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hk
      refine Ideal.mem_span_singleton'.2 ⟨algebraMap O RC w, ?_⟩
      rw [← map_pow, ← map_sub, ← hw, map_mul, map_natCast]) fun k => unit_one_sub RC v hv _ (by
      change v ((algebraMap O C (g a) - χ t) ^ (k + 1)) < 1
      rw [map_pow, Valuation.map_sub_swap]
      exact pow_lt_one₀ zero_le hlt (Nat.succ_ne_zero k))
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 h
  refine ⟨-w, ?_⟩
  have e : (w : C) * p = algebraMap O C (g a) - χ t := by
    have := congrArg (fun t : RC => (t : C)) hw
    simpa using this
  push_cast
  linear_combination e

theorem sum_unit (p : ℕ) [Fact p.Prime] {O C : Type} [CommRing O] [Field C] [Algebra O C]
    (RC : Subalgebra O C) (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (hvp : v (p : C) < 1)
    (d : ℤ) (hd : ¬ (p : ℤ) ∣ d) (t z : RC) (hz : z = d + t * p) : ∃ c : RC, c * z = 1 := by
  have hc : IsCoprime (p : ℤ) d := (Nat.prime_iff_prime_int.1 Fact.out).irreducible.coprime_iff_not_dvd.2 hd
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : RC) * p + b * d = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → RC) hab
  have hu := unit_one_sub RC v hv ((a - b * t) * p) (by
    change v (((a - b * t : RC) : C) * ((p : RC) : C)) < 1
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right ((hv _).1 (Subtype.prop _)) zero_le (by simpa using hvp))
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  refine ⟨u * b, ?_⟩
  rw [hz, ← hu]
  linear_combination u * h1

theorem eig_mem {B Ix Ω V : Type} [CommRing B] [Fintype Ix] [Field Ω] [CharZero Ω] [AddCommGroup V] [Module Ω V]
    (ρ : B →+* Module.End Ω V) (σ : B →+* Ω) (b y : Ix → B) (d : ℤ) (hd : d ≠ 0)
    (h : ∀ (β : B →+ B →+ V) (a : B), d • ∑ k, β (a * b k) (y k) = d • ∑ k, β (b k) (a * y k)) (w : V) :
    ∑ k, σ (y k) • ρ (b k) w ∈ eigSp ρ σ := by
  let β : B →+ B →+ V :=
    { toFun := fun x =>
        { toFun := fun z => σ z • ρ x w, map_zero' := by simp, map_add' := fun _ _ => by simp [add_smul] }
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  have hβ : ∀ x z, β x z = σ z • ρ x w := fun _ _ => rfl
  refine (Submodule.mem_iInf _).2 fun a => ?_
  have h1 := h β a
  rw [← Int.cast_smul_eq_zsmul Ω, ← Int.cast_smul_eq_zsmul Ω] at h1
  have h2 := smul_right_injective V (Int.cast_ne_zero.2 hd : (d : Ω) ≠ 0) h1
  simp only [hβ, map_mul, mul_smul, Module.End.mul_apply] at h2
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sum, Finset.smul_sum, ← h2]
  simp only [map_smul, sub_self]

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {F : Type} [Field F] {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω]
  {c' : ∀ k, J k} (P : ChartPack G O c') (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F)
  (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (C : Type) [Field C] [Algebra O C] [Algebra Ω C]

def kap (O : Type) [CommRing O] [Algebra O Ω] (y : (Σ k, J k) → Ω) (c' : ∀ k, J k) (C : Type) [Field C] [Algebra Ω C] :
    CR O y c' →+* C := (algebraMap Ω C).comp (algebraMap (CR O y c') Ω)

def evv {r : ℕ} (v : Fin r → 𝔐.Li) : Module.Dual (CR O y c') P.L →+ (Fin r → C) where
  toFun u k := algebraMap Ω C (P.j u (v k))
  map_zero' := by funext k; simp
  map_add' a b := by funext k; simp

variable {C}

theorem testOrdW_eq (RC : Subalgebra O C) :
    TestPt.testOrdW P sc RC = WW RC (kap O y c' C) (P.Γ₁.btOrder ⊤) (toN sc) := by
  unfold TestPt.testOrdW TestPt.testOrd WW
  rw [Submodule.map_span]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨_, ⟨f, hf, rfl⟩, rfl⟩

theorem toN_zero {N : ℕ} : toN sc (0 : Fin N → F) = 1 :=
  congrArg Multiplicative.ofAdd (funext fun _ => map_zero sc)

theorem fromN_one {N : ℕ} : fromN pq (1 : TorsT E N p) = 0 := funext fun _ => map_zero pq

theorem th_iff (RC : Subalgebra O C) (hsec : IsSec pq sc) {r : ℕ} (v : Fin r → 𝔐.Li)
    (θ : Module.Dual (CR O y c') P.L →ₗ[CR O y c'] omega (P.Γ₁.btOrder ⊤))
    (hθ : ∀ (f : augIdeal (P.Γ₁.btOrder ⊤)) w,
      θ w = (augIdeal (P.Γ₁.btOrder ⊤)).toCotangent f ↔ P.Γ₁.IsDerAtOne P.i₁ P.M p f.1.1 w)
    (hid : ∀ a ∈ P.Γ₁.btOrder ⊤, (fun t => a (toN sc (fromN pq t))) ∈ P.Γ₁.btOrder ⊤)
    (z : ((Fin (D.p + D.q) → F) → C) × (Fin r → C)) :
    z ∈ spanOver RC (Prod.map (bcMap Ω C _) (bcMap Ω C _) '' (thLat P pq sc v : Set _)) ↔
      z ∈ TH RC (kap O y c' C) (P.Γ₁.btOrder ⊤) (toN sc) (fromN pq) θ (evv P C v) := by
  have hπs : ∀ x : Fin (D.p + D.q) → F, fromN pq (toN sc x) = x := fun x => funext fun k => hsec.1 (x k)
  rw [mem_spanOver]
  refine ⟨fun h => (Submodule.span_le.2 ?_) h, fun h => (Submodule.span_le.2 ?_) h⟩
  · rintro _ ⟨q, hq, rfl⟩
    change (bcMap Ω C _ q.1, bcMap Ω C _ q.2) ∈ TH RC (kap O y c' C) (P.Γ₁.btOrder ⊤) (toN sc) (fromN pq) θ (evv P C v)
    induction hq using AddSubgroup.closure_induction with
    | mem q hq =>
      obtain ⟨⟨h, hh, e1⟩, h0, f, u, hf, hu, hm⟩ := hq
      have e2 : f = fun t => h (toN sc (fromN pq t)) := by
        funext t
        refine Subtype.ext ?_
        rw [hf, ← e1]
        rfl
      have hA : f ∈ P.Γ₁.btOrder ⊤ := e2 ▸ hid h hh
      have hI : (⟨f, hA⟩ : P.Γ₁.btOrder ⊤) ∈ augIdeal (P.Γ₁.btOrder ⊤) := by
        change f 1 = 0
        refine Subtype.ext ?_
        rw [hf, fromN_one, h0]
        rfl
      refine Submodule.subset_span ⟨⟨_, hI⟩, u, fun t => ?_, (hθ _ _).2 hu, Prod.ext ?_ ?_⟩
      · change f (toN sc (fromN pq t)) = f t
        refine Subtype.ext ?_
        rw [hf, hf, hπs]
      · funext x
        change algebraMap Ω C (q.1 x) = algebraMap Ω C ((f (toN sc x) : CR O y c') : Ω)
        rw [hf, hπs]
      · funext k
        exact congrArg (algebraMap Ω C) (hm k)
    | zero => rw [Prod.fst_zero, Prod.snd_zero, map_zero, map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [Prod.fst_add, Prod.snd_add, map_add, map_add]; exact Submodule.add_mem _ ha hb
    | neg a _ ha => rw [Prod.fst_neg, Prod.snd_neg, map_neg, map_neg]; exact Submodule.neg_mem _ ha
  · rintro _ ⟨f, u, hf, hu, rfl⟩
    refine Submodule.subset_span ⟨(fun x => ((f.1.1 (toN sc x) : CR O y c') : Ω), fun k => P.j u (v k)),
      AddSubgroup.subset_closure ⟨⟨f.1.1, f.1.2, rfl⟩, ?_, f.1.1, u, fun t => ?_, (hθ _ _).1 hu, fun _ => rfl⟩, rfl⟩
    · have h1 : f.1.1 1 = 0 := f.2
      change ((f.1.1 (toN sc 0) : CR O y c') : Ω) = 0
      rw [toN_zero, h1]
      rfl
    · change _ = ((f.1.1 (toN sc (fromN pq t)) : CR O y c') : Ω)
      rw [hf]

theorem toLi_comm (a : 𝓞 E) (v : P.L) : P.toLi (P.ρ a v) = 𝔐.ρ a (P.toLi v) := by
  refine 𝔐.M.inj (Over.OverMorphism.ext ?_)
  rw [P.toLi_pt, P.act a, 𝔐.act a, Over.comp_left, Over.comp_left, P.toLi_pt, Category.assoc]

theorem j_comp (a : 𝓞 E) (u : Module.Dual (CR O y c') P.L) (w : 𝔐.Li) :
    P.j (u ∘ₗ P.ρ a) w = P.j u (𝔐.ρ a w) := by
  refine P.toLi_bc.inductionOn w (fun w => P.j (u ∘ₗ P.ρ a) w = P.j u (𝔐.ρ a w)) (by simp) (fun v => ?_)
    (fun s n hn => ?_) (fun m n hm hn => ?_)
  · rw [← toLi_comm, P.j_apply, P.j_apply]
    rfl
  · simp only [map_smul, hn]
  · simp only [map_add, hm, hn]

open PositivityTheory.Xgn.FunctionFamilyIdempotent in
theorem mul_toN (hsec : IsSec pq sc) {N : ℕ} (a : 𝓞 E) (x : Fin N → F) :
    mulT N p a (toN sc x) = toN sc (pq (Ideal.Quotient.mk _ a) • x) := by
  refine congrArg Multiplicative.ofAdd (funext fun i => ?_)
  change Ideal.Quotient.mk _ a * sc (x i) = sc (pq (Ideal.Quotient.mk _ a) * x i)
  have e1 := sec_eq pq sc hsec.1 hsec.2 (Ideal.Quotient.mk _ a * sc (x i))
  have e2 := sec_eq pq sc hsec.1 hsec.2 (sc (x i))
  rw [map_mul, hsec.1] at e1
  rw [hsec.1] at e2
  rw [e1, mul_left_comm, ← e2]

open PositivityTheory.Xgn.FunctionFamilyIdempotent in
theorem fromN_mul {N : ℕ} (a : 𝓞 E) (t : TorsT E N p) :
    fromN pq (mulT N p a t) = pq (Ideal.Quotient.mk _ a) • fromN pq t :=
  funext fun i => map_mul pq (Ideal.Quotient.mk _ a) (Multiplicative.toAdd t i)

open PositivityTheory.Xgn.FunctionFamilyIdempotent in
theorem der_act [IsNoetherianRing (CR O y c')] [IsIntegrallyClosed (CR O y c')] [IsFractionRing (CR O y c') Ω]
    [Finite (TorsT E (D.p + D.q) p)]
    (θ : Module.Dual (CR O y c') P.L →ₗ[CR O y c'] omega (P.Γ₁.btOrder ⊤))
    (hθ : ∀ (f : augIdeal (P.Γ₁.btOrder ⊤)) w,
      θ w = (augIdeal (P.Γ₁.btOrder ⊤)).toCotangent f ↔ P.Γ₁.IsDerAtOne P.i₁ P.M p f.1.1 w)
    (a : 𝓞 E) (f : augIdeal (P.Γ₁.btOrder ⊤)) (u : Module.Dual (CR O y c') P.L)
    (hu : θ u = (augIdeal (P.Γ₁.btOrder ⊤)).toCotangent f) : ∃ f' : augIdeal (P.Γ₁.btOrder ⊤),
      (∀ t, f'.1.1 t = f.1.1 (mulT _ p a t)) ∧ θ (u ∘ₗ P.ρ a) = (augIdeal (P.Γ₁.btOrder ⊤)).toCotangent f' := by
  haveI := 𝔐.t.act.hom a
  haveI := frac_epi (CR O y c')
  have hα : ∀ t, (P.Γ₁.pt (mulT _ p a t)).left ≫ P.i₁ = (P.Γ₁.pt t).left ≫ P.i₁ ≫ (𝔐.t.act.act a).left := by
    intro t
    obtain ⟨x, rfl⟩ := qmk_surj _ p t
    rw [← cancel_epi (spMap (fracToField (CR O y c'))), ← P.pts₁, mulT_qmk, G.t₁.lin, Over.comp_left, P.pts₁]
    simp only [Category.assoc]
  have h4 := (GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁
    𝔐.t.semi.smooth).2.2.2.1 (𝔐.t.act.act a) (mulT _ p a) hα f.1.1 f.1.2
  have hI : (⟨_, h4⟩ : P.Γ₁.btOrder ⊤) ∈ augIdeal (P.Γ₁.btOrder ⊤) := by
    change f.1.1 (mulT _ p a 1) = 0
    rw [map_one]
    exact f.2
  exact ⟨⟨_, hI⟩, fun _ => rfl, (hθ _ _).2 (PositivityTheory.Xgn.isDerAtOne_comp_of_isDiffOf _ _ P.Γ₁ _ 𝔐.t.G P.x P.i₁ p P.tors₁
    P.L P.M (𝔐.t.act.act a) (P.ρ a) (P.act a) (mulT _ p a) hα _ _ ((hθ _ _).1 hu))⟩

end Chart

end PositivityTheory.Xgn.TeichmullerTest

open PositivityTheory.Xgn.TeichmullerTest PositivityTheory.Xgn.FunctionFamilyIdempotent in
theorem PositivityTheory.Xgn.teichmuller_test_function : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] (σ' : MulChar F RC) (ee : Sg → ℕ), (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) → ∀ τ, (∀ g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC)), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ ∀ g ∈ GlobalTheory.CompanionTheory.Ar.GR.eig (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) (σ' ^ p ^ ee τ), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC)) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hAr _ p _ hpS _ _ hdisc b hb φ _ A _ _ _ m _ hpm O _ _ _ _ _ _ _
    t₀ Sg _ e φ' F _ _ _ pq sc w σ hOrb hSec G c' hc' P i _ _ C _ _ _ _ RC hT χ hχ _ σ' ee hχσ τ
  classical
  obtain ⟨-, ⟨v, hv, hvp⟩, -, hRC⟩ := hT
  obtain ⟨-, -, -, hsurj, hσ, -⟩ := hOrb
  obtain ⟨h1, h2, h3, h4⟩ := PositivityTheory.Xgn.function_family_chart_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr p hpS A m
    hpm O c' hc'
  haveI := finite_tors (E := E) (D.p + D.q) (Fact.out : p.Prime).ne_zero
  haveI := P.fin
  haveI := P.proj
  obtain ⟨θ, ⟨-, hθ⟩, hθp, -⟩ := (GlobalTheory.T.LemmaBT_holds (CR O y c') (TorsT E (D.p + D.q) p) P.Γ₁ _ 𝔐.t.G P.x p P.i₁ P.tors₁
    𝔐.t.semi.smooth).2.2.2.2.2 P.L P.M
  have hid := PositivityTheory.Xgn.function_family_idempotent E H D l Xo c O₀ β Y S Ω K J y 𝔐 p G O c' P F pq sc hsurj hSec
  have hπs : ∀ x : Fin (D.p + D.q) → F, fromN pq (toN sc x) = x := fun x => funext fun k => hSec.1 (x k)
  have hTh : ∀ z, z ∈ ((chartD e b pq sc w P i).bc RC).Th τ ↔ _ := th_iff P pq sc RC hSec (b (e τ)) θ hθ hid
  have hκ : ∀ a, kap O y c' C a ∈ RC := fun a => hRC _ a.2
  have hinj := PositivityTheory.Xgn.TestCharacter.inj_loc (Ω := Ω) (O := O) m
  obtain ⟨g₀, hg₀⟩ := PositivityTheory.Xgn.TestCharacter.exists_lift (A := A) (𝔐.emb (e τ))
  obtain ⟨g, hg⟩ : ∃ g : 𝓞 E →+* O, ∀ t, algebraMap O Ω (g t) = 𝔐.emb (e τ) t :=
    ⟨(algebraMap A O).comp g₀, fun t => by rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, hg₀]⟩
  have hres : ∀ a, IsLocalRing.residue O (g a) = σ τ (pq (Ideal.Quotient.mk _ a)) := fun a => by
    obtain ⟨o, ho, ho'⟩ := hσ τ a
    rw [← ho', hinj (ho.trans (hg a).symm)]
  have hcong := chi_cong p RC v hv pq sc hSec.1 hSec.2 (σ τ) g hres (χ τ) (hχ τ)
  have hbv : ∀ k a, 𝔐.ρ a (b (e τ) k) = 𝔐.emb (e τ) a • b (e τ) k := fun k a => by
    have h : b (e τ) k ∈ 𝔐.Vgen (e τ) := (hb (e τ)).2 ▸ Submodule.subset_span ⟨k, rfl⟩
    exact sub_eq_zero.1 ((Submodule.mem_iInf _).1 h a)
  rw [testOrdW_eq]
  refine ⟨fun f hf => (hTh _).2 (part1 (toN_zero sc) (fromN_one pq) hπs hid f hf), fun a f n hf => ?_,
    fun f hf h0 => ?_⟩
  · obtain ⟨a, rfl⟩ := hsurj a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨t, ht⟩ := hcong a
    refine (hTh _).2 (part2 p (fun u => (hθp _).2 ⟨u, rfl⟩) (fun x => pq (Ideal.Quotient.mk _ a) • x) (mulT _ p a) (P.ρ a)
      (mul_toN pq sc hSec a) (fromN_mul pq a) (der_act P θ hθ a) _ _ (fun u => ?_) t ht f n ((hTh _).1 hf))
    funext k
    change algebraMap Ω C (P.j (u ∘ₗ P.ρ a) (b (e τ) k)) = algebraMap O C (g a) * algebraMap Ω C (P.j u (b (e τ) k))
    rw [j_comp, hbv, map_smul, smul_eq_mul, map_mul, IsScalarTower.algebraMap_apply O Ω C, hg]
  · obtain ⟨z, hz, hz'⟩ := sep (RingOfIntegers.basis E)
    rw [NumberField.discr_eq_discr] at hz hz'
    have hd0 : NumberField.discr E ≠ 0 := NumberField.discr_ne_zero E
    have hsum : ∑ k, RingOfIntegers.basis E k * z k = ((NumberField.discr E : ℤ) : 𝓞 E) :=
      smul_right_injective _ hd0 hz'
    choose t ht using fun k => hcong (RingOfIntegers.basis E k)
    have hk : ∀ a, kap O y c' C (algebraMap O (CR O y c') a) = algebraMap O C a := fun a =>
      (IsScalarTower.algebraMap_apply O Ω C a).symm
    obtain ⟨u, hu⟩ := sum_unit p RC v hv hvp _ hdisc (∑ k, algebraMap O RC (g (z k)) * t k)
      (∑ k, (⟨kap O y c' C (algebraMap O (CR O y c') (g (z k))), hκ _⟩ : RC) *
        (σ' ^ p ^ ee τ) (pq (Ideal.Quotient.mk _ (RingOfIntegers.basis E k)))) (by
      have e1 := congrArg ((algebraMap O C).comp g) hsum
      rw [map_intCast, map_sum] at e1
      apply Subtype.ext
      push_cast
      rw [← e1, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hχσ, ht, hk, map_mul]
      simp only [RingHom.comp_apply, Subalgebra.coe_algebraMap]
      ring)
    refine part3 hκ (toN_zero sc) (fun k x => pq (Ideal.Quotient.mk _ (RingOfIntegers.basis E k)) • x)
      (fun k => mulT _ p (RingOfIntegers.basis E k)) (fun k => P.ρ (RingOfIntegers.basis E k))
      (fun k => mul_toN pq sc hSec _) (fun k => der_act P θ hθ _)
      (fun k => algebraMap O (CR O y c') (g (z k))) (fun x => ?_) _ u hu f (fun k x => hf.2 _ x) ((hTh _).1 h0)
    have h5 : ∑ k, 𝔐.emb (e τ) (z k) • 𝔐.ρ (RingOfIntegers.basis E k) (P.toLi x) ∈
        Submodule.span Ω (Set.range (b (e τ))) := by
      rw [(hb (e τ)).2]
      exact eig_mem 𝔐.ρ (𝔐.emb (e τ)) _ z _ hd0 (fun β a => hz β a) _
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 h5
    refine ⟨fun j => algebraMap Ω C (a j), fun u => ?_⟩
    have h6 : P.toLi (∑ k, algebraMap O (CR O y c') (g (z k)) • P.ρ (RingOfIntegers.basis E k) x) =
        ∑ j, a j • b (e τ) j := by
      rw [ha, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, toLi_comm, ← hg]
      rfl
    change algebraMap Ω C (algebraMap (CR O y c') Ω _) = ∑ j, algebraMap Ω C (a j) * algebraMap Ω C (P.j u (b (e τ) j))
    rw [← P.j_apply, h6, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul, map_mul]
