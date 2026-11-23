import Mathlib

noncomputable section

open scoped WithZero

namespace GlobalTheory.CompanionTheory.Ar.Crv

structure ACurve (K : Type) [Field K] where

  I : Type

  v : I → Valuation K (WithZero (Multiplicative ℤ))

  w : I → ℕ

  fin : ∀ x : K, x ≠ 0 → {i | v i x ≠ 1}.Finite

  prod : ∀ x : K, x ≠ 0 → ∑ᶠ i, (w i : ℤ) * WithZero.log (v i x) = 0

variable {K : Type} [Field K] (C : ACurve K)

section One

variable {V : Type} [AddCommGroup V] [Module K V]

def IsLatOf (i : C.I) {n : ℕ} (b : Module.Basis (Fin n) K V) (L : AddSubgroup V) : Prop :=
  ∀ x, x ∈ L ↔ ∀ q, C.v i (b.repr x q) ≤ 1

def IsBun (L : C.I → AddSubgroup V) : Prop :=
  (∀ i, ∃ b : Module.Basis (Fin (Module.finrank K V)) K V, IsLatOf C i b (L i)) ∧
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V, {i | ¬ IsLatOf C i b (L i)}.Finite

open Classical in

def locBasis [FiniteDimensional K V] (i : C.I) (L : AddSubgroup V) :
    Module.Basis (Fin (Module.finrank K V)) K V :=
  if h : ∃ b : Module.Basis (Fin (Module.finrank K V)) K V, IsLatOf C i b L then h.choose
  else Module.finBasis K V

def deg [FiniteDimensional K V] (L : C.I → AddSubgroup V) : ℤ :=
  ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (locBasis C i (L i))))

def sub (L : C.I → AddSubgroup V) (W : Submodule K V) : C.I → AddSubgroup W :=
  fun i => (L i).comap W.subtype.toAddMonoidHom

def quot (L : C.I → AddSubgroup V) (W : Submodule K V) : C.I → AddSubgroup (V ⧸ W) :=
  fun i => (L i).map W.mkQ.toAddMonoidHom

def subDeg [FiniteDimensional K V] (L : C.I → AddSubgroup V) (W : Submodule K V) : ℤ :=
  deg C (sub C L W)

end One

section Two

variable {V V' V'' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
  [AddCommGroup V''] [Module K V'']

def IsHom (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') : Prop :=
  ∀ i, ∀ x ∈ L i, f x ∈ L' i

def ShortExact (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'')
    (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') : Prop :=
  Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧
    (∀ i x, x ∈ L i ↔ f x ∈ L' i) ∧ ∀ i z, z ∈ L'' i ↔ ∃ y ∈ L' i, g y = z

def dualLat (L : C.I → AddSubgroup V) (B : V →ₗ[K] V' →ₗ[K] K) : C.I → AddSubgroup V' :=
  fun i =>
    { carrier := {y | ∀ x ∈ L i, C.v i (B x y) ≤ 1}
      zero_mem' := fun x _ => by simp
      add_mem' := fun {a b} ha hb x hx => by
        rw [map_add]; exact (C.v i).map_add_le (ha x hx) (hb x hx)
      neg_mem' := fun {a} ha x hx => by
        rw [map_neg, Valuation.map_neg]; exact ha x hx }

def spanLat (L : C.I → AddSubgroup V) (φ : V → V') : C.I → AddSubgroup V' :=
  fun i => AddSubgroup.closure {y | ∃ (a : K) (x : V), C.v i a ≤ 1 ∧ x ∈ L i ∧ y = a • φ x}

end Two

def frobVec (p : ℕ) {d : ℕ} (x : Fin d → K) : Fin d → K := fun j => x j ^ p

def frobLat (p : ℕ) {d : ℕ} (L : C.I → AddSubgroup (Fin d → K)) : C.I → AddSubgroup (Fin d → K) :=
  spanLat C L (frobVec p)

def frobSub (p : ℕ) {d : ℕ} (W : Submodule K (Fin d → K)) : Submodule K (Fin d → K) :=
  Submodule.span K (frobVec p '' (W : Set (Fin d → K)))

def dotDual {d : ℕ} (L : C.I → AddSubgroup (Fin d → K)) : C.I → AddSubgroup (Fin d → K) :=
  dualLat C L (dotProductBilin K K)

def eig {O V : Type} [AddCommGroup V] [Module K V] (ρ : O → V →ₗ[K] V) (χ : O → K) : Submodule K V :=
  ⨅ a, LinearMap.ker (ρ a - χ a • LinearMap.id)

def IsSplit {O k S : Type} [CommRing O] [Field k] (χ : S → (O →+* k)) : Prop :=
  Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId k (S → k))
    (Pi.algHom ℤ (fun _ : S => k) fun s => (χ s).toIntAlgHom) (fun _ _ => Commute.all _ _) :
      TensorProduct ℤ k O →ₐ[k] (S → k))

structure ConjData (p : ℕ) (O : Type) [CommRing O] [StarRing O] (d : ℕ) where

  lie : C.I → AddSubgroup (Fin d → K)

  H : C.I → AddSubgroup ((Fin d → K) × (Fin d → K))

  lie_bun : IsBun C lie

  H_bun : IsBun C H

  ρ : O →+* Matrix (Fin d) (Fin d) K

  ρH : O →+* Module.End K ((Fin d → K) × (Fin d → K))

  ρH_hom : ∀ a, IsHom C H H (ρH a)

  ρH_fst : ∀ a y, (ρH a y).1 = (ρ a).mulVec y.1

  ρH_inr : ∀ a φ, ρH a (0, φ) = (0, (ρ (star a)).transpose.mulVec φ)

  hodge : ShortExact C (dotDual C lie) H lie (LinearMap.inr K _ _) (LinearMap.fst K _ _)

  α : (Fin d → K) →ₗ[K] (Fin d → K) × (Fin d → K)

  β : ((Fin d → K) × (Fin d → K)) →ₗ[K] (Fin d → K)

  conj : ShortExact C (frobLat C p lie) H (frobLat C p (dotDual C lie)) α β

  α_act : ∀ a u, α (((ρ a).map (· ^ p)).mulVec u) = ρH a (α u)

  β_act : ∀ a y, β (ρH a y) = ((ρ (star a)).transpose.map (· ^ p)).mulVec (β y)

namespace Inhab

section Line

open Polynomial IsDedekindDomain

variable (k : Type) [Field k]

open Classical in

def lineV : Option (HeightOneSpectrum k[X]) → Valuation (RatFunc k) (WithZero (Multiplicative ℤ))
  | none => RatFunc.inftyValuation k
  | some q => q.valuation (RatFunc k)

def lineW : Option (HeightOneSpectrum k[X]) → ℕ
  | none => 1
  | some q => (Submodule.IsPrincipal.generator q.asIdeal).natDegree

def LineGood (x : RatFunc k) : Prop :=
  {i | lineV k i x ≠ 1}.Finite ∧ ∑ᶠ i, (lineW k i : ℤ) * WithZero.log (lineV k i x) = 0

theorem LineGood.supp {x : RatFunc k} (h : LineGood k x) :
    (Function.support fun i => (lineW k i : ℤ) * WithZero.log (lineV k i x)).Finite :=
  h.1.subset fun i hi h1 => hi (by simp [h1])

theorem LineGood.mul {x y : RatFunc k} (hx : x ≠ 0) (hy : y ≠ 0) (h : LineGood k x)
    (h' : LineGood k y) : LineGood k (x * y) := by
  refine ⟨(h.1.union h'.1).subset fun i hi => ?_, ?_⟩
  · by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    exact hi (by simp [hc.1, hc.2])
  · have : ∀ i, (lineW k i : ℤ) * WithZero.log (lineV k i (x * y)) =
        (lineW k i : ℤ) * WithZero.log (lineV k i x) +
          (lineW k i : ℤ) * WithZero.log (lineV k i y) := by
      intro i
      rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx)
        ((Valuation.ne_zero_iff _).2 hy), mul_add]
    simp only [this]
    rw [finsum_add_distrib (h.supp k) (h'.supp k), h.2, h'.2, add_zero]

theorem LineGood.inv {x : RatFunc k} (h : LineGood k x) : LineGood k x⁻¹ := by
  refine ⟨h.1.subset fun i hi h1 => hi (by simp [h1]), ?_⟩
  have : ∀ i, (lineW k i : ℤ) * WithZero.log (lineV k i x⁻¹) =
      -((lineW k i : ℤ) * WithZero.log (lineV k i x)) := by
    intro i
    rw [map_inv₀, WithZero.log_inv, mul_neg]
  simp only [this]
  rw [finsum_neg_distrib, h.2, neg_zero]

open Classical in

theorem lineV_none {f : k[X]} (hf : f ≠ 0) :
    lineV k none (algebraMap _ _ f) = WithZero.exp (f.natDegree : ℤ) :=
  RatFunc.inftyValuation.polynomial k hf

theorem lineV_some (q : HeightOneSpectrum k[X]) (f : k[X]) :
    lineV k (some q) (algebraMap _ _ f) = q.intValuation f :=
  q.valuation_of_algebraMap f

theorem lineGood_unit {f : k[X]} (hf : IsUnit f) : LineGood k (algebraMap _ _ f) := by
  have : ∀ i, lineV k i (algebraMap _ _ f) = 1 := by
    rintro (_ | q)
    · rw [lineV_none k hf.ne_zero, natDegree_eq_zero_of_isUnit hf]; simp
    · rw [lineV_some, q.intValuation_eq_one_iff]
      exact fun h => q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hf)
  exact ⟨by simp [this], by simp [this]⟩

theorem lineGood_prime {f : k[X]} (hf : Prime f) : LineGood k (algebraMap _ _ f) := by
  classical
  let q : HeightOneSpectrum k[X] :=
    ⟨Ideal.span {f}, (Ideal.span_singleton_prime hf.ne_zero).2 hf, by simpa using hf.ne_zero⟩
  have h1 : ∀ i, i ≠ none → i ≠ some q → lineV k i (algebraMap _ _ f) = 1 := by
    rintro (_ | r) hi hi'
    · exact absurd rfl hi
    · rw [lineV_some, r.intValuation_eq_one_iff]
      intro h
      refine hi' (congrArg some (HeightOneSpectrum.ext ?_))
      exact (q.isMaximal.eq_of_le r.isPrime.ne_top
        ((Ideal.span_singleton_le_iff_mem _).2 h)).symm
  have hs : {i | lineV k i (algebraMap _ _ f) ≠ 1} ⊆ ({none, some q} : Finset _) := by
    intro i hi
    by_contra hc
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] at hc
    exact hi (h1 i hc.1 hc.2)
  refine ⟨(Finset.finite_toSet _).subset hs, ?_⟩
  rw [finsum_eq_sum_of_support_subset (s := {none, some q}) _
    (fun i hi => hs fun h => hi (by simp [h])), Finset.sum_pair (by simp),
    lineV_none k hf.ne_zero, lineV_some, q.intValuation_singleton hf.ne_zero rfl]
  have : lineW k (some q) = f.natDegree :=
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated
      (Ideal.span_singleton_eq_span_singleton.1 (Ideal.span_singleton_generator q.asIdeal)))
  rw [this]; simp [lineW]

theorem lineGood_poly (f : k[X]) (hf : f ≠ 0) : LineGood k (algebraMap _ _ f) := by
  induction f using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hf
  | h₂ x hx => exact lineGood_unit k hx
  | h₃ a p ha hp ih =>
    rw [map_mul]
    exact (lineGood_prime k hp).mul k (by simpa using hp.ne_zero) (by simpa using ha) (ih ha)

theorem lineGood (x : RatFunc k) (hx : x ≠ 0) : LineGood k x := by
  have hn := RatFunc.num_ne_zero hx
  have hd := x.denom_ne_zero
  rw [← x.num_div_denom, div_eq_mul_inv]
  exact (lineGood_poly k _ hn).mul k (by simpa using hn) (by simpa using hd)
    ((lineGood_poly k _ hd).inv k)

def projLine : ACurve (RatFunc k) where
  I := Option (HeightOneSpectrum k[X])
  v := lineV k
  w := lineW k
  fin x hx := (lineGood k x hx).1
  prod x hx := (lineGood k x hx).2

end Line

section Const

def trivLat (d : ℕ) : C.I → AddSubgroup (Fin d → K) := fun i =>
  { carrier := {x | ∀ j, C.v i (x j) ≤ 1}
    zero_mem' := fun j => by simp
    add_mem' := fun ha hb j => (C.v i).map_add_le (ha j) (hb j)
    neg_mem' := fun ha j => by simpa using ha j }

theorem mem_trivLat {d : ℕ} {i : C.I} {x : Fin d → K} :
    x ∈ trivLat C d i ↔ ∀ j, C.v i (x j) ≤ 1 := Iff.rfl

theorem isBun_of_basis {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
    (b : Module.Basis ι K V) (L : C.I → AddSubgroup V)
    (h : ∀ i x, x ∈ L i ↔ ∀ q, C.v i (b.repr x q) ≤ 1) : IsBun C L := by
  let e : ι ≃ Fin (Module.finrank K V) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  have : ∀ i, IsLatOf C i (b.reindex e) (L i) := fun i x => by
    rw [h]; simp only [Module.Basis.repr_reindex_apply]
    exact ⟨fun H q => H _, fun H q => by simpa using H (e q)⟩
  exact ⟨fun i => ⟨_, this i⟩, b.reindex e, by simp [this]⟩

theorem mulVec_mem_trivLat {d : ℕ} {i : C.I} {M : Matrix (Fin d) (Fin d) K}
    (hM : ∀ r s, C.v i (M r s) ≤ 1) {x : Fin d → K} (hx : x ∈ trivLat C d i) :
    M.mulVec x ∈ trivLat C d i := fun r =>
  (C.v i).map_sum_le (s := Finset.univ) (f := fun s => M r s * x s) fun s _ =>
    ((C.v i).map_mul _ _).trans_le (mul_le_one' (hM r s) (hx s))

theorem single_mem_trivLat {d : ℕ} (i : C.I) (j : Fin d) :
    (Pi.single j 1 : Fin d → K) ∈ trivLat C d i := fun r => by
  by_cases h : r = j
  · subst h; simp
  · simp [h]

theorem dotDual_trivLat (d : ℕ) : dotDual C (trivLat C d) = trivLat C d := by
  funext i; ext y
  refine ⟨fun h j => ?_, fun h x hx => ?_⟩
  · simpa using h _ (single_mem_trivLat C i j)
  · exact (C.v i).map_sum_le (s := Finset.univ) (f := fun s => x s * y s) fun s _ =>
      ((C.v i).map_mul _ _).trans_le (mul_le_one' (hx s) (h s))

theorem frobLat_trivLat {p : ℕ} (hp : p ≠ 0) (d : ℕ) :
    frobLat C p (trivLat C d) = trivLat C d := by
  funext i
  refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) fun y hy => ?_
  · rintro _ ⟨a, x, ha, hx, rfl⟩ j
    simp only [Pi.smul_apply, frobVec, smul_eq_mul, map_mul, map_pow]
    exact mul_le_one' ha (pow_le_one' (hx j) p)
  · rw [← Finset.univ_sum_single y]
    refine sum_mem fun j _ => AddSubgroup.subset_closure
      ⟨y j, Pi.single j 1, hy j, single_mem_trivLat C i j, ?_⟩
    funext r
    by_cases h : r = j
    · subst h; simp [frobVec]
    · simp [frobVec, h, hp]

def constData {p : ℕ} (hp : 1 < p) {O : Type} [CommRing O] [StarRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) (hρ : ∀ a r s, ρ a r s ^ p = ρ a r s) :
    ConjData C p O d :=
  have hv : ∀ i a r s, C.v i (ρ a r s) ≤ 1 := fun i a r s => by
    by_contra hlt
    have h1 : C.v i (ρ a r s) ^ p = C.v i (ρ a r s) := by rw [← map_pow, hρ]
    exact absurd h1 (lt_self_pow₀ (not_le.1 hlt) hp).ne'
  have hm : ∀ a, (ρ a).map (· ^ p) = ρ a := fun a => by ext r s; exact hρ a r s
  { lie := trivLat C d
    H := fun i => (trivLat C d i).prod (trivLat C d i)
    lie_bun := isBun_of_basis C (Pi.basisFun K (Fin d)) _ fun i x => by simp [mem_trivLat]
    H_bun := isBun_of_basis C ((Pi.basisFun K (Fin d)).prod (Pi.basisFun K (Fin d))) _
      fun i x => by simp [AddSubgroup.mem_prod, mem_trivLat]
    ρ := ρ
    ρH :=
      { toFun := fun a => (Matrix.toLin' (ρ a)).prodMap (Matrix.toLin' (ρ (star a)).transpose)
        map_one' := by simp [Module.End.one_eq_id]
        map_mul' := fun a b => by
          simp only [star_mul, map_mul, Matrix.transpose_mul, Matrix.toLin'_mul]; rfl
        map_zero' := by simp
        map_add' := fun a b => by
          simp [star_add, Matrix.transpose_add, LinearMap.prodMap_add] }
    ρH_hom := fun a i x hx =>
      ⟨mulVec_mem_trivLat C (hv i a) hx.1, mulVec_mem_trivLat C (fun r s => hv i _ s r) hx.2⟩
    ρH_fst := fun a y => rfl
    ρH_inr := fun a φ => by simp
    hodge := by
      rw [dotDual_trivLat]
      refine ⟨LinearMap.inr_injective, Function.Exact.inr_fst, LinearMap.fst_surjective,
        fun i x => by simp [AddSubgroup.mem_prod],
        fun i z => ⟨fun h => ⟨(z, 0), ⟨h, zero_mem _⟩, rfl⟩, ?_⟩⟩
      rintro ⟨y, hy, rfl⟩; exact hy.1
    α := LinearMap.inl K _ _
    β := LinearMap.snd K _ _
    conj := by
      rw [dotDual_trivLat, frobLat_trivLat C (by omega)]
      refine ⟨LinearMap.inl_injective, Function.Exact.inl_snd, LinearMap.snd_surjective,
        fun i x => by simp [AddSubgroup.mem_prod],
        fun i z => ⟨fun h => ⟨(0, z), ⟨zero_mem _, h⟩, rfl⟩, ?_⟩⟩
      rintro ⟨y, hy, rfl⟩; exact hy.2
    α_act := fun a u => by simp [hm]
    β_act := fun a y => by rw [Matrix.transpose_map, hm]; rfl }

variable {V : Type} [AddCommGroup V] [Module K V]

def latOf (i : C.I) {n : ℕ} (b : Module.Basis (Fin n) K V) : AddSubgroup V where
  carrier := {x | ∀ q, C.v i (b.repr x q) ≤ 1}
  zero_mem' := fun q => by simp
  add_mem' := fun ha hb q => by
    rw [map_add, Finsupp.add_apply]; exact (C.v i).map_add_le (ha q) (hb q)
  neg_mem' := fun ha q => by simpa using ha q

theorem isLatOf_latOf (i : C.I) {n : ℕ} (b : Module.Basis (Fin n) K V) :
    IsLatOf C i b (latOf C i b) := fun _ => Iff.rfl

theorem v_det {i : C.I} {n : ℕ}
    {b b' : Module.Basis (Fin n) K V} {L : AddSubgroup V} (h : IsLatOf C i b L)
    (h' : IsLatOf C i b' L) : C.v i (b.det b') = 1 := by
  have key : ∀ {b b' : Module.Basis (Fin n) K V}, IsLatOf C i b L → IsLatOf C i b' L →
      C.v i (b.det b') ≤ 1 := by
    intro b b' h h'
    rw [Module.Basis.det_apply, Matrix.det_apply']
    refine (C.v i).map_sum_le fun σ _ => ?_
    rw [map_mul, map_prod]
    refine mul_le_one' ?_ (Finset.prod_le_one' fun q _ => (h _).1 ((h' _).2 fun r => ?_) _)
    · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]
    · by_cases e : q = r <;> simp [e, Finsupp.single_apply]
  have h1 : C.v i (b.det b') * C.v i (b'.det b) = 1 := by
    rw [← map_mul, Module.Basis.det_mul_det, Module.Basis.det_self, map_one]
  exact le_antisymm (key h h') (h1 ▸ mul_le_of_le_one_right' (key h' h))

theorem deg_eq [FiniteDimensional K V]
    {L : C.I → AddSubgroup V} (b : C.I → Module.Basis (Fin (Module.finrank K V)) K V)
    (h : ∀ i, IsLatOf C i (b i) (L i)) :
    deg C L = ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i))) := by
  refine finsum_congr fun i => ?_
  have hex : ∃ b : Module.Basis (Fin (Module.finrank K V)) K V, IsLatOf C i b (L i) := ⟨_, h i⟩
  have : IsLatOf C i (locBasis C i (L i)) (L i) := by
    rw [locBasis, dif_pos hex]; exact hex.choose_spec
  rw [← Module.Basis.det_mul_det _ (b i), map_mul, v_det C (h i) this, mul_one]

theorem deg_const [FiniteDimensional K V] (b : Module.Basis (Fin (Module.finrank K V)) K V) :
    deg C (fun i => latOf C i b) = 0 := by
  rw [deg_eq C (fun _ => b) fun i => isLatOf_latOf C i b]
  exact C.prod _ ((Module.finBasis K V).isUnit_det b).ne_zero

end Const

section Gauss

local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

def gaussChar : GaussianInt →+* ZMod 5 := Zsqrtd.lift ⟨2, by decide⟩

theorem gaussChar_star_ne : gaussChar (star ⟨0, 1⟩) ≠ gaussChar ⟨0, 1⟩ := by
  simp only [gaussChar, Zsqrtd.lift_apply_apply]
  decide

def gaussData (d : ℕ) : ConjData (projLine (ZMod 5)) 5 GaussianInt d :=
  constData _ (by norm_num)
    ((algebraMap (ZMod 5) (Matrix (Fin d) (Fin d) (RatFunc (ZMod 5)))).comp gaussChar)
    fun a r s => by
      by_cases h : r = s
      · have : (RatFunc.C (gaussChar a)) ^ 5 = RatFunc.C (gaussChar a) := by
          rw [← map_pow, ZMod.pow_card]
        simpa [Matrix.algebraMap_matrix_apply, h] using this
      · simp [Matrix.algebraMap_matrix_apply, h]

def gaussChars : Bool → (GaussianInt →+* ZMod 5)
  | false => gaussChar
  | true => gaussChar.comp (starRingEnd GaussianInt)

theorem isSplit_gaussChars : IsSplit gaussChars := by
  have hgen : ∀ x : TensorProduct ℤ (ZMod 5) GaussianInt, ∃ a b : ZMod 5,
      x = a ⊗ₜ (1 : GaussianInt) + b ⊗ₜ (⟨0, 1⟩ : GaussianInt) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul c z =>
      refine ⟨z.re • c, z.im • c, ?_⟩
      rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul, ← TensorProduct.tmul_add]
      congr 1
      ext <;> simp
    | add x y hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨a', b', rfl⟩ := hy
      exact ⟨a + a', b + b', by simp only [TensorProduct.add_tmul]; abel⟩
  have h0 : gaussChars false ⟨0, 1⟩ = 2 := by
    simp [gaussChars, gaussChar, Zsqrtd.lift_apply_apply]
  have h1 : gaussChars true ⟨0, 1⟩ = -2 := by
    simp [gaussChars, gaussChar, Zsqrtd.lift_apply_apply, starRingEnd_apply]
  unfold IsSplit
  set F := Algebra.TensorProduct.lift (Algebra.ofId (ZMod 5) (Bool → ZMod 5))
    (Pi.algHom ℤ (fun _ : Bool => ZMod 5) fun s => (gaussChars s).toIntAlgHom)
    (fun _ _ => Commute.all _ _) with hF
  have hv : ∀ (a b : ZMod 5) (s : Bool),
      F (a ⊗ₜ (1 : GaussianInt) + b ⊗ₜ (⟨0, 1⟩ : GaussianInt)) s
        = a + b * gaussChars s ⟨0, 1⟩ := by
    intro a b s
    simp [hF, Algebra.ofId_apply]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, b, rfl⟩ := hgen x
    have e0 := congrFun hx false
    have e1 := congrFun hx true
    rw [hv, h0] at e0
    rw [hv, h1] at e1
    have key : ∀ a b : ZMod 5, a + b * 2 = 0 → a + b * -2 = 0 → a = 0 ∧ b = 0 := by decide
    obtain ⟨rfl, rfl⟩ := key a b e0 e1
    simp
  · intro y
    have key : ∀ u w : ZMod 5, ∃ a b : ZMod 5, a + b * 2 = u ∧ a + b * -2 = w := by decide
    obtain ⟨a, b, ha, hb⟩ := key (y false) (y true)
    refine ⟨a ⊗ₜ (1 : GaussianInt) + b ⊗ₜ (⟨0, 1⟩ : GaussianInt), funext fun s => ?_⟩
    rw [hv]
    cases s
    · rw [h0, ha]
    · rw [h1, hb]

end Gauss

section Twist

variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module (RatFunc k) V]
  [FiniteDimensional (RatFunc k) V]

def twistBasis (i : (projLine k).I) :
    Module.Basis (Fin (Module.finrank (RatFunc k) V)) (RatFunc k) V :=
  Option.casesOn i ((Module.finBasis (RatFunc k) V).unitsSMul
    fun _ => Units.mk0 RatFunc.X RatFunc.X_ne_zero) fun _ => Module.finBasis (RatFunc k) V

def twistLat : (projLine k).I → AddSubgroup V := fun i => latOf (projLine k) i (twistBasis k V i)

theorem isBun_twistLat : IsBun (projLine k) (twistLat k V) := by
  refine ⟨fun i => ⟨_, isLatOf_latOf _ i _⟩, Module.finBasis (RatFunc k) V,
    (Set.finite_singleton (show (projLine k).I from none)).subset ?_⟩
  rintro (_ | q) hq
  · rfl
  · exact absurd (isLatOf_latOf _ _ _) hq

open Classical in

theorem deg_twistLat : deg (projLine k) (twistLat k V) = Module.finrank (RatFunc k) V := by
  rw [deg_eq (projLine k) (L := twistLat k V) (twistBasis k V) (fun i => isLatOf_latOf _ i _),
    finsum_eq_single _ (show (projLine k).I from none)]
  · simp only [twistBasis, Module.Basis.det_unitsSMul_self]
    simp [projLine, lineV, lineW, RatFunc.inftyValuation.X]
  · rintro (_ | q) hq
    · exact absurd rfl hq
    · simp [twistBasis, Module.Basis.det_self]

end Twist

end Inhab

end GlobalTheory.CompanionTheory.Ar.Crv
