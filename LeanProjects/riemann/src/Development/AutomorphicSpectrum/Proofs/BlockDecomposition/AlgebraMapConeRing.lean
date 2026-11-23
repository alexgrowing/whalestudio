import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CombinatorialCechAcyclic

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

section Forms
variable {K : Type} [CommRing K] {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B] [Algebra K C]

theorem omMap_smul (φ : A →ₐ[K] B) {a : ℕ} (c : A) (ω : Om K A a) :
    omMap φ a (c • ω) = φ c • omMap φ a ω := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  have h := map_smul (exteriorPower.alternatingMapLinearEquiv
    { ((exteriorPower.ιMulti B a (M := Ω[B⁄K])).toMultilinearMap.restrictScalars A).compLinearMap
        fun _ => KaehlerDifferential.map K K A B with
      map_eq_zero_of_eq' := fun v i j h hij =>
        (exteriorPower.ιMulti B a (M := Ω[B⁄K])).map_eq_zero_of_eq (fun k => KaehlerDifferential.map K K A B (v k))
          (congrArg _ h) hij } : Om K A a →ₗ[A] Om K B a) c ω
  exact h.trans (algebraMap_smul B c _)

theorem omMap_ιMulti (φ : A →ₐ[K] B) {a : ℕ} (g : Fin a → Ω[A⁄K]) :
    letI : Algebra A B := φ.toRingHom.toAlgebra
    haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
    omMap φ a (exteriorPower.ιMulti A a g) = exteriorPower.ιMulti B a fun k => KaehlerDifferential.map K K A B (g k) := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem omMap_form (φ : A →ₐ[K] B) {a : ℕ} (g₀ : A) (g : Fin a → A) :
    omMap φ a (form K g₀ g) = form K (φ g₀) fun k => φ (g k) := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  unfold form
  rw [omMap_smul, omMap_ιMulti]
  congr 2
  funext k
  exact KaehlerDifferential.map_D K K A B (g k)

theorem omMap_mem_relOm (φ : A →ₐ[K] B) {I : Ideal A} {J : Ideal B} (h : ∀ x ∈ I, φ x ∈ J) (a : ℕ)
    {ω : Om K A a} (hω : ω ∈ relOm K I a) : omMap φ a ω ∈ relOm K J a := by
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g₀, g, hg, rfl⟩ := hx
    rw [omMap_form]
    refine Submodule.subset_span ⟨_, _, ?_, rfl⟩
    rcases hg with hg | ⟨k, hk⟩
    · exact Or.inl (h _ hg)
    · exact Or.inr ⟨k, h _ hk⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [omMap_smul]; exact Submodule.smul_mem _ _ hx

def relMap (φ : A →ₐ[K] B) {I : Ideal A} {J : Ideal B} (h : ∀ x ∈ I, φ x ∈ J) (a : ℕ) :
    relOm K I a →ₗ[K] relOm K J a :=
  ((omMap φ a).comp ((relOm K I a).subtype.restrictScalars K)).codRestrict ((relOm K J a).restrictScalars K)
    fun ω => omMap_mem_relOm φ h a ω.2

theorem map_map_apply (φ : A →ₐ[K] B) (χ : B →ₐ[K] C) (v : Ω[A⁄K]) :
    letI : Algebra A B := φ.toRingHom.toAlgebra
    letI : Algebra B C := χ.toRingHom.toAlgebra
    letI : Algebra A C := (χ.comp φ).toRingHom.toAlgebra
    haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
    haveI : IsScalarTower K B C := IsScalarTower.of_algHom χ
    haveI : IsScalarTower K A C := IsScalarTower.of_algHom (χ.comp φ)
    KaehlerDifferential.map K K B C (KaehlerDifferential.map K K A B v) = KaehlerDifferential.map K K A C v := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Algebra B C := χ.toRingHom.toAlgebra
  letI : Algebra A C := (χ.comp φ).toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  haveI : IsScalarTower K B C := IsScalarTower.of_algHom χ
  haveI : IsScalarTower K A C := IsScalarTower.of_algHom (χ.comp φ)
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hs : v ∈ (⊤ : Submodule A Ω[A⁄K]) := trivial
  rw [← KaehlerDifferential.span_range_derivation] at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    simp only [KaehlerDifferential.map_D]
    rfl
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx =>
    have h1 : KaehlerDifferential.map K K A B (c • x) = algebraMap A B c • KaehlerDifferential.map K K A B x := by
      rw [map_smul]; exact (algebraMap_smul B c _).symm
    rw [h1, map_smul, hx, map_smul]
    exact algebraMap_smul B c _

theorem omMap_comp (φ : A →ₐ[K] B) (χ : B →ₐ[K] C) (a : ℕ) (ω : Om K A a) :
    omMap χ a (omMap φ a ω) = omMap (χ.comp φ) a ω := by
  have hs : ω ∈ (⊤ : Submodule A (Om K A a)) := trivial
  rw [← exteriorPower.ιMulti_span] at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [omMap_ιMulti, omMap_ιMulti, omMap_ιMulti]
    congr 1
    funext k
    exact map_map_apply φ χ (v k)
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx => rw [omMap_smul, omMap_smul, omMap_smul, hx]; rfl
end Forms

section Exact
variable {ι : Type} [DecidableEq ι]

def dZ (M : Finset ι → Type) [∀ S, AddCommGroup (M S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, M (ent i)) : ∀ i : Fin (m + 2) → ι, M (ent i) := fun i =>
  ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • r (ent_comp i k.succAbove) (c (i ∘ k.succAbove))

def ExP (M : Finset ι → Type) [∀ S, AddCommGroup (M S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T) : Prop :=
  (∀ x : M ∅, (∀ i : Fin 1 → ι, r (Finset.empty_subset (ent i)) x = 0) → x = 0) ∧
  (∀ c : ∀ i : Fin 1 → ι, M (ent i), dZ M r 0 c = 0 → ∃ x : M ∅, ∀ i, r (Finset.empty_subset (ent i)) x = c i) ∧
  ∀ (m : ℕ) (c : ∀ i : Fin (m + 2) → ι, M (ent i)), dZ M r (m + 1) c = 0 → ∃ b, dZ M r m b = c

end Exact

section Model
variable (n d : ℕ)

abbrev E : Type := Fin n ⊕ Fin d

abbrev Gam : Type := E n d → ℤ

variable {n d}

def tdeg (g : Gam n d) : ℤ := ∑ j, g (Sum.inr j)

theorem tdeg_add (g g' : Gam n d) : tdeg (g + g') = tdeg g + tdeg g' := by
  simp [tdeg, Finset.sum_add_distrib]

def cone (S : Finset (Fin d)) : AddSubmonoid (Gam n d) where
  carrier := {g | (∀ l, 0 ≤ g (Sum.inl l)) ∧ (∀ j, j ∉ S → 0 ≤ g (Sum.inr j)) ∧ 0 ≤ tdeg g}
  add_mem' := fun {g g'} h h' => ⟨fun l => add_nonneg (h.1 l) (h'.1 l), fun j hj => add_nonneg (h.2.1 j hj) (h'.2.1 j hj), by
    rw [tdeg_add]; exact add_nonneg h.2.2 h'.2.2⟩
  zero_mem' := ⟨fun _ => le_rfl, fun _ _ => le_rfl, by simp [tdeg]⟩

theorem cone_mono {S T : Finset (Fin d)} (h : S ⊆ T) : (cone S : AddSubmonoid (Gam n d)) ≤ cone T :=
  fun _ hg => ⟨hg.1, fun j hj => hg.2.1 j fun hS => hj (h hS), hg.2.2⟩

def oneE (e : E n d) : Gam n d := Pi.single e 1

theorem oneE_mem (S : Finset (Fin d)) (e : E n d) : oneE e ∈ (cone S : AddSubmonoid (Gam n d)) := by
  have h0 : ∀ e', 0 ≤ oneE e e' := fun e' => by
    unfold oneE
    by_cases h : e' = e
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  exact ⟨fun _ => h0 _, fun _ _ => h0 _, Finset.sum_nonneg fun _ _ => h0 _⟩

variable (K : Type) [Field K]

abbrev Rg (M : AddSubmonoid (Gam n d)) : Type := AddMonoidAlgebra K M

abbrev R0 (n d : ℕ) (S : Finset (Fin d)) : Type := Rg (n := n) K (cone S)

abbrev Lr (n d : ℕ) : Type := Rg (n := n) (d := d) K ⊤

abbrev Bp (n d : ℕ) : Type := MvPolynomial (E n d) K

variable {K}

def incl {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') : Rg K M →ₐ[K] Rg K M' :=
  AddMonoidAlgebra.mapDomainAlgHom K K (AddSubmonoid.inclusion h)

variable (K) in

def mon {M : AddSubmonoid (Gam n d)} (g : Gam n d) (hg : g ∈ M) : Rg K M := AddMonoidAlgebra.single ⟨g, hg⟩ 1

theorem incl_mon {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') (g : Gam n d) (hg : g ∈ M) :
    incl h (mon K g hg) = mon K g (h hg) := by
  simp only [incl, mon, AddMonoidAlgebra.mapDomainAlgHom_apply]
  simp
  rfl

theorem incl_comp {M M' M'' : AddSubmonoid (Gam n d)} (h : M ≤ M') (h' : M' ≤ M'') :
    (incl (K := K) h').comp (incl h) = incl (h.trans h') := by
  refine AlgHom.ext fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single m c =>
    simp only [incl, AlgHom.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply]
    simp
    rfl

theorem mon_mul {M : AddSubmonoid (Gam n d)} (g g' : Gam n d) (hg : g ∈ M) (hg' : g' ∈ M) :
    mon K g hg * mon K g' hg' = mon K (g + g') (M.add_mem hg hg') := by
  simp only [mon, AddMonoidAlgebra.single_mul_single, mul_one]
  rfl

variable (K n) in

def poly (S : Finset (Fin d)) : Bp K n d →ₐ[K] R0 K n d S :=
  MvPolynomial.aeval fun e => mon K (oneE e) (oneE_mem S e)

instance (S : Finset (Fin d)) : Algebra (Bp K n d) (R0 K n d S) := (poly n K S).toRingHom.toAlgebra

theorem algebraMap_cone_ring (S : Finset (Fin d)) (b : Bp K n d) : algebraMap (Bp K n d) (R0 K n d S) b = poly n K S b := rfl

theorem poly_X (S : Finset (Fin d)) (e : E n d) : poly n K S (MvPolynomial.X e) = mon K (oneE e) (oneE_mem S e) := by
  simp [poly]

theorem incl_poly {S T : Finset (Fin d)} (h : S ⊆ T) (b : Bp K n d) :
    incl (cone_mono h) (poly n K S b) = poly n K T b := by
  have : (incl (cone_mono h)).comp (poly n K S) = poly n K T := by
    apply MvPolynomial.algHom_ext
    intro e
    simp only [AlgHom.comp_apply, poly_X, incl_mon]
  exact DFunLike.congr_fun this b

variable (K n) in

def I0 (S : Finset (Fin d)) : Ideal (R0 K n d S) :=
  Ideal.span {y | ∃ k, (S = ∅ ∨ k ∈ S) ∧ y = mon K (oneE (Sum.inr k)) (oneE_mem S _)}

def ratE (k j : Fin d) : Gam n d := oneE (Sum.inr j) - oneE (Sum.inr k)

theorem tdeg_oneE_inr (j : Fin d) : tdeg (oneE (Sum.inr j) : Gam n d) = 1 := by
  simp [tdeg, oneE, Pi.single_apply]

theorem ratE_mem {S : Finset (Fin d)} {k : Fin d} (hk : k ∈ S) (j : Fin d) : ratE k j ∈ (cone S : AddSubmonoid (Gam n d)) := by
  refine ⟨fun l => by simp [ratE, oneE], fun j' hj' => ?_, ?_⟩
  · have hne : j' ≠ k := fun h => hj' (h ▸ hk)
    simp only [ratE, oneE, Pi.sub_apply, Pi.single_apply, Sum.inr.injEq, if_neg hne, sub_zero]
    split_ifs <;> simp
  · have h1 := tdeg_add (ratE k j : Gam n d) (oneE (Sum.inr k))
    have h2 : (ratE k j : Gam n d) + oneE (Sum.inr k) = oneE (Sum.inr j) := by simp [ratE]
    rw [h2, tdeg_oneE_inr, tdeg_oneE_inr] at h1
    linarith

theorem cone_ideal_map_mono {S T : Finset (Fin d)} (h : S ⊆ T) (x : R0 K n d S) (hx : x ∈ I0 n K S) : incl (cone_mono h) x ∈ I0 n K T := by
  have hle : I0 n K S ≤ (I0 n K T).comap (incl (cone_mono h)) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    change incl (cone_mono h) _ ∈ I0 n K T
    rw [incl_mon]
    by_cases hT : T = ∅
    · exact Ideal.subset_span ⟨k, Or.inl hT, rfl⟩
    by_cases hkT : k ∈ T
    · exact Ideal.subset_span ⟨k, Or.inr hkT, rfl⟩
    · obtain ⟨k', hk'⟩ := Finset.nonempty_iff_ne_empty.2 hT
      have e : (oneE (Sum.inr k) : Gam n d) = oneE (Sum.inr k') + ratE k' k := by simp [ratE]
      have hm : mon K (oneE (Sum.inr k) : Gam n d) (cone_mono h (oneE_mem S _)) =
          mon K (oneE (Sum.inr k')) (oneE_mem T _) * mon K (ratE k' k) (ratE_mem hk' k) := by
        rw [mon_mul]; simp only [e]
      rw [hm]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨k', Or.inr hk', rfl⟩)
  exact hle hx

def wv (k : Fin d) : E n d → Gam n d
  | Sum.inl l => oneE (Sum.inl l)
  | Sum.inr j => if j = k then oneE (Sum.inr k) else ratE k j

theorem wv_mem {S : Finset (Fin d)} {k : Fin d} (hk : k ∈ S) (e : E n d) : wv k e ∈ (cone S : AddSubmonoid (Gam n d)) := by
  rcases e with l | j
  · exact oneE_mem S _
  · simp only [wv]
    split_ifs
    · exact oneE_mem S _
    · exact ratE_mem hk j

variable (K) in

def monL (g : Gam n d) : Lr K n d := mon K g (AddSubmonoid.mem_top g)

def dl (e : E n d) : Ω[Lr K n d⁄K] :=
  monL K (-oneE e) • KaehlerDifferential.D K (Lr K n d) (monL K (oneE e))

def wedge {a : ℕ} (f : Fin a → E n d) : Om K (Lr K n d) a := exteriorPower.ιMulti (Lr K n d) a fun i => dl (f i)

def enumD {a : ℕ} (D : {D : Finset (E n d) // D.card = a}) : Fin a → E n d := fun i =>
  finSumFinEquiv.symm ((D.1.map finSumFinEquiv.toEmbedding).orderEmbOfFin (by simpa using D.2) i)

variable (K) in

def monW {a : ℕ} (g : Gam n d) (D : {D : Finset (E n d) // D.card = a}) : Om K (Lr K n d) a :=
  monL K g • wedge (K := K) (enumD D)

def good (g : Gam n d) (D : Finset (E n d)) : Prop :=
  (∀ l, 0 ≤ g (Sum.inl l) ∧ (g (Sum.inl l) = 0 → Sum.inl l ∉ D)) ∧ 1 ≤ tdeg g

open Classical in

def Tset (g : Gam n d) (D : Finset (E n d)) : Finset (Fin d) :=
  Finset.univ.filter fun j => g (Sum.inr j) < 0 ∨ (g (Sum.inr j) = 0 ∧ Sum.inr j ∈ D)

end Model

section Chart
variable {K : Type} [Field K] {A : Type} [CommRing A] [Algebra K A] {n d : ℕ} (C : ChartRings K A n d)

def phi : Bp K n d →ₐ[K] A := MvPolynomial.aeval (Sum.elim C.x C.t)

def toR (S : Finset (Fin d)) : A →ₐ[K] C.R S := (C.res (Finset.empty_subset S)).comp C.base.symm.toAlgHom

def Aa (_C : ChartRings K A n d) : Type := A

instance : CommRing (Aa C) := inferInstanceAs (CommRing A)
instance : Algebra (Bp K n d) (Aa C) := (phi C).toRingHom.toAlgebra

def Rb (S : Finset (Fin d)) : Type := C.R S

instance (S : Finset (Fin d)) : CommRing (Rb C S) := inferInstanceAs (CommRing (C.R S))
instance (S : Finset (Fin d)) : Algebra (Aa C) (Rb C S) := (toR C S).toRingHom.toAlgebra
instance (S : Finset (Fin d)) : Algebra (Bp K n d) (Rb C S) := ((toR C S).toRingHom.comp (phi C).toRingHom).toAlgebra
instance (S : Finset (Fin d)) : IsScalarTower (Bp K n d) (Aa C) (Rb C S) := IsScalarTower.of_algebraMap_eq fun _ => rfl

def relA (S : Finset (Fin d)) (a : ℕ) : Type := relOm K (C.I S) a

instance (S : Finset (Fin d)) (a : ℕ) : AddCommGroup (relA C S a) := inferInstanceAs (AddCommGroup (relOm K (C.I S) a))
instance (S : Finset (Fin d)) (a : ℕ) : Module (C.R S) (relA C S a) := inferInstanceAs (Module (C.R S) (relOm K (C.I S) a))
instance (S : Finset (Fin d)) (a : ℕ) : Module (Aa C) (relA C S a) := Module.compHom _ (toR C S).toRingHom
instance (S : Finset (Fin d)) (a : ℕ) : Module (Bp K n d) (relA C S a) :=
  Module.compHom _ ((toR C S).toRingHom.comp (phi C).toRingHom)
instance (S : Finset (Fin d)) (a : ℕ) : IsScalarTower (Bp K n d) (Aa C) (relA C S a) :=
  ⟨fun b c y => by
    change (toR C S) (phi C b * (id c : A)) • y = (toR C S) (phi C b) • (toR C S c • y)
    rw [map_mul, mul_smul]
    rfl⟩

def thetaLin {S : Finset (Fin d)} (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)) :
    R0 K n d S →ₗ[Bp K n d] Rb C S where
  toFun := θ
  map_add' := map_add θ
  map_smul' b y := by
    change θ (poly n K S b * y) = toR C S (phi C b) * θ y
    rw [map_mul, hθ]

theorem theta_mem_I {S : Finset (Fin d)} (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b))
    (x : R0 K n d S) (hx : x ∈ I0 n K S) : θ x ∈ C.I S := by
  have hle : I0 n K S ≤ (C.I S).comap θ := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    change θ _ ∈ C.I S
    rw [← poly_X, hθ]
    refine Ideal.subset_span ⟨k, hk, ?_⟩
    simp [toR, phi]
  exact hle hx

def psi {S : Finset (Fin d)} (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)) (a : ℕ) :
    relOm K (I0 n K S) a →ₗ[Bp K n d] relA C S a where
  toFun ω := relMap θ (theta_mem_I C θ hθ) a ω
  map_add' := map_add _
  map_smul' b ω := by
    refine Subtype.ext ?_
    change omMap θ a ((b • ω : relOm K (I0 n K S) a) : Om K (R0 K n d S) a) = toR C S (phi C b) • omMap θ a (ω : Om K (R0 K n d S) a)
    rw [← hθ, ← omMap_smul]
    congr 1

theorem res_mem_I {S T : Finset (Fin d)} (h : S ⊆ T) (x : C.R S) (hx : x ∈ C.I S) : C.res h x ∈ C.I T := by
  have hle : C.I S ≤ (C.I T).comap (C.res h) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    change C.res h _ ∈ C.I T
    rw [C.res_comp]
    by_cases hT : T = ∅
    · exact Ideal.subset_span ⟨k, Or.inl hT, rfl⟩
    by_cases hkT : k ∈ T
    · exact Ideal.subset_span ⟨k, Or.inr hkT, rfl⟩
    · obtain ⟨k', hk'⟩ := Finset.nonempty_iff_ne_empty.2 hT
      rw [C.t_eq T k' hk' k]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨k', Or.inr hk', rfl⟩)
  exact hle hx

theorem res_toR {S T : Finset (Fin d)} (h : S ⊆ T) (c : A) : C.res h (toR C S c) = toR C T c := by
  simp [toR, C.res_comp]

theorem etale_Aa : Algebra.Etale (Bp K n d) (Aa C) := by
  have := C.etale
  exact this

end Chart

end GlobalTheory.CompanionTheory.SurjectionOntoH4
