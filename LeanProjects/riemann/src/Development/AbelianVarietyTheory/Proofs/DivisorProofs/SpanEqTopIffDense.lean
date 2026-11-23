import Mathlib

namespace GlobalTheory.Morita

structure MatrixUnits (R : Type*) [CommRing R] (N : Type*) [AddCommGroup N] [Module R N]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where

  E : ι → ι → Module.End R N
  mul_eq : ∀ i j k l, E i j * E k l = if j = k then E i l else 0
  sum_diag : ∑ i, E i i = 1

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace MatrixUnits

variable (U : MatrixUnits R N ι)

theorem apply_apply (i j k l : ι) (x : N) : U.E i j (U.E k l x) = if j = k then U.E i l x else 0 := by
  have h := LinearMap.congr_fun (U.mul_eq i j k l) x
  rw [Module.End.mul_apply] at h
  rw [h]; split_ifs <;> simp

theorem sum_apply (x : N) : ∑ i, U.E i i x = x := by
  have h := LinearMap.congr_fun U.sum_diag x
  simpa [LinearMap.sum_apply] using h

def corner (a : ι) : Submodule R N := LinearMap.range (U.E a a)

theorem mem_corner_iff (a : ι) (x : N) : x ∈ U.corner a ↔ U.E a a x = x := by
  constructor
  · rintro ⟨y, rfl⟩; rw [U.apply_apply]; simp
  · intro h; exact ⟨x, h⟩

theorem apply_mem_corner (a i : ι) (x : N) : U.E a i x ∈ U.corner a := ⟨U.E a i x, by rw [U.apply_apply]; simp⟩

def toPi (a : ι) : N ≃ₗ[R] (ι → U.corner a) where
  toFun x i := ⟨U.E a i x, U.apply_mem_corner a i x⟩
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp
  invFun v := ∑ i, U.E i a (v i)
  left_inv x := by
    simp only
    conv_rhs => rw [← U.sum_apply x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [U.apply_apply]; simp
  right_inv v := by
    ext j
    simp only [map_sum, U.apply_apply]
    simp [(U.mem_corner_iff a _).1 (v j).2]

theorem toPi_apply (a : ι) (x : N) (i : ι) : ((U.toPi a x) i : N) = U.E a i x := rfl

theorem toPi_symm_apply (a : ι) (v : ι → U.corner a) : (U.toPi a).symm v = ∑ i, U.E i a (v i) := rfl

theorem toPi_E (a i j : ι) (x : N) : U.toPi a (U.E i j x) = Pi.single i (U.toPi a x j) := by
  ext k
  rw [toPi_apply, U.apply_apply]
  by_cases h : k = i
  · subst h; simp [toPi_apply]
  · simp [h, Pi.single_apply]

end MatrixUnits

def stdUnits (M : Type*) [AddCommGroup M] [Module R M] : MatrixUnits R (ι → M) ι where
  E i j := LinearMap.single R (fun _ => M) i ∘ₗ LinearMap.proj j
  mul_eq i j k l := by
    ext x m
    by_cases h : j = k
    · subst h; simp [Pi.single_apply]
    · simp [h, Pi.single_apply]
  sum_diag := by
    ext x m
    simp [LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]

end GlobalTheory.Morita

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def ofModule [Module (Matrix ι ι R) N] [IsScalarTower R (Matrix ι ι R) N] : MatrixUnits R N ι where
  E i j := Algebra.lsmul R R N (Matrix.single i j (1 : R))
  mul_eq i j k l := by
    rw [← map_mul]
    by_cases h : j = k
    · subst h; rw [Matrix.single_mul_single_same]; simp
    · rw [Matrix.single_mul_single_of_ne (h := h)]; simp [h]
  sum_diag := by
    rw [← map_sum, Matrix.sum_single_one, map_one]

theorem ofModule_E [Module (Matrix ι ι R) N] [IsScalarTower R (Matrix ι ι R) N] (i j : ι) (x : N) :
    (ofModule (R := R)).E i j x = Matrix.single i j (1 : R) • x := rfl
end GlobalTheory.Morita

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

theorem toPi_corner (a : ι) (y : U.corner a) : U.toPi a y = Pi.single a y := by
  ext i
  rw [toPi_apply, ← (U.mem_corner_iff a _).1 y.2, U.apply_apply]
  by_cases h : i = a
  · subst h; simp [(U.mem_corner_iff i _).1 y.2]
  · simp [h, Pi.single_apply, Ne.symm h]

def IsStable (L : Submodule R N) : Prop := ∀ i j, ∀ x ∈ L, U.E i j x ∈ L

def cornerPart (a : ι) (L : Submodule R N) : Submodule R (U.corner a) := L.comap (U.corner a).subtype

def spread (a : ι) (L₀ : Submodule R (U.corner a)) : Submodule R N :=
  (Submodule.pi Set.univ fun _ => L₀).comap (U.toPi a).toLinearMap

theorem mem_cornerPart {a : ι} {L : Submodule R N} {y : U.corner a} : y ∈ U.cornerPart a L ↔ (y : N) ∈ L :=
  Iff.rfl

theorem mem_spread {a : ι} {L₀ : Submodule R (U.corner a)} {x : N} :
    x ∈ U.spread a L₀ ↔ ∀ i, U.toPi a x i ∈ L₀ := by
  simp [spread, Submodule.mem_pi]

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

theorem mem_of_forall {L : Submodule R N} (hL : U.IsStable L) (a : ι) {x : N} (h : ∀ i, U.E a i x ∈ L) : x ∈ L := by
  rw [← (U.toPi a).symm_apply_apply x, toPi_symm_apply]
  exact L.sum_mem fun i _ => hL i a _ (h i)

theorem spread_isStable (a : ι) (L₀ : Submodule R (U.corner a)) : U.IsStable (U.spread a L₀) := by
  intro i j x hx
  rw [mem_spread] at hx ⊢
  intro k
  rw [toPi_E]
  by_cases h : k = i
  · subst h; simpa using hx j
  · simp [Pi.single_apply, h, L₀.zero_mem]

theorem cornerPart_spread (a : ι) (L₀ : Submodule R (U.corner a)) : U.cornerPart a (U.spread a L₀) = L₀ := by
  ext y
  rw [mem_cornerPart, mem_spread, toPi_corner]
  constructor
  · intro h; simpa using h a
  · intro h i
    by_cases hi : i = a
    · subst hi; simpa using h
    · simp [Pi.single_apply, hi, L₀.zero_mem]

theorem spread_cornerPart {L : Submodule R N} (hL : U.IsStable L) (a : ι) : U.spread a (U.cornerPart a L) = L := by
  ext x
  rw [mem_spread]
  constructor
  · intro h; exact U.mem_of_forall hL a fun i => h i
  · intro h i; exact hL a i x h

def latIso (a : ι) : {L : Submodule R N // U.IsStable L} ≃o Submodule R (U.corner a) where
  toFun L := U.cornerPart a L.1
  invFun L₀ := ⟨U.spread a L₀, U.spread_isStable a L₀⟩
  left_inv L := Subtype.ext (U.spread_cornerPart L.2 a)
  right_inv L₀ := U.cornerPart_spread a L₀
  map_rel_iff' {L L'} := by
    constructor
    · intro h
      show L.1 ≤ L'.1
      rw [← U.spread_cornerPart L.2 a, ← U.spread_cornerPart L'.2 a]
      intro x hx
      rw [mem_spread] at hx ⊢
      exact fun i => h (hx i)
    · intro h y hy; exact h hy

theorem latIso_apply (a : ι) (L : {L : Submodule R N // U.IsStable L}) : U.latIso a L = U.cornerPart a L.1 := rfl

theorem latIso_symm_apply (a : ι) (L₀ : Submodule R (U.corner a)) : ((U.latIso a).symm L₀).1 = U.spread a L₀ := rfl

theorem map_toPi {L : Submodule R N} (hL : U.IsStable L) (a : ι) :
    L.map (U.toPi a).toLinearMap = Submodule.pi Set.univ fun _ => U.cornerPart a L := by
  conv_lhs => rw [← U.spread_cornerPart hL a]
  rw [spread, Submodule.map_comap_eq_of_surjective (U.toPi a).surjective]

def partEquiv {L : Submodule R N} (hL : U.IsStable L) (a : ι) : L ≃ₗ[R] (ι → U.cornerPart a L) where
  toFun x i := ⟨U.toPi a x i, hL a i x x.2⟩
  map_add' x y := by ext i; simp [toPi_apply]
  map_smul' r x := by ext i; simp [toPi_apply]
  invFun v := ⟨(U.toPi a).symm fun i => (v i : U.corner a), by
    rw [toPi_symm_apply]; exact L.sum_mem fun i _ => hL i a _ (v i).2⟩
  left_inv x := by ext1; simp
  right_inv v := by ext i; simp

theorem smul_mem_iff {L L' : Submodule R N} (hL : U.IsStable L) (hL' : U.IsStable L') (a : ι) (r : R) :
    (∀ x ∈ L, r • x ∈ L') ↔ ∀ y ∈ U.cornerPart a L, r • y ∈ U.cornerPart a L' := by
  constructor
  · intro h y hy; exact h _ hy
  · intro h x hx
    refine U.mem_of_forall hL' a fun i => ?_
    rw [map_smul]
    exact h ⟨U.E a i x, U.apply_mem_corner a i x⟩ (hL a i x hx)

section semilinear

variable {σ : R →+* R} (F : N →ₛₗ[σ] N)

def cornerMap (a : ι) (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) : U.corner a →ₛₗ[σ] U.corner a :=
  (F.domRestrict (U.corner a)).codRestrict (U.corner a) fun y => by
    rw [U.mem_corner_iff]
    simp only [LinearMap.domRestrict_apply]
    rw [← hF, (U.mem_corner_iff a _).1 y.2]

theorem cornerMap_apply (a : ι) (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) (y : U.corner a) :
    (U.cornerMap F a hF y : N) = F y := rfl

theorem toPi_map (a : ι) (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) (x : N) :
    U.toPi a (F x) = fun i => U.cornerMap F a hF (U.toPi a x i) := by
  ext i; simp [toPi_apply, cornerMap_apply, hF]

theorem map_mem_iff (a : ι) (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) {L : Submodule R N} (hL : U.IsStable L) :
    (∀ x ∈ L, F x ∈ L) ↔ ∀ y ∈ U.cornerPart a L, U.cornerMap F a hF y ∈ U.cornerPart a L := by
  constructor
  · intro h y hy; exact h _ hy
  · intro h x hx
    refine U.mem_of_forall hL a fun i => ?_
    rw [← hF]
    exact h ⟨U.E a i x, U.apply_mem_corner a i x⟩ (hL a i x hx)

theorem isStable_span_image (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) {L : Submodule R N} (hL : U.IsStable L) :
    U.IsStable (Submodule.span R (F '' L)) := by
  intro i j
  have : Submodule.span R (F '' L) ≤ (Submodule.span R (F '' L)).comap (U.E i j) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rw [← hF]
    exact Submodule.subset_span ⟨_, hL i j x hx, rfl⟩
  exact fun x hx => this hx

theorem cornerPart_span_image (a : ι) (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) {L : Submodule R N}
    (hL : U.IsStable L) :
    U.cornerPart a (Submodule.span R (F '' L)) =
      Submodule.span R (U.cornerMap F a hF '' U.cornerPart a L) := by
  apply le_antisymm
  · intro y hy
    have key : (Submodule.span R (F '' L)).map (U.E a a) ≤
        (Submodule.span R (U.cornerMap F a hF '' U.cornerPart a L)).map (U.corner a).subtype := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨U.cornerMap F a hF ⟨U.E a a x, U.apply_mem_corner a a x⟩,
        Submodule.subset_span ⟨_, hL a a x hx, rfl⟩, ?_⟩
      simp [cornerMap_apply, hF]
    obtain ⟨z, hz, hzy⟩ := key ⟨(y : N), hy, (U.mem_corner_iff a _).1 y.2⟩
    have : z = y := Subtype.ext hzy
    rwa [← this]
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩

end semilinear

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

theorem map_partEquiv_comap {L L' : Submodule R N} (hL : U.IsStable L) (hL' : U.IsStable L') (a : ι) :
    (L'.comap L.subtype).map (U.partEquiv hL a).toLinearMap =
      Submodule.pi Set.univ fun _ => (U.cornerPart a L').comap (U.cornerPart a L).subtype := by
  ext v
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies,
    Submodule.subtype_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    exact hL' a i x hx
  · intro h
    refine ⟨(U.partEquiv hL a).symm v, ?_, by simp⟩
    refine U.mem_of_forall hL' a fun i => ?_
    have := h i
    have e : ((U.partEquiv hL a) ((U.partEquiv hL a).symm v) i : N) = U.E a i ((U.partEquiv hL a).symm v : N) := rfl
    rw [LinearEquiv.apply_symm_apply] at e
    rw [← e]; exact this

theorem length_quotient {L L' : Submodule R N} (hL : U.IsStable L) (hL' : U.IsStable L') (a : ι) :
    Module.length R (L ⧸ L'.comap L.subtype) =
      Fintype.card ι * Module.length R (U.cornerPart a L ⧸ (U.cornerPart a L').comap (U.cornerPart a L).subtype) := by
  rw [(Submodule.Quotient.equiv _ _ (U.partEquiv hL a) (U.map_partEquiv_comap hL hL' a)).length_eq,
    (Submodule.quotientPi _).length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

theorem fg_iff {L : Submodule R N} (hL : U.IsStable L) (a : ι) :
    L.FG ↔ (U.cornerPart a L).FG := by
  rw [← Module.Finite.iff_fg, ← Module.Finite.iff_fg]
  constructor
  · intro h
    have : Module.Finite R (ι → U.cornerPart a L) := Module.Finite.equiv (U.partEquiv hL a)
    exact Module.Finite.of_surjective (LinearMap.proj a : (ι → U.cornerPart a L) →ₗ[R] _)
      (fun y => ⟨Pi.single a y, by simp⟩)
  · intro h
    exact Module.Finite.equiv (U.partEquiv hL a).symm

theorem dense_iff {L : Submodule R N} (hL : U.IsStable L) (a : ι) :
    (∀ x : N, ∃ r ∈ nonZeroDivisors R, r • x ∈ L) ↔
      ∀ y : U.corner a, ∃ r ∈ nonZeroDivisors R, r • y ∈ U.cornerPart a L := by
  constructor
  · intro h y
    obtain ⟨r, hr, hx⟩ := h y
    exact ⟨r, hr, hx⟩
  · intro h x
    choose r hr hrx using fun i => h (U.toPi a x i)
    refine ⟨∏ i, r i, prod_mem fun i _ => hr i, U.mem_of_forall hL a fun i => ?_⟩
    rw [map_smul]
    have e : (∏ j, r j) = (∏ j ∈ Finset.univ.erase i, r j) * r i :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    rw [e, mul_smul]
    exact L.smul_mem _ (hrx i)

theorem toPi_E_std (a i j : ι) (x : N) :
    U.toPi a (U.E i j x) = (stdUnits (R := R) (U.corner a)).E i j (U.toPi a x) := by
  rw [toPi_E]; ext k; simp [stdUnits, Pi.single_apply]

section extend

variable {σ : R →+* R}

def extend (a : ι) (F₀ : U.corner a →ₛₗ[σ] U.corner a) : N →ₛₗ[σ] N where
  toFun x := ∑ i, U.E i a (F₀ (U.toPi a x i))
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum]

theorem toPi_extend (a : ι) (F₀ : U.corner a →ₛₗ[σ] U.corner a) (x : N) :
    U.toPi a (U.extend a F₀ x) = fun i => F₀ (U.toPi a x i) := by
  rw [show U.extend a F₀ x = (U.toPi a).symm (fun i => F₀ (U.toPi a x i)) from rfl,
    LinearEquiv.apply_symm_apply]

theorem extend_comm (a : ι) (F₀ : U.corner a →ₛₗ[σ] U.corner a) :
    ∀ i j x, U.extend a F₀ (U.E i j x) = U.E i j (U.extend a F₀ x) := by
  intro i j x
  apply (U.toPi a).injective
  rw [toPi_extend, toPi_E, toPi_E, toPi_extend]
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem cornerMap_extend (a : ι) (F₀ : U.corner a →ₛₗ[σ] U.corner a) :
    U.cornerMap (U.extend a F₀) a (U.extend_comm a F₀) = F₀ := by
  ext y
  rw [cornerMap_apply]
  apply (U.toPi a).injective
  rw [toPi_extend, toPi_corner, toPi_corner]
  funext k
  by_cases h : k = a
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem extend_cornerMap (a : ι) (F : N →ₛₗ[σ] N) (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) :
    U.extend a (U.cornerMap F a hF) = F := by
  ext x
  apply (U.toPi a).injective
  rw [toPi_extend, U.toPi_map F a hF]

def semilinearEquiv (a : ι) :
    {F : N →ₛₗ[σ] N // ∀ i j x, F (U.E i j x) = U.E i j (F x)} ≃ (U.corner a →ₛₗ[σ] U.corner a) where
  toFun F := U.cornerMap F.1 a F.2
  invFun F₀ := ⟨U.extend a F₀, U.extend_comm a F₀⟩
  left_inv F := Subtype.ext (U.extend_cornerMap a F.1 F.2)
  right_inv F₀ := U.cornerMap_extend a F₀

end extend

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

def stdCornerEquiv (M : Type*) [AddCommGroup M] [Module R M] (a : ι) :
    (stdUnits (R := R) (ι := ι) M).corner a ≃ₗ[R] M where
  toFun v := (v : ι → M) a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := ⟨Pi.single a m, (MatrixUnits.mem_corner_iff _ _ _).2 (by ext i; simp [stdUnits, Pi.single_apply])⟩
  left_inv v := by
    have h := ((stdUnits (R := R) (ι := ι) M).mem_corner_iff a v).1 v.2
    apply Subtype.ext
    conv_rhs => rw [← h]
    ext i; simp [stdUnits]
  right_inv m := by simp

end GlobalTheory.Morita

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]

theorem span_eq_top_iff_dense (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [Module K N]
    [IsScalarTower R K N] (L : Submodule R N) :
    Submodule.span K (L : Set N) = ⊤ ↔ ∀ x : N, ∃ r ∈ nonZeroDivisors R, r • x ∈ L := by
  haveI : Nontrivial R := nontrivial_of_ne 0 1 fun h => by
    have := congrArg (algebraMap R K) h; simp at this
  constructor
  · intro h x
    have hx : x ∈ Submodule.span K (L : Set N) := h ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, one_mem _, by simpa using hy⟩
    | zero => exact ⟨1, one_mem _, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨r, hr, hry⟩ := hy
      obtain ⟨s, hs, hsz⟩ := hz
      refine ⟨r * s, mul_mem hr hs, ?_⟩
      rw [smul_add]
      refine L.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact L.smul_mem _ hry
      · rw [mul_smul]; exact L.smul_mem _ hsz
    | smul k y _ hy =>
      obtain ⟨r, hr, hry⟩ := hy
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
      have hB : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      have hc : algebraMap R K b * (algebraMap R K a / algebraMap R K b) = algebraMap R K a := by
        field_simp
      have e : (b * r) • ((algebraMap R K a / algebraMap R K b) • y) = a • (r • y) := by
        rw [mul_comm b r, mul_smul, ← algebraMap_smul K b, smul_smul, hc, algebraMap_smul, smul_comm]
      exact ⟨b * r, mul_mem hb hr, e ▸ L.smul_mem a hry⟩
  · intro h
    rw [eq_top_iff]
    intro x _
    obtain ⟨r, hr, hx⟩ := h x
    have hB : algebraMap R K r ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr
    have e : x = (algebraMap R K r)⁻¹ • (r • x) := by
      rw [← algebraMap_smul K r x, smul_smul, inv_mul_cancel₀ hB, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

end GlobalTheory.Morita

universe w

namespace GlobalTheory.Morita

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

open MatrixUnits in

theorem morita_lattices (U : MatrixUnits R N ι) (a : ι) {σ : R →+* R} (F : N →ₛₗ[σ] N)
    (hF : ∀ i j x, F (U.E i j x) = U.E i j (F x)) :
    (∀ i j x, U.toPi a (U.E i j x) = Pi.single i (U.toPi a x j)) ∧
    (∀ L : Submodule R N, U.IsStable L → U.spread a (U.cornerPart a L) = L) ∧
    (∀ L₀ : Submodule R (U.corner a), U.IsStable (U.spread a L₀) ∧ U.cornerPart a (U.spread a L₀) = L₀) ∧
    (∀ L : Submodule R N, U.IsStable L →
      Nonempty (L ≃ₗ[R] (ι → U.cornerPart a L)) ∧
      L.map (U.toPi a).toLinearMap = Submodule.pi Set.univ fun _ => U.cornerPart a L) ∧
    (∀ x, U.toPi a (F x) = fun i => U.cornerMap F a hF (U.toPi a x i)) ∧
    (∀ L : Submodule R N, U.IsStable L →
      ((∀ x ∈ L, F x ∈ L) ↔ ∀ y ∈ U.cornerPart a L, U.cornerMap F a hF y ∈ U.cornerPart a L) ∧
      U.IsStable (Submodule.span R (F '' L)) ∧
      U.cornerPart a (Submodule.span R (F '' L)) = Submodule.span R (U.cornerMap F a hF '' U.cornerPart a L)) ∧
    (∀ L L' : Submodule R N, U.IsStable L → U.IsStable L' →
      (∀ r : R, (∀ x ∈ L, r • x ∈ L') ↔ ∀ y ∈ U.cornerPart a L, r • y ∈ U.cornerPart a L') ∧
      Module.length R (L ⧸ L'.comap L.subtype) =
        Fintype.card ι * Module.length R (U.cornerPart a L ⧸ (U.cornerPart a L').comap (U.cornerPart a L).subtype)) ∧
    (∀ i j x, U.toPi a (U.E i j x) = (stdUnits (R := R) (U.corner a)).E i j (U.toPi a x)) ∧
    (∀ L : Submodule R N, U.IsStable L →
      (L.FG ↔ (U.cornerPart a L).FG) ∧
      ((∀ x : N, ∃ r ∈ nonZeroDivisors R, r • x ∈ L) ↔
        ∀ y : U.corner a, ∃ r ∈ nonZeroDivisors R, r • y ∈ U.cornerPart a L)) ∧
    (∀ (K : Type w) [Field K] [Algebra R K] [IsFractionRing R K] [Module K N] [IsScalarTower R K N]
      (L : Submodule R N), Submodule.span K (L : Set N) = ⊤ ↔ ∀ x : N, ∃ r ∈ nonZeroDivisors R, r • x ∈ L) ∧
    (∃ e : {G : N →ₛₗ[σ] N // ∀ i j x, G (U.E i j x) = U.E i j (G x)} ≃ (U.corner a →ₛₗ[σ] U.corner a),
      ∀ G, e G = U.cornerMap G.1 a G.2) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module R M],
      ∃ e : (stdUnits (R := R) (ι := ι) M).corner a ≃ₗ[R] M, ∀ v, e v = (v : ι → M) a) :=
  ⟨fun i j x => U.toPi_E a i j x, fun _ hL => U.spread_cornerPart hL a,
    fun L₀ => ⟨U.spread_isStable a L₀, U.cornerPart_spread a L₀⟩,
    fun _ hL => ⟨⟨U.partEquiv hL a⟩, U.map_toPi hL a⟩, fun x => U.toPi_map F a hF x,
    fun _ hL => ⟨U.map_mem_iff F a hF hL, U.isStable_span_image F hF hL, U.cornerPart_span_image F a hF hL⟩,
    fun _ _ hL hL' => ⟨fun r => U.smul_mem_iff hL hL' a r, U.length_quotient hL hL' a⟩,
    fun i j x => U.toPi_E_std a i j x, fun _ hL => ⟨U.fg_iff hL a, U.dense_iff hL a⟩,
    fun K _ _ _ _ _ L => span_eq_top_iff_dense K L, ⟨U.semilinearEquiv a, fun _ => rfl⟩,
    fun M _ _ => ⟨stdCornerEquiv M a, fun _ => rfl⟩⟩

example : (Pi.single 0 1 : Fin 2 → ℤ) ∈ (stdUnits (R := ℤ) (ι := Fin 2) ℤ).corner 0 ∧ (Pi.single 0 1 : Fin 2 → ℤ) ≠ 0 := by
  refine ⟨(MatrixUnits.mem_corner_iff _ _ _).2 ?_, ?_⟩
  · ext i; fin_cases i <;> simp [stdUnits]
  · intro h; have := congrFun h 0; simp at this

end GlobalTheory.Morita
