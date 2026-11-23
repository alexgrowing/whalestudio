import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.Wedge

section Forms

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

def form (l l' : Module.Dual R V) : Module.Dual R (⋀[R]^2 V) :=
  exteriorPower.pairingDual R V 2 (exteriorPower.ιMulti R 2 ![l, l'])

theorem form_ιMulti (l l' : Module.Dual R V) (v : Fin 2 → V) :
    form l l' (exteriorPower.ιMulti R 2 v) = l (v 0) * l' (v 1) - l' (v 0) * l (v 1) := by
  rw [GlobalTheory.CompanionTheory.HopfC.Wedge.form, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]
  simp

theorem eq_zero_of_form {g : ℕ} (b : Module.Basis (Fin g) R V) (t : ⋀[R]^2 V)
    (h : ∀ l l', form l l' t = 0) : t = 0 := by
  refine (b.exteriorPower 2).forall_coord_eq_zero_iff.mp fun s => ?_
  rw [Module.Basis.coord_apply, exteriorPower.basis_repr_apply]
  have hv : (b.coord ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm s)) =
      ![b.coord (Set.powersetCard.ofFinEmbEquiv.symm s 0),
        b.coord (Set.powersetCard.ofFinEmbEquiv.symm s 1)] := by
    funext i
    fin_cases i <;> first | rfl | simp
  have key : exteriorPower.ιMultiDual R 2 b s =
      GlobalTheory.CompanionTheory.HopfC.Wedge.form (b.coord (Set.powersetCard.ofFinEmbEquiv.symm s 0))
        (b.coord (Set.powersetCard.ofFinEmbEquiv.symm s 1)) := by
    show exteriorPower.pairingDual R V 2
        (exteriorPower.ιMulti R 2 (b.coord ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm s))) = _
    rw [hv]
    rfl
  rw [key]
  exact h _ _

def alt {N : Type} [AddCommGroup N] [Module R N] (f : V →ₗ[R] V →ₗ[R] N)
    (h : ∀ x, f x x = 0) : V [⋀^Fin 2]→ₗ[R] N where
  toFun v := f (v 0) (v 1)
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp
  map_eq_zero_of_eq' := by
    intro v i j hv hij
    have h01 : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    show f (v 0) (v 1) = 0
    rw [h01]
    exact h _

end Forms

section Iter

variable {R : Type} [CommRing R] {H : ℕ → Type} [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)]

noncomputable def iter (L : ∀ n, H 1 →ₗ[R] H n →ₗ[R] H (n + 1)) (c : H 2) :
    (s : List (H 1)) → H (s.length + 2)
  | [] => c
  | x :: xs => L (xs.length + 2) x (iter L c xs)

variable {L : ∀ n, H 1 →ₗ[R] H n →ₗ[R] H (n + 1)}
  {D : ∀ n, Module.Dual R (H 1) → H (n + 1) →ₗ[R] H n} {τ : ∀ n, H n →ₗ[R] H n}

theorem tau_iter (hτ : ∀ n x z, τ (n + 2) (L (n + 1) x z) = L (n + 1) x (τ (n + 1) z))
    {c : H 2} (hc : τ 2 c = c) (s : List (H 1)) : τ (s.length + 2) (iter L c s) = iter L c s := by
  induction s with
  | nil => exact hc
  | cons x xs ih =>
    show τ (xs.length + 1 + 2) (L (xs.length + 1 + 1) x (GlobalTheory.CompanionTheory.HopfC.Wedge.iter L c xs)) =
      L (xs.length + 1 + 1) x (GlobalTheory.CompanionTheory.HopfC.Wedge.iter L c xs)
    exact (hτ (xs.length + 1) x _).trans (congrArg (L (xs.length + 1 + 1) x) ih)

theorem D_iter (hD : ∀ n l x z, D (n + 1) l (L (n + 1) x z) = l x • τ (n + 1) z - L n x (D n l z))
    {l : Module.Dual R (H 1)} {c : H 2} (hc : D 1 l c = 0) (s : List (H 1))
    (hs : ∀ y ∈ s, l y = 0) : D (s.length + 1) l (iter L c s) = 0 := by
  induction s with
  | nil => exact hc
  | cons x xs ih =>
    have hx : l x = 0 := hs x (by simp)
    have hxs : ∀ y ∈ xs, l y = 0 := fun y hy => hs y (by simp [hy])
    show D (xs.length + 1 + 1) l (L (xs.length + 1 + 1) x (GlobalTheory.CompanionTheory.HopfC.Wedge.iter L c xs)) = 0
    rw [hD]
    simp [hx, ih hxs]

theorem iter_eq (hD : ∀ n l x z, D (n + 1) l (L (n + 1) x z) = l x • τ (n + 1) z - L n x (D n l z))
    (hτ : ∀ n x z, τ (n + 2) (L (n + 1) x z) = L (n + 1) x (τ (n + 1) z))
    {c : H 2} (hc : τ 2 c = c) (s : List (H 1)) {l : Module.Dual R (H 1)} {x : H 1} (hx : l x = 1) :
    iter L c s = D (s.length + 2) l (iter L c (x :: s)) +
      L (s.length + 1) x (D (s.length + 1) l (iter L c s)) := by
  have h1 : D (s.length + 2) l (GlobalTheory.CompanionTheory.HopfC.Wedge.iter L c (x :: s)) =
      GlobalTheory.CompanionTheory.HopfC.Wedge.iter L c s - L (s.length + 1) x (D (s.length + 1) l (GlobalTheory.CompanionTheory.HopfC.Wedge.iter L c s)) := by
    show D (s.length + 1 + 1) l (L (s.length + 1 + 1) x (GlobalTheory.CompanionTheory.HopfC.Wedge.iter L c s)) = _
    rw [hD, hx, one_smul]
    congr 1
    exact GlobalTheory.CompanionTheory.HopfC.Wedge.tau_iter hτ hc s
  rw [h1, sub_add_cancel]

def M {J : Type} (L : ∀ n, H 1 →ₗ[R] H n →ₗ[R] H (n + 1)) (b : J → H 1) (T : Set J) (n : ℕ) :
    Submodule R (H (n + 1)) :=
  Submodule.span R {w | ∃ i ∈ T, ∃ z : H n, w = L n (b i) z}

theorem M_mono {J : Type} (b : J → H 1) {T T' : Set J} (h : T ⊆ T') (n : ℕ) :
    M L b T n ≤ M L b T' n := by
  unfold GlobalTheory.CompanionTheory.HopfC.Wedge.M
  apply Submodule.span_mono
  rintro w ⟨i, hi, z, rfl⟩
  exact ⟨i, h hi, z, rfl⟩

theorem L_mem {J : Type} (b : J → H 1) {T : Set J} {i : J} (hi : i ∈ T) (n : ℕ) (z : H n) :
    L n (b i) z ∈ M L b T n := by
  unfold GlobalTheory.CompanionTheory.HopfC.Wedge.M
  exact Submodule.subset_span ⟨i, hi, z, rfl⟩

theorem D_mem (hD : ∀ n l x z, D (n + 1) l (L (n + 1) x z) = l x • τ (n + 1) z - L n x (D n l z))
    {J : Type} (b : J → H 1) {T : Set J} {l : Module.Dual R (H 1)} (hl : ∀ j ∈ T, l (b j) = 0)
    (n : ℕ) {w : H (n + 1 + 1)} (hw : w ∈ M L b T (n + 1)) : D (n + 1) l w ∈ M L b T n := by
  have hle : GlobalTheory.CompanionTheory.HopfC.Wedge.M L b T (n + 1) ≤ (GlobalTheory.CompanionTheory.HopfC.Wedge.M L b T n).comap (D (n + 1) l) := by
    unfold GlobalTheory.CompanionTheory.HopfC.Wedge.M
    rw [Submodule.span_le]
    rintro w ⟨i, hi, z, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, hD, hl i hi, zero_smul, zero_sub]
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨i, hi, D n l z, rfl⟩)
  exact hle hw

end Iter

section Basis

variable {R : Type} [CommRing R] {H : ℕ → Type} [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)]
  {L : ∀ n, H 1 →ₗ[R] H n →ₗ[R] H (n + 1)}
  {D : ∀ n, Module.Dual R (H 1) → H (n + 1) →ₗ[R] H n} {τ : ∀ n, H n →ₗ[R] H n}
  {g : ℕ}

theorem coord_self (b : Module.Basis (Fin g) R (H 1)) (i : Fin g) : b.coord i (b i) = 1 := by
  simp

theorem coord_ne (b : Module.Basis (Fin g) R (H 1)) {i j : Fin g} (h : i ≠ j) :
    b.coord i (b j) = 0 := by
  simp [Module.Basis.coord_apply, Finsupp.single_apply, h, h.symm]

theorem eq_zero_of_iter
    (hD : ∀ n l x z, D (n + 1) l (L (n + 1) x z) = l x • τ (n + 1) z - L n x (D n l z))
    (hτ : ∀ n x z, τ (n + 2) (L (n + 1) x z) = L (n + 1) x (τ (n + 1) z))
    (b : Module.Basis (Fin g) R (H 1)) {c : H 2} (hc : τ 2 c = c)
    (hc0 : ∀ l, D 1 l c = 0) (s : List (Fin g)) (hs : s.Nodup)
    (h : iter L c (s.map b) = 0) : c = 0 := by
  have key : ∀ s : List (Fin g), s.Nodup → GlobalTheory.CompanionTheory.HopfC.Wedge.iter L c (s.map b) = 0 → c = 0 := by
    intro s
    induction s with
    | nil => exact fun _ h => h
    | cons i s ih =>
      intro hs h
      rw [List.nodup_cons] at hs
      have hx : b.coord i (b i) = 1 := GlobalTheory.CompanionTheory.HopfC.Wedge.coord_self b i
      have hzero : ∀ y ∈ s.map b, b.coord i y = 0 := by
        intro y hy
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
        exact GlobalTheory.CompanionTheory.HopfC.Wedge.coord_ne b fun hij => hs.1 (by rw [hij]; exact hj)
      have h' : GlobalTheory.CompanionTheory.HopfC.Wedge.iter L c (b i :: s.map b) = 0 := h
      apply ih hs.2
      rw [GlobalTheory.CompanionTheory.HopfC.Wedge.iter_eq hD hτ hc (s.map b) hx, h', map_zero,
        GlobalTheory.CompanionTheory.HopfC.Wedge.D_iter hD (hc0 (b.coord i)) (s.map b) hzero, map_zero, add_zero]
  exact key s hs h

theorem mem_of_iter
    (hD : ∀ n l x z, D (n + 1) l (L (n + 1) x z) = l x • τ (n + 1) z - L n x (D n l z))
    (hτ : ∀ n x z, τ (n + 2) (L (n + 1) x z) = L (n + 1) x (τ (n + 1) z))
    (b : Module.Basis (Fin g) R (H 1)) {y : H 2} (hy : τ 2 y = y)
    (s : List (Fin g)) (hs : s.Nodup) (T : Set (Fin g)) (hT : ∀ i ∈ s, i ∉ T)
    (h : iter L y (s.map b) ∈ M L b T ((s.map b).length + 1)) : y ∈ M L b Set.univ 1 := by
  have key : ∀ s : List (Fin g), s.Nodup → ∀ T : Set (Fin g), (∀ i ∈ s, i ∉ T) →
      GlobalTheory.CompanionTheory.HopfC.Wedge.iter L y (s.map b) ∈ GlobalTheory.CompanionTheory.HopfC.Wedge.M L b T ((s.map b).length + 1) →
        y ∈ GlobalTheory.CompanionTheory.HopfC.Wedge.M L b Set.univ 1 := by
    intro s
    induction s with
    | nil =>
      intro _ T _ h
      exact GlobalTheory.CompanionTheory.HopfC.Wedge.M_mono b (Set.subset_univ T) 1 h
    | cons i s ih =>
      intro hs T hT h
      rw [List.nodup_cons] at hs
      have hiT : i ∉ T := hT i (by simp)
      have hl : ∀ j ∈ T, b.coord i (b j) = 0 := fun j hj =>
        GlobalTheory.CompanionTheory.HopfC.Wedge.coord_ne b fun hij => hiT (by rw [hij]; exact hj)
      have hw : GlobalTheory.CompanionTheory.HopfC.Wedge.iter L y (b i :: s.map b) ∈
          GlobalTheory.CompanionTheory.HopfC.Wedge.M L b T ((s.map b).length + 1 + 1) := h
      have h1 := GlobalTheory.CompanionTheory.HopfC.Wedge.D_mem hD b hl ((s.map b).length + 1) hw
      have h2 := GlobalTheory.CompanionTheory.HopfC.Wedge.iter_eq hD hτ hy (s.map b)
        (GlobalTheory.CompanionTheory.HopfC.Wedge.coord_self b i)
      refine ih hs.2 (insert i T) ?_ ?_
      · intro j hj hjT
        rcases Set.mem_insert_iff.mp hjT with rfl | hjT
        · exact hs.1 hj
        · exact hT j (by simp [hj]) hjT
      · rw [h2]
        exact add_mem (GlobalTheory.CompanionTheory.HopfC.Wedge.M_mono b (Set.subset_insert i T) _ h1)
          (GlobalTheory.CompanionTheory.HopfC.Wedge.L_mem b (Set.mem_insert i T) _ _)
  exact key s hs T hT h

end Basis

theorem exteriorSquare_equiv {R : Type} [CommRing R] (H : ℕ → Type) [∀ n, AddCommGroup (H n)]
    [∀ n, Module R (H n)] (g : ℕ) (b : Module.Basis (Fin g) R (H 1)) (one : H 0)
    (L : ∀ n, H 1 →ₗ[R] H n →ₗ[R] H (n + 1))
    (D : ∀ n, Module.Dual R (H 1) → H (n + 1) →ₗ[R] H n) (τ : ∀ n, H n →ₗ[R] H n)
    (hone : ∀ r : R, r • one = 0 → r = 0) (hL0 : ∀ x, L 0 x one = x)
    (hD0 : ∀ l x, D 0 l x = l x • one)
    (hD : ∀ n l x z, D (n + 1) l (L (n + 1) x z) = l x • τ (n + 1) z - L n x (D n l z))
    (hτ : ∀ n x z, τ (n + 2) (L (n + 1) x z) = L (n + 1) x (τ (n + 1) z))
    (hτ1 : ∀ x, τ 1 x = x) (hτ2 : ∀ y, τ 2 y = y) (hS : Subsingleton (H (g + 2))) :
    ∃ e : ⋀[R]^2 (H 1) ≃ₗ[R] H 2, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = L 1 a b := by
  have hsub : ∀ n, n = g → ∀ w : H (n + 2), w = 0 := by
    rintro n rfl w
    exact @Subsingleton.elim _ hS w 0
  have hlen : (List.map b (List.finRange g)).length = g := by simp
  have hzero : ∀ w : H ((List.map b (List.finRange g)).length + 2), w = 0 := fun w => hsub _ hlen w
  have hD1 : ∀ (l : Module.Dual R (H 1)) (x y : H 1), D 1 l (L 1 x y) = l x • y - l y • x := by
    intro l x y
    have h : D 1 l (L 1 x y) = l x • τ 1 y - L 0 x (D 0 l y) := hD 0 l x y
    rw [hτ1, hD0, map_smul, hL0] at h
    exact h
  have hLxx : ∀ x : H 1, L 1 x x = 0 := by
    intro x
    refine GlobalTheory.CompanionTheory.HopfC.Wedge.eq_zero_of_iter hD hτ b (hτ2 _) ?_ (List.finRange g)
      (List.nodup_finRange g) (hzero _)
    intro l
    rw [hD1, sub_self]
  obtain ⟨φ, hφ⟩ : ∃ φ : ⋀[R]^2 (H 1) →ₗ[R] H 2,
      ∀ v : Fin 2 → H 1, φ (exteriorPower.ιMulti R 2 v) = L 1 (v 0) (v 1) :=
    ⟨exteriorPower.alternatingMapLinearEquiv (GlobalTheory.CompanionTheory.HopfC.Wedge.alt (N := H 2) (L 1) hLxx),
      fun v => exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v⟩
  have hext : ∀ l l' : Module.Dual R (H 1),
      (D 0 l').comp ((D 1 l).comp φ) = (GlobalTheory.CompanionTheory.HopfC.Wedge.form l l').smulRight one := by
    intro l l'
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearMap.smulRight_apply,
      GlobalTheory.CompanionTheory.HopfC.Wedge.form_ιMulti, hφ, hD1, hD0, map_sub, map_smul, smul_eq_mul]
    congr 1
    ring
  have key : ∀ (l l' : Module.Dual R (H 1)) (t : ⋀[R]^2 (H 1)),
      D 0 l' (D 1 l (φ t)) = GlobalTheory.CompanionTheory.HopfC.Wedge.form l l' t • one := fun l l' t =>
    LinearMap.congr_fun (hext l l') t
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    apply GlobalTheory.CompanionTheory.HopfC.Wedge.eq_zero_of_form b t
    intro l l'
    apply hone
    rw [← key l l' t, ht, map_zero, map_zero]
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : y ∈ GlobalTheory.CompanionTheory.HopfC.Wedge.M L b Set.univ 1 :=
      GlobalTheory.CompanionTheory.HopfC.Wedge.mem_of_iter hD hτ b (hτ2 y) (List.finRange g)
        (List.nodup_finRange g) ∅ (by simp)
        (by rw [hzero (GlobalTheory.CompanionTheory.HopfC.Wedge.iter L y _)]; exact Submodule.zero_mem _)
    have hle : GlobalTheory.CompanionTheory.HopfC.Wedge.M L b Set.univ 1 ≤ LinearMap.range φ := by
      unfold GlobalTheory.CompanionTheory.HopfC.Wedge.M
      rw [Submodule.span_le]
      rintro w ⟨i, -, z, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_range]
      exact ⟨exteriorPower.ιMulti R 2 ![b i, z], by simpa using hφ ![b i, z]⟩
    exact LinearMap.mem_range.mp (hle hy)
  have hbij : Function.Bijective φ := ⟨hinj, hsurj⟩
  refine ⟨LinearEquiv.ofBijective φ hbij, fun a a' => ?_⟩
  first
    | (rw [LinearEquiv.ofBijective_apply]; simpa using hφ ![a, a'])
    | exact hφ ![a, a']
    | simpa using hφ ![a, a']

end GlobalTheory.CompanionTheory.HopfC.Wedge
