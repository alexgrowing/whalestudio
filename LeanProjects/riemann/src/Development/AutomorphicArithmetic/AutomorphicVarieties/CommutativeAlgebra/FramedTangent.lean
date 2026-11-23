import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhGroup

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

noncomputable section

namespace UpperTheory.V.Alg.FramedTangent

section Abstract

variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
  {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (i : B →ₐ[O] R)

private theorem res_k (x : ResidueField O) :
    haveI := (co_res O).1
    res O (ResidueField O) x = x := by
  haveI := (co_res O).1
  obtain ⟨a, rfl⟩ := residue_surjective x
  exact (res O (ResidueField O)).commutes a

private theorem res_dual (x : DualNumber (ResidueField O)) :
    haveI := (co_res O).2
    res O (DualNumber (ResidueField O)) x = x.fst := by
  haveI := (co_res O).1
  haveI := (co_res O).2
  rw [← res_map (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)), res_k]
  rfl

private theorem fst_map (f : R →ₐ[O] DualNumber (ResidueField O)) (y : R) : (f y).fst = res O R y := by
  haveI := (co_res O).2
  rw [← res_dual, res_map]

private theorem snd_mul (f : R →ₐ[O] DualNumber (ResidueField O)) (y z : R) :
    (f (y * z)).snd = res O R y * (f z).snd + (f y).snd * res O R z := by
  rw [map_mul, DualNumber.snd_mul, fst_map, fst_map]

private theorem snd_alg (f : R →ₐ[O] DualNumber (ResidueField O)) (a : O) : (f (algebraMap O R a)).snd = 0 := by
  rw [AlgHom.commutes]; rfl

private theorem snd_zero (f : R →ₐ[O] DualNumber (ResidueField O)) (hf : ∀ b, (f (i b)).snd = 0) (S : Set R)
    (hS : S ⊆ maximalIdeal R) (h : ∀ s ∈ S, (f s).snd = 0) (y : R)
    (hy : y ∈ Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2) : (f y).snd = 0 := by
  have : Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 ≤ RingHom.ker f := by
    refine sup_le (sup_le (Ideal.span_le.2 fun s hs => ?_) (Ideal.map_le_iff_le_comap.2 fun b hb => ?_)) ?_
    · show f s = 0
      ext
      · rw [fst_map]; exact (res_eq_zero_iff O R s).2 (hS hs)
      · exact h s hs
    · show f (i b) = 0
      ext
      · rw [fst_map, res_map]; exact (res_eq_zero_iff O B b).2 hb
      · exact hf b
    · rw [sq, Ideal.mul_le]
      intro a ha b hb
      show f (a * b) = 0
      rw [← res_eq_zero_iff O] at ha hb
      ext
      · rw [fst_map, map_mul, ha, zero_mul]; rfl
      · rw [snd_mul, ha, hb]; simp
  have h2 : f y = 0 := this hy
  rw [h2]; rfl

private theorem span_of (S : Set R) (hS : S ⊆ maximalIdeal R)
    (H : ∀ f : R →ₐ[O] DualNumber (ResidueField O), (∀ b, (f (i b)).snd = 0) → (∀ s ∈ S, (f s).snd = 0) →
      ∀ y, (f y).snd = 0) :
    maximalIdeal R ≤ Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 := by
  refine co_span O R B i S hS fun f f' h1 h2 => ?_
  let g : R →ₐ[O] DualNumber (ResidueField O) :=
    { toFun := fun y => (res O R y, (f y).snd - (f' y).snd)
      map_one' := by
        ext
        · exact map_one (res O R)
        · show (f 1).snd - (f' 1).snd = 0
          simp
      map_mul' := fun y z => by
        ext
        · exact map_mul (res O R) y z
        · show (f (y * z)).snd - (f' (y * z)).snd =
            res O R y * ((f z).snd - (f' z).snd) + ((f y).snd - (f' y).snd) * res O R z
          rw [snd_mul, snd_mul]; ring
      map_zero' := by
        ext
        · exact map_zero (res O R)
        · show (f 0).snd - (f' 0).snd = 0
          simp
      map_add' := fun y z => by
        ext
        · exact map_add (res O R) y z
        · show (f (y + z)).snd - (f' (y + z)).snd = ((f y).snd - (f' y).snd) + ((f z).snd - (f' z).snd)
          simp only [map_add, TrivSqZeroExt.snd_add]; ring
      commutes' := fun a => by
        ext
        · exact (res O R).commutes a
        · show (f (algebraMap O R a)).snd - (f' (algebraMap O R a)).snd = 0
          rw [snd_alg, snd_alg, sub_zero] }
  have := H g (fun b => by
      show (f (i b)).snd - (f' (i b)).snd = 0
      rw [show f (i b) = f' (i b) from DFunLike.congr_fun h1 b, sub_self])
    fun s hs => by
      show (f s).snd - (f' s).snd = 0
      rw [h2 s hs, sub_self]
  ext y
  · rw [fst_map, fst_map]
  · exact sub_eq_zero.1 (this y)

private theorem dual_basis {k H S : Type} [Field k] [AddCommGroup H] [Module k H] [Finite S]
    (l : S → Module.Dual k H) (hl : ∀ x, (∀ s, l s x = 0) → x = 0) :
    ∃ (κ : Type) (a : κ → S), Function.Injective a ∧ Nat.card κ = Module.finrank k H ∧
      (∀ x, (∀ t, l (a t) x = 0) → x = 0) ∧ ∀ t, ∃ x, l (a t) x = 1 ∧ ∀ t', t' ≠ t → l (a t') x = 0 := by
  classical
  haveI : FiniteDimensional k H :=
    FiniteDimensional.of_injective (LinearMap.pi l) ((injective_iff_map_eq_zero _).2 fun x hx =>
      hl x fun s => congrFun hx s)
  obtain ⟨κ, a, ha, h1, h2⟩ := exists_linearIndependent' k l
  have h3 : Submodule.span k (Set.range l) = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span k (Set.range l))]
    have : (Submodule.span k (Set.range l)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_dualCoannihilator] at hx
      exact hl x fun s => hx _ (Submodule.subset_span ⟨s, rfl⟩)
    rw [this, Submodule.dualAnnihilator_bot]
  let b : Module.Basis κ k (Module.Dual k H) := Module.Basis.mk h2 (by rw [h1, h3])
  have hb : ∀ t, b t = l (a t) := fun t => Module.Basis.mk_apply _ _ t
  refine ⟨κ, a, ha, ?_, fun x hx => ?_, fun t => ?_⟩
  · rw [← Subspace.dual_finrank_eq, Module.finrank_eq_nat_card_basis b]
  · rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro φ
    have : Module.Dual.eval k H x = 0 := b.ext fun t => by rw [hb]; exact hx t
    exact DFunLike.congr_fun this φ
  · obtain ⟨x, hx⟩ := (Module.evalEquiv k H).surjective (b.coord t)
    have : ∀ t', l (a t') x = b.coord t (b t') := fun t' => by rw [← hx, hb]; rfl
    refine ⟨x, by simp [this], fun t' h => ?_⟩
    simp [this, Finsupp.single_apply, h]

private theorem abstract {S X : Type} (z : S → R) (hz : ∀ s, z s ∈ maximalIdeal R) (wt : S → X) (H : X → Type)
    [∀ j, AddCommGroup (H j)] [∀ j, Module (ResidueField O) (H j)]
    (l : ∀ j, S → Module.Dual (ResidueField O) (H j))
    (ha : ∀ j s x, wt s ≠ j → l j s x = 0) (hb : ∀ j x, (∀ s, l j s x = 0) → x = 0)
    (hc : ∀ j x, ∃ f : R →ₐ[O] DualNumber (ResidueField O), (∀ b, (f (i b)).snd = 0) ∧ ∀ s, (f (z s)).snd = l j s x)
    (hd : ∀ f : R →ₐ[O] DualNumber (ResidueField O), (∀ b, (f (i b)).snd = 0) → ∀ j, ∃ x, ∀ s, wt s = j →
      l j s x = (f (z s)).snd)
    (he : ∀ f : R →ₐ[O] DualNumber (ResidueField O), (∀ b, (f (i b)).snd = 0) → (∀ s, (f (z s)).snd = 0) →
      ∀ y, (f y).snd = 0) :
    ∃ (τ : Type) (_ : Fintype τ) (u : τ → S),
      maximalIdeal R ≤ Ideal.span (Set.range (z ∘ u)) ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 ∧
      (∀ c : τ → O, ∑ t, c t • (z ∘ u) t ∈ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 →
        ∀ t, c t ∈ maximalIdeal O) ∧
      ∀ j, Nat.card {t // (wt ∘ u) t = j} = Module.finrank (ResidueField O) (H j) := by
  classical
  have h1 := span_of i (Set.range z) (by rintro _ ⟨s, rfl⟩; exact hz s)
    fun f h h' => he f h fun s => h' _ ⟨s, rfl⟩
  obtain ⟨S0, hS0⟩ : ∃ S0 : Finset S,
      maximalIdeal R ≤ Ideal.span (z '' S0) ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 := by
    have hfg : (Ideal.span (Set.range z)).FG := IsNoetherian.noetherian _
    obtain ⟨T, hT, hT'⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
    obtain ⟨S0, rfl⟩ : ∃ S0 : Finset S, T = S0.image z := by
      rw [← Set.image_univ] at hT
      obtain ⟨S0, -, h⟩ := Finset.subset_set_image_iff.1 hT
      exact ⟨S0, h.symm⟩
    refine ⟨S0, ?_⟩
    rw [← Finset.coe_image]
    exact h1.trans (le_of_eq (by rw [Ideal.span, hT']))
  have h2 : ∀ j x, (∀ s : {s : S0 // wt s = j}, l j s.1 x = 0) → x = 0 := fun j x hx => by
    obtain ⟨f, hf, hf'⟩ := hc j x
    refine hb j x fun s => ?_
    rw [← hf']
    refine snd_zero i f hf _ ?_ ?_ _ (hS0 (hz s))
    · rintro _ ⟨s, -, rfl⟩; exact hz s
    · rintro _ ⟨s, hs, rfl⟩
      rw [hf']
      by_cases e : wt s = j
      · exact hx ⟨⟨s, hs⟩, e⟩
      · exact ha j s x e
  choose κ a a1 a2 a3 a4 using fun j => dual_basis (fun s : {s : S0 // wt s = j} => l j s.1) (h2 j)
  haveI : Finite (Σ j, κ j) := by
    refine Finite.of_injective (fun t : Σ j, κ j => (a t.1 t.2).1) ?_
    rintro ⟨j, t⟩ ⟨j', t'⟩ e
    have e' : (a j t).1 = (a j' t').1 := e
    obtain rfl : j = j' := by rw [← (a j t).2, ← (a j' t').2, e']
    rw [a1 j (Subtype.ext e')]
  refine ⟨Σ j, κ j, Fintype.ofFinite _, fun t => (a t.1 t.2).1, ?_, fun c hcm t => ?_, fun j => ?_⟩
  · refine span_of i _ (by rintro _ ⟨s, rfl⟩; exact hz _) fun f h h' => he f h fun s => ?_
    obtain ⟨x, hx⟩ := hd f h (wt s)
    have : x = 0 := a3 _ x fun t => (hx _ (a _ t).2).trans (h' _ ⟨⟨_, t⟩, rfl⟩)
    rw [← hx s rfl, this, map_zero]
  · obtain ⟨j, t⟩ := t
    obtain ⟨x, x1, x2⟩ := a4 j t
    obtain ⟨f, hf, hf'⟩ := hc j x
    have h3 := snd_zero i f hf ∅ (Set.empty_subset _) (by simp) _ (by
      rw [sup_assoc]; exact Ideal.mem_sup_right hcm)
    rw [map_sum, TrivSqZeroExt.snd_sum, Finset.sum_eq_single ⟨j, t⟩] at h3
    · rw [map_smul, TrivSqZeroExt.snd_smul, Function.comp_apply, hf', x1, Algebra.smul_def, mul_one] at h3
      exact (residue_eq_zero_iff _).1 h3
    · rintro ⟨j', t'⟩ - e
      rw [map_smul, TrivSqZeroExt.snd_smul, Function.comp_apply, hf']
      by_cases e' : j' = j
      · subst e'
        rw [x2 t' fun n => e (by rw [n]), smul_zero]
      · rw [ha j _ x (by rw [(a j' t').2]; exact e'), smul_zero]
    · simp
  · rw [← a2]
    refine (Nat.card_congr (Equiv.ofBijective (fun t : κ j => ⟨⟨j, t⟩, (a j t).2⟩) ⟨?_, ?_⟩)).symm
    · intro t t' e
      simpa using e
    · rintro ⟨⟨j', t⟩, e⟩
      obtain rfl : j' = j := (a j' t).2.symm.trans e
      exact ⟨t, rfl⟩

end Abstract

section Mat

open Matrix TrivSqZeroExt

variable {k ι : Type} [CommRing k] [Fintype ι] [DecidableEq ι]

private def mk (A B : Matrix ι ι k) : Matrix ι ι (DualNumber k) := Matrix.of fun a b => (A a b, B a b)

omit [Fintype ι] [DecidableEq ι] in
private theorem fst_mk (A B : Matrix ι ι k) : (mk A B).map fst = A := rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem snd_mk (A B : Matrix ι ι k) : (mk A B).map snd = B := rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem mext {M M' : Matrix ι ι (DualNumber k)} (h1 : M.map fst = M'.map fst) (h2 : M.map snd = M'.map snd) :
    M = M' := by
  ext a b
  · exact congrFun (congrFun h1 a) b
  · exact congrFun (congrFun h2 a) b

omit [DecidableEq ι] in
private theorem mfst_mul (M M' : Matrix ι ι (DualNumber k)) : (M * M').map fst = M.map fst * M'.map fst := by
  ext a b
  simp [Matrix.mul_apply, fst_sum]

omit [DecidableEq ι] in
private theorem msnd_mul (M M' : Matrix ι ι (DualNumber k)) :
    (M * M').map snd = M.map fst * M'.map snd + M.map snd * M'.map fst := by
  ext a b
  simp [Matrix.mul_apply, snd_sum, Finset.sum_add_distrib, mul_comm]

omit [Fintype ι] in
private theorem mfst_one : (1 : Matrix ι ι (DualNumber k)).map fst = 1 := by
  ext a b
  by_cases e : a = b <;> simp [Matrix.one_apply, e]

omit [Fintype ι] in
private theorem msnd_one : (1 : Matrix ι ι (DualNumber k)).map snd = 0 := by
  ext a b
  by_cases e : a = b <;> simp [Matrix.one_apply, e]

omit [Fintype ι] [DecidableEq ι] [CommRing k] in
private theorem lc_mat [Finite ι] {Γ : Type} [TopologicalSpace Γ] {c : Γ → Matrix ι ι k}
    (h : ∀ a b, IsLocallyConstant fun s => c s a b) : IsLocallyConstant c := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ᶠ y in nhds x, ∀ a b, c y a b = c x a b := by
    simp only [Filter.eventually_all]
    exact fun a b => (IsLocallyConstant.iff_eventually_eq _).1 (h a b) x
  exact this.mono fun y hy => Matrix.ext hy

variable {X : Type} [AddCommGroup X] (w : ι → X)

open Classical in
private def mask (j : X) (Y : Matrix ι ι k) : Matrix ι ι k := Matrix.of fun a b => if w a - w b = j then Y a b else 0

omit [Fintype ι] [DecidableEq ι] in
private theorem mask_add (j : X) (Y Z : Matrix ι ι k) : mask w j (Y + Z) = mask w j Y + mask w j Z := by
  ext a b
  by_cases e : w a - w b = j <;> simp [mask, e]

omit [Fintype ι] [DecidableEq ι] in
private theorem mask_sub (j : X) (Y Z : Matrix ι ι k) : mask w j (Y - Z) = mask w j Y - mask w j Z := by
  ext a b
  by_cases e : w a - w b = j <;> simp [mask, e]

omit [Fintype ι] [DecidableEq ι] in
private theorem mask_zero (j : X) : mask w j (0 : Matrix ι ι k) = 0 := by
  ext a b
  simp [mask]

omit [DecidableEq ι] in
private theorem mask_mul (j : X) (Y : Matrix ι ι k) {A : Matrix ι ι k} (hA : ∀ a b, w a ≠ w b → A a b = 0) :
    mask w j (Y * A) = mask w j Y * A := by
  ext a b
  simp only [mask, Matrix.mul_apply, of_apply]
  split_ifs with e
  · refine Finset.sum_congr rfl fun c _ => ?_
    by_cases n : w c = w b
    · rw [if_pos (by rw [n, e])]
    · simp [hA c b n]
  · refine (Finset.sum_eq_zero fun c _ => ?_).symm
    by_cases n : w c = w b
    · rw [if_neg (by rw [n]; exact e), zero_mul]
    · simp [hA c b n]

omit [DecidableEq ι] in
private theorem mul_mask (j : X) (Y : Matrix ι ι k) {A : Matrix ι ι k} (hA : ∀ a b, w a ≠ w b → A a b = 0) :
    mask w j (A * Y) = A * mask w j Y := by
  ext a b
  simp only [mask, Matrix.mul_apply, of_apply]
  split_ifs with e
  · refine Finset.sum_congr rfl fun c _ => ?_
    by_cases n : w a = w c
    · rw [if_pos (by rw [← n, e])]
    · simp [hA a c n]
  · refine (Finset.sum_eq_zero fun c _ => ?_).symm
    by_cases n : w a = w c
    · rw [if_neg (by rw [← n]; exact e), mul_zero]
    · simp [hA a c n]

variable {O : Type} [CommRing O] [Algebra O k] {w} (Φ : FormData O w)

private theorem mask_fix {j : X} {Y : Matrix ι ι k} (hY : Y ∈ Φ.gw k j) : mask w j Y = Y := by
  ext a b
  by_cases e : w a - w b = j
  · simp [mask, e]
  · simp [mask, e, hY.2 a b e]

private theorem mask_mem (j : X) {Y : Matrix ι ι k} (hY : Y ∈ Φ.g k) : mask w j Y ∈ Φ.gw k j := by
  refine ⟨⟨?_, fun a b e => by simp [mask, hY.2 a b e]⟩, fun a b e => by simp [mask, e]⟩
  have hJ : ∀ a b, w a + w b ≠ Φ.c → Φ.JR k a b = 0 := fun a b e => by
    have : Φ.J a b = 0 := by_contra fun n => e (Φ.hw a b n)
    simp [FormData.JR, this]
  ext a b
  have h := congrFun (congrFun hY.1 a) b
  simp only [Matrix.add_apply, Matrix.mul_apply, transpose_apply, Matrix.zero_apply, mask, of_apply] at h ⊢
  by_cases e : Φ.c - w a - w b = j
  · rw [← h]
    congr 1 <;> refine Finset.sum_congr rfl fun c _ => ?_
    · by_cases n : w c + w b = Φ.c
      · rw [if_pos (by rw [← e, ← n]; abel)]
      · simp [hJ _ _ n]
    · by_cases n : w a + w c = Φ.c
      · rw [if_pos (by rw [← e, ← n]; abel)]
      · simp [hJ _ _ n]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro c _
      by_cases n : w a + w c = Φ.c
      · rw [if_neg (fun m => e (by rw [← m, ← n]; abel)), mul_zero]
      · simp [hJ _ _ n]
    · intro c _
      by_cases n : w c + w b = Φ.c
      · rw [if_neg (fun m => e (by rw [← m, ← n]; abel)), zero_mul]
      · simp [hJ _ _ n]

end Mat

section Dual

open Matrix TrivSqZeroExt

variable {O : Type} [CommRing O] [IsLocalRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] {w : ι → X}
  (Φ : FormData O w) [IsCO O (ResidueField O)] [IsCO O (DualNumber (ResidueField O))]

private theorem hh_iff (h : Matrix ι ι (DualNumber (ResidueField O))) :
    Φ.HH h ↔ h.map fst = 1 ∧ h.map snd ∈ Φ.g (ResidueField O) := by
  have e0 : h.map (res O _) = h.map fst := by ext a b; exact res_dual _
  have e1 : (Φ.JR (DualNumber (ResidueField O))).map fst = Φ.JR (ResidueField O) := rfl
  have e2 : (Φ.JR (DualNumber (ResidueField O))).map snd = 0 := rfl
  have e3 : h.map fst = 1 → (hᵀ * Φ.JR _ * h).map snd =
      (h.map snd)ᵀ * Φ.JR (ResidueField O) + Φ.JR (ResidueField O) * h.map snd := fun e => by
    rw [msnd_mul, msnd_mul, mfst_mul, transpose_map, transpose_map, e, e1, e2]
    simp [add_comm]
  rw [FormData.HH, e0]
  constructor
  · rintro ⟨a1, a2, a3⟩
    refine ⟨a3, ?_, fun a b e => by simp [a2 a b e]⟩
    rw [← e3 a3, a1, e2]
  · rintro ⟨a1, a2, a3⟩
    refine ⟨mext ?_ ?_, fun a b e => ?_, a1⟩
    · rw [mfst_mul, mfst_mul, transpose_map, a1]; simp
    · rw [e3 a1, a2, e2]
    · ext
      · exact (congrFun (congrFun a1 a) b).trans (Matrix.one_apply_ne fun n => e (by rw [n]))
      · exact a3 a b e

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* Matrix ι ι (ResidueField O)}

omit [IsCO O (ResidueField O)] in
private theorem lift_fst (r : Lift O rbar (DualNumber (ResidueField O))) (s : Γ) : (r.hom s).map fst = rbar s := by
  ext a b
  rw [← r.red, res_dual]; rfl

omit [IsCO O (ResidueField O)] in
private theorem lift_lc (r : Lift O rbar (DualNumber (ResidueField O))) : IsLocallyConstant r.hom := by
  refine lc_mat fun a b => IsLocallyConstant.desc _ _ (r.cont a b 2) ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, sq, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [← res_eq_zero_iff O, res_dual] at hx hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx, hy]

variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (r0 : Lift O rbar O)

omit [IsCO O (ResidueField O)] [IsCO O (DualNumber (ResidueField O))] in
private theorem tangent_representation_reduction (s : Γ) : ((r0.hom s).map (algebraMap O (DualNumber (ResidueField O)))).map fst = rbar s := by
  ext a b
  rw [← r0.red]
  exact ((res O O).commutes _).symm

private theorem inH_iff (r : Lift O rbar (DualNumber (ResidueField O))) :
    Φ.InH r0.hom _ r ↔ ∀ s, (r.hom s).map snd * rbar s⁻¹ ∈ Φ.g (ResidueField O) := by
  refine forall_congr' fun s => ?_
  have e : ((r0.hom s⁻¹).map (algebraMap O (DualNumber (ResidueField O)))).map snd = 0 := rfl
  rw [hh_iff, mfst_mul, msnd_mul, tangent_representation_reduction, lift_fst, e, ← map_mul]
  simp

private theorem loc_iff {N : Subgroup Γ} {L : Cond O rbar} (hL : Φ.IsLocCond r0.hom N L) (h0 : L O r0)
    (r : Lift O rbar (DualNumber (ResidueField O))) (hr : Φ.InH r0.hom _ r) :
    L _ r ↔ ∀ n ∈ N, (r.hom n).map snd = 0 := by
  have e : ∀ s, ((r0.map (Algebra.ofId O (DualNumber (ResidueField O)))).hom s).map snd = 0 := fun s => rfl
  have h1 : L _ (r0.map (Algebra.ofId O (DualNumber (ResidueField O)))) := by
    obtain ⟨I, hI⟩ := hL.closed O r0 fun s => by
      rw [show (r0.hom s⁻¹).map (algebraMap O O) = r0.hom s⁻¹ from rfl, ← map_mul, mul_inv_cancel, map_one]
      exact ⟨by simp, fun a b hab => Matrix.one_apply_ne fun e => hab (by rw [e]), by simp⟩
    refine (hI _ _).2 fun x hx => ?_
    have : x = 0 := (hI O (AlgHom.id O O)).1 h0 x hx
    rw [this, map_zero]
  rw [hL.tangent _ _ (fstHom O (ResidueField O) (ResidueField O)) (fun x => ⟨inl x, rfl⟩) ?_ _ r
    ((inH_iff Φ r0 _).2 fun s => by rw [e, zero_mul]; exact zero_mem _) hr ?_ h1]
  · refine forall₂_congr fun n _ => ⟨fun h => by rw [h, e], fun h => mext ?_ ?_⟩
    · rw [lift_fst, lift_fst]
    · rw [h, e]
  · rw [eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [← res_eq_zero_iff O, res_dual] at hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx, hy']
  · refine Lift.ext (MonoidHom.ext fun s => ?_)
    exact (lift_fst _ s).trans (lift_fst r s).symm

end Dual

section Framed

open Matrix TrivSqZeroExt

variable {O : Type} [CommRing O] [IsLocalRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] {w : ι → X}
  (Φ : FormData O w) [IsCO O (ResidueField O)] [IsCO O (DualNumber (ResidueField O))]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* Matrix ι ι (ResidueField O)}
  [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (r0 : Lift O rbar O)
  (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q)))
  {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B)

private theorem framed_iff (hL : ∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q))
    (h0 : ∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) (i : B →ₐ[O] DualNumber (ResidueField O))
    (hi : ∀ b, (i b).snd = 0) (r : Lift O rbar (DualNumber (ResidueField O)))
    (α : F.T → Matrix ι ι (DualNumber (ResidueField O))) :
    IsFramed Φ r0.hom F L ρ i r α ↔ (∀ s, (r.hom s).map snd * rbar s⁻¹ ∈ Φ.g (ResidueField O)) ∧
      (∀ q, ∀ n ∈ F.N q, (r.hom (F.ψ q n)).map snd = 0) ∧
      (∀ v, (α v).map fst = 1 ∧ (α v).map snd ∈ Φ.g (ResidueField O)) ∧ (α F.v0).map snd = 0 ∧
      ∀ v s, rbar (F.φ v s) * (α v).map snd + (r.hom (F.φ v s)).map snd = (α v).map snd * rbar (F.φ v s) := by
  have e1 : ∀ v s, (((ρ v).hom s).map i).map fst = rbar (F.φ v s) := fun v s => lift_fst ((ρ v).map i) s
  have e2 : ∀ v s, (((ρ v).hom s).map i).map snd = 0 := fun v s => by ext a b; exact hi _
  rw [IsFramed, ← inH_iff Φ r0]
  refine and_congr_right fun h1 => and_congr (forall_congr' fun q => ?_) ?_
  · exact loc_iff Φ (r0.comap (F.ψ q) (F.hψ q)) (hL q) (h0 q) _ fun s => by
      have := h1 (F.ψ q s)
      rwa [← map_inv] at this
  simp only [hh_iff]
  refine and_congr_right fun h2 => and_congr ⟨fun h => by rw [h, msnd_one], fun h => mext ?_ ?_⟩
    (forall₂_congr fun v s => ⟨fun h => ?_, fun h => mext ?_ ?_⟩)
  · rw [(h2 _).1, mfst_one]
  · rw [h, msnd_one]
  · have := congrArg (fun M => M.map snd) h
    simpa only [msnd_mul, lift_fst, (h2 v).1, e1, e2, mul_one, mul_zero, zero_add] using this
  · rw [mfst_mul, mfst_mul, lift_fst, e1, (h2 v).1, mul_one, one_mul]
  · simpa only [msnd_mul, lift_fst, (h2 v).1, e1, e2, mul_one, mul_zero, zero_add] using h

variable {Φ} (hbar : Φ.Normalises rbar)

private def ell (j : X) : (Γ × ι × ι) ⊕ (F.T × ι × ι) →
    Module.Dual (ResidueField O) (F.H1c (FormData.adRep hbar j))
  | .inl (s, a, b) =>
    { toFun := fun x => ((x.1.1 s).1 * rbar s) a b
      map_add' := fun x y => by simp [add_mul]
      map_smul' := fun c x => by simp }
  | .inr (v, a, b) =>
    { toFun := fun x => -(x.1.2 v).1 a b
      map_add' := fun x y => by simp [add_comm]
      map_smul' := fun c x => by simp }

include r0 in
private theorem rbar_lc : IsLocallyConstant rbar := by
  have := (lift_lc (r0.map (Algebra.ofId O (DualNumber (ResidueField O))))).comp fun M => M.map fst
  convert this using 1
  funext s
  exact (lift_fst _ s).symm

private def liftOf (j : X) (x : F.H1c (FormData.adRep hbar j)) : Lift O rbar (DualNumber (ResidueField O)) where
  hom :=
    { toFun := fun s => mk (rbar s) ((x.1.1 s).1 * rbar s)
      map_one' := by
        have h : x.1.1 1 = 0 := by simpa using x.2.2.1 1 1
        refine mext ?_ ?_
        · rw [fst_mk, mfst_one, map_one]
        · rw [snd_mk, msnd_one, h]; simp
      map_mul' := fun s t => by
        have h : (x.1.1 (s * t)).1 = (x.1.1 s).1 + rbar s * (x.1.1 t).1 * rbar s⁻¹ :=
          congrArg Subtype.val (x.2.2.1 s t)
        refine mext ?_ ?_
        · rw [mfst_mul, fst_mk, fst_mk, fst_mk, map_mul]
        · rw [msnd_mul, fst_mk, fst_mk, snd_mk, snd_mk, snd_mk, h, add_mul, mul_assoc _ (rbar s⁻¹), ← map_mul,
            inv_mul_cancel_left, map_mul, add_comm]
          simp only [mul_assoc] }
  cont a b N := (x.2.1.prodMk (rbar_lc r0)).comp fun p =>
    Ideal.Quotient.mk (maximalIdeal (DualNumber (ResidueField O)) ^ N) (mk p.2 (p.1.1 * p.2) a b)
  red s a b := res_dual _

end Framed

end UpperTheory.V.Alg.FramedTangent

open UpperTheory.V.Alg.FramedTangent TrivSqZeroExt in
theorem UpperTheory.V.Alg.framed_tangent :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) → (∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) →
      ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B), (∀ v, Φ.InH (r0.hom.comp (F.φ v)) B (ρ v)) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (i : B →ₐ[O] R) (r : Lift O rbar R) (α : F.T → Matrix ι ι R), IsUnivFramed Φ r0.hom F L ρ i r α →
      ∃ (τ : Type) (_ : Fintype τ) (z : τ → R) (wt : τ → X),
        (∀ t, ∃ a b, wt t = w a - w b ∧ ((∃ s, z t = r.hom s a b - algebraMap O R (r0.hom s a b)) ∨ ∃ v, z t = (α v - 1) a b)) ∧
        maximalIdeal R ≤ Ideal.span (Set.range z) ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 ∧
        (∀ c : τ → O, ∑ t, c t • z t ∈ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 → ∀ t, c t ∈ maximalIdeal O) ∧
        ∀ j, Nat.card {t // wt t = j} = Module.finrank (ResidueField O) (F.H1c (FormData.adRep hbar j)) := by
  intro O _ _ _ _ ι X _ _ _ w Φ _ Γ _ _ _ rbar r0 hbar _ F L _ hL h0 B _ _ _ ρ _ R _ _ _ i r α ⟨hF, hU⟩
  haveI := (co_res O).1
  haveI := (co_res O).2
  let z : (Γ × ι × ι) ⊕ (F.T × ι × ι) → R :=
    Sum.elim (fun p => r.hom p.1 p.2.1 p.2.2 - algebraMap O R (r0.hom p.1 p.2.1 p.2.2)) fun p => (α p.1 - 1) p.2.1 p.2.2
  let wt : (Γ × ι × ι) ⊕ (F.T × ι × ι) → X := Sum.elim (fun p => w p.2.1 - w p.2.2) fun p => w p.2.1 - w p.2.2
  have z1 : ∀ (f : R →ₐ[O] DualNumber (ResidueField O)) s a b,
      (f (z (.inl (s, a, b)))).snd = ((r.map f).hom s).map snd a b := fun f s a b => by
    show (f (_ - _)).snd = _
    rw [map_sub, snd_sub, snd_alg, sub_zero]; rfl
  have z2 : ∀ (f : R →ₐ[O] DualNumber (ResidueField O)) v a b,
      (f (z (.inr (v, a, b)))).snd = ((α v).map f).map snd a b := fun f v a b => by
    show (f (α v a b - (1 : Matrix ι ι R) a b)).snd = (f (α v a b)).snd
    by_cases e : a = b <;> simp [Matrix.one_apply, e]
  have hmap : ∀ f : R →ₐ[O] DualNumber (ResidueField O),
      IsFramed Φ r0.hom F L ρ (f.comp i) (r.map f) fun v => (α v).map f := fun f => by
    obtain ⟨a1, a2, a3, a4, a5⟩ := hF
    have hm : ∀ A A' : Matrix ι ι R, (A * A').map f = A.map f * A'.map f := fun A A' =>
      Matrix.map_mul (f := (f : R →+* DualNumber (ResidueField O)))
    refine ⟨fun s => ?_, fun q => ?_, fun v => (hh_group O ι X w Φ R).2.2.2.1 _ f _ (a3 v), by simp [a4],
      fun v s => ?_⟩
    · have := (hh_group O ι X w Φ R).2.2.2.1 _ f _ (a1 s)
      rwa [hm, show ((r0.hom s⁻¹).map (algebraMap O R)).map f = (r0.hom s⁻¹).map (algebraMap O _) from
        Matrix.ext fun a b => f.commutes _] at this
    · obtain ⟨I, hI⟩ := (hL q).closed R (r.comap (F.ψ q) (F.hψ q)) fun s => by
        have := a1 (F.ψ q s)
        rwa [← map_inv] at this
      refine (hI _ f).2 fun x hx => ?_
      have : x = 0 := (hI R (AlgHom.id O R)).1 (a2 q) x hx
      rw [this, map_zero]
    · have := congrArg (fun M => M.map f) (a5 v s)
      simp only [hm] at this
      exact this
  let i0 : B →ₐ[O] DualNumber (ResidueField O) := (inlAlgHom O (ResidueField O) (ResidueField O)).comp (res O B)
  have inv1 : ∀ s, rbar s⁻¹ * rbar s = 1 := fun s => by rw [← map_mul, inv_mul_cancel, map_one]
  have inv2 : ∀ s, rbar s * rbar s⁻¹ = 1 := fun s => by rw [← map_mul, mul_inv_cancel, map_one]
  refine Exists.elim (abstract (O := O) i z ?_ wt (fun j => F.H1c (FormData.adRep hbar j)) (ell F hbar)
    ?_ ?_ ?_ ?_ ?_) ?_
  rotate_right
  · rintro τ ⟨hτ, u, u1, u2, u3⟩
    refine ⟨τ, hτ, z ∘ u, wt ∘ u, fun t => ?_, u1, u2, u3⟩
    simp only [Function.comp_apply]
    rcases u t with ⟨s, a, b⟩ | ⟨v, a, b⟩
    · exact ⟨a, b, rfl, .inl ⟨s, rfl⟩⟩
    · exact ⟨a, b, rfl, .inr ⟨v, rfl⟩⟩
  · rintro (⟨s, a, b⟩ | ⟨v, a, b⟩) <;> rw [← res_eq_zero_iff O]
    · show res O R (_ - _) = 0
      rw [map_sub, r.red, ← r0.red, AlgHom.commutes, sub_eq_zero]
      exact (res O O).commutes _
    · show res O R (α v a b - (1 : Matrix ι ι R) a b) = 0
      rw [map_sub, show res O R (α v a b) = (1 : Matrix ι ι _) a b from congrFun (congrFun (hF.2.2.1 v).2.2 a) b]
      by_cases e : a = b <;> simp [Matrix.one_apply, e]
  · rintro j (⟨s, a, b⟩ | ⟨v, a, b⟩) x e
    · show ((x.1.1 s).1 * rbar s) a b = 0
      rw [← mask_fix Φ (x.1.1 s).2, ← mask_mul w j _ (hbar.2.2 s)]
      exact if_neg e
    · exact neg_eq_zero.2 ((x.1.2 v).2.2 a b e)
  · intro j x hx
    refine Subtype.ext (Prod.ext (funext fun s => Subtype.ext ?_) (funext fun v => Subtype.ext ?_))
    · have : (x.1.1 s).1 * rbar s = 0 := Matrix.ext fun a b => hx (.inl (s, a, b))
      show (x.1.1 s).1 = 0
      rw [← mul_one (x.1.1 s).1, ← inv2 s, ← mul_assoc, this, zero_mul]
    · exact Matrix.ext fun a b => neg_eq_zero.1 (hx (.inr (v, a, b)))
  · intro j x
    have e : ∀ s, ((liftOf r0 F hbar j x).hom s).map snd = (x.1.1 s).1 * rbar s := fun s => rfl
    refine Exists.elim (hU _ i0 (liftOf r0 F hbar j x) (fun v => mk 1 (-(x.1.2 v).1))
      ((framed_iff Φ r0 F L ρ hL h0 i0 (fun _ => rfl) _ _).2 ⟨fun s => ?_, fun q n hn => ?_,
        fun v => ⟨rfl, neg_mem (x.1.2 v).2.1⟩, ?_, fun v s => ?_⟩)) ?_
    rotate_right
    · rintro f ⟨⟨f1, f2, f3⟩, -⟩
      refine ⟨f, fun b => by rw [show f (i b) = i0 b from DFunLike.congr_fun f1 b]; rfl, ?_⟩
      rintro (⟨s, a, b⟩ | ⟨v, a, b⟩)
      · rw [z1, f2]; rfl
      · rw [z2, f3]; rfl
    · rw [e, mul_assoc, inv2, mul_one]
      exact (x.1.1 s).2.1
    · rw [e, x.2.2.2.1 q n hn]; simp
    · show -(x.1.2 F.v0).1 = 0
      rw [x.2.2.2.2.2]; simp
    · have h : (x.1.1 (F.φ v s)).1 = rbar (F.φ v s) * (x.1.2 v).1 * rbar (F.φ v s)⁻¹ - (x.1.2 v).1 :=
        congrArg Subtype.val (x.2.2.2.2.1 v s)
      rw [e, FramedTangent.snd_mk, h, sub_mul, mul_assoc, inv1, mul_one, mul_neg, neg_mul]
      abel
  · intro f hf j
    obtain ⟨b1, b2, b3, b4, b5⟩ := (framed_iff Φ r0 F L ρ hL h0 (f.comp i) hf _ _).1 (hmap f)
    refine ⟨⟨(fun s => ⟨_, mask_mem Φ j (b1 s)⟩, fun v => ⟨_, mask_mem Φ j (neg_mem (b3 v).2)⟩), ?_,
      fun s t => Subtype.ext ?_, fun q n hn => Subtype.ext ?_, fun v s => Subtype.ext ?_, Subtype.ext ?_⟩, ?_⟩
    · refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      exact ((lift_lc (r.map f)).prodMk ((rbar_lc r0).comp_continuous continuous_inv)).comp
        fun p => mask w j (p.1.map snd * p.2)
    · show mask w j _ = mask w j _ + rbar s * mask w j _ * rbar s⁻¹
      rw [← mul_mask w j _ (hbar.2.2 s), ← mask_mul w j _ (hbar.2.2 s⁻¹), ← mask_add, map_mul, msnd_mul, lift_fst,
        lift_fst, mul_inv_rev, map_mul, add_mul, mul_assoc _ (rbar t), ← mul_assoc (rbar t), inv2, one_mul, add_comm]
      simp only [mul_assoc]
    · show mask w j _ = 0
      rw [b2 q n hn, zero_mul, mask_zero]
    · show mask w j _ = rbar (F.φ v s) * mask w j _ * rbar (F.φ v s)⁻¹ - mask w j _
      rw [← mul_mask w j _ (hbar.2.2 _), ← mask_mul w j _ (hbar.2.2 _), ← mask_sub, eq_sub_of_add_eq' (b5 v s),
        sub_mul, mul_assoc, inv2]
      congr 1
      simp only [mul_neg, neg_mul, mul_one]
      abel
    · show mask w j _ = 0
      rw [b4, neg_zero, mask_zero]
    · rintro (⟨s, a, b⟩ | ⟨v, a, b⟩) e
      · show (mask w j (((r.map f).hom s).map snd * rbar s⁻¹) * rbar s) a b = _
        rw [z1, ← mask_mul w j _ (hbar.2.2 s), mul_assoc, inv1, mul_one]
        exact if_pos e
      · show -(mask w j _ a b) = _
        rw [z2, neg_eq_iff_eq_neg]
        exact if_pos e
  · intro f hf hz y
    let f0 : R →ₐ[O] DualNumber (ResidueField O) := (inlAlgHom O (ResidueField O) (ResidueField O)).comp (res O R)
    have key : ∀ y, (f y).snd = 0 → f0 y = f y := fun y hy => by
      ext
      · rw [FramedTangent.fst_map, FramedTangent.fst_map]
      · exact hy.symm
    have := (hU _ _ _ _ (hmap f)).unique (y₁ := f0) (y₂ := f) ⟨AlgHom.ext fun b => key _ (hf b), ?_, fun v => ?_⟩
      ⟨rfl, rfl, fun _ => rfl⟩
    · rw [← this]; rfl
    · exact Lift.ext (MonoidHom.ext fun s => Matrix.ext fun a b => key _ ((z1 f s a b).symm.trans (hz _)))
    · exact Matrix.ext fun a b => key _ ((z2 f v a b).symm.trans (hz _))
