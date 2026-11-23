import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne

set_option autoImplicit false

noncomputable section

open PowerSeries Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange

namespace GlobalTheory.WachPlace

section Columns

variable {F : Type} [Field F] {a b c : ℕ}

def vecL (y : Fin a → F⟦X⟧) : Fin a → LaurentSeries F := fun j => algebraMap F⟦X⟧ (LaurentSeries F) (y j)

def linL (A : Mx F⟦X⟧ a b) : (Fin b → LaurentSeries F) →ₗ[LaurentSeries F] (Fin a → LaurentSeries F) :=
  (A.map (algebraMap F⟦X⟧ (LaurentSeries F))).mulVecLin

def colL (A : Mx F⟦X⟧ a b) : Submodule (LaurentSeries F) (Fin a → LaurentSeries F) := LinearMap.range (linL A)

theorem finrank_colL (A : Mx F⟦X⟧ a b) : Module.finrank (LaurentSeries F) (colL A) = lrank A := rfl

theorem linL_vecL (A : Mx F⟦X⟧ a b) (y : Fin b → F⟦X⟧) : linL A (vecL y) = vecL (A.mulVec y) := by
  funext j
  exact (RingHom.map_mulVec (algebraMap F⟦X⟧ (LaurentSeries F)) A y j).symm

theorem linL_mul (A : Mx F⟦X⟧ a b) (B : Mx F⟦X⟧ b c) : linL (A * B) = (linL A).comp (linL B) := by
  rw [linL, Matrix.map_mul, Matrix.mulVecLin_mul]
  rfl

theorem vecL_smul (s : F⟦X⟧) (y : Fin a → F⟦X⟧) : vecL (s • y) = algebraMap F⟦X⟧ (LaurentSeries F) s • vecL y := by
  funext j
  simp only [vecL, Pi.smul_apply, smul_eq_mul, map_mul]

theorem vecL_sub (y z : Fin a → F⟦X⟧) : vecL (y - z) = vecL y - vecL z := by
  funext j
  simp only [vecL, Pi.sub_apply, map_sub]

theorem vecL_injective : Function.Injective (vecL : (Fin a → F⟦X⟧) → _) := fun _ _ h =>
  funext fun j => IsFractionRing.injective F⟦X⟧ (LaurentSeries F) (congrFun h j)

theorem colL_mul_le (A : Mx F⟦X⟧ a b) (B : Mx F⟦X⟧ b c) : colL (A * B) ≤ colL A := by
  rw [colL, linL_mul]
  exact LinearMap.range_comp_le_range _ _

theorem colL_eq_top {A : Mx F⟦X⟧ a b} (h : lrank A = a) : colL A = ⊤ :=
  Submodule.eq_top_of_finrank_eq (by rw [finrank_colL, h, Module.finrank_fin_fun])

theorem colL_mul_eq (A : Mx F⟦X⟧ a b) {B : Mx F⟦X⟧ b c} (h : lrank B = b) : colL (A * B) = colL A := by
  rw [colL, linL_mul]
  exact LinearMap.range_comp_of_range_eq_top _ (colL_eq_top h)

theorem exists_clear (z : Fin a → LaurentSeries F) :
    ∃ (m : ℕ) (w : Fin a → F⟦X⟧), vecL w = algebraMap F⟦X⟧ (LaurentSeries F) (X ^ m) • z := by
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (X : F⟦X⟧)) z
  obtain ⟨m, hm⟩ := s.2
  choose w hw using hs
  refine ⟨m, w, funext fun j => ?_⟩
  rw [vecL, hw j, ← hm, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]

theorem semilin_mem (θ : F⟦X⟧ →+* F⟦X⟧) (hθ : θ X ≠ 0) {M : Mx F⟦X⟧ a a} {M' : Mx F⟦X⟧ b b} {A A' : Mx F⟦X⟧ a b}
    (h : M * A'.map θ = A * M') {y : Fin a → F⟦X⟧} (hy : vecL y ∈ colL A') :
    vecL (M.mulVec fun j => θ (y j)) ∈ colL A := by
  obtain ⟨z, hz⟩ := hy
  obtain ⟨m, w, hw⟩ := exists_clear z
  have e1 : A'.mulVec w = (X : F⟦X⟧) ^ m • y := by
    apply vecL_injective
    rw [← linL_vecL, hw, map_smul, hz, vecL_smul]
  have e2 : (A'.map θ).mulVec (fun j => θ (w j)) = θ X ^ m • fun j => θ (y j) := by
    funext j
    have := RingHom.map_mulVec θ A' w j
    rw [e1] at this
    rw [show (fun j => θ (w j)) = θ ∘ w from rfl, ← this]
    simp
  have e3 : θ X ^ m • (M.mulVec fun j => θ (y j)) = A.mulVec (M'.mulVec fun j => θ (w j)) := by
    rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_smul]
  have h0 : algebraMap F⟦X⟧ (LaurentSeries F) (θ X ^ m) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective F⟦X⟧ (LaurentSeries F))).2 (pow_ne_zero _ hθ)
  rw [← Submodule.smul_mem_iff _ h0, ← vecL_smul, e3, ← linL_vecL]
  exact LinearMap.mem_range_self _ _

theorem ker_eq_colL {C : Mx F⟦X⟧ 1 (a + 1)} {E : Mx F⟦X⟧ (a + 1) a} (h : C * E = 0) (hE : lrank E = a)
    (hC : lrank C = 1) : LinearMap.ker (linL C) = colL E := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← linL_mul, h]
    simp [linL]
  · have := LinearMap.finrank_range_add_finrank_ker (linL C)
    rw [← colL, finrank_colL, hC, Module.finrank_fin_fun] at this
    rw [finrank_colL, hE]
    omega

theorem exists_mulVec_eq_pow {C : Mx F⟦X⟧ 1 a} (hC : lrank C = 1) :
    ∃ (y : Fin a → F⟦X⟧) (m : ℕ), C.mulVec y = fun _ => X ^ m := by
  obtain ⟨z, hz⟩ : (fun _ => 1 : Fin 1 → LaurentSeries F) ∈ colL C := by
    rw [colL_eq_top hC]
    trivial
  obtain ⟨m, w, hw⟩ := exists_clear z
  refine ⟨w, m, vecL_injective ?_⟩
  rw [← linL_vecL, hw, map_smul, hz]
  funext j
  simp [vecL]

theorem line_rel (θ : F⟦X⟧ →+* F⟦X⟧) {M : Mx F⟦X⟧ a a} {M₂ : Mx F⟦X⟧ (a + 1) (a + 1)} {M₁ : Mx F⟦X⟧ 1 1}
    {B B' : Mx F⟦X⟧ a (a + 1)} {C C' : Mx F⟦X⟧ 1 (a + 1)} {E : Mx F⟦X⟧ (a + 1) a}
    (hB : M * B'.map θ = B * M₂) (hC : M₁ * C'.map θ = C * M₂) (h : C * E = 0) (hE : lrank E = a)
    (hC1 : lrank C = 1) {y y' : Fin (a + 1) → F⟦X⟧} {m m' : ℕ} (hy : C.mulVec y = fun _ => X ^ m)
    (hy' : C'.mulVec y' = fun _ => X ^ m') :
    algebraMap F⟦X⟧ (LaurentSeries F) X ^ m • vecL (M.mulVec fun j => θ (B'.mulVec y' j)) -
      (algebraMap F⟦X⟧ (LaurentSeries F) (θ X) ^ m' * algebraMap F⟦X⟧ (LaurentSeries F) (M₁ 0 0)) •
        vecL (B.mulVec y) ∈ colL (B * E) := by
  have e : ∀ {k : ℕ} (A : Mx F⟦X⟧ k (a + 1)), (fun j => θ (A.mulVec y' j)) = (A.map θ).mulVec fun j => θ (y' j) :=
    fun A => funext fun j => RingHom.map_mulVec θ A y' j
  let z : Fin (a + 1) → F⟦X⟧ := (X : F⟦X⟧) ^ m • (M₂.mulVec fun j => θ (y' j)) - (θ X ^ m' * M₁ 0 0) • y
  have hz : C.mulVec z = 0 := by
    simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hC]
    rw [← Matrix.mulVec_mulVec, ← e, hy, hy']
    funext j
    rw [Subsingleton.elim j 0]
    simp [Matrix.mulVec, dotProduct]
    ring
  have hk : vecL z ∈ colL E := by
    rw [← ker_eq_colL h hE hC1, LinearMap.mem_ker, linL_vecL, hz]
    funext j
    simp [vecL]
  obtain ⟨v, hv⟩ := hk
  refine ⟨v, ?_⟩
  rw [linL_mul, LinearMap.comp_apply, hv, linL_vecL]
  simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hB]
  rw [← Matrix.mulVec_mulVec, ← e, vecL_sub, vecL_smul, vecL_smul, map_pow, map_mul, map_pow]

theorem colL_eq_sup {B : Mx F⟦X⟧ a (a + 1)} {C : Mx F⟦X⟧ 1 (a + 1)} {E : Mx F⟦X⟧ (a + 1) a} (h : C * E = 0)
    (hE : lrank E = a) (hC1 : lrank C = 1) {y : Fin (a + 1) → F⟦X⟧} {m : ℕ} (hy : C.mulVec y = fun _ => X ^ m) :
    colL B = colL (B * E) ⊔ Submodule.span (LaurentSeries F) {vecL (B.mulVec y)} := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    have h0 : algebraMap F⟦X⟧ (LaurentSeries F) (X ^ m) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F⟦X⟧ (LaurentSeries F))).2 (pow_ne_zero _ X_ne_zero)
    let s : LaurentSeries F := linL C z 0 / algebraMap F⟦X⟧ (LaurentSeries F) (X ^ m)
    have hk : z - s • vecL y ∈ colL E := by
      rw [← ker_eq_colL h hE hC1, LinearMap.mem_ker, map_sub, map_smul, linL_vecL, hy]
      funext j
      rw [Subsingleton.elim j 0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, vecL, div_mul_cancel₀ _ h0, sub_self]
      rfl
    obtain ⟨v, hv⟩ := hk
    have : linL B z = linL (B * E) v + s • vecL (B.mulVec y) := by
      rw [linL_mul, LinearMap.comp_apply, hv, map_sub, map_smul, linL_vecL, sub_add_cancel]
    rw [this]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · refine sup_le (colL_mul_le _ _) ?_
    rw [Submodule.span_singleton_le_iff_mem, ← linL_vecL]
    exact LinearMap.mem_range_self _ _

end Columns

theorem filtration_of_chain {F : Type} [Field F] {ι : Type} (σ : Equiv.Perm ι) {l n t R : ℕ} (hl : 0 < l) (un : F⟦X⟧)
    (P D : ι → Mx F⟦X⟧ n n) (Pψ Dψ : Fin t → ι → Mx F⟦X⟧ 1 1) (rs : Fin t → Fin R) (dim : Fin (R + 1) → ℕ)
    (y : ι → Slot F n t R) (h0 : dim 0 = 0) (hR : dim (Fin.last R) = n)
    (hs : ∀ s, dim (rs s).succ = dim (rs s).castSucc + 1)
    (hy : ∀ i, (y i).Chain (y (σ i)) l un (P i) (D i) (fun s => Pψ s i) (fun s => Dψ s i) rs dim) :
    ∃ (V : ι → Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F))
      (e : ι → Fin t → Fin n → F⟦X⟧) (m : ι → Fin t → ℤ),
      (∀ i, V i 0 = ⊥ ∧ V i (Fin.last R) = ⊤ ∧ Monotone (V i)) ∧
      (∀ k i j, Module.finrank (LaurentSeries F) (V i k) = Module.finrank (LaurentSeries F) (V j k)) ∧
      (∀ i k v, vecL v ∈ V (σ i) k → vecL ((P i).mulVec fun a => frob0 l (v a)) ∈ V i k) ∧
      (∀ i k v, vecL v ∈ V i k → vecL ((1 + (X : F⟦X⟧) • D i).mulVec fun a => gam0 0 un (v a)) ∈ V i k) ∧
      (∀ i s, vecL (e i s) ∉ V i (rs s).castSucc ∧
        V i (rs s).succ = V i (rs s).castSucc ⊔ Submodule.span (LaurentSeries F) {vecL (e i s)}) ∧
      (∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) • vecL ((P i).mulVec fun a => frob0 l (e (σ i) s a)) -
        (((X : F⟦X⟧) : LaurentSeries F) ^ ((l : ℤ) * m (σ i) s) * ((Pψ s i 0 0 : F⟦X⟧) : LaurentSeries F)) •
          vecL (e i s) ∈ V i (rs s).castSucc) ∧
      ∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) •
          vecL ((1 + (X : F⟦X⟧) • D i).mulVec fun a => gam0 0 un (e i s a)) -
        (((gamSer 0 un : F⟦X⟧) : LaurentSeries F) ^ m i s *
          ((1 + X * Dψ s i 0 0 : F⟦X⟧) : LaurentSeries F)) • vecL (e i s) ∈ V i (rs s).castSucc := by
  have h1 : HasSubst (X ^ l : F⟦X⟧) := HasSubst.X_pow hl.ne'
  have h2 : HasSubst (gamSer 0 un) := HasSubst.of_constantCoeff_zero' (by simp [gamSer])
  obtain ⟨φ, hφ⟩ : ∃ φ : F⟦X⟧ →+* F⟦X⟧, ⇑φ = frob0 l := ⟨(substAlgHom h1 : F⟦X⟧ →ₐ[F] F⟦X⟧), coe_substAlgHom h1⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : F⟦X⟧ →+* F⟦X⟧, ⇑γ = gam0 0 un := ⟨(substAlgHom h2 : F⟦X⟧ →ₐ[F] F⟦X⟧), coe_substAlgHom h2⟩
  have hφX : φ X = X ^ l := by rw [hφ, frob0, subst_X h1]
  have hγX : γ X = gamSer 0 un := by rw [hγ, gam0, subst_X h2]
  have hγ0 : γ X ≠ 0 := by
    rw [hγX, gamSer]
    refine mul_ne_zero X_ne_zero fun h => ?_
    simpa using congrArg constantCoeff h
  choose w m hw using fun i s => exists_mulVec_eq_pow ((hy i).2.2 s).2.2.2.2.2.2.1
  have hsup : ∀ i s, colL ((y i).A (rs s).succ) =
      colL ((y i).A (rs s).castSucc) ⊔ Submodule.span (LaurentSeries F) {vecL (((y i).B s).mulVec (w i s))} := by
    intro i s
    obtain ⟨-, -, e1, e2, e3, e4, e5, e6⟩ := (hy i).2.2 s
    rw [← e1, ← colL_eq_sup e2 e4 e5 (hw i s), e3, colL_mul_eq _ e6]
  refine ⟨fun i k => colL ((y i).A k), fun i s => ((y i).B s).mulVec (w i s), fun i s => m i s,
    fun i => ⟨?_, colL_eq_top (((hy i).1 _).2.trans hR), ?_⟩, fun k i j => ?_, fun i k v hv => ?_, fun i k v hv => ?_,
    fun i s => ⟨fun hm => ?_, hsup i s⟩, fun i s => ?_, fun i s => ?_⟩
  · exact Submodule.finrank_eq_zero.1 ((finrank_colL _).trans (((hy i).1 _).2.trans h0))
  · refine Fin.monotone_iff_le_succ.2 fun k => ?_
    exact (congrArg colL ((hy i).2.1 k)).trans_le (colL_mul_le _ _)
  · rw [finrank_colL, finrank_colL, ((hy i).1 k).2, ((hy j).1 k).2]
  · rw [← hφ]
    exact semilin_mem φ (by rw [hφX]; exact pow_ne_zero _ X_ne_zero) (hφ ▸ ((hy i).1 k).1.1) hv
  · rw [← hγ]
    exact semilin_mem γ hγ0 (hγ ▸ ((hy i).1 k).1.2) hv
  · have e := hsup i s
    rw [sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 hm)] at e
    have e' := finrank_colL ((y i).A (rs s).succ)
    rw [e, finrank_colL, ((hy i).1 _).2, ((hy i).1 _).2, hs] at e'
    omega
  · obtain ⟨b1, c1, e1, e2, -, e4, e5, -⟩ := (hy i).2.2 s
    have := line_rel φ (hφ ▸ b1.1) (hφ ▸ c1.1) e2 e4 e5 (hw i s) (hw (σ i) s)
    rw [e1, hφX, hφ, map_pow, ← pow_mul] at this
    rw [← Nat.cast_mul, zpow_natCast, zpow_natCast]
    exact this
  · obtain ⟨b1, c1, e1, e2, -, e4, e5, -⟩ := (hy i).2.2 s
    have := line_rel γ (hγ ▸ b1.2) (hγ ▸ c1.2) e2 e4 e5 (hw i s) (hw i s)
    rw [e1, hγX, hγ, Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul] at this
    rw [zpow_natCast, zpow_natCast]
    exact this

end GlobalTheory.WachPlace

end
