import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.CharacterFiniteLevelZeroOfForms
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.OneAddPowOfSq

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Grp

theorem conj_pow_rational_rel {H A : Type} [Group H] [Group A] (ι : H →* A) (g : H) (hh yy δ κ : A) (hge : ι g = hh)
    (e1 : yy = hh * (yy * δ) * κ) (j : ℕ) : (δ * κ) ^ j = yy⁻¹ * ι (g⁻¹ ^ j) * yy := by
  have hhv : hh = yy * κ⁻¹ * δ⁻¹ * yy⁻¹ := by
    calc hh = hh * (yy * δ) * κ * (κ⁻¹ * δ⁻¹ * yy⁻¹) := by group
      _ = yy * κ⁻¹ * δ⁻¹ * yy⁻¹ := by rw [← e1]; group
  have hrel : ι g⁻¹ = yy * (δ * κ) * yy⁻¹ := by rw [map_inv, hge, hhv]; group
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, ih, pow_succ, map_mul, hrel]; group

theorem map_mul_pow_of_map_eq_one {A B : Type} [Group A] [Group B] (ψ : A →* B) (δ κ : A) (h : ψ δ = 1) (j : ℕ) :
    ψ ((δ * κ) ^ j) = (ψ κ) ^ j := by
  rw [map_pow, map_mul, h, one_mul]

theorem pow_image_eq_one {H A B : Type} [Group H] [Group A] [Group B] (ψ : A →* B) (ι : H →* A) (z yy : A) (γ : H)
    (hz : ∀ j : ℕ, z ^ j = yy⁻¹ * ι (γ ^ j) * yy) (j N : ℕ) (h : (γ ^ j) ^ N = 1) : (ψ (z ^ j)) ^ N = 1 := by
  rw [← map_pow, ← pow_mul, hz, pow_mul, h, map_one, mul_one, inv_mul_cancel, map_one]

theorem pow_eq_one_of_comp_eq_one {H A B C : Type} [Group H] [Group A] [Group B] [Group C] (ι : H →* A) (ψ : A →* B)
    (φ : B →* C) (hinj : Function.Injective (φ.comp (ψ.comp ι))) (z yy : A) (γ : H)
    (hz : ∀ j : ℕ, z ^ j = yy⁻¹ * ι (γ ^ j) * yy) (j : ℕ) (h : φ (ψ (z ^ j)) = 1) : γ ^ j = 1 := by
  rw [hz, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv] at h
  apply hinj
  rw [map_one]
  show φ (ψ (ι (γ ^ j))) = 1
  set X := φ (ψ (yy))
  calc φ (ψ (ι (γ ^ j))) = X * (X⁻¹ * φ (ψ (ι (γ ^ j))) * X) * X⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem eq_one_of_coprime_torsion_two_primes {H : Type} [Group H] (γ : H) (p q N0 : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hN0 : 0 < N0)
    (h0 : γ ^ N0 = 1) (hcp : ∀ j N : ℕ, Nat.Coprime N p → (γ ^ j) ^ N = 1 → γ ^ j = 1)
    (hcq : ∀ j N : ℕ, Nat.Coprime N q → (γ ^ j) ^ N = 1 → γ ^ j = 1) : γ = 1 := by
  obtain ⟨a, m, hm, em⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0.ne' p hp.ne_one
  have h1 : γ ^ (p ^ a) = 1 := hcp _ m ((hp.coprime_iff_not_dvd.2 hm).symm) (by rw [← pow_mul, ← em, h0])
  have h2 := hcq 1 (p ^ a) (Nat.Coprime.pow_left a ((Nat.coprime_primes hp hq).2 hpq)) (by rw [pow_one, h1])
  simpa using h2

theorem eq_inv_of_conj_trivial {H A : Type} [Group H] [Group A] (ι : H →* A) (γ : H) (yy δ κ : A)
    (hz : (δ * κ) ^ 1 = yy⁻¹ * ι (γ ^ 1) * yy) (h : γ = 1) : δ = κ⁻¹ := by
  rw [h, one_pow, map_one, mul_one, inv_mul_cancel, pow_one] at hz
  calc δ = δ * κ * κ⁻¹ := by group
    _ = κ⁻¹ := by rw [hz, one_mul]

theorem base_change_GL_injective {A B : Type} [CommRing A] [CommRing B] {m : ℕ} (φ : A →+* B)
    (hφ : Function.Injective φ) : Function.Injective (bc (n := Fin m) φ) := by
  intro x y hxy
  apply Units.ext
  have h := congrArg (fun z : GL (Fin m) B => (z : Matrix (Fin m) (Fin m) B)) hxy
  exact Matrix.map_injective hφ h

theorem base_change_GL_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {m : ℕ} (g : A →+* B) (f : B →+* C)
    (x : GL (Fin m) A) : bc (n := Fin m) f (bc (n := Fin m) g x) = bc (n := Fin m) (f.comp g) x := by
  apply Units.ext
  simp [bc, Matrix.map_map]

theorem base_change_GL_comp_injective {A B C D' : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D'] {m : ℕ}
    (ι : A →+* B) (ψ : B →+* C) (φ : C →+* D') (h : Function.Injective (φ.comp (ψ.comp ι))) :
    Function.Injective ((bc (n := Fin m) φ).comp ((bc (n := Fin m) ψ).comp (bc (n := Fin m) ι))) := by
  intro x y hxy
  have e : ∀ z, ((bc (n := Fin m) φ).comp ((bc (n := Fin m) ψ).comp (bc (n := Fin m) ι))) z =
      bc (n := Fin m) (φ.comp (ψ.comp ι)) z := by
    intro z
    simp only [MonoidHom.comp_apply, base_change_GL_comp]
  rw [e, e] at hxy
  exact base_change_GL_injective _ h hxy

end Grp

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

theorem level_matrix_entries_integral (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp) {a t nb skip fc : ℕ} {zl : Bool}
    (L : GLev S G a t nb skip fc zl) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ levelVL σ J v S.Lb) (p q : Fin n) :
    G.mat i v h (L.fr i v h) x p q ∈ v.adicCompletionIntegers F := by
  set fr := L.fr i v h with hfr
  set e : Fin n → v.adicCompletion F := Pi.single q 1 with he
  set X : Fin n → v.adicCompletion F := (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ e with hX
  have hXi : ∀ b, (((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ X) b ∈
      v.adicCompletionIntegers F := by
    intro b
    rw [hX, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, he]
    by_cases hb : b = q
    · subst hb; simp only [Pi.single_eq_same]; exact (v.adicCompletionIntegers F).one_mem
    · rw [Pi.single_eq_of_ne hb]; exact (v.adicCompletionIntegers F).zero_mem
  obtain ⟨y, hy, hyX⟩ := (L.fr_lat i v h X).2 hXi
  have hst : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb) := hx.2
  have hxy := (hst y).1 hy
  have hmap : ∀ b, G.phi i v h (((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) b) =
      (((bc (G.phi i v h) x : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ X) b := by
    intro b
    rw [RingHom.map_mulVec]
    have : (⇑(G.phi i v h) ∘ y) = X := funext hyX
    rw [this]
    rfl
  have h2 := (L.fr_lat i v h _).1 ⟨_, hxy, hmap⟩ p
  rw [hX, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, he, Matrix.mulVec_single_one] at h2
  unfold GLoc.mat
  simpa [Units.val_mul, Matrix.mul_assoc, Matrix.col_apply, hfr] using h2

theorem torsion_reduction_trivial (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp) {a t nb skip fc : ℕ} {zl : Bool}
    (L : GLev S G a t nb skip fc zl) (ha : n ≤ a) (i : Fin 2) (hp : (gp i).Prime) (v : HeightOneSpectrum (𝓞 F))
    (h : (gp i : 𝓞 F) ∈ v.asIdeal) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ S.Uloc v)
    (N : ℕ) (hc : Nat.Coprime N (gp i)) (hN : x ^ N = 1) : bc (G.phi i v h) x = 1 := by
  set fr := L.fr i v h with hfr
  set M : GL (Fin n) (v.adicCompletion F) := fr⁻¹ * bc (G.phi i v h) x * fr with hM
  have hxL := S.Uloc_lev v hx
  have hxiL : x⁻¹ ∈ levelVL σ J v S.Lb := (levelVL σ J v S.Lb).inv_mem hxL
  have hMi : ∀ p q, (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) p q ∈ v.adicCompletionIntegers F :=
    level_matrix_entries_integral S G L i v h x hxL
  have hMinv : M⁻¹ = fr⁻¹ * bc (G.phi i v h) x⁻¹ * fr := by rw [hM, map_inv]; group
  have hMii : ∀ p q, ((M⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) p q ∈
      v.adicCompletionIntegers F := by
    rw [hMinv]; exact level_matrix_entries_integral S G L i v h x⁻¹ hxiL
  let A : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) := fun p q => ⟨_, hMi p q⟩
  let B : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) := fun p q => ⟨_, hMii p q⟩
  have hAm : A.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) =
      (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by ext p q; rfl
  have hBm : B.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) =
      ((M⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by ext p q; rfl
  have hinj := FaithfulSMul.algebraMap_injective (v.adicCompletionIntegers F) (v.adicCompletion F)
  have hAB : A * B = 1 := by
    apply Matrix.map_injective hinj
    beta_reduce
    rw [Matrix.map_mul, hAm, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
  have hBA : B * A = 1 := by
    apply Matrix.map_injective hinj
    beta_reduce
    rw [Matrix.map_mul, hAm, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
  let aGL : GL (Fin n) (v.adicCompletionIntegers F) := ⟨A, B, hAB, hBA⟩
  have hbc : bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) aGL = M := Units.ext hAm
  have hInJ := (L.mem i v h x hxL).1 hx
  have hred : ∀ p q, redM F v (G.mat i v h fr x) p q =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (A p q) := by
    intro p q
    unfold redM
    rw [dif_pos (show G.mat i v h fr x p q ∈ v.adicCompletionIntegers F from hMi p q)]
    rfl
  have hup : redGL (n := Fin n) (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) aGL ∈
      upperUni n (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) := by
    intro p q
    refine ⟨fun hqp => ?_, ?_⟩
    · have h1 := hInJ.1 p q (by
        unfold blkOf
        rw [if_pos (lt_of_lt_of_le q.2 ha), if_pos (lt_of_lt_of_le p.2 ha)]
        exact hqp)
      rw [hred] at h1
      exact h1
    · have h1 := hInJ.2.1 p (lt_of_lt_of_le p.2 ha)
      rw [hred] at h1
      exact h1
  have hiw : M ∈ iwU F n v := by
    refine ⟨aGL, ?_, hbc⟩
    exact Subgroup.subset_closure hup
  have hpw : ∀ j : ℕ, M ^ j = fr⁻¹ * (bc (G.phi i v h) x) ^ j * fr := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ih, hM, pow_succ]; group
  have hMN : M ^ N = 1 := by
    rw [hpw, ← map_pow, hN, map_one, mul_one, inv_mul_cancel]
  have h1 := Formalism.L2.G.Triv.iwU_coprime v (gp i) hp h M hiw N hc hMN
  have : bc (G.phi i v h) x = fr * M * fr⁻¹ := by rw [hM]; group
  rw [this, h1, mul_one, mul_inv_cancel]

theorem is_diamond_one' (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) : IsDia S v hv 1 1 := by
  refine ⟨fun v' _ => ?_, ?_, ?_⟩
  · simp
  · simp only [OneMemClass.coe_one, map_one]; exact (levelVL σ J v S.Lb).one_mem
  · refine ⟨by simp only [OneMemClass.coe_one, map_one]; exact (stabGL _).one_mem, fun x => ?_⟩
    rw [one_smul]
    congr 1
    apply Subtype.ext
    simp

theorem is_diamond_mul_mult (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k k' : ℤ} {δ δ' : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : IsDia S v hv k δ) (h' : IsDia S v hv k' δ') : IsDia S v hv (k * k') (δ * δ') := by
  obtain ⟨h1, h2, hg, h3⟩ := h
  obtain ⟨h1', h2', hg', h3'⟩ := h'
  refine ⟨fun v' hv' => ?_, ?_, ?_⟩
  · simp [Subgroup.coe_mul, map_mul, h1 v' hv', h1' v' hv']
  · simpa [Subgroup.coe_mul, map_mul] using (levelVL σ J v S.Lb).mul_mem h2 h2'
  · have hgg : bc (prV (E := E) v) (δ * δ').1 ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) := by
      simpa [Subgroup.coe_mul, map_mul] using (stabGL _).mul_mem hg hg'
    refine ⟨hgg, fun x => ?_⟩
    have e : (⟨(bc (prV (E := E) v) (δ * δ').1).1 *ᵥ x.1, (hgg x.1).1 x.2⟩ :
        latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) =
        ⟨(bc (prV (E := E) v) δ.1).1 *ᵥ ((bc (prV (E := E) v) δ'.1).1 *ᵥ x.1),
          (hg _).1 ((hg' x.1).1 x.2)⟩ := by
      apply Subtype.ext
      simp [Subgroup.coe_mul, map_mul, Matrix.mulVec_mulVec]
    rw [e, mul_comm, mul_smul, h3 ⟨_, (hg' x.1).1 x.2⟩, h3' x]

theorem diamond_conj_mem_level' (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : IsDia S v hv k δ) (κ : S.U) : δ.1⁻¹ * κ.1 * δ.1 ∈ S.U := by
  obtain ⟨h1, h2, hg, h3⟩ := h
  have hκ := (S.U_eq κ.1).1 κ.2
  rw [S.U_eq]
  refine ⟨(UPts σ J _).mul_mem ((UPts σ J _).mul_mem ((UPts σ J _).inv_mem δ.2) hκ.1) δ.2, fun v' => ?_⟩
  by_cases hv' : v' = v
  · subst hv'
    have hk := hκ.2 v'
    rw [S.UlocAlt v' hv] at hk ⊢
    obtain ⟨hkL, hkF, hkf⟩ := hk
    simp only [map_mul, map_inv]
    refine ⟨(levelVL σ J v' S.Lb).mul_mem ((levelVL σ J v' S.Lb).mul_mem
      ((levelVL σ J v' S.Lb).inv_mem h2) hkL) h2, ?_⟩
    have hgg : (bc (prV (E := E) v') δ.1)⁻¹ * bc (prV (E := E) v') κ.1 * bc (prV (E := E) v') δ.1 ∈
        stabGL (latS (F := F) (v'.adicCompletion F) (intV E v')
          (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :=
      (stabGL _).mul_mem ((stabGL _).mul_mem ((stabGL _).inv_mem hg) hkF) hg
    refine ⟨hgg, fun x => ?_⟩
    set y : latS (F := F) (v'.adicCompletion F) (intV E v')
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) :=
      ⟨((bc (prV (E := E) v') δ.1)⁻¹ * bc (prV (E := E) v') κ.1 * bc (prV (E := E) v') δ.1).1 *ᵥ x.1,
        (hgg x.1).1 x.2⟩ with hy
    have e1 : (⟨(bc (prV (E := E) v') δ.1).1 *ᵥ y.1, (hg y.1).1 y.2⟩ :
        latS (F := F) (v'.adicCompletion F) (intV E v') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) =
        ⟨(bc (prV (E := E) v') κ.1).1 *ᵥ ((bc (prV (E := E) v') δ.1).1 *ᵥ x.1),
          (hkF _).1 ((hg x.1).1 x.2)⟩ := by
      apply Subtype.ext
      simp only [hy, Matrix.mulVec_mulVec, Units.val_mul, ← Matrix.mul_assoc]
      rw [Units.mul_inv, Matrix.one_mul]
    have A := h3 y
    rw [e1, hkf ⟨_, (hg x.1).1 x.2⟩, h3 x] at A
    exact A.symm
  · have hk := hκ.2 v'
    simpa [map_mul, map_inv, h1 v' hv'] using hk

theorem pow_mul_mem_of_normalises {G : Type} [Group G] (U : Subgroup G) (d : G) (hd : ∀ κ ∈ U, d⁻¹ * κ * d ∈ U) (N : ℕ)
    (hN : d ^ N ∈ U) (κ : G) (hκ : κ ∈ U) : (d * κ) ^ N ∈ U := by
  have key : ∀ m : ℕ, ∃ κ' ∈ U, (d * κ) ^ m = d ^ m * κ' := by
    intro m
    induction m with
    | zero => exact ⟨1, U.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨κ', hκ', e⟩ := ih
      refine ⟨(d⁻¹ * κ' * d) * κ, U.mul_mem (hd κ' hκ') hκ, ?_⟩
      rw [pow_succ, e, pow_succ]; group
  obtain ⟨κ', hκ', e⟩ := key N
  rw [e]; exact U.mul_mem hN hκ'

theorem is_diamond_pow (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : IsDia S v hv k δ) (j : ℕ) :
    IsDia S v hv (k ^ j) (δ ^ j) := by
  induction j with
  | zero => simpa using is_diamond_one' S v hv
  | succ j ih => rw [pow_succ, pow_succ]; exact is_diamond_mul_mult S v hv ih h

theorem zsmul_eq_of_dvd_sub_one {M : Type} [AddCommGroup M] (T : ℕ) (m : M) (hT : (T : ℤ) • m = 0) (k : ℤ)
    (hk : (T : ℤ) ∣ k - 1) : k • m = m := by
  obtain ⟨c, hc⟩ := hk
  have : k = 1 + c * T := by linarith
  rw [this, add_zsmul, one_zsmul, mul_smul, hT, smul_zero, add_zero]

theorem level_functional_torsion (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (x) :
    (T : ℤ) • S.fT v hv x = 0 := by
  have h := S.fT_T v hv x
  rw [map_smul] at h
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (intV E v)]
  exact h

theorem diamond_mem_level_of_congr_one (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : IsDia S v hv k δ) (hk : (T : ℤ) ∣ k - 1) : δ.1 ∈ S.U := by
  obtain ⟨h1, h2, hg, h3⟩ := h
  rw [S.U_eq]
  refine ⟨δ.2, fun v' => ?_⟩
  by_cases hv' : v' = v
  · subst hv'
    rw [S.UlocAlt v' hv]
    refine ⟨h2, hg, fun x => ?_⟩
    have e := h3 x
    rw [zsmul_eq_of_dvd_sub_one T _ (level_functional_torsion S v' hv _) k hk] at e
    exact e
  · rw [h1 v' hv']; exact (S.Uloc v').one_mem

theorem multiplier_congr_one_of_mem (S : StepLevel F E σ J T f bad) (hT : T.Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : IsDia S v hv k δ)
    (hU : δ.1 ∈ S.U) : (T : ℤ) ∣ k - 1 := by
  obtain ⟨h1, h2, hg, h3⟩ := h
  have hloc := ((S.U_eq δ.1).1 hU).2 v
  rw [S.UlocAlt v hv] at hloc
  obtain ⟨_, hg', hfix⟩ := hloc
  have hne := S.fT_ne v hv
  obtain ⟨x, hx⟩ : ∃ x, S.fT v hv x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (LinearMap.ext hc)
  have e1 := h3 x
  have e2 := hfix x
  rw [e2] at e1
  have hk1 : (k - 1) • S.fT v hv x = 0 := by rw [sub_zsmul, one_zsmul, e1]; simp
  have hT0 := level_functional_torsion S v hv x
  by_contra hnd
  have hp : Prime (T : ℤ) := Nat.prime_iff_prime_int.1 hT
  obtain ⟨p, q, hpq⟩ := (hp.coprime_iff_not_dvd).2 hnd
  apply hx
  calc S.fT v hv x = (p * T + q * (k - 1)) • S.fT v hv x := by rw [hpq, one_zsmul]
    _ = 0 := by rw [add_zsmul, mul_smul, mul_smul, hT0, hk1, smul_zero, smul_zero, add_zero]

def LocalDiamondCondition (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : ℤ)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Prop :=
  x ∈ levelVL σ J v S.Lb ∧ ∃ hg : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))),
    ∀ y : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      k • S.fT v hv ⟨(x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y.1, (hg y.1).1 y.2⟩ = S.fT v hv y

theorem is_diamond_local_cond (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : IsDia S v hv k δ) :
    LocalDiamondCondition S v hv k (bc (prV (E := E) v) δ.1) := h.2

theorem local_diamond_cond_one (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) :
    LocalDiamondCondition S v hv 1 1 := by
  refine ⟨(levelVL σ J v S.Lb).one_mem, (stabGL _).one_mem, fun y => ?_⟩
  rw [one_smul]
  congr 1
  apply Subtype.ext
  simp

theorem local_diamond_cond_mul (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k k' : ℤ} {x x' : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (h : LocalDiamondCondition S v hv k x) (h' : LocalDiamondCondition S v hv k' x') :
    LocalDiamondCondition S v hv (k * k') (x * x') := by
  obtain ⟨h2, hg, h3⟩ := h
  obtain ⟨h2', hg', h3'⟩ := h'
  have hgg : x * x' ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) := (stabGL _).mul_mem hg hg'
  refine ⟨(levelVL σ J v S.Lb).mul_mem h2 h2', hgg, fun y => ?_⟩
  have e : (⟨((x * x' : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y.1,
      (hgg y.1).1 y.2⟩ : latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) =
      ⟨(x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
        ((x' : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y.1), (hg _).1 ((hg' y.1).1 y.2)⟩ := by
    apply Subtype.ext
    simp [Units.val_mul, Matrix.mulVec_mulVec]
  rw [e, mul_comm, mul_smul, h3 ⟨_, (hg' y.1).1 y.2⟩, h3' y]

theorem local_diamond_cond_pow (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (h : LocalDiamondCondition S v hv k x) (j : ℕ) :
    LocalDiamondCondition S v hv (k ^ j) (x ^ j) := by
  induction j with
  | zero => simpa using local_diamond_cond_one S v hv
  | succ j ih => rw [pow_succ, pow_succ]; exact local_diamond_cond_mul S v hv ih h

theorem local_diamond_conj_mem (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (h : LocalDiamondCondition S v hv k x) (y : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy : y ∈ S.Uloc v) : x⁻¹ * y * x ∈ S.Uloc v := by
  obtain ⟨h2, hg, h3⟩ := h
  rw [S.UlocAlt v hv] at hy ⊢
  obtain ⟨hkL, hkF, hkf⟩ := hy
  refine ⟨(levelVL σ J v S.Lb).mul_mem ((levelVL σ J v S.Lb).mul_mem ((levelVL σ J v S.Lb).inv_mem h2) hkL) h2, ?_⟩
  have hgg : x⁻¹ * y * x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :=
    (stabGL _).mul_mem ((stabGL _).mul_mem ((stabGL _).inv_mem hg) hkF) hg
  refine ⟨hgg, fun z => ?_⟩
  set w : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) :=
    ⟨((x⁻¹ * y * x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ z.1,
      (hgg z.1).1 z.2⟩ with hw
  have e1 : (⟨(x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ w.1, (hg w.1).1 w.2⟩ :
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) =
      ⟨(y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
        ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ z.1), (hkF _).1 ((hg z.1).1 z.2)⟩ := by
    apply Subtype.ext
    simp only [hw, Matrix.mulVec_mulVec, Units.val_mul, ← Matrix.mul_assoc]
    rw [Units.mul_inv, Matrix.one_mul]
  have A := h3 w
  rw [e1, hkf ⟨_, (hg z.1).1 z.2⟩, h3 z] at A
  exact A.symm

theorem local_diamond_mem_level (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (h : LocalDiamondCondition S v hv k x) (hk : (T : ℤ) ∣ k - 1) :
    x ∈ S.Uloc v := by
  obtain ⟨h2, hg, h3⟩ := h
  rw [S.UlocAlt v hv]
  refine ⟨h2, hg, fun y => ?_⟩
  have e := h3 y
  rw [zsmul_eq_of_dvd_sub_one T _ (level_functional_torsion S v hv _) k hk] at e
  exact e

theorem local_multiplier_congr_one (S : StepLevel F E σ J T f bad) (hT : T.Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : ℤ} {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (h : LocalDiamondCondition S v hv k x)
    (hU : x ∈ S.Uloc v) : (T : ℤ) ∣ k - 1 := by
  obtain ⟨h2, hg, h3⟩ := h
  rw [S.UlocAlt v hv] at hU
  obtain ⟨_, hg', hfix⟩ := hU
  obtain ⟨y, hy⟩ : ∃ y, S.fT v hv y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact S.fT_ne v hv (LinearMap.ext hc)
  have e1 := h3 y
  rw [hfix y] at e1
  have hk1 : (k - 1) • S.fT v hv y = 0 := by rw [sub_zsmul, one_zsmul, e1]; simp
  have hT0 := level_functional_torsion S v hv y
  by_contra hnd
  have hp : Prime (T : ℤ) := Nat.prime_iff_prime_int.1 hT
  obtain ⟨p, q, hpq⟩ := (hp.coprime_iff_not_dvd).2 hnd
  apply hy
  calc S.fT v hv y = (p * T + q * (k - 1)) • S.fT v hv y := by rw [hpq, one_zsmul]
    _ = 0 := by rw [add_zsmul, mul_smul, mul_smul, hT0, hk1, smul_zero, smul_zero, add_zero]

def MultiPlaceDiamond (S : StepLevel F E σ J T f bad) {P : Type} (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) (k : P → ℤ) (δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : Prop :=
  (∀ w, (∀ p, w ≠ pl p) → bc (prV (E := E) w) δ.1 = 1) ∧ ∀ p, LocalDiamondCondition S (pl p) (hpl p) (k p) (bc (prV (E := E) (pl p)) δ.1)

theorem multi_diamond_mul (S : StepLevel F E σ J T f bad) {P : Type} (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) {k k' : P → ℤ} {δ δ' : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : MultiPlaceDiamond S pl hpl k δ) (h' : MultiPlaceDiamond S pl hpl k' δ') : MultiPlaceDiamond S pl hpl (k * k') (δ * δ') := by
  refine ⟨fun w hw => ?_, fun p => ?_⟩
  · simp [Subgroup.coe_mul, map_mul, h.1 w hw, h'.1 w hw]
  · have := local_diamond_cond_mul S (pl p) (hpl p) (h.2 p) (h'.2 p)
    simpa [Subgroup.coe_mul, map_mul] using this

theorem multi_diamond_one (S : StepLevel F E σ J T f bad) {P : Type} (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) : MultiPlaceDiamond S pl hpl 1 1 := by
  refine ⟨fun w _ => by simp, fun p => ?_⟩
  simpa using local_diamond_cond_one S (pl p) (hpl p)

theorem multi_diamond_pow (S : StepLevel F E σ J T f bad) {P : Type} (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) {k : P → ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : MultiPlaceDiamond S pl hpl k δ) (j : ℕ) : MultiPlaceDiamond S pl hpl (k ^ j) (δ ^ j) := by
  induction j with
  | zero => simpa using multi_diamond_one S pl hpl
  | succ j ih => rw [pow_succ, pow_succ]; exact multi_diamond_mul S pl hpl ih h

theorem multi_diamond_of_is_diamond (S : StepLevel F E σ J T f bad) {P : Type} [DecidableEq P] (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) (hinj : Function.Injective pl) (p0 : P) {k : ℤ}
    {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : IsDia S (pl p0) (hpl p0) k δ) :
    MultiPlaceDiamond S pl hpl (Function.update 1 p0 k) δ := by
  refine ⟨fun w hw => h.1 w (hw p0), fun p => ?_⟩
  by_cases hp : p = p0
  · subst hp
    rw [Function.update_self]
    exact h.2
  · rw [Function.update_of_ne hp, h.1 (pl p) (fun e => hp (hinj e))]
    simpa using local_diamond_cond_one S (pl p) (hpl p)

theorem multi_diamond_conj_mem (S : StepLevel F E σ J T f bad) {P : Type} (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) {k : P → ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : MultiPlaceDiamond S pl hpl k δ) (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hκ : κ ∈ S.U) :
    δ.1⁻¹ * κ * δ.1 ∈ S.U := by
  have hκ' := (S.U_eq κ).1 hκ
  rw [S.U_eq]
  refine ⟨(UPts σ J _).mul_mem ((UPts σ J _).mul_mem ((UPts σ J _).inv_mem δ.2) hκ'.1) δ.2, fun w => ?_⟩
  by_cases hw : ∃ p, w = pl p
  · obtain ⟨p, rfl⟩ := hw
    simp only [map_mul, map_inv]
    exact local_diamond_conj_mem S (pl p) (hpl p) (h.2 p) _ (hκ'.2 (pl p))
  · push_neg at hw
    simpa [map_mul, map_inv, h.1 w hw] using hκ'.2 w

theorem multi_diamond_mem_level (S : StepLevel F E σ J T f bad) {P : Type} (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) {k : P → ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : MultiPlaceDiamond S pl hpl k δ) (hk : ∀ p, (T : ℤ) ∣ k p - 1) : δ.1 ∈ S.U := by
  rw [S.U_eq]
  refine ⟨δ.2, fun w => ?_⟩
  by_cases hw : ∃ p, w = pl p
  · obtain ⟨p, rfl⟩ := hw
    exact local_diamond_mem_level S (pl p) (hpl p) (h.2 p) (hk p)
  · push_neg at hw
    rw [h.1 w hw]; exact (S.Uloc w).one_mem

theorem multi_diamond_multiplier_congr (S : StepLevel F E σ J T f bad) (hT : T.Prime) {P : Type} (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) {k : P → ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : MultiPlaceDiamond S pl hpl k δ) (hU : δ.1 ∈ S.U) (p : P) : (T : ℤ) ∣ k p - 1 :=
  local_multiplier_congr_one S hT (pl p) (hpl p) (h.2 p) (((S.U_eq δ.1).1 hU).2 (pl p))

theorem class_mul_right_of_normalises (S : StepLevel F E σ J T f bad) (y y' δ' δ : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hδ : ∀ κ ∈ S.U, δ.1⁻¹ * κ * δ.1 ∈ S.U)
    (h : (Quotient.mk'' y' : Cls S) = Quotient.mk'' (y * δ')) :
    (Quotient.mk'' (y' * δ) : Cls S) = Quotient.mk'' (y * δ' * δ) := by
  obtain ⟨hh, hhH, κ, hκK, e⟩ := (DoubleCoset.eq _ _ y' (y * δ')).1 h
  refine (DoubleCoset.eq _ _ (y' * δ) (y * δ' * δ)).2 ⟨hh, hhH, δ⁻¹ * κ * δ, ?_, ?_⟩
  · exact hδ κ.1 hκK
  · rw [e]; group

end Loc

variable {D : D7} {u : D.what₂.Word}

theorem level_prime_ne_type_prime' (A : AtTTied u) (j : Fin 2) : (D.mem u).A.T ≠ D.host.g j := by
  intro hTg
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 A.piU_cong
  have hdiv : D.host.g j ∣ D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 := by
    apply Dvd.dvd.mul_left
    fin_cases j
    · exact Dvd.dvd.pow (Dvd.intro _ rfl) two_ne_zero
    · exact Dvd.dvd.pow (Dvd.intro_left _ rfl) two_ne_zero
  obtain ⟨M, hM⟩ := hdiv
  set N : ℕ := D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 with hN
  have hpi : ((A.piU : 𝓞 D.host.E) : D.host.E) = 1 + (r : D.host.E) * (N : D.host.E) := by
    have := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hr
    push_cast at this
    linear_combination -this
  have hcpi : D.host.conj ((A.piU : 𝓞 D.host.E) : D.host.E) =
      1 + D.host.conj (r : D.host.E) * (N : D.host.E) := by
    rw [hpi, map_add, map_one, map_mul, map_natCast]
  have hNM : (N : D.host.E) = (D.host.g j : D.host.E) * (M : D.host.E) := by
    rw [hM]; push_cast; ring
  have h0 := A.piU_norm
  rw [hcpi, hpi, hTg] at h0
  set r' := D.host.conj (r : D.host.E)
  have key : (D.host.g j : D.host.E) * (1 - (M : D.host.E) * ((r : D.host.E) + r' + (r : D.host.E) * r' * N)) = 1 := by
    linear_combination (-1 : D.host.E) * h0 + ((r : D.host.E) + r' + (r : D.host.E) * r' * N) * hNM
  have hr' : IsIntegral ℤ r' := map_isIntegral_int D.host.conj (RingOfIntegers.isIntegral_coe r)
  have hrI : IsIntegral ℤ (r : D.host.E) := RingOfIntegers.isIntegral_coe r
  have hint : IsIntegral ℤ (1 - (M : D.host.E) * ((r : D.host.E) + r' + (r : D.host.E) * r' * N)) := by
    refine isIntegral_one.sub (IsIntegral.mul ?_ ((hrI.add hr').add ((hrI.mul hr').mul ?_)))
    · simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (M : ℤ)))
    · simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (N : ℤ)))
  have hg0 : (D.host.g j : D.host.E) ≠ 0 := by
    exact_mod_cast (D.host.g_prime j).ne_zero
  have hinv : (1 - (M : D.host.E) * ((r : D.host.E) + r' + (r : D.host.E) * r' * N)) =
      algebraMap ℚ D.host.E ((D.host.g j : ℚ)⁻¹) := by
    rw [map_inv₀, map_natCast]
    exact (eq_inv_of_mul_eq_one_right key)
  rw [hinv] at hint
  have hq : IsIntegral ℤ ((D.host.g j : ℚ)⁻¹) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ D.host.E).injective).1 hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hq
  have hy' : (y : ℚ) * (D.host.g j : ℚ) = 1 := by
    rw [show (y : ℚ) = algebraMap ℤ ℚ y from rfl, hy]
    exact inv_mul_cancel₀ (by exact_mod_cast (D.host.g_prime j).ne_zero)
  have hyz : y * (D.host.g j : ℤ) = 1 := by exact_mod_cast hy'
  have hd : ((D.host.g j : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ) := ⟨y, by rw [Nat.cast_one, ← hyz, mul_comm]⟩
  exact (D.host.g_prime j).not_dvd_one (Int.natCast_dvd_natCast.1 hd)

theorem level_places_prime_to_type (A : AtTTied u) (v : (D.mem u).A.vT) : (A.eV v).1 ∉ badG D := by
  have hT := (A.eV v).2
  have hTp := (D.mem u).A.T_prime
  have key : ∀ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∉ (A.eV v).1.asIdeal := by
    intro j hj
    have hcop : Nat.Coprime (D.mem u).A.T (D.host.g j) :=
      (Nat.coprime_primes hTp (D.host.g_prime j)).2 (level_prime_ne_type_prime' A j)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : ((a * (D.mem u).A.T + b * D.host.g j : ℤ) : 𝓞 D.host.F) ∈ (A.eV v).1.asIdeal := by
      push_cast
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hT) (Ideal.mul_mem_left _ _ hj)
    rw [hab, Int.cast_one] at h1
    exact (A.eV v).1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  rintro (h | h)
  · exact key 0 h
  · exact key 1 h

theorem rank_zero_le_type_level : D.R.N 0 ≤ aOf D.R 0 := by
  have := D.R.two_le_m
  unfold aOf Ranks.N
  rw [if_pos (by omega)]
  simp

theorem fixed_class_mem_level_general (K : ClsTied u 0 (Nat.zero_le _)) (G : GLoc D.host.F D.host.E (sigD D) D.host.g)
    {a t nb skip fc : ℕ} {zl : Bool} (L : GLev K.lev G a t nb skip fc zl) (ha : D.R.N 0 ≤ a)
    (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (c : (D.mem u).C.cls 0)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hbad : ∀ w ∈ badG D, bc (prV (E := D.host.E) w) δ.1 = 1) (N0 : ℕ) (hN0 : 0 < N0)
    (hpow : ∀ κ ∈ K.lev.U, (δ.1 * κ) ^ N0 ∈ K.lev.U)
    (hfix : (Quotient.mk'' (K.y c * δ) : Cls K.lev) = Quotient.mk'' (K.y c)) :
    δ.1 ∈ K.lev.U := by
  obtain ⟨hh, hhH, κ, hκK, e⟩ := (DoubleCoset.eq _ _ (K.y c * δ) (K.y c)).1 hfix
  have hκ : κ.1 ∈ K.lev.U := hκK
  obtain ⟨g, hgU, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have e1 : (K.y c).1 = hh.1 * ((K.y c).1 * δ.1) * κ.1 := by
    have := congrArg Subtype.val e
    simp only [Subgroup.coe_mul] at this
    exact this
  have hzp := conj_pow_rational_rel (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) g hh.1 (K.y c).1
    δ.1 κ.1 hge e1
  have hgi : g⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := (UJ _ _).inv_mem hgU
  have hN0one : g⁻¹ ^ N0 = 1 := by
    have hmem : (⟨g⁻¹ ^ N0, (UJ _ _).pow_mem hgi N0⟩ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) ∈
        (K.stabI c).range := by
      rw [K.stabI_range c]
      refine Subgroup.mem_map.2 ⟨(δ.1 * κ.1) ^ N0, hpow κ.1 hκ, ?_⟩
      show (K.y c).1 * (δ.1 * κ.1) ^ N0 * (K.y c).1⁻¹ =
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (g⁻¹ ^ N0)
      rw [hzp N0]; group
    obtain ⟨s, hs⟩ := hmem
    haveI := hS c
    rw [Subsingleton.elim s 1, map_one] at hs
    exact (congrArg Subtype.val hs).symm
  have hcop : ∀ (i : Fin 2) (j N : ℕ), Nat.Coprime N (D.host.g i) → (g⁻¹ ^ j) ^ N = 1 → g⁻¹ ^ j = 1 := by
    intro i j N hc hjN
    obtain ⟨w, hw⟩ := Formalism.L2.G.Triv.exists_place (F := D.host.F) (D.host.g i) (D.host.g_prime i)
    have hwb : w ∈ badG D := by
      fin_cases i
      · exact Or.inl hw
      · exact Or.inr hw
    have hxU : bc (prV (E := D.host.E) w) ((δ.1 * κ.1) ^ j) ∈ K.lev.Uloc w := by
      rw [map_mul_pow_of_map_eq_one _ δ.1 κ.1 (hbad w hwb) j]
      exact (K.lev.Uloc w).pow_mem (((K.lev.U_eq κ.1).1 hκ).2 w) j
    have hxN := pow_image_eq_one (bc (prV (E := D.host.E) w)) _ _ _ g⁻¹ hzp j N hjN
    have h1 := torsion_reduction_trivial K.lev G L ha i (D.host.g_prime i) w hw _ hxU N hc hxN
    have hinj := base_change_GL_comp_injective (m := D.R.N 0) (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (prV (E := D.host.E) w) (G.phi i w hw) (RingHom.injective _)
    exact pow_eq_one_of_comp_eq_one (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
      (bc (prV (E := D.host.E) w)) (bc (G.phi i w hw)) hinj _ _ g⁻¹ hzp j h1
  have hg1 : g⁻¹ = 1 := eq_one_of_coprime_torsion_two_primes g⁻¹ (D.host.g 0) (D.host.g 1) N0 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hN0
    hN0one (hcop 0) (hcop 1)
  rw [eq_inv_of_conj_trivial _ g⁻¹ _ δ.1 κ.1 (hzp 1) hg1]
  exact K.lev.U.inv_mem hκ

theorem rank_zero_le_weight : D.R.N 0 ≤ D.R.k := by
  have h := rank_zero_le_type_level (D := D)
  have e : aOf D.R 0 = D.R.k := by
    unfold aOf
    rw [if_pos (by have := D.R.two_le_m; omega)]
    simp
  omega

theorem fixed_class_mem_level (Tf : Forms0 D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (c : (D.mem u).C.cls 0)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hbad : ∀ w ∈ badG D, bc (prV (E := D.host.E) w) δ.1 = 1) (N0 : ℕ) (hN0 : 0 < N0)
    (hpow : ∀ κ ∈ (Tf.cls 0 (Nat.zero_le _) rfl).lev.U, (δ.1 * κ) ^ N0 ∈ (Tf.cls 0 (Nat.zero_le _) rfl).lev.U)
    (hfix : (Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _) rfl).y c * δ) : Cls (Tf.cls 0 (Nat.zero_le _) rfl).lev) =
      Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _) rfl).y c)) :
    δ.1 ∈ (Tf.cls 0 (Nat.zero_le _) rfl).lev.U :=
  fixed_class_mem_level_general (Tf.cls 0 (Nat.zero_le _) rfl) Tf.gl (Tf.glev0) rank_zero_le_weight hS c δ hbad N0 hN0 hpow hfix

theorem dilation_free_on_classes (Tf : Forms0 D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (v : (D.mem u).A.vT)
    (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ) (hk : (k : (D.mem u).A.Fv v) = a)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia (Tf.cls 0 (Nat.zero_le _) rfl).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 k δ)
    (c : (D.mem u).C.cls 0) (hc : (D.fm u).dil 0 v a c = c) : a = 1 := by
  have hcls := (Tf.val 0 (Nat.zero_le _) rfl).dil v a k hk c δ hδ
  rw [hc] at hcls
  have hT := (D.mem u).A.T_prime
  have hnb := level_places_prime_to_type Tf.atT v
  have hbad : ∀ w ∈ badG D, bc (prV (E := D.host.E) w) δ.1 = 1 := fun w hw =>
    hδ.1 w (fun e => hnb (e ▸ hw))
  have hcard := (D.mem u).A.card_Fv v
  haveI : Fact (D.mem u).A.T.Prime := ⟨hT⟩
  haveI : CharP ((D.mem u).A.Fv v) (D.mem u).A.T := charP_of_card_eq_prime hcard
  have ha0 : (a : (D.mem u).A.Fv v) ≠ 0 := a.ne_zero
  have hkT : ((D.mem u).A.T : ℤ) ∣ k ^ ((D.mem u).A.T - 1) - 1 := by
    rw [← CharP.intCast_eq_zero_iff ((D.mem u).A.Fv v) (D.mem u).A.T]
    push_cast
    rw [hk, ← hcard, FiniteField.pow_card_sub_one_eq_one _ ha0, sub_self]
  have hpowU : δ.1 ^ ((D.mem u).A.T - 1) ∈ (Tf.cls 0 (Nat.zero_le _) rfl).lev.U := by
    have := diamond_mem_level_of_congr_one _ _ _ (is_diamond_pow _ _ _ hδ ((D.mem u).A.T - 1)) hkT
    simpa using this
  have hmem := fixed_class_mem_level Tf hS c δ hbad ((D.mem u).A.T - 1) (by have := hT.two_le; omega)
    (fun κ hκ => pow_mul_mem_of_normalises _ δ.1 (fun κ' hκ' => diamond_conj_mem_level' _ _ _ hδ ⟨κ', hκ'⟩) _ hpowU κ hκ) hcls.symm
  have hdvd := multiplier_congr_one_of_mem _ hT _ _ hδ hmem
  apply Units.ext
  rw [← hk, Units.val_one]
  have := (CharP.intCast_eq_zero_iff ((D.mem u).A.Fv v) (D.mem u).A.T (k - 1)).2 hdvd
  push_cast at this
  exact sub_eq_zero.1 this

theorem diamond_free_on_classes (Tf : Forms0 D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (k : (D.mem u).A.vT → ℤ)
    (hk0 : ∀ v, (k v : (D.mem u).A.Fv v) ≠ 0)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : MultiPlaceDiamond (Tf.cls 0 (Nat.zero_le _) rfl).lev (fun v => (Tf.atT.eV v).1) (fun v => (Tf.atT.eV v).2) k δ)
    (c : (D.mem u).C.cls 0)
    (hfix : (Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _) rfl).y c * δ) : Cls (Tf.cls 0 (Nat.zero_le _) rfl).lev) =
      Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _) rfl).y c)) :
    ∀ v, (k v : (D.mem u).A.Fv v) = 1 := by
  have hT := (D.mem u).A.T_prime
  have hbad : ∀ w ∈ badG D, bc (prV (E := D.host.E) w) δ.1 = 1 := fun w hw =>
    hδ.1 w (fun v e => level_places_prime_to_type Tf.atT v (by subst e; exact hw))
  haveI : Fact (D.mem u).A.T.Prime := ⟨hT⟩
  have hkT : ∀ v, ((D.mem u).A.T : ℤ) ∣ (k ^ ((D.mem u).A.T - 1)) v - 1 := by
    intro v
    haveI : CharP ((D.mem u).A.Fv v) (D.mem u).A.T := charP_of_card_eq_prime ((D.mem u).A.card_Fv v)
    rw [← CharP.intCast_eq_zero_iff ((D.mem u).A.Fv v) (D.mem u).A.T, Pi.pow_apply]
    push_cast
    rw [← (D.mem u).A.card_Fv v, FiniteField.pow_card_sub_one_eq_one _ (hk0 v), sub_self]
  have hpowU : δ.1 ^ ((D.mem u).A.T - 1) ∈ (Tf.cls 0 (Nat.zero_le _) rfl).lev.U := by
    have := multi_diamond_mem_level _ _ _ (multi_diamond_pow _ _ _ hδ ((D.mem u).A.T - 1)) hkT
    simpa using this
  have hmem := fixed_class_mem_level Tf hS c δ hbad ((D.mem u).A.T - 1) (by have := hT.two_le; omega)
    (fun κ hκ => pow_mul_mem_of_normalises _ δ.1 (fun κ' hκ' => multi_diamond_conj_mem _ _ _ hδ κ' hκ') _ hpowU κ hκ) hfix
  intro v
  have hdvd := multi_diamond_multiplier_congr _ hT _ _ hδ hmem v
  haveI : CharP ((D.mem u).A.Fv v) (D.mem u).A.T := charP_of_card_eq_prime ((D.mem u).A.card_Fv v)
  have := (CharP.intCast_eq_zero_iff ((D.mem u).A.Fv v) (D.mem u).A.T (k v - 1)).2 hdvd
  push_cast at this
  exact sub_eq_zero.1 this

theorem dilation_mul_of_diamonds (Tf : Forms0 D u) (v : (D.mem u).A.vT) (a b : ((D.mem u).A.Fv v)ˣ)
    (ka kb : ℤ) (hka : (ka : (D.mem u).A.Fv v) = a) (hkb : (kb : (D.mem u).A.Fv v) = b)
    (δa δb : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (ha : IsDia (Tf.cls 0 (Nat.zero_le _) rfl).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 ka δa)
    (hb : IsDia (Tf.cls 0 (Nat.zero_le _) rfl).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 kb δb) (c : (D.mem u).C.cls 0) :
    (D.fm u).dil 0 v a ((D.fm u).dil 0 v b c) = (D.fm u).dil 0 v (b * a) c := by
  have W := Tf.val 0 (Nat.zero_le _) rfl
  have h1 := W.dil v a ka hka ((D.fm u).dil 0 v b c) δa ha
  have h2 := W.dil v b kb hkb c δb hb
  have h3 := class_mul_right_of_normalises _ _ _ _ δa (fun κ hκ => diamond_conj_mem_level' _ _ _ ha ⟨κ, hκ⟩) h2
  have hab : ((kb * ka : ℤ) : (D.mem u).A.Fv v) = ((b * a : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) := by
    rw [Int.cast_mul, hka, hkb, Units.val_mul]
  have h4 := W.dil v (b * a) (kb * ka) hab c (δb * δa) (is_diamond_mul_mult _ _ _ hb ha)
  have h5 : (Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _) rfl).y c * δb * δa) : Cls (Tf.cls 0 (Nat.zero_le _) rfl).lev) =
      Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _) rfl).y c * (δb * δa)) := by rw [mul_assoc]
  exact (Tf.cls 0 (Nat.zero_le _) rfl).y_bij.1 (h1.trans (h3.trans (h5.trans h4.symm)))

theorem dilation_commute_distinct (Tf : Forms0 D u) (v v' : (D.mem u).A.vT) (hvv : v ≠ v') (a : ((D.mem u).A.Fv v)ˣ)
    (b : ((D.mem u).A.Fv v')ˣ) (ka kb : ℤ) (hka : (ka : (D.mem u).A.Fv v) = a) (hkb : (kb : (D.mem u).A.Fv v') = b)
    (δa δb : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (ha : IsDia (Tf.cls 0 (Nat.zero_le _) rfl).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 ka δa)
    (hb : IsDia (Tf.cls 0 (Nat.zero_le _) rfl).lev (Tf.atT.eV v').1 (Tf.atT.eV v').2 kb δb) (c : (D.mem u).C.cls 0) :
    (D.fm u).dil 0 v a ((D.fm u).dil 0 v' b c) = (D.fm u).dil 0 v' b ((D.fm u).dil 0 v a c) := by
  have W := Tf.val 0 (Nat.zero_le _) rfl
  have hne : (Tf.atT.eV v).1 ≠ (Tf.atT.eV v').1 := fun e => hvv (Tf.atT.eV.injective (Subtype.ext e))
  have h1 := class_mul_right_of_normalises _ _ _ _ δa (fun κ hκ => diamond_conj_mem_level' _ _ _ ha ⟨κ, hκ⟩) (W.dil v' b kb hkb c δb hb)
  have h2 := class_mul_right_of_normalises _ _ _ _ δb (fun κ hκ => diamond_conj_mem_level' _ _ _ hb ⟨κ, hκ⟩) (W.dil v a ka hka c δa ha)

  have hU : ((δb * δa)⁻¹ * (δa * δb)).1 ∈ (Tf.cls 0 (Nat.zero_le _) rfl).lev.U := by
    rw [(Tf.cls 0 (Nat.zero_le _) rfl).lev.U_eq]
    refine ⟨((δb * δa)⁻¹ * (δa * δb)).2, fun w => ?_⟩
    have hcomp : bc (prV (E := D.host.E) w) ((δb * δa)⁻¹ * (δa * δb)).1 = 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      by_cases hw : w = (Tf.atT.eV v).1
      · rw [hb.1 w (by rw [hw]; exact hne)]; group
      · rw [ha.1 w hw]; group
    rw [hcomp]
    exact (Subgroup.one_mem _)
  have hmid : (Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _) rfl).y c * δb * δa) : Cls (Tf.cls 0 (Nat.zero_le _) rfl).lev) =
      Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _) rfl).y c * δa * δb) :=
    (DoubleCoset.eq _ _ _ _).2 ⟨1, Subgroup.one_mem _, (δb * δa)⁻¹ * (δa * δb), hU, by group⟩
  exact (Tf.cls 0 (Nat.zero_le _) rfl).y_bij.1 ((W.dil v a ka hka _ δa ha).trans (h1.trans (hmid.trans
    (h2.symm.trans (W.dil v' b kb hkb _ δb hb).symm))))

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
