import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.OneAddPowOfSq

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Grp

theorem conj_pow_rational_rel {H A : Type} [Group H] [Group A] (ι : H →* A) (g : H) (hh yy δ κ : A) (hge : ι g = hh)
    (e1 : yy = hh * (yy * δ) * κ) (j : ℕ) : (δ * κ) ^ j = yy⁻¹ * ι (g⁻¹ ^ j) * yy := by
  have h1 : yy⁻¹ * hh⁻¹ * yy = δ * κ := by
    calc yy⁻¹ * hh⁻¹ * yy = yy⁻¹ * hh⁻¹ * (hh * (yy * δ) * κ) := by rw [← e1]
      _ = δ * κ := by simp [mul_assoc]
  rw [← h1, map_pow, map_inv, hge]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ, ih]
    simp [mul_assoc]

theorem map_mul_pow_of_map_eq_one {A B : Type} [Group A] [Group B] (ψ : A →* B) (δ κ : A) (h : ψ δ = 1) (j : ℕ) :
    ψ ((δ * κ) ^ j) = (ψ κ) ^ j := by
  rw [map_pow, map_mul, h, one_mul]

theorem pow_image_eq_one {H A B : Type} [Group H] [Group A] [Group B] (ψ : A →* B) (ι : H →* A) (z yy : A) (γ : H)
    (hz : ∀ j : ℕ, z ^ j = yy⁻¹ * ι (γ ^ j) * yy) (j N : ℕ) (h : (γ ^ j) ^ N = 1) : (ψ (z ^ j)) ^ N = 1 := by
  rw [← map_pow, ← pow_mul, hz, pow_mul, h]
  simp

theorem pow_eq_one_of_comp_eq_one {H A B C : Type} [Group H] [Group A] [Group B] [Group C] (ι : H →* A) (ψ : A →* B)
    (φ : B →* C) (hinj : Function.Injective (φ.comp (ψ.comp ι))) (z yy : A) (γ : H)
    (hz : ∀ j : ℕ, z ^ j = yy⁻¹ * ι (γ ^ j) * yy) (j : ℕ) (h : φ (ψ (z ^ j)) = 1) : γ ^ j = 1 := by
  apply hinj
  rw [map_one]
  rw [hz] at h
  simp only [map_mul, map_inv] at h
  have h2 := congrArg (fun t => φ (ψ yy) * t * (φ (ψ yy))⁻¹) h
  simp [mul_assoc] at h2
  simpa using h2

theorem eq_one_of_coprime_torsion_two_primes {H : Type} [Group H] (γ : H) (p q N0 : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hN0 : 0 < N0)
    (h0 : γ ^ N0 = 1) (hcp : ∀ j N : ℕ, Nat.Coprime N p → (γ ^ j) ^ N = 1 → γ ^ j = 1)
    (hcq : ∀ j N : ℕ, Nat.Coprime N q → (γ ^ j) ^ N = 1 → γ ^ j = 1) : γ = 1 := by
  obtain ⟨a, m, hm, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0.ne' p hp.one_lt.ne'
  obtain ⟨b, m', hm', hN'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0.ne' q hq.one_lt.ne'
  have h1 : γ ^ (p ^ a) = 1 :=
    hcp (p ^ a) m ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm (by rw [← pow_mul, ← hN, h0])
  have h2 : γ ^ (q ^ b) = 1 :=
    hcq (q ^ b) m' ((Nat.Prime.coprime_iff_not_dvd hq).mpr hm').symm (by rw [← pow_mul, ← hN', h0])
  have hcop : Nat.Coprime (p ^ a) (q ^ b) := Nat.Coprime.pow a b ((Nat.coprime_primes hp hq).mpr hpq)
  have h3 : γ ^ Nat.gcd (p ^ a) (q ^ b) = 1 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rwa [hcop.gcd_eq_one, pow_one] at h3

theorem eq_inv_of_conj_trivial {H A : Type} [Group H] [Group A] (ι : H →* A) (γ : H) (yy δ κ : A)
    (hz : (δ * κ) ^ 1 = yy⁻¹ * ι (γ ^ 1) * yy) (h : γ = 1) : δ = κ⁻¹ := by
  subst h
  have h1 : δ * κ = 1 := by simpa using hz
  exact eq_inv_of_mul_eq_one_left h1

theorem base_change_GL_injective {A B : Type} [CommRing A] [CommRing B] {m : ℕ} (φ : A →+* B)
    (hφ : Function.Injective φ) : Function.Injective (bc (n := Fin m) φ) := by
  intro x y hxy
  apply Units.ext
  ext i j
  have h1 := congrArg (fun z : GL (Fin m) B => (z : Matrix (Fin m) (Fin m) B) i j) hxy
  simp [bc] at h1
  exact hφ h1

theorem base_change_GL_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {m : ℕ} (g : A →+* B) (f : B →+* C)
    (x : GL (Fin m) A) : bc (n := Fin m) f (bc (n := Fin m) g x) = bc (n := Fin m) (f.comp g) x := by
  apply Units.ext
  ext i j
  simp [bc]

theorem base_change_GL_comp_injective {A B C D' : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D'] {m : ℕ}
    (ι : A →+* B) (ψ : B →+* C) (φ : C →+* D') (h : Function.Injective (φ.comp (ψ.comp ι))) :
    Function.Injective ((bc (n := Fin m) φ).comp ((bc (n := Fin m) ψ).comp (bc (n := Fin m) ι))) := by
  intro x y hxy
  simp only [MonoidHom.comp_apply, base_change_GL_comp] at hxy
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

private theorem loc1_lemma_2 (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (X : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hX : X = 1) :
    X ∈ levelVL σ J v S.Lb ∧ ∃ hg : X ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))),
      ∀ y : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
        (1 : ℤ) • S.fT v hv ⟨(X : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y.1, (hg y.1).1 y.2⟩ = S.fT v hv y := by
  subst hX
  exact ⟨one_mem _, one_mem _, fun y => by simp⟩

private theorem locmul_lemma_3 (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k k' : ℤ} (x x' z : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hz : z = x * x')
    (h : x ∈ levelVL σ J v S.Lb ∧ ∃ hg : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))),
      ∀ y : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
        k • S.fT v hv ⟨(x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y.1, (hg y.1).1 y.2⟩ = S.fT v hv y)
    (h' : x' ∈ levelVL σ J v S.Lb ∧ ∃ hg : x' ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))),
      ∀ y : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
        k' • S.fT v hv ⟨(x' : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y.1, (hg y.1).1 y.2⟩ = S.fT v hv y) :
    z ∈ levelVL σ J v S.Lb ∧ ∃ hg : z ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))),
      ∀ y : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
        (k * k') • S.fT v hv ⟨(z : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y.1, (hg y.1).1 y.2⟩ = S.fT v hv y := by
  subst hz
  obtain ⟨hx, hg, hf⟩ := h
  obtain ⟨hx', hg', hf'⟩ := h'
  refine ⟨mul_mem hx hx', mul_mem hg hg', fun y => ?_⟩
  rw [← hf' y, ← hf ⟨_, (hg' y.1).1 y.2⟩, mul_comm k k', mul_smul]
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec]

theorem is_diamond_one' (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) : IsDia S v hv 1 1 := by
  unfold IsDia
  exact ⟨fun v' _ => by simp, loc1_lemma_2 S v hv _ (by simp)⟩

theorem is_diamond_mul_mult (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k k' : ℤ} {δ δ' : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : IsDia S v hv k δ) (h' : IsDia S v hv k' δ') : IsDia S v hv (k * k') (δ * δ') := by
  unfold IsDia at h h' ⊢
  refine ⟨fun w hw => ?_, locmul_lemma_3 S v hv _ _ _ (by rw [Subgroup.coe_mul, map_mul]) h.2 h'.2⟩
  rw [Subgroup.coe_mul, map_mul, h.1 w hw, h'.1 w hw, one_mul]

private theorem mem_stabFun_lemma {A : Type} [CommRing A] {R : Type} [CommRing R] [Algebra R A] {M : Type}
    [AddCommGroup M] [Module R M] {m : ℕ} (Λ : Submodule R (Fin m → A)) (g' : Λ →ₗ[R] M) (g : GL (Fin m) A) :
    g ∈ stabFun Λ g' ↔ ∃ hg : g ∈ stabGL Λ,
      ∀ x : Λ, g' ⟨(g : Matrix (Fin m) (Fin m) A) *ᵥ (x : Fin m → A), (hg x).1 x.2⟩ = g' x :=
  Iff.rfl

private theorem conj_loc_lemma (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : ℤ} {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)}
    (hx : x ∈ levelVL σ J v S.Lb)
    (hg : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))))
    (hf : ∀ y : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      k • S.fT v hv ⟨(x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y.1, (hg y.1).1 y.2⟩ = S.fT v hv y)
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hy : y ∈ S.Uloc v) : x⁻¹ * y * x ∈ S.Uloc v := by
  rw [S.UlocAlt v hv, Subgroup.mem_inf, mem_stabFun_lemma] at hy ⊢
  obtain ⟨hyl, hgy, hfy⟩ := hy
  have hi := inv_mem hg
  refine ⟨mul_mem (mul_mem (inv_mem hx) hyl) hx, mul_mem (mul_mem hi hgy) hg, fun z => ?_⟩
  have m1 := (hg z.1).1 z.2
  have m2 := (hgy _).1 m1
  have m3 := (hi _).1 m2
  have e1 := hfy ⟨_, m1⟩
  have e2 := hf z
  have e3 := hf ⟨_, m3⟩
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [← e3, ← e2, ← e1]
  simp only [Matrix.mulVec_mulVec, Units.mul_inv_cancel_left]

theorem diamond_conj_mem_level' (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : IsDia S v hv k δ) (κ : S.U) : δ.1⁻¹ * κ.1 * δ.1 ∈ S.U := by
  unfold IsDia at h
  obtain ⟨h0, hx, hg, hf⟩ := h
  have hκ := (S.U_eq κ.1).mp κ.2
  rw [S.U_eq]
  refine ⟨mul_mem (mul_mem (inv_mem δ.2) hκ.1) δ.2, fun w => ?_⟩
  rw [map_mul, map_mul, map_inv]
  by_cases hw : w = v
  · rw [hw]
    exact conj_loc_lemma S v hv hx hg hf _ (hκ.2 v)
  · rw [h0 w hw, inv_one, one_mul, mul_one]
    exact hκ.2 w

theorem pow_mul_mem_of_normalises {G : Type} [Group G] (U : Subgroup G) (d : G) (hd : ∀ κ ∈ U, d⁻¹ * κ * d ∈ U) (N : ℕ)
    (hN : d ^ N ∈ U) (κ : G) (hκ : κ ∈ U) : (d * κ) ^ N ∈ U := by
  have key : ∀ m : ℕ, ∃ u ∈ U, (d * κ) ^ m = d ^ m * u := by
    intro m
    induction m with
    | zero => exact ⟨1, U.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨u, hu, he⟩ := ih
      refine ⟨d⁻¹ * u * d * κ, U.mul_mem (hd u hu) hκ, ?_⟩
      rw [pow_succ, pow_succ, he]
      simp [mul_assoc]
  obtain ⟨u, hu, he⟩ := key N
  rw [he]
  exact U.mul_mem hN hu

theorem is_diamond_pow (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : IsDia S v hv k δ) (j : ℕ) :
    IsDia S v hv (k ^ j) (δ ^ j) := by
  induction j with
  | zero => simpa using is_diamond_one' S v hv
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact is_diamond_mul_mult S v hv ih h

theorem zsmul_eq_of_dvd_sub_one {M : Type} [AddCommGroup M] (T : ℕ) (m : M) (hT : (T : ℤ) • m = 0) (k : ℤ)
    (hk : (T : ℤ) ∣ k - 1) : k • m = m := by
  obtain ⟨c, hc⟩ := hk
  have hk' : k = 1 + (T : ℤ) * c := by linarith
  rw [hk', add_smul, one_smul, mul_comm, mul_smul, hT, smul_zero, add_zero]

theorem level_functional_torsion (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (x) :
    (T : ℤ) • S.fT v hv x = 0 := by
  have h := S.fT_T v hv x
  rw [map_smul, Nat.cast_smul_eq_nsmul] at h
  rw [natCast_zsmul]
  exact h

theorem diamond_mem_level_of_congr_one (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : IsDia S v hv k δ) (hk : (T : ℤ) ∣ k - 1) : δ.1 ∈ S.U := by
  unfold IsDia at h
  obtain ⟨h0, hx, hg, hf⟩ := h
  rw [S.U_eq]
  refine ⟨δ.2, fun w => ?_⟩
  by_cases hw : w = v
  · rw [hw, S.UlocAlt v hv, Subgroup.mem_inf, mem_stabFun_lemma]
    refine ⟨hx, hg, fun y => ?_⟩
    rw [← hf y, zsmul_eq_of_dvd_sub_one T _ (level_functional_torsion S v hv _) k hk]
  · rw [h0 w hw]
    exact one_mem _

theorem multiplier_congr_one_of_mem (S : StepLevel F E σ J T f bad) (hT : T.Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : IsDia S v hv k δ)
    (hU : δ.1 ∈ S.U) : (T : ℤ) ∣ k - 1 := by
  unfold IsDia at h
  obtain ⟨-, -, hg, hf⟩ := h
  have hl := ((S.U_eq _).mp hU).2 v
  rw [S.UlocAlt v hv, Subgroup.mem_inf, mem_stabFun_lemma] at hl
  obtain ⟨-, hg', hf'⟩ := hl
  obtain ⟨y, hy⟩ : ∃ y, S.fT v hv y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact S.fT_ne v hv (LinearMap.ext fun z => by simpa using hcon z)
  have e1 := hf y
  rw [hf' y] at e1
  have e4 : (k - 1) • S.fT v hv y = 0 := by rw [sub_smul, one_smul, e1, sub_self]
  have hd : addOrderOf (S.fT v hv y) ∣ T := by
    have h5 := addOrderOf_dvd_natCard (S.fT v hv y)
    rwa [S.fM_card] at h5
  have hord : addOrderOf (S.fT v hv y) = T := by
    rcases (Nat.dvd_prime hT).mp hd with h1 | h1
    · have h7 := addOrderOf_nsmul_eq_zero (S.fT v hv y)
      rw [h1, one_nsmul] at h7
      exact absurd h7 hy
    · exact h1
  have h6 := (addOrderOf_dvd_iff_zsmul_eq_zero).mpr e4
  rwa [hord] at h6

def LocalDiamondCondition (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : ℤ)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Prop :=
  x ∈ levelVL σ J v S.Lb ∧ ∃ hg : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))),
    ∀ y : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      k • S.fT v hv ⟨(x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y.1, (hg y.1).1 y.2⟩ = S.fT v hv y

theorem is_diamond_local_cond (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : IsDia S v hv k δ) :
    LocalDiamondCondition S v hv k (bc (prV (E := E) v) δ.1) := by
  unfold IsDia at h
  exact h.2

theorem local_diamond_cond_one (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) :
    LocalDiamondCondition S v hv 1 1 := by
  unfold LocalDiamondCondition
  exact loc1_lemma_2 S v hv 1 rfl

theorem local_diamond_cond_mul (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k k' : ℤ} {x x' : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (h : LocalDiamondCondition S v hv k x) (h' : LocalDiamondCondition S v hv k' x') :
    LocalDiamondCondition S v hv (k * k') (x * x') := by
  unfold LocalDiamondCondition at h h' ⊢
  exact locmul_lemma_3 S v hv _ _ _ rfl h h'

theorem local_diamond_cond_pow (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (h : LocalDiamondCondition S v hv k x) (j : ℕ) :
    LocalDiamondCondition S v hv (k ^ j) (x ^ j) := by
  induction j with
  | zero => simpa using local_diamond_cond_one S v hv
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact local_diamond_cond_mul S v hv ih h

theorem local_diamond_conj_mem (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (h : LocalDiamondCondition S v hv k x) (y : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hy : y ∈ S.Uloc v) : x⁻¹ * y * x ∈ S.Uloc v := by
  unfold LocalDiamondCondition at h
  obtain ⟨hx, hg, hf⟩ := h
  exact conj_loc_lemma S v hv hx hg hf y hy

theorem local_diamond_mem_level (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : ℤ} {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (h : LocalDiamondCondition S v hv k x) (hk : (T : ℤ) ∣ k - 1) :
    x ∈ S.Uloc v := by
  unfold LocalDiamondCondition at h
  obtain ⟨hx, hg, hf⟩ := h
  rw [S.UlocAlt v hv, Subgroup.mem_inf, mem_stabFun_lemma]
  refine ⟨hx, hg, fun y => ?_⟩
  rw [← hf y, zsmul_eq_of_dvd_sub_one T _ (level_functional_torsion S v hv _) k hk]

theorem local_multiplier_congr_one (S : StepLevel F E σ J T f bad) (hT : T.Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : ℤ} {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (h : LocalDiamondCondition S v hv k x)
    (hU : x ∈ S.Uloc v) : (T : ℤ) ∣ k - 1 := by
  unfold LocalDiamondCondition at h
  obtain ⟨-, hg, hf⟩ := h
  rw [S.UlocAlt v hv, Subgroup.mem_inf, mem_stabFun_lemma] at hU
  obtain ⟨-, hg', hf'⟩ := hU
  obtain ⟨y, hy⟩ : ∃ y, S.fT v hv y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact S.fT_ne v hv (LinearMap.ext fun z => by simpa using hcon z)
  have e1 := hf y
  rw [hf' y] at e1
  have e4 : (k - 1) • S.fT v hv y = 0 := by rw [sub_smul, one_smul, e1, sub_self]
  have hd : addOrderOf (S.fT v hv y) ∣ T := by
    have h5 := addOrderOf_dvd_natCard (S.fT v hv y)
    rwa [S.fM_card] at h5
  have hord : addOrderOf (S.fT v hv y) = T := by
    rcases (Nat.dvd_prime hT).mp hd with h1 | h1
    · have h7 := addOrderOf_nsmul_eq_zero (S.fT v hv y)
      rw [h1, one_nsmul] at h7
      exact absurd h7 hy
    · exact h1
  have h6 := (addOrderOf_dvd_iff_zsmul_eq_zero).mpr e4
  rwa [hord] at h6

def MultiPlaceDiamond (S : StepLevel F E σ J T f bad) {P : Type} (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) (k : P → ℤ) (δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : Prop :=
  (∀ w, (∀ p, w ≠ pl p) → bc (prV (E := E) w) δ.1 = 1) ∧ ∀ p, LocalDiamondCondition S (pl p) (hpl p) (k p) (bc (prV (E := E) (pl p)) δ.1)

theorem multi_diamond_mul (S : StepLevel F E σ J T f bad) {P : Type} (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) {k k' : P → ℤ} {δ δ' : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : MultiPlaceDiamond S pl hpl k δ) (h' : MultiPlaceDiamond S pl hpl k' δ') : MultiPlaceDiamond S pl hpl (k * k') (δ * δ') := by
  unfold MultiPlaceDiamond at h h' ⊢
  refine ⟨fun w hw => ?_, fun p => ?_⟩
  · rw [Subgroup.coe_mul, map_mul, h.1 w hw, h'.1 w hw, one_mul]
  · rw [Subgroup.coe_mul, map_mul]
    exact local_diamond_cond_mul S (pl p) (hpl p) (h.2 p) (h'.2 p)

theorem multi_diamond_one (S : StepLevel F E σ J T f bad) {P : Type} (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) : MultiPlaceDiamond S pl hpl 1 1 := by
  unfold MultiPlaceDiamond
  refine ⟨fun w _ => by simp, fun p => ?_⟩
  simpa using local_diamond_cond_one S (pl p) (hpl p)

theorem multi_diamond_pow (S : StepLevel F E σ J T f bad) {P : Type} (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) {k : P → ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : MultiPlaceDiamond S pl hpl k δ) (j : ℕ) : MultiPlaceDiamond S pl hpl (k ^ j) (δ ^ j) := by
  induction j with
  | zero => simpa using multi_diamond_one S pl hpl
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact multi_diamond_mul S pl hpl ih h

theorem multi_diamond_of_is_diamond (S : StepLevel F E σ J T f bad) {P : Type} [DecidableEq P] (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) (hinj : Function.Injective pl) (p0 : P) {k : ℤ}
    {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : IsDia S (pl p0) (hpl p0) k δ) :
    MultiPlaceDiamond S pl hpl (Function.update 1 p0 k) δ := by
  have hloc := is_diamond_local_cond S (pl p0) (hpl p0) h
  unfold IsDia at h
  unfold MultiPlaceDiamond
  refine ⟨fun w hw => h.1 w (hw p0), fun p => ?_⟩
  by_cases hp : p = p0
  · subst hp
    simpa using hloc
  · rw [h.1 (pl p) (fun e => hp (hinj e))]
    simpa [Function.update_apply, hp] using local_diamond_cond_one S (pl p) (hpl p)

theorem multi_diamond_conj_mem (S : StepLevel F E σ J T f bad) {P : Type} (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) {k : P → ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : MultiPlaceDiamond S pl hpl k δ) (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hκ : κ ∈ S.U) :
    δ.1⁻¹ * κ * δ.1 ∈ S.U := by
  unfold MultiPlaceDiamond at h
  obtain ⟨h0, hl⟩ := h
  have hκ' := (S.U_eq κ).mp hκ
  rw [S.U_eq]
  refine ⟨mul_mem (mul_mem (inv_mem δ.2) hκ'.1) δ.2, fun w => ?_⟩
  rw [map_mul, map_mul, map_inv]
  by_cases hw : ∃ p, w = pl p
  · obtain ⟨p, rfl⟩ := hw
    exact local_diamond_conj_mem S (pl p) (hpl p) (hl p) _ (hκ'.2 (pl p))
  · push_neg at hw
    rw [h0 w hw, inv_one, one_mul, mul_one]
    exact hκ'.2 w

theorem multi_diamond_mem_level (S : StepLevel F E σ J T f bad) {P : Type} (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) {k : P → ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : MultiPlaceDiamond S pl hpl k δ) (hk : ∀ p, (T : ℤ) ∣ k p - 1) : δ.1 ∈ S.U := by
  unfold MultiPlaceDiamond at h
  obtain ⟨h0, hl⟩ := h
  rw [S.U_eq]
  refine ⟨δ.2, fun w => ?_⟩
  by_cases hw : ∃ p, w = pl p
  · obtain ⟨p, rfl⟩ := hw
    exact local_diamond_mem_level S (pl p) (hpl p) (hl p) (hk p)
  · push_neg at hw
    rw [h0 w hw]
    exact one_mem _

theorem multi_diamond_multiplier_congr (S : StepLevel F E σ J T f bad) (hT : T.Prime) {P : Type} (pl : P → HeightOneSpectrum (𝓞 F))
    (hpl : ∀ p, (T : 𝓞 F) ∈ (pl p).asIdeal) {k : P → ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : MultiPlaceDiamond S pl hpl k δ) (hU : δ.1 ∈ S.U) (p : P) : (T : ℤ) ∣ k p - 1 := by
  unfold MultiPlaceDiamond at h
  exact local_multiplier_congr_one S hT (pl p) (hpl p) (h.2 p) (((S.U_eq _).mp hU).2 (pl p))

theorem class_mul_right_of_normalises (S : StepLevel F E σ J T f bad) (y y' δ' δ : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hδ : ∀ κ ∈ S.U, δ.1⁻¹ * κ * δ.1 ∈ S.U)
    (h : (Quotient.mk'' y' : Cls S) = Quotient.mk'' (y * δ')) :
    (Quotient.mk'' (y' * δ) : Cls S) = Quotient.mk'' (y * δ' * δ) := by
  obtain ⟨g, hg, κ, hκ, he⟩ := (DoubleCoset.eq _ _ _ _).mp h
  apply (DoubleCoset.eq _ _ _ _).mpr
  refine ⟨g, hg, δ⁻¹ * κ * δ, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hκ ⊢
    simpa [mul_assoc] using hδ _ hκ
  · rw [he]
    simp [mul_assoc]

end Loc

variable {D : D7} {u : D.what₂.Word}

private theorem gres_lemma_4 (A : AtTTied u) (v : (D.mem u).A.vT) (j : Fin 2) :
    ((D.host.g j : ℕ) : (D.mem u).A.Fv v) ≠ 0 := by
  intro hg
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp A.piU_cong
  have h1 := congrArg (A.res v) hx
  rw [map_mul, map_sub, map_one, A.res_pi v, map_natCast] at h1
  have h01 : ((D.host.g 0 : ℕ) : (D.mem u).A.Fv v) * ((D.host.g 1 : ℕ) : (D.mem u).A.Fv v) = 0 := by
    rcases (show j = 0 ∨ j = 1 by fin_cases j <;> simp) with rfl | rfl
    · rw [hg, zero_mul]
    · rw [hg, mul_zero]
  have hc : ((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : (D.mem u).A.Fv v) = 0 := by
    push_cast
    rw [h01]
    simp
  rw [hc, mul_zero, zero_sub] at h1
  exact one_ne_zero (neg_eq_zero.mp h1.symm)

theorem level_prime_ne_type_prime' (A : AtTTied u) (j : Fin 2) : (D.mem u).A.T ≠ D.host.g j := by
  intro h
  have hpos : 0 < @Fintype.card _ (D.mem u).A.vTFin := by
    rw [(D.mem u).A.card_vT]
    show 0 < 2 * D.R.ord
    have h1 := D.R.m_le_f
    have h2 := D.R.two_le_m
    omega
  obtain ⟨v⟩ := (@Fintype.card_pos_iff _ (D.mem u).A.vTFin).mp hpos
  apply gres_lemma_4 A v j
  rw [← h]
  have h1 := (A.res_v v _).mp (A.eV v).2
  rw [map_natCast, map_natCast] at h1
  exact h1

theorem level_places_prime_to_type (A : AtTTied u) (v : (D.mem u).A.vT) : (A.eV v).1 ∉ badG D := by
  intro hb
  rcases hb with hb | hb
  · apply gres_lemma_4 A v 0
    have h1 := (A.res_v v _).mp hb
    rw [map_natCast, map_natCast] at h1
    exact h1
  · apply gres_lemma_4 A v 1
    have h1 := (A.res_v v _).mp hb
    rw [map_natCast, map_natCast] at h1
    exact h1

theorem rank_zero_le_type_level : D.R.N 0 ≤ aOf D.R 0 := by
  unfold aOf
  rw [if_pos (by have := D.R.two_le_m; omega)]
  simp [Ranks.N]

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

theorem fixed_class_mem_level (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (c : (D.mem u).C.cls 0)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hbad : ∀ w ∈ badG D, bc (prV (E := D.host.E) w) δ.1 = 1) (N0 : ℕ) (hN0 : 0 < N0)
    (hpow : ∀ κ ∈ (Tf.cls 0 (Nat.zero_le _)).lev.U, (δ.1 * κ) ^ N0 ∈ (Tf.cls 0 (Nat.zero_le _)).lev.U)
    (hfix : (Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _)).y c * δ) : Cls (Tf.cls 0 (Nat.zero_le _)).lev) =
      Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _)).y c)) :
    δ.1 ∈ (Tf.cls 0 (Nat.zero_le _)).lev.U := by
  exact fixed_class_mem_level_general (Tf.cls 0 (Nat.zero_le _)) Tf.gl (Tf.glev 0 (Nat.zero_le _)) rank_zero_le_type_level hS c δ hbad N0 hN0
    hpow hfix

theorem dilation_free_on_classes (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (v : (D.mem u).A.vT)
    (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ) (hk : (k : (D.mem u).A.Fv v) = a)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia (Tf.cls 0 (Nat.zero_le _)).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 k δ)
    (c : (D.mem u).C.cls 0) (hc : (D.fm u).dil 0 v a c = c) : a = 1 := by
  have hcls := (Tf.val 0 (Nat.zero_le _)).dil v a k hk c δ hδ
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
  have hpowU : δ.1 ^ ((D.mem u).A.T - 1) ∈ (Tf.cls 0 (Nat.zero_le _)).lev.U := by
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

theorem diamond_free_on_classes (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (k : (D.mem u).A.vT → ℤ)
    (hk0 : ∀ v, (k v : (D.mem u).A.Fv v) ≠ 0)
    (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : MultiPlaceDiamond (Tf.cls 0 (Nat.zero_le _)).lev (fun v => (Tf.atT.eV v).1) (fun v => (Tf.atT.eV v).2) k δ)
    (c : (D.mem u).C.cls 0)
    (hfix : (Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _)).y c * δ) : Cls (Tf.cls 0 (Nat.zero_le _)).lev) =
      Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _)).y c)) :
    ∀ v, (k v : (D.mem u).A.Fv v) = 1 := by
  have hTp : (D.mem u).A.T.Prime := (D.mem u).A.T_prime
  have hchar : ∀ v : (D.mem u).A.vT, ((D.mem u).A.T : (D.mem u).A.Fv v) = 0 := by
    intro v
    have h1 := (Tf.atT.res_v v _).mp (Tf.atT.eV v).2
    rw [map_natCast, map_natCast] at h1
    exact h1
  have hN0 : 0 < (D.mem u).A.T - 1 := by have := hTp.two_le; omega
  have hkpow : ∀ v, ((D.mem u).A.T : ℤ) ∣ k v ^ ((D.mem u).A.T - 1) - 1 := by
    intro v
    have hnd : ¬ ((D.mem u).A.T : ℤ) ∣ k v := by
      rintro ⟨m, hm⟩
      apply hk0 v
      rw [hm]
      push_cast
      rw [hchar v, zero_mul]
    have hcop : IsCoprime (k v) ((D.mem u).A.T : ℤ) :=
      ((Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hTp).irreducible).mpr hnd).symm
    exact (Int.ModEq.pow_card_sub_one_eq_one hTp hcop).symm.dvd
  have hall := multi_diamond_pow _ _ _ hδ ((D.mem u).A.T - 1)
  have hmem := multi_diamond_mem_level _ _ _ hall (fun v => hkpow v)
  have hN : δ.1 ^ ((D.mem u).A.T - 1) ∈ (Tf.cls 0 (Nat.zero_le _)).lev.U := by simpa using hmem
  have hbad : ∀ w ∈ badG D, bc (prV (E := D.host.E) w) δ.1 = 1 := by
    intro w hw
    have hδ1 := hδ
    unfold MultiPlaceDiamond at hδ1
    refine hδ1.1 w (fun v e => ?_)
    have e' : w = (Tf.atT.eV v).1 := e
    exact level_places_prime_to_type Tf.atT v (by rw [← e']; exact hw)
  have hU := fixed_class_mem_level Tf hS c δ hbad ((D.mem u).A.T - 1) hN0
    (fun κ hκ => pow_mul_mem_of_normalises _ δ.1 (fun κ' hκ' => multi_diamond_conj_mem _ _ _ hδ κ' hκ') _ hN κ hκ) hfix
  intro v
  obtain ⟨m, hm⟩ := multi_diamond_multiplier_congr _ hTp _ _ hδ hU v
  have hkv : k v = 1 + ((D.mem u).A.T : ℤ) * m := by linarith
  rw [hkv]
  push_cast
  rw [hchar v, zero_mul, add_zero]

theorem dilation_mul_of_diamonds (Tf : FormsTied D u) (v : (D.mem u).A.vT) (a b : ((D.mem u).A.Fv v)ˣ)
    (ka kb : ℤ) (hka : (ka : (D.mem u).A.Fv v) = a) (hkb : (kb : (D.mem u).A.Fv v) = b)
    (δa δb : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (ha : IsDia (Tf.cls 0 (Nat.zero_le _)).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 ka δa)
    (hb : IsDia (Tf.cls 0 (Nat.zero_le _)).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 kb δb) (c : (D.mem u).C.cls 0) :
    (D.fm u).dil 0 v a ((D.fm u).dil 0 v b c) = (D.fm u).dil 0 v (b * a) c := by
  rw [mul_comm b a, (D.fm u).dil_mul]

theorem dilation_commute_distinct (Tf : FormsTied D u) (v v' : (D.mem u).A.vT) (hvv : v ≠ v') (a : ((D.mem u).A.Fv v)ˣ)
    (b : ((D.mem u).A.Fv v')ˣ) (ka kb : ℤ) (hka : (ka : (D.mem u).A.Fv v) = a) (hkb : (kb : (D.mem u).A.Fv v') = b)
    (δa δb : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (ha : IsDia (Tf.cls 0 (Nat.zero_le _)).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 ka δa)
    (hb : IsDia (Tf.cls 0 (Nat.zero_le _)).lev (Tf.atT.eV v').1 (Tf.atT.eV v').2 kb δb) (c : (D.mem u).C.cls 0) :
    (D.fm u).dil 0 v a ((D.fm u).dil 0 v' b c) = (D.fm u).dil 0 v' b ((D.fm u).dil 0 v a c) := by
  have W := Tf.val 0 (Nat.zero_le _)
  have hne : (Tf.atT.eV v).1 ≠ (Tf.atT.eV v').1 := fun e => hvv (Tf.atT.eV.injective (Subtype.ext e))
  have h1 := class_mul_right_of_normalises _ _ _ _ δa (fun κ hκ => diamond_conj_mem_level' _ _ _ ha ⟨κ, hκ⟩) (W.dil v' b kb hkb c δb hb)
  have h2 := class_mul_right_of_normalises _ _ _ _ δb (fun κ hκ => diamond_conj_mem_level' _ _ _ hb ⟨κ, hκ⟩) (W.dil v a ka hka c δa ha)

  have hU : ((δb * δa)⁻¹ * (δa * δb)).1 ∈ (Tf.cls 0 (Nat.zero_le _)).lev.U := by
    rw [(Tf.cls 0 (Nat.zero_le _)).lev.U_eq]
    refine ⟨((δb * δa)⁻¹ * (δa * δb)).2, fun w => ?_⟩
    have hcomp : bc (prV (E := D.host.E) w) ((δb * δa)⁻¹ * (δa * δb)).1 = 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      by_cases hw : w = (Tf.atT.eV v).1
      · rw [hb.1 w (by rw [hw]; exact hne)]; group
      · rw [ha.1 w hw]; group
    rw [hcomp]
    exact (Subgroup.one_mem _)
  have hmid : (Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _)).y c * δb * δa) : Cls (Tf.cls 0 (Nat.zero_le _)).lev) =
      Quotient.mk'' ((Tf.cls 0 (Nat.zero_le _)).y c * δa * δb) :=
    (DoubleCoset.eq _ _ _ _).2 ⟨1, Subgroup.one_mem _, (δb * δa)⁻¹ * (δa * δb), hU, by group⟩
  exact (Tf.cls 0 (Nat.zero_le _)).y_bij.1 ((W.dil v a ka hka _ δa ha).trans (h1.trans (hmid.trans
    (h2.symm.trans (W.dil v' b kb hkb _ δb hb).symm))))

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
