import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.CharacterFiniteLevelZeroOfForms

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem is_diamond_one (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) : IsDia S v hv 1 1 := by
  refine ⟨fun v' _ => ?_, ?_, ?_⟩
  · simp
  · simp only [OneMemClass.coe_one, map_one]; exact (levelVL σ J v S.Lb).one_mem
  · refine ⟨by simp only [OneMemClass.coe_one, map_one]; exact (stabGL _).one_mem, fun x => ?_⟩
    rw [one_smul]
    congr 1
    apply Subtype.ext
    simp

theorem is_diamond_mul (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
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

theorem diamond_conj_mem_level (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
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

theorem level_character_conj_diamond (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (hb : v ∉ bad) {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : IsDia S v hv k δ) (κ : S.U) :
    S.chi ⟨δ.1⁻¹ * κ.1 * δ.1, diamond_conj_mem_level S v hv h κ⟩ = S.chi κ := by
  have h1 := h.1
  have key : S.chi (κ⁻¹ * ⟨δ.1⁻¹ * κ.1 * δ.1, diamond_conj_mem_level S v hv h κ⟩) = 1 := by
    apply S.chi_triv
    intro v'' hv''
    have hne : v'' ≠ v := fun e => hb (e ▸ hv'')
    simp [Subgroup.coe_mul, map_mul, map_inv, h1 v'' hne]
  rw [map_mul, map_inv, inv_mul_eq_one] at key
  exact key.symm

theorem adelic_function_right_translate_diamond {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (hb : v ∉ bad) {k : ℤ}
    {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : IsDia S v hv k δ)
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdFun S emb) :
    (fun x => g (x * δ)) ∈ AdFun S emb := by
  intro γ hγ x x' κ hx y y' hy
  have e : (x' * δ).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (x * δ).1 *
      (⟨δ.1⁻¹ * κ.1 * δ.1, diamond_conj_mem_level S v hv h κ⟩ : S.U).1 := by
    simp only [Subgroup.coe_mul, hx]
    group
  have := hg γ hγ (x * δ) (x' * δ) ⟨δ.1⁻¹ * κ.1 * δ.1, diamond_conj_mem_level S v hv h κ⟩ e y y' hy
  rw [level_character_conj_diamond S v hv hb h κ] at this
  exact this

end Gen

variable {D : D7} {u : D.what₂.Word}

def DiamondElementsExist (Tf : Forms0 D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) (h0 : i = 0) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ), ∃ k : ℤ, (k : (D.mem u).A.Fv v) = a ∧
    ∃ δ, IsDia (Tf.cls i hi h0).lev (Tf.atT.eV v).1 (Tf.atT.eV v).2 k δ

def DiaMul0 (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ i, i ≤ D.R.m → i = 0 → ∀ v, ∀ φ ∈ (D.fm u).Fi i,
    Formalism.MainNotions.product_first_zeroth_parts.dia D u i v 1 φ = φ ∧ ∀ a b, Formalism.MainNotions.product_first_zeroth_parts.dia D u i v (a * b) φ = Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b φ)

theorem diamond_mul_of_elements_prime_to_bad (Tf : Forms0 D u) (hE : DiamondElementsExist Tf) (hb : ∀ v, (Tf.atT.eV v).1 ∉ badG D) :
    DiaMul0 D u := by
  intro i hi h0 v φ hφ
  obtain ⟨g, hg, hgφ⟩ := ((Tf.val i hi h0).Fi φ).1 hφ
  have hval : ∀ c, φ c = fun z => g ((Tf.cls i hi h0).y c) ((Tf.val i hi h0).eY z) := by
    intro c; funext z
    have := congrFun (congrFun hgφ c) ((Tf.val i hi h0).eY z)
    simp only [Equiv.symm_apply_apply] at this
    exact this.symm
  have hgA : g ∈ AdFun (Tf.cls i hi h0).lev (embT D) := (Submodule.mem_inf.1 hg).1
  have hdia : ∀ a c, Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ c = (D.fm u).dilT i v a c (φ ((D.fm u).dil i v a c)) :=
    fun a c => rfl
  refine ⟨?_, fun a b => ?_⟩
  · funext c
    rw [hdia, hval ((D.fm u).dil i v 1 c),
      (Tf.val i hi h0).dilT v 1 1 (by simp) c 1 (is_diamond_one _ _ _) g hgA, mul_one, hval c]
  · funext c
    obtain ⟨ka, hka, δa, hδa⟩ := hE i hi h0 v a
    obtain ⟨kb, hkb, δb, hδb⟩ := hE i hi h0 v b
    have hab : ((ka * kb : ℤ) : (D.mem u).A.Fv v) = ((a * b : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) := by
      rw [Int.cast_mul, hka, hkb, Units.val_mul]
    have h1 : Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b φ ((D.fm u).dil i v a c) =
        fun z => g ((Tf.cls i hi h0).y ((D.fm u).dil i v a c) * δb) ((Tf.val i hi h0).eY z) := by
      rw [hdia, hval, (Tf.val i hi h0).dilT v b kb hkb _ δb hδb g hgA]
    have hg' := adelic_function_right_translate_diamond (Tf.cls i hi h0).lev (embT D) _ _ (hb v) hδb hgA
    have h2 := (Tf.val i hi h0).dilT v a ka hka c δa hδa _ hg'
    rw [hdia (a * b) c, hval ((D.fm u).dil i v (a * b) c),
      (Tf.val i hi h0).dilT v (a * b) (ka * kb) hab c (δa * δb) (is_diamond_mul _ _ _ hδa hδb) g hgA,
]
    show _ = (D.fm u).dilT i v a c (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b φ ((D.fm u).dil i v a c))
    rw [h1, h2]
    funext z
    simp only [mul_assoc]

theorem level_prime_ne_type_prime (A : AtTTied u) (j : Fin 2) : (D.mem u).A.T ≠ D.host.g j := by
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

theorem level_places_not_bad (A : AtTTied u) (v : (D.mem u).A.vT) : (A.eV v).1 ∉ badG D := by
  have hT := (A.eV v).2
  have hTp := (D.mem u).A.T_prime
  have key : ∀ j : Fin 2, (D.host.g j : 𝓞 D.host.F) ∉ (A.eV v).1.asIdeal := by
    intro j hj
    have hcop : Nat.Coprime (D.mem u).A.T (D.host.g j) :=
      (Nat.coprime_primes hTp (D.host.g_prime j)).2 (level_prime_ne_type_prime A j)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : ((a * (D.mem u).A.T + b * D.host.g j : ℤ) : 𝓞 D.host.F) ∈ (A.eV v).1.asIdeal := by
      push_cast
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hT) (Ideal.mul_mem_left _ _ hj)
    rw [hab, Int.cast_one] at h1
    exact (A.eV v).1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  rintro (h | h)
  · exact key 0 h
  · exact key 1 h

theorem diamond_mul_of_diamond_elements (Tf : Forms0 D u) (hE : DiamondElementsExist Tf) : DiaMul0 D u :=
  diamond_mul_of_elements_prime_to_bad Tf hE (level_places_not_bad Tf.atT)

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
