import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdmissibleHarmonicLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNeZeroSmulMemOfMemSpan

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenusLatCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped Pointwise

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def toGen (Λ : Lat E n) : GenLat E n := ⟨Λ.L⟩

def IsLat (Λ : GenLat E n) : Prop := Λ.La.FG ∧ Submodule.span E (Λ.La : Set (Fin n → E)) = ⊤

def latEquiv : Lat E n ≃ {Λ : GenLat E n // IsLat Λ} where
  toFun Λ := ⟨toGen Λ, Λ.fg, Λ.span_top⟩
  invFun Λ := ⟨Λ.1.La, Λ.2.1, Λ.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem stdLat_eq : stdLat E n = stdMod E n := rfl

theorem toGen_std : toGen (Lat.std E n) = ⟨stdLat E n⟩ := rfl

theorem ln_eq (Λ : Lat E n) : (toGen Λ).Ln = Λ.inter := inf_comm _ _

theorem span_smul_eq (N : ℕ) : Ideal.span {(N : 𝓞 E)} • stdLat E n = mulStd E n N :=
  Submodule.ideal_span_singleton_smul _ _

theorem levOK_iff (Λ : Lat E n) (N M : ℕ) : (toGen Λ).LevOK N M ↔ Λ.Admissible M N := by
  rw [GenLat.LevOK, Lat.Admissible, span_smul_eq, ln_eq]

theorem mIdx_eq (Λ : Lat E n) (N r : ℕ) : (toGen Λ).mIdx N r = Λ.cardCenterZero r N := by
  rw [GenLat.mIdx, Lat.cardCenterZero, span_smul_eq, ln_eq]; rfl

theorem zCard_eq (Λ : Lat E n) (N r : ℕ) : (toGen Λ).zCard N r = Λ.cardZ r N := by
  rw [GenLat.zCard, Lat.cardZ, span_smul_eq]; rfl

omit [NumberField E] in
theorem span_smul_le_iff (k : ℕ) (A B : Submodule (𝓞 E) (Fin n → E)) :
    Ideal.span {(k : 𝓞 E)} • A ≤ B ↔ ∀ x ∈ A, k • x ∈ B := by
  rw [Submodule.smul_le]
  constructor
  · intro h x hx
    have := h k (Ideal.mem_span_singleton_self _) x hx
    rwa [Nat.cast_smul_eq_nsmul] at this
  · intro h r hr x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
    exact B.smul_mem _ (h x hx)

omit [NumberField E] in
theorem exists_uniform {p : ℕ} (hp : p.Prime) {A B : Submodule (𝓞 E) (Fin n → E)} (hA : A.FG)
    (h : ∀ x ∈ A, ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ B) : ∃ k : ℕ, ¬ p ∣ k ∧ ∀ x ∈ A, k • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! k hk using h
  refine ⟨∏ s ∈ S, k s, ?_, ?_⟩
  · rw [Prime.dvd_finset_prod_iff hp.prime]
    rintro ⟨s, hs, hd⟩
    exact (hk s (Submodule.subset_span hs)).1 hd
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem s hs =>
      rw [← Finset.prod_erase_mul S k hs, mul_smul]
      exact B.toAddSubmonoid.nsmul_mem (hk s (Submodule.subset_span hs)).2 _
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact B.smul_mem _ hx

theorem eqAtPrime_of_trivAt (Λ : GenLat E n) {s : ℕ} (h : Λ.TrivAt s) (p : ℕ) (hp : p.Prime) (hs : p ∣ s) :
    EqAtPrime p Λ.La (stdMod E n) := by
  obtain ⟨k, hk, h1, h2⟩ := h
  have hpk : ¬ p ∣ k := fun hd => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hk hd hs)
  rw [span_smul_le_iff] at h1 h2
  exact ⟨fun x hx => ⟨k, hpk, h1 x hx⟩, fun x hx => ⟨k, hpk, h2 x hx⟩⟩

theorem trivAt_iff (Λ : Lat E n) (s : ℕ) : (toGen Λ).TrivAt s ↔ Λ.StdAt s := by
  refine ⟨fun h p hp hs => eqAtPrime_of_trivAt _ h p hp hs, fun h => ?_⟩
  let J : Ideal ℤ :=
    { carrier := {k | (∀ x ∈ Λ.L, k • x ∈ stdMod E n) ∧ ∀ x ∈ stdMod E n, k • x ∈ Λ.L}
      add_mem' := fun {a b} ha hb =>
        ⟨fun x hx => by rw [add_smul]; exact add_mem (ha.1 x hx) (hb.1 x hx),
          fun x hx => by rw [add_smul]; exact add_mem (ha.2 x hx) (hb.2 x hx)⟩
      zero_mem' := ⟨fun x _ => by simp, fun x _ => by simp⟩
      smul_mem' := fun c a ha =>
        ⟨fun x hx => by rw [smul_eq_mul, mul_smul]; exact zsmul_mem (ha.1 x hx) c,
          fun x hx => by rw [smul_eq_mul, mul_smul]; exact zsmul_mem (ha.2 x hx) c⟩ }
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal J).principal
  have hdJ : ((d.natAbs : ℕ) : ℤ) ∈ J := by
    rw [hd]
    exact Ideal.mem_span_singleton.2 (Int.dvd_natAbs.2 dvd_rfl)
  refine ⟨d.natAbs, Nat.coprime_of_dvd fun p hp hpd hps => ?_, ?_, ?_⟩
  · obtain ⟨k₁, hk₁, h₁⟩ := exists_uniform hp Λ.fg (h p hp hps).1
    obtain ⟨k₂, hk₂, h₂⟩ := exists_uniform hp (Lat.std E n).fg (h p hp hps).2
    have hJ : ((k₁ * k₂ : ℕ) : ℤ) ∈ J :=
      ⟨fun x hx => by rw [natCast_zsmul, mul_comm, mul_smul]; exact nsmul_mem (h₁ x hx) _,
        fun x hx => by rw [natCast_zsmul, mul_smul]; exact nsmul_mem (h₂ x hx) _⟩
    rw [hd] at hJ
    have h3 : d.natAbs ∣ k₁ * k₂ := Int.natCast_dvd_natCast.1 (Int.natAbs_dvd.2 (Ideal.mem_span_singleton.1 hJ))
    exact (hp.dvd_mul.1 (hpd.trans h3)).elim hk₁ hk₂
  · rw [span_smul_le_iff]
    intro x hx
    have := hdJ.1 x hx
    rwa [natCast_zsmul] at this
  · rw [span_smul_le_iff]
    intro x hx
    have := hdJ.2 x hx
    rwa [natCast_zsmul] at this

theorem fg_of_smul_mem {A : Submodule (𝓞 E) (Fin n → E)} {o : 𝓞 E} (ho : o ≠ 0)
    (h : ∀ x ∈ A, o • x ∈ stdMod E n) : A.FG := by
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 E) (Fin n → E) o) := by
    intro x y hxy
    funext j
    have := congrFun hxy j
    simp only [LinearMap.lsmul_apply, Pi.smul_apply, Algebra.smul_def] at this
    exact mul_left_cancel₀ (by simpa using ho) this
  refine Submodule.fg_of_fg_map_injective _ hinj ?_
  haveI : IsNoetherian (𝓞 E) (stdMod E n) := isNoetherian_of_fg_of_noetherian _ (Lat.std E n).fg
  refine Submodule.FG.of_le_of_isNoetherian (T := stdMod E n) ?_
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

variable [IsCMField E]

theorem conj_mem_range (z : E) :
    IsCMField.complexConj E z ∈ (algebraMap (𝓞 E) E).range ↔ ∃ a : 𝓞 E, (a : E) = z := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨IsCMField.ringOfIntegersComplexConj E a, ?_⟩
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    change IsCMField.complexConj E (algebraMap (𝓞 E) E a) = z
    rw [ha, IsCMField.complexConj_apply_apply]
  · rintro ⟨a, rfl⟩
    exact ⟨IsCMField.ringOfIntegersComplexConj E a, IsCMField.coe_ringOfIntegersComplexConj E a⟩

theorem conj_stdForm (v w : Fin n → E) :
    ∑ j, IsCMField.complexConj E (v j) * w j = IsCMField.complexConj E (stdForm v w) := by
  simp [stdForm, map_sum]

theorem unimod_iff (Λ : Lat E n) : (toGen Λ).Unimod ↔ Λ.SelfDual := by
  simp only [GenLat.Unimod, Lat.SelfDual, conj_stdForm, conj_mem_range]
  rfl

theorem eq_zero_of_sum_conj (v : Fin n → E) (h : ∑ j, IsCMField.complexConj E (v j) * v j = 0) : v = 0 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := congrArg φ h
  simp only [map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_zero,
    Complex.conj_mul'] at h1
  have h2 : ∑ j, ‖φ (v j)‖ ^ 2 = 0 := by exact_mod_cast h1
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity] at h2
  funext j
  simpa using h2 j (Finset.mem_univ j)

omit [IsCMField E] in

private theorem exists_mul_mem_of_mem_span (A : Submodule (𝓞 E) (Fin n → E)) {x : Fin n → E}
    (hx : x ∈ Submodule.span E (A : Set (Fin n → E))) : ∃ o : 𝓞 E, o ≠ 0 ∧ o • x ∈ A := by
  first
  | exact @_root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span
  | exact _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span
  | (apply _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroSmulMemSpan.exists_ne_zero_smul_mem_of_mem_span ..)

private theorem span_eq_top_of_unimod (Λ : GenLat E n) (h : Λ.Unimod) :
    Submodule.span E (Λ.La : Set (Fin n → E)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let v : Fin n → E := fun j => IsCMField.complexConj E (f (Pi.single j 1))
  have hpair : ∀ w : Fin n → E, ∑ j, IsCMField.complexConj E (v j) * w j = f w := by
    intro w
    conv_rhs => rw [pi_eq_sum_univ' w, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    simp only [v, IsCMField.complexConj_apply_apply]
  have hkill : ∀ w ∈ Λ.La, f w = 0 := fun w hw => hf (Submodule.subset_span hw)
  have hv : v ∈ Λ.La := (h v).2 fun w hw => by
    rw [hpair, hkill w hw]
    exact zero_mem _
  have hv0 : v = 0 := eq_zero_of_sum_conj v (by rw [hpair, hkill v hv])
  refine hf0 (LinearMap.ext fun w => ?_)
  rw [← hpair, hv0]
  simp

theorem isLat_of_unimod (Λ : GenLat E n) (h : Λ.Unimod) : IsLat Λ := by
  classical
  have hspan := span_eq_top_of_unimod Λ h
  refine ⟨?_, hspan⟩
  choose o ho0 ho using fun j : Fin n =>
    exists_mul_mem_of_mem_span Λ.La (x := Pi.single j 1) (hspan ▸ Submodule.mem_top)
  have hd : ∀ j, (∏ i, o i) • (Pi.single j 1 : Fin n → E) ∈ Λ.La := fun j => by
    rw [← Finset.prod_erase_mul _ o (Finset.mem_univ j), mul_smul]
    exact Λ.La.smul_mem _ (ho j)
  have hd0 : ∏ i, o i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ho0 i
  refine fg_of_smul_mem (o := IsCMField.ringOfIntegersComplexConj E (∏ i, o i))
    ((map_ne_zero_iff _ (IsCMField.ringOfIntegersComplexConj E).injective).2 hd0) fun x hx => ?_
  refine mem_stdMod.2 fun j => ?_
  obtain ⟨a, ha⟩ := (h _).1 (hd j) x hx
  refine ⟨a, Eq.trans ha ?_⟩
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)]
  rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, Algebra.smul_def, mul_one]
  congr 1

def selfDualEquiv : {Λ : Lat E n // Λ.SelfDual} ≃ {Λ : GenLat E n // Λ.Unimod} where
  toFun Λ := ⟨toGen Λ.1, (unimod_iff Λ.1).2 Λ.2⟩
  invFun Λ := ⟨latEquiv.symm ⟨Λ.1, isLat_of_unimod Λ.1 Λ.2⟩, (unimod_iff _).1 Λ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Poly

variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

theorem symO_eq (Λ : Lat E n) : symO (Dw := Dw) c (toGen Λ) = (symLat Dw c Λ).toSubring := by
  rw [symLat, Algebra.adjoin_eq_ring_closure, symO]
  rfl

theorem harmL_eq (Λ : Lat E n) (a : (E →+* ℂ) × ℕ → ℕ) :
    harmL (Dw := Dw) c (toGen Λ) a = harmLat Dw c a Λ := by
  ext P
  simp only [harmL, harmLat, symO_eq, Set.mem_setOf_eq]
  rfl

end Poly

end GlobalTheory.GenusLatCompare
