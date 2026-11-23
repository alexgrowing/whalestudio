import Formalism.FormalGroupWitt.FormalGroupWittProofs.FunctionalEquationHomVector
import Formalism.FormalGroupWitt.FormalGroupWittProofs.EqSingleOfDegreeEqOne
import Formalism.FormalGroupWitt.FormalGroupWittProofs.ShiftFE
import Formalism.FormalGroupWitt.FormalGroupWittProofs.FrobSqV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.CongrV

noncomputable section

namespace Formalism.FG.HeightVAux

open MvPowerSeries Formalism.G Formalism.LT

section Rename

variable {K : Type*} [Field K] {l m : ℕ} [NeZero m]

theorem subst_shift_shiftLog (hl : 2 ≤ l) (j : ZMod m) :
    subst (fun k : ZMod m => (X (k - 1) : MvPowerSeries (ZMod m) K)) (shiftLog K l m j) =
      shiftLog K l m (j - 1) := by
  classical
  set e : ZMod m ↪ ZMod m := (Equiv.subRight (1 : ZMod m)).toEmbedding with he
  have hs : ∀ a : ZMod m, e a = a - 1 := fun a => by simp [he]
  have hX : (fun k : ZMod m => (X (k - 1) : MvPowerSeries (ZMod m) K)) = X ∘ ⇑e := by
    funext k; simp [hs]
  rw [hX, ← rename_eq_subst]
  ext n
  obtain ⟨x, rfl⟩ : ∃ x, Finsupp.embDomain e x = n :=
    ⟨n.comapDomain e e.injective.injOn, Finsupp.embDomain_comapDomain (by
      intro a _; exact ⟨a + 1, by simp [hs]⟩)⟩
  rw [coeff_embDomain_rename]
  by_cases hA : ∃ t : ℕ, x = Finsupp.single (j - (t : ZMod m)) ((l ^ 2) ^ t)
  · obtain ⟨t, rfl⟩ := hA
    rw [Finsupp.embDomain_single, hs, ShiftFEAux.coeff_shiftLog_single hl]
    have : j - (t : ZMod m) - 1 = j - 1 - (t : ZMod m) := by ring
    rw [this, ShiftFEAux.coeff_shiftLog_single hl]
  · push Not at hA
    rw [ShiftFEAux.coeff_shiftLog_zero j x hA, ShiftFEAux.coeff_shiftLog_zero]
    intro t ht
    apply hA t
    have : Finsupp.single (j - 1 - (t : ZMod m)) ((l ^ 2) ^ t) =
        Finsupp.embDomain e (Finsupp.single (j - (t : ZMod m)) ((l ^ 2) ^ t)) := by
      rw [Finsupp.embDomain_single, hs]; congr 1; ring
    rw [this] at ht
    exact Finsupp.embDomain_inj.mp ht

end Rename

section Subst

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] [DecidableEq ι] {τ : Type*}

theorem hasSubst0 {σ : Type*} [Finite σ] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, constantCoeff (a i) = 0) : HasSubst a :=
  hasSubst_of_constantCoeff_zero ha

theorem hasSubst_vX : HasSubst (fun i : ι => (vX i : MvPowerSeries (Fin 2 × ι) R)) :=
  hasSubst0 _ (fun _ => constantCoeff_X _)

theorem hasSubst_vY : HasSubst (fun i : ι => (vY i : MvPowerSeries (Fin 2 × ι) R)) :=
  hasSubst0 _ (fun _ => constantCoeff_X _)

theorem constantCoeff_atXv {g : MvPowerSeries ι R} (hg : constantCoeff g = 0) :
    constantCoeff (atXv g) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_vX (fun _ => constantCoeff_X _) hg

theorem constantCoeff_atYv {g : MvPowerSeries ι R} (hg : constantCoeff g = 0) :
    constantCoeff (atYv g) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_vY (fun _ => constantCoeff_X _) hg

theorem subst_atXv (G : Fin 2 × ι → MvPowerSeries τ R) (hG : HasSubst G)
    (g : MvPowerSeries ι R) : subst G (atXv g) = subst (fun i => G (0, i)) g := by
  unfold atXv
  rw [subst_comp_subst_apply hasSubst_vX hG]
  congr 1
  funext i
  exact subst_X hG _

theorem subst_atYv (G : Fin 2 × ι → MvPowerSeries τ R) (hG : HasSubst G)
    (g : MvPowerSeries ι R) : subst G (atYv g) = subst (fun i => G (1, i)) g := by
  unfold atYv
  rw [subst_comp_subst_apply hasSubst_vY hG]
  congr 1
  funext i
  exact subst_X hG _

theorem atXv_subst (h : ι → MvPowerSeries ι R) (hh : ∀ i, constantCoeff (h i) = 0)
    (g : MvPowerSeries ι R) : atXv (subst h g) = subst (fun i => atXv (h i)) g := by
  unfold atXv
  rw [subst_comp_subst_apply (hasSubst0 h hh) hasSubst_vX]

theorem atYv_subst (h : ι → MvPowerSeries ι R) (hh : ∀ i, constantCoeff (h i) = 0)
    (g : MvPowerSeries ι R) : atYv (subst h g) = subst (fun i => atYv (h i)) g := by
  unfold atYv
  rw [subst_comp_subst_apply (hasSubst0 h hh) hasSubst_vY]

theorem map_atXv {S : Type*} [CommRing S] (φ : R →+* S) (g : MvPowerSeries ι R) :
    map φ (atXv g) = atXv (map φ g) := by
  unfold atXv
  rw [map_subst hasSubst_vX]
  congr 1
  funext i
  exact map_X φ _

theorem map_atYv {S : Type*} [CommRing S] (φ : R →+* S) (g : MvPowerSeries ι R) :
    map φ (atYv g) = atYv (map φ g) := by
  unfold atYv
  rw [map_subst hasSubst_vY]
  congr 1
  funext i
  exact map_X φ _

end Subst

section Padic

variable {l : ℕ} [Fact l.Prime]

theorem coe_map_injective {σ : Type*} :
    Function.Injective (map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) :
      MvPowerSeries σ ℤ_[l] → MvPowerSeries σ ℚ_[l]) := by
  intro a b hab
  ext n
  have := congrArg (coeff n) hab
  rw [coeff_map, coeff_map] at this
  exact Subtype.ext this

theorem constantCoeff_of_map {σ : Type*} (x : MvPowerSeries σ ℤ_[l])
    (hx : constantCoeff (map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) x) = 0) :
    constantCoeff x = 0 := by
  rw [constantCoeff_map] at hx
  exact Subtype.ext hx

def liftZ {σ : Type*} (g : MvPowerSeries σ ℚ_[l]) (hg : IntegralMv g) : MvPowerSeries σ ℤ_[l] :=
  fun n => ⟨coeff n g, hg n⟩

theorem map_liftZ {σ : Type*} (g : MvPowerSeries σ ℚ_[l]) (hg : IntegralMv g) :
    map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (liftZ g hg) = g := by
  ext n
  rw [coeff_map]
  rfl

theorem dvd_of_norm_le {x : ℤ_[l]}
    (hx : ‖(PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) x‖ ≤ ‖((l : ℕ) : ℚ_[l])‖) :
    (l : ℤ_[l]) ∣ x :=
  (PadicInt.norm_lt_one_iff_dvd x).mp (lt_of_le_of_lt hx Padic.norm_p_lt_one)

theorem toZMod_eq_zero_iff (x : ℤ_[l]) : PadicInt.toZMod x = 0 ↔ (l : ℤ_[l]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

end Padic

section Main

open PadicInt in
theorem main (hC : Formalism.FG.FunEqCongrV.{0, 0, 0}) : Formalism.FG.ShiftHeight := by
  intro l _ m _ F hF
  have hlp : l.Prime := Fact.out
  have hl2 : 2 ≤ l := hlp.two_le
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hlp.ne_zero
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hlp.ne_zero
  obtain ⟨hf, hfeq⟩ := Formalism.FG.shift_functional_equation.{0} ℚ_[l] l hlp m (RingHom.id ℚ_[l])
  have hS := Formalism.FG.frobenius_lift_padic_square l
  have hM : IntegralMat (shiftMat ℚ_[l] m) := by
    intro j k; unfold shiftMat; split_ifs <;> simp
  have hXI : ∀ j : ZMod m, IntegralMv (X j : MvPowerSeries (ZMod m) ℚ_[l]) := by
    intro j d; rw [coeff_X]; split_ifs <;> simp
  have hfE : IsFunEqTypeV l (l ^ 2) hq (RingHom.id ℚ_[l]) (shiftMat ℚ_[l] m)
      (shiftLog ℚ_[l] l m) := by
    intro j; rw [hfeq j]; exact hXI j

  have hsum : ∀ j : ZMod m, ∑ k, shiftMat ℚ_[l] m j k •
        MvPowerSeries.expand (l ^ 2) hq
          (MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k)) =
      MvPowerSeries.expand (l ^ 2) hq (shiftLog ℚ_[l] l m (j - 1)) := by
    intro j
    simp [shiftMat]
  have hexp : ∀ j : ZMod m, MvPowerSeries.expand (l ^ 2) hq (shiftLog ℚ_[l] l m (j - 1)) =
      (l : ℚ_[l]) • (shiftLog ℚ_[l] l m j - X j) := by
    intro j
    have h1 := hfeq j
    rw [hsum j] at h1
    rw [← h1, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hl0, one_smul]

  have hgE : IsFunEqTypeV l (l ^ 2) hq (RingHom.id ℚ_[l]) (shiftMat ℚ_[l] m)
      (fun j => (l : ℚ_[l]) • shiftLog ℚ_[l] l m j) := by
    intro j
    have : (l : ℚ_[l]) • shiftLog ℚ_[l] l m j - ((l : ℕ) : ℚ_[l])⁻¹ • ∑ k, shiftMat ℚ_[l] m j k •
        MvPowerSeries.expand (l ^ 2) hq
          (MvPowerSeries.map (RingHom.id ℚ_[l]) ((l : ℚ_[l]) • shiftLog ℚ_[l] l m k)) =
        (l : ℚ_[l]) • (X j : MvPowerSeries (ZMod m) ℚ_[l]) := by
      have h2 : ∀ k, MvPowerSeries.map (RingHom.id ℚ_[l]) ((l : ℚ_[l]) • shiftLog ℚ_[l] l m k) =
          (l : ℚ_[l]) • MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k) := by
        intro k; simp
      have h3 : ∑ k, shiftMat ℚ_[l] m j k • (l : ℚ_[l]) • MvPowerSeries.expand (l ^ 2) hq
            (MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k)) =
          (l : ℚ_[l]) • ∑ k, shiftMat ℚ_[l] m j k • MvPowerSeries.expand (l ^ 2) hq
            (MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k)) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
      simp only [h2, map_smul]
      rw [h3, hsum j, hexp j]
      rw [smul_smul ((l : ℚ_[l])⁻¹), inv_mul_cancel₀ hl0, one_smul, ← smul_sub, sub_sub_cancel]
    rw [this]
    intro d
    rw [coeff_smul, norm_mul]
    exact mul_le_one₀ Padic.norm_p_lt_one.le (norm_nonneg _) (hXI j d)
  have hg0 : ∀ j : ZMod m, constantCoeff ((l : ℚ_[l]) • shiftLog ℚ_[l] l m j) = 0 := by
    intro j
    rw [smul_eq_C_mul, map_mul, hf.1 j, mul_zero]
  obtain ⟨h, hh0, hhI, hh⟩ := Formalism.FG.functional_equation_hom_vector.{0, 0, 0} ℚ_[l] l (l ^ 2) hq
    (RingHom.id ℚ_[l]) hS (ZMod m) (shiftMat ℚ_[l] m) hM (shiftLog ℚ_[l] l m) hf hfE (ZMod m)
    (fun j => (l : ℚ_[l]) • shiftLog ℚ_[l] l m j) hg0 hgE
  set e : ZMod m → MvPowerSeries (ZMod m) ℤ_[l] := fun i => liftZ (h i) (hhI i) with he_def
  have he : ∀ i, map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (e i) = h i :=
    fun i => map_liftZ (h i) (hhI i)
  have he0 : ∀ i, constantCoeff (e i) = 0 :=
    fun i => constantCoeff_of_map _ (by rw [he i]; exact hh0 i)
  have hF0 : ∀ i, constantCoeff (F i) = 0 := fun i => constantCoeff_of_map _ (hF.1 i)

  set FK : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℚ_[l] :=
    fun i => map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (F i) with hFK
  set EK : Fin 2 × ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℚ_[l] :=
    fun x => if x.1 = 0 then atXv (h x.2) else atYv (h x.2) with hEK
  have hFKs : HasSubst FK := hasSubst0 FK hF.1
  have hhs : HasSubst h := hasSubst0 h hh0
  have hEK0 : ∀ x, constantCoeff (EK x) = 0 := by
    intro x
    simp only [hEK]
    split_ifs
    · exact constantCoeff_atXv (hh0 _)
    · exact constantCoeff_atYv (hh0 _)
  have hEKs : HasSubst EK := hasSubst0 EK hEK0

  have hkey : (fun i => subst FK (h i)) = (fun i => subst EK (FK i)) := by
    refine Formalism.FG.subst_injective_vector.{0, 0, 0} ℚ_[l] (ZMod m) (Fin 2 × ZMod m)
      (shiftLog ℚ_[l] l m) _ _ hf
      (fun i => constantCoeff_subst_eq_zero hFKs hF.1 (hh0 i))
      (fun i => constantCoeff_subst_eq_zero hEKs hEK0 (hF.1 i)) (fun j => ?_)
    rw [← subst_comp_subst_apply hhs hFKs, hh j, subst_smul hFKs, hF.2.2 j,
      ← subst_comp_subst_apply hFKs hEKs, hF.2.2 j, subst_add hEKs,
      subst_atXv EK hEKs, subst_atYv EK hEKs]
    have hx : (fun i => EK (0, i)) = fun i => atXv (h i) := by
      funext i; simp [hEK]
    have hy : (fun i => EK (1, i)) = fun i => atYv (h i) := by
      funext i; simp [hEK]
    rw [hx, hy, ← atXv_subst h hh0, ← atYv_subst h hh0, hh j, smul_add]
    unfold atXv atYv
    rw [subst_smul hasSubst_vX, subst_smul hasSubst_vY]
  have hFs : HasSubst F := hasSubst0 F hF0
  have hE0 : ∀ x : Fin 2 × ZMod m, constantCoeff
      ((fun x : Fin 2 × ZMod m => if x.1 = 0 then atXv (e x.2) else atYv (e x.2)) x) = 0 := by
    intro x
    simp only
    split_ifs
    · exact constantCoeff_atXv (he0 _)
    · exact constantCoeff_atYv (he0 _)
  have hHom : IsHomV F F e := by
    refine ⟨he0, fun i => ?_⟩
    apply coe_map_injective
    rw [map_subst hFs, map_subst (hasSubst0 _ hE0), he i]
    have := congrFun hkey i
    rw [this]
    congr 1
    funext x
    simp only [hEK]
    split_ifs
    · rw [map_atXv, he]
    · rw [map_atYv, he]
  have hfe : (fun k => map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (e k)) = h := funext he

  set β : ZMod m → MvPowerSeries (ZMod m) ℚ_[l] := fun k => X (k - 1) ^ (l ^ 2) with hβ
  have hβ0 : ∀ k, constantCoeff (β k) = 0 := by
    intro k; simp [hβ, hlp.ne_zero]
  have hβI : ∀ k, IntegralMv (β k) := by
    intro k d; simp only [hβ]; rw [coeff_X_pow]; split_ifs <;> simp
  have hρs : HasSubst (fun k : ZMod m => (X (k - 1) : MvPowerSeries (ZMod m) ℚ_[l])) :=
    hasSubst0 _ (fun _ => constantCoeff_X _)
  have hβf : ∀ j, subst β (shiftLog ℚ_[l] l m j) =
      MvPowerSeries.expand (l ^ 2) hq (shiftLog ℚ_[l] l m (j - 1)) := by
    intro j
    have : β = fun k => MvPowerSeries.expand (l ^ 2) hq (X (k - 1)) := by
      funext k; simp [hβ]
    rw [this, ← expand_subst _ _ hρs, subst_shift_shiftLog hl2]
  have hdiv := (hC ℚ_[l] l (l ^ 2) hq (RingHom.id _) hS (ZMod m) (shiftMat ℚ_[l] m) hM
    (shiftLog ℚ_[l] l m) hf hfE (ZMod m) h β hh0 hβ0 hhI hβI 1 le_rfl).mpr (by
      intro j d
      rw [hh j, hβf j, hexp j, ← smul_sub, sub_sub_cancel, pow_one, coeff_smul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hXI j d))
  have hcongr : ∀ j n, (l : ℤ_[l]) ∣ coeff n (e j - X (j - 1) ^ (l ^ 2)) := by
    intro j n
    apply dvd_of_norm_le
    have hmap : h j - β j =
        map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (e j - X (j - 1) ^ (l ^ 2)) := by
      rw [map_sub, map_pow, map_X, he j]
    have := hdiv j n
    rw [hmap, coeff_map, pow_one] at this
    exact this

  have hred : ∀ j, map (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (e j) = X (j - 1) ^ (l ^ 2) := by
    intro j
    have h0 : map (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (e j - X (j - 1) ^ (l ^ 2)) = 0 := by
      ext n
      rw [coeff_map, map_zero, toZMod_eq_zero_iff]
      exact hcongr j n
    rwa [map_sub, map_pow, map_X, sub_eq_zero] at h0
  have hit : ∀ n : ℕ, (∀ i, constantCoeff (iterV e n i) = 0) ∧
      ∀ i, map (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (iterV e n i) =
        X (i - (n : ZMod m)) ^ ((l ^ 2) ^ n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simp [iterV]
      · simp [iterV, map_X]
    | succ n ih =>
      have hsucc : ∀ i, iterV e (n + 1) i = subst (iterV e n) (e i) := by
        intro i
        simp only [iterV]
        rw [Function.iterate_succ_apply']
      have hs1 : HasSubst (iterV e n) := hasSubst0 _ ih.1
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rw [hsucc]
        exact constantCoeff_subst_eq_zero hs1 ih.1 (he0 i)
      · rw [hsucc, map_subst hs1, hred i, subst_pow (hs1.map _), subst_X (hs1.map _), ih.2,
          ← pow_mul, ← pow_succ]
        congr 2
        push_cast
        ring
  refine ⟨e, hHom, fun j => by rw [hfe]; exact hh j, hcongr, fun j n => ?_⟩
  rw [← toZMod_eq_zero_iff, ← coeff_map, map_sub, (hit m).2 j, ZMod.natCast_self, sub_zero,
    ← pow_mul, map_pow, map_X, sub_self, map_zero]

end Main

end Formalism.FG.HeightVAux

namespace Formalism.FG

end Formalism.FG
