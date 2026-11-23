import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSubstitutionIntegral.IntegralSubst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditiveCubes.ConstantCoeffLogEqZero

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.PhGram

open PI.FglGram

variable {p : ℕ} [Fact p.Prime]

section Exact

variable {σ τ : Type*}

private theorem hasSubst_of_constantCoeff_eq_zero_gram_substitution_integral {κ ι : Type*} [Finite ι] {a : ι → MvPowerSeries κ ℂ_[p]}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) : MvPowerSeries.HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [ha i]; exact IsNilpotent.zero)
  | exact ⟨fun i => by rw [ha i]; exact IsNilpotent.zero, by rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩

theorem subst_psubst {s : τ → MvPowerSeries σ ℂ_[p]} (hs : MvPowerSeries.HasSubst s)
    {a : MvPowerSeries τ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst s (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst s a) f := by
  have haS : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    hasSubst_of_constantCoeff_eq_zero_gram_substitution_integral (fun _ => ha)
  unfold PowerSeries.subst
  exact MvPowerSeries.subst_comp_subst_apply haS hs f

private theorem cc_subst_lemma {κ : Type*} {a : MvPowerSeries κ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [map_pow, ha, zero_pow hd]

theorem cc_psubst {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0)
    {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := (cc_subst_lemma ha f).trans hf

variable {l ex ph : PowerSeries ℂ_[p]}

theorem cc_l (hD : Data l ex ph) : PowerSeries.constantCoeff l = 0 := by
  have h := cc_subst_lemma (κ := Unit) (a := ex) hD.1 l
  rw [hD.2.1] at h
  exact h.symm.trans PowerSeries.constantCoeff_X

theorem cc_lg (hD : Data l ex ph) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (lg l a) = 0 := (cc_subst_lemma ha l).trans (cc_l hD)

theorem cc_pt (hD : Data l ex ph) {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.constantCoeff (pt ex x) = 0 := (cc_subst_lemma hx ex).trans hD.1

theorem cc_phAt (hD : Data l ex ph) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (phAt ph a) = 0 := (cc_subst_lemma ha ph).trans hD.2.2

private theorem inv_lemma_2 {κ : Type*} {l ex : PowerSeries ℂ_[p]}
    (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {u : MvPowerSeries κ ℂ_[p]} (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst (PowerSeries.subst u ex) l = u := by
  have hexS : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have huS : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [← PowerSeries.subst_comp_subst_apply hexS huS, hl, PowerSeries.subst_X huS]

theorem lg_pt (hD : Data l ex ph) {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) :
    lg l (pt ex x) = x := inv_lemma_2 hD.1 hD.2.1 hx

theorem cc_add (hD : Data l ex ph) {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : MvPowerSeries.constantCoeff (add l ex a b) = 0 := by
  show MvPowerSeries.constantCoeff (pt ex (lg l a + lg l b)) = 0
  exact cc_pt hD (by rw [map_add, cc_lg hD ha, cc_lg hD hb, add_zero])

theorem cc_mulBy (hD : Data l ex ph) (c : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) : MvPowerSeries.constantCoeff (mulBy l ex c a) = 0 := by
  show MvPowerSeries.constantCoeff (pt ex (MvPowerSeries.C c * lg l a)) = 0
  exact cc_pt hD (by rw [map_mul, cc_lg hD ha, mul_zero])

theorem mulBy_mulBy (hD : Data l ex ph) (c d : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    mulBy l ex d (mulBy l ex c a) = mulBy l ex (d * c) a := by
  show pt ex (MvPowerSeries.C d * lg l (pt ex (MvPowerSeries.C c * lg l a))) =
    pt ex (MvPowerSeries.C (d * c) * lg l a)
  rw [lg_pt hD (by rw [map_mul, cc_lg hD ha, mul_zero]), ← mul_assoc, map_mul]

variable {s : τ → MvPowerSeries σ ℂ_[p]}

theorem subst_lg (hD : Data l ex ph) (hs : MvPowerSeries.HasSubst s) {a : MvPowerSeries τ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) : MvPowerSeries.subst s (lg l a) = lg l (MvPowerSeries.subst s a) := subst_psubst hs ha l

theorem subst_pt (hs : MvPowerSeries.HasSubst s) {x : MvPowerSeries τ ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) : MvPowerSeries.subst s (pt ex x) = pt ex (MvPowerSeries.subst s x) := subst_psubst hs hx ex

theorem subst_phAt (hs : MvPowerSeries.HasSubst s) {a : MvPowerSeries τ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst s (phAt ph a) = phAt ph (MvPowerSeries.subst s a) := subst_psubst hs ha ph

private theorem subst_add_gram_substitution_integral (hs : MvPowerSeries.HasSubst s) (f g : MvPowerSeries τ ℂ_[p]) :
    MvPowerSeries.subst s (f + g) = MvPowerSeries.subst s f + MvPowerSeries.subst s g := by
  rw [← MvPowerSeries.coe_substAlgHom hs, map_add]

theorem subst_add' (hD : Data l ex ph) (hs : MvPowerSeries.HasSubst s) {a b : MvPowerSeries τ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst s (add l ex a b) = add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
  have hab : MvPowerSeries.constantCoeff (lg l a + lg l b) = 0 := by
    rw [map_add, cc_lg hD ha, cc_lg hD hb, add_zero]
  show MvPowerSeries.subst s (pt ex (lg l a + lg l b)) =
    pt ex (lg l (MvPowerSeries.subst s a) + lg l (MvPowerSeries.subst s b))
  rw [subst_pt hs hab, subst_add_gram_substitution_integral hs, subst_lg hD hs ha, subst_lg hD hs hb]

private theorem subst_C_mul_gram_substitution_integral (hs : MvPowerSeries.HasSubst s) (c : ℂ_[p])
    (f : MvPowerSeries τ ℂ_[p]) :
    MvPowerSeries.subst s (MvPowerSeries.C c * f) = MvPowerSeries.C c * MvPowerSeries.subst s f := by
  rw [← MvPowerSeries.coe_substAlgHom hs, map_mul]
  congr 1
  exact (MvPowerSeries.substAlgHom hs).commutes c

theorem subst_mulBy (hD : Data l ex ph) (hs : MvPowerSeries.HasSubst s) (c : ℂ_[p]) {a : MvPowerSeries τ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst s (mulBy l ex c a) = mulBy l ex c (MvPowerSeries.subst s a) := by
  show MvPowerSeries.subst s (pt ex (MvPowerSeries.C c * lg l a)) =
    pt ex (MvPowerSeries.C c * lg l (MvPowerSeries.subst s a))
  rw [subst_pt hs (by rw [map_mul, cc_lg hD ha, mul_zero]), subst_C_mul_gram_substitution_integral hs, subst_lg hD hs ha]

private theorem subst_sub_gram_substitution_integral (hs : MvPowerSeries.HasSubst s) (f g : MvPowerSeries τ ℂ_[p]) :
    MvPowerSeries.subst s (f - g) = MvPowerSeries.subst s f - MvPowerSeries.subst s g := by
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sub]

theorem subst_be (hD : Data l ex ph) (hs : MvPowerSeries.HasSubst s) {a b : MvPowerSeries τ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst s (be l ex ph a b) = be l ex ph (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
  show MvPowerSeries.subst s (phAt ph (add l ex a b) - phAt ph a - phAt ph b) =
    phAt ph (add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b)) -
      phAt ph (MvPowerSeries.subst s a) - phAt ph (MvPowerSeries.subst s b)
  rw [subst_sub_gram_substitution_integral hs, subst_sub_gram_substitution_integral hs, subst_phAt hs (cc_add hD ha hb), subst_phAt hs ha,
    subst_phAt hs hb, subst_add' hD hs ha hb]

end Exact

theorem cc_X {σ : Type*} (i : σ) : MvPowerSeries.constantCoeff (Xv (p := p) i) = 0 := by
  first
  | exact MvPowerSeries.constantCoeff_X i
  | simp

theorem hasSubst_good {σ τ : Type*} [Finite τ] {s : τ → MvPowerSeries σ ℂ_[p]} (hs : ∀ i, Good (s i)) :
    MvPowerSeries.HasSubst s := hasSubst_of_constantCoeff_eq_zero_gram_substitution_integral (fun i => (hs i).1)

theorem goodAdd : GoodAdd := by
  intro p _ l ex ph S H σ a b ha hb
  have hsG : ∀ i, Good (![a, b] i) := by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
  have hs := hasSubst_good hsG
  have hI := integral_subst' ![a, b] hsG H.intAdd
  rw [subst_add' H.data hs (cc_X 0) (cc_X 1)] at hI
  have e0 : MvPowerSeries.subst ![a, b] (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = a :=
    MvPowerSeries.subst_X hs 0
  have e1 : MvPowerSeries.subst ![a, b] (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = b :=
    MvPowerSeries.subst_X hs 1
  rw [e0, e1] at hI
  exact ⟨cc_add H.data ha.1 hb.1, hI⟩

theorem goodMul : GoodMul := by
  intro p _ l ex ph S H σ α hα a ha
  have hsG : ∀ i : Unit, Good ((fun _ : Unit => a) i) := fun _ => ha
  have hs := hasSubst_good hsG
  have hI := integral_subst' (fun _ : Unit => a) hsG (H.intMul α hα)
  rw [subst_mulBy H.data hs α.1 (cc_X ())] at hI
  have e : MvPowerSeries.subst (fun _ : Unit => a) (Xv () : MvPowerSeries Unit ℂ_[p]) = a :=
    MvPowerSeries.subst_X hs ()
  rw [e] at hI
  exact ⟨cc_mulBy H.data α.1 ha.1, hI⟩

theorem biaddSub : BiaddSub := by
  intro p _ l ex ph S H σ a b c ha hb hc
  have hsG : ∀ i, Good (![a, b, c] i) := by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
    · simpa using hc
  have hs := hasSubst_good hsG
  have h := sSubst ![a, b, c] hsG H.biadd
  have e0 : MvPowerSeries.subst ![a, b, c] (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) = a :=
    MvPowerSeries.subst_X hs 0
  have e1 : MvPowerSeries.subst ![a, b, c] (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) = b :=
    MvPowerSeries.subst_X hs 1
  have e2 : MvPowerSeries.subst ![a, b, c] (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) = c :=
    MvPowerSeries.subst_X hs 2
  rw [subst_be H.data hs (cc_add H.data (cc_X 0) (cc_X 1)) (cc_X 2),
    subst_add' H.data hs (cc_X 0) (cc_X 1), subst_add_gram_substitution_integral hs,
    subst_be H.data hs (cc_X 0) (cc_X 2), subst_be H.data hs (cc_X 1) (cc_X 2), e0, e1, e2] at h
  exact h

theorem normSub : NormSub := by
  intro p _ l ex ph S H σ α hα a ha
  have hsG : ∀ i : Unit, Good ((fun _ : Unit => a) i) := fun _ => ha
  have hs := hasSubst_good hsG
  have h := sSubst (fun _ : Unit => a) hsG (H.norm α hα)
  have e : MvPowerSeries.subst (fun _ : Unit => a) (Xv () : MvPowerSeries Unit ℂ_[p]) = a :=
    MvPowerSeries.subst_X hs ()
  rw [subst_phAt hs (cc_mulBy H.data α.1 (cc_X ())), subst_mulBy H.data hs α.1 (cc_X ()),
    subst_C_mul_gram_substitution_integral hs, subst_phAt hs (cc_X ()), e] at h
  exact h

private theorem be_comm' {σ : Type*} {l ex ph : PowerSeries ℂ_[p]} (x y : MvPowerSeries σ ℂ_[p]) :
    be l ex ph x y = be l ex ph y x := by
  have hxy : add l ex x y = add l ex y x := by
    show pt ex (lg l x + lg l y) = pt ex (lg l y + lg l x)
    rw [add_comm]
  show phAt ph (add l ex x y) - phAt ph x - phAt ph y = phAt ph (add l ex y x) - phAt ph y - phAt ph x
  rw [hxy, sub_right_comm]

theorem moveSub : MoveSub := by
  intro p _ l ex ph S H σ α α' hα hα' a b ha hb
  have hu : Good (mulBy l ex α.1 a) := goodMul p l ex ph S H σ α hα a ha
  have hsG : ∀ i, Good (![b, mulBy l ex α.1 a] i) := by
    intro i
    fin_cases i
    · simpa using hb
    · simpa using hu
  have hs := hasSubst_good hsG
  have h := sSubst ![b, mulBy l ex α.1 a] hsG (H.conj α' hα')
  have e0 : MvPowerSeries.subst ![b, mulBy l ex α.1 a] (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = b :=
    MvPowerSeries.subst_X hs 0
  have e1 : MvPowerSeries.subst ![b, mulBy l ex α.1 a] (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) =
      mulBy l ex α.1 a :=
    MvPowerSeries.subst_X hs 1
  rw [subst_be H.data hs (cc_mulBy H.data α'.1 (cc_X 0)) (cc_X 1), subst_mulBy H.data hs α'.1 (cc_X 0),
    subst_be H.data hs (cc_X 0) (cc_mulBy H.data α'.2 (cc_X 1)), subst_mulBy H.data hs α'.2 (cc_X 1),
    e0, e1, mulBy_mulBy H.data α.1 α'.2 ha.1] at h
  rw [be_comm' (mulBy l ex α.1 a), be_comm' (mulBy l ex (α'.2 * α.1) a)]
  exact h

end PI.UnitaryGroupMassFormula.PhGram
