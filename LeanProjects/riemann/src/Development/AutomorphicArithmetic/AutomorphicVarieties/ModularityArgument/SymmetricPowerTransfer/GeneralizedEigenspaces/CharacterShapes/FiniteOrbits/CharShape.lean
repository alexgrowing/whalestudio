import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ExpoEq

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So.CS

section One

variable {G : Type} [CommGroup G]

end One

section Main

variable {I : Type}

structure D (S : Finset I) (G : I → Type) [∀ v, CommGroup (G v)] where
  o : ∀ v, G v →* Multiplicative ℤ
  ϖ : ∀ v, G v
  H : ∀ v, Subgroup (G v)
  R : ∀ v, Finset (G v)
  hϖ : ∀ v ∈ S, (o v (ϖ v)).toAdd = 1
  hH : ∀ v ∈ S, ∀ h ∈ H v, (o v h).toAdd = 0
  hR1 : ∀ v ∈ S, ∀ y ∈ R v, 0 ≤ (o v y).toAdd ∧ (o v y).toAdd ≤ 1
  hR2 : ∀ v ∈ S, ∀ u : G v, ∃! y, y ∈ R v ∧ ∃ s : G v, u / (y * s ^ 2) ∈ H v

variable {S : Finset I} {G : I → Type} [∀ v, CommGroup (G v)]

def sg (d : ∀ v, Fin 3 → G v) : ∀ v, Fin 3 → G v := fun v => ![(d v 2)⁻¹, (d v 1)⁻¹, (d v 0)⁻¹]

def io (i : Fin 3) : (∀ v, G v) →* (∀ v, Fin 3 → G v) where
  toFun t v := Pi.mulSingle i (t v)
  map_one' := by
    funext v
    exact Pi.mulSingle_one i
  map_mul' s t := by
    funext v
    exact Pi.mulSingle_mul i _ _

namespace D

variable (L : D S G)

def od (v : I) (x : G v) : ℤ := (L.o v x).toAdd

@[simp] private theorem od_mul (v : I) (x y : G v) : L.od v (x * y) = L.od v x + L.od v y := by
  simp [od]

@[simp] private theorem od_one (v : I) : L.od v 1 = 0 := by
  simp [od]

@[simp] private theorem od_inv (v : I) (x : G v) : L.od v x⁻¹ = - L.od v x := by
  simp [od]

@[simp] private theorem od_pow (v : I) (x : G v) (n : ℕ) : L.od v (x ^ n) = n * L.od v x := by
  simp [od]

def Dm (d : ∀ v, Fin 3 → G v) : Prop :=
  ∀ v ∈ S, L.od v (d v 1) ≤ L.od v (d v 0) ∧ L.od v (d v 2) ≤ L.od v (d v 1)

def Sd (d : ∀ v, Fin 3 → G v) : Prop :=
  ∀ v ∈ S, L.od v (d v 1) < L.od v (d v 0) ∧ L.od v (d v 2) < L.od v (d v 1)

def Cn (t : ∀ v, G v) : Prop := ∀ v ∈ S, 2 < L.od v (t v)

variable {L}

private theorem Dm.mul {d d' : ∀ v, Fin 3 → G v} (h : L.Dm d) (h' : L.Dm d') : L.Dm (d * d') := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  obtain ⟨h1', h2'⟩ := h' v hv
  simp only [Pi.mul_apply, od_mul]
  constructor <;> linarith

private theorem Sd.mul {d d' : ∀ v, Fin 3 → G v} (h : L.Sd d) (h' : L.Dm d') : L.Sd (d * d') := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  obtain ⟨h1', h2'⟩ := h' v hv
  simp only [Pi.mul_apply, od_mul]
  constructor <;> linarith

private theorem Dm.sg {d : ∀ v, Fin 3 → G v} (h : L.Dm d) : L.Dm (sg d) := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  simp only [CS.sg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, od_inv]
  constructor <;> linarith

private theorem dm_one : L.Dm 1 := by
  intro v hv
  simp

private theorem Dm.pow {d : ∀ v, Fin 3 → G v} (h : L.Dm d) (N : ℕ) : L.Dm (d ^ N) := by
  induction N with
  | zero => simpa using dm_one
  | succ n ih => rw [pow_succ]; exact ih.mul h

variable (L) in

structure Ch (χ : (∀ v, Fin 3 → G v) → ℂ) : Prop where
  mul : ∀ d d', L.Dm d → L.Dm d' → χ (d * d') = χ d * χ d'
  lev : ∀ d, (∀ v ∈ S, ∀ i, d v i ∈ L.H v) → χ d = 1
  inv : ∀ d, L.Dm d → χ (sg d) = χ d

variable {χ : (∀ v, Fin 3 → G v) → ℂ}

private theorem Ch.pow (hχ : L.Ch χ) {d : ∀ v, Fin 3 → G v} (hd : L.Dm d) (N : ℕ) :
    χ (d ^ N) = χ d ^ N := by
  induction N with
  | zero =>
    simp only [pow_zero]
    exact hχ.lev 1 (fun v _ i => by simp [Subgroup.one_mem])
  | succ n ih =>
    rw [pow_succ, pow_succ, hχ.mul _ _ (hd.pow n) hd, ih]

section X

variable {X : (∀ v, Fin 3 → G v) →* ℂˣ}

end X

end D

end Main

section Ord

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem phi_ne (x : kˣ) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (valuation k (x : k)) ≠ 0 := by
  simp

def ordU : kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd
    (-WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (valuation k (x : k))))
  map_one' := by simp
  map_mul' x y := by
    have hx := phi_ne k x
    have hy := phi_ne k y
    rw [Units.val_mul, map_mul, map_mul, WithZero.log_mul hx hy, neg_add, ofAdd_add]

end Ord

end UpperTheory.V.Z.Sym.So.CS

private theorem dom_of_valuation_monotone_fin_three {k : Type} [Field k] [ValuativeRel k] {x : Fin 3 → kˣ}
    (h01 : valuation k (x 0 : k) ≤ valuation k (x 1 : k))
    (h12 : valuation k (x 1 : k) ≤ valuation k (x 2 : k)) : Dom x := by
  unfold Dom
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact le_rfl
    | exact h01
    | exact h12
    | exact h01.trans h12
    | exact absurd hij (by decide)

private theorem dom_mul' {k : Type} [Field k] [ValuativeRel k] {n : ℕ} {x y : Fin n → kˣ}
    (hx : Dom x) (hy : Dom y) : Dom (x * y) := by
  unfold Dom at *
  intro i j hij
  simp only [Pi.mul_apply, Units.val_mul, map_mul]
  exact mul_le_mul' (hx i j hij) (hy i j hij)

private theorem valuation_monotone_of_dom_fin_three {k : Type} [Field k] [ValuativeRel k] {x : Fin 3 → kˣ} (hx : Dom x) :
    valuation k (x 0 : k) ≤ valuation k (x 1 : k) ∧ valuation k (x 1 : k) ≤ valuation k (x 2 : k) := by
  unfold Dom at hx
  exact ⟨hx 0 1 (by decide), hx 1 2 (by decide)⟩

private theorem valuation_unif_eq_uniformizer' (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    valuation k (unif k : k) = ValuativeRel.uniformizer k := by
  unfold unif
  apply Classical.epsilon_spec (p := fun x : kˣ => valuation k (x : k) = ValuativeRel.uniformizer k)
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer k)
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact ValuativeRel.uniformizer_ne_zero hy.symm
  exact ⟨Units.mk0 y hy0, by simpa using hy⟩

private theorem valuation_unif_pos_and_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    0 < valuation k (unif k : k) ∧ valuation k (unif k : k) < 1 := by
  rw [valuation_unif_eq_uniformizer']
  exact ⟨ValuativeRel.uniformizer_pos, ValuativeRel.uniformizer_lt_one⟩

private theorem valuation_mul_unif_pow_inv_le_one_of_lt_sq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {t : kˣ}
    (h : valuation k (t : k) < valuation k (unif k : k) ^ 2) :
    valuation k ((t * (unif k ^ 3)⁻¹ : kˣ) : k) ≤ 1 := by
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀,
    map_pow]
  rw [valuation_unif_eq_uniformizer'] at h ⊢
  have hπ0 : 0 < ValuativeRel.uniformizer k := ValuativeRel.uniformizer_pos
  have h1 : valuation k (t : k) / ValuativeRel.uniformizer k ^ 2 < 1 :=
    (div_lt_one₀ (pow_pos hπ0 2)).mpr h
  have h2 := ValuativeRel.le_uniformizer_iff.mpr h1
  have h3 := (div_le_iff₀ (pow_pos hπ0 2)).mp h2
  rw [← div_eq_mul_inv, div_le_one₀ (pow_pos hπ0 3), pow_succ']
  exact h3

private theorem valuation_div_le_valuation_div_of_le {k : Type} [Field k] [ValuativeRel k] {a b c : kˣ}
    (h : valuation k (a : k) ≤ valuation k (b : k)) :
    valuation k ((a / c : kˣ) : k) ≤ valuation k ((b / c : kˣ) : k) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, Units.val_mul, Units.val_mul, map_mul, map_mul]
  exact mul_le_mul' h le_rfl

private theorem valuation_div_le_one_of_le {k : Type} [Field k] [ValuativeRel k] {a b : kˣ}
    (h : valuation k (a : k) ≤ valuation k (b : k)) :
    valuation k ((a / b : kˣ) : k) ≤ 1 := by
  have h1 := valuation_div_le_valuation_div_of_le (c := b) h
  rw [div_self', Units.val_one, map_one] at h1
  exact h1

private theorem one_le_valuation_inv_of_le_one {k : Type} [Field k] [ValuativeRel k] {a : kˣ}
    (h : valuation k (a : k) ≤ 1) : 1 ≤ valuation k ((a⁻¹ : kˣ) : k) := by
  have h1 := valuation_div_le_valuation_div_of_le (a := a) (b := 1) (c := a) (by rw [Units.val_one, map_one]; exact h)
  rw [div_self', one_div, Units.val_one, map_one] at h1
  exact h1

open UpperTheory.V.Z.Sym.So.CS in
theorem UpperTheory.V.Z.Sym.So.charShape :
    UpperTheory.V.Z.Sym.So.CharShape := by
  classical
  intro F _ _ Δ A hA χ hmul hlev hsg
  obtain ⟨e1, he1⟩ : ∃ e1 : Dat.Par F → ParN F 3, ∀ t v, e1 t v = ![t v, 1, 1] :=
    ⟨fun t v => ![t v, 1, 1], fun _ _ => rfl⟩
  obtain ⟨sc, hsc⟩ : ∃ sc : Dat.Par F → ParN F 3, ∀ z v, sc z v = ![z v, z v, z v] :=
    ⟨fun z v => ![z v, z v, z v], fun _ _ => rfl⟩
  obtain ⟨pp, hpp⟩ : ∃ pp : Dat.Par F, ∀ v, pp v = unif (Kv v) :=
    ⟨fun v => unif (Kv v), fun _ => rfl⟩
  obtain ⟨hat, hhat⟩ : ∃ hat : ((v : A.Sg) → (Kv v.1)ˣ) → Dat.Par F,
      ∀ y v, hat y v = if h : v ∈ A.Sg then y ⟨v, h⟩ else (1 : (Kv v)ˣ) :=
    ⟨fun y v => if h : v ∈ A.Sg then y ⟨v, h⟩ else (1 : (Kv v)ˣ), fun _ _ => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ((v : A.Sg) → (Kv v.1)ˣ) → ParN F 3,
      ∀ y v, M y v = ![pp v, hat y v, (pp v)⁻¹] :=
    ⟨fun y v => ![pp v, hat y v, (pp v)⁻¹], fun _ _ => rfl⟩
  have hdm : ∀ {d d' : ParN F 3}, A.DomS d → A.DomS d' → A.DomS (d * d') :=
    fun hd hd' v hv => dom_mul' (hd v hv) (hd' v hv)
  have hχ1 : χ 1 = 1 := hlev 1 (fun v _ i => by simp [Subgroup.one_mem])
  have hπ : ∀ v, 0 < valuation (Kv v) ((pp v : (Kv v)ˣ) : Kv v) ∧
      valuation (Kv v) ((pp v : (Kv v)ˣ) : Kv v) < 1 := fun v => by
    rw [hpp]
    exact valuation_unif_pos_and_lt_one _
  have e1mul : ∀ t t', e1 (t * t') = e1 t * e1 t' := by
    intro t t'
    funext v i
    fin_cases i <;> simp [he1]
  have scmul : ∀ z z', sc (z * z') = sc z * sc z' := by
    intro z z'
    funext v i
    fin_cases i <;> simp [hsc]
  have de1 : ∀ t : Dat.Par F, (∀ v ∈ A.Sg, valuation (Kv v) ((t v : (Kv v)ˣ) : Kv v) ≤ 1) →
      A.DomS (e1 t) := by
    intro t ht v hv
    rw [he1]
    apply dom_of_valuation_monotone_fin_three <;> simp [ht v hv]
  have dsc : ∀ z, A.DomS (sc z) := by
    intro z v _
    rw [hsc]
    apply dom_of_valuation_monotone_fin_three <;> simp
  have σmul : ∀ z z', χ (sc (z * z')) = χ (sc z) * χ (sc z') := by
    intro z z'
    rw [scmul]
    exact hmul _ _ (dsc _) (dsc _)
  have hχsc : ∀ z, χ (sc z) * χ (sc z) = 1 := by
    intro z
    have hs : SD.sg (sc z) = sc z⁻¹ := by
      funext v i
      fin_cases i <;> simp [SD.sg, hsc]
    have h1 : sc (z * z⁻¹) = 1 := by
      rw [mul_inv_cancel]
      funext v i
      fin_cases i <;> simp [hsc]
    calc χ (sc z) * χ (sc z) = χ (sc z) * χ (SD.sg (sc z)) := by rw [hsg _ (dsc z)]
      _ = 1 := by rw [hs, ← σmul, h1, hχ1]
  have cone_le : ∀ t, A.Cone t → ∀ v ∈ A.Sg, valuation (Kv v) ((t v : (Kv v)ˣ) : Kv v) ≤ 1 := by
    intro t ht v hv
    have h1 := ht v hv
    have h2 := hπ v
    rw [hpp] at h2
    exact (h1.trans_le (pow_le_one₀ zero_le' h2.2.le)).le
  have dGeq : ∀ t y, A.dG t y = e1 (t * (pp ^ 3)⁻¹) * e1 pp * M y := by
    intro t y
    funext v i
    fin_cases i <;> simp [SD.dG, he1, hM, hhat, hpp] <;> group
  have e1eq : ∀ t, e1 t = e1 (t * (pp ^ 3)⁻¹) * e1 pp * e1 pp * e1 pp := by
    intro t
    funext v i
    fin_cases i <;> simp [he1] <;> group
  have dpp : A.DomS (e1 pp) := de1 pp (fun v _ => (hπ v).2.le)
  have dr : ∀ t, A.Cone t → A.DomS (e1 (t * (pp ^ 3)⁻¹)) := by
    intro t ht
    apply de1
    intro v hv
    have e : (t * (pp ^ 3)⁻¹) v = t v * (unif (Kv v) ^ 3)⁻¹ := by simp [hpp]
    rw [e]
    exact valuation_mul_unif_pow_inv_le_one_of_lt_sq (Kv v) (ht v hv)
  have dMy : ∀ y ∈ A.Ys, A.DomS (M y) := by
    intro y hy v hv
    have hyv : y ⟨v, hv⟩ ∈ A.Ry v := Fintype.mem_piFinset.mp hy ⟨v, hv⟩
    have hsq := hA.ry v hv
    unfold Lev.IsSqReps at hsq
    obtain ⟨h1, h2⟩ := hsq.1 _ hyv
    rw [hM]
    apply dom_of_valuation_monotone_fin_three
    · simpa [hhat, hv, hpp] using h1
    · have h3 := (one_le_inv₀ (hπ v).1).mpr (hπ v).2.le
      simp [hhat, hv]
      exact h2.trans h3
  refine ⟨(χ (e1 pp) ^ 2)⁻¹ * ∑ y ∈ A.Ys, χ (M y), fun t => χ (e1 t), ?_, ?_, ?_⟩
  · intro t t' ht ht'
    show χ (e1 (t * t')) = χ (e1 t) * χ (e1 t')
    rw [e1mul]
    exact hmul _ _ (de1 t (cone_le t ht)) (de1 t' (cone_le t' ht'))
  · intro t ht
    show ∑ y ∈ A.Ys, χ (A.dG t y) = (χ (e1 pp) ^ 2)⁻¹ * (∑ y ∈ A.Ys, χ (M y)) * χ (e1 t)
    have hr := dr t ht
    have hsum : ∀ y ∈ A.Ys, χ (A.dG t y) = χ (e1 (t * (pp ^ 3)⁻¹)) * χ (e1 pp) * χ (M y) := by
      intro y hy
      rw [dGeq, hmul _ _ (hdm hr dpp) (dMy y hy), hmul _ _ hr dpp]
    have hbeta : χ (e1 t) = χ (e1 (t * (pp ^ 3)⁻¹)) * χ (e1 pp) ^ 3 := by
      rw [e1eq t, hmul _ _ (hdm (hdm hr dpp) dpp) dpp, hmul _ _ (hdm hr dpp) dpp, hmul _ _ hr dpp]
      ring
    rw [Finset.sum_congr rfl hsum, ← Finset.mul_sum, hbeta]
    rcases eq_or_ne (χ (e1 pp)) 0 with hc | hc
    · simp [hc]
    · field_simp
  · intro hb a ha d hd
    have hc : χ (e1 pp) ≠ 0 := by
      rintro h
      apply hb
      simp [h]
    have hS : ∑ y ∈ A.Ys, χ (M y) ≠ 0 := by
      rintro h
      apply hb
      simp [h]
    obtain ⟨Aa, hAa⟩ : ∃ Aa : Dat.Par F → ℂ, ∀ u, Aa u =
        ∏ v ∈ A.Sg, ((a v (u v) : ℂ) * (absPow (Kv v) (-1) (u v) : ℂ)) := ⟨_, fun _ => rfl⟩
    have hAmul : ∀ u u', Aa (u * u') = Aa u * Aa u' := by
      intro u u'
      simp only [hAa, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v _
      simp only [Pi.mul_apply, map_mul, Units.val_mul]
      ring
    have hAne : ∀ u, Aa u ≠ 0 := by
      intro u
      rw [hAa]
      exact Finset.prod_ne_zero_iff.mpr (fun v _ => mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
    have hexS : ∀ t, A.exS a t = Aa t := by
      intro t
      rw [hAa]
      unfold SD.exS SD.dS
      exact Finset.prod_congr rfl (fun v _ => (expoEq (Kv v) (a v)).2.1 (t v))
    have hexG : ∀ d : ParN F 3, A.exG a d = Aa (fun v => d v 0 / d v 2) := by
      intro d
      rw [hAa]
      unfold SD.exG
      exact Finset.prod_congr rfl (fun v _ => (expoEq (Kv v) (a v)).1 (d v))
    have step1 : ∀ t : Dat.Par F, (∀ v ∈ A.Sg, valuation (Kv v) ((t v : (Kv v)ˣ) : Kv v) ≤ 1) →
        χ (e1 t) = Aa t := by
      intro t ht
      have hq : A.Cone (pp ^ 3) := by
        intro v hv
        have h := hπ v
        rw [hpp] at h
        simp only [Pi.pow_apply, hpp, Units.val_pow_eq_pow_val, map_pow]
        exact pow_lt_pow_right_of_lt_one₀ h.1 h.2 (by norm_num)
      have htq : A.Cone (t * pp ^ 3) := by
        intro v hv
        have h := hq v hv
        simp only [Pi.mul_apply, Units.val_mul, map_mul]
        calc _ ≤ 1 * valuation (Kv v) (((pp ^ 3) v : (Kv v)ˣ) : Kv v) := mul_le_mul' (ht v hv) le_rfl
          _ < _ := by rw [one_mul]; exact h
      have h1 : χ (e1 (t * pp ^ 3)) = A.exS a (t * pp ^ 3) := ha _ htq
      have h2 : χ (e1 (pp ^ 3)) = A.exS a (pp ^ 3) := ha _ hq
      rw [hexS] at h1 h2
      rw [e1mul, hmul _ _ (de1 t ht) (de1 _ (cone_le _ hq)), h2, hAmul] at h1
      exact mul_right_cancel₀ (hAne _) h1
    have step3 : ∀ d : ParN F 3, A.DomS d →
        χ d = Aa (fun v => d v 0 / d v 2) * χ (sc (fun v => d v 1)) := by
      intro d hd
      obtain ⟨x, hx⟩ : ∃ x : Dat.Par F, x = fun v => d v 0 / d v 2 := ⟨_, rfl⟩
      obtain ⟨w, hw⟩ : ∃ w : Dat.Par F, w = fun v => d v 1 / d v 2 := ⟨_, rfl⟩
      rw [← hx]
      have hvx : ∀ v ∈ A.Sg, valuation (Kv v) ((x v : (Kv v)ˣ) : Kv v) ≤
          valuation (Kv v) ((w v : (Kv v)ˣ) : Kv v) ∧
          valuation (Kv v) ((w v : (Kv v)ˣ) : Kv v) ≤ 1 := by
        intro v hv
        obtain ⟨h01, h12⟩ := valuation_monotone_of_dom_fin_three (hd v hv)
        subst hx hw
        refine ⟨valuation_div_le_valuation_div_of_le h01, ?_⟩
        exact valuation_div_le_one_of_le h12
      obtain ⟨X, hX⟩ : ∃ X : ParN F 3, ∀ v, X v = ![x v, w v, 1] := ⟨_, fun _ => rfl⟩
      obtain ⟨T, hT⟩ : ∃ T : ParN F 3, ∀ v, T v = ![w v, w v, 1] := ⟨_, fun _ => rfl⟩
      obtain ⟨N, hN⟩ : ∃ N : ParN F 3, ∀ v, N v = ![1, 1, (w v)⁻¹] := ⟨_, fun _ => rfl⟩
      have dX : A.DomS X := by
        intro v hv
        rw [hX]
        apply dom_of_valuation_monotone_fin_three <;> simp [(hvx v hv).1, (hvx v hv).2]
      have dT : A.DomS T := by
        intro v hv
        rw [hT]
        apply dom_of_valuation_monotone_fin_three <;> simp [(hvx v hv).2]
      have dN : A.DomS N := by
        intro v hv
        rw [hN]
        apply dom_of_valuation_monotone_fin_three
        · simp
        · simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
          exact one_le_valuation_inv_of_le_one (hvx v hv).2
      have dxw : ∀ v ∈ A.Sg, valuation (Kv v) (((x / w) v : (Kv v)ˣ) : Kv v) ≤ 1 := by
        intro v hv
        rw [Pi.div_apply]
        exact valuation_div_le_one_of_le (hvx v hv).1
      have eq1 : d = X * sc (fun v => d v 2) := by
        funext v i
        fin_cases i <;> simp [hsc, hX, hx, hw]
      have eq2 : X = e1 (x / w) * T := by
        funext v i
        fin_cases i <;> simp [he1, hX, hT]
      have eq3 : T = sc w * N := by
        funext v i
        fin_cases i <;> simp [hsc, hT, hN]
      have eq4 : SD.sg N = e1 w := by
        funext v i
        fin_cases i <;> simp [SD.sg, he1, hN]
      have eq5 : x / w * w = x := by simp
      have eq6 : w * (fun v => d v 2) = fun v => d v 1 := by
        funext v
        simp [hw]
      calc χ d = χ (X * sc (fun v => d v 2)) := congrArg χ eq1
        _ = χ X * χ (sc (fun v => d v 2)) := hmul _ _ dX (dsc _)
        _ = Aa (x / w) * (χ (sc w) * Aa w) * χ (sc (fun v => d v 2)) := by
          rw [eq2, hmul _ _ (de1 _ dxw) dT, step1 _ dxw, eq3, hmul _ _ (dsc _) dN, ← hsg _ dN, eq4,
            step1 w (fun v hv => (hvx v hv).2)]
        _ = Aa (x / w * w) * χ (sc (w * fun v => d v 2)) := by
          rw [hAmul, σmul]
          ring
        _ = Aa x * χ (sc (fun v => d v 1)) := by rw [eq5, eq6]
    have step4 : ∀ y ∈ A.Ys, χ (M y) = Aa (fun v => pp v / (pp v)⁻¹) * χ (sc (hat y)) := by
      intro y hy
      rw [step3 _ (dMy y hy)]
      have e1' : (fun v => M y v 0 / M y v 2) = fun v => pp v / (pp v)⁻¹ := by
        funext v
        simp [hM]
      have e2' : (fun v => M y v 1) = hat y := by
        funext v
        simp [hM]
      rw [e1', e2']
    have hsum : ∑ y ∈ A.Ys, χ (sc (hat y)) ≠ 0 := by
      intro h
      apply hS
      rw [Finset.sum_congr rfl step4, ← Finset.mul_sum, h, mul_zero]
    have step5 : ∀ z, χ (sc z) = 1 := by
      intro z0
      by_contra hne
      have hneg : χ (sc z0) = -1 := (mul_self_eq_one_iff.mp (hχsc z0)).resolve_left hne
      apply hsum
      have hsq : ∀ (w : A.Sg) (u : (Kv w.1)ˣ), ∃! y, y ∈ A.Ry w.1 ∧
          ∃ s : (Kv w.1)ˣ, u / (y * s ^ 2) ∈ (A.V w.1).H := by
        intro w u
        have h := hA.ry w.1 w.2
        unfold Lev.IsSqReps at h
        exact h.2 u
      choose rep hrepR sq hsqH using fun w u => (hsq w u).exists
      have hinv : ∀ (w : A.Sg) (g y : (Kv w.1)ˣ), y ∈ A.Ry w.1 →
          rep w (g⁻¹ * rep w (g * y)) = y := by
        intro w g y hy
        symm
        refine (hsq w _).unique ⟨hy, (sq w (g * y))⁻¹, ?_⟩ ⟨hrepR w _, sq w _, hsqH w _⟩
        have h := (A.V w.1).H.inv_mem (hsqH w (g * y))
        have e : g⁻¹ * rep w (g * y) / (y * (sq w (g * y))⁻¹ ^ 2) =
            (g * y / (rep w (g * y) * sq w (g * y) ^ 2))⁻¹ := by
          ext
          push_cast
          field_simp
        rw [e]
        exact h
      obtain ⟨φ, hφ⟩ : ∃ φ : ((v : A.Sg) → (Kv v.1)ˣ) → ((v : A.Sg) → (Kv v.1)ˣ),
          ∀ y w, φ y w = rep w (z0 w.1 * y w) := ⟨_, fun _ _ => rfl⟩
      obtain ⟨ψ, hψ⟩ : ∃ ψ : ((v : A.Sg) → (Kv v.1)ˣ) → ((v : A.Sg) → (Kv v.1)ˣ),
          ∀ y w, ψ y w = rep w ((z0 w.1)⁻¹ * y w) := ⟨_, fun _ _ => rfl⟩
      have memφ : ∀ y, φ y ∈ A.Ys := fun y =>
        Fintype.mem_piFinset.mpr (fun w => by rw [hφ]; exact hrepR w _)
      have memψ : ∀ y, ψ y ∈ A.Ys := fun y =>
        Fintype.mem_piFinset.mpr (fun w => by rw [hψ]; exact hrepR w _)
      have φψ : ∀ y ∈ A.Ys, φ (ψ y) = y := by
        intro y hy
        funext w
        rw [hφ, hψ]
        have := hinv w (z0 w.1)⁻¹ (y w) (Fintype.mem_piFinset.mp hy w)
        rw [inv_inv] at this
        exact this
      have ψφ : ∀ y ∈ A.Ys, ψ (φ y) = y := by
        intro y hy
        funext w
        rw [hψ, hφ]
        exact hinv w (z0 w.1) (y w) (Fintype.mem_piFinset.mp hy w)
      have hflip : ∀ y ∈ A.Ys, χ (sc (hat (φ y))) = -χ (sc (hat y)) := by
        intro y hy
        obtain ⟨Sq, hSq⟩ : ∃ Sq : Dat.Par F, ∀ v, Sq v =
            if h : v ∈ A.Sg then sq ⟨v, h⟩ (z0 v * y ⟨v, h⟩) else (1 : (Kv v)ˣ) := ⟨_, fun _ => rfl⟩
        obtain ⟨L, hL⟩ : ∃ L : Dat.Par F, L = (hat (φ y) * Sq * Sq)⁻¹ * (z0 * hat y) := ⟨_, rfl⟩
        have hLv : ∀ v ∈ A.Sg, L v ∈ (A.V v).H := by
          intro v hv
          have h := hsqH ⟨v, hv⟩ (z0 v * y ⟨v, hv⟩)
          have e : L v = z0 v * y ⟨v, hv⟩ / (rep ⟨v, hv⟩ (z0 v * y ⟨v, hv⟩) *
              sq ⟨v, hv⟩ (z0 v * y ⟨v, hv⟩) ^ 2) := by
            rw [hL]
            simp only [Pi.mul_apply, Pi.inv_apply, hhat, hSq, dif_pos hv, hφ]
            ext
            push_cast
            field_simp
          rw [e]
          exact h
        have hLlev : χ (sc L) = 1 := by
          apply hlev
          intro v hv i
          rw [hsc]
          fin_cases i <;> simpa using hLv v hv
        have hdec : z0 * hat y = hat (φ y) * Sq * Sq * L := by
          rw [hL, mul_inv_cancel_left]
        have key : χ (sc z0) * χ (sc (hat y)) = χ (sc (hat (φ y))) := by
          rw [← σmul, hdec, σmul, σmul, σmul, hLlev, mul_one, mul_assoc, hχsc, mul_one]
        rw [hneg] at key
        linear_combination -key
      have hperm : ∑ y ∈ A.Ys, χ (sc (hat y)) = ∑ y ∈ A.Ys, χ (sc (hat (φ y))) :=
        Finset.sum_nbij' ψ φ (fun y _ => memψ y) (fun y _ => memφ y) φψ ψφ
          (fun y hy => by rw [φψ y hy])
      have h1 : ∑ y ∈ A.Ys, χ (sc (hat y)) = -∑ y ∈ A.Ys, χ (sc (hat y)) := by
        conv_lhs => rw [hperm]
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl hflip
      linear_combination h1 / 2
    rw [hexG, step3 d hd, step5, mul_one]

end
