import Formalism.HermitianCurvature.StatementR

namespace Formalism.FourierDecayAlt.P.RuleGD

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Matrix

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

def cj (g gi : A) (h : g * gi = 1) (h' : gi * g = 1) : A →+* A where
  toFun x := gi * x * g
  map_one' := by simp [h']
  map_mul' x y := by
    simp only [mul_assoc]
    rw [← mul_assoc g gi (y * g), h, one_mul]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]

section cjlemmas
variable (g gi : A) (h : g * gi = 1) (h' : gi * g = 1)

lemma cj_apply (x : A) : cj g gi h h' x = gi * x * g := rfl

lemma cj_fix {x : A} (hx : x * g = g * x) : cj g gi h h' x = x := by
  rw [cj_apply, mul_assoc, hx, ← mul_assoc, h', one_mul]

lemma cj_alg (z : ℂ) : cj g gi h h' (algebraMap ℂ A z) = algebraMap ℂ A z :=
  cj_fix g gi h h' (Algebra.commutes z g)

lemma cj_of_eq {x a : A} (hx : x * g = g * x + a * g) : cj g gi h h' x = x + cj g gi h h' a := by
  rw [cj_apply, cj_apply, mul_assoc, hx, mul_add, ← mul_assoc, h', one_mul, ← mul_assoc]

lemma comm_of_cj {y : A} (hy : cj g gi h h' y = y) : g * y = y * g := by
  have := congrArg (g * ·) hy
  simp only [cj_apply, ← mul_assoc, h, one_mul] at this
  exact this.symm

end cjlemmas

lemma comm_prod {n : ℕ} (f : Fin n → A) (x : A) (hx : ∀ i, x * f i = f i * x) :
    x * (List.ofFn f).prod = (List.ofFn f).prod * x :=
  (Commute.list_prod_right _ _ (by
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact hx i)).eq

lemma shift_prod {n : ℕ} (f : Fin n → A) (x : A) (a : Fin n → ℂ)
    (hx : ∀ i, x * f i = f i * x + a i • f i) :
    x * (List.ofFn f).prod = (List.ofFn f).prod * x + (∑ i, a i) • (List.ofFn f).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, ← mul_assoc, hx 0, add_mul, mul_assoc,
      ih (fun i => f i.succ) (fun i => a i.succ) (fun i => hx i.succ)]
    simp only [mul_add, add_smul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    abel

lemma prod_mul_prod_eq_one {n : ℕ} (f g : Fin n → A) (hfg : ∀ i, f i * g i = 1)
    (hc : ∀ i j, g i * f j = f j * g i) : (List.ofFn f).prod * (List.ofFn g).prod = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have hcomm := (comm_prod (fun i => f i.succ) (g 0) (fun i => hc 0 i.succ)).symm
    rw [mul_assoc, ← mul_assoc _ (g 0), hcomm, ← mul_assoc, ← mul_assoc, hfg 0, one_mul,
      ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hfg i.succ) (fun i j => hc i.succ j.succ)]

lemma map_ofFn_prod {n : ℕ} (φ : A →+* A) (f : Fin n → A) (hf : ∀ i, φ (f i) = f i) :
    φ (List.ofFn f).prod = (List.ofFn f).prod := by
  rw [map_list_prod, List.map_ofFn]
  have : (⇑φ ∘ f) = f := funext hf
  rw [this]

section fnsmem
variable (L : LevelData A r)

lemma fc {x y : A} (hx : x ∈ L.fns) (hy : y ∈ L.fns) : x * y = y * x := L.fns_comm x hx y hy

lemma m_c (l) : L.c l ∈ L.fns := by simp [LevelData.fns]
lemma m_ci (l) : L.ci l ∈ L.fns := by simp [LevelData.fns]
lemma m_cb (l) : L.cb l ∈ L.fns := by simp [LevelData.fns]
lemma m_cbi (l) : L.cbi l ∈ L.fns := by simp [LevelData.fns]
lemma m_ζ : L.ζ ∈ L.fns := by simp [LevelData.fns]
lemma m_ζi : L.ζi ∈ L.fns := by simp [LevelData.fns]
lemma m_ζb : L.ζb ∈ L.fns := by simp [LevelData.fns]
lemma m_ζbi : L.ζbi ∈ L.fns := by simp [LevelData.fns]
lemma m_GG : L.GG ∈ L.fns := by simp [LevelData.fns]
lemma m_GGi : L.GGi ∈ L.fns := by simp [LevelData.fns]

end fnsmem

lemma tprod_map (L : LevelData A r) (φ : A →+* A) (Y Y' : ℂ)
    (h : ∀ l, (L.Tl Y l).map φ = L.Tl Y' l) : (L.Tprod Y).map φ = L.Tprod Y' := by
  unfold LevelData.Tprod
  rw [← RingHom.mapMatrix_apply, map_list_prod, List.map_reverse, List.map_ofFn]
  exact congrArg (fun f => ((List.ofFn f).reverse).prod) (funext h)

lemma tvprod_map (L : LevelData A r) (φ : A →+* A) (Y Y' : ℂ)
    (h : ∀ l, (L.Tvl Y l).map φ = L.Tvl Y' l) : (L.Tvprod Y).map φ = L.Tvprod Y' := by
  unfold LevelData.Tvprod
  rw [← RingHom.mapMatrix_apply, map_list_prod, List.map_reverse, List.map_ofFn]
  exact congrArg (fun f => ((List.ofFn f).reverse).prod) (funext h)

lemma keyA (L : LevelData A r) (φ : A →+* A) (t : ℂ) (e : A)
    (hal : ∀ z, φ (algebraMap ℂ A z) = algebraMap ℂ A z)
    (hp : ∀ l, φ (L.p l) = L.p l + algebraMap ℂ A t)
    (hc : ∀ l, φ (L.c l) = L.c l) (hci : ∀ l, φ (L.ci l) = L.ci l)
    (hcb : ∀ l, φ (L.cb l) = L.cb l) (hGG : φ L.GG = L.GG) (hzb : φ L.ζb = L.ζb)
    (hGGi : φ L.GGi = L.GGi)
    (hnab : φ L.nab = L.nab + algebraMap ℂ A t * (L.ζb * L.GGi) - e) (Y : ℂ) :
    φ (L.Ahat Y) = L.Ahat (Y + t) ∧
      φ (L.R0 Y) = L.R0 (Y + t) + L.Drb * L.GG * e * L.Ar (Y + t) := by
  have hT : (L.Tprod Y).map φ = L.Tprod (Y + t) := by
    apply tprod_map
    intro l
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LevelData.Tl, hp, hc, hci, hal, map_add]
    abel
  have hAr : φ (L.Ar Y) = L.Ar (Y + t) := by
    unfold LevelData.Ar; rw [← hT]; rfl
  have hBr : φ (L.Br Y) = L.Br (Y + t) := by
    unfold LevelData.Br; rw [← hT]; rfl
  have hDr : φ L.Dr = L.Dr := map_ofFn_prod φ L.c hc
  have hDrb : φ L.Drb = L.Drb := map_ofFn_prod φ L.cb hcb
  have hl0 : φ (L.l0 Y) = L.l0 (Y + t) + e := by
    have h2 : algebraMap ℂ A (Y + t + 1 / 2) = algebraMap ℂ A (Y + 1 / 2) + algebraMap ℂ A t := by
      rw [← map_add]; congr 1; ring
    simp only [LevelData.l0, map_sub, map_neg, map_mul, hal, hnab, hzb, hGGi, h2, add_mul]
    abel
  constructor
  · unfold LevelData.Ahat; rw [map_mul, hDr, hAr]
  · unfold LevelData.R0
    rw [map_mul, map_mul, map_add, map_mul, hDrb, hGG, hl0, hAr, hBr]
    simp only [add_mul, mul_add, mul_assoc]
    abel

lemma keyV (L : LevelData A r) (φ : A →+* A) (t : ℂ) (e : A)
    (hal : ∀ z, φ (algebraMap ℂ A z) = algebraMap ℂ A z)
    (hpb : ∀ l, φ (L.pb l) = L.pb l + algebraMap ℂ A t)
    (hcb : ∀ l, φ (L.cb l) = L.cb l) (hcbi : ∀ l, φ (L.cbi l) = L.cbi l)
    (hc : ∀ l, φ (L.c l) = L.c l) (hGG : φ L.GG = L.GG) (hz : φ L.ζ = L.ζ)
    (hGGi : φ L.GGi = L.GGi)
    (hnabs : φ L.nabs = L.nabs - algebraMap ℂ A t * (L.ζ * L.GGi) - e) (Y : ℂ) :
    φ (L.Ahatv Y) = L.Ahatv (Y - t) ∧
      φ (L.R0v Y) = L.R0v (Y - t) + L.Dr * L.GG * e * L.Avr (Y - t) := by
  have hT : (L.Tvprod Y).map φ = L.Tvprod (Y - t) := by
    apply tvprod_map
    intro l
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LevelData.Tvl, hpb, hcb, hcbi, hal, map_sub]
    abel
  have hAr : φ (L.Avr Y) = L.Avr (Y - t) := by
    unfold LevelData.Avr; rw [← hT]; rfl
  have hBr : φ (L.Bvr Y) = L.Bvr (Y - t) := by
    unfold LevelData.Bvr; rw [← hT]; rfl
  have hDr : φ L.Dr = L.Dr := map_ofFn_prod φ L.c hc
  have hDrb : φ L.Drb = L.Drb := map_ofFn_prod φ L.cb hcb
  have hm0 : φ (L.m0 Y) = L.m0 (Y - t) + e := by
    have h2 : algebraMap ℂ A (Y - t - 1 / 2) = algebraMap ℂ A (Y - 1 / 2) - algebraMap ℂ A t := by
      rw [← map_sub]; congr 1; ring
    simp only [LevelData.m0, map_sub, map_neg, map_mul, hal, hnabs, hz, hGGi, h2, sub_mul]
    abel
  constructor
  · unfold LevelData.Ahatv; rw [map_mul, hDrb, hAr]
  · unfold LevelData.R0v
    rw [map_mul, map_mul, map_add, map_mul, hDr, hGG, hm0, hAr, hBr]
    simp only [add_mul, mul_add, mul_assoc]
    abel

lemma commA (L : LevelData A r) (x xi : A) (h : x * xi = 1) (h' : xi * x = 1)
    (hp : ∀ m, L.p m * x = x * L.p m) (hfn : ∀ y ∈ L.fns, y * x = x * y)
    (hn : L.nab * x = x * L.nab) (Y : ℂ) :
    x * L.Ahat Y = L.Ahat Y * x ∧ x * L.R0 Y = L.R0 Y * x := by
  have hf : ∀ y ∈ L.fns, cj x xi h h' y = y := fun y hy => cj_fix x xi h h' (hfn y hy)
  obtain ⟨a1, a2⟩ := keyA L (cj x xi h h') 0 0 (cj_alg x xi h h')
    (fun m => by rw [map_zero, add_zero]; exact cj_fix x xi h h' (hp m))
    (fun l => hf _ (m_c L l)) (fun l => hf _ (m_ci L l)) (fun l => hf _ (m_cb L l))
    (hf _ (m_GG L)) (hf _ (m_ζb L)) (hf _ (m_GGi L))
    (by rw [map_zero, zero_mul, add_zero, sub_zero]; exact cj_fix x xi h h' hn) Y
  rw [add_zero] at a1 a2
  rw [mul_zero, zero_mul, add_zero] at a2
  exact ⟨comm_of_cj x xi h h' a1, comm_of_cj x xi h h' a2⟩

lemma commV (L : LevelData A r) (x xi : A) (h : x * xi = 1) (h' : xi * x = 1)
    (hp : ∀ m, L.pb m * x = x * L.pb m) (hfn : ∀ y ∈ L.fns, y * x = x * y)
    (hn : L.nabs * x = x * L.nabs) (Y : ℂ) :
    x * L.Ahatv Y = L.Ahatv Y * x ∧ x * L.R0v Y = L.R0v Y * x := by
  have hf : ∀ y ∈ L.fns, cj x xi h h' y = y := fun y hy => cj_fix x xi h h' (hfn y hy)
  obtain ⟨a1, a2⟩ := keyV L (cj x xi h h') 0 0 (cj_alg x xi h h')
    (fun m => by rw [map_zero, add_zero]; exact cj_fix x xi h h' (hp m))
    (fun l => hf _ (m_cb L l)) (fun l => hf _ (m_cbi L l)) (fun l => hf _ (m_c L l))
    (hf _ (m_GG L)) (hf _ (m_ζ L)) (hf _ (m_GGi L))
    (by rw [map_zero, zero_mul, sub_zero, sub_zero]; exact cj_fix x xi h h' hn) Y
  rw [sub_zero] at a1 a2
  rw [mul_zero, zero_mul, add_zero] at a2
  exact ⟨comm_of_cj x xi h h' a1, comm_of_cj x xi h h' a2⟩

lemma Dr_Dri (L : LevelData A r) : L.Dr * L.Dri = 1 :=
  prod_mul_prod_eq_one L.c L.ci L.c_ci (fun i j => fc L (m_ci L i) (m_c L j))
lemma Dri_Dr (L : LevelData A r) : L.Dri * L.Dr = 1 :=
  prod_mul_prod_eq_one L.ci L.c L.ci_c (fun i j => fc L (m_c L i) (m_ci L j))
lemma Drb_Drbi (L : LevelData A r) : L.Drb * L.Drbi = 1 :=
  prod_mul_prod_eq_one L.cb L.cbi L.cb_cbi (fun i j => fc L (m_cbi L i) (m_cb L j))
lemma Drbi_Drb (L : LevelData A r) : L.Drbi * L.Drb = 1 :=
  prod_mul_prod_eq_one L.cbi L.cb L.cbi_cb (fun i j => fc L (m_cb L i) (m_cbi L j))

lemma comm_Dr (L : LevelData A r) {x : A} (hx : ∀ l, x * L.c l = L.c l * x) :
    x * L.Dr = L.Dr * x := comm_prod L.c x hx
lemma comm_Drb (L : LevelData A r) {x : A} (hx : ∀ l, x * L.cb l = L.cb l * x) :
    x * L.Drb = L.Drb * x := comm_prod L.cb x hx

lemma fns_Dr (L : LevelData A r) {x : A} (hx : x ∈ L.fns) : x * L.Dr = L.Dr * x :=
  comm_Dr L (fun l => fc L hx (m_c L l))
lemma fns_Drb (L : LevelData A r) {x : A} (hx : x ∈ L.fns) : x * L.Drb = L.Drb * x :=
  comm_Drb L (fun l => fc L hx (m_cb L l))

lemma p_Dr (L : LevelData A r) (l : Fin r) : L.p l * L.Dr = L.Dr * L.p l + 1 * L.Dr := by
  have := shift_prod L.c (L.p l) (fun i => if l = i then (1 : ℂ) else 0) (fun i => by
    rw [L.p_c]; split_ifs <;> simp)
  simpa [LevelData.Dr] using this

lemma pb_Drb (L : LevelData A r) (l : Fin r) : L.pb l * L.Drb = L.Drb * L.pb l + 1 * L.Drb := by
  have := shift_prod L.cb (L.pb l) (fun i => if l = i then (1 : ℂ) else 0) (fun i => by
    rw [L.pb_cb]; split_ifs <;> simp)
  simpa [LevelData.Drb] using this

end Formalism.FourierDecayAlt.P.RuleGD

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

theorem gaugeConjugation : Formalism.FourierDecayAlt.R.RuleG := by
  intro A _ _ r L s Gs Gsi h1 h2 hf hp hpb hnab hnabs Y
  have hfx : ∀ x ∈ L.fns, cj Gs Gsi h1 h2 x = x := fun x hx => cj_fix Gs Gsi h1 h2 (hf x hx)
  have hpφ : ∀ l, cj Gs Gsi h1 h2 (L.p l) = L.p l + algebraMap ℂ A s := by
    intro l; rw [cj_of_eq Gs Gsi h1 h2 (hp l), cj_alg]
  have hpbφ : ∀ l, cj Gs Gsi h1 h2 (L.pb l) = L.pb l + algebraMap ℂ A s := by
    intro l; rw [cj_of_eq Gs Gsi h1 h2 (hpb l), cj_alg]
  have hnabφ : cj Gs Gsi h1 h2 L.nab = L.nab + algebraMap ℂ A s * (L.ζb * L.GGi) - 0 := by
    rw [sub_zero, cj_of_eq Gs Gsi h1 h2 (a := algebraMap ℂ A s * (L.ζb * L.GGi))
      (by rw [hnab]; simp only [mul_assoc]), map_mul, map_mul, cj_alg, hfx _ (m_ζb L),
      hfx _ (m_GGi L)]
  have hnabsφ : cj Gs Gsi h1 h2 L.nabs = L.nabs - algebraMap ℂ A s * (L.ζ * L.GGi) - 0 := by
    rw [sub_zero, cj_of_eq Gs Gsi h1 h2 (a := -(algebraMap ℂ A s * (L.ζ * L.GGi)))
      (by rw [hnabs, sub_eq_add_neg, neg_mul]; simp only [mul_assoc]), map_neg, map_mul,
      map_mul, cj_alg, hfx _ (m_ζ L), hfx _ (m_GGi L), sub_eq_add_neg]
  obtain ⟨a1, a2⟩ := keyA L (cj Gs Gsi h1 h2) s 0 (cj_alg Gs Gsi h1 h2) hpφ
    (fun l => hfx _ (m_c L l)) (fun l => hfx _ (m_ci L l)) (fun l => hfx _ (m_cb L l))
    (hfx _ (m_GG L)) (hfx _ (m_ζb L)) (hfx _ (m_GGi L)) hnabφ Y
  obtain ⟨b1, b2⟩ := keyV L (cj Gs Gsi h1 h2) s 0 (cj_alg Gs Gsi h1 h2) hpbφ
    (fun l => hfx _ (m_cb L l)) (fun l => hfx _ (m_cbi L l)) (fun l => hfx _ (m_c L l))
    (hfx _ (m_GG L)) (hfx _ (m_ζ L)) (hfx _ (m_GGi L)) hnabsφ Y
  rw [mul_zero, zero_mul, add_zero] at a2 b2
  exact ⟨a1, a2, b1, b2⟩

theorem shiftConjugation : Formalism.FourierDecayAlt.R.RuleD := by
  intro A _ _ r L Y

  set ψ1 := cj L.Dr L.Dri (Dr_Dri L) (Dri_Dr L)
  set ψ2 := cj L.ζ L.ζi L.ζ_ζi L.ζi_ζ
  have hφ : ∀ x, (ψ2.comp ψ1) x = L.Di * x * L.D := by
    intro x; simp only [ψ1, ψ2, RingHom.comp_apply, cj_apply, LevelData.Di, LevelData.D, mul_assoc]
  have f1 : ∀ x ∈ L.fns, ψ1 x = x := fun x hx => cj_fix _ _ _ _ (fns_Dr L hx)
  have f2 : ∀ x ∈ L.fns, ψ2 x = x := fun x hx => cj_fix _ _ _ _ (fc L hx (m_ζ L))
  have f12 : ∀ x ∈ L.fns, (ψ2.comp ψ1) x = x := fun x hx => by
    rw [RingHom.comp_apply, f1 x hx, f2 x hx]
  have hal : ∀ z, (ψ2.comp ψ1) (algebraMap ℂ A z) = algebraMap ℂ A z := fun z => by
    rw [RingHom.comp_apply, cj_alg, cj_alg]
  have hp : ∀ l, (ψ2.comp ψ1) (L.p l) = L.p l + algebraMap ℂ A 1 := fun l => by
    rw [RingHom.comp_apply, cj_of_eq _ _ _ _ (p_Dr L l), map_one, map_add, map_one,
      cj_fix _ _ _ _ (L.p_ζ l), map_one]
  have hnab : (ψ2.comp ψ1) L.nab = L.nab + algebraMap ℂ A 1 * (L.ζb * L.GGi)
      - (L.ζb * L.GGi - L.ζi) := by
    have e1 : ψ1 L.nab = L.nab := cj_fix _ _ _ _ (comm_Dr L L.nab_c)
    have e2 : ψ2 L.nab = L.nab + L.ζi := by
      rw [cj_of_eq _ _ _ _ (a := L.ζi) (by rw [L.nab_ζ, L.ζi_ζ]), f2 _ (m_ζi L)]
    rw [RingHom.comp_apply, e1, e2, map_one, one_mul]
    abel
  obtain ⟨a1, a2⟩ := keyA L (ψ2.comp ψ1) 1 (L.ζb * L.GGi - L.ζi) hal hp
    (fun l => f12 _ (m_c L l)) (fun l => f12 _ (m_ci L l)) (fun l => f12 _ (m_cb L l))
    (f12 _ (m_GG L)) (f12 _ (m_ζb L)) (f12 _ (m_GGi L)) hnab Y
  rw [hφ] at a1 a2

  set χ1 := cj L.Drb L.Drbi (Drb_Drbi L) (Drbi_Drb L)
  set χ2 := cj L.ζb L.ζbi L.ζb_ζbi L.ζbi_ζb
  have hχ : ∀ x, (χ2.comp χ1) x = L.Dbi * x * L.Db := by
    intro x; simp only [χ1, χ2, RingHom.comp_apply, cj_apply, LevelData.Dbi, LevelData.Db, mul_assoc]
  have g1 : ∀ x ∈ L.fns, χ1 x = x := fun x hx => cj_fix _ _ _ _ (fns_Drb L hx)
  have g2 : ∀ x ∈ L.fns, χ2 x = x := fun x hx => cj_fix _ _ _ _ (fc L hx (m_ζb L))
  have g12 : ∀ x ∈ L.fns, (χ2.comp χ1) x = x := fun x hx => by
    rw [RingHom.comp_apply, g1 x hx, g2 x hx]
  have hal' : ∀ z, (χ2.comp χ1) (algebraMap ℂ A z) = algebraMap ℂ A z := fun z => by
    rw [RingHom.comp_apply, cj_alg, cj_alg]
  have hpb : ∀ l, (χ2.comp χ1) (L.pb l) = L.pb l + algebraMap ℂ A 1 := fun l => by
    rw [RingHom.comp_apply, cj_of_eq _ _ _ _ (pb_Drb L l), map_one, map_add, map_one,
      cj_fix _ _ _ _ (L.pb_ζb l), map_one]
  have hnabs : (χ2.comp χ1) L.nabs = L.nabs - algebraMap ℂ A 1 * (L.ζ * L.GGi)
      - (L.ζbi - L.ζ * L.GGi) := by
    have e1 : χ1 L.nabs = L.nabs := cj_fix _ _ _ _ (comm_Drb L L.nabs_cb)
    have e2 : χ2 L.nabs = L.nabs + -L.ζbi := by
      rw [cj_of_eq _ _ _ _ (a := -L.ζbi) (by rw [L.nabs_ζb, neg_mul, L.ζbi_ζb, sub_eq_add_neg]), map_neg, g2 _ (m_ζbi L)]
    rw [RingHom.comp_apply, e1, e2, map_one, one_mul]
    abel
  obtain ⟨b1, b2⟩ := keyV L (χ2.comp χ1) 1 (L.ζbi - L.ζ * L.GGi) hal' hpb
    (fun l => g12 _ (m_cb L l)) (fun l => g12 _ (m_cbi L l)) (fun l => g12 _ (m_c L l))
    (g12 _ (m_GG L)) (g12 _ (m_ζ L)) (g12 _ (m_GGi L)) hnabs Y
  rw [hχ] at b1 b2

  have s1 : L.GG * (L.ζb * L.GGi - L.ζi) = algebraMap ℂ A L.TT * L.ζi := by
    rw [mul_sub, ← mul_assoc, fc L (m_GG L) (m_ζb L), mul_assoc, L.GG_GGi, mul_one, L.GG_def,
      sub_mul, mul_assoc, fc L (m_ζb L) (m_ζi L), ← mul_assoc, L.ζ_ζi, one_mul, sub_sub_cancel]
  have s2 : L.GG * (L.ζbi - L.ζ * L.GGi) = -(algebraMap ℂ A L.TT * L.ζbi) := by
    rw [mul_sub, ← mul_assoc, fc L (m_GG L) (m_ζ L), mul_assoc, L.GG_GGi, mul_one, L.GG_def,
      sub_mul, mul_assoc, L.ζb_ζbi, mul_one, sub_sub_cancel_left]
  have t1 : L.Drb * L.GG * (L.ζb * L.GGi - L.ζi) * L.Ar (Y + 1)
      = algebraMap ℂ A L.TT * (L.Drb * L.Di * L.Ahat (Y + 1)) := by
    rw [mul_assoc L.Drb, s1, LevelData.Di, LevelData.Ahat]
    have h3 : L.Drb * (L.ζi * L.Dri) * (L.Dr * L.Ar (Y + 1)) = L.Drb * (L.ζi * L.Ar (Y + 1)) := by
      simp only [mul_assoc]; rw [← mul_assoc L.Dri, Dri_Dr, one_mul]
    rw [h3, Algebra.left_comm]; simp only [mul_assoc]
  have t2 : L.Dr * L.GG * (L.ζbi - L.ζ * L.GGi) * L.Avr (Y - 1)
      = -(algebraMap ℂ A L.TT * (L.Dr * L.Dbi * L.Ahatv (Y - 1))) := by
    rw [mul_assoc L.Dr, s2, LevelData.Dbi, LevelData.Ahatv]
    have h3 : L.Dr * (L.ζbi * L.Drbi) * (L.Drb * L.Avr (Y - 1)) = L.Dr * (L.ζbi * L.Avr (Y - 1)) := by
      simp only [mul_assoc]; rw [← mul_assoc L.Drbi, Drbi_Drb, one_mul]
    rw [h3, mul_neg, neg_mul, Algebra.left_comm]; simp only [mul_assoc]
  refine ⟨a1, a2.trans (by rw [t1]), b1, b2.trans (by rw [t2]; exact (sub_eq_add_neg _ _).symm), ?_, ?_⟩
  · rintro x ((⟨l, rfl⟩ | ⟨l, rfl⟩) | rfl | rfl)
    · exact commA L _ _ (L.cb_cbi l) (L.cbi_cb l) (fun m => L.p_cb m l)
        (fun y hy => fc L hy (m_cb L l)) (L.nab_cb l) Y
    · exact commA L _ _ (L.cbi_cb l) (L.cb_cbi l) (fun m => L.p_cbi m l)
        (fun y hy => fc L hy (m_cbi L l)) (L.nab_cbi l) Y
    · exact commA L _ _ L.ζb_ζbi L.ζbi_ζb (fun m => L.p_ζb m)
        (fun y hy => fc L hy (m_ζb L)) L.nab_ζb Y
    · exact commA L _ _ L.ζbi_ζb L.ζb_ζbi (fun m => L.p_ζbi m)
        (fun y hy => fc L hy (m_ζbi L)) L.nab_ζbi Y
  · rintro x ((⟨l, rfl⟩ | ⟨l, rfl⟩) | rfl | rfl)
    · exact commV L _ _ (L.c_ci l) (L.ci_c l) (fun m => L.pb_c m l)
        (fun y hy => fc L hy (m_c L l)) (L.nabs_c l) Y
    · exact commV L _ _ (L.ci_c l) (L.c_ci l) (fun m => L.pb_ci m l)
        (fun y hy => fc L hy (m_ci L l)) (L.nabs_ci l) Y
    · exact commV L _ _ L.ζ_ζi L.ζi_ζ (fun m => L.pb_ζ m)
        (fun y hy => fc L hy (m_ζ L)) L.nabs_ζ Y
    · exact commV L _ _ L.ζi_ζ L.ζ_ζi (fun m => L.pb_ζi m)
        (fun y hy => fc L hy (m_ζi L)) L.nabs_ζi Y

end Formalism.FourierDecayAlt.P
