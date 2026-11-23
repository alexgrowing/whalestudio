import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD
import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.TieAlg

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ}

def hats (L : LevelData A r) : Set A :=
  Set.range L.Ahat ∪ Set.range L.R0 ∪ Set.range L.Ahatv ∪ Set.range L.R0v

def NFs (L : LevelData A r) (B : Subalgebra ℂ A) (P : A) (n : ℕ) : Submodule ℂ A :=
  Submodule.span ℂ {x | ∃ b ∈ B, ∃ h : List A, h.length = n ∧ (∀ a ∈ h, a ∈ hats L) ∧ x = b * P * h.prod}

structure NFHypA (L : LevelData A r) (st : Start A) (B K : Subalgebra ℂ A) : Prop where
  starB : ∀ b ∈ B, star b ∈ B
  starK : ∀ b ∈ K, star b ∈ K
  le : K ≤ B
  fn : ∀ b ∈ B, ∀ f ∈ L.fns, Commute b f
  ζi : L.ζi ∈ B
  ζbi : L.ζbi ∈ B
  DDb : L.D * L.Dbi ∈ B
  DbD : L.Db * L.Di ∈ B
  x : ∀ Y, st.x Y ∈ K
  xi : ∀ Y, st.xi Y ∈ K
  ee : ∀ Y, st.ee Y ∈ B
  nabs : ∀ b ∈ K, Commute b L.nabs
  hat : ∀ X ∈ hats L, ∀ b ∈ B, X * b ∈ NFs L B 1 1

section fns

omit [StarRing A]

variable (L : LevelData A r)

theorem comm_cl {z : A} (hz : ∀ f ∈ L.fns, Commute z f) {y : A} (hy : y ∈ Subring.closure L.fns) : Commute z y := by
  induction hy using Subring.closure_induction with
  | mem x hx => exact hz x hx
  | zero => exact Commute.zero_right _
  | one => exact Commute.one_right _
  | add x y _ _ hx hy => exact hx.add_right hy
  | neg x _ hx => exact hx.neg_right
  | mul x y _ _ hx hy => exact hx.mul_right hy

theorem cl_comm {x y : A} (hx : x ∈ Subring.closure L.fns) (hy : y ∈ Subring.closure L.fns) : Commute x y :=
  comm_cl L (fun _ hf => (comm_cl L (fun _ hg => fc L hf hg) hx).symm) hy

theorem clF {x : A} (hx : x ∈ L.fns) : x ∈ Subring.closure L.fns := Subring.subset_closure hx

theorem clProd (f : Fin r → A) (hf : ∀ l, f l ∈ L.fns) : (List.ofFn f).prod ∈ Subring.closure L.fns :=
  Subring.list_prod_mem _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
    exact clF L (hf l)

theorem cζ : L.ζ ∈ Subring.closure L.fns := clF L (m_ζ L)
theorem cζi : L.ζi ∈ Subring.closure L.fns := clF L (m_ζi L)
theorem cζb : L.ζb ∈ Subring.closure L.fns := clF L (m_ζb L)
theorem cζbi : L.ζbi ∈ Subring.closure L.fns := clF L (m_ζbi L)
theorem cGG : L.GG ∈ Subring.closure L.fns := clF L (m_GG L)
theorem cGGi : L.GGi ∈ Subring.closure L.fns := clF L (m_GGi L)
theorem cDr : L.Dr ∈ Subring.closure L.fns := clProd L _ (m_c L)
theorem cDri : L.Dri ∈ Subring.closure L.fns := clProd L _ (m_ci L)
theorem cDrb : L.Drb ∈ Subring.closure L.fns := clProd L _ (m_cb L)
theorem cDrbi : L.Drbi ∈ Subring.closure L.fns := clProd L _ (m_cbi L)
theorem cD : L.D ∈ Subring.closure L.fns := Subring.mul_mem _ (cDr L) (cζ L)
theorem cDi : L.Di ∈ Subring.closure L.fns := Subring.mul_mem _ (cζi L) (cDri L)
theorem cDb : L.Db ∈ Subring.closure L.fns := Subring.mul_mem _ (cDrb L) (cζb L)
theorem cDbi : L.Dbi ∈ Subring.closure L.fns := Subring.mul_mem _ (cζbi L) (cDrbi L)

theorem D_Di : L.D * L.Di = 1 := by
  rw [LevelData.D, LevelData.Di, mul_assoc, ← mul_assoc L.ζ, L.ζ_ζi, one_mul, Dr_Dri]

theorem Di_Dr : L.Di * L.Dr = L.ζi := by rw [LevelData.Di, mul_assoc, Dri_Dr, mul_one]

theorem Dbi_Drb : L.Dbi * L.Drb = L.ζbi := by rw [LevelData.Dbi, mul_assoc, Drbi_Drb, mul_one]

theorem Dbi_eq : L.D * L.Dbi * L.Di = L.Dbi := by
  rw [mul_assoc, (cl_comm L (cDbi L) (cDi L)).eq, ← mul_assoc, D_Di, one_mul]

theorem Drb_Di : L.Drb * L.Di = L.ζbi * (L.Db * L.Di) := by
  rw [LevelData.Db, (cl_comm L (cDrb L) (cζb L)).eq, ← mul_assoc, ← mul_assoc, L.ζbi_ζb, one_mul]

theorem f5 : L.ζbi * L.GG * (L.ζb * L.ζi * L.GGi) = L.ζi := by
  have h1 := (cl_comm L (cGG L) (Subring.mul_mem _ (cζb L) (cζi L))).eq
  calc L.ζbi * L.GG * (L.ζb * L.ζi * L.GGi) = L.ζbi * (L.GG * (L.ζb * L.ζi)) * L.GGi := by simp only [mul_assoc]
    _ = L.ζbi * L.ζb * L.ζi * (L.GG * L.GGi) := by rw [h1]; simp only [mul_assoc]
    _ = L.ζi := by rw [L.ζbi_ζb, L.GG_GGi, one_mul, mul_one]

theorem f6 : L.ζi * L.GG * (L.GGi * (L.ζbi * L.ζ)) = L.ζbi := by
  rw [mul_assoc, ← mul_assoc L.GG, L.GG_GGi, one_mul, (cl_comm L (cζbi L) (cζ L)).eq, ← mul_assoc, L.ζi_ζ, one_mul]

theorem f7 : L.ζi * L.GG * (L.ζbi * L.GGi) = L.ζi * L.ζbi := by
  rw [mul_assoc, (cl_comm L (cζbi L) (cGGi L)).eq, ← mul_assoc L.GG, L.GG_GGi, one_mul]

theorem W_inv_mul_W : (L.GG * L.ζi * L.ζbi) * (L.ζ * L.ζb * L.GGi) = 1 := by
  have h1 := (cl_comm L (cζbi L) (cζ L)).eq
  calc (L.GG * L.ζi * L.ζbi) * (L.ζ * L.ζb * L.GGi) = L.GG * L.ζi * (L.ζbi * L.ζ) * L.ζb * L.GGi := by
        simp only [mul_assoc]
    _ = L.GG * (L.ζi * L.ζ) * (L.ζbi * L.ζb) * L.GGi := by rw [h1]; simp only [mul_assoc]
    _ = 1 := by rw [L.ζi_ζ, L.ζbi_ζb, mul_one, mul_one, L.GG_GGi]

theorem cW : L.ζ * L.ζb * L.GGi ∈ Subring.closure L.fns :=
  Subring.mul_mem _ (Subring.mul_mem _ (cζ L) (cζb L)) (cGGi L)

theorem cWi : L.GG * L.ζi * L.ζbi ∈ Subring.closure L.fns :=
  Subring.mul_mem _ (Subring.mul_mem _ (cGG L) (cζi L)) (cζbi L)

theorem Wi_W_pow (n : ℕ) : (L.GG * L.ζi * L.ζbi) ^ n * (L.ζ * L.ζb * L.GGi) ^ n = 1 := by
  rw [← (cl_comm L (cWi L) (cW L)).mul_pow, W_inv_mul_W, one_pow]

theorem nabs_alt_alt : L.nabs * (L.ζ * L.ζb * L.GGi) =
    (L.ζ * L.ζb * L.GGi) * (L.nabs + L.TT • (L.ζbi * L.GGi)) := by
  have hz : L.ζ * L.ζb = L.GG + algebraMap ℂ A L.TT := by rw [L.GG_def, sub_add_cancel]
  have e1 : L.nabs * (L.ζ * L.ζb * L.GGi) = L.nabs + L.TT • (L.nabs * L.GGi) := by
    rw [hz, add_mul, L.GG_GGi, mul_add, mul_one, ← Algebra.smul_def, mul_smul_comm]
  have e2 : L.ζ * L.ζb * L.GGi = 1 + L.TT • L.GGi := by rw [hz, add_mul, L.GG_GGi, ← Algebra.smul_def]
  have e3 : (L.ζ * L.ζb * L.GGi) * (L.ζbi * L.GGi) = L.ζ * L.GGi * L.GGi := by
    have h1 := (cl_comm L (cGGi L) (cζbi L)).eq
    calc (L.ζ * L.ζb * L.GGi) * (L.ζbi * L.GGi) = L.ζ * L.ζb * (L.GGi * L.ζbi) * L.GGi := by simp only [mul_assoc]
      _ = L.ζ * (L.ζb * L.ζbi) * L.GGi * L.GGi := by rw [h1]; simp only [mul_assoc]
      _ = _ := by rw [L.ζb_ζbi, mul_one]
  rw [e1, mul_add, mul_smul_comm, e3, L.nabs_GGi, smul_add, ← add_assoc]
  congr 1
  rw [e2, add_mul, one_mul, smul_mul_assoc]

theorem m0_mul_W (Y c : ℂ) : (L.m0 Y - c • (L.ζbi * L.GGi)) * (L.ζ * L.ζb * L.GGi) =
    (L.ζ * L.ζb * L.GGi) * (L.m0 Y - (c + L.TT) • (L.ζbi * L.GGi)) := by
  have h1 := (cl_comm L (Subring.mul_mem _ (cζ L) (cGGi L)) (cW L)).eq
  have h2 := (cl_comm L (Subring.mul_mem _ (cζbi L) (cGGi L)) (cW L)).eq
  simp only [LevelData.m0, ← Algebra.smul_def, sub_mul, mul_sub, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm,
    nabs_alt_alt, h1, h2, mul_add, add_smul]
  abel

theorem m0_mul_W_pow (Y : ℂ) (n : ℕ) : L.m0 Y * (L.ζ * L.ζb * L.GGi) ^ n =
    (L.ζ * L.ζb * L.GGi) ^ n * (L.m0 Y - ((n : ℂ) * L.TT) • (L.ζbi * L.GGi)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, m0_mul_W, ← mul_assoc]
    congr 3
    push_cast; ring

end fns

section spans

variable {L : LevelData A r} {B : Subalgebra ℂ A}

omit [StarRing A] in
theorem nfs_gen {P : A} {n : ℕ} {b : A} (hb : b ∈ B) {h : List A} (hl : h.length = n) (hh : ∀ a ∈ h, a ∈ hats L) :
    b * P * h.prod ∈ NFs L B P n := Submodule.subset_span ⟨b, hb, h, hl, hh, rfl⟩

omit [StarRing A] in
theorem nfs_one {P : A} {b : A} (hb : b ∈ B) {X : A} (hX : X ∈ hats L) : b * P * X ∈ NFs L B P 1 := by
  have := nfs_gen (L := L) (P := P) hb (h := [X]) rfl (by simpa using hX)
  simpa using this

omit [StarRing A] in
theorem nfs_left {P : A} {n : ℕ} {b : A} (hb : b ∈ B) {x : A} (hx : x ∈ NFs L B P n) : b * x ∈ NFs L B P n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b', hb', h, hl, hh, rfl⟩ := hx
    have := nfs_gen (L := L) (P := P) (B.mul_mem hb hb') hl hh
    simpa only [mul_assoc] using this
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

omit [StarRing A] in

theorem nfs_mul_gen {P Q : A} {n : ℕ} (hP : ∀ b ∈ B, Commute b P)
    (hQ : ∀ X ∈ hats L, ∀ b ∈ B, X * (b * Q) ∈ NFs L B Q 1) {x y : A} (hx : x ∈ NFs L B P 1) (hy : y ∈ NFs L B Q n) :
    x * y ∈ NFs L B (P * Q) (n + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, h, hl, hh, rfl⟩ := hx
    obtain ⟨X, rfl⟩ := List.length_eq_one_iff.1 hl
    have hX : X ∈ hats L := hh X (by simp)
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b', hb', h', hl', hh', rfl⟩ := hy
      have key : ∀ z ∈ NFs L B Q 1, b * P * z * h'.prod ∈ NFs L B (P * Q) (n + 1) := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨b'', hb'', h'', hl'', hh'', rfl⟩ := hz
          have := nfs_gen (L := L) (P := P * Q) (B.mul_mem hb hb'') (h := h'' ++ h') (n := n + 1)
            (by rw [List.length_append, hl'', hl', add_comm])
            (fun a ha => (List.mem_append.1 ha).elim (hh'' a) (hh' a))
          convert this using 1
          rw [List.prod_append]
          have e := (hP b'' hb'').eq
          calc b * P * (b'' * Q * h''.prod) * h'.prod = b * (P * b'') * Q * (h''.prod * h'.prod) := by
                simp only [mul_assoc]
            _ = _ := by rw [← e]; simp only [mul_assoc]
        | zero => rw [mul_zero, zero_mul]; exact Submodule.zero_mem _
        | add x y _ _ hx hy => rw [mul_add, add_mul]; exact Submodule.add_mem _ hx hy
        | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
      have := key _ (hQ X hX b' hb')
      simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using this
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

omit [StarRing A] in

theorem nfs_pass {P Q : A} (hP : ∀ b ∈ B, Commute b P) (hQ : ∀ X ∈ hats L, X * Q ∈ NFs L B Q 1) {x : A}
    (hx : x ∈ NFs L B P 1) : x * Q ∈ NFs L B (P * Q) 1 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, h, hl, hh, rfl⟩ := hx
    obtain ⟨X, rfl⟩ := List.length_eq_one_iff.1 hl
    have key : ∀ z ∈ NFs L B Q 1, b * P * z ∈ NFs L B (P * Q) 1 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨b'', hb'', h'', hl'', hh'', rfl⟩ := hz
        have := nfs_gen (L := L) (P := P * Q) (B.mul_mem hb hb'') hl'' hh''
        convert this using 1
        have e := (hP b'' hb'').eq
        calc b * P * (b'' * Q * h''.prod) = b * (P * b'') * Q * h''.prod := by simp only [mul_assoc]
          _ = _ := by rw [← e]; simp only [mul_assoc]
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
    have := key _ (hQ X (hh X (by simp)))
    simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using this
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

omit [StarRing A] in
theorem mA (y : ℂ) : L.Ahat y ∈ hats L := Or.inl (Or.inl (Or.inl ⟨y, rfl⟩))
omit [StarRing A] in
theorem mR (y : ℂ) : L.R0 y ∈ hats L := Or.inl (Or.inl (Or.inr ⟨y, rfl⟩))
omit [StarRing A] in
theorem mAv (y : ℂ) : L.Ahatv y ∈ hats L := Or.inl (Or.inr ⟨y, rfl⟩)
omit [StarRing A] in
theorem mRv (y : ℂ) : L.R0v y ∈ hats L := Or.inr ⟨y, rfl⟩

end spans

section main

variable {L : LevelData A r} {st : Start A} {B K : Subalgebra ℂ A} (H : NFHypA L st B K)
include H

theorem NFHypA.cl {b : A} (hb : b ∈ B) {y : A} (hy : y ∈ Subring.closure L.fns) : Commute b y :=
  comm_cl L (H.fn b hb) hy

theorem hat_Di (X : A) (hX : X ∈ hats L) : X * L.Di ∈ NFs L B L.Di 1 := by
  have hA : ∀ y, L.Ahat y * L.Di = L.Di * L.Ahat (y - 1) := fun y => by
    have h := (shiftConjugation A r L (y - 1)).1
    rw [sub_add_cancel] at h
    rw [← h, mul_assoc, D_Di, mul_one]
  have hv : ∀ Z : A, (∀ x ∈ Set.range L.c ∪ Set.range L.ci ∪ {L.ζ, L.ζi}, x * Z = Z * x) → Z * L.Di = L.Di * Z :=
    fun Z hZ => by
      have h1 : Commute Z L.ζi := (hZ _ (by simp)).symm
      have h2 : Commute Z L.Dri := comm_prod L.ci Z fun l => (hZ _ (by simp)).symm
      exact (h1.mul_right h2).eq
  rcases hX with (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)
  · rw [hA]; simpa using nfs_one (P := L.Di) B.one_mem (mA (L := L) (y - 1))
  · have h := (shiftConjugation A r L (y - 1)).2.1
    rw [sub_add_cancel] at h
    have e : L.R0 y * L.Di = 1 * L.Di * L.R0 (y - 1) - L.TT • (L.ζbi * (L.Db * L.Di) * L.Di * L.Ahat (y - 1)) := by
      have e1 : L.R0 y = L.Di * L.R0 (y - 1) * L.D - L.TT • (L.Drb * L.Di * L.Ahat y) := by
        rw [h, ← Algebra.smul_def, add_sub_cancel_right]
      rw [e1, sub_mul, mul_assoc _ L.D, D_Di, mul_one, one_mul, smul_mul_assoc, mul_assoc _ (L.Ahat y), hA, Drb_Di]
      simp only [mul_assoc]
    rw [e]
    exact Submodule.sub_mem _ (nfs_one B.one_mem (mR _))
      (Submodule.smul_mem _ _ (nfs_one (B.mul_mem H.ζbi H.DbD) (mA _)))
  · rw [hv _ fun x hx => ((shiftConjugation A r L y).2.2.2.2.2 x hx).1]
    simpa using nfs_one (P := L.Di) B.one_mem (mAv (L := L) y)
  · rw [hv _ fun x hx => ((shiftConjugation A r L y).2.2.2.2.2 x hx).2]
    simpa using nfs_one (P := L.Di) B.one_mem (mRv (L := L) y)

theorem hat_Dipow (n : ℕ) : ∀ X ∈ hats L, X * L.Di ^ n ∈ NFs L B (L.Di ^ n) 1 := by
  induction n with
  | zero => intro X hX; simpa using nfs_one (P := 1) B.one_mem hX
  | succ n ih =>
    intro X hX
    rw [pow_succ, ← mul_assoc]
    exact nfs_pass (fun b hb => (H.cl hb (cDi L)).pow_right n) (hat_Di H) (ih X hX)

theorem nfs_step {n : ℕ} {x y : A} (hx : x ∈ NFs L B L.Di 1) (hy : y ∈ NFs L B (L.Di ^ n) n) :
    x * y ∈ NFs L B (L.Di ^ (n + 1)) (n + 1) := by
  rw [pow_succ']
  refine nfs_mul_gen (fun b hb => H.cl hb (cDi L)) (fun X hX b hb => ?_) hx hy
  rw [← mul_assoc]
  have := nfs_pass (P := 1) (fun b _ => Commute.one_right b) (hat_Dipow H n) (H.hat X hX b hb)
  rwa [one_mul] at this

end main

def memRel (B : Subalgebra ℂ A) (hB : ∀ b ∈ B, star b ∈ B) : SRel A A where
  r a _ := a ∈ B
  zero := B.zero_mem
  one := B.one_mem
  add h h' := B.add_mem h h'
  mul h h' := B.mul_mem h h'
  smul c _ _ h := B.smul_mem h c
  star h := hB _ h

section frames

variable [StarModule ℂ A] {S : Type} [Fintype S] [DecidableEq S]
variable {L : LevelData A r} {st : Start A} {B K : Subalgebra ℂ A} (H : NFHypA L st B K)
include H

omit [StarModule ℂ A] in
theorem frame_mem (w : List (Letter ℂ S)) :
    (∀ Y i j, (ofWord L st w).x Y i j ∈ K) ∧ (∀ Y i j, (ofWord L st w).xi Y i j ∈ K) ∧
    (∀ i j, (ofWord L st w).c i j ∈ K) ∧ (∀ i j, (ofWord L st w).ci i j ∈ K) ∧
    ∀ Y i j, (ofWord L st w).ee Y i j ∈ B := by
  let RK := (memRel K H.starK).mat (Ix S)
  let RB := (memRel B H.starB).mat (Ix S)
  have toK : ∀ {M : SlopeTestRemainingChoices S A}, (∀ i j, M i j ∈ K) → RK.r M M := fun h => h
  have toB : ∀ {M : SlopeTestRemainingChoices S A}, (∀ i j, M i j ∈ B) → RB.r M M := fun h => h
  have KB : ∀ {M : SlopeTestRemainingChoices S A}, (∀ i j, M i j ∈ K) → RB.r M M := fun h i j => H.le (h i j)
  have ofK : ∀ {M M' : SlopeTestRemainingChoices S A}, RK.r M M' → ∀ i j, M i j ∈ K := fun h => h
  have ofB : ∀ {M M' : SlopeTestRemainingChoices S A}, RB.r M M' → ∀ i j, M i j ∈ B := fun h => h
  have tzB : RB.r (tz L) (tz L) := SRel.io (R := memRel B H.starB) (x' := L.TT • L.ζbi) (B.smul_mem H.ζbi _)
  induction w with
  | nil =>
    exact ⟨fun Y => ofK (SRel.io (R := memRel K H.starK) (x' := st.x Y) (H.x Y)),
      fun Y => ofK (SRel.io (R := memRel K H.starK) (x' := st.x Y) (H.xi Y)), ofK RK.one, ofK RK.one,
      fun Y => ofB (SRel.io (R := memRel B H.starB) (x' := st.x Y) (H.ee Y))⟩
  | cons l w ih =>
    obtain ⟨hx, hxi, hc, hci, hee⟩ := ih
    have z := RK.zero
    have o := RK.one
    have hDD : ∀ Y Ya, RB.r ((ofWord L st w).DD Y Ya) ((ofWord L st w).DD Y Ya) := fun Y Ya =>
      RB.smul _ (SRel.sub (toB (hee Y)) (toB (hee Ya)))
    by_cases hp : l.plus = true
    · simp only [ofWord, hp, if_true, FrameData.plus]
      exact ⟨fun Y => ofK (RK.mul (toK (hx Y)) (SRel.ins _ (SRel.m2 (RK.smul _ o) z z o))),
        fun Y => ofK (RK.mul (toK (hxi Y)) (SRel.ins _ (SRel.m2 (RK.smul _ o) z z o))),
        ofK (RK.mul (toK hc) (SRel.ins _ (SRel.m2 (RK.smul _ (toK (hxi _))) z z (toK (hx _))))),
        ofK (RK.mul (toK hci) (SRel.ins _ (SRel.m2 (RK.smul _ (toK (hx _))) z z (toK (hxi _))))),
        fun Y => ofB (SRel.ins _ (SRel.m2 (RB.add (SRel.sub (toB (hee Y)) (hDD _ _)) tzB) (SRel.neg (RB.smul _ RB.one))
          RB.zero (RB.mul (RB.mul (KB (hxi _)) (toB (hee Y))) (KB (hx _)))))⟩
    · simp only [ofWord, hp, FrameData.minus]
      exact ⟨fun Y => ofK (RK.mul (toK (hx Y)) (SRel.ins _ (SRel.m2 (RK.smul _ o) z z o))),
        fun Y => ofK (RK.mul (toK (hxi Y)) (SRel.ins _ (SRel.m2 (RK.smul _ o) z z o))),
        ofK (RK.mul (toK hc) (SRel.ins _ (SRel.m2 (RK.smul _ (toK (hxi _))) z z (toK (hx _))))),
        ofK (RK.mul (toK hci) (SRel.ins _ (SRel.m2 (RK.smul _ (toK (hx _))) z z (toK (hxi _))))),
        fun Y => ofB (SRel.ins _ (SRel.m2 (toB (hee Y)) RB.zero
          (SRel.neg (RB.smul _ (RB.mul (KB (hxi _)) (KB (hxi _)))))
          (RB.add (SRel.sub (RB.mul (RB.mul (KB (hxi _)) (toB (hee Y))) (KB (hx _))) (hDD _ _)) tzB)))⟩

end frames

section io

variable {S : Type} [Fintype S] [DecidableEq S]

omit [StarRing A] [Algebra ℂ A] in
theorem io_mul_apply (x : A) (M : SlopeTestRemainingChoices S A) (i j : Ix S) : ((io x : SlopeTestRemainingChoices S A) * M) i j = x * M i j := by
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_mul]

omit [StarRing A] [Algebra ℂ A] in
theorem mul_io_apply (x : A) (M : SlopeTestRemainingChoices S A) (i j : Ix S) : (M * (io x : SlopeTestRemainingChoices S A)) i j = M i j * x := by
  simp only [io, Matrix.scalar_apply, Matrix.mul_diagonal]

omit [StarRing A] [Algebra ℂ A] in
theorem comm_io {x : A} {M : SlopeTestRemainingChoices S A} (h : ∀ i j, Commute (M i j) x) : M * io x = io x * M := by
  ext i j
  rw [io_mul_apply, mul_io_apply, (h i j).eq]

omit [StarRing A] [Algebra ℂ A] in
theorem io_mul' (x y : A) : (io x : SlopeTestRemainingChoices S A) * io y = io (x * y) := by simp only [io, map_mul]

omit [StarRing A] [Algebra ℂ A] in
theorem io_add' (x y : A) : (io x : SlopeTestRemainingChoices S A) + io y = io (x + y) := by simp only [io, map_add]

omit [StarRing A] [Algebra ℂ A] in
theorem io_pow' (x : A) (n : ℕ) : (io x : SlopeTestRemainingChoices S A) ^ n = io (x ^ n) := by simp only [io, map_pow]

omit [Algebra ℂ A] in
theorem star_io' (x : A) : star (io x : SlopeTestRemainingChoices S A) = io (star x) := by
  ext i j
  simp only [io, Matrix.scalar_apply, Matrix.star_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

omit [StarRing A] in
theorem io_entry_mem (T : Submodule ℂ A) {x : A} (hx : x ∈ T) (i j : Ix S) : (io x : SlopeTestRemainingChoices S A) i j ∈ T := by
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact hx
  · exact T.zero_mem

end io

theorem ring_plus {R : Type} [Ring R] {a l k E x y z : R} (h : a * k = z) (h' : E * z = z * E) :
    a * ((l + k * E) * x + y) = a * (l * x + y) + E * (z * x) := by
  rw [← mul_assoc E, h', ← h]; noncomm_ring

theorem ring_minus {R : Type} [Ring R] {a l k E x y z : R} (h : a * k = z) (h' : E * a = a * E) :
    a * ((l + E * k) * x + y) = a * (l * x + y) + E * (z * x) := by
  rw [← h, ← mul_assoc E, ← mul_assoc E, h']; noncomm_ring

section letters

variable [StarModule ℂ A] {S : Type} [Fintype S] [DecidableEq S]
variable {L : LevelData A r} {st : Start A} {B K : Subalgebra ℂ A}

theorem star_facts (hS : IsStarLevel L) : star L.ζb = L.ζ ∧ star L.ζi = L.ζbi ∧ star L.GGi = L.GGi := by
  obtain ⟨h1, -, h3⟩ := hS
  have e1 : star L.ζb = L.ζ := by rw [← h1, star_star]
  have eG : star L.GG = L.GG := by
    rw [L.GG_def, star_sub, star_mul, h1, e1, ← algebraMap_star_comm, h3]
  refine ⟨e1, ?_, ?_⟩
  · calc star L.ζi = star L.ζi * (star L.ζ * L.ζbi) := by rw [h1, L.ζb_ζbi, mul_one]
      _ = L.ζbi := by rw [← mul_assoc, ← star_mul, L.ζ_ζi, star_one, one_mul]
  · calc star L.GGi = star L.GGi * (star L.GG * L.GGi) := by rw [eG, L.GG_GGi, mul_one]
      _ = L.GGi := by rw [← mul_assoc, ← star_mul, L.GG_GGi, star_one, one_mul]

theorem star_lowering_constant (hS : IsStarLevel L) {Y : ℂ} (hY : star Y = Y) : star (L.l0 (Y - 1)) = L.m0 Y := by
  obtain ⟨e1, -, e3⟩ := star_facts hS
  have e : star (Y - 1 + 1 / 2) = Y - 1 / 2 := by
    rw [star_add, star_sub, hY, star_one, star_div₀, star_one, star_ofNat]; ring
  rw [LevelData.l0, LevelData.m0, ← Algebra.smul_def, ← Algebra.smul_def, star_sub, star_neg, hS.2.1, star_smul, e,
    star_mul, e1, e3, (cl_comm L (cGGi L) (cζ L)).eq]

theorem m_form (H : NFHypA L st B K) (hS : IsStarLevel L) (w : List (Letter ℂ S)) (hf : IsFrame L (ofWord L st w))
    {Y : ℂ} (hY : star Y = Y) : ∃ (c : ℂ) (E : SlopeTestRemainingChoices S A), (∀ i j, E i j ∈ B) ∧
      (ofWord L st w).m L Y = io (L.m0 Y - c • (L.ζbi * L.GGi)) + E * io (L.GGi * (L.ζbi * L.ζ)) := by
  obtain ⟨-, -, hc, hci, hee⟩ := frame_mem H (S := S) w
  obtain ⟨e1, e2, e3⟩ := star_facts hS
  set f := ofWord L st w with hfdef
  let RB := (memRel B H.starB).mat (Ix S)
  have hE : RB.r (f.ci * star (f.ee (Y - 1)) * f.c) (f.ci * star (f.ee (Y - 1)) * f.c) :=
    RB.mul (RB.mul (fun i j => H.le (hci i j)) (RB.star (a' := f.ee (Y - 1)) (hee (Y - 1)))) fun i j => H.le (hc i j)
  have hse : ∀ i j, star (f.ee (Y - 1)) i j ∈ B := RB.star (a' := f.ee (Y - 1)) (hee (Y - 1))
  refine ⟨(f.N : ℂ) * L.TT, _, hE, ?_⟩
  have ck : L.GGi * (L.ζbi * L.ζ) ∈ Subring.closure L.fns :=
    Subring.mul_mem _ (cGGi L) (Subring.mul_mem _ (cζbi L) (cζ L))
  have sk : star (kapL L : SlopeTestRemainingChoices S A) = io (L.GGi * (L.ζbi * L.ζ)) := by
    rw [kapL, star_io', star_mul, star_mul, e1, e2, e3]
  have cX : f.c * io (L.m0 Y - ((f.N : ℂ) * L.TT) • (L.ζbi * L.GGi)) =
      io (L.m0 Y - ((f.N : ℂ) * L.TT) • (L.ζbi * L.GGi)) * f.c := comm_io fun i j => by
    have hb := H.le (hc i j)
    refine Commute.sub_right ?_ ((H.cl hb (Subring.mul_mem _ (cζbi L) (cGGi L))).smul_right _)
    rw [LevelData.m0, ← Algebra.smul_def]
    exact (H.nabs _ (hc i j)).neg_right.sub_right ((H.cl hb (Subring.mul_mem _ (cζ L) (cGGi L))).smul_right _)
  have ck' : f.c * io (L.GGi * (L.ζbi * L.ζ)) = io (L.GGi * (L.ζbi * L.ζ)) * f.c :=
    comm_io fun i j => H.cl (H.le (hc i j)) ck
  have cW' : star (f.ee (Y - 1)) * io ((L.GG * L.ζi * L.ζbi) ^ f.N) =
      io ((L.GG * L.ζi * L.ζbi) ^ f.N) * star (f.ee (Y - 1)) :=
    comm_io fun i j => (H.cl (hse i j) (cWi L)).pow_right _
  have p1 : (L.GG * L.ζi * L.ζbi) ^ f.N * L.m0 Y * (L.ζ * L.ζb * L.GGi) ^ f.N =
      L.m0 Y - ((f.N : ℂ) * L.TT) • (L.ζbi * L.GGi) := by
    rw [mul_assoc, m0_mul_W_pow, ← mul_assoc, Wi_W_pow, one_mul]
  have p2 : (L.GG * L.ζi * L.ζbi) ^ f.N * (L.GGi * (L.ζbi * L.ζ)) * (L.ζ * L.ζb * L.GGi) ^ f.N =
      L.GGi * (L.ζbi * L.ζ) := by
    rw [mul_assoc, ((cl_comm L ck (cW L)).pow_right _).eq, ← mul_assoc, Wi_W_pow, one_mul]
  rw [FrameData.m, FrameData.di, FrameData.d, FrameData.l, star_add, star_mul, star_io', star_lowering_constant hS hY, sk, wt, wti,
    io_pow', io_pow', mul_add, add_mul]
  congr 1
  · calc f.ci * io ((L.GG * L.ζi * L.ζbi) ^ f.N) * io (L.m0 Y) * (io ((L.ζ * L.ζb * L.GGi) ^ f.N) * f.c)
        = f.ci * (io ((L.GG * L.ζi * L.ζbi) ^ f.N) * io (L.m0 Y) * io ((L.ζ * L.ζb * L.GGi) ^ f.N) * f.c) := by
          simp only [mul_assoc]
      _ = _ := by rw [io_mul', io_mul', p1, ← cX, ← mul_assoc, hf.c_ci.2, one_mul]
  · calc f.ci * io ((L.GG * L.ζi * L.ζbi) ^ f.N) * (star (f.ee (Y - 1)) * io (L.GGi * (L.ζbi * L.ζ))) *
          (io ((L.ζ * L.ζb * L.GGi) ^ f.N) * f.c)
        = f.ci * (io ((L.GG * L.ζi * L.ζbi) ^ f.N) * star (f.ee (Y - 1))) * io (L.GGi * (L.ζbi * L.ζ)) *
          io ((L.ζ * L.ζb * L.GGi) ^ f.N) * f.c := by simp only [mul_assoc]
      _ = f.ci * star (f.ee (Y - 1)) * ((io ((L.GG * L.ζi * L.ζbi) ^ f.N) * io (L.GGi * (L.ζbi * L.ζ)) *
          io ((L.ζ * L.ζb * L.GGi) ^ f.N)) * f.c) := by rw [← cW']; simp only [mul_assoc]
      _ = _ := by rw [io_mul', io_mul', p2, ← ck']; simp only [mul_assoc]

theorem letter_mem (H : NFHypA L st B K) (hS : IsStarLevel L) (l : Letter ℂ S) (w : List (Letter ℂ S))
    (hf : IsFrame L (ofWord L st w)) (hY : star l.pt = l.pt) (i : Fin 2) (e e' : Ix S) :
    TL.letterCol L st l w i e e' ∈ NFs L B L.Di 1 := by
  have a1 : L.ζi * L.Ar l.pt ∈ NFs L B L.Di 1 := by
    have := nfs_one (L := L) (P := L.Di) B.one_mem (mA l.pt)
    rwa [one_mul, LevelData.Ahat, ← mul_assoc, Di_Dr] at this
  have a2 : L.ζbi * L.Avr l.pt ∈ NFs L B L.Di 1 := by
    have := nfs_one (L := L) (P := L.Di) H.DDb (mAv l.pt)
    rwa [Dbi_eq, LevelData.Ahatv, ← mul_assoc, Dbi_Drb] at this
  have a3 : L.ζbi * L.GG * (L.l0 l.pt * L.Ar l.pt + L.Br l.pt) ∈ NFs L B L.Di 1 := by
    have := nfs_one (L := L) (P := L.Di) H.DDb (mR l.pt)
    rwa [Dbi_eq, LevelData.R0, ← mul_assoc, ← mul_assoc, Dbi_Drb] at this
  have a4 : L.ζi * L.GG * (L.m0 l.pt * L.Avr l.pt + L.Bvr l.pt) ∈ NFs L B L.Di 1 := by
    have := nfs_one (L := L) (P := L.Di) B.one_mem (mRv l.pt)
    rwa [one_mul, LevelData.R0v, ← mul_assoc, ← mul_assoc, Di_Dr] at this
  unfold TL.letterCol
  by_cases hp : l.plus = true
  · rw [if_pos hp]
    fin_cases i
    · exact io_entry_mem _ a1 e e'
    · have hee := (frame_mem H (S := S) w).2.2.2.2 l.pt
      have e1 : io (L.ζbi * L.GG) * ((ofWord L st w).l L l.pt * io (L.Ar l.pt) + io (L.Br l.pt)) =
          io (L.ζbi * L.GG * (L.l0 l.pt * L.Ar l.pt + L.Br l.pt)) +
            (ofWord L st w).ee l.pt * io (L.ζi * L.Ar l.pt) := by
        rw [FrameData.l, kapL, ring_plus (z := io L.ζi) (by rw [io_mul', f5])
          (comm_io fun i j => H.cl (hee i j) (cζi L)), io_mul', io_add', io_mul', io_mul']
      show (io (L.ζbi * L.GG) * ((ofWord L st w).l L l.pt * io (L.Ar l.pt) + io (L.Br l.pt)) : SlopeTestRemainingChoices S A) e e' ∈ _
      rw [e1, Matrix.add_apply, mul_io_apply]
      exact Submodule.add_mem _ (io_entry_mem _ a3 e e') (nfs_left (hee e e') a1)
  · rw [if_neg hp]
    fin_cases i
    · exact io_entry_mem _ a2 e e'
    · obtain ⟨c, E, hE, hm⟩ := m_form H hS w hf hY
      have cE : E * io (L.ζi * L.GG) = io (L.ζi * L.GG) * E :=
        comm_io fun i j => H.cl (hE i j) (Subring.mul_mem _ (cζi L) (cGG L))
      have q1 : L.ζi * L.GG * ((L.m0 l.pt - c • (L.ζbi * L.GGi)) * L.Avr l.pt + L.Bvr l.pt) =
          L.ζi * L.GG * (L.m0 l.pt * L.Avr l.pt + L.Bvr l.pt) - c • (L.ζi * (L.ζbi * L.Avr l.pt)) := by
        rw [← mul_assoc L.ζi L.ζbi, ← f7 L]
        simp only [sub_mul, mul_sub, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]
        abel
      have e1 : io (L.ζi * L.GG) * ((ofWord L st w).m L l.pt * io (L.Avr l.pt) + io (L.Bvr l.pt)) =
          io (L.ζi * L.GG * ((L.m0 l.pt - c • (L.ζbi * L.GGi)) * L.Avr l.pt + L.Bvr l.pt)) +
            E * io (L.ζbi * L.Avr l.pt) := by
        rw [hm, ring_minus (z := io L.ζbi) (by rw [io_mul', f6]) cE, io_mul', io_add', io_mul', io_mul']
      show (io (L.ζi * L.GG) * ((ofWord L st w).m L l.pt * io (L.Avr l.pt) + io (L.Bvr l.pt)) : SlopeTestRemainingChoices S A) e e' ∈ _
      rw [e1, Matrix.add_apply, mul_io_apply, q1]
      exact Submodule.add_mem _
        (io_entry_mem _ (Submodule.sub_mem _ a4 (Submodule.smul_mem _ _ (nfs_left H.ζi a2))) e e')
        (nfs_left (hE e e') a2)

omit [StarRing A] [StarModule ℂ A] [Fintype S] [DecidableEq S] in
theorem admissible_tail {l : Letter ℂ S} {w : List (Letter ℂ S)} (h : admitted st (l :: w)) : admitted st w := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨(List.nodup_cons.1 h1).2, fun a ha => h2 a (List.mem_cons_of_mem _ ha),
    fun a ha => h3 a (List.mem_cons_of_mem _ ha), (List.pairwise_cons.1 h4).2⟩

theorem word_nf (hWS : TL.WordStep) (H : NFHypA L st B K) (hA : TL.AHyp L st) (w : List (Letter ℂ S))
    (hw : admitted st w) (e : Ix S) :
    ((ofWord L st w).F * TL.bTA L w) e e1 ∈ NFs L B (L.Di ^ w.length) w.length := by
  induction w generalizing e with
  | nil =>
    have e0 : ((ofWord L st ([] : List (Letter ℂ S))).F * TL.bTA L []) = 1 := by
      simp [ofWord, Start.frame, TL.bTA, bT]
    rw [e0, Matrix.one_apply]
    split_ifs
    · simpa using nfs_gen (L := L) (P := 1) (n := 0) B.one_mem (h := []) rfl (by simp)
    · exact Submodule.zero_mem _
  | cons l w ih =>
    have hw' := admissible_tail hw
    have hf := frame_of_admissible_word A S r L st w hA.starLev hA.start hw'
    rw [hWS A S r L st l w hA hw e, Matrix.mul_apply]
    refine Submodule.sum_mem _ fun e' _ => nfs_step H ?_ (ih hw' e')
    rw [Matrix.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun e'' _ => nfs_left ?_
      (letter_mem H hA.starLev l w hf (hw.2.1 l List.mem_cons_self) i e'' e')
    exact SRel.eU (R := memRel B H.starB) l.intersection_update_fsHerm_neg_one i 0 e e''

end letters

end

end Formalism.FourierDecayAlt.P.NormalFormRelations
