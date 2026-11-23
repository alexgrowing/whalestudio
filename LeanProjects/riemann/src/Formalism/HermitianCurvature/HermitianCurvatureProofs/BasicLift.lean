import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommuteAvrBvrOfCommuteSiteOps
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LagrangeExtraction

namespace Formalism.FourierDecayAlt.TL

open Matrix Finset Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.RuleGD

section

variable {A : Type} [Ring A] [Algebra ℂ A]

inductive PT : ℕ → (ℂ → A) → A → Prop
  | const (c : A) : PT 0 (fun _ => c) c
  | add {d f g c c'} : PT d f c → PT d g c' → PT d (fun s => f s + g s) (c + c')
  | up {d f c} : PT d f c → PT (d + 1) f 0
  | mulS {d f c} : PT d f c → PT (d + 1) (fun s => s • f s) c

theorem PT.congr {d : ℕ} {f g : ℂ → A} {c c' : A} (h : PT d f c) (e : ∀ s, f s = g s) (e' : c = c') : PT d g c' := by
  have hfg : f = g := funext e
  subst hfg
  subst e'
  exact h

theorem PT.mulL {d : ℕ} {f : ℂ → A} {c : A} (h : PT d f c) (a : A) : PT d (fun s => a * f s) (a * c) := by
  induction h with
  | const c => exact PT.const (a * c)
  | add _ _ ih1 ih2 => exact (PT.add ih1 ih2).congr (fun s => (mul_add _ _ _).symm) (mul_add _ _ _).symm
  | up _ ih => exact (PT.up ih).congr (fun _ => rfl) (mul_zero a).symm
  | mulS _ ih => exact (PT.mulS ih).congr (fun s => (mul_smul_comm s a _).symm) rfl

theorem PT.mulR {d : ℕ} {f : ℂ → A} {c : A} (h : PT d f c) (a : A) : PT d (fun s => f s * a) (c * a) := by
  induction h with
  | const c => exact PT.const (c * a)
  | add _ _ ih1 ih2 => exact (PT.add ih1 ih2).congr (fun s => (add_mul _ _ _).symm) (add_mul _ _ _).symm
  | up _ ih => exact (PT.up ih).congr (fun _ => rfl) (zero_mul a).symm
  | mulS _ ih => exact (PT.mulS ih).congr (fun s => (smul_mul_assoc s _ a).symm) rfl

theorem PT.coef {d : ℕ} {f : ℂ → A} {c : A} (h : PT d f c) :
    ∃ a : Fin (d + 1) → A, a (Fin.last d) = c ∧ ∀ s, f s = ∑ j : Fin (d + 1), s ^ (j : ℕ) • a j := by
  induction h with
  | const c => exact ⟨fun _ => c, rfl, fun s => by simp⟩
  | add _ _ ih1 ih2 =>
    obtain ⟨a1, h1, e1⟩ := ih1
    obtain ⟨a2, h2, e2⟩ := ih2
    exact ⟨a1 + a2, by simp [h1, h2], fun s => by simp [e1, e2, Finset.sum_add_distrib, smul_add]⟩
  | up _ ih =>
    obtain ⟨a, h1, e1⟩ := ih
    refine ⟨Fin.snoc (α := fun _ => A) a 0, by simp, fun s => ?_⟩
    rw [Fin.sum_univ_castSucc, e1]
    simp
  | mulS _ ih =>
    obtain ⟨a, h1, e1⟩ := ih
    refine ⟨Fin.cons (α := fun _ => A) 0 a, ?_, fun s => ?_⟩
    · rw [← Fin.succ_last, Fin.cons_succ, h1]
    · dsimp only
      rw [Fin.sum_univ_succ, e1, Finset.smul_sum]
      simp [smul_smul, pow_succ']

theorem PT.lag {d : ℕ} {f : ℂ → A} {c : A} (h : PT d f c) :
    c = ∑ s : Fin (d + 1), ((F7.lagCo (fun j : Fin (d + 1) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) • f ((s : ℕ) : ℂ) := by
  obtain ⟨a, ha, hf⟩ := h.coef
  have hy : Function.Injective (fun j : Fin (d + 1) => ((j : ℕ) : ℝ)) := fun i j hij =>
    Fin.ext (by simpa using hij)
  have key : ∀ j : Fin (d + 1), ∑ s : Fin (d + 1), (((F7.lagCo (fun j : Fin (d + 1) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) *
      (((s : ℕ) : ℂ)) ^ (j : ℕ)) = if (j : ℕ) = d then 1 else 0 := by
    intro j
    have h1 := Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.sum_lagCo_mul_pow _ hy (j : ℕ) (Nat.lt_succ_iff.1 j.isLt)
    have h2 : ((∑ s, F7.lagCo (fun j : Fin (d + 1) => ((j : ℕ) : ℝ)) s * ((s : ℕ) : ℝ) ^ (j : ℕ) : ℝ) : ℂ) =
        ((if (j : ℕ) = d then 1 else 0 : ℝ) : ℂ) := by rw [h1]
    push_cast at h2
    rw [h2]
    split_ifs <;> simp
  symm
  simp_rw [hf, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single (Fin.last d)]
  · rw [key, if_pos (by simp), one_smul, ha]
  · intro j _ hj
    rw [key, if_neg, zero_smul]
    intro hjd
    exact hj (Fin.ext (by simpa using hjd))
  · intro h0
    exact absurd (Finset.mem_univ _) h0

theorem PT.prod (ε Y : ℂ) (l : List (A × A × A)) :
    PT l.length (fun s => (l.map fun x => (!![algebraMap ℂ A (Y + ε * s) + x.1, -x.2.1; x.2.2, 0] :
      Matrix (Fin 2) (Fin 2) A)).prod 0 0) (algebraMap ℂ A (ε ^ l.length)) ∧
    PT l.length (fun s => (l.map fun x => (!![algebraMap ℂ A (Y + ε * s) + x.1, -x.2.1; x.2.2, 0] :
      Matrix (Fin 2) (Fin 2) A)).prod 1 0) 0 := by
  induction l with
  | nil =>
    refine ⟨(PT.const 1).congr (fun s => by simp) (by simp), (PT.const 0).congr (fun s => by simp) rfl⟩
  | cons x l ih =>
    obtain ⟨h0, h1⟩ := ih
    have hA := (h0.mulL (algebraMap ℂ A Y)).up
    have hB := (h0.mulL (algebraMap ℂ A ε)).mulS
    have hC := (h0.mulL x.1).up
    have hD := (h1.mulL (-x.2.1)).up
    have hE := (h0.mulL x.2.2).up
    refine ⟨((hA.add hB).add (hC.add hD)).congr (fun s => ?_) ?_, hE.congr (fun s => ?_) ?_⟩
    · simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
      rw [Algebra.smul_def, map_add, mul_comm ε s, map_mul]
      noncomm_ring
    · simp [pow_succ', map_mul]
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp

variable {r : ℕ}

theorem ptP (L : LevelData A r) (Y : ℂ) : PT r (fun s => L.Ar (Y + s)) 1 ∧ PT r (fun s => L.Br (Y + s)) 0 := by
  obtain ⟨h0, h1⟩ := PT.prod (A := A) 1 Y ((List.ofFn fun l => (L.p l, L.c l, L.ci l)).reverse)
  have hlen : ((List.ofFn fun l => (L.p l, L.c l, L.ci l)).reverse).length = r := by simp
  have e : ∀ s : ℂ, ((List.ofFn fun l => (L.p l, L.c l, L.ci l)).reverse.map fun x =>
      (!![algebraMap ℂ A (Y + 1 * s) + x.1, -x.2.1; x.2.2, 0] : Matrix (Fin 2) (Fin 2) A)) =
      (List.ofFn (L.Tl (Y + s))).reverse := by
    intro s
    rw [List.map_reverse, List.map_ofFn]
    congr 2
    funext l
    simp [LevelData.Tl]
  rw [hlen] at h0 h1
  exact ⟨h0.congr (fun s => by rw [e s]; rfl) (by simp), h1.congr (fun s => by rw [e s]; rfl) rfl⟩

theorem ptM (L : LevelData A r) (Y : ℂ) :
    PT r (fun s => L.Avr (Y - s)) (algebraMap ℂ A ((-1) ^ r)) ∧ PT r (fun s => L.Bvr (Y - s)) 0 := by
  obtain ⟨h0, h1⟩ := PT.prod (A := A) (-1) Y ((List.ofFn fun l => (-L.pb l, L.cb l, L.cbi l)).reverse)
  have hlen : ((List.ofFn fun l => (-L.pb l, L.cb l, L.cbi l)).reverse).length = r := by simp
  have e : ∀ s : ℂ, ((List.ofFn fun l => (-L.pb l, L.cb l, L.cbi l)).reverse.map fun x =>
      (!![algebraMap ℂ A (Y + -1 * s) + x.1, -x.2.1; x.2.2, 0] : Matrix (Fin 2) (Fin 2) A)) =
      (List.ofFn (L.Tvl (Y - s))).reverse := by
    intro s
    rw [List.map_reverse, List.map_ofFn]
    congr 2
    funext l
    simp [LevelData.Tvl, sub_eq_add_neg]
  rw [hlen] at h0 h1
  exact ⟨h0.congr (fun s => by rw [e s]; rfl) rfl, h1.congr (fun s => by rw [e s]; rfl) rfl⟩

end

theorem bFromCap : BFromCap := by
  intro A _ _ _ _ r L st hA Y hY hinv hinv'
  have hc := fun s => capConj A r L st hA Y hY hinv hinv' s
  obtain ⟨hAv, hBv⟩ := ptM L Y
  obtain ⟨hAr, hBr⟩ := ptP L Y
  have P1 : PT (r + 1) (fun s : ℂ => L.Avr (Y - s) * (nP L st Y 0 + s • bP L st Y) + L.Bvr (Y - s) * nP L st Y 1)
      (algebraMap ℂ A ((-1) ^ r) * bP L st Y) := by
    have t1 := (hAv.mulR (nP L st Y 0)).up
    have t2 := (hAv.mulR (bP L st Y)).mulS
    have t3 := (hBv.mulR (nP L st Y 1)).up
    exact ((t1.add t2).add t3).congr (fun s => by rw [mul_add, mul_smul_comm]) (by simp)
  have P2 : PT (r + 1) (fun s : ℂ => (L.Avr Y * st.QQ Y 0 0 + L.Bvr Y * st.QQ Y 1 0 - s • bM L st Y) * L.Ar (Y + s) +
      (L.Avr Y * st.QQ Y 0 1 + L.Bvr Y * st.QQ Y 1 1) * L.Br (Y + s)) (-bM L st Y) := by
    have t1 := (hAr.mulL (L.Avr Y * st.QQ Y 0 0 + L.Bvr Y * st.QQ Y 1 0)).up
    have t2 := (hAr.mulL (-bM L st Y)).mulS
    have t3 := (hBr.mulL (L.Avr Y * st.QQ Y 0 1 + L.Bvr Y * st.QQ Y 1 1)).up
    exact ((t1.add t2).add t3).congr
      (fun s => by rw [sub_mul, smul_mul_assoc, neg_mul, smul_neg, sub_eq_add_neg]) (by simp)
  have hl1 := P1.lag
  have hl2 := P2.lag
  constructor
  · have h1 : algebraMap ℂ A ((-1) ^ r) * bP L st Y =
        ∑ s : Fin (r + 2), ((F7.lagCo (fun j : Fin (r + 2) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) •
          (L.Dbi ^ (s : ℕ) * cst L st Y * L.Db ^ (s : ℕ)) := by
      rw [hl1]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [(hc s).1]
    rw [← h1, Algebra.smul_def, ← mul_assoc, ← map_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, map_one,
      one_mul]
  · have h2 : -bM L st Y =
        ∑ s : Fin (r + 2), ((F7.lagCo (fun j : Fin (r + 2) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) •
          (L.Di ^ (s : ℕ) * cst L st Y * L.D ^ (s : ℕ)) := by
      rw [hl2]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [(hc s).2]
    rw [← h2, neg_neg]

theorem basicLift : BasicLift := by
  intro A _ _ _ _ r n L st Lf hA hS hn Y hY hm1 h0 hp1
  have hpow : ∀ {a : A} {κ : ℕ}, Lf 0 κ a → ∀ s : ℕ, Lf 0 (κ * s) (a ^ s) := by
    intro a κ ha s
    induction s with
    | zero => simpa using hS.one
    | succ s ih =>
      rw [pow_succ]
      exact hS.mono le_rfl (by simp [Nat.mul_succ]) (hS.mul ih ha)
  have hsum : ∀ {κ : ℕ} (f : Fin (r + 2) → A) (c : Fin (r + 2) → ℂ), (∀ s, Lf n κ (f s)) →
      Lf n κ (∑ s, c s • f s) := by
    intro κ f c hf
    refine Finset.sum_induction _ (fun x => Lf n κ x) (fun a b ha hb => hS.add ha hb) (hS.zero n κ) ?_
    intro s _
    exact hS.smul (c s) (hf s)
  obtain ⟨hD, hDb, hDr, hDrb, hDi, hDbi, hgI⟩ := hS.fns
  have hN : r + 1 ≤ (r + 1) * n := Nat.le_mul_of_pos_right _ (by omega)
  have hterm : ∀ {u v : A} (hu : Lf 0 0 u) (hv : Lf 0 (r + 1) v) (Z : ℂ), star Z = Z →
      ∀ s : Fin (r + 2), Lf n (3 * (r + 1) * n) (u ^ (s : ℕ) * cst L st Z * v ^ (s : ℕ)) := by
    intro u v hu hv Z hZ s
    have h1 := hS.mul (hS.mul (hpow hu (s : ℕ)) (hS.cap Z hZ)) (hpow hv (s : ℕ))
    have hs : (s : ℕ) ≤ r + 1 := Nat.lt_succ_iff.1 s.isLt
    have hb : (r + 1) * (s : ℕ) ≤ (r + 1) * n := Nat.mul_le_mul_left _ (by omega)
    refine hS.mono (by simp) ?_ h1
    simp only [zero_mul, add_zero, zero_add, Nat.mul_zero]
    nlinarith
  have hB : ∀ Z : ℂ, star Z = Z → Z ∈ st.inv → (Z - 1 ∈ st.inv ∨ Z + 1 ∈ st.inv) →
      Lf n (3 * (r + 1) * n) (bP L st Z) ∧ Lf n (3 * (r + 1) * n) (bM L st Z) := by
    intro Z hZ hZi hZo
    obtain ⟨e1, e2⟩ := bFromCap A r L st hA Z hZ hZi hZo
    refine ⟨?_, ?_⟩
    · rw [e1]
      exact hS.smul _ (hsum _ _ fun s => hterm hDbi hDb Z hZ s)
    · rw [e2]
      have h3 := hS.smul (-1 : ℂ) (hsum _ (fun s => ((F7.lagCo (fun j : Fin (r + 2) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ))
        fun s => hterm hDi hD Z hZ s)
      rwa [neg_one_smul] at h3
  obtain ⟨hbP, hbM⟩ := hB Y hY h0 (Or.inl hm1)
  have hstar1 : star (Y - 1) = Y - 1 := by rw [star_sub, hY, star_one]
  have hstar2 : star (Y + 1) = Y + 1 := by rw [star_add, hY, star_one]
  obtain ⟨hbP', -⟩ := hB (Y - 1) hstar1 hm1 (Or.inr (by simpa using h0))
  obtain ⟨-, hbM'⟩ := hB (Y + 1) hstar2 hp1 (Or.inl (by simpa using h0))
  obtain ⟨ha1, -⟩ := aFromB A r L st hA (Y - 1) hstar1 hm1
  obtain ⟨-, ha2⟩ := aFromB A r L st hA (Y + 1) hstar2 hp1
  rw [sub_add_cancel] at ha1
  rw [add_sub_cancel_right] at ha2
  have hx1 := hS.xi (Y - 1) hm1 hstar1
  have hx2 := hS.xi (Y + 1) hp1 hstar2
  refine ⟨hbP, hbM, ?_, ?_⟩
  · rw [ha1]
    have t1 := hS.mul hbP' hDr
    have t2 := hS.mul (hS.mul (hS.mul hDr hDi) hbP') hD
    have t3 : Lf n (3 * (r + 1) * n + (r + 1) + (2 * r + 2) * n + r)
        (bP L st (Y - 1) * L.Dr - L.Dr * L.Di * bP L st (Y - 1) * L.D) := by
      rw [sub_eq_add_neg]
      have t2' := hS.smul (-1 : ℂ) t2
      rw [neg_one_smul] at t2'
      refine hS.add (hS.mono (by simp) (by omega) t1) (hS.mono (by simp) ?_ t2')
      simp only [zero_add, add_zero, Nat.mul_zero]
      omega
    have t4 := hS.mul (hS.mul (hS.mul hDb hgI) hx1) t3
    refine hS.mono (by simp) ?_ t4
    simp only [zero_add, add_zero, Nat.mul_zero]
    nlinarith
  · rw [ha2]
    have t1 := hS.mul hbM' hDrb
    have t2 := hS.mul (hS.mul (hS.mul hDrb hDbi) hbM') hDb
    have t3 : Lf n (3 * (r + 1) * n + (r + 1) + (2 * r + 2) * n + r)
        (bM L st (Y + 1) * L.Drb - L.Drb * L.Dbi * bM L st (Y + 1) * L.Db) := by
      rw [sub_eq_add_neg]
      have t2' := hS.smul (-1 : ℂ) t2
      rw [neg_one_smul] at t2'
      refine hS.add (hS.mono (by simp) (by omega) t1) (hS.mono (by simp) ?_ t2')
      simp only [zero_add, add_zero, Nat.mul_zero]
      omega
    have t4 := hS.mul (hS.mul (hS.mul hD hgI) hx2) t3
    have t5 := hS.smul (-1 : ℂ) t4
    rw [neg_one_smul] at t5
    refine hS.mono (by simp) ?_ t5
    simp only [zero_add, add_zero, Nat.mul_zero]
    nlinarith

end Formalism.FourierDecayAlt.TL
