import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscPowerMonomialMemSupported

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem mem_degAt_det {R : Type} [CommRing R] {n : ℕ} (y : Fin n → ℤ) (t : ℤ) :
    DegAt t (∑ a : Fin n, if y a = t then 1 else 0)
      (Matrix.det (Matrix.of fun a c : Fin n => (MvPolynomial.X (y a, c) : MvPolynomial (ℤ × Fin n) R))) := by
  classical
  rw [Matrix.det_apply]
  refine degAt_sum _ _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  have h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (ℤ × Fin n) R) = C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) := by
    simp
  rw [h1]
  refine degAt_C_mul _ ?_
  have h2 := degAt_prod (R := R) (x := t) Finset.univ
    (fun i : Fin n => (MvPolynomial.X (y (σ i), i) : MvPolynomial (ℤ × Fin n) R))
    (fun i => if y (σ i) = t then 1 else 0) (fun i _ => degAt_X (x := t) (y (σ i), i))
  rw [Equiv.sum_comp σ (fun a => if y a = t then 1 else 0)] at h2
  exact h2

namespace Dat

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

def discPowerMonomialDegree (j : ℤ) (b : ℤ → ℕ) (x : ℤ) : ℕ :=
  X.m0 K * (∑ a : Fin r, if X.F.fr (j - 1) a.val = x then 1 else 0) +
    ∑ i : Fin r, ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat *
      (if X.F.fr (j - 1) i.val = x then 1 else 0)

omit [NeZero n'] [NeZero r] in

def memdMu (j : ℤ) (u : Fin r × Fin r → ℕ) (x : ℤ) : ℕ :=
  ∑ v : Fin r × Fin r, u v * (if X.F.fr j v.1.val = x then 1 else 0)

end Dat

section Deg

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem degAt_disc_power_monomial (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) (x : ℤ) :
    DegAt x (X.discPowerMonomialDegree p K j b x) (X.discPowerTimesMonomial p K O j b) := by
  classical
  unfold Dat.discPowerMonomialDegree Dat.discPowerTimesMonomial Dat.Dw
  refine degAt_mul (degAt_pow (mem_degAt_det _ x) _) ?_
  exact degAt_prod Finset.univ _ _ fun i _ => degAt_pow (degAt_X (x := x) (X.F.fr (j - 1) i.val, (0 : Fin r))) _

theorem mem_degAt_Mu (O : Type) [CommRing O] (j : ℤ) (u : Fin r × Fin r → ℕ) (x : ℤ) :
    DegAt x (X.memdMu j u x) (X.memMu O j u) := by
  classical
  unfold Dat.memdMu Dat.memMu
  exact degAt_prod Finset.univ _ _ fun v _ => degAt_pow (degAt_X (x := x) (X.F.fr j v.1.val, v.2)) _

theorem disc_power_monomial_degree_off (j : ℤ) (b : ℤ → ℕ) (x : ℤ) (h : ∀ a : Fin r, X.F.fr (j - 1) a.val ≠ x) :
    X.discPowerMonomialDegree p K j b x = 0 := by
  unfold Dat.discPowerMonomialDegree
  simp [h]

theorem mem_dMu_off (j : ℤ) (u : Fin r × Fin r → ℕ) (x : ℤ) (h : ∀ a : Fin r, X.F.fr j a.val ≠ x) :
    X.memdMu j u x = 0 := by
  unfold Dat.memdMu
  simp [h]

theorem disc_power_monomial_degree_at_w (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (a0 : Fin r) :
    X.discPowerMonomialDegree p K j b (X.F.fr (j - 1) a0.val) =
      X.m0 K + ((b (X.F.fr (j - 1) a0.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) a0.val)).toNat := by
  classical
  have hinj := fr_injective X.F hX.valid (j - 1)
  have hiff : ∀ a : Fin r, (X.F.fr (j - 1) a.val = X.F.fr (j - 1) a0.val) ↔ a = a0 :=
    fun a => ⟨fun h => hinj h, fun h => by rw [h]⟩
  unfold Dat.discPowerMonomialDegree
  simp only [hiff]
  simp

theorem mem_dMu_tau (hX : X.Hyp p K) (j : ℤ) (u : Fin r × Fin r → ℕ) (t : Fin r) :
    X.memdMu j u (X.F.fr j t.val) = ∑ c, u (t, c) := by
  classical
  have hinj := fr_injective X.F hX.valid j
  have hiff : ∀ a : Fin r, (X.F.fr j a.val = X.F.fr j t.val) ↔ a = t :=
    fun a => ⟨fun h => hinj h, fun h => by rw [h]⟩
  unfold Dat.memdMu
  rw [Fintype.sum_prod_type]
  simp only [hiff]
  rw [Finset.sum_eq_single t]
  · simp
  · intro a _ ha
    simp [ha]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mem_degAt_segRen_off {R : Type} [CommRing R] (j : ℤ) {n : ℕ} (A : MvPolynomial (Fin (segN X.F j) × Fin n) R)
    (x : ℤ) (hx : x ∉ X.F.letters j) : DegAt x 0 (segRen X.F j R n A) := by
  refine degAt_of_supported {v : ℤ × Fin n | v.1 ∈ X.F.letters j} ?_ ?_
  · refine mem_supported.mpr fun v hv => ?_
    obtain ⟨u, _, rfl⟩ := mem_vars_rename _ _ (Finset.mem_coe.mp hv)
    exact segE_mem X.F j u.1
  · intro v hv h
    exact hx (h ▸ hv)

end Deg

theorem restMemB_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) : RestMemB C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hb q mm hmm x hx hW
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hV := hX.valid
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  obtain ⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hPATH, hGood, hSt, hu, hd⟩ := exists_path_decomposition D hAdm hX j b q
  have H := plHyp_of X p K hX j _ _ dd hPATH
  have hI' : IsSt P1.mu (Ican P1.mu) := by rw [h1]; exact mem_isSt_Ican H
  have hI'' : IsSt P2.mu q.1.2.1 := by rw [h2]; exact hSt
  have u1 := (standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).1) P1 _ hI').1
  have u2 := (standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).1) P2 _ hI'').1
  rw [h1] at u1
  rw [h2] at u2
  obtain ⟨i, rfl⟩ := segE_surj X.F j hx
  have hevW : ∀ a : Fin r, Even (X.F.fr (j - 1) a.val) := fun a => (hV.2.2.2.2.1 (j - 1) a.val a.isLt).2
  have hevT : ∀ a : Fin r, Even (X.F.fr j a.val) := fun a => (hV.2.2.2.2.1 j a.val a.isLt).2
  have hA : ¬ Even (segE X.F j i) → DegAt (segE X.F j i) (0 + 0 + b' i) (X.memA p K O j b q.1) := by
    intro ho
    unfold Dat.memA
    refine degAt_mul (degAt_mul ?_ ?_) (degAt_segRen X.F j u1 i)
    · refine degAt_of_supported {v : ℤ × Fin r | Even v.1} (disc_power_monomial_mem_supported O j b _ fun a _ => hevW a) ?_
      intro v hv h
      exact ho (h ▸ hv)
    · refine degAt_of_supported {v : ℤ × Fin r | Even v.1} (mem_Mu_supported O j _ _ fun a _ => hevT a) ?_
      intro v hv h
      exact ho (h ▸ hv)
  have hG : Even (segE X.F j i) → DegAt (segE X.F j i) (b'' i) (X.memG K O j q.1) := fun _ =>
    degAt_segRen X.F j u2 i
  rw [ordDeg_prod hA hG mm hmm]
  obtain ⟨-, gE, gO⟩ := hGood i hW
  split_ifs with he
  · have hs := (T.step_vec P2 i ((comb_vec X.F j i).mpr he)).2.2
    rw [h2] at hs
    have := gE he
    rw [hs] at this
    exact_mod_cast this
  · have hvec : (segLL X.F j).vec i = false := by
      by_contra h
      exact he ((comb_vec X.F j i).mp (by simpa using h))
    have hs := (T.step_cov P1 i hvec).2.2
    rw [h1] at hs
    have := gO he
    rw [hs] at this
    simpa using this

end Formalism.MainNotions.SelectionLemmas.Pf
