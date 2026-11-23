import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ScaleMultiHomogeneous

namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

section Kernel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}

noncomputable def chiImg (j₀ : Fin (N + 1)) (x : Fin N → Ω) (p : TVar D N) :
    MvPolynomial (Fin (D + 1) × Fin N) Ω :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (Fin (D + 1) × Fin N) Ω) j₀
    (-∑ k, X (p.1, k) * C (x k)) (fun k => X (p.1, k)) p.2

noncomputable def chiP (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    MvPolynomial (TVar D N) K →ₐ[K] MvPolynomial (Fin (D + 1) × Fin N) Ω :=
  aeval (chiImg j₀ x)

noncomputable def kerP (j₀ : Fin (N + 1)) (x : Fin N → Ω) : Ideal (MvPolynomial (TVar D N) K) :=
  RingHom.ker (chiP (K := K) (D := D) j₀ x).toRingHom

noncomputable def psiS : MvPolynomial (Fin (D + 1) × Fin N) Ω →+* OmS Ω D N :=
  (algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)).comp
    (rename (R := Ω) (Sum.inr : Fin (D + 1) × Fin N → SVar D N)).toRingHom

theorem ker_eval_isPrime (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    (kerP (K := K) (D := D) j₀ x).IsPrime := by
  unfold kerP
  exact RingHom.ker_isPrime _

theorem psiS_chiImg (j₀ : Fin (N + 1)) (x : Fin N → Ω) (v : TVar D N)
    (hv : ¬ (v.1 = 0 ∧ v.2 = j₀)) :
    psiS (chiImg j₀ x v) = sImg (Ω := Ω) j₀ x v := by
  obtain ⟨i, j⟩ := v
  by_cases hj : j = j₀
  · rw [hj] at hv ⊢
    have hi : i ≠ 0 := fun h => hv ⟨h, rfl⟩
    have h1 : chiImg j₀ x (i, j₀) = -∑ k, X (i, k) * C (x k) :=
      Fin.insertNth_apply_same (α := fun _ => MvPolynomial (Fin (D + 1) × Fin N) Ω) j₀ _ _
    have h2 : sImg (Ω := Ω) j₀ x (i, j₀) = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
        (-∑ k, X (Sum.inr (i, k)) * C (x k)) := by
      unfold sImg
      congr 1
      exact (Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _).trans
        (if_neg hi)
    rw [h1, h2]
    simp [psiS, map_neg, map_sum, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C]
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
    rw [← hk]
    have h1 : chiImg j₀ x (i, j₀.succAbove k) = X (i, k) :=
      Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (Fin (D + 1) × Fin N) Ω) j₀ _ _ k
    have h2 : sImg (Ω := Ω) j₀ x (i, j₀.succAbove k) =
        algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inr (i, k))) := by
      unfold sImg
      congr 1
      exact Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _ k
    rw [h1, h2]
    simp [psiS, MvPolynomial.rename_X]

theorem psiS_chiImg_base (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    psiS (chiImg j₀ x ((0 : Fin (D + 1)), j₀)) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
        (-∑ k, X (Sum.inr ((0 : Fin (D + 1)), k)) * C (x k)) := by
  have h1 : chiImg j₀ x ((0 : Fin (D + 1)), j₀) = -∑ k, X ((0 : Fin (D + 1)), k) * C (x k) :=
    Fin.insertNth_apply_same (α := fun _ => MvPolynomial (Fin (D + 1) × Fin N) Ω) j₀ _ _
  rw [h1]
  simp [psiS, map_neg, map_sum, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C]

theorem sImg_base (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    sImg (Ω := Ω) j₀ x ((0 : Fin (D + 1)), j₀) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inl ())) := by
  unfold sImg
  congr 1
  first
  | exact (Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _).trans (if_pos rfl)
  | simp [Fin.succAboveCases]

theorem sImg_succAbove (j₀ : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) (k : Fin N) :
    sImg (Ω := Ω) j₀ x (i, j₀.succAbove k) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inr (i, k))) := by
  unfold sImg
  congr 1
  exact Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _ k

theorem ker_eval_ne_bot (hΩ : Algebra.trdeg K Ω = D) (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    kerP (K := K) (D := D) j₀ x ≠ ⊥ := by
  intro hbot
  have hinj : Function.Injective (chiP (K := K) (D := D) j₀ x) :=
    (RingHom.injective_iff_ker_eq_bot (chiP (K := K) (D := D) j₀ x).toRingHom).mpr hbot
  have hphi : MvPolynomial.aeval (fun i : TVar D N => chiP (K := K) (D := D) j₀ x (MvPolynomial.X i)) =
      chiP (K := K) (D := D) j₀ x := by
    first
    | (ext i; simp)
    | exact (MvPolynomial.aeval_unique _).symm
  have hind : AlgebraicIndependent K
      (fun i : TVar D N => chiP (K := K) (D := D) j₀ x (MvPolynomial.X i)) := by
    rw [algebraicIndependent_iff_injective_aeval, hphi]
    exact hinj
  have h1 := hind.cardinalMk_le_trdeg
  have h2 : Algebra.trdeg K Ω + Algebra.trdeg Ω (MvPolynomial (Fin (D + 1) × Fin N) Ω) =
      Algebra.trdeg K (MvPolynomial (Fin (D + 1) × Fin N) Ω) := trdeg_add_eq K Ω
  rw [← h2, MvPolynomial.trdeg_of_isDomain, hΩ, Cardinal.mk_fintype, Cardinal.mk_fintype,
    Cardinal.lift_natCast] at h1
  have h3 : Fintype.card (TVar D N) ≤ D + Fintype.card (Fin (D + 1) × Fin N) := by exact_mod_cast h1
  simp only [TVar, Fintype.card_prod, Fintype.card_fin] at h3
  have h4 : (D + 1) * (N + 1) = (D + 1) * N + (D + 1) := by ring
  linarith

end Kernel

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem sH_X (c : ι) (v : TVar d.D d.N) : d.sH c (X v) = sImg (Ω := Ω c) (d.jc c) (d.x c) v := by
  unfold Data.sH sHom
  exact MvPolynomial.aeval_X _ _

theorem w0rat_eq_base (hd : d.AxH 𝒜) (c : ι) :
    d.rationalBaseRow c = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
      (X (Sum.inl ()) + ∑ k, X (Sum.inr ((0 : Fin (d.D + 1)), k)) * C (d.x c k)) := by
  have hb := hd.w_base c
  have key : ∀ (a b : Ω c) (g : A c), g ≠ 0 → a • g = b • g → a = b := by
    intro a b g hg hab
    by_contra hne
    apply hg
    have h1 : (a - b) • g = 0 := by rw [sub_smul, hab, sub_self]
    have h2 : (a - b)⁻¹ • ((a - b) • g) = g := by
      rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
    rw [← h2, h1, smul_zero]
  have hr1 : ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w (d.jc c) c) = 1 := by
    have hex : ∃ a : Ω c, d.w (d.jc c) c = a • d.w (d.jc c) c := ⟨1, (one_smul _ _).symm⟩
    unfold ratio
    rw [dif_pos hex]
    exact (key _ _ _ hb ((one_smul _ _).trans hex.choose_spec)).symm
  unfold Data.rationalBaseRow
  rw [Fin.sum_univ_succAbove _ (d.jc c), hr1, map_one, mul_one]
  simp only [sH_X, sImg_succAbove, sImg_base, map_add, map_sum, map_mul]
  congr 1

theorem ker_eval_le_of_place (hd : d.AxH 𝒜) (c : ι) {p : Ideal (KTp K d.D d.N)}
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.OverP c p)
    (htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) (hy : 0 < w (d.rationalBaseRow c)) :
    kerP (K := K) (D := d.D) (d.jc c) (d.x c) ≤ p := by
  obtain ⟨_, hw2⟩ := hw
  intro F hF
  have hF0 : chiP (K := K) (D := d.D) (d.jc c) (d.x c) F = 0 := RingHom.mem_ker.mp hF
  have hsH : ∀ v, 0 ≤ w (sImg (Ω := Ω c) (d.jc c) (d.x c) v) := fun v => by
    rw [← d.sH_X c v]
    exact (hw2 (MvPolynomial.X v)).1
  have hv : ∀ v : TVar d.D d.N, 0 ≤ w (psiS (chiImg (d.jc c) (d.x c) v)) ∧ 0 < w (sImg (Ω := Ω c) (d.jc c) (d.x c) v - psiS (chiImg (d.jc c) (d.x c) v)) := by
    intro v
    by_cases hv0 : v.1 = 0 ∧ v.2 = d.jc c
    · obtain ⟨v1, v2⟩ := v
      obtain ⟨h1, h2⟩ := hv0
      have h1' : v1 = 0 := h1
      have h2' : v2 = d.jc c := h2
      subst h1'
      subst h2'
      have hdiff : sImg (Ω := Ω c) (d.jc c) (d.x c) ((0 : Fin (d.D + 1)), d.jc c) - psiS (chiImg (d.jc c) (d.x c) ((0 : Fin (d.D + 1)), d.jc c)) =
          d.rationalBaseRow c := by
        rw [sImg_base, psiS_chiImg_base, d.w0rat_eq_base hd c, ← map_sub]
        congr 1
        ring
      rw [hdiff]
      refine ⟨?_, hy⟩
      have e : psiS (chiImg (d.jc c) (d.x c) ((0 : Fin (d.D + 1)), d.jc c)) =
          sImg (Ω := Ω c) (d.jc c) (d.x c) ((0 : Fin (d.D + 1)), d.jc c) - d.rationalBaseRow c := by
        rw [← hdiff]
        ring
      rw [e]
      exact le_trans (le_min (hsH _) hy.le) (AddValuation.map_sub _ _ _)
    · rw [psiS_chiImg (d.jc c) (d.x c) v hv0, sub_self, AddValuation.map_zero]
      exact ⟨hsH v, by simp⟩
  have hC : ∀ k : K, d.sH c (MvPolynomial.C k) = psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) (MvPolynomial.C k)) := by
    intro k
    have e1 : chiP (K := K) (D := d.D) (d.jc c) (d.x c) (MvPolynomial.C k) =
        algebraMap K (MvPolynomial (Fin (d.D + 1) × Fin d.N) (Ω c)) k := MvPolynomial.aeval_C _ _
    have e2 : d.sH c (MvPolynomial.C k) = algebraMap K (OmS (Ω c) d.D d.N) k :=
      MvPolynomial.aeval_C _ _
    rw [e1, e2]
    unfold psiS
    rw [RingHom.comp_apply]
    first
    | (rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
       exact IsScalarTower.algebraMap_apply K _ _ k)
    | (simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
       exact IsScalarTower.algebraMap_apply K _ _ k)
    | (simp [IsScalarTower.algebraMap_apply K (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)])
  have key : ∀ G : KTp K d.D d.N, 0 ≤ w (psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) G)) ∧ 0 < w (d.sH c G - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) G)) := by
    intro G
    induction G using MvPolynomial.induction_on
    · rename_i k
      rw [← hC k, sub_self, AddValuation.map_zero]
      exact ⟨(hw2 _).1, by simp⟩
    · rename_i p q hp hq
      simp only [map_add]
      refine ⟨le_trans (le_min hp.1 hq.1) (AddValuation.map_add _ _ _), ?_⟩
      have e : d.sH c p + d.sH c q - (psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) p) + psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) q)) =
          (d.sH c p - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) p)) + (d.sH c q - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) q)) := by ring
      rw [e]
      exact lt_of_lt_of_le (lt_min hp.2 hq.2) (AddValuation.map_add _ _ _)
    · rename_i p v hp
      have hX : chiP (K := K) (D := d.D) (d.jc c) (d.x c) (MvPolynomial.X v) = chiImg (d.jc c) (d.x c) v := MvPolynomial.aeval_X _ _
      rw [map_mul (chiP (K := K) (D := d.D) (d.jc c) (d.x c)) p (MvPolynomial.X v), hX,
        map_mul (psiS (Ω := Ω c) (D := d.D) (N := d.N)), map_mul (d.sH c) p (MvPolynomial.X v),
        d.sH_X c v]
      refine ⟨by rw [AddValuation.map_mul]; exact add_nonneg hp.1 (hv v).1, ?_⟩
      have e : d.sH c p * sImg (Ω := Ω c) (d.jc c) (d.x c) v - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) p) * psiS (chiImg (d.jc c) (d.x c) v) =
          d.sH c p * (sImg (Ω := Ω c) (d.jc c) (d.x c) v - psiS (chiImg (d.jc c) (d.x c) v)) + (d.sH c p - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) p)) * psiS (chiImg (d.jc c) (d.x c) v) := by ring
      rw [e]
      refine lt_of_lt_of_le (lt_min ?_ ?_) (AddValuation.map_add _ _ _)
      · rw [AddValuation.map_mul]
        exact lt_of_lt_of_le (hv v).2 (le_add_of_nonneg_left (hw2 p).1)
      · rw [AddValuation.map_mul]
        exact lt_of_lt_of_le hp.2 (le_add_of_nonneg_right (hv v).1)
  apply (hw2 F).2.mp
  have h := (key F).2
  rw [hF0, map_zero, sub_zero] at h
  exact h

theorem ker_eval_eq_of_place (hd : d.AxH 𝒜) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.OverP c p)
    (htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) (hy : 0 < w (d.rationalBaseRow c)) :
    kerP (K := K) (D := d.D) (d.jc c) (d.x c) = p := by
  have hle := d.ker_eval_le_of_place hd c hw htriv hy
  have hprime := ker_eval_isPrime (K := K) (D := d.D) (d.jc c) (d.x c)
  have hne := ker_eval_ne_bot (K := K) (hd.trdeg c) (d.jc c) (d.x c)
  obtain ⟨hpp, hph⟩ := hp
  by_contra hneq
  have hlt := lt_of_le_of_ne hle hneq
  have h1 : p.height ≤ ((1 : ℕ) : ℕ∞) := by rw [hph]; simp
  have h2 := (Ideal.height_le_iff.mp h1) _ hprime hlt
  have h3 : ¬ (kerP (K := K) (D := d.D) (d.jc c) (d.x c)).height ≤ ((0 : ℕ) : ℕ∞) := by
    intro h0
    have h4 := (Ideal.height_le_iff.mp h0) ⊥ Ideal.bot_prime (bot_lt_iff_ne_bot.mpr hne)
    simp at h4
  apply h3
  have h5 : (kerP (K := K) (D := d.D) (d.jc c) (d.x c)).height = 0 :=
    ENat.lt_one_iff_eq_zero.mp (by simpa using h2)
  rw [h5]
  simp

end Data

end ReciprocityTheory.ChartRestriction.G.T0
