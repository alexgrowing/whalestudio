import Formalism.LocalToGlobal.Columns.RefXi1Above

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section YA

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.yOfAt (d : Deco E n ST SG) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) (w : SG) (z : Sp E n) : Prop :=
  (qOf w.1 : E) • z ∈ d.at w.1 ∧ d.be w ((qOf w.1 : E) • z) = v w

theorem Deco.yOfAt_iff {d : Deco E n ST SG} {w : SG} {f : Sp E n ≃ₗ[E] Sp E n} (hf : d.IsLift w f)
    (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) (z : Sp E n) :
    d.yOfAt v w z ↔ ∀ i : Fin n, IntAt w.1 ((qOf w.1 : E) * f.symm z i) ∧ redP w.1 ((qOf w.1 : E) * f.symm z i) = v w i := by
  have e : (qOf w.1 : E) • z = f ((qOf w.1 : E) • f.symm z) := by rw [map_smul, LinearEquiv.apply_symm_apply]
  unfold Deco.yOfAt
  rw [e, hf.1, ciMem_stdAt]
  constructor
  · rintro ⟨h1, h2⟩ i
    refine ⟨h1 i, ?_⟩
    rw [hf.2 _ ((ciMem_stdAt _ _).2 h1)] at h2
    exact congrFun h2 i
  · intro h
    have h1 : ∀ i, IntAt w.1 (((qOf w.1 : E) • f.symm z) i) := fun i => (h i).1
    refine ⟨h1, ?_⟩
    rw [hf.2 _ ((ciMem_stdAt _ _).2 h1)]
    funext i
    exact (h i).2

theorem Deco.yOfAt_sub_iff {d : Deco E n ST SG} {w : SG} (hl : d.HasLift w) (hq2 : ((qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2)
    {v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal} {z z' : Sp E n} (hz : d.yOfAt v w z) : d.yOfAt v w z' ↔ z' - z ∈ d.at w.1 := by
  obtain ⟨f, hf⟩ := hl
  have hq := ciQ_mem w.1
  have hq0 : ((qOf w.1 : ℕ) : E) ≠ 0 := ciQ_ne_zero hq2
  rw [Deco.yOfAt_iff hf] at hz ⊢
  have e : z' - z = f (f.symm z' - f.symm z) := by
    rw [map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [e, hf.1, ciMem_stdAt]
  constructor
  · intro h i
    have h1 := ciIntAt_sub (h i).1 (hz i).1
    have h2 : redP w.1 ((qOf w.1 : E) * f.symm z' i - (qOf w.1 : E) * f.symm z i) = 0 := by
      rw [redP_sub (h i).1 (hz i).1, (h i).2, (hz i).2, sub_self]
    have h3 := ciIntAt_div hq hq2 h1 h2
    have e2 : ((qOf w.1 : E) * f.symm z' i - (qOf w.1 : E) * f.symm z i) / (qOf w.1 : E) = f.symm z' i - f.symm z i := by
      field_simp
    rw [e2] at h3
    exact h3
  · intro h i
    have h' : IntAt w.1 (f.symm z' i - f.symm z i) := h i
    have e2 : (qOf w.1 : E) * f.symm z' i = (qOf w.1 : E) * f.symm z i + (qOf w.1 : E) * (f.symm z' i - f.symm z i) := by ring
    rw [e2]
    exact ⟨(ciIntAt_add_iff ((ciIntAt_q (q := qOf w.1)).mul h')).2 (hz i).1, by rw [redP_add_natCast_mul hq h']; exact (hz i).2⟩

theorem Deco.yOf_eq_of_mem {d : Deco E n ST SG} (hl : ∀ w, d.HasLift w) (hq2 : ∀ w : SG, ((qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2)
    {v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal} {z : Sp E n} (hz : z ∈ d.yOf v) : d.yOf v = {z' | ∀ w : SG, z' - z ∈ d.at w.1} := by
  ext z'
  exact forall_congr' fun w => Deco.yOfAt_sub_iff (hl w) (hq2 w) (hz w)

theorem Deco.Ok.exists_beV {d : Deco E n ST SG} (hd : d.Ok) (c : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) :
    ∃ x ∈ d.N, ∀ w, d.be w x = c w := by
  classical
  choose x hx hxc using fun w : SG => hd.be_surj w (c w)
  have hcop : Pairwise fun w w' : SG => IsCoprime w.1.asIdeal w'.1.asIdeal := fun w w' hne => by
    show IsCoprime w.1.asIdeal w'.1.asIdeal
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne w.1.isMaximal w'.1.isMaximal fun h => hne (Subtype.ext (HeightOneSpectrum.ext h))
  choose a ha using fun w₀ : SG => Ideal.exists_forall_sub_mem_ideal hcop fun w : SG => if w = w₀ then (1 : 𝓞 E) else 0
  refine ⟨∑ w₀ : SG, a w₀ • x w₀, Submodule.sum_mem _ fun w₀ _ => Submodule.smul_mem _ _ (hx w₀), fun w => ?_⟩
  rw [hd.be_sum w _ _ fun w₀ _ => le_locP w.1 d.N (Submodule.smul_mem _ _ (hx w₀)), Finset.sum_eq_single w]
  · rw [hd.be_smul w _ _ (le_locP w.1 d.N (hx w)), hxc]
    have h1 := ha w w
    rw [if_pos rfl] at h1
    rw [(Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 h1, map_one, one_smul]
  · intro w₀ _ hne
    rw [hd.be_smul w _ _ (le_locP w.1 d.N (hx w₀))]
    have h1 := ha w₀ w
    rw [if_neg (Ne.symm hne), sub_zero] at h1
    rw [Ideal.Quotient.eq_zero_iff_mem.2 h1, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem Deco.Ok.yOf_nonempty {d : Deco E n ST SG} (hd : d.Ok) (G : ℕ) (hG0 : G ≠ 0) (Gw : SG → ℕ) (hG : ∀ w, Gw w * qOf w.1 = G)
    (hGw : ∀ w : SG, ((Gw w : ℕ) : 𝓞 E) ∉ w.1.asIdeal) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) : ∃ y, y ∈ d.yOf v := by
  obtain ⟨x, hx, hxc⟩ := hd.exists_beV fun w => Ideal.Quotient.mk w.1.asIdeal ((Gw w : ℕ) : 𝓞 E) • v w
  refine ⟨(G : E)⁻¹ • x, fun w => ?_⟩
  have hGE : (G : E) ≠ 0 := by exact_mod_cast hG0
  have e : ((Gw w : ℕ) : 𝓞 E) • ((qOf w.1 : E) • ((G : E)⁻¹ • x)) = x := by
    rw [← algebraMap_smul E (((Gw w : ℕ) : 𝓞 E)), map_natCast, smul_smul, smul_smul, ← Nat.cast_mul, hG w, mul_inv_cancel₀ hGE, one_smul]
  have hmem : (qOf w.1 : E) • ((G : E)⁻¹ • x) ∈ d.at w.1 := (mem_locP w.1 d.N _).2 ⟨_, hGw w, by rw [e]; exact hx⟩
  refine ⟨hmem, ?_⟩
  have h1 := hd.be_smul w ((Gw w : ℕ) : 𝓞 E) _ hmem
  rw [e, hxc w] at h1
  funext i
  have h2 := congrFun h1 i
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  exact (mul_left_cancel₀ (mk_ne_zero (hGw w)) h2).symm

end YA

section YB

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

variable {sel mu} in
theorem pc_rowSG (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (P : rowSG Pr sel mu) : P.1 ∈ Pr.vGs := by
  classical
  rcases Finset.mem_union.1 P.2 with h | h
  · exact h
  · exact absurd (hQ ▸ h : P.1 ∈ (∅ : Finset (HeightOneSpectrum (𝓞 X.E)))) (Finset.notMem_empty _)

variable {sel mu cst} in
open Classical in

theorem pc_mem_locLat_zero (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (v : Sp X.E n) :
    v ∈ locLat (rowSG Pr sel mu) N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) ↔ ∀ w : Pr.vGs, v ∈ localization₂ w.1.asIdeal N := by
  classical
  rw [mem_locLat]
  constructor
  · intro h w
    have h1 := h ⟨w.1, Finset.mem_union_left _ w.2⟩
    rw [if_pos w.2, zpow_zero, inv_one, one_smul] at h1
    exact h1
  · intro h P
    rw [if_pos (hQ P), zpow_zero, inv_one, one_smul]
    exact h ⟨P.1, hQ P⟩

theorem pc_G_notMem (hPr : Pr.Ok) {i j : Fin 2} (hij : i ≠ j) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) :
    ((Pr.g j : ℕ) : 𝓞 X.E) ∉ w.asIdeal := by
  intro h
  have h1 : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
    rw [← ciQOf_eq hPr hw]
    exact ciQ_mem w
  have hne : Pr.g i ≠ Pr.g j := by
    intro e
    apply hPr.g_ne
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact e | exact e.symm
  have hc : Nat.Coprime (Pr.g i) (Pr.g j) := (Nat.coprime_primes (hPr.g_prime i) (hPr.g_prime j)).2 hne
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc)
  have h2 : ((a : ℤ) : 𝓞 X.E) * ((Pr.g i : ℕ) : 𝓞 X.E) + ((b : ℤ) : 𝓞 X.E) * ((Pr.g j : ℕ) : 𝓞 X.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 X.E) hab
    push_cast at this
    exact this
  exact one_notMem w (h2 ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h))

theorem yOf_nonempty (hPr : Pr.Ok) {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 X.E))} {d : Deco X.E n ST Pr.vGs} (hd : d.Ok)
    (v : ∀ w : Pr.vGs, Fin n → 𝓞 X.E ⧸ w.1.asIdeal) : ∃ y, y ∈ d.yOf v := by
  classical
  refine hd.yOf_nonempty (Pr.g 0 * Pr.g 1) (Nat.mul_ne_zero (hPr.g_prime 0).ne_zero (hPr.g_prime 1).ne_zero)
    (fun w => if w.1 ∈ Pr.vG 0 then Pr.g 1 else Pr.g 0) (fun w => ?_) (fun w => ?_) v
  · by_cases h0 : w.1 ∈ Pr.vG 0
    · simp only [if_pos h0]
      rw [ciQOf_eq hPr h0, mul_comm]
    · have h1 : w.1 ∈ Pr.vG 1 := (Finset.mem_union.1 w.2).resolve_left h0
      simp only [if_neg h0]
      rw [ciQOf_eq hPr h1]
  · by_cases h0 : w.1 ∈ Pr.vG 0
    · simp only [if_pos h0]
      exact pc_G_notMem hPr (by decide) h0
    · have h1 : w.1 ∈ Pr.vG 1 := (Finset.mem_union.1 w.2).resolve_left h0
      simp only [if_neg h0]
      exact pc_G_notMem hPr (by decide) h1

theorem yOf_mem_ybSet (hX : X.Ok) (hPr : Pr.Ok) (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) {n : ℕ}
    {ST : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E n ST Pr.vGs) (v : ∀ w : Pr.vGs, Fin n → 𝓞 X.E ⧸ w.1.asIdeal) :
    d.1.yOf v ∈ ybSet sel mu cst d.1.N := by
  classical
  obtain ⟨y, hy⟩ := yOf_nonempty hPr d.2 v
  refine ⟨y, ?_, ?_⟩
  · rw [mem_locLat]
    intro P
    rw [if_pos (hQ P), _root_.zpow_neg, zpow_one, inv_inv]
    exact (hy ⟨P.1, hQ P⟩).1
  · rw [Deco.yOf_eq_of_mem (fun w => d.2.hasLift w) (fun w => ciQ_notMem_sq hX hPr w.2) hy]
    ext z
    exact (pc_mem_locLat_zero (cst := cst) hQ d.1.N (z - y)).symm

end YB

end Formalism.L2.Col
