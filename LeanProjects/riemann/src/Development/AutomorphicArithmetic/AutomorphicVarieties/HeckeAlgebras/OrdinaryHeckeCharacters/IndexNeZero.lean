import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.TcAnti
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LduDecompositionExists
open Matrix ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi

namespace UpperTheory.V.Hi.GlAx

theorem mem_low {R : Type} [CommRing R] {n : ℕ} {y : GL (Fin n) R} :
    y ∈ (unipB R (Fin n)).comap (GlobalTheory.CuspRep.invT n R) ↔
      (∀ i j, i < j → (y : Matrix (Fin n) (Fin n) R) i j = 0) ∧ ∀ i, (y : Matrix (Fin n) (Fin n) R) i i = 1 := by
  rw [← inv_mem_iff, Subgroup.mem_comap, mem_unipB]
  exact ⟨fun h => ⟨fun i j hij => h.1 j i hij, h.2⟩, fun h => ⟨fun i j hij => h.1 j i hij, h.2⟩⟩

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7 Formalism.FourierDecayAlt.S3 Formalism.DoubleCosetMeasures in
theorem udl {A : Type} [CommRing A] [IsLocalRing A] {n : ℕ} (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A)
    (g : GL (Fin n) A) (hg : GeneralLinearGroup.map (Ideal.Quotient.mk I) g = 1) :
    ∃ u ∈ unipB A (Fin n), ∃ t : Fin n → Aˣ, ∃ l ∈ (unipB A (Fin n)).comap (GlobalTheory.CuspRep.invT n A),
      GeneralLinearGroup.map (Ideal.Quotient.mk I) (diagT A (Fin n) t) = 1 ∧
      GeneralLinearGroup.map (Ideal.Quotient.mk I) l = 1 ∧ g = u * diagT A (Fin n) t * l := by
  set π := Ideal.Quotient.mk I
  have hg' : GeneralLinearGroup.map π g⁻¹ = 1 := by rw [map_inv, hg, inv_one]
  have hM : (g⁻¹).val.map π = 1 := congrArg Units.val hg'
  have hu : ∀ x : A, π x = 1 → IsUnit x := fun x hx => by
    have h1 : 1 - x ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]; exact sub_eq_zero.2 hx.symm
    exact (IsLocalRing.isUnit_or_isUnit_one_sub_self x).resolve_right (hI h1)
  obtain ⟨L, U, d, hL, hU, hE, -⟩ := ldu_decomposition_exists A n (g⁻¹).val fun l hl => hu _ (by
    rw [lead, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, hM,
      Matrix.submatrix_one _ (Fin.castLE_injective _), det_one])
  have hE' : L.map π * diagonal (fun i => π (d i)) * U.map π = 1 := by
    rw [← hM, hE, Matrix.map_mul, Matrix.map_mul, diagonal_map (map_zero π)]
  obtain ⟨h1, h2, -⟩ := ldu_unique (L := L.map π) (U := U.map π) (d := fun i => π (d i)) (L' := 1) (U' := 1)
    (d' := fun _ => 1)
    (mk_low (fun i j h => by rw [map_apply, low_apply hL h, map_zero]) fun i => by rw [map_apply, hL.2, map_one])
    (mk_up (fun i j h => by rw [map_apply, up_apply hU h, map_zero]) fun i => by rw [map_apply, hU.2, map_one])
    (isLowUni_one _) (isUpUni_one _)
    (by rw [hE', lead, Matrix.submatrix_one _ (Fin.castLE_injective _), det_one]; exact one_mem _)
    (by rw [hE']; simp)
  let L' : GL (Fin n) A := GeneralLinearGroup.mk'' L (by rw [isLowUni_det A hL]; exact isUnit_one)
  let U' : GL (Fin n) A := GeneralLinearGroup.mk'' U (by rw [isUpUni_det A hU]; exact isUnit_one)
  let t : Fin n → Aˣ := fun i => (hu _ (congrFun h2 i)).unit
  have e : g⁻¹ = L' * diagT A (Fin n) t * U' := Units.ext (by
    rw [hE, Units.val_mul, Units.val_mul, val_diagT]; rfl)
  refine ⟨U'⁻¹, inv_mem ((mem_unipB _).2 ⟨fun i j h => up_apply hU h, hU.2⟩), t⁻¹, L'⁻¹,
    inv_mem (mem_low.2 ⟨fun i j h => low_apply hL h, hL.2⟩), ?_, ?_, ?_⟩
  · rw [map_inv, map_inv, inv_eq_one]
    refine Units.ext ?_
    change (diagT A (Fin n) t).val.map π = 1
    rw [val_diagT, diagonal_map (map_zero π)]
    exact (congrArg diagonal h2).trans diagonal_one
  · rw [map_inv, inv_eq_one]
    exact Units.ext h1
  · rw [← inv_inv g, e, map_inv]; group

theorem conj_apply {R : Type} [CommRing R] {n : ℕ} (t : Fin n → Rˣ) (g : GL (Fin n) R) (i j : Fin n) :
    (diagT R (Fin n) t * g * (diagT R (Fin n) t)⁻¹).val i j = t i * g.val i j * ((t j)⁻¹ : Rˣ) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal, diagonal_mul]; rfl

theorem conj_sub_one {R : Type} [CommRing R] {n : ℕ} (t : Fin n → Rˣ) (g : GL (Fin n) R) (i j : Fin n) :
    ((diagT R (Fin n) t * g * (diagT R (Fin n) t)⁻¹).val - 1) i j = t i * (g.val - 1) i j * ((t j)⁻¹ : Rˣ) := by
  rw [Matrix.sub_apply, Matrix.sub_apply, conj_apply, Matrix.one_apply]
  split_ifs with h
  · subst h; rw [mul_sub, sub_mul]; simp
  · simp

theorem conj_up {R : Type} [CommRing R] {n : ℕ} (t : Fin n → Rˣ) {g : GL (Fin n) R} (hg : g ∈ unipB R (Fin n)) :
    diagT R (Fin n) t * g * (diagT R (Fin n) t)⁻¹ ∈ unipB R (Fin n) := by
  rw [mem_unipB] at hg ⊢
  exact ⟨fun i j h => by rw [conj_apply, hg.1 i j h]; simp, fun i => by rw [conj_apply, hg.2]; simp⟩

theorem conj_low {R : Type} [CommRing R] {n : ℕ} (t : Fin n → Rˣ) {g : GL (Fin n) R}
    (hg : g ∈ (unipB R (Fin n)).comap (GlobalTheory.CuspRep.invT n R)) :
    diagT R (Fin n) t * g * (diagT R (Fin n) t)⁻¹ ∈ (unipB R (Fin n)).comap (GlobalTheory.CuspRep.invT n R) := by
  rw [mem_low] at hg ⊢
  exact ⟨fun i j h => by rw [conj_apply, hg.1 i j h]; simp, fun i => by rw [conj_apply, hg.2]; simp⟩

theorem up_sub_one {R : Type} [CommRing R] {n : ℕ} {g : GL (Fin n) R} (hg : g ∈ unipB R (Fin n)) {i j : Fin n}
    (h : j ≤ i) : (g.val - 1) i j = 0 := by
  rw [mem_unipB] at hg
  rcases h.eq_or_lt with rfl | h
  · simp [hg.2]
  · simp [hg.1 i j h, one_apply_ne h.ne']

theorem low_sub_one {R : Type} [CommRing R] {n : ℕ} {g : GL (Fin n) R}
    (hg : g ∈ (unipB R (Fin n)).comap (GlobalTheory.CuspRep.invT n R)) {i j : Fin n}
    (h : i ≤ j) : (g.val - 1) i j = 0 := by
  rw [mem_low] at hg
  rcases h.eq_or_lt with rfl | h
  · simp [hg.2]
  · simp [hg.1 i j h, one_apply_ne h.ne]

theorem uniq {R : Type} [CommRing R] {n : ℕ} {x y : GL (Fin n) R} (t : Fin n → Rˣ) (hx : x ∈ unipB R (Fin n))
    (hy : y ∈ (unipB R (Fin n)).comap (GlobalTheory.CuspRep.invT n R)) (h : x * diagT R (Fin n) t * y = 1) :
    x = 1 ∧ diagT R (Fin n) t = 1 := by
  have e : x * diagT R (Fin n) t = y⁻¹ := eq_inv_of_mul_eq_one_left h
  have hy' := inv_mem hy
  have ht : t = 1 := funext fun i => Units.ext (by
    have h1 := (mem_low.1 hy').2 i
    rw [← e, Units.val_mul, val_diagT, mul_diagonal, ((mem_unipB _).1 hx).2, one_mul] at h1
    exact h1)
  rw [ht, map_one, mul_one] at e
  refine ⟨Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => ?_)), by rw [ht, map_one]⟩
  rcases le_total i j with hij | hij
  · exact low_sub_one (e ▸ hy') hij
  · exact up_sub_one hx hij

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem unif_pos : 0 < uniformizer k := zero_lt_iff.2 (by simp)

theorem unif_spec : valuation k (unif k : k) = uniformizer k := by
  refine Classical.epsilon_spec (p := fun x : kˣ => valuation k (x : k) = uniformizer k) ?_
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  refine ⟨Units.mk0 x ?_, hx⟩
  rintro rfl
  exact unif_pos.ne ((map_zero _).symm.trans hx)

theorem zpow_le {a b : ℤ} (h : b ≤ a) : uniformizer k ^ a ≤ uniformizer k ^ b :=
  zpow_le_zpow_right_of_le_one₀ unif_pos uniformizer_lt_one.le h

theorem val_div_ord (x : kˣ) : valuation k ((x / unif k ^ ord k x : kˣ) : k) = 1 := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h1 : o (x / unif k ^ ord k x) = 1 := by
    rw [map_div, map_zpow, show o (unif k) = .ofAdd 1 from congrArg Multiplicative.ofAdd (ord_eq_one unif_spec),
      ← ofAdd_zsmul, smul_eq_mul, mul_one]
    exact div_self' _
  exact ord_eq_zero_iff.1 (ofAdd_eq_one.1 h1)

theorem val_zpow (a : ℤ) : valuation k ((unif k ^ a : kˣ) : k) = uniformizer k ^ a := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, unif_spec]

theorem exists_le (x : k) : ∃ m : ℤ, valuation k x ≤ uniformizer k ^ m := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  · refine ⟨ord k (Units.mk0 x hx), le_of_eq ?_⟩
    have h := val_div_ord (Units.mk0 x hx)
    rw [Units.val_div_eq_div_val, map_div₀, val_zpow] at h
    exact (div_eq_one_iff_eq (zpow_pos unif_pos _).ne').1 h

theorem mem_pow (c : ℕ) (x : 𝒪[k]) :
    x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c ↔ valuation k (x : k) ≤ uniformizer k ^ (c : ℤ) := by
  have hv := Valuation.integer.integers (valuation k)
  let p : 𝒪[k] := ⟨unif k, (unif_spec.trans_lt uniformizer_lt_one).le⟩
  have hp : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {p} := by
    ext y
    rw [Ideal.mem_span_singleton, hv.dvd_iff_le, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      hv.isUnit_iff_valuation_eq_one]
    change _ ↔ valuation k (y : k) ≤ valuation k (unif k : k)
    rw [unif_spec, le_uniformizer_iff]
    exact ⟨fun h => lt_of_le_of_ne y.2 h, fun h => h.ne⟩
  rw [hp, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hv.dvd_iff_le, map_pow, map_pow, zpow_natCast]
  change valuation k (x : k) ≤ valuation k (unif k : k) ^ c ↔ _
  rw [unif_spec]

def Bd (c : ℤ) (g : GL (Fin n) k) : Prop := ∀ i j, valuation k ((g.val - 1) i j) ≤ uniformizer k ^ c

theorem bd_zero {g : GL (Fin n) k} : Bd 0 g ↔ ∀ i j, g.val i j ∈ 𝒪[k] := by
  refine forall₂_congr fun i j => ?_
  have h1 : (1 : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
    rw [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  rw [zpow_zero, Matrix.sub_apply]
  exact ⟨fun h => by simpa using add_mem (show _ ∈ 𝒪[k] from h) h1, fun h => sub_mem h h1⟩

theorem Bd.mono {c c' : ℤ} {g : GL (Fin n) k} (h : Bd c g) (hc : c' ≤ c) : Bd c' g :=
  fun i j => (h i j).trans (zpow_le hc)

theorem exists_bd (g : GL (Fin n) k) : ∃ m : ℕ, Bd (-m) g := by
  choose f hf using fun p : Fin n × Fin n => exists_le ((g.val - 1) p.1 p.2)
  obtain ⟨m, hm⟩ := (Set.finite_range fun p => (f p).natAbs).bddAbove
  refine ⟨m, fun i j => (hf (i, j)).trans (zpow_le ?_)⟩
  have : (f (i, j)).natAbs ≤ m := hm ⟨(i, j), rfl⟩
  omega

theorem mem_KO {g : GL (Fin n) k} : g ∈ KO k (Fin n) ↔ Bd 0 g ∧ Bd 0 g⁻¹ := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff, bd_zero, bd_zero]

theorem map_eq_one (c : ℕ) (h : GL (Fin n) 𝒪[k]) :
    GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c)) h = 1 ↔
      Bd c (GeneralLinearGroup.map (algebraMap 𝒪[k] k) h) := by
  rw [Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  have e : ((GeneralLinearGroup.map (algebraMap 𝒪[k] k) h).val - 1) i j = (((h.val - 1) i j : 𝒪[k]) : k) := by
    simp only [Matrix.sub_apply, Matrix.one_apply]
    split_ifs <;> rfl
  rw [e, ← mem_pow, ← Ideal.Quotient.eq_zero_iff_mem, Matrix.sub_apply, map_sub, sub_eq_zero]
  refine Eq.congr rfl ?_
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem mem_Kc {c : ℕ} {g : GL (Fin n) k} : g ∈ Kc k n c ↔ Bd c g ∧ Bd c g⁻¹ := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨(map_eq_one c h).1 hh, ?_⟩
    rw [← map_inv]
    exact (map_eq_one c _).1 (inv_mem hh)
  · rintro ⟨h1, h2⟩
    obtain ⟨h, rfl⟩ := mem_KO.2 ⟨h1.mono (by omega), h2.mono (by omega)⟩
    exact ⟨h, (map_eq_one c h).2 h1, rfl⟩

theorem Kc_zero : Kc k n 0 = KO k (Fin n) := by
  ext g; rw [mem_Kc, mem_KO]; rfl

theorem Kc_anti : Antitone (Kc k n) := fun a b hab g hg =>
  mem_Kc.2 ⟨(mem_Kc.1 hg).1.mono (by omega), (mem_Kc.1 hg).2.mono (by omega)⟩

theorem Kc_le (c : ℕ) : Kc k n c ≤ KO k (Fin n) := Kc_zero (k := k) (n := n) ▸ Kc_anti (Nat.zero_le c)

theorem Kc_index (c : ℕ) {H : Subgroup (GL (Fin n) k)} (hH : H ≤ KO k (Fin n)) : (Kc k n c).relIndex H ≠ 0 := by
  refine fun h => absurd (Subgroup.relIndex_eq_zero_of_le_right hH h) ?_
  have inj : Function.Injective (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)) := fun A B h =>
    Units.ext (Matrix.ext fun i j => Subtype.ext (congrArg (fun g : GL (Fin n) k => g.val i j) h))
  have : Finite (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k]) := inferInstanceAs (Finite 𝓀[k])
  have := Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal 𝒪[k])) c
  rw [Kc, KO, MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ inj, Subgroup.relIndex_top_right,
    Subgroup.index_ker]
  have : Finite (Matrix (Fin n) (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ c)) :=
    inferInstanceAs (Finite (Fin n → Fin n → _))
  have : Finite (GL (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ c)) :=
    Finite.of_injective _ Units.val_injective
  exact Nat.card_pos.ne'

theorem index_ne_zero (c : ℕ) {H H' : Subgroup (GL (Fin n) k)} (hH : H ≤ KO k (Fin n)) (h : Kc k n c ⊓ H ≤ H') :
    H'.relIndex H ≠ 0 := fun h0 =>
  Kc_index c hH (by rw [← Subgroup.inf_relIndex_right]; exact Subgroup.relIndex_eq_zero_of_le_left h h0)

theorem Bd.conj {c c' : ℤ} {g : GL (Fin n) k} (h : Bd c g) (t : Fin n → kˣ) (a : Fin n → ℤ)
    (ht : ∀ i, valuation k (t i : k) = uniformizer k ^ a i)
    (H : ∀ i j, (g.val - 1) i j = 0 ∨ c' + a j ≤ c + a i) :
    Bd c' (diagT k (Fin n) t * g * (diagT k (Fin n) t)⁻¹) := fun i j => by
  rw [conj_sub_one]
  rcases H i j with H | H
  · simp [H]
  · rw [map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, ht, ht, ← _root_.zpow_neg]
    calc _ ≤ uniformizer k ^ a i * uniformizer k ^ c * uniformizer k ^ (-a j) := by
          gcongr; exact h i j
      _ ≤ _ := by
          rw [← zpow_add₀ unif_pos.ne', ← zpow_add₀ unif_pos.ne']
          exact zpow_le (by omega)

theorem conj_Kc {c c' : ℤ} {S : Subgroup (GL (Fin n) k)} {g : GL (Fin n) k} (hS : g ∈ S) (h : Bd c g ∧ Bd c g⁻¹)
    (t : Fin n → kˣ) (a : Fin n → ℤ) (ht : ∀ i, valuation k (t i : k) = uniformizer k ^ a i)
    (H : ∀ i j, (∀ x ∈ S, (x.val - 1) i j = 0) ∨ c' + a j ≤ c + a i) :
    Bd c' (diagT k (Fin n) t * g * (diagT k (Fin n) t)⁻¹) ∧
      Bd c' (diagT k (Fin n) t * g * (diagT k (Fin n) t)⁻¹)⁻¹ := by
  refine ⟨h.1.conj t a ht fun i j => (H i j).imp_left fun H => H _ hS, ?_⟩
  rw [conj_inv]
  exact h.2.conj t a ht fun i j => (H i j).imp_left fun H => H _ (inv_mem hS)

theorem upow_add (a b : Fin n → ℤ) : upow k n (a + b) = upow k n a * upow k n b := by
  rw [upow, upow, upow, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

theorem upow_neg (a : Fin n → ℤ) : upow k n (-a) = (upow k n a)⁻¹ := by
  rw [upow, upow, ← map_inv]
  congr 1
  funext i
  simp

theorem upow_pow (a : Fin n → ℤ) (m : ℕ) : upow k n a ^ m = upow k n fun i => m * a i := by
  rw [upow, upow, ← map_pow]
  congr 1
  funext i
  rw [Pi.pow_apply, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]

theorem exists_anti (o : Fin n → ℤ) : ∃ m : ℕ, Antitone fun i : Fin n => m * ((n : ℤ) - 1 - (i : ℕ)) + o i := by
  obtain ⟨m, hm⟩ := (Set.finite_range fun p : Fin n × Fin n => (o p.1 - o p.2).natAbs).bddAbove
  refine ⟨m, fun i j hij => ?_⟩
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  have h1 : (o i - o j).natAbs ≤ m := hm ⟨(i, j), rfl⟩
  have h2 : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast hij
  have h3 : o j - o i ≤ m := by omega
  change (m : ℤ) * _ + _ ≤ m * _ + _
  nlinarith [mul_le_mul_of_nonneg_left h2 (Int.natCast_nonneg m)]

end Loc

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem conj_N {t : Fin n → kˣ} {a : Fin n → ℤ} (ht : ∀ i, valuation k (t i : k) = uniformizer k ^ a i)
    (ha : Antitone a) {x : GL (Fin n) k} (hx : x ∈ (glData k n).N) :
    diagT k (Fin n) t * x * (diagT k (Fin n) t)⁻¹ ∈ (glData k n).N :=
  ⟨conj_up t hx.1, mem_KO.2 (conj_Kc hx.1 (mem_KO.1 hx.2) t a ht fun i j =>
    (le_total j i).imp (fun h _ hx => up_sub_one hx h) fun h => by have := ha h; omega)⟩

theorem conj_Nm {t : Fin n → kˣ} {a : Fin n → ℤ} (ht : ∀ i, valuation k (t i : k) = uniformizer k ^ a i)
    {c c' : ℕ} (ha : ∀ i j, j < i → c' + a j ≤ c + a i) {y : GL (Fin n) k} (hy : y ∈ (glData k n).Nm c) :
    diagT k (Fin n) t * y * (diagT k (Fin n) t)⁻¹ ∈ (glData k n).Nm c' :=
  ⟨conj_low t hy.1, mem_Kc.2 (conj_Kc hy.1 (mem_Kc.1 hy.2) t a ht fun i j =>
    (le_or_gt i j).imp (fun h _ hx => low_sub_one hx h) fun h => by have := ha i j h; push_cast; omega)⟩

theorem conj_Nm' (a : Fin n → ℤ) {c c' : ℕ} (ha : ∀ i j, j < i → c' + a i ≤ c + a j) {y : GL (Fin n) k}
    (hy : y ∈ (glData k n).Nm c) : (upow k n a)⁻¹ * y * upow k n a ∈ (glData k n).Nm c' := by
  have := conj_Nm (a := -a) (t := fun i => unif k ^ (-a) i) (fun i => val_zpow _) (c := c) (c' := c')
    (fun i j h => by have := ha i j h; simp only [Pi.neg_apply]; omega) hy
  change upow k n (-a) * y * (upow k n (-a))⁻¹ ∈ _ at this
  rwa [upow_neg, inv_inv] at this

theorem swap (c : ℕ) {y x : GL (Fin n) k} (hy : y ∈ (glData k n).Nm c) (hx : x ∈ (glData k n).N) :
    ∃ x' ∈ (glData k n).N, ∃ t ∈ (glData k n).Tc c, ∃ y' ∈ (glData k n).Nm c, y * x = x' * t * y' := by
  obtain ⟨-, y₀, hy₀, rfl⟩ := hy
  obtain ⟨hx, x₀, rfl⟩ := hx
  obtain ⟨u, hu, t, l, hl, ht1, hl1, e⟩ := udl (IsLocalRing.maximalIdeal 𝒪[k] ^ (c + 1))
    (Ideal.pow_le_self (Nat.succ_ne_zero c)) (x₀⁻¹ * y₀ * x₀)
    (by rw [map_mul, map_mul, MonoidHom.mem_ker.1 hy₀, map_inv, mul_one, inv_mul_cancel])
  rw [mem_unipB] at hu
  rw [mem_low] at hl
  refine ⟨GeneralLinearGroup.map (algebraMap 𝒪[k] k) (x₀ * u), ⟨?_, _, rfl⟩,
    GeneralLinearGroup.map (algebraMap 𝒪[k] k) (diagT _ (Fin n) t),
    ⟨⟨fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (t i), fun i => ?_, ?_⟩, _, ht1, rfl⟩,
    GeneralLinearGroup.map (algebraMap 𝒪[k] k) l, ⟨mem_low.2 ⟨fun i j h => ?_, fun i => ?_⟩, _, hl1, rfl⟩, ?_⟩
  · rw [map_mul]
    exact mul_mem hx ((mem_unipB _).2 ⟨fun i j h => congrArg (algebraMap 𝒪[k] k) (hu.1 i j h),
      fun i => congrArg (algebraMap 𝒪[k] k) (hu.2 i)⟩)
  · exact (Valuation.integer.integers (valuation k)).one_of_isUnit (t i).isUnit
  · refine Units.ext ?_
    change _ = (diagT _ (Fin n) t).val.map (algebraMap 𝒪[k] k)
    rw [val_diagT, val_diagT, diagonal_map (map_zero _)]
    rfl
  · exact congrArg (algebraMap 𝒪[k] k) (hl.1 i j h)
  · exact congrArg (algebraMap 𝒪[k] k) (hl.2 i)
  · rw [← map_mul, ← map_mul, ← map_mul, mul_assoc x₀, mul_assoc x₀, ← e]
    congr 1
    group

theorem T_le_KO : (glData k n).T ≤ KO k (Fin n) := by
  rintro _ ⟨t, ht, rfl⟩
  exact iwahori_le_KO k _ (diagT_mem_iwahori ht)

theorem fin_N (a : Fin n → ℤ) :
    ((glData k n).N.map (MulAut.conj (upow k n a)).toMonoidHom).relIndex (glData k n).N ≠ 0 := by
  obtain ⟨m, hm⟩ := (Set.finite_range fun p : Fin n × Fin n => (a p.1 - a p.2).natAbs).bddAbove
  refine index_ne_zero m inf_le_right fun x hx => ⟨(upow k n a)⁻¹ * x * upow k n a, ?_, ?_⟩
  · have : upow k n (-a) * x * (upow k n (-a))⁻¹ ∈ (glData k n).N :=
      ⟨conj_up _ hx.2.1, mem_KO.2 (conj_Kc hx.2.1 (mem_Kc.1 hx.1) _ (-a) (fun i => val_zpow _) fun i j => Or.inr (by
        have h1 : (a i - a j).natAbs ≤ m := hm ⟨(i, j), rfl⟩
        simp only [Pi.neg_apply]; omega))⟩
    rwa [upow_neg, inv_inv] at this
  · simp [mul_assoc]

theorem exh {x : GL (Fin n) k} (hx : x ∈ unipB k (Fin n)) :
    ∃ m : ℕ, (glData k n).z ^ m * x * ((glData k n).z ^ m)⁻¹ ∈ (glData k n).N := by
  obtain ⟨a, ha⟩ := exists_bd x
  obtain ⟨b, hb⟩ := exists_bd x⁻¹
  refine ⟨a + b, ?_⟩
  change upow k n _ ^ _ * x * (upow k n _ ^ _)⁻¹ ∈ _
  rw [upow_pow]
  refine ⟨conj_up _ hx, mem_KO.2 (conj_Kc (c := -((a + b : ℕ) : ℤ)) hx ⟨ha.mono (by omega), hb.mono (by omega)⟩ _ _
    (fun i => val_zpow _) fun i j => (le_or_gt j i).imp (fun h _ hx => up_sub_one hx h) fun h => ?_)⟩
  have h2 : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast h
  nlinarith [mul_le_mul_of_nonneg_left h2 (Int.natCast_nonneg (a + b))]

theorem z_anti : Antitone fun i : Fin n => (n : ℤ) - 1 - (i : ℕ) := fun i j h => by
  have : (i : ℕ) ≤ j := h
  change (n : ℤ) - 1 - (j : ℕ) ≤ (n : ℤ) - 1 - (i : ℕ)
  omega

theorem z_mul (o : Fin n → ℤ) : ∃ m : ℕ, (glData k n).z ^ m * upow k n o ∈ (glData k n).P := by
  obtain ⟨m, hm⟩ := exists_anti o
  refine ⟨m, _, hm, ?_⟩
  change upow k n _ ^ _ * _ = _
  rw [upow_pow, ← upow_add]
  rfl

end Main

end UpperTheory.V.Hi.GlAx

open UpperTheory.V.Hi.GlAx in
theorem UpperTheory.V.Hi.glAx :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), (glData k n).Ax := by
  intro k _ _ _ _ n
  have comm : ∀ s ∈ (glData k n).Tf, ∀ t ∈ (glData k n).Tf, s * t = t * s := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hz : (glData k n).z ∈ (glData k n).P := ⟨_, z_anti, rfl⟩
  refine
    { N_le := inf_le_left
      T_le := Subgroup.map_le_range _ _
      P_le := by rintro _ ⟨a, -, rfl⟩; exact ⟨_, rfl⟩
      z_mem := hz
      Tc_le := fun c => inf_le_left
      Tc_anti := fun a b h => inf_le_inf_left _ (Kc_anti (Nat.succ_le_succ h))
      Nm_anti := fun a b h => inf_le_inf_left _ (Kc_anti (Nat.succ_le_succ h))
      comm := comm
      Tf_Nf := by rintro _ ⟨t, rfl⟩ x hx; exact conj_up t hx
      T_N := by
        rintro _ ⟨t, ht, rfl⟩ x hx
        exact conj_N (a := 0) (fun i => (ht i).trans (zpow_zero _).symm) (fun _ _ _ => le_rfl) hx
      T_Nm := by
        rintro c _ ⟨t, ht, rfl⟩ x hx
        exact conj_Nm (a := 0) (fun i => (ht i).trans (zpow_zero _).symm) (fun _ _ _ => le_rfl) hx
      P_N := by
        rintro _ ⟨a, ha, rfl⟩ x hx
        exact conj_N (fun i => val_zpow _) ha hx
      P_Nm := by
        rintro c _ ⟨a, ha, rfl⟩ y hy
        exact conj_Nm' a (fun i j h => by have := ha h.le; omega) hy
      z_Nm := fun c y hy => conj_Nm' _ (fun i j h => by
        have : (j : ℕ) < i := h
        push_cast; omega) hy
      swap := fun c y hy x hx => swap c hy hx
      uniq := by rintro x hx _ ⟨t, rfl⟩ y hy h; exact uniq t hx hy.1 h
      fin_N := by rintro _ ⟨a, -, rfl⟩; exact fin_N a
      fin_Nm := fun c => index_ne_zero (c + 1) (inf_le_right.trans (Kc_le _)) fun y hy => ⟨hy.2.1, hy.1⟩
      fin_Tc := fun c => index_ne_zero (c + 1) T_le_KO fun y hy => ⟨hy.2, hy.1⟩
      exh := fun x hx => exh hx
      exists_pow_mul_inv_mem := by
        rintro _ ⟨a, -, rfl⟩
        rw [← upow_neg]
        exact z_mul _
      gen := ?_ }
  rintro _ ⟨t, rfl⟩
  obtain ⟨m, hm⟩ := z_mul (k := k) fun i => ord k (t i)
  refine ⟨_, ⟨fun i => t i / unif k ^ ord k (t i), fun i => val_div_ord _, rfl⟩, _, hm, _, pow_mem hz m, ?_⟩
  have h : (glData k n).z ^ m * upow k n (fun i => ord k (t i)) = upow k n (fun i => ord k (t i)) * (glData k n).z ^ m :=
    comm _ (pow_mem (⟨_, rfl⟩ : (glData k n).z ∈ (glData k n).Tf) m) _ ⟨_, rfl⟩
  rw [h, mul_assoc, mul_inv_cancel_right, upow, ← map_mul]
  congr 1
  funext i
  simp
