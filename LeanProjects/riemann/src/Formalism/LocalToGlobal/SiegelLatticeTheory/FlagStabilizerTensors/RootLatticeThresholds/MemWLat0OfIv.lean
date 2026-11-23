import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictAll

noncomputable section

open NumberField
open scoped TensorProduct Pointwise
open Matrix Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.RedConj0Pf

open Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin

section

variable (I : AutInst) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E))

theorem wLat0_eq : wLat0 I w = w.asIdeal • I.L := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, y, hy, rfl⟩
    have e : ((a : 𝓞 I.E) : I.E) • y = a • y := by first | rfl | (ext i; simp [Algebra.smul_def])
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem_smul ha hy
  · refine Submodule.smul_le.2 ?_
    intro a ha y hy
    have e : ((a : 𝓞 I.E) : I.E) • y = a • y := by first | rfl | (ext i; simp [Algebra.smul_def])
    exact Submodule.subset_span ⟨a, ha, y, hy, e.symm⟩

theorem wLat0_le : wLat0 I w ≤ I.L := by
  rw [wLat0_eq]
  exact Submodule.smul_le_right

abbrev Lw : Submodule (IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F) := lamAf (F := I.F) (wLat0 I w)

theorem iv_mem_Lw {l : Fin I.n → I.E} (hl : l ∈ wLat0 I w) : iv I l ∈ Lw I w := Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩

theorem smul_mem_Lw {a : 𝓞 I.E} (ha : a ∈ w.asIdeal) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) • y ∈ Lw I w := by
  rw [DictGen.lf_eq] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hx
    have e : Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) • iv I l = iv I ((a : I.E) • l) := by
      funext i; simp [iv, Algebra.smul_def]
    rw [e]
    exact iv_mem_Lw I w (Submodule.subset_span ⟨a, ha, l, hl, rfl⟩)
  | zero => rw [smul_zero]; exact (Lw I w).zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact (Lw I w).add_mem hx hy
  | smul r x _ hx =>
    rw [Subring.smul_def, smul_comm, ← Subring.smul_def]
    exact (Lw I w).smul_mem r hx

theorem Lw_decomp (p : ℕ) (hp0 : 0 < p) {z : Fin I.n → I.E ⊗[I.F] Af I.F} (hz : z ∈ Lw I w) :
    ∃ l ∈ wLat0 I w, ∃ y ∈ I.Lf, z = iv I l + (p : I.E ⊗[I.F] Af I.F) • y := by
  have hz' : z ∈ Submodule.span (IntAf I.F I.E)
      (Set.range fun x : wLat0 I w => iv I (x : Fin I.n → I.E)) := hz
  clear hz
  induction hz' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hx
    exact ⟨l, hl, 0, I.Lf.zero_mem, by rw [smul_zero, add_zero]⟩
  | zero => exact ⟨0, (wLat0 I w).zero_mem, 0, I.Lf.zero_mem, by rw [DictLat.iv_zero, smul_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨l, hl, a, ha, rfl⟩ := hx
    obtain ⟨m, hm, b, hb, rfl⟩ := hy
    exact ⟨l + m, (wLat0 I w).add_mem hl hm, a + b, I.Lf.add_mem ha hb,
      by rw [DictLat.iv_add, smul_add]; abel⟩
  | smul r x _ hx =>
    obtain ⟨l, hl, a, ha, rfl⟩ := hx
    obtain ⟨c, r', hr', hr⟩ := dual_dense I.F I.E p hp0 r.1 r.2
    have hlL : iv I l ∈ I.Lf := DictGen.iv_mem I (wLat0_le I w hl)
    refine ⟨c • l, (wLat0 I w).smul_mem c hl, (⟨r', hr'⟩ : IntAf I.F I.E) • iv I l + r • a,
      I.Lf.add_mem (I.Lf.smul_mem _ hlL) (I.Lf.smul_mem r ha), ?_⟩
    have e1 : iv I (c • l) = Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) • iv I l := by
      funext i; simp [iv, Algebra.smul_def]
    rw [e1]
    simp only [Subring.smul_def]
    rw [hr]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem mem_wLat0_of_iv (p : ℕ) (hp0 : 0 < p) (hpw : (p : 𝓞 I.E) ∈ w.asIdeal) (y : Fin I.n → I.E)
    (hy : iv I y ∈ Lw I w) : y ∈ wLat0 I w := by
  obtain ⟨l, hl, y', hy', he⟩ := Lw_decomp I w p hp0 hy
  have hpE : (p : I.E) ≠ 0 := by exact_mod_cast hp0.ne'
  have hsub : iv I (y - l) = (p : I.E ⊗[I.F] Af I.F) • y' := by
    have e : iv I (y - l) = iv I y - iv I l := by funext i; simp [iv]
    rw [e, he]; abel
  have hu : iv I ((p : I.E)⁻¹ • (y - l)) = y' := by
    have e : iv I ((p : I.E)⁻¹ • (y - l)) =
        Formalism.UG.inclE (F := I.F) (Af I.F) ((p : I.E)⁻¹) • iv I (y - l) := by
      funext i; simp [iv, Algebra.smul_def]
    rw [e, hsub, smul_smul]
    have e2 : Formalism.UG.inclE (F := I.F) (Af I.F) ((p : I.E)⁻¹) * (p : I.E ⊗[I.F] Af I.F) = 1 := by
      rw [← map_natCast (Formalism.UG.inclE (F := I.F) (Af I.F)) p, ← map_mul, inv_mul_cancel₀ hpE, map_one]
    rw [e2, one_smul]
  have huL : (p : I.E)⁻¹ • (y - l) ∈ I.L := lattice_intersection' I _ (hu ▸ hy')
  have hyl : y - l ∈ wLat0 I w := by
    have e : y - l = ((p : 𝓞 I.E) : I.E) • ((p : I.E)⁻¹ • (y - l)) := by
      rw [smul_smul]; push_cast; rw [mul_inv_cancel₀ hpE, one_smul]
    rw [e]
    exact Submodule.subset_span ⟨p, hpw, _, huL, rfl⟩
  have e : y = l + (y - l) := by abel
  rw [e]
  exact (wLat0 I w).add_mem hl hyl

theorem charP_res (p : ℕ) (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) :
    CharP (𝓞 I.E ⧸ w.asIdeal) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (𝓞 I.E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  haveI := Fintype.ofFinite (𝓞 I.E ⧸ w.asIdeal)
  exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hcard])

theorem p_mem (p : ℕ) (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) :
    (p : 𝓞 I.E) ∈ w.asIdeal := by
  haveI := charP_res I w p hp hcard
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem int_mem_iff (p : ℕ) (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (z : ℤ) :
    (z : 𝓞 I.E) ∈ w.asIdeal ↔ (p : ℤ) ∣ z := by
  haveI := charP_res I w p hp hcard
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast]
  exact CharP.intCast_eq_zero_iff _ p z

theorem span_of_red {m : ℕ} {b : Fin m → (Fin I.n → I.E)} (hb : IsRedBasis0 I w b) :
    I.L ≤ Submodule.span (𝓞 I.E) (Set.range b) ⊔ w.asIdeal • I.L := by
  intro y hy
  obtain ⟨c, hc⟩ := hb.2 y hy
  rw [← wLat0_eq]
  have hS : ∑ i, (c i : I.E) • b i ∈ Submodule.span (𝓞 I.E) (Set.range b) := by
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : (c i : I.E) • b i = (c i : 𝓞 I.E) • b i := by
      ext j; simp [Algebra.smul_def]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have e : y = ∑ i, (c i : I.E) • b i + (y - ∑ i, (c i : I.E) • b i) := by abel
  rw [e]
  exact Submodule.add_mem_sup hS hc

theorem indep {b : Fin I.n → (Fin I.n → I.E)} (hb : ∀ i, b i ∈ I.L)
    (hsp : I.L ≤ Submodule.span (𝓞 I.E) (Set.range b) ⊔ w.asIdeal • I.L)
    (c : Fin I.n → 𝓞 I.E) (hc : ∑ j, c j • b j ∈ w.asIdeal • I.L) (j0 : Fin I.n) : c j0 ∈ w.asIdeal := by
  classical
  have hsm : ∀ (a : 𝓞 I.E) (v : Fin I.n → I.E), a • v = (a : I.E) • v := fun a v => by
    first | rfl | (ext i; simp [Algebra.smul_def])
  obtain ⟨r, hr1, hr⟩ : ∃ r : 𝓞 I.E, r - 1 ∈ w.asIdeal ∧
      ∀ x ∈ I.L, r • x ∈ Submodule.span (𝓞 I.E) (Set.range b) := by
    set S := Submodule.span (𝓞 I.E) (Set.range b) with hS
    have hfg : (I.L.map S.mkQ).FG := I.L_fg.map _
    have hle : I.L.map S.mkQ ≤ w.asIdeal • I.L.map S.mkQ := by
      rw [← Submodule.map_smul'']
      intro q hq
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hq
      obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 (hsp hx)
      refine Submodule.mem_map.2 ⟨t, ht, ?_⟩
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      rw [show t - (s + t) = -s by abel]
      exact S.neg_mem hs
    obtain ⟨r, hr1, hr⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul w.asIdeal _ hfg hle
    refine ⟨r, hr1, fun x hx => ?_⟩
    have h := hr _ (Submodule.mem_map_of_mem (f := S.mkQ) hx)
    rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  have hrw : r ∉ w.asIdeal := by
    intro h
    have h1 : (1 : 𝓞 I.E) ∈ w.asIdeal := by
      have := w.asIdeal.sub_mem h hr1
      simpa using this
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hr0 : (r : I.E) ≠ 0 := by
    intro h
    apply hrw
    have : r = 0 := RingOfIntegers.ext (by simpa using h)
    rw [this]
    exact w.asIdeal.zero_mem
  have hspan : ⊤ ≤ Submodule.span I.E (Set.range b) := by
    rw [← I.L_span]
    refine Submodule.span_le.2 fun x hx => ?_
    have h1 : r • x ∈ Submodule.span I.E (Set.range b) :=
      Submodule.span_le_restrictScalars (𝓞 I.E) I.E (Set.range b) (hr x hx)
    have e : x = (r : I.E)⁻¹ • (r • x) := by
      rw [hsm, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ h1
  have hli : LinearIndependent I.E b :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp)
  have hmap : (I.L).map (r • LinearMap.id) ≤ Submodule.span (𝓞 I.E) (Set.range b) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hr x hx
  have hrel : r • ∑ j, c j • b j ∈ w.asIdeal • Submodule.span (𝓞 I.E) (Set.range b) := by
    have h : r • ∑ j, c j • b j ∈ (w.asIdeal • I.L).map (r • LinearMap.id) := ⟨_, hc, rfl⟩
    rw [Submodule.map_smul''] at h
    exact Submodule.smul_mono le_rfl hmap h
  obtain ⟨d, hd, hdx⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum w.asIdeal b _).1 hrel
  rw [Finsupp.sum_fintype _ _ (by simp)] at hdx
  have hsum : ∑ i, ((r * c i - d i : 𝓞 I.E) : I.E) • b i = 0 := by
    have e : ∑ i, ((r * c i - d i : 𝓞 I.E) : I.E) • b i = ∑ i, (r * c i - d i) • b i := by
      simp_rw [hsm]
    rw [e]
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hdx, sub_self]
  have key := Fintype.linearIndependent_iff.1 hli (fun i => ((r * c i - d i : 𝓞 I.E) : I.E)) hsum j0
  have h0 : r * c j0 - d j0 = 0 := RingOfIntegers.ext (by simpa using key)
  have hmem : r * c j0 ∈ w.asIdeal := by rw [sub_eq_zero.1 h0]; exact hd j0
  exact (w.isPrime.mem_or_mem hmem).resolve_left hrw

theorem zcoef (p : ℕ) (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {b : Fin I.n → (Fin I.n → I.E)} (hb : IsRedBasis0 I w b) (z : Fin I.n → ℤ)
    (hz : ∑ l, z l • b l ∈ wLat0 I w) (l : Fin I.n) : ((z l : ℤ) : ZMod p) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hsp := span_of_red I w hb
  have hc : ∑ j, (z j : 𝓞 I.E) • b j ∈ w.asIdeal • I.L := by
    rw [← wLat0_eq]
    convert hz using 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ext i; simp [Algebra.smul_def, zsmul_eq_mul]
  have h := indep I w hb.1 hsp (fun j => (z j : 𝓞 I.E)) hc l
  rw [int_mem_iff I w p hp hcard] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h

end

theorem comb {G : Type*} [AddCommGroup G] {n : ℕ} (β : Fin n → G) (X Y : Matrix (Fin n) (Fin n) ℤ)
    (i : Fin n) : ∑ k, Y k i • ∑ l, X l k • β l = ∑ l, (X * Y) l i • β l := by
  simp only [Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

end Formalism.L2.SG.Pf.RedConj0Pf
