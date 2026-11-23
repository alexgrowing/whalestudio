import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal

private theorem host_bar_bar' {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) :
    H.bar (H.bar a) = a :=
  RingOfIntegers.ext (by rw [H.bar_eq, H.bar_eq, NumberField.IsCMField.complexConj_apply_apply])

private theorem levelM_mem_Mb_and_Mfr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (l : Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ l.Mb ∧ (l.M : 𝓞 E) ∈ Mfr l := by
  have h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]; exact Ideal.mem_span_singleton_self _
  have h2 : (l.M : 𝓞 E) ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mul_le_right h
  exact ⟨Ideal.mul_le_left h, h2⟩

private theorem cSep_mem_Mfr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (l : Geo.Tor.Level H) : cSep l ∈ Mfr l := by
  unfold cSep
  split_ifs with h
  · exact h.choose_spec.1
  · exact zero_mem _

private theorem exists_mul_eq_M_mul_of_mem_Mb_Mfr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (l : Geo.Tor.Level H) {α β : 𝓞 E} (hα : α ∈ l.Mb) (hβ : β ∈ Mfr l) :
    ∃ γ : 𝓞 E, α * β = (l.M : 𝓞 E) * γ := by
  have h : α * β ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mul_mem_mul hα hβ
  rw [l.prod, Ideal.mem_span_singleton'] at h
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ, by rw [← hγ, mul_comm]⟩

private theorem dvd_EF_M_mul_smul_right {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (Dw : Datum H) (M : ℕ) (γ : 𝓞 E) (u y : Dw.La) : (M : ℤ) ∣ Dw.EF u (((M : 𝓞 E) * γ) • y) := by
  rw [mul_smul, ← Int.cast_natCast (R := 𝓞 E), Int.cast_smul_eq_zsmul, map_zsmul, smul_eq_mul]
  exact dvd_mul_right _ _

private theorem dvd_EF_cSep_of_mem_Mb_right {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} (l : Geo.Tor.Level H) (u : Dw.La) {x : Dw.La}
    (hx : x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) : (l.M : ℤ) ∣ Dw.EF u (cSep l • x) := by
  refine Submodule.smul_induction_on (p := fun x => (l.M : ℤ) ∣ Dw.EF u (cSep l • x)) hx ?_ ?_
  · intro α hα y _
    obtain ⟨γ, hγ⟩ := exists_mul_eq_M_mul_of_mem_Mb_Mfr l hα (cSep_mem_Mfr l)
    show (l.M : ℤ) ∣ Dw.EF u (cSep l • α • y)
    rw [smul_smul, mul_comm, hγ]
    exact dvd_EF_M_mul_smul_right Dw l.M γ u y
  · intro a b ha hb
    show (l.M : ℤ) ∣ Dw.EF u (cSep l • (a + b))
    rw [smul_add, map_add]
    exact dvd_add ha hb

private theorem dvd_EF_cSep_of_mem_Mfr_left {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} (l : Geo.Tor.Level H) {x : Dw.La} (hx : x ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La))
    (v : Dw.La) : (l.M : ℤ) ∣ Dw.EF x (cSep l • v) := by
  refine Submodule.smul_induction_on (p := fun x => (l.M : ℤ) ∣ Dw.EF x (cSep l • v)) hx ?_ ?_
  · intro μ hμ y _
    show (l.M : ℤ) ∣ Dw.EF (μ • y) (cSep l • v)
    obtain ⟨α, hα, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 hμ
    obtain ⟨γ, hγ⟩ := exists_mul_eq_M_mul_of_mem_Mb_Mfr l hα (cSep_mem_Mfr l)
    have hb : H.bar ((H.bar : 𝓞 E →+* 𝓞 E) α) = α := host_bar_bar' H α
    rw [Dw.adj, hb, smul_smul, hγ]
    exact dvd_EF_M_mul_smul_right Dw l.M γ y v
  · intro a b ha hb
    show (l.M : ℤ) ∣ Dw.EF (a + b) (cSep l • v)
    rw [map_add, LinearMap.add_apply]
    exact dvd_add ha hb

private theorem sim_f_sub_mem_Mb_of_inGam_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} (l l₂ : Geo.Tor.Level H) (s : Sim Dw) (hs : s.InGam l l₂) (hd : l.Dvd l₂) (a : Dw.La) :
    s.f l₂.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨k, hk⟩ := hd.1
  have hMpos : 0 < l.M := by have := l.three_le; omega
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · have := l₂.three_le
      rw [hk, h, mul_zero] at this
      omega
    · exact h
  obtain ⟨b, hb⟩ := s.tower l.M k hMpos hkpos a
  have e : s.f l₂.M a - a = (s.f (l.M * k) a - s.f l.M a) + (s.f l.M a - a) := by rw [hk]; abel
  rw [e, hb]
  refine Submodule.add_mem _ ?_ (hs.2.1 a)
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (levelM_mem_Mb_and_Mfr l).1 Submodule.mem_top

private theorem exists_EF_eq_one' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (Dw : Datum H) [Nontrivial Dw.La] : ∃ a b : Dw.La, Dw.EF a b = 1 := by
  have := Dw.fin
  have : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
  have : Module.IsTorsionFree ℤ Dw.La := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    apply Dw.unimod.1
    ext y
    have h' : Dw.EF (r • m) y = 0 := by rw [h]; simp
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h'
    rw [map_zero, LinearMap.zero_apply]
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact absurd h'' hr
    · exact h''
  let b := Module.Free.chooseBasis ℤ Dw.La
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨a, ha⟩ := Dw.unimod.2 (b.coord i)
  exact ⟨a, b i, by rw [ha]; simp⟩

private theorem dvd_EF_add_nsmul_sub {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (Dw : Datum H) (M : ℕ) (x y c c' : Dw.La) :
    (M : ℤ) ∣ Dw.EF (x + M • c) (y + M • c') - Dw.EF x y := by
  have e : Dw.EF (x + M • c) (y + M • c') - Dw.EF x y =
      Dw.EF x (M • c') + (Dw.EF (M • c) y + Dw.EF (M • c) (M • c')) := by
    simp only [map_add, LinearMap.add_apply]
    abel
  rw [e]
  refine dvd_add ?_ (dvd_add ?_ ?_)
  · rw [map_nsmul, nsmul_eq_mul]; exact dvd_mul_right _ _
  · rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]; exact dvd_mul_right _ _
  · rw [map_nsmul, nsmul_eq_mul]; exact dvd_mul_right _ _

private theorem exists_inv_sim_nu_mod {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (Dw : Datum H) [Nontrivial Dw.La] (s : Sim Dw) (M : ℕ) (hM : 0 < M) :
    ∃ ν' : ℤ, (M : ℤ) ∣ ν' * s.ν M - 1 := by
  obtain ⟨a, b, hab⟩ := exists_EF_eq_one' Dw
  obtain ⟨g, hg⟩ := s.inv M hM
  obtain ⟨c, hc⟩ := (hg a).2
  obtain ⟨c', hc'⟩ := (hg b).2
  have e1 : s.f M (g a) = a + M • c := by rw [← hc]; abel
  have e2 : s.f M (g b) = b + M • c' := by rw [← hc']; abel
  have hm := s.mult M hM (g a) (g b)
  have hs := dvd_EF_add_nsmul_sub Dw M a b c c'
  rw [e1, e2] at hm
  rw [hab] at hs
  refine ⟨Dw.EF (g a) (g b), ?_⟩
  have h3 := dvd_sub hs hm
  rw [sub_sub_sub_cancel_left, mul_comm] at h3
  exact h3

private theorem zetaM_pow_M {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l : Geo.Tor.Level H} (c : Coeff l) : (zetaM c) ^ l.M = 1 := by
  have hM : 0 < l.M := by have := l.three_le; omega
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero hM.ne' l.A_pos.ne'
  have hz : (⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ l.M' = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact (Complex.isPrimitiveRoot_exp l.M' hM').pow_eq_one
  have hd : l.M ∣ l.M' := Nat.dvd_lcm_left l.M l.A
  unfold zetaM
  rw [← pow_mul, Nat.div_mul_cancel hd]
  exact hz

private theorem zpow_eq_zpow_of_dvd_sub_of_pow_eq_one {K : Type} [Field K] (z : K) (M : ℕ) (hM : 0 < M) (hz : z ^ M = 1)
    {a b : ℤ} (h : (M : ℤ) ∣ a - b) : z ^ a = z ^ b := by
  obtain ⟨j, hj⟩ := h
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hz
    exact zero_ne_one hz
  have e : a = b + M * j := by omega
  rw [e, zpow_add₀ hz0, _root_.zpow_mul, zpow_natCast, hz, _root_.one_zpow, mul_one]

private theorem quotient_mk_qRep {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {K : Submodule (𝓞 E) Dw.La} (q : Dw.La ⧸ K) :
    (Submodule.Quotient.mk (qRep q) : Dw.La ⧸ K) = q :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

private theorem quotient_mk_levRep {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} (q : LevQ Dw l) :
    (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

open GlobalTheory.DatumInverseCharacter in

theorem datEq_of_phiHat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (φ : (Fin n → LevQc Dw d.l₂) → c.F) (w : (Fin n → LevQ Dw d.l₂) → c.F), (∀ q, d.eF (w q) = phiHat d.c₂ (fun x => d.eF (φ x)) q) → (∀ (kI : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (σq : LevQ Dw d.l₂ ≃ₗ[𝓞 E] LevQ Dw d.l₂) (σc : LevQc Dw d.l₂ ≃ₗ[𝓞 E] LevQc Dw d.l₂), (∀ a b : Dw.La, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk b → a - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ∧ kI (Submodule.Quotient.mk a) = Submodule.Quotient.mk b) → (∀ (x : LevQc Dw d.l₂) (q : LevQ Dw d.l₂), (d.l₂.M : ℤ) ∣ Dw.EF (qRep (σc x)) (cSep d.l₂ • levRep (σq q)) - Dw.EF (qRep x) (cSep d.l₂ • levRep q)) → ∀ x, φ (fun b => σc.symm (x b)) = (((ψ kI)⁻¹ : c.Fˣ) : c.F) * φ x) → DatEq d ψ w := by
  intro E _ _ _ H Dw l Xo c n d hLev ψ φ w hw hφ
  obtain ⟨hDvd, -, -, hMb2, -⟩ := hLev
  unfold DatEq
  intro s hs kI σq hkI hσq q
  have hM2pos : 0 < d.l₂.M := by have := d.l₂.three_le; omega

  let σL : LevQ Dw d.l₂ ≃ₗ[𝓞 E] LevQ Dw d.l₂ :=
    { σq with
      map_add' := by
        intro x y
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        show σq (Submodule.Quotient.mk a + Submodule.Quotient.mk b) =
          σq (Submodule.Quotient.mk a) + σq (Submodule.Quotient.mk b)
        rw [← Submodule.Quotient.mk_add, hσq, hσq, hσq, map_add, Submodule.Quotient.mk_add]
      map_smul' := by
        intro r x
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        show σq (r • Submodule.Quotient.mk a) = r • σq (Submodule.Quotient.mk a)
        rw [← Submodule.Quotient.mk_smul, hσq, hσq, map_smul, Submodule.Quotient.mk_smul] }
  have H1 : ∀ a b : Dw.La, σL (Submodule.Quotient.mk a) = Submodule.Quotient.mk b →
      a - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ∧
        kI (Submodule.Quotient.mk a) = Submodule.Quotient.mk b := by
    intro a b hab
    have hab' : s.f d.l₂.M a - b ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have h : σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk b := hab
      rw [hσq] at h
      exact (Submodule.Quotient.eq _).1 h
    have hle : d.l₂.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ≤ l.Mb • ⊤ := Submodule.smul_mono_left hDvd.2.1
    have hleI : d.l₂.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ≤ d.I • ⊤ := by
      rw [hMb2]; exact Submodule.smul_mono_left Ideal.mul_le_right
    refine ⟨?_, ?_⟩
    · have e : a - b = (s.f d.l₂.M a - b) - (s.f d.l₂.M a - a) := by abel
      rw [e]
      exact Submodule.sub_mem _ (hle hab') (sim_f_sub_mem_Mb_of_inGam_dvd l d.l₂ s hs hDvd a)
    · rw [← hkI]
      exact (Submodule.Quotient.eq _).2 (hleI hab')

  obtain ⟨σc, H2⟩ : ∃ σc : LevQc Dw d.l₂ ≃ₗ[𝓞 E] LevQc Dw d.l₂, ∀ (x : LevQc Dw d.l₂) (y : LevQ Dw d.l₂),
      (d.l₂.M : ℤ) ∣ Dw.EF (qRep (σc x)) (cSep d.l₂ • levRep (σL y)) -
        Dw.EF (qRep x) (cSep d.l₂ • levRep y) := by
    rcases subsingleton_or_nontrivial Dw.La with hsub | hnt
    · refine ⟨LinearEquiv.refl _ _, fun x y => ?_⟩
      have h0 : ∀ u v : Dw.La, Dw.EF u v = 0 := fun u v => by rw [Subsingleton.elim u 0]; simp
      rw [h0, h0, sub_zero]
      exact dvd_zero _
    · obtain ⟨ν', hν'⟩ := exists_inv_sim_nu_mod Dw s d.l₂.M hM2pos
      obtain ⟨k, hk⟩ := hν'
      obtain ⟨g, hg⟩ := s.inv d.l₂.M hM2pos
      have hMfr := (levelM_mem_Mb_and_Mfr d.l₂).2
      let t : Dw.La →ₗ[𝓞 E] Dw.La := ν' • s.f d.l₂.M
      let t' : Dw.La →ₗ[𝓞 E] Dw.La := s.ν d.l₂.M • g
      have hpres : ∀ u : Dw.La →ₗ[𝓞 E] Dw.La,
          Mfr d.l₂ • (⊤ : Submodule (𝓞 E) Dw.La) ≤ (Mfr d.l₂ • (⊤ : Submodule (𝓞 E) Dw.La)).comap u := by
        intro u
        rw [Submodule.smul_le]
        intro r hr m _
        rw [Submodule.mem_comap, map_smul]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      have hMsm : ∀ m : Dw.La, d.l₂.M • m ∈ Mfr d.l₂ • (⊤ : Submodule (𝓞 E) Dw.La) := by
        intro m
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
        exact Submodule.smul_mem_smul hMfr Submodule.mem_top
      have hMk : ∀ a : Dw.La, ((d.l₂.M : ℤ) * k) • a ∈ Mfr d.l₂ • (⊤ : Submodule (𝓞 E) Dw.La) := by
        intro a
        rw [mul_smul, natCast_zsmul]
        exact hMsm _
      have hinv1 : ∀ a, t (t' a) - a ∈ Mfr d.l₂ • (⊤ : Submodule (𝓞 E) Dw.La) := by
        intro a
        obtain ⟨c, hc⟩ := (hg a).2
        have e : t (t' a) - a =
            (ν' * s.ν d.l₂.M) • (s.f d.l₂.M (g a) - a) + (ν' * s.ν d.l₂.M - 1) • a := by
          simp only [t, t', LinearMap.smul_apply, map_zsmul, smul_smul, smul_sub, sub_smul, one_smul,
            mul_comm (s.ν d.l₂.M) ν']
          abel
        rw [e, hc, hk]
        exact Submodule.add_mem _ (Submodule.smul_of_tower_mem _ _ (hMsm c)) (hMk a)
      have hinv2 : ∀ a, t' (t a) - a ∈ Mfr d.l₂ • (⊤ : Submodule (𝓞 E) Dw.La) := by
        intro a
        obtain ⟨c, hc⟩ := (hg a).1
        have e : t' (t a) - a =
            (ν' * s.ν d.l₂.M) • (g (s.f d.l₂.M a) - a) + (ν' * s.ν d.l₂.M - 1) • a := by
          simp only [t, t', LinearMap.smul_apply, map_zsmul, smul_smul, smul_sub, sub_smul, one_smul]
          abel
        rw [e, hc, hk]
        exact Submodule.add_mem _ (Submodule.smul_of_tower_mem _ _ (hMsm c)) (hMk a)
      let σc : LevQc Dw d.l₂ ≃ₗ[𝓞 E] LevQc Dw d.l₂ :=
        LinearEquiv.ofLinear (Submodule.mapQ _ _ t (hpres t)) (Submodule.mapQ _ _ t' (hpres t'))
          (by
            refine LinearMap.ext fun x => ?_
            obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
            exact (Submodule.Quotient.eq _).2 (hinv1 a))
          (by
            refine LinearMap.ext fun x => ?_
            obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
            exact (Submodule.Quotient.eq _).2 (hinv2 a))
      have hσc : ∀ a : Dw.La, σc (Submodule.Quotient.mk a) = Submodule.Quotient.mk (t a) := fun a => rfl
      refine ⟨σc, fun x y => ?_⟩
      have hu : qRep (σc x) - t (qRep x) ∈ Mfr d.l₂ • (⊤ : Submodule (𝓞 E) Dw.La) := by
        rw [← Submodule.Quotient.eq, quotient_mk_qRep, ← hσc, quotient_mk_qRep]
      have hv : levRep (σL y) - s.f d.l₂.M (levRep y) ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
        rw [← Submodule.Quotient.eq, quotient_mk_levRep, ← hσq, quotient_mk_levRep]
        rfl
      have A1 := dvd_EF_cSep_of_mem_Mfr_left d.l₂ hu (levRep (σL y))
      have A2 := dvd_EF_cSep_of_mem_Mb_right d.l₂ (t (qRep x)) hv
      have A3 := s.mult d.l₂.M hM2pos (qRep x) (cSep d.l₂ • levRep y)
      have e1 : Dw.EF (t (qRep x)) (cSep d.l₂ • s.f d.l₂.M (levRep y)) =
          ν' * Dw.EF (s.f d.l₂.M (qRep x)) (s.f d.l₂.M (cSep d.l₂ • levRep y)) := by
        show Dw.EF (ν' • s.f d.l₂.M (qRep x)) (cSep d.l₂ • s.f d.l₂.M (levRep y)) = _
        rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul, map_smul (s.f d.l₂.M) (cSep d.l₂) (levRep y)]
      have key : Dw.EF (qRep (σc x)) (cSep d.l₂ • levRep (σL y)) - Dw.EF (qRep x) (cSep d.l₂ • levRep y) =
          Dw.EF (qRep (σc x) - t (qRep x)) (cSep d.l₂ • levRep (σL y)) +
          Dw.EF (t (qRep x)) (cSep d.l₂ • (levRep (σL y) - s.f d.l₂.M (levRep y))) +
          ν' * (Dw.EF (s.f d.l₂.M (qRep x)) (s.f d.l₂.M (cSep d.l₂ • levRep y)) -
            s.ν d.l₂.M * Dw.EF (qRep x) (cSep d.l₂ • levRep y)) +
          (ν' * s.ν d.l₂.M - 1) * Dw.EF (qRep x) (cSep d.l₂ • levRep y) := by
        simp only [map_sub, LinearMap.sub_apply, smul_sub]
        rw [e1]
        ring
      rw [key, hk, mul_assoc]
      exact dvd_add (dvd_add (dvd_add A1 A2) (dvd_mul_of_dvd_right A3 _)) (dvd_mul_right _ _)
  have hφ' := hφ kI σL σc H1 H2
  have hpair : ∀ y : Fin n → LevQc Dw d.l₂, (d.l₂.M : ℤ) ∣
      pairL (l := d.l₂) (fun b => qRep (y b)) (fun b => levRep (q b)) -
        pairL (l := d.l₂) (fun b => qRep (σc.symm (y b))) (fun b => levRep (σq.symm (q b))) := by
    intro y
    unfold pairL
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    have h := H2 (σc.symm (y b)) (σL.symm (q b))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact h
  have hζ := zetaM_pow_M d.c₂
  apply d.eF.injective
  rw [map_mul, hw, hw]
  simp only [phiHat]
  rw [mul_finsum]
  let e : (Fin n → LevQc Dw d.l₂) ≃ (Fin n → LevQc Dw d.l₂) :=
    ⟨fun y b => σc.symm (y b), fun y b => σc (y b), fun y => by simp, fun y => by simp⟩
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun y => ?_
  show d.eF (φ (fun b => σc.symm (y b))) *
      zetaM d.c₂ ^ pairL (l := d.l₂) (fun b => qRep (σc.symm (y b))) (fun b => levRep (σq.symm (q b))) = _
  rw [hφ' y, map_mul, zpow_eq_zpow_of_dvd_sub_of_pow_eq_one _ _ hM2pos hζ (dvd_sub_comm.mp (hpair y)), mul_assoc]

end GlobalTheory.ClsVal
