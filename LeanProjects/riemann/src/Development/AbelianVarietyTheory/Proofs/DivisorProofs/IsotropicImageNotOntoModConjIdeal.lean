import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveModOfSurjectiveModOpposite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModuliOfSignatureEq

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.CoisBar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem cois_dvd (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    (y : D.La →ₗ[𝓞 E] X) {n : ℕ} (hn : 0 < n) (hc : Cois D y n) {p : ℕ} (hpn : p ∣ n) (a : D.La)
    (ha : ∀ b, (∃ e, y b = p • e) → (p : ℤ) ∣ D.EF a b) : ∃ e, y a = p • e := by
  obtain ⟨k, rfl⟩ := hpn
  have hk : k ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨e, he⟩ := hc.2 (k • a) fun b ⟨e, he⟩ => by
    obtain ⟨c, hc'⟩ := ha b ⟨k • e, by rw [he, mul_smul]⟩
    exact ⟨c, by rw [map_nsmul, LinearMap.smul_apply, hc', nsmul_eq_mul]; push_cast; ring⟩
  refine ⟨e, ?_⟩
  have h2 : (k : ℤ) • (y a - p • e) = 0 := by
    rw [natCast_zsmul, smul_sub, ← map_nsmul, he, smul_smul, mul_comm k p, sub_self]
  rcases smul_eq_zero.1 h2 with h | h
  · exact absurd (by exact_mod_cast h) hk
  · exact sub_eq_zero.1 h

theorem exists_pair (D : Datum H) {p : ℕ} (hp : p.Prime) (S : AddSubgroup D.La) (hpS : ∀ x : D.La, p • x ∈ S)
    {c : D.La} (hc : c ∉ S) : ∃ a : D.La, (∀ b ∈ S, (p : ℤ) ∣ D.EF a b) ∧ ¬ (p : ℤ) ∣ D.EF a c := by
  haveI := Fact.mk hp
  letI : Module (ZMod p) (D.La ⧸ S) := AddCommGroup.zmodModule (fun x => by
    induction x using QuotientAddGroup.induction_on with
    | H x => rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]; exact hpS x)
  have hc' : (QuotientAddGroup.mk c : D.La ⧸ S) ≠ 0 := by rwa [Ne, QuotientAddGroup.eq_zero_iff]
  obtain ⟨f, hf⟩ : ∃ f : (D.La ⧸ S) →+ ZMod p, f (QuotientAddGroup.mk c) ≠ 0 := by
    by_contra hne
    push_neg at hne
    refine hc' ((Module.forall_dual_apply_eq_zero_iff (ZMod p) _).1 fun φ => ?_)
    exact hne (LinearMap.toAddMonoidHom φ)
  let g : D.La →+ ZMod p := f.comp (QuotientAddGroup.mk' S)
  haveI := datum_finite_int D
  haveI := datum_isTorsionFree_int D
  haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let bs := Module.Free.chooseBasis ℤ D.La
  let G : D.La →ₗ[ℤ] ℤ := bs.constr ℤ (fun i => ((g (bs i)).val : ℤ))
  have hG : ∀ x, ((G x : ℤ) : ZMod p) = g x := by
    have : (Int.castAddHom (ZMod p)).toIntLinearMap.comp G = g.toIntLinearMap := bs.ext fun i => by
      simp [G, Module.Basis.constr_basis]
    intro x
    exact LinearMap.congr_fun this x
  obtain ⟨a, ha⟩ := D.unimod.2 G
  refine ⟨a, fun b hb => ?_, fun hdvd => hf ?_⟩
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ha, hG]
    show f (QuotientAddGroup.mk b) = 0
    rw [(QuotientAddGroup.eq_zero_iff b).2 hb, map_zero]
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ha, hG] at hdvd
    exact hdvd

variable {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La}

theorem mem_nsmul_of_dvd (h : IsOpp D Z Z') {p : ℕ} (hp : 0 < p) {z : D.La} (hz : z ∈ Z)
    (hd : ∀ b ∈ Z', (p : ℤ) ∣ D.EF z b) : ∃ w ∈ Z, z = p • w := by
  choose c hc using fun b : Z' => hd b b.2
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  let φ : Z' →+ ℤ := AddMonoidHom.mk' c fun x x' =>
    mul_left_cancel₀ hp' (by rw [mul_add, ← hc, ← hc, ← hc, Submodule.coe_add, map_add])
  obtain ⟨w, hw, -⟩ := h.2.2.2 φ
  refine ⟨w, w.2, ?_⟩
  have : z - p • (w : D.La) = 0 := h.symm.eq_zero (sub_mem hz (Z.nsmul_mem w.2 p)) fun b hb => by
    have := hw ⟨b, hb⟩
    simp only [AddMonoidHom.mk'_apply, φ] at this
    rw [map_sub, LinearMap.sub_apply, map_nsmul, LinearMap.smul_apply, this, hc ⟨b, hb⟩, nsmul_eq_mul, sub_self]
  exact sub_eq_zero.1 this

end GlobalTheory.LowFilt.CoisBar

namespace GlobalTheory.LowFilt.CoisBar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem mem_nsmul_of_img_eq_top (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (y : D.La →ₗ[𝓞 E] X) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔮 : Ideal (𝓞 E)) (h𝔮 : 𝔮.IsMaximal)
    (htop : img D y Z' 𝔮 = ⊤) {p : ℕ} {b : D.La} (hb : b ∈ Z') (hyb : ∃ e, y b = p • e)
    (hq : ∀ t ∈ 𝔮, ∃ e ∈ Z', t • b = p • e) : ∃ e ∈ Z', b = p • e := by
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨r, hr1, hrX⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (I := 𝔮) (N := Z'.map y)
    (N' := ⊤) (P := ⊤) Module.Finite.fg_top le_rfl (le_of_eq htop.symm)
  have hr0 : r ∉ 𝔮 := fun h' => h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem h' hr1))
  have hrx : ∀ x : X, ∃ k ∈ Z', y k = r • x := fun x =>
    Submodule.mem_map.1 (hrX (Submodule.smul_mem_pointwise_smul x r ⊤ trivial))
  have hinj : ∀ k ∈ Z', y k = 0 → k = 0 := by
    obtain ⟨hZf', hZn'⟩ := sub_free_finite D Z'
    have hrank : Module.finrank ℤ Z' = Module.finrank ℤ X := by
      obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
      rw [h.finrank_int_eq, GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z,
        GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E X, hr]
    have hr00 : r ≠ 0 := fun h0 => hr0 (h0 ▸ 𝔮.zero_mem)
    set N := Ideal.absNorm (Ideal.span {r}) with hN
    have hN0 : N ≠ 0 := by
      rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hr00
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {r}))
    let g : Z' →ₗ[ℤ] X := (y.restrictScalars ℤ).comp (Z'.subtype.restrictScalars ℤ)
    have hmem : ∀ x : X, (N • LinearMap.id : X →ₗ[ℤ] X) x ∈ LinearMap.range g := fun x => by
      obtain ⟨k, hk, hyk⟩ := hrx (s • x)
      refine ⟨⟨k, hk⟩, ?_⟩
      show y k = N • x
      rw [hyk, smul_smul, mul_comm, hs, Nat.cast_smul_eq_nsmul]
    let m : X →ₗ[ℤ] LinearMap.range g := LinearMap.codRestrict _ (N • LinearMap.id) hmem
    have hm : Function.Injective m := fun x x' hxx => by
      have h1 : (N : ℤ) • (x - x') = 0 := by
        have : N • x = N • x' := congrArg Subtype.val hxx
        rw [natCast_zsmul, smul_sub, this, sub_self]
      rcases smul_eq_zero.1 h1 with h2 | h2
      · exact absurd (by exact_mod_cast h2) hN0
      · exact sub_eq_zero.1 h2
    have h1 := LinearMap.rank_le_of_injective m hm
    have h2 := LinearMap.rank_range_add_rank_ker g
    have h3 := rank_range_le g
    rw [← Module.finrank_eq_rank (R := ℤ) (M := X)] at h1
    rw [← Module.finrank_eq_rank (R := ℤ) (M := Z'), hrank] at h2 h3
    have h4 : Module.rank ℤ (LinearMap.range g) = Module.finrank ℤ X := le_antisymm h3 h1
    rw [h4] at h2
    have h5 : Module.rank ℤ (LinearMap.ker g) = 0 := by
      obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.1 (lt_of_le_of_lt (le_add_self.trans h2.le) (Cardinal.nat_lt_aleph0 _))
      rw [hk] at h2 ⊢
      norm_cast at h2 ⊢
      omega
    intro k hk hyk
    obtain ⟨a, ha0, hak⟩ := (rank_eq_zero_iff.1 h5) ⟨⟨k, hk⟩, hyk⟩
    have : a • (⟨k, hk⟩ : Z') = 0 := congrArg Subtype.val hak
    rcases smul_eq_zero.1 this with h' | h'
    · exact absurd h' ha0
    · exact congrArg Subtype.val h'
  obtain ⟨x, hx⟩ := hyb
  obtain ⟨b'', hb'', hyb''⟩ := hrx x
  have hrb : r • b = p • b'' := sub_eq_zero.1 (hinj _ (sub_mem (Z'.smul_mem r hb) (Z'.nsmul_mem hb'' p))
    (by rw [map_sub, map_smul, map_nsmul, hx, hyb'', smul_comm r p x, sub_self]))
  obtain ⟨c, u, hu, hcu⟩ := h𝔮.exists_inv hr0
  obtain ⟨e, he, hue⟩ := hq u hu
  refine ⟨c • b'' + e, add_mem (Z'.smul_mem c hb'') he, ?_⟩
  calc b = (c * r + u) • b := by rw [hcu, one_smul]
    _ = p • (c • b'' + e) := by rw [add_smul, mul_smul, hrb, hue, smul_add, smul_comm c p]

end GlobalTheory.LowFilt.CoisBar

namespace GlobalTheory.LowFilt.CoisBar

theorem img_bar_ne_top : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (hc : Cois D y n) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hn𝔭 : (n : 𝓞 E) ∈ 𝔭) (hi : img D y Z' 𝔭 ≠ ⊤) (hL : (perp D Z ⊓ perp D Z').map y ≤ img D y Z' 𝔭),
    img D y Z' (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)) ≠ ⊤ := by
  intro E _ _ _ H D X _ _ _ _ y n hn hc Z Z' h hr 𝔭 h𝔭 hn𝔭 hi hL htop
  obtain ⟨p, hp, hp𝔭, hpn⟩ : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 E) ∈ 𝔭 ∧ p ∣ n := by
    letI := Ideal.Quotient.field 𝔭
    obtain ⟨p, hch⟩ := CharP.exists (𝓞 E ⧸ 𝔭)
    have hn0 : Ideal.Quotient.mk 𝔭 (n : 𝓞 E) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hn𝔭
    rw [map_natCast] at hn0
    have hpn : p ∣ n := (CharP.cast_eq_zero_iff (𝓞 E ⧸ 𝔭) p n).1 hn0
    have hp : p.Prime := (CharP.char_is_prime_or_zero (𝓞 E ⧸ 𝔭) p).resolve_right (by
      rintro rfl
      rw [zero_dvd_iff] at hpn
      omega)
    refine ⟨p, hp, Ideal.Quotient.eq_zero_iff_mem.1 ?_, hpn⟩
    rw [map_natCast]
    exact CharP.cast_eq_zero _ p
  have hp0 := hp.pos
  have hsmA : ∀ t ∈ 𝔭, ∀ x : X, t • x ∈ img D y Z' 𝔭 := fun t ht x =>
    Submodule.mem_sup_right (Submodule.smul_mem_smul ht trivial)
  have hpA : ∀ x : X, p • x ∈ img D y Z' 𝔭 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact hsmA _ hp𝔭 x
  obtain ⟨c0, hc0⟩ : ∃ c, y c ∉ img D y Z' 𝔭 := by
    by_contra hne
    push_neg at hne
    apply hi
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, e, he⟩ := hc.1 x
    have : x = y a - n • e := by rw [he, add_sub_cancel_right]
    rw [this]
    refine sub_mem (hne a) ?_
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact hsmA _ hn𝔭 e
  obtain ⟨a, ha, hac⟩ := exists_pair D hp ((img D y Z' 𝔭).toAddSubgroup.comap y.toAddMonoidHom)
    (fun x => by
      show y (p • x) ∈ img D y Z' 𝔭
      rw [map_nsmul]
      exact hpA _) (c := c0) hc0
  replace ha : ∀ b, y b ∈ img D y Z' 𝔭 → (p : ℤ) ∣ D.EF a b := fun b hb => ha b hb
  have hya : ∃ e, y a = p • e := cois_dvd D y hn hc hpn a fun b ⟨e, he⟩ => ha b (by rw [he]; exact hpA e)
  have hbar : ∀ t ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E), H.bar t ∈ 𝔭 := fun t ht => by
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap] at ht
    have : H.bar.symm t = H.bar t := by
      apply H.bar.injective
      rw [RingEquiv.apply_symm_apply, bar_bar]
    rwa [← this]
  have hta : ∀ t ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E), ∃ e, t • a = p • e := fun t ht =>
    GlobalTheory.ModuliGenus.exists_eq_nsmul_of_dvd D hp0 _ fun c => by
      rw [D.adj]
      apply ha
      rw [map_smul]
      exact hsmA _ (hbar t ht) _
  obtain ⟨z, hz, m, hm, b', hb', rfl⟩ := h.exists_decomp a
  obtain ⟨w1, -, hw1⟩ := mem_nsmul_of_dvd h hp0 hz fun b hb => by
    have := ha b (Submodule.mem_sup_left (Submodule.mem_map_of_mem hb))
    rwa [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hm.2 b hb, h.2.1 hb' b hb, add_zero,
      add_zero] at this
  obtain ⟨w2, hw2⟩ := GlobalTheory.ModuliGenus.exists_eq_nsmul_of_dvd D hp0 m fun c => by
    obtain ⟨zc, hzc, mc, hmc, bc, hbc, rfl⟩ := h.exists_decomp c
    have h1 := ha mc (hL (Submodule.mem_map_of_mem hmc))
    have e1 : D.EF z mc = 0 := by rw [ef_swap, hmc.1 z hz, neg_zero]
    have e2 : D.EF b' mc = 0 := by rw [ef_swap, hmc.2 b' hb', neg_zero]
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, e1, e2, zero_add, add_zero] at h1
    rwa [map_add, map_add, hm.1 zc hzc, hm.2 bc hbc, zero_add, add_zero]
  have hzm : z + m = p • (w1 + w2) := by rw [hw1, hw2, smul_add]
  have hyb : ∃ e, y b' = p • e := by
    obtain ⟨e, he⟩ := hya
    refine ⟨e - y (w1 + w2), ?_⟩
    calc y b' = y (z + m + b') - y (z + m) := by rw [map_add y (z + m) b', add_sub_cancel_left]
      _ = p • (e - y (w1 + w2)) := by rw [he, hzm, map_nsmul, smul_sub]
  have hq : ∀ t ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E), ∃ e ∈ Z', t • b' = p • e := fun t ht => by
    obtain ⟨e, he⟩ := hta t ht
    have h1 : t • b' = p • (e - t • (w1 + w2)) := by
      calc t • b' = t • (z + m + b') - t • (z + m) := by rw [smul_add t (z + m) b', add_sub_cancel_left]
        _ = p • (e - t • (w1 + w2)) := by rw [he, hzm, smul_comm t p, smul_sub]
    refine ⟨_, (h.symm.isIsoSat).2 p _ hp.ne_zero ?_, h1⟩
    rw [← h1]
    exact Z'.smul_mem t hb'
  haveI := Ideal.map_isMaximal_of_equiv H.bar (p := 𝔭)
  obtain ⟨e, -, he⟩ := mem_nsmul_of_img_eq_top D y Z Z' h hr _ this htop hb' hyb hq
  apply hac
  rw [hzm, he, ← smul_add, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  exact dvd_mul_right _ _

end GlobalTheory.LowFilt.CoisBar
