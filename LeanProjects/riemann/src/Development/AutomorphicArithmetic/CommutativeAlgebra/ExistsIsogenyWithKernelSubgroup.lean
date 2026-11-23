import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiholomorphicLiftSystem
import Development.AutomorphicArithmetic.SpecialMaps.QuotObjDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSystemRealStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsTypeTjPIsogeny
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

attribute [local instance] ptModuleWvs

private theorem UpperTheory.exists_lagrangian_submodule_containing (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)) (c : ℕ)
    (hw : w.IsMaximal) (hu : uIdeal D r ≤ w) (hc' : ∃ e : ℕ, c = p ^ e) (M : Type) [AddCommGroup M]
    [Module (𝓞 D.F) M] [Finite M] (hM : ∀ x : M, c • x = 0) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (e : M → M → kˣ) (eadd1 : ∀ x x' y, e (x + x') y = e x y * e x' y)
    (eadd2 : ∀ x y y', e x (y + y') = e x y * e x y')
    (eadj : ∀ (a : 𝓞 D.F) x y, e (a • x) y = e x (D.bar a • y)) (eskew : ∀ x y, e x y * e y x = 1)
    (endeg : ∀ x, (∀ y, e x y = 1) → x = 0) (K : Submodule (𝓞 D.F) M) (hKw : ∀ x ∈ K, ∀ a ∈ w, a • x = 0) :
    ∃ H : Submodule (𝓞 D.F) M, (∀ x ∈ H, ∀ y ∈ H, e x y = 1) ∧ (∀ x, (∀ y ∈ H, e x y = 1) → x ∈ H) ∧ K ≤ H ∧
      ∀ x ∈ H, (∃ i : ℕ, ∀ a ∈ uIdeal D r ^ i, a • x = 0) → x ∈ K := by
  obtain ⟨E0, hc⟩ := hc'
  have e0r : ∀ x, e x 0 = 1 := fun x => by
    have h := eadd2 x 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  have einv : ∀ x y, e y x = (e x y)⁻¹ := fun x y => eq_inv_of_mul_eq_one_right (eskew x y)
  have hbb : ∀ a, D.bar (D.bar a) = a := fun a => by
    apply Subtype.ext
    have h1 := D.bar_eq (D.bar a)
    rw [D.bar_eq a] at h1
    exact h1.trans (by simp; rfl)
  set u := uIdeal D r with hu_def
  set v := Ideal.comap D.bar u with hv_def
  set E := E0 + 1 with hE
  obtain ⟨hcop, hprod⟩ := uIdeal_sup_comap_bar_and_mul_le p D r w hw.ne_top hu
  have hpE : ∀ x : M, ((p : 𝓞 D.F) ^ E) • x = 0 := by
    intro x
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hE, pow_succ', mul_smul, ← hc, hM x, smul_zero]
  have hprodE : ∀ a ∈ u ^ E, ∀ b ∈ v ^ E, ∀ x : M, (a * b) • x = 0 := by
    intro a ha b hb x
    have h1 : a * b ∈ (u * v) ^ E := by rw [mul_pow]; exact Ideal.mul_mem_mul ha hb
    have h2 := Ideal.pow_right_mono hprod E h1
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2
    obtain ⟨d, hd⟩ := h2
    rw [← hd, mul_smul, hpE, smul_zero]
  have hcopE : ∀ i, ∃ a ∈ u ^ i, ∃ b ∈ v ^ E, a + b = 1 := fun i =>
    Ideal.isCoprime_iff_exists.mp ((Ideal.isCoprime_iff_sup_eq.mpr hcop).pow)
  obtain ⟨ε', hε'u, ε, hεv, hsum⟩ := hcopE E
  have barv : ∀ a ∈ v ^ E, D.bar a ∈ u ^ E := fun a ha => Ideal.le_comap_pow _ E ha
  have baru : ∀ a ∈ u ^ E, D.bar a ∈ v ^ E := by
    intro a ha
    have h1 : Ideal.map D.bar u ≤ v := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      show D.bar (D.bar x) ∈ u
      rw [hbb]; exact hx
    have h2 : D.bar a ∈ Ideal.map D.bar (u ^ E) := Ideal.mem_map_of_mem _ ha
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 E h2
  have hsplit : ∀ x : M, ε • x + ε' • x = x := fun x => by rw [← add_smul, add_comm, hsum, one_smul]
  have hεε' : ∀ x : M, ε • ε' • x = 0 := fun x => by rw [← mul_smul, mul_comm]; exact hprodE _ hε'u _ hεv x
  have hε'ε : ∀ x : M, ε' • ε • x = 0 := fun x => by rw [← mul_smul]; exact hprodE _ hε'u _ hεv x
  have isoε : ∀ a b : M, e (ε • a) (ε • b) = 1 := fun a b => by
    rw [eadj, ← mul_smul]
    rw [hprodE _ (barv _ hεv) _ hεv b, e0r]
  have isoε' : ∀ a b : M, e (ε' • a) (ε' • b) = 1 := fun a b => by
    rw [eadj, ← mul_smul, mul_comm]
    rw [hprodE _ hε'u _ (baru _ hε'u) b, e0r]
  have hε'K : ∀ x ∈ K, ε' • x = 0 := fun x hx =>
    hKw x hx ε' (hu (Ideal.pow_le_self (by omega) hε'u))
  have hεK : ∀ x ∈ K, ε • x = x := fun x hx => by
    have := hsplit x
    rwa [hε'K x hx, add_zero] at this
  let K' : Submodule (𝓞 D.F) M :=
    { carrier := {y | ε • y = 0 ∧ ∀ x ∈ K, e x y = 1}
      add_mem' := fun {y y'} hy hy' => ⟨by rw [smul_add, hy.1, hy'.1, add_zero],
        fun x hx => by rw [eadd2, hy.2 x hx, hy'.2 x hx, _root_.mul_one]⟩
      zero_mem' := ⟨smul_zero _, fun x _ => e0r x⟩
      smul_mem' := fun a y hy => ⟨by rw [← mul_smul, mul_comm, mul_smul, hy.1, smul_zero],
        fun x hx => by
          have h := eadj (D.bar.symm a) x y
          rw [RingEquiv.apply_symm_apply] at h
          rw [← h]
          exact hy.2 _ (K.smul_mem _ hx)⟩ }
  have memK' : ∀ y, y ∈ K' ↔ ε • y = 0 ∧ ∀ x ∈ K, e x y = 1 := fun y => Iff.rfl
  have hK'ε' : ∀ y ∈ K', ε' • y = y := fun y hy => by
    have := hsplit y
    rwa [hy.1, zero_add] at this

  have hε'mem : ∀ y : M, (∀ x ∈ K, e y x = 1) → ε' • y ∈ K' := by
    intro y hy
    refine ⟨hεε' y, fun x hx => ?_⟩
    have h1 : e x y = 1 := by rw [einv, hy x hx, inv_one]
    have h2 := h1
    rw [← hsplit y, eadd2] at h2
    have h3 : e x (ε • y) = 1 := by rw [← hεK x hx]; exact isoε x y
    rwa [h3, _root_.one_mul] at h2
  have hinK : ∀ x ∈ K ⊔ K', (∃ i : ℕ, ∀ a ∈ u ^ i, a • x = 0) → x ∈ K := by
    rintro x hx ⟨i, hi⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have hz' : z = ε' • (y + z) := by rw [smul_add, hε'K y hy, zero_add, hK'ε' z hz]
    obtain ⟨a, ha, b, hb, hab⟩ := hcopE i
    have h1 : a • z = 0 := by
      rw [hz', ← mul_smul, mul_comm, mul_smul, hi a ha, smul_zero]
    have h2 : b • z = 0 := by
      rw [hz', ← mul_smul, mul_comm]
      exact hprodE _ hε'u _ hb _
    have h3 : z = 0 := by rw [← one_smul (𝓞 D.F) z, ← hab, add_smul, h1, h2, add_zero]
    rw [h3, add_zero]
    exact hy
  refine ⟨K ⊔ K', ?_, ?_, le_sup_left, hinK⟩
  · intro x hx y hy
    obtain ⟨k1, hk1, k1', hk1', rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨k2, hk2, k2', hk2', rfl⟩ := Submodule.mem_sup.1 hy
    have a1 : e k1 k2 = 1 := by rw [← hεK k1 hk1, ← hεK k2 hk2]; exact isoε _ _
    have a2 : e k1 k2' = 1 := hk2'.2 k1 hk1
    have a3 : e k1' k2 = 1 := by rw [einv, hk1'.2 k2 hk2, inv_one]
    have a4 : e k1' k2' = 1 := by rw [← hK'ε' k1' hk1', ← hK'ε' k2' hk2']; exact isoε' _ _
    rw [eadd1, eadd2, eadd2, a1, a2, a3, a4, _root_.mul_one, _root_.mul_one]
  · intro g hg
    have hg' : ε' • g ∈ K' := by
      refine hε'mem g fun x hx => hg x (Submodule.mem_sup_left hx)
    have hgK : ε • g ∈ K := by
      refine mem_addSubgroup_of_double_orthogonal M k e eadd1 eadd2 endeg K.toAddSubgroup (ε • g) fun y hy => ?_
      have hy' : ε' • y ∈ K' := hε'mem y hy
      have h1 : e g (ε' • y) = 1 := hg _ (Submodule.mem_sup_right hy')
      rw [← hsplit g, eadd1, isoε' g y, _root_.mul_one] at h1
      rw [← hsplit y, eadd1, isoε y g, _root_.one_mul, einv, h1, inv_one]
    rw [← hsplit g]
    exact Submodule.add_mem_sup hgK hg'

private theorem UpperTheory.exists_stable_maximal_isotropic_torsion_subgroup_ge {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (r : ℤ) (w : Ideal (𝓞 D.F)) (c : ℕ) (hw : w.IsMaximal) (hu : uIdeal D r ≤ w) (hc : ∃ e : ℕ, c = p ^ e)
    (hm : D.m = 1) {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {s : Sp k ⟶ Sp R} (o : Obj b N s)
    (H₀ : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A)) (stab₀ : ∀ a : D.O, ∀ h ∈ H₀, h ≫ o.act.act a ∈ H₀)
    (hk₀ : ∀ h ∈ H₀, KilledBy o w h) (hc₀ : ∀ h ∈ H₀, h ^ c = 1) :
    ∃ H : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A), (∀ c' : D.O, ∀ h ∈ H, h ≫ o.act.act c' ∈ H) ∧ (∀ h ∈ H, h ^ c = 1) ∧
      (∀ h₁ ∈ H, ∀ h₂ ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
        (lift h₁ 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h₂) 1) ∧
      (∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
        (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h) 1) → g ∈ H) ∧
      H₀ ≤ H ∧ (∀ h ∈ H, (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) h) → h ∈ H₀) := by
  obtain ⟨ex, hce⟩ := hc
  have hpk : ((p : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hck : (c : k) ≠ 0 := by rw [hce, Nat.cast_pow]; exact pow_ne_zero _ hpk
  obtain ⟨e, he, hl, hr, hadj, hskew, hnd⟩ : ∃ e : (𝟙_ (Over (Sp k)) ⟶ o.A) → (𝟙_ (Over (Sp k)) ⟶ o.A) → kˣ,
      (∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → ∀ u : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ,
        Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 g') u ↔
          u = unitOn (e g g')) ∧
      (∀ g₁ g₂ g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g₁ ^ c = 1 → g₂ ^ c = 1 → g' ^ c = 1 →
        e (g₁ * g₂) g' = e g₁ g' * e g₂ g') ∧
      (∀ g g₁ g₂ : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g₁ ^ c = 1 → g₂ ^ c = 1 →
        e g (g₁ * g₂) = e g g₁ * e g g₂) ∧
      (∀ (a : D.O) (g g' : 𝟙_ (Over (Sp k)) ⟶ o.A), g ^ c = 1 → g' ^ c = 1 →
        e (g ≫ o.act.act a) g' = e g (g' ≫ o.act.act (D.star a).unop)) ∧
      (∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → e g g' * e g' g = 1) ∧
      (∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → (∀ g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g' ^ c = 1 → e g g' = 1) → g = 1) :=
    PQuot.exists_pairing o c ⟨ex, hce⟩ k hpk (𝟙 _)
  have hinj : Function.Injective (unitOn (R := k)) := by
    refine Units.map_injective (f := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) ?_
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.injective
  have hone : unitOn (1 : kˣ) = 1 := map_one (Units.map _)
  have he1 : ∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 →
      (Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 g') 1 ↔
        e g g' = 1) := fun g g' hg hg' => by
    rw [he g g' hg hg']
    exact ⟨fun h => (hinj (hone.trans h)).symm, fun h => by rw [h]; exact hone.symm⟩
  let M := TjExists.torsSub o (𝟙_ (Over (Sp k))) c
  haveI : Finite M := (GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed k o.A o.ab c hck).1
  have hM0 : ∀ x : M, x = 0 ↔ x.1.toMul = 1 := fun x => ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  have hkill : ∀ (v : Ideal (𝓞 D.F)) (x : M), (∀ a ∈ v, a • x = 0) ↔ KilledBy o v x.1.toMul :=
    fun v x => forall₂_congr fun a _ => hM0 (a • x)
  let K₀ : Submodule (𝓞 D.F) M :=
    { carrier := {x | x.1.toMul ∈ H₀}
      add_mem' := fun {x y} hx hy => H₀.mul_mem hx hy
      zero_mem' := H₀.one_mem
      smul_mem' := fun a x hx => stab₀ (algebraMap (𝓞 D.F) D.O a) _ hx }
  obtain ⟨K, Kiso, Kmax, K₀K, KK₀⟩ := UpperTheory.exists_lagrangian_submodule_containing p D r w c hw hu ⟨ex, hce⟩ M
    (fun x => (hM0 _).2 x.2) k (fun x y => e x.1.toMul y.1.toMul)
    (fun x x' y => hl _ _ _ x.2 x'.2 y.2) (fun x y y' => hr _ _ _ x.2 y.2 y'.2)
    (fun a x y => by
      have := hadj (algebraMap (𝓞 D.F) D.O a) _ _ x.2 y.2
      rw [D.star_F, MulOpposite.unop_op] at this
      exact this)
    (fun x y => hskew _ _ x.2 y.2)
    (fun x h => (hM0 x).2 (hnd _ x.2 fun g' hg' => h ⟨Additive.ofMul g', hg'⟩)) K₀
    (fun x hx => (hkill w x).2 (hk₀ _ hx))
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A) :=
    { carrier := {g | ∃ x ∈ K, x.1.toMul = g}
      one_mem' := ⟨0, K.zero_mem, rfl⟩
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, K.add_mem hx hy, rfl⟩
      inv_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨-x, K.neg_mem hx, rfl⟩ }
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro c' _ ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := GlobalTheory.UPel.HT.Datum.algebraMap_surjective_of_m_eq_one p D hm c'
    exact ⟨a • x, K.smul_mem a hx, rfl⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (he1 _ _ x.2 y.2).2 (Kiso x hx y hy)
  · intro g hg h
    exact ⟨⟨Additive.ofMul g, hg⟩, Kmax _ fun y hy => (he1 _ _ hg y.2).1 (h _ ⟨y, hy, rfl⟩), rfl⟩
  · intro h hh
    exact ⟨⟨Additive.ofMul h, hc₀ h hh⟩, K₀K hh, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ ⟨i, hi⟩
    exact KK₀ x hx ⟨i, (hkill _ x).2 hi⟩

theorem UpperTheory.exists_isogeny_with_kernel_subgroup :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (k : Type) [Field k] [IsAlgClosed k] (σ : Sp k ⟶ Sp R) (o : Obj b N σ) (H₀ : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A)), (∀ a : D.O, ∀ h ∈ H₀, h ≫ o.act.act a ∈ H₀) → (∀ h ∈ H₀, KilledBy o w h) → Nat.card H₀ = Ideal.absNorm w ^ j → ∃ (o' : Obj b N σ) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ IsTj r w j o o' ψ ∧ ∀ h : 𝟙_ (Over (Sp k)) ⟶ o.A, (h ≫ ψ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) h) ↔ h ∈ H₀ := by
  intro p _ D R _ _ b N _ _ hp hm r w j c hw hu hc k _ _ s o H₀ stab₀ hk₀ hcard₀
  haveI := TjExists.charZero_of_base b hp s
  obtain ⟨ex, hce, hje⟩ := hc
  have hc₀ : ∀ h ∈ H₀, h ^ c = 1 := by
    intro h hh
    rcases Nat.eq_zero_or_pos ex with rfl | hex
    · have hj0 : j = 0 := by
        by_contra hj
        exact lt_irrefl 0 (hje (Nat.pos_of_ne_zero hj))
      rw [hj0, pow_zero] at hcard₀
      have hb : H₀ = ⊥ := Subgroup.eq_bot_of_card_eq H₀ hcard₀
      rw [hb, Subgroup.mem_bot] at hh
      rw [hh, one_pow]
    · have h1 := hk₀ h hh _ (hu (p_mem_uIdeal D r))
      rw [map_natCast, TjExists.comp_act_natCast] at h1
      obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hex.ne'
      rw [hce, pow_succ', pow_mul, h1, one_pow]
  obtain ⟨H, stab, hpow, hiso, hmax, hH₀, hHU⟩ := UpperTheory.exists_stable_maximal_isotropic_torsion_subgroup_ge r w c hw hu ⟨ex, hce⟩ hm o H₀ stab₀ hk₀ hc₀
  have hck : (c : k) ≠ 0 := by
    rw [hce, Nat.cast_pow]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hfin : Finite H := by
    haveI := (GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed k o.A o.ab c hck).1
    exact Finite.of_injective (fun h : H => (⟨h.1, hpow h.1 h.2⟩ : {g : 𝟙_ (Over (Sp k)) ⟶ o.A // g ^ c = 1}))
      fun a a' h => Subtype.ext (Subtype.mk.inj h)
  have hinj : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ Sp k) (h h' : 𝟙_ (Over (Sp k)) ⟶ o.A),
      toUnit (Over.mk x) ≫ h = toUnit (Over.mk x) ≫ h' → h = h' := fun κ _ x h h' e => by
    haveI : Nonempty (Over.mk x).left := inferInstanceAs (Nonempty (PrimeSpectrum κ))
    haveI := GlobalTheory.PointQuot.epi_toUnit (Over.mk x)
    exact (cancel_epi _).1 e
  have hfree : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ Sp k) (h : 𝟙_ (Over (Sp k)) ⟶ o.A),
      toUnit (Over.mk x) ≫ h = 1 ↔ h = 1 := fun κ _ x h =>
    ⟨fun e => hinj κ x h 1 (by rw [e, MonObj.comp_one]), fun e => by rw [e, MonObj.comp_one]⟩
  obtain ⟨o', ψ, hψ, hker⟩ := PQuot.exists_quot o c ⟨ex, hce⟩ hp H hfin (fun κ _ _ x h _ e => (hfree κ x h).1 e)
    stab hpow hiso (fun κ _ _ x g hg ho => PQuot.max_geom o c hck H hpow hmax κ x g hg ho)
  have hkb : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ Sp k) (v : Ideal (𝓞 D.F)) (h : 𝟙_ (Over (Sp k)) ⟶ o.A),
      KilledBy o v (toUnit (Over.mk x) ≫ h) ↔ KilledBy o v h := fun κ _ x v h =>
    forall₂_congr fun a _ => by rw [Category.assoc, hfree]
  have hkw : ∀ h : 𝟙_ (Over (Sp k)) ⟶ o.A, h ∈ H ∧ KilledBy o w h ↔ h ∈ H₀ := fun h =>
    ⟨fun ⟨h1, h2⟩ => hHU h h1 ⟨1, fun a ha => h2 a (hu (by rwa [pow_one] at ha))⟩, fun h1 => ⟨hH₀ h1, hk₀ h h1⟩⟩
  have hcard : Nat.card {h : 𝟙_ (Over (Sp k)) ⟶ o.A // h ∈ H ∧ KilledBy o w h} = Ideal.absNorm w ^ j := by
    rw [← hcard₀]
    exact Nat.card_congr (Equiv.subtypeEquivRight hkw)
  refine ⟨o', ψ, hψ, fun κ _ _ _ x => ?_, fun h => ?_⟩
  · refine ⟨fun g hg ⟨i, hi⟩ => ?_, ?_⟩
    · obtain ⟨h, hh, rfl⟩ := (hker κ x g).1 hg
      exact (hkb κ x w h).2 (hk₀ h (hHU h hh ⟨i, (hkb κ x _ h).1 hi⟩))
    · rw [hm, Nat.one_mul, ← hcard]
      refine (Nat.card_eq_of_bijective (fun h : {h : 𝟙_ (Over (Sp k)) ⟶ o.A // h ∈ H ∧ KilledBy o w h} =>
        (⟨toUnit (Over.mk x) ≫ h.1, (hker κ x _).2 ⟨h.1, h.2.1, rfl⟩, (hkb κ x w _).2 h.2.2⟩ :
          {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g})) ⟨fun a a' h => ?_, ?_⟩).symm
      · exact Subtype.ext (hinj κ x _ _ (congrArg Subtype.val h))
      · rintro ⟨g, hg, hk⟩
        obtain ⟨h, hh, rfl⟩ := (hker κ x g).1 hg
        exact ⟨⟨h, hh, (hkb κ x w h).1 hk⟩, rfl⟩
  · have hid : toUnit (Over.mk (𝟙 (Sp k))) = 𝟙 (𝟙_ (Over (Sp k))) := toUnit_unique _ _
    have hk' : h ≫ ψ = 1 ↔ h ∈ H := by
      have h1 := hker k (𝟙 _) h
      constructor
      · intro e
        obtain ⟨h', hh', e'⟩ := h1.1 e
        have e2 : h = h' := by
          refine e'.trans ?_
          erw [hid]
          exact Category.id_comp _
        exact e2 ▸ hh'
      · intro hh
        refine h1.2 ⟨h, hh, ?_⟩
        erw [hid]
        exact (Category.id_comp _).symm
    rw [hk']
    exact ⟨fun ⟨a, b⟩ => hHU h a b, fun a => ⟨hH₀ a, 1, fun x hx => hk₀ h a x (hu (by rwa [pow_one] at hx))⟩⟩
