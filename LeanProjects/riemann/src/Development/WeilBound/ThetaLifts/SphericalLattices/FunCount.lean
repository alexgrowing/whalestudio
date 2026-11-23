import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs

noncomputable section

namespace PositivityTheory.Sph

section Count

variable {G : Type} [Group G]

theorem mem_map_conj {H : Subgroup G} {y z : G} : z ∈ H.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * z * y ∈ H := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show y⁻¹ * (y * b * y⁻¹) * y = b by group]
  · intro hz
    refine ⟨_, hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem mk_mul_mem {H : Subgroup G} (x : G) {b : G} (hb : b ∈ H) : ((x * b : G) : G ⧸ H) = (x : G ⧸ H) :=
  QuotientGroup.eq.2 (by rw [mul_inv_rev, inv_mul_cancel_right]; exact H.inv_mem hb)

def orb (H : Subgroup G) (y : G) : Set (G ⧸ H) := {c | ∃ a ∈ H, c = ((a * y : G) : G ⧸ H)}

theorem ncard_orb (H : Subgroup G) (y : G) : (orb H y).ncard = (H.map (MulAut.conj y).toMonoidHom).relIndex H := by
  classical
  set M := H.map (MulAut.conj y).toMonoidHom with hM
  let Φ : H ⧸ M.subgroupOf H → G ⧸ H := fun q => ((((Quotient.out q : H) : G) * y : G) : G ⧸ H)
  have hinj : Function.Injective Φ := fun q q' e => by
    have e' := QuotientGroup.eq.1 e
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mem_map_conj]
    convert e' using 1
    group
  have hrange : Set.range Φ = orb H y := by
    ext c
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨_, (Quotient.out q).2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨((⟨a, ha⟩ : H) : H ⧸ M.subgroupOf H), ?_⟩
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (M.subgroupOf H) (⟨a, ha⟩ : H)
      have hm' : ((m : H) : G) ∈ M := Subgroup.mem_subgroupOf.1 m.2
      rw [mem_map_conj] at hm'
      change ((((Quotient.out ((⟨a, ha⟩ : H) : H ⧸ M.subgroupOf H) : H) : G) * y : G) : G ⧸ H) = _
      rw [hm, Subgroup.coe_mul, show a * ((m : H) : G) * y = a * y * (y⁻¹ * ((m : H) : G) * y) by group]
      exact mk_mul_mem _ hm'
  rw [← hrange, Set.ncard_range_of_injective hinj, Subgroup.relIndex, Subgroup.index_eq_card]

theorem orb_mul {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H) (y : G) : orb H (a * y * b) = orb H y := by
  ext c
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x * a, H.mul_mem hx ha, ?_⟩
    rw [show x * (a * y * b) = x * a * y * b by group]
    exact mk_mul_mem _ hb
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x * a⁻¹, H.mul_mem hx (H.inv_mem ha), ?_⟩
    rw [show x * a⁻¹ * (a * y * b) = x * y * b by group]
    exact (mk_mul_mem _ hb).symm

theorem orb_symm (H : Subgroup G) {d e : G ⧸ H} (h : e ∈ orb H (Quotient.out d)⁻¹) : d ∈ orb H (Quotient.out e)⁻¹ := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul H (a * (Quotient.out d)⁻¹)
  refine ⟨m, m.2, ?_⟩
  rw [hm, show (m : G) * (a * (Quotient.out d)⁻¹ * m)⁻¹ = Quotient.out d * a⁻¹ by group, mk_mul_mem _ (H.inv_mem ha),
    QuotientGroup.out_eq']

def dblK (K : Subgroup G) (x : G) : Set G := {y | ∃ a ∈ K, ∃ b ∈ K, y = a * x * b}

def cosT (P K : Subgroup G) (x : G) : Set (G ⧸ (P ⊓ K)) := {d | ∃ p ∈ P, p ∈ dblK K x ∧ d = (p : G ⧸ (P ⊓ K))}

theorem out_cosT {P K : Subgroup G} {x : G} {d : G ⧸ (P ⊓ K)} (hd : d ∈ cosT P K x) :
    Quotient.out d ∈ P ∧ Quotient.out d ∈ dblK K x := by
  obtain ⟨p, hp, ⟨a, ha, b, hb, rfl⟩, rfl⟩ := hd
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (P ⊓ K) (a * x * b)
  rw [hm]
  exact ⟨P.mul_mem hp m.2.1, a, ha, b * m, K.mul_mem hb m.2.2, by group⟩

theorem orb_sub_cosT {P K : Subgroup G} {x : G} {d : G ⧸ (P ⊓ K)} (hd : d ∈ cosT P K x) :
    orb (P ⊓ K) (Quotient.out d)⁻¹ ⊆ cosT P K x⁻¹ := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨h1, b, hb, c, hc, e⟩ := out_cosT hd
  refine ⟨_, P.mul_mem ha.1 (P.inv_mem h1), ⟨a * c⁻¹, K.mul_mem ha.2 (K.inv_mem hc), b⁻¹, K.inv_mem hb, ?_⟩, rfl⟩
  rw [e]
  group

theorem count_core {U P K : Subgroup G} (hPU : P ≤ U) {f f' : G → ℂ} (f1 : f 1 = 1) (f1' : f' 1 = 1)
    (hf : ∀ p ∈ P, ∀ g ∈ U, ∀ k ∈ K, f (p * g * k) = f p * f g)
    (hf' : ∀ p ∈ P, ∀ g ∈ U, ∀ k ∈ K, f' (p * g * k) = f' p * f' g)
    (hmod : ∀ p ∈ P, f p * f' p * (((P ⊓ K).map (MulAut.conj p).toMonoidHom).relIndex (P ⊓ K) : ℂ) =
      (((P ⊓ K).map (MulAut.conj p⁻¹).toMonoidHom).relIndex (P ⊓ K) : ℂ))
    {A B : Set (G ⧸ (P ⊓ K))} (hA : A.Finite) (hB : B.Finite)
    (hBP : ∀ e ∈ B, Quotient.out e ∈ P)
    (hAB : ∀ d ∈ A, orb (P ⊓ K) (Quotient.out d)⁻¹ ⊆ B) (hBA : ∀ e ∈ B, orb (P ⊓ K) (Quotient.out e)⁻¹ ⊆ A) :
    ∑ᶠ d ∈ A, f' (Quotient.out d) = ∑ᶠ e ∈ B, f (Quotient.out e) := by
  classical
  have bi' : ∀ a ∈ P ⊓ K, ∀ g ∈ U, ∀ b ∈ P ⊓ K, f' (a * g * b) = f' g := fun a ha g hg b hb => by
    rw [hf' a ha.1 g hg b hb.2]
    have : f' a = 1 := by simpa [f1'] using hf' 1 P.one_mem 1 U.one_mem a ha.2
    rw [this, one_mul]
  have finv : ∀ p ∈ P, f p * f p⁻¹ = 1 := fun p hp => by
    have := hf p hp p⁻¹ (hPU (P.inv_mem hp)) 1 K.one_mem
    rwa [mul_one, mul_inv_cancel, f1, eq_comm] at this
  have hN : ∀ y : G, (orb (P ⊓ K) y).Finite → ((orb (P ⊓ K) y).ncard : ℂ) ≠ 0 := fun y hy =>
    Nat.cast_ne_zero.2 ((Set.ncard_pos hy).2 ⟨_, 1, (P ⊓ K).one_mem, rfl⟩).ne'
  have finA : ∀ d ∈ A, (orb (P ⊓ K) (Quotient.out d)⁻¹).Finite := fun d hd => hB.subset (hAB d hd)
  have finB : ∀ e ∈ B, (orb (P ⊓ K) (Quotient.out e)).Finite := fun e he => by
    have hd : (((Quotient.out e)⁻¹ : G) : G ⧸ (P ⊓ K)) ∈ A := hBA e he ⟨1, (P ⊓ K).one_mem, by rw [one_mul]⟩
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (P ⊓ K) (Quotient.out e)⁻¹
    have h2 := finA _ hd
    rwa [hm, mul_inv_rev, inv_inv, show ((m : G))⁻¹ * Quotient.out e = ((m : G))⁻¹ * Quotient.out e * 1 by rw [mul_one],
      orb_mul ((P ⊓ K).inv_mem m.2) (P ⊓ K).one_mem] at h2
  let w : G ⧸ (P ⊓ K) → ℂ := fun d => f' (Quotient.out d) / ((orb (P ⊓ K) (Quotient.out d)⁻¹).ncard : ℂ)
  have s1 : ∀ d ∈ A, f' (Quotient.out d) =
      ∑ e ∈ hB.toFinset, if e ∈ orb (P ⊓ K) (Quotient.out d)⁻¹ then w d else 0 := fun d hd => by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have e : ((hB.toFinset.filter (· ∈ orb (P ⊓ K) (Quotient.out d)⁻¹) : Finset (G ⧸ (P ⊓ K))) : Set (G ⧸ (P ⊓ K))) =
        orb (P ⊓ K) (Quotient.out d)⁻¹ := by
      ext c
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨hAB d hd h, h⟩⟩
    rw [← Set.ncard_coe_finset, e]
    simp only [w]
    field_simp [hN _ (finA d hd)]
  have s2 : ∀ e ∈ B, (∑ d ∈ hA.toFinset, if e ∈ orb (P ⊓ K) (Quotient.out d)⁻¹ then w d else 0) = f (Quotient.out e) :=
    fun e he => by
    have hr : (Quotient.out e)⁻¹ ∈ P := P.inv_mem (hBP e he)
    have hcond : ∀ d ∈ hA.toFinset, (if e ∈ orb (P ⊓ K) (Quotient.out d)⁻¹ then w d else 0) =
        if d ∈ orb (P ⊓ K) (Quotient.out e)⁻¹ then f' (Quotient.out e)⁻¹ / ((orb (P ⊓ K) (Quotient.out e)).ncard : ℂ) else 0 :=
      fun d _ => by
      by_cases h1 : e ∈ orb (P ⊓ K) (Quotient.out d)⁻¹
      · have h2 := orb_symm (P ⊓ K) h1
        rw [if_pos h1, if_pos h2]
        obtain ⟨a, ha, hd'⟩ := h2
        obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (P ⊓ K) (a * (Quotient.out e)⁻¹)
        have hod : Quotient.out d = a * (Quotient.out e)⁻¹ * m := by rw [hd', hm]
        simp only [w]
        rw [hod, bi' a ha _ (hPU hr) m m.2, mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc,
          orb_mul ((P ⊓ K).inv_mem m.2) ((P ⊓ K).inv_mem ha)]
      · rw [if_neg h1, if_neg (fun h2 => h1 (orb_symm (P ⊓ K) h2))]
    rw [Finset.sum_congr rfl hcond, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have e1 : ((hA.toFinset.filter (· ∈ orb (P ⊓ K) (Quotient.out e)⁻¹) : Finset (G ⧸ (P ⊓ K))) : Set (G ⧸ (P ⊓ K))) =
        orb (P ⊓ K) (Quotient.out e)⁻¹ := by
      ext c
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨hBA e he h, h⟩⟩
    rw [← Set.ncard_coe_finset, e1, ncard_orb, ncard_orb]
    have hm := hmod _ hr
    rw [inv_inv] at hm
    have hn2 : ((((P ⊓ K).map (MulAut.conj (Quotient.out e)).toMonoidHom).relIndex (P ⊓ K) : ℕ) : ℂ) ≠ 0 := by
      rw [← ncard_orb]; exact hN _ (finB e he)
    have hfr := finv _ hr
    rw [inv_inv] at hfr
    rw [eq_comm, ← mul_div_assoc, eq_div_iff hn2, ← hm]
    linear_combination ((((((P ⊓ K).map (MulAut.conj (Quotient.out e)⁻¹).toMonoidHom).relIndex (P ⊓ K) : ℕ) : ℂ)) *
      f' (Quotient.out e)⁻¹) * hfr
  rw [finsum_mem_eq_finite_toFinset_sum _ hA, finsum_mem_eq_finite_toFinset_sum _ hB]
  calc ∑ d ∈ hA.toFinset, f' (Quotient.out d)
      = ∑ d ∈ hA.toFinset, ∑ e ∈ hB.toFinset, (if e ∈ orb (P ⊓ K) (Quotient.out d)⁻¹ then w d else 0) :=
        Finset.sum_congr rfl fun d hd => s1 d (hA.mem_toFinset.1 hd)
    _ = ∑ e ∈ hB.toFinset, ∑ d ∈ hA.toFinset, (if e ∈ orb (P ⊓ K) (Quotient.out d)⁻¹ then w d else 0) := Finset.sum_comm
    _ = ∑ e ∈ hB.toFinset, f (Quotient.out e) := Finset.sum_congr rfl fun e he => s2 e (hB.mem_toFinset.1 he)

theorem sum_eq_cosT {U K P : Subgroup G} (hKU : K ≤ U) (hPU : P ≤ U) (hIw : ∀ g ∈ U, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
    {h : G} (hh : h ∈ U) (hfin : (conjInf K h).relIndex K ≠ 0) {φ : G → ℂ} (hr : ∀ g ∈ U, ∀ k ∈ K, φ (g * k) = φ g) :
    (cosT P K h).Finite ∧
      ∑ᶠ q : K ⧸ (conjInf K h).subgroupOf K, φ (((Quotient.out q : K) : G) * h) = ∑ᶠ d ∈ cosT P K h, φ (Quotient.out d) := by
  classical
  have hKPK : P ⊓ K ≤ K := inf_le_right
  let μ : K ⧸ (conjInf K h).subgroupOf K → G ⧸ K := fun q => ((((Quotient.out q : K) : G) * h : G) : G ⧸ K)
  let ι : G ⧸ (P ⊓ K) → G ⧸ K := Subgroup.quotientMapOfLE hKPK
  have hι : ∀ x : G, ι (x : G ⧸ (P ⊓ K)) = (x : G ⧸ K) := fun x => Subgroup.quotientMapOfLE_apply_mk hKPK x
  have hμ : Function.Injective μ := fun q q' e => by
    have e' := QuotientGroup.eq.1 e
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ⟨((Quotient.out q)⁻¹ * Quotient.out q').2, mem_map_conj.2 ?_⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    convert e' using 1
    group
  have hrange : Set.range μ = ι '' cosT P K h := by
    ext c
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨p, hp, k, hk, e⟩ := hIw _ (U.mul_mem (hKU (Quotient.out q).2) hh)
      refine ⟨(p : G ⧸ (P ⊓ K)), ⟨p, hp, ⟨_, (Quotient.out q).2, k⁻¹, K.inv_mem hk, by rw [e, mul_inv_cancel_right]⟩, rfl⟩, ?_⟩
      rw [hι]
      change _ = ((((Quotient.out q : K) : G) * h : G) : G ⧸ K)
      rw [e, mk_mul_mem _ hk]
    · rintro ⟨_, ⟨p, hp, ⟨a, ha, b, hb, rfl⟩, rfl⟩, rfl⟩
      refine ⟨((⟨a, ha⟩ : K) : K ⧸ (conjInf K h).subgroupOf K), ?_⟩
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul ((conjInf K h).subgroupOf K) (⟨a, ha⟩ : K)
      have hm' : ((m : K) : G) ∈ K.map (MulAut.conj h).toMonoidHom := (Subgroup.mem_subgroupOf.1 m.2).2
      rw [mem_map_conj] at hm'
      have key : ((Quotient.out ((⟨a, ha⟩ : K) : K ⧸ (conjInf K h).subgroupOf K) : K) : G) = a * ((m : K) : G) := by
        rw [hm]; rfl
      rw [hι]
      change ((((Quotient.out ((⟨a, ha⟩ : K) : K ⧸ (conjInf K h).subgroupOf K) : K) : G) * h : G) : G ⧸ K) = _
      rw [key, show a * ((m : K) : G) * h = a * h * (h⁻¹ * ((m : K) : G) * h) by group, mk_mul_mem _ hm', mk_mul_mem _ hb]
  have hinj : Set.InjOn ι (cosT P K h) := by
    rintro _ ⟨p, hp, -, rfl⟩ _ ⟨p', hp', -, rfl⟩ e
    rw [hι, hι] at e
    exact QuotientGroup.eq.2 ⟨P.mul_mem (P.inv_mem hp) hp', QuotientGroup.eq.1 e⟩
  have hfinT : (cosT P K h).Finite := by
    have : Finite (K ⧸ (conjInf K h).subgroupOf K) := Subgroup.index_ne_zero_iff_finite.1 hfin
    exact Set.Finite.of_finite_image (hrange ▸ Set.finite_range μ) hinj
  refine ⟨hfinT, ?_⟩
  have e1 : ∀ q, φ (((Quotient.out q : K) : G) * h) = φ (Quotient.out (μ q)) := fun q => by
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul K (((Quotient.out q : K) : G) * h)
    change _ = φ (Quotient.out ((((Quotient.out q : K) : G) * h : G) : G ⧸ K))
    rw [hm, hr _ (U.mul_mem (hKU (Quotient.out q).2) hh) _ m.2]
  have e2 : ∀ d ∈ cosT P K h, φ (Quotient.out (ι d)) = φ (Quotient.out d) := fun d hd => by
    have hιd : ι d = ((Quotient.out d : G) : G ⧸ K) := by
      rw [← hι]
      congr 1
      exact (QuotientGroup.out_eq' d).symm
    rw [hιd]
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul K (Quotient.out d)
    rw [hm, hr _ (hPU (out_cosT hd).1) _ m.2]
  calc ∑ᶠ q, φ (((Quotient.out q : K) : G) * h) = ∑ᶠ q, φ (Quotient.out (μ q)) := finsum_congr e1
    _ = ∑ᶠ c ∈ Set.range μ, φ (Quotient.out c) := (finsum_mem_range hμ (f := fun c => φ (Quotient.out c))).symm
    _ = ∑ᶠ c ∈ ι '' cosT P K h, φ (Quotient.out c) := by rw [hrange]
    _ = ∑ᶠ d ∈ cosT P K h, φ (Quotient.out (ι d)) := finsum_mem_image hinj
    _ = ∑ᶠ d ∈ cosT P K h, φ (Quotient.out d) := finsum_mem_congr rfl e2

end Count

theorem countSt : CountSt := by
  classical
  intro G _ U K P f f' hKU hPU hIw hC hfin f1 f1' hf hf' hmod h hh
  have rK : ∀ φ : G → ℂ, φ 1 = 1 → (∀ p ∈ P, ∀ g ∈ U, ∀ k ∈ K, φ (p * g * k) = φ p * φ g) →
      ∀ g ∈ U, ∀ k ∈ K, φ (g * k) = φ g := fun φ h1 hφ g hg k hk => by
    simpa [h1] using hφ 1 P.one_mem g hg k hk
  obtain ⟨hT, e1⟩ := sum_eq_cosT hKU hPU hIw hh (hfin h hh) (rK f f1 hf)
  obtain ⟨-, e1'⟩ := sum_eq_cosT hKU hPU hIw hh (hfin h hh) (rK f' f1' hf')
  obtain ⟨k₁, hk₁, k₂, hk₂, eC⟩ := hC h hh
  have hD : ∀ y, y ∈ dblK K h⁻¹ ↔ y ∈ dblK K h := fun y => by
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a * k₁, K.mul_mem ha hk₁, k₂ * b, K.mul_mem hk₂ hb, by rw [eC]; group⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * k₁⁻¹, K.mul_mem ha (K.inv_mem hk₁), k₂⁻¹ * b, K.mul_mem (K.inv_mem hk₂) hb, ?_⟩
      rw [eC]; group
  have hTi : cosT P K h⁻¹ = cosT P K h := Set.ext fun d =>
    ⟨fun ⟨p, hp, hp', e⟩ => ⟨p, hp, (hD p).1 hp', e⟩, fun ⟨p, hp, hp', e⟩ => ⟨p, hp, (hD p).2 hp', e⟩⟩
  have hsub : ∀ d ∈ cosT P K h, orb (P ⊓ K) (Quotient.out d)⁻¹ ⊆ cosT P K h := fun d hd => by
    rw [← hTi]; exact orb_sub_cosT hd
  have core := count_core hPU f1 f1' hf hf' hmod hT hT (fun e he => (out_cosT he).1) hsub hsub
  unfold avgK
  rw [e1, e1', core]

end PositivityTheory.Sph

end
