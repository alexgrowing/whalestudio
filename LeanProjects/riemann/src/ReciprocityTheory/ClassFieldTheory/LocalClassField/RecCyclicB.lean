import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclicA

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.RecCyc

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

theorem isCoprime_of_gen {G : Type} [Group G] [Fintype G] (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (r : ℚ)
    (hr : ∀ e : ℕ, (∃ j : ℤ, (e : ℚ) * r = j) → g₀ ^ e = 1) (k : ℤ) (hk : (k : ℚ) = Fintype.card G * r) :
    IsCoprime k (Fintype.card G : ℤ) := by
  have hn : 0 < Fintype.card G := Fintype.card_pos
  have ho : orderOf g₀ = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  rw [Int.isCoprime_iff_gcd_eq_one]
  obtain ⟨j, hj⟩ : ((Int.gcd k (Fintype.card G : ℤ) : ℕ) : ℤ) ∣ k := Int.gcd_dvd_left ..
  obtain ⟨e, he⟩ : Int.gcd k (Fintype.card G : ℤ) ∣ Fintype.card G :=
    Int.natCast_dvd_natCast.1 (Int.gcd_dvd_right ..)
  generalize Int.gcd k (Fintype.card G : ℤ) = d at hj he
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos ⟨e, he⟩ hn
  have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at he)
  have h1 : g₀ ^ e = 1 := by
    refine hr e ⟨j, ?_⟩
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0.ne'
    rw [hj, he] at hk
    push_cast at hk
    apply mul_left_cancel₀ hd'
    rw [hk]; ring
  have h2 : Fintype.card G ∣ e := ho ▸ orderOf_dvd_of_pow_eq_one h1
  rw [he] at h2
  have h3 : d * e ≤ 1 * e := by simpa using Nat.le_of_dvd he0 h2
  have := Nat.le_of_mul_le_mul_right h3 he0
  omega

theorem exists_gen_of_injective {G : Type} [Group G] [Finite G] (f : Additive G →+ QZ) (hf : Injective f) :
    ∃ g₀ : G, ∀ g, g ∈ Subgroup.zpowers g₀ := by
  have hn : 0 < Nat.card (Additive G) := Nat.card_pos
  have hmem : ∀ g, f g ∈ AddSubgroup.zmultiples
      (QuotientAddGroup.mk ((1 : ℚ) / (Nat.card (Additive G) : ℕ)) : QZ) := fun g =>
    qz_mem_zmultiples hn _ (by rw [← map_nsmul, card_nsmul_eq_zero', map_zero])
  have hf' : Injective (f.codRestrict _ hmem) := fun a b h => hf (congrArg Subtype.val h)
  have h1 : IsAddCyclic (Additive G) := isAddCyclic_of_injective _ hf'
  have h2 : IsCyclic G := isAddCyclic_additive_iff.1 h1
  exact IsCyclic.exists_generator

theorem defect_mem_B_iff {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : TRep R G) [Fintype G] [DiscreteTopology G] {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (a : M.V) (ha : ∀ g, M.rho g a = a)
    (z : M.coch.X 2) (hza : ∀ g, z.1 g = m g • a) (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀)
    (hr : ∀ e : ℕ, (∃ j : ℤ, (e : ℚ) * t g₀ = j) → g₀ ^ e = 1) :
    z ∈ M.coch.B 2 ↔ ∃ y, ∑ g, M.rho g y = a := by
  constructor
  · rintro ⟨b, hb⟩
    have h1 := sum_defect_smul M a b (fun g => by rw [hb]; exact hza g) g₀
    have h2 := sum_defect hm g₀
    generalize (∑ σ, m ![σ, g₀]) = k at h1 h2
    obtain ⟨u, v, huv⟩ := isCoprime_of_gen g₀ hg (t g₀) hr k h2
    have h3 : ∑ g, M.rho g a = (Fintype.card G : ℤ) • a := by
      rw [Finset.sum_congr rfl fun g _ => ha g]
      simp
    refine ⟨u • b.1 ![g₀] + v • a, ?_⟩
    simp only [map_add, map_zsmul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, ← h1, h3, smul_smul, smul_smul, ← add_smul,
      huv, one_smul]
  · rintro ⟨y, rfl⟩
    obtain ⟨b, hb⟩ := exists_cobound_of_norm M hm y
    exact ⟨b, Subtype.ext (funext fun g => by rw [hb, hza])⟩

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem kbarRep_ofK (σ : GK p K) (a : Additive Kˣ) : kbarRep p K σ (ofK p K a) = ofK p K a :=
  (mem_multOf_iff_fixed (le_refl K) _).1 (ofK_mem p K a) σ (fun y hy => σ.commutes ⟨y, hy⟩)

theorem exists_ofK_eq (x : KbarMult p) (hx : x ∈ multOf p K) : ∃ a : Kˣ, ofK p K (Additive.ofMul a) = x := by
  refine ⟨Units.mk0 ⟨((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p), hx⟩
    (fun h => (Additive.toMul x : (PadicAlgCl p)ˣ).ne_zero (congrArg Subtype.val h)), ?_⟩
  exact Units.ext rfl

variable (p K L) in

noncomputable def kToLayer [(subG p K L).Normal] : Additive Kˣ →+ (layer p K L).V where
  toFun a := ⟨ofK p K a, fun g => kbarRep_ofK g.1 a⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

theorem kToLayer_val [(subG p K L).Normal] (a : Additive Kˣ) : (kToLayer p K L a).1 = ofK p K a := rfl

theorem kToLayer_rho [(subG p K L).Normal] (g : GalLK p K L) (a : Additive Kˣ) :
    (layer p K L).rho g (kToLayer p K L a) = kToLayer p K L a :=
  (layer_invariant_iff _).2 (ofK_mem p K a) g

theorem exists_lift_layer [(subG p K L).Normal] (χ : charGrp (GK p K)) (hχ : TrivOn p K L χ) :
    ∃ tb : GalLK p K L → ℚ, IsLocallyConstant tb ∧
      ∀ g : GK p K, (QuotientAddGroup.mk (tb (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g) := by
  have key : ∀ g : GK p K, χ.1 (Additive.ofMul (QuotientGroup.mk g : GalLK p K L).out) = χ.1 (Additive.ofMul g) := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (subG p K L) g
    rw [hh, ofMul_mul, map_add, hχ h.1 h.2, add_zero]
  refine ⟨fun q => (χ.1 (Additive.ofMul q.out)).out, fun s => ?_, fun g => ?_⟩
  · rw [← QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.isOpen_preimage]
    have h1 : IsLocallyConstant fun g : GK p K => (χ.1 (Additive.ofMul g)).out :=
      IsLocallyConstant.comp (f := fun g : GK p K => χ.1 (Additive.ofMul g)) χ.2 (fun x : QZ => x.out)
    convert h1 s using 1
    ext g
    simp only [Set.mem_preimage, key]
  · rw [QuotientAddGroup.out_eq', key]

theorem exists_defect_layer [(subG p K L).Normal] (χ : charGrp (GK p K)) (tb : GalLK p K L → ℚ)
    (htb : ∀ g : GK p K, (QuotientAddGroup.mk (tb (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g)) :
    ∃ mb : (Fin 2 → GalLK p K L) → ℤ, ∀ q, (mb q : ℚ) = tb (q 0) + tb (q 1) - tb (q 0 * q 1) := by
  obtain ⟨m, hm⟩ := exists_defect (t := fun g : GK p K => tb (QuotientGroup.mk g)) χ.1 htb
  refine ⟨fun q => m fun i => (q i).out, fun q => ?_⟩
  rw [hm]
  simp only [QuotientGroup.mk_mul, QuotientGroup.out_eq']

theorem pairBr_eq_layerInf [(subG p K L).Normal] (a : Kˣ) (χ : charGrp (GK p K)) (tb : GalLK p K L → ℚ)
    (htb : IsLocallyConstant tb)
    (hχ : ∀ g : GK p K, (QuotientAddGroup.mk (tb (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g))
    (mb : (Fin 2 → GalLK p K L) → ℤ) (hmb : ∀ q, (mb q : ℚ) = tb (q 0) + tb (q 1) - tb (q 0 * q 1))
    (z : (layer p K L).coch.X 2) (hz : (layer p K L).coch.d 2 z = 0)
    (hza : ∀ q, z.1 q = mb q • kToLayer p K L (Additive.ofMul a)) :
    pairBr p K a χ = (layerInf p K L).hom.H 2 ((layer p K L).coch.cls 2 z hz) := by
  refine (isPairClass_pairBr a χ).unique ⟨fun g => tb (QuotientGroup.mk g), fun g => mb fun i => QuotientGroup.mk (g i),
    (layerInf p K L).hom.f 2 z, by rw [← (layerInf p K L).hom.comm, hz, map_zero],
    htb.comp_continuous continuous_quot_mk, hχ, fun g => hmb _, fun g => ?_, rfl⟩
  show (z.1 fun i => QuotientGroup.mk (g i)).1 = _
  rw [hza]
  rfl

theorem mem_normGrp_iff_layer (h : K ≤ L) [(subG p K L).Normal] [Fintype (GalLK p K L)] (a : Kˣ) :
    a ∈ normGrp p K L ↔ ∃ y : (layer p K L).V, ∑ g, (layer p K L).rho g y = kToLayer p K L (Additive.ofMul a) := by
  rw [mem_normGrp_iff]
  constructor
  · rintro ⟨y, hy, e⟩
    refine ⟨toLayer p ⟨y, hy⟩, Subtype.ext ?_⟩
    rw [← normHom_layer h, kToLayer_val]
    exact e
  · rintro ⟨y, hy⟩
    refine ⟨y.1, layer_val_mem h y, ?_⟩
    rw [normHom_layer h, hy, kToLayer_val]

end ReciprocityTheory.DiscreteGroups.LocalClassField.RecCyc
