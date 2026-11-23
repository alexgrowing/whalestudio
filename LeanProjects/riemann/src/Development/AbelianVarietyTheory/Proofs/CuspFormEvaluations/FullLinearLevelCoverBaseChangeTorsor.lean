import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsIdempotentElemRangeSpMapSubset
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatFullLinearLevelStructure

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FullLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem mem_iff_modN (k : ℕ) (x : Dw.La) :
    x ∈ (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La) ↔ Dw.ModN k x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨b, _, hb⟩ => ⟨b, by rw [← hb, Nat.cast_smul_eq_nsmul]⟩,
    fun ⟨b, hb⟩ => ⟨b, trivial, by rw [hb, Nat.cast_smul_eq_nsmul]⟩⟩

theorem mk_eq_iff (k : ℕ) (a b : Dw.La) :
    (Submodule.Quotient.mk a : LatMod Dw k) = Submodule.Quotient.mk b ↔ Dw.ModN k (a - b) := by
  rw [Submodule.Quotient.eq, mem_iff_modN]

theorem finite_latMod (k : ℕ) (hk : 0 < k) : Finite (LatMod Dw k) := by
  obtain ⟨J, _, π, r, hr, hπ⟩ := LevelFlat.exists_finite_quotient Dw k hk
  refine Finite.of_surjective (fun j => (Submodule.Quotient.mk (r j) : LatMod Dw k)) fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨π a, (mk_eq_iff k _ _).2 ((hπ _ _).1 (hr _))⟩

theorem nsmul_latMod (k : ℕ) (q : LatMod Dw k) : k • q = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_iff_modN]
  exact ⟨a, Nat.cast_smul_eq_nsmul _ _ _⟩

variable (Xo : Moduli Dw l)

theorem exists_descend (k : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    (ev : Dw.La → (ptO Xo x0 ⟶ Xo.univ.t.G)) (hadd : ∀ a b, ev (a + b) = ev a * ev b)
    (hlin : ∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) (hker : ∀ a, ev (k • a) = 1)
    (hinj : ∀ (K : Type) [Field K] (χ : S →+* K) (a b : Dw.La),
      spMap χ ≫ (ev a).left = spMap χ ≫ (ev b).left → Dw.ModN k (a - b)) :
    ∃ ev' : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G), IsFullLev Xo k x0 ev' ∧
      ∀ a, ev' (Submodule.Quotient.mk a) = ev a := by
  choose r hr using Submodule.Quotient.mk_surjective (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La)
  have h : ∀ a, ev (r (Submodule.Quotient.mk a)) = ev a := fun a => by
    obtain ⟨b, hb⟩ := (mk_eq_iff k _ _).1 (hr (Submodule.Quotient.mk a))
    rw [sub_eq_iff_eq_add.1 hb, hadd, hker, _root_.one_mul]
  refine ⟨fun q => ev (r q), ⟨fun a b => ?_, fun o a => ?_, fun K _ χ a b hab => ?_⟩, h⟩
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    beta_reduce
    rw [← Submodule.Quotient.mk_add, h, h, h, hadd]
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    beta_reduce
    rw [← Submodule.Quotient.mk_smul, h, h, hlin]
  · rw [← hr a, ← hr b]
    exact (mk_eq_iff k _ _).2 (hinj K χ _ _ hab)

theorem pow_eq_one {k : ℕ} {S : Type} [CommRing S] {x0 : Sp S ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (h : IsFullLev Xo k x0 ev) (q : LatMod Dw k) : ev q ^ k = 1 := by
  let f : LatMod Dw k →+ Additive (ptO Xo x0 ⟶ Xo.univ.t.G) :=
    AddMonoidHom.mk' (fun q => Additive.ofMul (ev q)) fun a b => congrArg Additive.ofMul (h.1 a b)
  have := map_nsmul f k q
  rw [nsmul_latMod, map_zero] at this
  exact (congrArg Additive.toMul this).symm

theorem baseChange {k : ℕ} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x0 : Sp S ⟶ Xo.X}
    {x1 : Sp T ⟶ Xo.X} (h : ptO Xo x1 ⟶ ptO Xo x0) (hh : h.left = spMap ψ)
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) :
    IsFullLev Xo k x1 (fun q => h ≫ ev q) := by
  refine ⟨fun a b => ?_, fun o a => ?_, fun K _ χ a b hab => hev.2.2 K (χ.comp ψ) a b ?_⟩
  · beta_reduce
    rw [hev.1, MonObj.comp_mul]
  · beta_reduce
    rw [hev.2.1, Category.assoc]
  · have : spMap χ ≫ h.left ≫ (ev a).left = spMap χ ≫ h.left ≫ (ev b).left := hab
    rw [hh] at this
    rw [spMap_comp, Category.assoc, Category.assoc]
    exact this

theorem eq_of_agree (hL : Laws) {k : ℕ} (hk : 0 < k) {S T : Type} [CommRing S] [CommRing T] (χ : S →+* T)
    (hχ : ∀ e, χ e = 1 → IsUnit e) {x0 : Sp S ⟶ Xo.X} {a b : ptO Xo x0 ⟶ Xo.univ.t.G} (ha : a ^ k = 1)
    (hb : b ^ k = 1) (hab : spMap χ ≫ a.left = spMap χ ≫ b.left) : a = b := by
  obtain ⟨e, he, He⟩ := exists_isIdempotentElem_torsion_eq hL E H Dw l Xo S x0 k hk a b ha hb
  have h1 : e = 1 := (hχ e ((He T χ).2 hab)).mul_left_cancel (he.eq.trans (_root_.mul_one _).symm)
  have h2 := (He S (RingHom.id S)).1 h1
  have h3 : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id (CommRingCat.of S)
  rw [h3] at h2
  exact Over.OverMorphism.ext ((Category.id_comp _).symm.trans (h2.trans (Category.id_comp _)))

theorem exists_geometric (hL : Laws) {k : ℕ} (hk : 0 < k) (K : Type) [Field K] [IsAlgClosed K] (x0 : Sp K ⟶ Xo.X) :
    ∃ ev, IsFullLev Xo k x0 ev ∧ ∀ p : ptO Xo x0 ⟶ Xo.univ.t.G, p ^ k = 1 → ∃ q, ev q = p := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x0 ≫ Xo.s)
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x0 β.hom hβ.symm
  obtain ⟨ev, hev, h⟩ := exists_descend Xo k x0 (I.ev k) (I.add k) (I.lin k) (fun a => (I.ker k hk _).2 ⟨a, rfl⟩)
    fun K' _ χ a b hab => by
      have h1 : I.ev k a = I.ev k b :=
        eq_of_agree Xo hL hk χ (fun e he => isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at he)
          ((I.onto k hk _).2 ⟨_, rfl⟩) ((I.onto k hk _).2 ⟨_, rfl⟩) hab
      have h2 : I.ev k a = I.ev k (a - b) * I.ev k b := by rw [← I.add, sub_add_cancel]
      rw [h2, mul_eq_right, I.ker k hk] at h1
      exact h1
  refine ⟨ev, hev, fun p hp => ?_⟩
  obtain ⟨a, ha⟩ := (I.onto k hk p).1 hp
  exact ⟨_, (h a).trans ha⟩

theorem onto_of_local (hL : Laws) {k : ℕ} (hk : 0 < k) {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) (p : ptO Xo x0 ⟶ Xo.univ.t.G)
    (hp : p ^ k = 1) : ∃ q, ev q = p := by
  haveI := finite_latMod (Dw := Dw) k hk
  let K := AlgebraicClosure (IsLocalRing.ResidueField T)
  let χ : T →+* K := (algebraMap (IsLocalRing.ResidueField T) K).comp (IsLocalRing.residue T)
  have hχ : ∀ e, χ e = 1 → IsUnit e := fun e he => by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0
    simp [χ, h0] at he
  let h : ptO Xo (spMap χ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap χ) rfl
  obtain ⟨ev₀, -, h₀⟩ := exists_geometric Xo hL hk K (spMap χ ≫ x0)
  have hpow : ∀ a : ptO Xo x0 ⟶ Xo.univ.t.G, a ^ k = 1 → (h ≫ a) ^ k = 1 := fun a ha => by
    rw [← MonObj.comp_pow, ha, MonObj.comp_one]
  choose f hf using fun q => h₀ (h ≫ ev q) (hpow _ (pow_eq_one Xo hev q))
  have hinj : Function.Injective f := fun a b hab => hev.2.2 K χ a b
    (congrArg CommaMorphism.left ((hf a).symm.trans ((congrArg ev₀ hab).trans (hf b))))
  obtain ⟨r, hr⟩ := h₀ (h ≫ p) (hpow p hp)
  obtain ⟨q, rfl⟩ := Finite.surjective_of_injective hinj r
  exact ⟨q, eq_of_agree Xo hL hk χ hχ (pow_eq_one Xo hev q) hp
    (congrArg CommaMorphism.left ((hf q).symm.trans hr))⟩

theorem injective_of_local {k : ℕ} {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) : Function.Injective ev :=
  fun a b hab => hev.2.2 _ (IsLocalRing.residue T) a b (by rw [hab])

theorem exists_levGrp (hL : Laws) {k : ℕ} (hk : 0 < k) {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev ev' : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) (hev' : IsFullLev Xo k x0 ev') :
    ∃ g : LevGrp Dw k, ∀ q, ev' q = ev (g q) := by
  haveI := finite_latMod (Dw := Dw) k hk
  choose f hf using fun q => onto_of_local Xo hL hk hev (ev' q) (pow_eq_one Xo hev' q)
  have hi := injective_of_local Xo hev
  let g : LatMod Dw k →ₗ[𝓞 E] LatMod Dw k :=
    { toFun := f
      map_add' := fun a b => hi (by rw [hev.1, hf, hf, hf, hev'.1])
      map_smul' := fun o a => hi (by rw [RingHom.id_apply, hev.2.1, hf, hf, hev'.2.1]) }
  have hg : Function.Injective g := fun a b hab => injective_of_local Xo hev'
    ((hf a).symm.trans ((congrArg ev hab).trans (hf b)))
  exact ⟨LinearEquiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩, fun q => (hf q).symm⟩

end FullLevel

open FullLevel in

theorem fullLevel_cover_baseChange_torsor :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (k : ℕ), 0 < k → (∀ (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X), ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (ev : LatMod Dw k → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ IsFullLev Xo k (spMap φ ≫ x0) ev) ∧ (∀ (S T : Type) [CommRing S] [CommRing T] (ψ : S →+* T) (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X) (h : ptO Xo x1 ⟶ ptO Xo x0), h.left = spMap ψ → ∀ ev, IsFullLev Xo k x0 ev → IsFullLev Xo k x1 (fun q => h ≫ ev q) ∧ ∀ q, ev q ^ k = 1) ∧ (∀ (T : Type) [CommRing T] [IsLocalRing T] (x0 : Sp T ⟶ Xo.X) (ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)), IsFullLev Xo k x0 ev → (∀ p : ptO Xo x0 ⟶ Xo.univ.t.G, p ^ k = 1 → ∃ q, ev q = p) ∧ ∀ ev', IsFullLev Xo k x0 ev' → ∃ g : LevGrp Dw k, ∀ q, ev' q = ev (g q)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x0 : Sp K ⟶ Xo.X), ∃ ev, IsFullLev Xo k x0 ev := by
  intro hL E _ _ _ H Dw l Xo k hk
  refine ⟨fun S _ x0 => ?_, fun S T _ _ ψ x0 x1 h hh ev hev => ⟨baseChange Xo ψ h hh hev, pow_eq_one Xo hev⟩,
    fun T _ _ x0 ev hev => ⟨onto_of_local Xo hL hk hev, fun ev' hev' => exists_levGrp Xo hL hk hev hev'⟩,
    fun K _ _ x0 => (exists_geometric Xo hL hk K x0).imp fun _ h => h.1⟩
  obtain ⟨B, _, φ, ev, hφ, h1, h2, h3, h4⟩ := exists_faithfullyFlat_linear_level hL E H Dw l Xo S x0 k hk
  obtain ⟨ev', hev', -⟩ := exists_descend Xo k _ ev h1 h2 h3 h4
  exact ⟨B, inferInstance, φ, ev', hφ, hev'⟩

end GlobalTheory
