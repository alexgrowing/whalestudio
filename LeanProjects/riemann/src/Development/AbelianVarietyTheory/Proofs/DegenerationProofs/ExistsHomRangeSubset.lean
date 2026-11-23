import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineOpenRingOnEqAdjoinInv

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

theorem comp_toSpecΓ_eq_valMap {C : Type} [CommRing C] {X : Scheme.{0}} (V : X.Opens) (p : Sp C ⟶ V)
    (h : ⊤ ≤ (p ≫ V.ι) ⁻¹ᵁ V) : p ≫ V.toSpecΓ = Spec.map (valMap (p ≫ V.ι) V h) := by
  rw [Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, valMap,
    ← Spec.map_comp, ← Spec.map_comp]
  have e : V.topIso.inv ≫ p.appTop = (p ≫ V.ι).appLE V ⊤ h := by
    rw [← Scheme.Hom.appLE_comp_appLE p V.ι V ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  rw [← e]

theorem exists_hom_range_subset {U : M.Z.Opens} (hU : IsAffineOpen U) (hUne : (U : Set M.Z).Nonempty)
    {V : M'.Z.Opens} (hVne : (V : Set M'.Z).Nonempty) (h : ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V) :
    ∃ (p : Sp Ω' ⟶ V) (g : (V : Scheme.{0}) ⟶ M.Z), p ≫ V.ι = M'.pt ∧ Set.range g ⊆ U ∧
      p ≫ g = spMap φ.toRingHom ≫ M.pt := by
  let χ : M.ringOn U →+* M'.ringOn V :=
    (φ.toRingHom.comp (M.ringOn U).val.toRingHom).codRestrict (M'.ringOn V) fun x => h x x.2
  let ψ : Γ(M.Z, U) →+* Γ(M'.Z, V) :=
    (M'.sectionsEquiv V hVne).symm.toRingHom.comp (χ.comp (M.sectionsEquiv U hUne).toRingHom)
  have hr : Set.range M'.pt ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M'.top_le_preimage_pt hVne)
  have hp := IsOpenImmersion.lift_fac V.ι M'.pt hr
  set p := IsOpenImmersion.lift V.ι M'.pt hr
  have hp' : p ≫ V.toSpecΓ = Spec.map (valMap M'.pt V (M'.top_le_preimage_pt hVne)) := by
    have := comp_toSpecΓ_eq_valMap V p (hp ▸ M'.top_le_preimage_pt hVne)
    simpa only [hp] using this
  refine ⟨p, V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, hp, ?_, ?_⟩
  · rintro _ ⟨w, rfl⟩
    rw [← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  rw [← Category.assoc, hp']
  conv_rhs => rw [← specMap_valMap_fromSpec hU M.pt (M.top_le_preimage_pt hUne)]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext a
  have e : (M'.sectionsEquiv V hVne (ψ a) : Ω') = φ (M.sectionsEquiv U hUne a) :=
    congrArg Subtype.val ((M'.sectionsEquiv V hVne).apply_symm_apply _)
  exact e

theorem IsHom.map_mem_of_ringOn {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) {U : M.Z.Opens} (hU : IsAffineOpen U)
    (hUne : (U : Set M.Z).Nonempty) {V : M'.Z.Opens} (h : ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V) {z : M'.Z}
    (hz : z ∈ V) : f z ∈ U := by
  obtain ⟨p, g, hp, hg, e⟩ := exists_hom_range_subset hU hUne ⟨z, hz⟩ h
  have e' : V.ι ≫ f = g := hom_ext_of_isOpenImmersion V.ι hp (by rw [← Category.assoc, hp]; exact hf) e
  exact hg ⟨⟨z, hz⟩, by rw [← e']; rfl⟩

theorem isAffineOpen_of_isHom (R : Subalgebra o Ω) [Algebra.FiniteType o R] [IsFractionRing R Ω] {U : M.Z.Opens}
    (hR : R ≤ M.ringOn U) {g : (ofAffine o Ω R).Z ⟶ M.Z} (hg : M.IsHom (ofAffine o Ω R) (AlgHom.id o Ω) g)
    (hU : Set.range g ⊆ U) : IsAffineOpen U ∧ M.ringOn U = R := by
  have hne : (U : Set M.Z).Nonempty := ⟨_, hU ⟨genericPoint _, rfl⟩⟩
  refine ⟨?_, le_antisymm (fun x hx => ?_) hR⟩
  · haveI : IsAffine (ofAffine o Ω R).Z := inferInstanceAs (IsAffine (Sp R))
    obtain ⟨p, h, hp, -, e⟩ := exists_hom_range_subset (M := ofAffine o Ω R) (φ := AlgHom.id o Ω)
      (isAffineOpen_top _) ⟨genericPoint _, trivial⟩ hne fun x hx => by
        obtain ⟨a, rfl⟩ := mem_ringOn_univ_ofAffine.1 hx
        exact hR a.2
    have hid : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := Spec.map_id _
    have hg' : (ofAffine o Ω R).pt ≫ g = M.pt := by
      have := hg
      rwa [IsHom, hid, Category.id_comp] at this
    have e1 : h ≫ g = U.ι := hom_ext_of_isOpenImmersion (φ := AlgHom.id o Ω) U.ι hp
      (by rw [← Category.assoc, e, Category.assoc, hg']) (by rw [hp, hid, Category.id_comp])
    have hr : Set.range g ⊆ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
    have hl := IsOpenImmersion.lift_fac U.ι g hr
    set l := IsOpenImmersion.lift U.ι g hr
    have e2 : h ≫ l = 𝟙 _ := by rw [← cancel_mono U.ι, Category.assoc, hl, e1, Category.id_comp]
    have e3 : l ≫ h = 𝟙 _ := by
      refine IsHom.unique (φ := AlgHom.id o Ω) ?_ (isHom_id _)
      have : (ofAffine o Ω R).pt ≫ l = p := by rw [← cancel_mono U.ι, Category.assoc, hl, hg', hp]
      rw [IsHom, ← Category.assoc, this, e]
    haveI : IsIso h := ⟨l, e2, e3⟩
    exact IsAffine.of_isIso h
  · obtain ⟨a, rfl⟩ := mem_ringOn_univ_ofAffine.1 (mem_ringOn.2 fun z _ =>
      hg.map_mem_O (mem_ringOn.1 hx (g z) (hU ⟨z, rfl⟩)))
    exact a.2

theorem IsHom.inv_mem_O {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) {z : M'.Z} {x : Ω} (hx : x ∈ M.O (f z))
    (h0 : x ≠ 0) (hi : (φ x)⁻¹ ∈ M'.O z) : x⁻¹ ∈ M.O (f z) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have e := hf.valF_app ⟨_, hz⟩ a
  have h1 : z ∈ M'.Z.basicOpen (f.app U a) :=
    (isUnit_valF_iff (U := f ⁻¹ᵁ U) hz _).1 ((isUnit_O_iff _).2 ⟨by simpa [e] using h0, by simpa only [e] using hi⟩)
  rw [← Scheme.preimage_basicOpen] at h1
  exact ((isUnit_O_iff _).1 ((isUnit_valF_iff hz a).2 h1)).2

theorem IsHom.div_of_div {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) {J : Type} {t : J → Ω} {i k : J} {z : M'.Z}
    (hk : M.Div t k (f z)) (h : M'.Div (fun j => φ (t j)) i z) : M.Div t i (f z) := by
  have h0 : t i / t k ≠ 0 := div_ne_zero ((map_ne_zero φ).1 h.1) hk.1
  exact (hk.div_iff_isUnit i).2 ((isUnit_O_iff _).2 ⟨h0, hf.inv_mem_O (hk.2 i) h0 (by simpa using h.2 k)⟩)

section Pairing

variable {J : Type} [Fintype J]

def pairing (φ : Ω →ₐ[o] Ω') (s : J → Ω') (v : J → Ω) : Ω' := ∑ j, φ (v j) * s j

theorem pairing_sum {I : Type} [Fintype I] (s : J → Ω') (c : I → Ω) (a : I → J → Ω) :
    pairing φ s (∑ i, c i • a i) = ∑ i, φ (c i) * pairing φ s (a i) := by
  simp only [pairing, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum, _root_.mul_assoc]
  exact Finset.sum_comm

theorem pairing_div (s : J → Ω') (v : J → Ω) (c : Ω) :
    pairing φ s (fun j => v j / c) = (φ c)⁻¹ * pairing φ s v := by
  simp only [pairing, map_div₀, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_pairing_eq {I : Type} [Fintype I] (s : J → Ω') {S : Subalgebra o Ω} {a : I → J → Ω} {v : J → Ω}
    (hv : v ∈ Submodule.span S (Set.range a)) :
    ∃ c : I → Ω, (∀ i, c i ∈ S) ∧ pairing φ s v = ∑ i, φ (c i) * pairing φ s (a i) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  exact ⟨fun i => c i, fun i => (c i).2, pairing_sum s (fun i => (c i : Ω)) a⟩

theorem IsHom.exists_div_pairing {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f) (s : J → Ω') {I K : Type} [Fintype I]
    [Fintype K] {a : I → J → Ω} {b : K → J → Ω} {z : M'.Z}
    (h : Submodule.span (M.O (f z)) (Set.range a) = Submodule.span (M.O (f z)) (Set.range b)) {i : I}
    (hi : M'.Div (fun i => pairing φ s (a i)) i z) : ∃ k, M'.Div (fun k => pairing φ s (b k)) k z := by
  have h0 : pairing φ s (a i) ≠ 0 := hi.1
  have h1 : ∀ k, pairing φ s (b k) / pairing φ s (a i) ∈ M'.O z := fun k => by
    obtain ⟨c, hc, e⟩ := exists_pairing_eq (φ := φ) s (h ▸ Submodule.subset_span ⟨k, rfl⟩ :
      b k ∈ Submodule.span (M.O (f z)) (Set.range a))
    rw [e, Finset.sum_div]
    exact sum_mem fun i' _ => by
      rw [mul_div_assoc]
      exact mul_mem (hf.map_mem_O (hc i')) (hi.2 i')
  obtain ⟨d, hd, e⟩ := exists_pairing_eq (φ := φ) s (h ▸ Submodule.subset_span ⟨i, rfl⟩ :
      a i ∈ Submodule.span (M.O (f z)) (Set.range b))
  have e1 : ∑ k, (⟨φ (d k), hf.map_mem_O (hd k)⟩ * ⟨_, h1 k⟩ : M'.O z) = 1 := by
    refine Subtype.ext ?_
    simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, OneMemClass.coe_one, ← mul_div_assoc,
      ← Finset.sum_div, ← e, div_self h0]
  obtain ⟨k, -, hk⟩ := IsLocalRing.exists_of_isUnit_sum (e1 ▸ isUnit_one)
  obtain ⟨hk0, hk1⟩ := (isUnit_O_iff _).1 (isUnit_of_mul_isUnit_right hk)
  have hk2 : pairing φ s (b k) ≠ 0 := fun h => hk0 (by simp [h])
  refine ⟨k, hk2, fun k' => ?_⟩
  have := mul_mem (h1 k') hk1
  convert this using 1
  field_simp

theorem Lat.exists_eq_sum_pairing [DecidableEq J] (EE : M.Lat J) (s : J → Ω') {I : Type} [Fintype I]
    {a : I → J → Ω} {z : M.Z} (h : EE.E z = Submodule.span (M.O z) (Set.range a)) (j : J) :
    ∃ c : I → Ω, s j = ∑ i, φ (c i) * pairing φ s (a i) := by
  obtain ⟨U, b, hz, hb, H⟩ := EE.loc z
  have h1 : ∀ l, b l ∈ Submodule.span (M.O z) (Set.range a) := fun l =>
    h ▸ H z hz ▸ Submodule.subset_span ⟨l, rfl⟩
  choose c _ hc using fun l => exists_pairing_eq (φ := φ) s (h1 l)
  have e : (Pi.single j 1 : J → Ω) = ∑ l, b⁻¹ j l • b l := by
    ext j'
    have := congrFun (congrFun (Matrix.nonsing_inv_mul b (isUnit_iff_ne_zero.2 hb)) j) j'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp [Finset.sum_apply, this, Pi.single_apply, eq_comm]
  have e2 : pairing φ s (Pi.single j 1) = s j := by
    simp [pairing, Pi.single_apply, apply_ite φ]
  refine ⟨fun i => ∑ l, b⁻¹ j l * c l i, ?_⟩
  rw [← e2, e]
  refine (pairing_sum s (fun l => b⁻¹ j l) fun l => b l).trans ?_
  simp only [hc, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
  exact Finset.sum_comm

theorem Lat.eq_top_of_pairing_mem [DecidableEq J] (EE : M.Lat J) {s : J → Ω'}
    (hs : Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤) {I : Type} [Fintype I]
    {a : I → J → Ω} {z : M.Z} (h : EE.E z = Submodule.span (M.O z) (Set.range a)) {g : Ω'} (hg : g ≠ 0)
    {K : Subfield Ω'} (h1 : ∀ x, φ x ∈ K) (h2 : ∀ i, pairing φ s (a i) / g ∈ K) : K = ⊤ := by
  have h3 : ∀ j, s j / g ∈ K := fun j => by
    obtain ⟨c, e⟩ := EE.exists_eq_sum_pairing (φ := φ) s h j
    rw [e, Finset.sum_div]
    exact sum_mem fun i _ => by
      rw [mul_div_assoc]
      exact mul_mem (h1 _) (h2 i)
  refine top_unique (hs ▸ Subfield.closure_le.2 ?_)
  rintro _ (⟨x, rfl⟩ | ⟨i, j, rfl⟩)
  · exact h1 x
  · have := div_mem (h3 j) (h3 i)
    rwa [div_div_div_cancel_right₀ hg] at this

end Pairing

theorem map_mem_of_ringOn {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty) {K : Subfield Ω'}
    (h : ∀ x ∈ M.ringOn V, φ x ∈ K) (x : Ω) : φ x ∈ K := by
  obtain ⟨a, b, -, rfl⟩ := exists_eq_div hV hne x
  rw [map_div₀]
  exact div_mem (h _ ((mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩)) (h _ ((mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩))

theorem div_comp_iff {I K : Type} {t : K → Ω} {e : I → K} (he : Function.Surjective e) {i : I} {z : M.Z} :
    M.Div (fun i => t (e i)) i z ↔ M.Div t (e i) z :=
  and_congr_right fun _ => (he.forall (p := fun k => t k / t (e i) ∈ M.O z)).symm

theorem div_mul_prod_iff {I K : Type} {t : I → Ω} {u : K → Ω} {i : I} {k : K} {z : M.Z} :
    M.Div (fun q : I × K => t q.1 * u q.2) (i, k) z ↔ M.Div t i z ∧ M.Div u k z := by
  constructor
  · rintro ⟨h0, h⟩
    have hi : t i ≠ 0 := left_ne_zero_of_mul h0
    have hk : u k ≠ 0 := right_ne_zero_of_mul h0
    exact ⟨⟨hi, fun i' => by simpa [mul_div_mul_right _ _ hk] using h (i', k)⟩,
      ⟨hk, fun k' => by simpa [mul_div_mul_left _ _ hi] using h (i, k')⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_ne_zero h1.1 h2.1, fun q => by simpa [mul_div_mul_comm] using mul_mem (h1.2 q.1) (h2.2 q.2)⟩

end GlobalTheory.ZH.RatModel
end
