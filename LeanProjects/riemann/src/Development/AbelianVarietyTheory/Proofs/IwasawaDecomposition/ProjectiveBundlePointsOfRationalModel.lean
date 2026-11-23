import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle.ProjPts

open GlobalTheory.ZH.RatModel GlobalTheory.Points

variable {F Ω Ω' : Type} [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
  {M : RatModel F Ω} {M' : RatModel F Ω'} {φ : Ω →ₐ[F] Ω'} {f : M'.Z ⟶ M.Z}

theorem exists_open_span_le {J : Type} [Fintype J] (a b : J → J → Ω) {z : M.Z}
    (h : Submodule.span (M.O z) (Set.range a) ≤ Submodule.span (M.O z) (Set.range b)) :
    ∃ V : M.Z.Opens, z ∈ V ∧ ∀ w ∈ V, Submodule.span (M.O w) (Set.range a) ≤ Submodule.span (M.O w) (Set.range b) := by
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun _).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  refine ⟨⟨⋂ i, ⋂ l, {w | (c i l : Ω) ∈ M.O w}, isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun l =>
    M.isOpen_setOf_mem_O _⟩, Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun l => (c i l).2, fun w hw => ?_⟩
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact (Submodule.mem_span_range_iff_exists_fun _).2
    ⟨fun l => ⟨c i l, Set.mem_iInter.1 (Set.mem_iInter.1 hw i) l⟩, hc i⟩

theorem exists_affine_basis {J : Type} [Fintype J] [DecidableEq J] (EE : M.Lat J) (B : Matrix J J Ω) {z : M.Z}
    (h : EE.E z = Submodule.span (M.O z) (Set.range B)) :
    ∃ W : M.Z.Opens, IsAffineOpen W ∧ z ∈ W ∧ ∀ w ∈ W, EE.E w = Submodule.span (M.O w) (Set.range B) := by
  obtain ⟨U, b, hz, -, H⟩ := EE.loc z
  have e := (H z hz).symm.trans h
  obtain ⟨V₁, h₁, H₁⟩ := exists_open_span_le b B e.le
  obtain ⟨V₂, h₂, H₂⟩ := exists_open_span_le B b e.ge
  obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := U ⊓ V₁ ⊓ V₂) (x := z) ⟨⟨hz, h₁⟩, h₂⟩
  exact ⟨W, hW, hzW, fun w hw => (H w (hle hw).1.1).trans (le_antisymm (H₁ w (hle hw).1.2) (H₂ w (hle hw).2))⟩

variable {K : Type} [Field K]

theorem range_subset {p : Sp K ⟶ M.Z} {U : M.Z.Opens} (h : p (IsLocalRing.closedPoint K) ∈ U) :
    Set.range p ⊆ U := by
  rw [range_eq_singleton p (IsLocalRing.closedPoint K), Set.singleton_subset_iff]
  exact h

theorem exists_point {U : M.Z.Opens} (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty)
    (ψ : M.ringOn U →+* K) :
    ∃ p : Sp K ⟶ M.Z, p (IsLocalRing.closedPoint K) ∈ U ∧ ∀ a : M.ringOn U, M.val p a = ψ a := by
  let χ : Γ(M.Z, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (ψ.comp (M.sectionsEquiv U hne).toRingHom)
  have h := le_preimage_specMap_fromSpec hU χ
  refine ⟨Spec.map χ ≫ hU.fromSpec, (le_preimage_iff _ _).1 h, fun a => ?_⟩
  obtain ⟨a, rfl⟩ := (M.sectionsEquiv U hne).surjective a
  rw [coe_sectionsEquiv, val_valF ((top_le_preimage_iff _ _).1 h), valF_eq_valR, valR_eq _ _ h,
    valMap_specMap_fromSpec]
  rfl

theorem ext_of_val {U : M.Z.Opens} (hU : IsAffineOpen U) {p q : Sp K ⟶ M.Z}
    (hp : p (IsLocalRing.closedPoint K) ∈ U) (hq : q (IsLocalRing.closedPoint K) ∈ U)
    (H : ∀ a ∈ M.ringOn U, M.val p a = M.val q a) : p = q := by
  refine ext_of_valR hU ((le_preimage_iff _ _).2 hp) ((le_preimage_iff _ _).2 hq) fun g => ?_
  have := H _ ((mem_ringOn_iff_exists ⟨_, hp⟩).2 ⟨g, rfl⟩)
  rwa [val_valF (range_subset hp), val_valF (range_subset hq)] at this

theorem val_eq_of_adjoin {U : M.Z.Opens} {p q : Sp K ⟶ M.Z}
    (hp : p (IsLocalRing.closedPoint K) ∈ U) (hq : q (IsLocalRing.closedPoint K) ∈ U) {T : Set Ω}
    (hT : M.ringOn U = Algebra.adjoin F T) (h0 : ∀ a, M.val p (algebraMap F Ω a) = M.val q (algebraMap F Ω a))
    (h1 : ∀ a ∈ T, M.val p a = M.val q a) : ∀ a ∈ M.ringOn U, M.val p a = M.val q a := by
  have sp := specializes_of_range_eq (range_eq_singleton p (IsLocalRing.closedPoint K))
  have sq := specializes_of_range_eq (range_eq_singleton q (IsLocalRing.closedPoint K))
  intro a ha
  rw [hT] at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact h1 x hx
  | algebraMap r => exact h0 r
  | add x y hx hy ex ey =>
    rw [← hT] at hx hy
    rw [val_add sp (ringOn_le_O hp hx) (ringOn_le_O hp hy), val_add sq (ringOn_le_O hq hx) (ringOn_le_O hq hy), ex, ey]
  | mul x y hx hy ex ey =>
    rw [← hT] at hx hy
    rw [val_mul sp (ringOn_le_O hp hx) (ringOn_le_O hp hy), val_mul sq (ringOn_le_O hq hx) (ringOn_le_O hq hy), ex, ey]

theorem exists_ringHom (R : Subalgebra F Ω) {σ : Type} (t : σ → Ω')
    (ht : ∀ P : MvPolynomial σ Ω, MvPolynomial.eval₂ (φ : Ω →+* Ω') t P = 0 → P = 0) (S : Subalgebra F Ω')
    {T : Set Ω'} (hS : S = Algebra.adjoin F (φ '' (R : Set Ω) ∪ T)) (hT : ∀ y ∈ T, y = 1 ∨ y ∈ Set.range t)
    (v : R →+* K) (c : σ → K) :
    ∃ ψ : S →+* K, (∀ (r : R) (h : φ r ∈ S), ψ ⟨φ r, h⟩ = v r) ∧ ∀ j (h : t j ∈ S), ψ ⟨t j, h⟩ = c j := by
  let g : MvPolynomial σ R →+* Ω' := MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp R.val.toRingHom) t
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    have := ht (MvPolynomial.map R.val.toRingHom P) (by rw [MvPolynomial.eval₂_map]; exact hP)
    exact MvPolynomial.map_injective R.val.toRingHom Subtype.val_injective (this.trans (map_zero _).symm)
  have hC : ∀ r : R, g (MvPolynomial.C r) = φ r := fun r => MvPolynomial.eval₂Hom_C _ _ r
  have hX : ∀ j, g (MvPolynomial.X j) = t j := fun j => MvPolynomial.eval₂Hom_X' _ _ j
  have hle : ∀ y ∈ S, y ∈ g.range := by
    intro y hy
    rw [hS] at hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨r, hr, rfl⟩ | hx
      · exact ⟨_, hC ⟨r, hr⟩⟩
      · rcases hT x hx with rfl | ⟨j, rfl⟩
        · exact one_mem _
        · exact ⟨_, hX j⟩
    | algebraMap r => exact ⟨_, (hC (algebraMap F R r)).trans (φ.commutes r)⟩
    | add x y _ _ ex ey => exact add_mem ex ey
    | mul x y _ _ ex ey => exact mul_mem ex ey
  let e : MvPolynomial σ R ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict
    ⟨fun _ _ h => hg (congrArg Subtype.val h), g.rangeRestrict_surjective⟩
  let ι : S →+* g.range := S.val.toRingHom.codRestrict g.range fun y => hle y y.2
  have key : ∀ (P : MvPolynomial σ R) (y : S), g P = y → e.symm (ι y) = P := fun P y h =>
    e.symm_apply_eq.2 (Subtype.ext h.symm)
  refine ⟨(MvPolynomial.eval₂Hom v c).comp (e.symm.toRingHom.comp ι), fun r h => ?_, fun j h => ?_⟩
  · exact (congrArg (MvPolynomial.eval₂Hom v c) (key _ ⟨_, h⟩ (hC r))).trans (MvPolynomial.eval₂Hom_C _ _ r)
  · exact (congrArg (MvPolynomial.eval₂Hom v c) (key _ ⟨_, h⟩ (hX j))).trans (MvPolynomial.eval₂Hom_X' _ _ j)

theorem div_of_ne_zero {J : Type} {t : J → Ω} {p : Sp K ⟶ M.Z} {c : J → K} {i k : J} (hi : c i ≠ 0)
    (hk : M.Div t k (p (IsLocalRing.closedPoint K))) (h : ∀ j, c j = c k * M.val p (t j / t k)) :
    M.Div t i (p (IsLocalRing.closedPoint K)) ∧ ∀ j, M.val p (t j / t i) = c j / c i := by
  have hr := range_eq_singleton p (IsLocalRing.closedPoint K)
  have h0 : M.val p (t i / t k) ≠ 0 := right_ne_zero_of_mul (h i ▸ hi)
  have hd : M.Div t i (p (IsLocalRing.closedPoint K)) :=
    (hk.div_iff_isUnit i).2 ((val_ne_zero_iff hr ⟨_, hk.2 i⟩).1 h0)
  refine ⟨hd, fun j => ?_⟩
  have e := val_mul (specializes_of_range_eq hr) (hd.2 j) (hk.2 i)
  rw [div_mul_div_cancel₀ hd.1] at e
  rw [eq_div_iff hi, h j, h i, e]
  ring

theorem projPoints {J : Type} [Fintype J] [DecidableEq J] {EE : M.Lat J} {s : J → Ω'}
    (H : ProjBundle M EE M' φ f s) : ProjPoints M EE M' φ f s := by
  refine ⟨H.hom, fun z' B _ hB => ?_, fun K _ x B hB hE c hc => ?_⟩
  · obtain ⟨W, hW, hz, hE⟩ := exists_affine_basis EE B hB
    exact (H.chart W B hW ⟨_, hz⟩ hE).1 z' hz
  obtain ⟨W, hW, hz, hEW⟩ := exists_affine_basis EE B hE
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
  replace hi : c i ≠ 0 := hi
  obtain ⟨hti, hind⟩ := H.gen B hB i
  obtain ⟨U, hU, hUeq, hR⟩ := (H.chart W B hW ⟨_, hz⟩ hEW).2 i hti
  set t := (B.map φ).mulVec s with ht
  have hmem : ∀ z', z' ∈ U ↔ f z' ∈ W ∧ M'.Div t i z' := fun z' => Set.ext_iff.1 hUeq z'
  have hne : (U : Set M'.Z).Nonempty := by
    refine ⟨genericPoint M'.Z, (hmem _).2 ⟨?_, div_genericPoint hti⟩⟩
    rw [← M'.pt_apply (IsLocalRing.closedPoint Ω')]
    have e : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') ∈ W := by
      rw [H.hom]
      exact M.top_le_preimage_pt ⟨_, hz⟩ (x := spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) trivial
    exact e
  let v : M.ringOn W →+* K := (valHom x _ (range_eq_singleton x (IsLocalRing.closedPoint K))).comp
    (Subalgebra.inclusion (ringOn_le_O hz)).toRingHom
  obtain ⟨ψ, hψ₁, hψ₂⟩ := exists_ringHom (M.ringOn W) _ hind (M'.ringOn U) hR (by
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · exact Or.inl (by rw [hj]; exact div_self hti)
    · exact Or.inr ⟨⟨j, hj⟩, rfl⟩) v fun j => c j.1 / c i
  obtain ⟨p, hp, hv⟩ := exists_point hU hne ψ
  have hφ : ∀ a ∈ M.ringOn W, φ a ∈ M'.ringOn U := fun a ha =>
    hR ▸ Algebra.subset_adjoin (Or.inl ⟨a, ha, rfl⟩)
  have hcomp : ∀ q : Sp K ⟶ M'.Z, q (IsLocalRing.closedPoint K) ∈ U → ∀ a ∈ M.ringOn W,
      M.val (q ≫ f) a = M'.val q (φ a) := fun q hq a ha =>
    H.hom.val_comp q _ (ringOn_le_O ((hmem _).1 hq).1 ha)
  have hpf : p ≫ f = x := by
    refine ext_of_val hW ((hmem _).1 hp).1 hz fun a ha => ?_
    exact (hcomp p hp a ha).trans ((hv ⟨_, hφ a ha⟩).trans (hψ₁ ⟨a, ha⟩ _))
  have hrat : ∀ j, M'.val p (t j / t i) = c j / c i := fun j => by
    by_cases hj : j = i
    · rw [hj, div_self hti, div_self hi, RatModel.val_one]
    · have hm : t j / t i ∈ M'.ringOn U := hR ▸ Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)
      exact (hv ⟨_, hm⟩).trans (hψ₂ ⟨j, hj⟩ hm)
  refine ⟨p, ⟨hpf, i, ((hmem _).1 hp).2, fun j => by rw [hrat, mul_div_cancel₀ _ hi]⟩, ?_⟩
  rintro q ⟨hqf, k, hk, hq⟩
  obtain ⟨hd, hqr⟩ := div_of_ne_zero hi hk hq
  have hqU : q (IsLocalRing.closedPoint K) ∈ U := (hmem _).2 ⟨by rw [← hqf] at hz; exact hz, hd⟩
  have hb : ∀ a ∈ M.ringOn W, M'.val q (φ a) = M'.val p (φ a) := fun a ha => by
    rw [← hcomp q hqU a ha, ← hcomp p hp a ha, hqf, hpf]
  refine ext_of_val hU hqU hp (val_eq_of_adjoin hqU hp hR (fun a => ?_) ?_)
  · rw [← φ.commutes]
    exact hb _ (Subalgebra.algebraMap_mem _ a)
  · rintro _ (⟨a, ha, rfl⟩ | ⟨j, rfl⟩)
    · exact hb a ha
    · exact (hqr j).trans (hrat j).symm

end GlobalTheory.FlagBundle.ProjPts

theorem GlobalTheory.FlagBundle.projPoints_of_projBundle : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω']
    [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J]
    [DecidableEq J] (EE : M.Lat J) (s : J → Ω'), ProjBundle M EE M' φ f s → ProjPoints M EE M' φ f s :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H => GlobalTheory.FlagBundle.ProjPts.projPoints H

end
