import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Spec

open TensorProduct

theorem closure_ratio (N : ℕ) (i : Fin (N + 1)) : Subring.closure (Set.range (ratio ℤ N i)) = ⊤ := by
  refine eq_top_iff.2 fun s hs => ?_
  clear hs
  obtain ⟨p, rfl⟩ := aeval_ratio_surjective ℤ N i s
  induction p using MvPolynomial.induction_on with
  | C a => simpa using intCast_mem _ a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul, aeval_X]
    exact mul_mem hp (Subring.subset_closure ⟨j, rfl⟩)

theorem isAffineOpen_fst_inf_snd {X Y : Scheme.{0}} (f : X ⟶ Spec (.of ℤ)) (g : Y ⟶ Spec (.of ℤ)) {U : X.Opens}
    {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  let q : pullback (hU.fromSpec ≫ f) (hV.fromSpec ≫ g) ⟶ pullback f g :=
    pullback.map _ _ _ _ hU.fromSpec hV.fromSpec (𝟙 _) (by simp) (by simp)
  have e : q.opensRange = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V := by
    apply Opens.ext
    rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_map, hU.range_fromSpec, hV.range_fromSpec]
    rfl
  exact e ▸ isAffineOpen_opensRange q

theorem range_sup_range_eq_top {X Y : Scheme.{0}} (f : X ⟶ Spec (.of ℤ)) (g : Y ⟶ Spec (.of ℤ)) {U : X.Opens}
    {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    ((pullback.fst f g).appLE U (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_left).hom.range ⊔
      ((pullback.snd f g).appLE V (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_right).hom.range = ⊤ := by
  have hW := isAffineOpen_fst_inf_snd f g hU hV
  set W := pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V with hWdef
  let a := (pullback.fst f g).appLE U W inf_le_left
  let b := (pullback.snd f g).appLE V W inf_le_right
  have f₁ : Spec.map (CommRingCat.ofHom (algebraMap ℤ Γ(X, U))) ≫ 𝟙 _ = hU.fromSpec ≫ f :=
    specZIsTerminal.hom_ext _ _
  have g₁ : Spec.map (CommRingCat.ofHom (algebraMap ℤ Γ(Y, V))) ≫ 𝟙 _ = hV.fromSpec ≫ g :=
    specZIsTerminal.hom_ext _ _
  let q : pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ Γ(X, U))))
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ Γ(Y, V)))) ⟶ pullback f g :=
    pullback.map _ _ _ _ hU.fromSpec hV.fromSpec (𝟙 _) f₁ g₁
  let e : Spec (.of (Γ(X, U) ⊗[ℤ] Γ(Y, V))) ⟶ pullback f g := (pullbackSpecIso ℤ Γ(X, U) Γ(Y, V)).inv ≫ q
  have hq : q.opensRange = W := by
    apply Opens.ext
    rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_map, hU.range_fromSpec, hV.range_fromSpec]
    rfl
  have hr : e.opensRange = W := (Scheme.Hom.opensRange_comp_of_isIso _ _).trans hq
  have hr' : Set.range e ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec, ← hr, Scheme.Hom.coe_opensRange]
  let ψ : Γ(X, U) ⊗[ℤ] Γ(Y, V) →ₐ[ℤ] Γ(pullback f g, W) :=
    Algebra.TensorProduct.lift a.hom.toIntAlgHom b.hom.toIntAlgHom fun _ _ => Commute.all _ _
  let Ψ : CommRingCat.of (Γ(X, U) ⊗[ℤ] Γ(Y, V)) ⟶ Γ(pullback f g, W) := CommRingCat.ofHom ψ.toRingHom
  have ha : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := Γ(X, U)) (B := Γ(Y, V))) ≫ Ψ = a := by
    ext u
    simp [Ψ, ψ]
  have hb : CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := ℤ) (A := Γ(X, U)) (B := Γ(Y, V))).toRingHom) ≫ Ψ = b := by
    ext v
    simp [Ψ, ψ]
  have hψ : Spec.map Ψ ≫ e = hW.fromSpec := by
    apply pullback.hom_ext
    · have e₁ := IsAffineOpen.SpecMap_appLE_fromSpec (pullback.fst f g) hU hW inf_le_left
      simp only [e, q, Category.assoc, pullback.lift_fst, pullback.map]
      rw [pullbackSpecIso_inv_fst_assoc, ← Spec.map_comp_assoc, ha]
      exact e₁
    · have e₁ := IsAffineOpen.SpecMap_appLE_fromSpec (pullback.snd f g) hV hW inf_le_right
      simp only [e, q, Category.assoc, pullback.lift_snd, pullback.map]
      rw [pullbackSpecIso_inv_snd_assoc, ← Spec.map_comp_assoc]
      refine Eq.trans ?_ e₁
      congr 2
  let l := IsOpenImmersion.lift hW.fromSpec e hr'
  have hl : l ≫ hW.fromSpec = e := IsOpenImmersion.lift_fac _ _ _
  have hiso : IsIso (Spec.map Ψ) := by
    refine ⟨l, ?_, ?_⟩
    · rw [← cancel_mono hW.fromSpec, Category.assoc, hl, hψ, Category.id_comp]
    · rw [← cancel_mono e, Category.assoc, hψ, hl, Category.id_comp]
  have hsurj : Function.Surjective ψ := (isIso_SpecMap_iff.1 hiso).2
  refine eq_top_iff.2 fun s hs => ?_
  clear hs
  obtain ⟨t, rfl⟩ := hsurj s
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul u v =>
    have : ψ (u ⊗ₜ v) = a.hom u * b.hom v := by simp [ψ]
    rw [this]
    exact mul_mem ((le_sup_left : a.hom.range ≤ _) ⟨u, rfl⟩) ((le_sup_right : b.hom.range ≤ _) ⟨v, rfl⟩)

end GlobalTheory.CompanionTheory.MPDict.Spec

namespace GlobalTheory.CompanionTheory.MPDict.Spec

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def mratio (c : ∀ k, Bk n k) (p : Σ k, Bk n k) : Γ(MP ℤ m n, mchart c) :=
  pullRatio (prB n p.1) (mchart c) (c p.1) (mchart_le c p.1) p.2

theorem appLE_id_apply {X : Scheme.{0}} (U : X.Opens) (h : U ≤ 𝟙 X ⁻¹ᵁ U) (s : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U h).hom s = s := by
  have e : (𝟙 X : X ⟶ X).appLE U U h = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (X.presheaf.map_id (Opposite.op U))
  rw [e]
  rfl

theorem closure_mratio_of_eq (c : ∀ k, Bk n k) {W : (MP ℤ m n).Opens} (hW : W = mchart c)
    (hi : ∀ k, W ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (c k))
    (h : Subring.closure (Set.range fun p : Σ k, Bk n k => pullRatio (prB n p.1) W (c p.1) (hi p.1) p.2) = ⊤) :
    Subring.closure (Set.range (mratio c)) = ⊤ := by
  subst hW
  exact h

theorem isAffineOpen_mchart_and_closure : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k),
    IsAffineOpen (mchart c) ∧ Subring.closure (Set.range (mratio c)) = ⊤
  | 0, n, c => by
    let W : (MP ℤ 0 n).Opens := chart ℤ (n 0) (c 0)
    have e : W = mchart c := by
      apply Opens.ext
      ext x
      refine ⟨fun h => Set.mem_iInter.2 fun k => ?_, fun h => Set.mem_iInter.1 h 0⟩
      have hk : k = 0 := Fin.fin_one_eq_zero k
      subst hk
      exact h
    have hi : ∀ k, W ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (c k) := fun k => e.le.trans (mchart_le c k)
    refine ⟨e ▸ isAffineOpen_chart ℤ (n 0) (c 0), closure_mratio_of_eq c e hi ?_⟩
    refine eq_top_iff.2 ((closure_ratio (n 0) (c 0)).symm.le.trans (Subring.closure_le.2 ?_))
    rintro _ ⟨j, rfl⟩
    refine Subring.subset_closure ⟨⟨0, j⟩, ?_⟩
    simp only [pullRatio, W]
    exact appLE_id_apply _ _ _
  | m + 1, n, c => by
    let c' : ∀ k, Bk (Fin.tail n) k := fun j => c j.succ
    obtain ⟨hV, hG⟩ := isAffineOpen_mchart_and_closure m (Fin.tail n) c'
    have hU := isAffineOpen_chart ℤ (n 0) (c 0)
    let f := toSpecBase ℤ (n 0)
    let g := mpStr ℤ m (Fin.tail n)
    let W : (pullback f g).Opens := pullback.fst f g ⁻¹ᵁ chart ℤ (n 0) (c 0) ⊓ pullback.snd f g ⁻¹ᵁ mchart c'
    have e : (W : (MP ℤ (m + 1) n).Opens) = mchart c := by
      apply Opens.ext
      ext x
      refine ⟨fun h => Set.mem_iInter.2 fun k => ?_, fun h => ⟨Set.mem_iInter.1 h 0, Set.mem_iInter.2 fun j => Set.mem_iInter.1 h j.succ⟩⟩
      induction k using Fin.cases with
      | zero => exact h.1
      | succ j => exact Set.mem_iInter.1 h.2 j
    have hi : ∀ k, (W : (MP ℤ (m + 1) n).Opens) ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (c k) :=
      fun k => e.le.trans (mchart_le c k)
    refine ⟨e ▸ isAffineOpen_fst_inf_snd f g hU hV, closure_mratio_of_eq c e hi ?_⟩
    refine eq_top_iff.2 ((range_sup_range_eq_top f g hU hV).symm.le.trans (sup_le ?_ ?_))
    · rintro _ ⟨u, rfl⟩
      have hu : u ∈ Subring.closure (Set.range (ratio ℤ (n 0) (c 0))) := by
        rw [closure_ratio]; trivial
      have := (Subring.mem_map (f := ((pullback.fst f g).appLE _ W inf_le_left).hom)).2 ⟨u, hu, rfl⟩
      rw [RingHom.map_closure] at this
      refine (Subring.closure_le.2 ?_) this
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      exact Subring.subset_closure ⟨⟨0, j⟩, rfl⟩
    · rintro _ ⟨u, rfl⟩
      have hu : u ∈ Subring.closure (Set.range (mratio c')) := by
        rw [hG]; trivial
      have := (Subring.mem_map (f := ((pullback.snd f g).appLE _ W inf_le_right).hom)).2 ⟨u, hu, rfl⟩
      rw [RingHom.map_closure] at this
      refine (Subring.closure_le.2 ?_) this
      rintro _ ⟨_, ⟨⟨j, i⟩, rfl⟩, rfl⟩
      refine Subring.subset_closure ⟨⟨j.succ, i⟩, ?_⟩
      change ((pr ℤ (m + 1) n j.succ).appLE _ W _).hom _ = ((pullback.snd f g).appLE _ W inf_le_right).hom
        (((pr ℤ m (Fin.tail n) j).appLE _ (mchart c') _).hom _)
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
      rfl

theorem isAffineOpen_mchart (c : ∀ k, Bk n k) : IsAffineOpen (mchart c) :=
  (isAffineOpen_mchart_and_closure m n c).1

theorem closure_mratio (c : ∀ k, Bk n k) : Subring.closure (Set.range (mratio c)) = ⊤ :=
  (isAffineOpen_mchart_and_closure m n c).2

end GlobalTheory.CompanionTheory.MPDict.Spec

namespace GlobalTheory.CompanionTheory.MPDict.Spec

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem mratio_self (c : ∀ k, Bk n k) (k : Fin (m + 1)) : mratio c ⟨k, c k⟩ = 1 :=
  pullRatio_self

theorem evaluation_resG' {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    X.evaluation V x hx (resG X h s) = X.evaluation U x (h hx) s := by
  rw [← Scheme.germ_residue, ← Scheme.germ_residue]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]

theorem ptCoord_ne_zero_iff (x : MP ℤ m n) (k : Fin (m + 1)) (i : Bk n k) :
    ptCoord x ⟨k, i⟩ ≠ 0 ↔ x ∈ blockChart n k i := by
  have e := (MP ℤ m n).evaluation_ne_zero_iff_mem_basicOpen x (mem_ptChart x k)
    (pullRatio (prB n k) (blockChart n k (ptChart x k)) (ptChart x k) le_rfl i)
  rw [basicOpen_pullRatio] at e
  exact e.trans ⟨fun h => h.2, fun h => ⟨mem_ptChart x k, h⟩⟩

theorem ptCoord_eq_mul (c : ∀ k, Bk n k) {z : MP ℤ m n} (hz : z ∈ mchart c) (p : Σ k, Bk n k) :
    ptCoord z p = ptCoord z ⟨p.1, c p.1⟩ * (MP ℤ m n).evaluation (mchart c) z hz (mratio c p) := by
  obtain ⟨k, i⟩ := p
  let W₀ := blockChart n k (ptChart z k)
  let V : (MP ℤ m n).Opens := W₀ ⊓ mchart c
  have hzV : z ∈ V := ⟨mem_ptChart z k, hz⟩
  have hV₀ : V ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (ptChart z k) := inf_le_left
  have hV₁ : V ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (c k) := inf_le_right.trans (mchart_le c k)
  have e₀ : ∀ j : Bk n k, ptCoord z ⟨k, j⟩ =
      (MP ℤ m n).evaluation V z hzV (pullRatio (prB n k) V (ptChart z k) hV₀ j) := fun j => by
    rw [← resG_pullRatio (φ := prB n k) (W := W₀) (i := ptChart z k) (hi := le_rfl) (inf_le_left : V ≤ W₀),
      evaluation_resG']
    rfl
  have e₁ : (MP ℤ m n).evaluation (mchart c) z hz (mratio c ⟨k, i⟩) =
      (MP ℤ m n).evaluation V z hzV (pullRatio (prB n k) V (c k) hV₁ i) := by
    rw [← resG_pullRatio (φ := prB n k) (W := mchart c) (i := c k) (hi := mchart_le c k)
      (inf_le_right : V ≤ mchart c), evaluation_resG']
    rfl
  rw [e₀ i, e₀ (c k), e₁, ← map_mul]
  exact congrArg _ (pullRatio_mul_pullRatio (φ := prB n k) (hi := hV₀) (hj := hV₁) (k := i)).symm

theorem mCoordIdeal_le_of_scale {Ω : Type} [Field Ω] (y r : (Σ k, Bk n k) → Ω) (l : Fin (m + 1) → Ω)
    (h : ∀ p, y p = l p.1 * r p) :
    Geo.mCoordIdeal r ≤ Geo.mCoordIdeal y := by
  intro f hf
  rw [Geo.mCoordIdeal, RingHom.mem_ker] at hf ⊢
  let S : MvPolynomial (Fin (m + 1)) Ω →ₐ[Ω] MvPolynomial (Fin (m + 1)) Ω := aeval fun k => C (l k) * X k
  have e : (Geo.mConeMap y).toRingHom = S.toRingHom.comp (Geo.mConeMap r).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun p => ?_
    · simp
    · simp [Geo.mConeMap, S, h p, mul_comm, mul_left_comm, mul_assoc]
  have := RingHom.congr_fun e f
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this, hf, map_zero]

theorem ptIdeal_eq (c : ∀ k, Bk n k) {z : MP ℤ m n} (hz : z ∈ mchart c) :
    ptIdeal z = Geo.mCoordIdeal fun p => (MP ℤ m n).evaluation (mchart c) z hz (mratio c p) := by
  have hl : ∀ k, ptCoord z ⟨k, c k⟩ ≠ 0 := fun k => (ptCoord_ne_zero_iff z k (c k)).2 (mchart_le c k hz)
  refine le_antisymm ?_ ?_
  · exact mCoordIdeal_le_of_scale _ _ (fun k => (ptCoord z ⟨k, c k⟩)⁻¹) fun p => by
      rw [ptCoord_eq_mul c hz p, inv_mul_cancel_left₀ (hl p.1)]
  · exact mCoordIdeal_le_of_scale _ _ (fun k => ptCoord z ⟨k, c k⟩) fun p => ptCoord_eq_mul c hz p

def Phi (c : ∀ k, Bk n k) : Geo.MRing (Bk n) →+* MvPolynomial (Fin (m + 1)) Γ(MP ℤ m n, mchart c) :=
  eval₂Hom (Int.castRingHom _) fun p => C (mratio c p) * X p.1

@[simp] theorem Phi_X (c : ∀ k, Bk n k) (p : Σ k, Bk n k) : Phi c (X p) = C (mratio c p) * X p.1 := by
  simp [Phi]

theorem mem_ptIdeal_iff (c : ∀ k, Bk n k) {z : MP ℤ m n} (hz : z ∈ mchart c) (f : Geo.MRing (Bk n)) :
    f ∈ ptIdeal z ↔ MvPolynomial.map ((MP ℤ m n).evaluation (mchart c) z hz).hom (Phi c f) = 0 := by
  rw [ptIdeal_eq c hz, Geo.mCoordIdeal, RingHom.mem_ker]
  have e : (Geo.mConeMap (fun p => (MP ℤ m n).evaluation (mchart c) z hz (mratio c p))).toRingHom =
      (MvPolynomial.map ((MP ℤ m n).evaluation (mchart c) z hz).hom).comp (Phi c) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun p => ?_
    · simp
    · simp [Geo.mConeMap]
  have := RingHom.congr_fun e f
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this]

end GlobalTheory.CompanionTheory.MPDict.Spec

namespace GlobalTheory.CompanionTheory.MPDict.Spec

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem evaluation_eq_zero_of_specializes {X : Scheme.{0}} {U : X.Opens} {x y : X} (h : x ⤳ y) (hx : x ∈ U) (hy : y ∈ U)
    (s : Γ(X, U)) (hs : X.evaluation U x hx s = 0) : X.evaluation U y hy s = 0 := by
  by_contra hne
  have h1 : y ∈ X.basicOpen s := (X.evaluation_ne_zero_iff_mem_basicOpen y hy s).1 hne
  exact (X.evaluation_ne_zero_iff_mem_basicOpen x hx s).2 (h.mem_open (X.basicOpen s).isOpen h1) hs

theorem mem_mchart_ptChart (y : MP ℤ m n) : y ∈ mchart (ptChart y) :=
  Set.mem_iInter.2 fun k => mem_ptChart y k

theorem ptIdeal_le_of_specializes {x y : MP ℤ m n} (h : x ⤳ y) : ptIdeal x ≤ ptIdeal y := by
  intro f hf
  have hy := mem_mchart_ptChart y
  have hx : x ∈ mchart (ptChart y) := h.mem_open (mchart (ptChart y)).isOpen hy
  rw [mem_ptIdeal_iff _ hx] at hf
  rw [mem_ptIdeal_iff _ hy]
  ext a
  rw [coeff_map, coeff_zero]
  have := congrArg (coeff a) hf
  rw [coeff_map, coeff_zero] at this
  exact evaluation_eq_zero_of_specializes h hx hy _ this

def mono (c : ∀ k, Bk n k) (a : Fin (m + 1) → ℕ) : Geo.MRing (Bk n) := ∏ k, X ⟨k, c k⟩ ^ a k

theorem Phi_mono (c : ∀ k, Bk n k) (a : Fin (m + 1) → ℕ) : Phi c (mono c a) = ∏ k, X k ^ a k := by
  simp [mono, map_prod, mratio_self]

theorem exists_form (c : ∀ k, Bk n k)
    (s : Γ(MP ℤ m n, mchart c)) :
    ∃ (f : Geo.MRing (Bk n)) (a : Fin (m + 1) → ℕ), Phi c f = C s * ∏ k, X k ^ a k := by
  have hs : s ∈ Subring.closure (Set.range (mratio c)) := by rw [closure_mratio]; trivial
  induction hs using Subring.closure_induction with
  | mem s hs =>
    obtain ⟨p, rfl⟩ := hs
    refine ⟨X p, Pi.single p.1 1, ?_⟩
    rw [Phi_X, Finset.prod_eq_single p.1 (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]
    simp
  | zero => exact ⟨0, 0, by simp⟩
  | one => exact ⟨1, 0, by simp⟩
  | add s t _ _ hs ht =>
    obtain ⟨f, a, hf⟩ := hs
    obtain ⟨g, b, hg⟩ := ht
    refine ⟨f * mono c b + g * mono c a, a + b, ?_⟩
    simp only [map_add, map_mul, Phi_mono, hf, hg, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  | neg s _ hs =>
    obtain ⟨f, a, hf⟩ := hs
    exact ⟨-f, a, by simp [hf]⟩
  | mul s t _ _ hs ht =>
    obtain ⟨f, a, hf⟩ := hs
    obtain ⟨g, b, hg⟩ := ht
    refine ⟨f * g, a + b, ?_⟩
    simp only [map_mul, hf, hg, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring

theorem X_mem_ptIdeal_iff (x : MP ℤ m n) (p : Σ k, Bk n k) :
    (X p : Geo.MRing (Bk n)) ∈ ptIdeal x ↔ ptCoord x p = 0 := by
  rw [ptIdeal, Geo.mCoordIdeal, RingHom.mem_ker]
  simp [Geo.mConeMap]

theorem evaluation_eq_zero_of_le
    {x y : MP ℤ m n} (h : ptIdeal x ≤ ptIdeal y) (c : ∀ k, Bk n k) (hx : x ∈ mchart c) (hy : y ∈ mchart c)
    (s : Γ(MP ℤ m n, mchart c)) (hs : (MP ℤ m n).evaluation (mchart c) x hx s = 0) :
    (MP ℤ m n).evaluation (mchart c) y hy s = 0 := by
  obtain ⟨f, a, hf⟩ := exists_form c s
  have h1 : f ∈ ptIdeal x := by
    rw [mem_ptIdeal_iff c hx, hf, map_mul, map_C]
    erw [hs]
    simp
  have h2 := h h1
  rw [mem_ptIdeal_iff c hy, hf, map_mul, map_C, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact C_eq_zero.1 h2
  · exfalso
    simp only [map_prod, map_pow, map_X] at h2
    exact (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)) h2

theorem specializes_of_ptIdeal_le
    {x y : MP ℤ m n} (h : ptIdeal x ≤ ptIdeal y) : x ⤳ y := by
  have hy := mem_mchart_ptChart y
  have hx : x ∈ mchart (ptChart y) := Set.mem_iInter.2 fun k => by
    refine (ptCoord_ne_zero_iff x k _).1 fun h0 => ?_
    have h1 := h ((X_mem_ptIdeal_iff x ⟨k, ptChart y k⟩).2 h0)
    exact (ptCoord_ne_zero_iff y k _).2 (mem_ptChart y k) ((X_mem_ptIdeal_iff y _).1 h1)
  refine specializes_iff_forall_open.2 fun V hV hyV => ?_
  obtain ⟨s, hsV, hys⟩ := (isAffineOpen_mchart (ptChart y)).exists_basicOpen_le (V := ⟨V, hV⟩) ⟨y, hyV⟩ hy
  refine hsV ((MP ℤ m n).evaluation_ne_zero_iff_mem_basicOpen x hx s |>.1 fun h0 => ?_)
  exact ((MP ℤ m n).evaluation_ne_zero_iff_mem_basicOpen y hy s).2 hys
    (evaluation_eq_zero_of_le h _ hx hy s h0)

theorem specializes_iff_ptIdeal_le (m : ℕ) (n : Fin (m + 1) → ℕ) (x y : MP ℤ m n) :
    x ⤳ y ↔ ptIdeal x ≤ ptIdeal y :=
  ⟨ptIdeal_le_of_specializes, specializes_of_ptIdeal_le⟩

end GlobalTheory.CompanionTheory.MPDict.Spec
