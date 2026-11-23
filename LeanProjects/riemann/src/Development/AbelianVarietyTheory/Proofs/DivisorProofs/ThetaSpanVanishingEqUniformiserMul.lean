import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSendsClosedFibreGenericPointDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtPointFunctionFieldMapOfGenericPointCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDvrClosedFibreStalkUniformiserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldLinearIndependentClosedFibreGenericPStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ModPi

theorem gp_comp_cst (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R) :
    gp X ≫ p = spMap (GlobalTheory.Desc.cst p) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop, gp,
    Scheme.fromSpecStalk_appTop]
  ext r
  simp [GlobalTheory.Desc.cst, fnOf, Scheme.functionField]

theorem cst_reg_zero (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp R) (x : X)
    (hx : p x = closedPoint R) (r : R) :
    GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) ∧ (r ∈ maximalIdeal R → GlobalTheory.Cartier.ZeroAt x (GlobalTheory.Desc.cst p r)) := by
  have hreg : GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _
  refine ⟨hreg, fun hr => zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩⟩
  have h1 := (unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact h1
  have h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hr

theorem span_add {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁) {S : Set F₁} {v w : F₁}
    (hv : v ∈ spanBy c S) (hw : w ∈ spanBy c S) : v + w ∈ spanBy c S := by
  obtain ⟨n, r, t, ht, rfl⟩ := hv
  obtain ⟨m, r', t', ht', rfl⟩ := hw
  refine ⟨n + m, Fin.append r r', Fin.append t t', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ht i
    · rw [Fin.append_right]; exact ht' i
  · rw [Fin.sum_univ_add]; simp

theorem regAt_npow {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : GlobalTheory.Cartier.RegAt x f) (n : ℕ) :
    GlobalTheory.Cartier.RegAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem modPi : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → ∀ ϖ : T, maximalIdeal T = Ideal.span {ϖ} → ∀ z ∈ spanBy (GlobalTheory.Desc.cst H'.hom) (θ '' regSet y), GlobalTheory.Cartier.ZeroAt y' z → ∃ z₁ ∈ spanBy (GlobalTheory.Desc.cst H'.hom) (θ '' regSet y), z = GlobalTheory.Desc.cst H'.hom (a ϖ) * z₁ := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hff y y' hy hy' hdy hdy' ϖ hmT
  have hmD : maximalIdeal D = Ideal.span {a ϖ} := by rw [← hm, hmT, Ideal.map_span, Set.image_singleton]
  have hcomp : θ.comp (cst H.hom) = (cst H'.hom).comp a := by
    obtain ⟨l, hl1, hl2⟩ := hff
    have e1 := gp_comp_cst H.left T H.hom
    have e2 := gp_comp_cst H'.left D H'.hom
    have hl : l = gp H'.left := by simpa using hl1
    have key : spMap (θ.comp (cst H.hom)) = spMap ((cst H'.hom).comp a) := by
      calc spMap (θ.comp (cst H.hom)) = spMap θ ≫ spMap (cst H.hom) := by simp [spMap, CommRingCat.ofHom_comp]
        _ = spMap θ ≫ gp H.left ≫ H.hom := by rw [e1]
        _ = l ≫ π ≫ H.hom := by rw [← Category.assoc, ← hl2, Category.assoc]
        _ = gp H'.left ≫ H'.hom ≫ spMap a := by rw [hpb.w, hl]
        _ = spMap (cst H'.hom) ≫ spMap a := by rw [← Category.assoc, e2]
        _ = spMap ((cst H'.hom).comp a) := by simp [spMap, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  have hθc : ∀ t, θ (cst H.hom t) = cst H'.hom (a t) := fun t => by
    rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply]
  set c := cst H'.hom with hc
  have hreg : ∀ u, GlobalTheory.Cartier.RegAt y u → GlobalTheory.Cartier.RegAt y' (θ u) := by
    intro u hu
    have hpt := GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy'
    exact GlobalTheory.T.regularAtPoint_functionField_map_of_genericPoint_comp H.left H'.left π θ ⟨_, hff.choose_spec⟩ y' u (hpt ▸ hu)
  have hcreg : ∀ d, GlobalTheory.Cartier.RegAt y' (c d) := fun d => (cst_reg_zero D H'.left H'.hom y' hy' d).1
  have hc0reg : ∀ t, GlobalTheory.Cartier.RegAt y (cst H.hom t) := fun t => (cst_reg_zero T H.left H.hom y hy t).1
  have hϖz : GlobalTheory.Cartier.ZeroAt y (cst H.hom ϖ) :=
    (cst_reg_zero T H.left H.hom y hy ϖ).2 (by rw [hmT]; exact Ideal.subset_span rfl)
  obtain ⟨hϖ0, hfac⟩ := GlobalTheory.T.semiAbelian_dvr_closedFibre_stalk_uniformiser T H hH y hy hdy ϖ hmT

  have hdiv : ∀ x, GlobalTheory.Cartier.ZeroAt y x → ∃ w, GlobalTheory.Cartier.RegAt y w ∧ x = cst H.hom ϖ * w := by
    intro x hx
    by_cases hx0 : x = 0
    · exact ⟨0, regAt_zero y, by rw [hx0, mul_zero]⟩
    obtain ⟨k, w, hw, rfl⟩ := hfac x hx0
    rcases le_or_gt 1 k with hk | hk
    · refine ⟨cst H.hom ϖ ^ (k - 1).toNat * w, (regAt_npow (hc0reg ϖ) _).mul hw.regAt, ?_⟩
      rw [← _root_.mul_assoc, ← pow_succ', ← zpow_natCast]
      congr 2; omega
    · exfalso
      have hk' : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have e : cst H.hom ϖ ^ k * w * cst H.hom ϖ ^ (-k).toNat = w := by
        rw [mul_comm _ (cst H.hom ϖ ^ (-k).toNat), ← _root_.mul_assoc, ← zpow_natCast, hk',
          ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, _root_.one_mul]
      exact (zeroAt_iff.1 (e ▸ hx.mul (regAt_npow (hc0reg ϖ) _))).2 hw
  have hgeo := GlobalTheory.T.residueField_linearIndependent_closedFibre_genericPoints T D a ha hm H H' π θ hH hpb hff y y' hy hy' hdy hdy'
  set S := spanBy c (θ '' regSet y) with hS

  have hyes : ∀ (n : ℕ) (d : Fin n → D) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) →
      (∀ cc : Fin n → T, GlobalTheory.Cartier.ZeroAt y (∑ i, cst H.hom (cc i) * u i) → ∀ i, cc i ∈ maximalIdeal T) →
      GlobalTheory.Cartier.ZeroAt y' (∑ i, c (d i) * θ (u i)) → ∃ z₁ ∈ S, ∑ i, c (d i) * θ (u i) = c (a ϖ) * z₁ := by
    intro n d u hu hind hz
    have hd := hgeo n u hu hind d hz
    choose e he using fun i => Ideal.mem_span_singleton'.1 (hmD ▸ hd i)
    refine ⟨∑ i, c (e i) * θ (u i), ⟨n, e, fun i => θ (u i), fun i => ⟨u i, hu i, rfl⟩, rfl⟩, ?_⟩
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← he i, map_mul]; ring
  have hmain : ∀ (n : ℕ) (d : Fin n → D) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) →
      GlobalTheory.Cartier.ZeroAt y' (∑ i, c (d i) * θ (u i)) → ∃ z₁ ∈ S, ∑ i, c (d i) * θ (u i) = c (a ϖ) * z₁ := by
    intro n
    induction n with
    | zero => intro d u hu hz; exact hyes 0 d u hu (fun _ _ i => i.elim0) hz
    | succ n ih =>
      intro d u hu hz
      by_cases hind : ∀ cc : Fin (n + 1) → T, GlobalTheory.Cartier.ZeroAt y (∑ i, cst H.hom (cc i) * u i) → ∀ i, cc i ∈ maximalIdeal T
      · exact hyes _ d u hu hind hz
      push_neg at hind
      obtain ⟨cc, hZ, k, hk⟩ := hind
      obtain ⟨ν, hν⟩ : ∃ ν : T, ν * cc k = 1 := by
        obtain ⟨v, hv⟩ := IsLocalRing.notMem_maximalIdeal.1 hk
        exact ⟨↑v⁻¹, by rw [← hv, Units.inv_mul]⟩
      obtain ⟨w, hw, hrel⟩ := hdiv _ hZ
      rw [Fin.sum_univ_succAbove _ k] at hrel
      have hrel' := congrArg θ hrel
      simp only [map_add, map_sum, map_mul, hθc] at hrel'
      have hν' : c (a ν) * c (a (cc k)) = 1 := by rw [← map_mul, ← map_mul, hν, map_one, map_one]
      set d' : Fin n → D := fun j => d (k.succAbove j) - d k * a ν * a (cc (k.succAbove j)) with hd'
      set u' : Fin n → H.left.functionField := fun j => u (k.succAbove j) with hu'
      have hsplit : ∑ i, c (d i) * θ (u i) = c (a ϖ) * (c (d k * a ν) * θ w) + ∑ j, c (d' j) * θ (u' j) := by
        rw [Fin.sum_univ_succAbove _ k]
        have : ∑ j, c (d' j) * θ (u' j) = ∑ j, c (d (k.succAbove j)) * θ (u (k.succAbove j)) -
            c (d k) * c (a ν) * ∑ j, c (a (cc (k.succAbove j))) * θ (u (k.succAbove j)) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [hd', hu', map_sub, map_mul]; ring
        rw [this, map_mul]
        linear_combination (c (d k) * c (a ν)) * hrel' - (c (d k) * θ (u k)) * hν'
      have hz' : GlobalTheory.Cartier.ZeroAt y' (∑ j, c (d' j) * θ (u' j)) := by
        have e : ∑ j, c (d' j) * θ (u' j) = ∑ i, c (d i) * θ (u i) + c (a ϖ) * (c (-(d k * a ν)) * θ w) := by
          rw [hsplit, map_neg]; ring
        rw [e]
        refine hz.add (ZeroAt.mul ?_ ((hcreg _).mul (hreg w hw)))
        exact (cst_reg_zero D H'.left H'.hom y' hy' (a ϖ)).2 (by rw [hmD]; exact Ideal.subset_span rfl)
      obtain ⟨z₁, hz₁, e₁⟩ := ih d' u' (fun j => hu _) hz'
      refine ⟨c (d k * a ν) * θ w + z₁, span_add c ⟨1, fun _ => d k * a ν, fun _ => θ w, fun _ => ⟨w, hw, rfl⟩, by simp⟩ hz₁, ?_⟩
      rw [hsplit, e₁]; ring
  intro z hz hzy
  obtain ⟨n, r, t, ht, rfl⟩ := hz
  choose u hu hut using ht
  have e : ∑ i, c (r i) * t i = ∑ i, c (r i) * θ (u i) := Finset.sum_congr rfl fun i _ => by rw [hut i]
  rw [e] at hzy ⊢
  exact hmain n r u hu hzy

end GlobalTheory.Desc.ModPi
