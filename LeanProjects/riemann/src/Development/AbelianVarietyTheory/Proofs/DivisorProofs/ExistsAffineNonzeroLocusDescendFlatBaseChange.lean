import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivOfIsPushout

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.FlatSec
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AmplePoint

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem exists_of_mem_map [Algebra R R'] {A A' : Type} [CommRing A] [CommRing A'] [Algebra R A] (p : A →+* A')
    (s' : R' →+* A') (e : R' ⊗[R] A ≃+ A') (he : ∀ c v, e (c ⊗ₜ v) = s' c * p v) (N : Ideal A) {y : A'}
    (hy : y ∈ N.map p) : ∃ x : R' ⊗[R] (N.restrictScalars R), e ((N.restrictScalars R).subtype.lTensor R' x) = y := by
  suffices h : ∀ r, ∃ x : R' ⊗[R] (N.restrictScalars R), e ((N.restrictScalars R).subtype.lTensor R' x) = r * y by
    simpa using h 1
  refine Submodule.span_induction (p := fun y _ => ∀ r, ∃ x : R' ⊗[R] (N.restrictScalars R),
    e ((N.restrictScalars R).subtype.lTensor R' x) = r * y) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨v, hv, rfl⟩ r
    obtain ⟨t, rfl⟩ := e.surjective r
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c a => exact ⟨c ⊗ₜ ⟨a * v, N.mul_mem_left a hv⟩, by simp [he, mul_assoc]⟩
    | add a b ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨x', hx'⟩ := hb
      exact ⟨x + x', by rw [map_add, map_add, hx, hx', map_add, add_mul]⟩
  · exact fun r => ⟨0, by simp⟩
  · intro a b _ _ ha hb r
    obtain ⟨x, hx⟩ := ha r
    obtain ⟨x', hx'⟩ := hb r
    exact ⟨x + x', by rw [map_add, map_add, hx, hx', mul_add]⟩
  · intro a b _ hb r
    obtain ⟨x, hx⟩ := hb (r * a)
    exact ⟨x, by rw [hx, smul_eq_mul, mul_assoc]⟩

def vanIdeal (W U : X.Opens) : Ideal Γ(X, W) where
  carrier := {v | X.basicOpen v ≤ U}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => (X.basicOpen_add_le a b).trans (sup_le ha hb)
  smul_mem' := fun c a ha => by
    change X.basicOpen (c * a) ≤ U
    rw [Scheme.basicOpen_mul]
    exact inf_le_right.trans ha

theorem exists_pow_mem (π : X' ⟶ X) [IsAffineHom π] {W : X.Opens} (hW : IsAffineOpen W) (U : X.Opens)
    (t : Γ(X', π ⁻¹ᵁ W)) (ht : X'.basicOpen t ≤ π ⁻¹ᵁ U) : ∃ m, t ^ m ∈ (vanIdeal W U).map (π.app W).hom := by
  have hW' := hW.preimage π
  change t ∈ ((vanIdeal W U).map (π.app W).hom).radical
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hP, hp⟩
  by_contra h
  let z : Spec Γ(X', π ⁻¹ᵁ W) := ⟨P, hp⟩
  have key : ∀ s : Γ(X', π ⁻¹ᵁ W), hW'.fromSpec z ∈ X'.basicOpen s ↔ s ∉ P := fun s => by
    change z ∈ hW'.fromSpec ⁻¹ᵁ X'.basicOpen s ↔ _
    rw [hW'.fromSpec_preimage_basicOpen]
    rfl
  have hz := (key t).2 h
  obtain ⟨v, hv, hzv⟩ := hW.exists_basicOpen_le (V := U) ⟨π (hW'.fromSpec z), ht hz⟩ (X'.basicOpen_le t hz)
  refine (key ((π.app W).hom v)).1 ?_ (hP (Ideal.mem_map_of_mem _ hv))
  rw [← Scheme.preimage_basicOpen]
  exact hzv

theorem exists_sec_mem (g : R →+* R') (hg : g.Flat) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (CommRingCat.of R)) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R'))
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (M : LB X) (hM : M.IsLB) {α : Type} [Fintype α]
    (W : α → X.Opens) (j : α → M.ι) (hA : ∀ a, IsAffineOpen (W a)) (hW : ∀ a, W a ≤ M.U (j a))
    (hc : ∀ y : X, ∃ a, y ∈ W a) (N : ∀ a, Ideal Γ(X, W a)) (σ : LB.Sec (M.pull π))
    (hσ : ∀ a, rs X' (le_pull M π (hW a)) (σ.f fun _ => j a) ∈ (N a).map (π.app (W a)).hom)
    (z : X') (hz : z ∈ nonzeroLocus σ) :
    ∃ u : M.Sec, π z ∈ nonzeroLocus u ∧ ∀ a, rs X (hW a) (u.f (j a)) ∈ N a := by
  let _ : Algebra R R' := g.toAlgebra
  have : Module.Flat R R' := hg
  let _ : ∀ U : X.Opens, Algebra R Γ(X, U) := fun U => (cst f U).toAlgebra
  choose e he using fun a => exists_equiv_of_isPushout (R := R) (π.app (W a)) (cst f' (π ⁻¹ᵁ W a))
    (isPushout_app hg H (hA a).isCompact (hA a).isQuasiSeparated)
  choose e' he' using fun p : α × α => exists_equiv_of_isPushout (R := R) (π.app (W p.1 ⊓ W p.2))
    (cst f' (π ⁻¹ᵁ (W p.1 ⊓ W p.2))) (isPushout_app hg H
      (QuasiSeparatedSpace.inter_isCompact _ _ (W p.1).isOpen (hA p.1).isCompact (W p.2).isOpen (hA p.2).isCompact)
      (IsQuasiSeparated.of_quasiSeparatedSpace _))
  let d : (∀ a, (N a).restrictScalars R) →ₗ[R] (∀ p : α × α, Γ(X, W p.1 ⊓ W p.2)) :=
    { toFun := fun v p => rs X inf_le_left (v p.1).1 -
        rs X (inf_le_inf (hW p.1) (hW p.2)) (M.g (j p.1) (j p.2)).val * rs X inf_le_right (v p.2).1
      map_add' := fun v w => funext fun p => by
        simp only [Pi.add_apply, Submodule.coe_add, map_add]; ring
      map_smul' := fun r v => funext fun p => by
        simp only [Pi.smul_apply, Submodule.coe_smul, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, rs_cst,
          RingHom.id_apply]; ring }
  choose x hxe using fun a => exists_of_mem_map (π.app (W a)).hom (cst f' (π ⁻¹ᵁ W a)) (e a) (he a) (N a) (hσ a)
  have hx : ∀ {n : ℕ} {c : Fin n → R'} {v : Fin n → ∀ a, (N a).restrictScalars R},
      (∀ a, x a = ∑ i, AddEquiv.refl _ (c i ⊗ₜ v i a)) →
      ∀ a z, π z ∈ W a → gs (𝟙 X') z _ (σ.f fun _ => j a) =
        ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z _ (v i a).1 := fun {n c v} h a z hz => by
    have h' := congrArg (gs (𝟙 X') z (π ⁻¹ᵁ W a)) (hxe a).symm
    simp only [h a, map_sum, AddEquiv.refl_apply, LinearMap.lTensor_tmul, Submodule.subtype_apply, he] at h'
    rw [gs_comb f' π _ z hz] at h'
    exact (gs_res (𝟙 X') z _ hz _).symm.trans h'
  obtain ⟨n, c, v, hv, hd⟩ := exists_comb_ker (fun a => AddEquiv.refl _) e' d x
    (fun n c v h p => fn_ext fun z hz => by
      simp only [he']
      rw [gs_comb f' π _ z hz, LBGerm.gs_zero (𝟙 X') z _ hz]
      have h₁ := gs_pull_trans σ z (hW _ hz.1) (hW _ hz.2)
      rw [hx h p.1 z hz.1, hx h p.2 z hz.2, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h₁
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h₁
      refine (congrArg _ (gs_diff (hW p.1) (hW p.2) (v i p.1).1 (v i p.2).1 π z hz)).trans ?_
      ring)
  choose u hu using fun i => exists_sec_of_refinement hM W j hW hc (fun a => (v i a).1) fun y a b ha hb => by
    have h := congrArg (gs (𝟙 X) y (W a ⊓ W b)) (congrFun (hd i) (a, b))
    exact sub_eq_zero.1 ((gs_diff (hW a) (hW b) (v i a).1 (v i b).1 (𝟙 X) y ⟨ha, hb⟩).symm.trans
      (h.trans (LBGerm.gs_zero (𝟙 X) y _ ⟨ha, hb⟩)))
  have hu' : ∀ i a, rs X (hW a) ((u i).f (j a)) = (v i a).1 := fun i a => fn_ext fun y hy => by
    rw [gs_res (𝟙 X) y _ hy, hu i y (j a) a (hW a hy) hy, gm_self hM (𝟙 X) y (hW a hy), Units.val_one,
      _root_.one_mul]
  obtain ⟨a, ha⟩ := hc (π z)
  have h₁ := (mem_nonzeroLocus_iff_isUnit σ (k := fun _ => j a) (mem_pull.2 (hW a ha))).1 hz
  replace h₁ := hx hv a z ha ▸ h₁
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum h₁
  refine ⟨u i, (mem_nonzeroLocus_iff_pull (u i) π z (hW a ha)).2 ?_, fun b => hu' i b ▸ (v i b).2⟩
  rw [← gs_res π z (hW a) ha]
  exact (congrArg (fun w => IsUnit (gs π z _ w)) (hu' i a)).mpr (isUnit_of_mul_isUnit_right hi)

def chartPullPullPow (L : LB X) (f : X' ⟶ X) (n : ℕ) :
    ChartPull ((lbPow L n).pull f) (lbPow (L.pull f) n) (𝟙 X') where
  idx J := fun _ _ => J PUnit.unit PUnit.unit
  le _ _ hy := mem_powChart.2 (mem_pull.2 (mem_powChart.1 (mem_pull.1 hy)))
  g y J J' hJ hJ' := by
    have h₁ := mem_pull.1 hJ
    have h₂ := mem_pull.1 hJ'
    refine (gm_pull_g (lbPow L n) f (𝟙 X') y J J' hJ hJ').trans (Eq.symm ?_)
    refine ((chartPullPowPull L f n).g y _ _ (mem_powChart.2 (mem_pull.2 (mem_powChart.1 h₁)))
      (mem_powChart.2 (mem_pull.2 (mem_powChart.1 h₂)))).trans ?_
    rw [Category.id_comp]
    rfl

theorem exists_affine_locus : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Flat → ∀ (X : Scheme.{0}) (q : X ⟶ Sp R), QuasiCompact q → QuasiSeparated q → ∀ (L : LB X), L.IsLB → ∀ (x' : ↥(Limits.pullback q (spMap ρ))), (∃ n, 1 ≤ n ∧ ∃ s : (lbPow (L.pull (pullback.fst q (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)) → ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, pullback.fst q (spMap ρ) x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  rintro R R' _ _ ρ hρ X q _ _ L hL x' ⟨n, hn, s, hs, ha⟩
  have H := IsPullback.of_hasPullback q (spMap ρ)
  generalize pullback.snd q (spMap ρ) = q' at H
  have hπ : IsAffineHom (pullback.fst q (spMap ρ)) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback q (spMap ρ)).flip inferInstance
  generalize pullback.fst q (spMap ρ) = π at *
  generalize Limits.pullback q (spMap ρ) = X' at *
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated q
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated π
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := π x') trivial
  obtain ⟨φ, hφ, hxφ⟩ := ha.exists_basicOpen_le (V := π ⁻¹ᵁ U) ⟨x', hx⟩ hs
  obtain ⟨k, hk, t, ht⟩ := exists_nonzeroLocus_eq_basicOpen (LB.isLB_pull hL π) s φ
  obtain ⟨α, _, W, J, hWa, hW, hc⟩ : ∃ (α : Type) (_ : Fintype α) (W : α → X.Opens) (J : α → PUnit → L.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ powChart L (J a)) ∧ ∀ y : X, ∃ a, y ∈ W a :=
    exists_finite_affine_refinement (isLB_lbPow hL 0)
  have le : ∀ a, π ⁻¹ᵁ W a ≤ powChart (L.pull π) (fun _ _ => J a PUnit.unit) := fun a y hy =>
    mem_powChart.2 (mem_pull.2 (mem_powChart.1 (hW a hy)))
  choose m hm using fun a => exists_pow_mem π (hWa a) U (resG X' (le a) (powFn t _)) fun y hy => by
    have hy₁ : y ∈ π ⁻¹ᵁ W a := X'.basicOpen_le _ hy
    have h := (LBGerm.isUnit_gs_iff (𝟙 X') y _ hy₁ _).2 hy
    exact hφ (ht.le ((mem_nonzeroLocus_iff_powFn t (le a hy₁)).2
      ((congrArg IsUnit (gs_res (𝟙 X') y (le a) hy₁ _)).mp h)))
  let K := Finset.univ.sup m + 1
  have hK : 1 ≤ K := Nat.le_add_left _ _
  obtain ⟨u, hxu, hu⟩ := exists_sec_mem ρ hρ q π q' H (lbPow L (n * k * K)) (isLB_lbPow hL _) W J hWa hW hc
    (fun a => vanIdeal (W a) U) (chartSec (chartPullPullPow L π _) (secPow t K)) (fun a => by
      have e : rs X' (le_pull (lbPow L (n * k * K)) π (hW a))
          ((chartSec (chartPullPullPow L π _) (secPow t K)).f fun _ => J a) = resG X' (le a) (powFn t _) ^ K :=
        fn_ext fun y hy => by
          refine (gs_res (𝟙 X') y _ hy _).trans ((gs_chartSec _ _ (𝟙 X') y _
            (le_pull (lbPow L (n * k * K)) π (hW a) hy)).trans ?_)
          rw [Category.comp_id, LBGerm.gs_pow (𝟙 X') y _ hy, gs_res (𝟙 X') y _ hy]
          exact LBGerm.gs_pow (𝟙 X') y _ (le a hy) _ _
      rw [e]
      exact Ideal.pow_mem_of_pow_mem _ (hm a) ((Finset.le_sup (f := m) (Finset.mem_univ a)).trans (Nat.le_succ _)))
    x' (by
      rw [nonzeroLocus_chartSec_id (chartPullPullPow L π _) _ fun y I hI => ⟨fun _ _ => I PUnit.unit PUnit.unit,
        mem_pull.2 (mem_powChart.2 (mem_pull.1 (mem_powChart.1 hI)))⟩, nonzeroLocus_secPow t hK, ht]
      exact hxφ)
  have hle : nonzeroLocus u ≤ U := fun y hy => by
    obtain ⟨a, hya⟩ := hc y
    refine (show X.basicOpen _ ≤ U from hu a) ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hya _).1 ?_)
    exact (congrArg IsUnit (gs_res (𝟙 X) y (hW a) hya _)).mpr ((mem_nonzeroLocus_iff_isUnit u (hW a hya)).1 hy)
  have h := isAffineOpen_nonzeroLocus_inf (isLB_lbPow hL _) u hU
  rw [inf_eq_left.2 hle] at h
  exact ⟨_, Nat.mul_pos (Nat.mul_pos hn hk) hK, u, hxu, h⟩

end GlobalTheory.AmplePoint
