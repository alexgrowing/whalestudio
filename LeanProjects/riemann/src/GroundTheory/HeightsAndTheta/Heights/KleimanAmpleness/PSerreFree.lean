import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section FreeGraded

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']

omit [IsScalarTower S (Poly S N) M] in

theorem smul_mem_of_mem_polyGraded (𝓜 : GradedPMod S N M) {a c : ℤ} {p : Poly S N} {m : M}
    (hp : p ∈ (polyGraded S N).piece a) (hm : m ∈ 𝓜.piece c) : p • m ∈ 𝓜.piece (c + a) := by
  change p ∈ weightedHomogeneousSubmodule S (fun _ => (1 : ℤ)) a at hp
  rw [mem_weightedHomogeneousSubmodule] at hp
  rcases le_or_gt 0 a with ha | ha
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    refine 𝓜.smul_mem n c p m ?_ hm
    intro μ hμ
    have h := hp hμ
    simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one,
      nsmul_eq_mul] at h ⊢
    exact_mod_cast h
  · have hp0 : p = 0 := by
      by_contra hne
      obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.mp hne
      have h := hp hμ
      simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, mul_one] at h
      have : (0 : ℤ) ≤ ∑ i ∈ μ.support, (μ i : ℤ) := Finset.sum_nonneg fun i _ => Int.natCast_nonneg _
      omega
    rw [hp0, zero_smul]
    exact zero_mem _

theorem locMap_locResS (f : M →ₗ[Poly S N] M') (I J : StdCell N) (h : I.1 ⊆ J.1)
    (x : LocMod S N M I.1) :
    (locMap f J.1).restrictScalars S (locResS I J h x) =
      locResS I J h ((locMap f I.1).restrictScalars S x) := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    change locMap f J.1 (locRes h _) = locRes h (locMap f I.1 _)
    rw [locRes_mk, locMap_mk, locMap_mk, locRes_mk]

theorem locMap_mem_degLoc {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : M →ₗ[Poly S N] M')
    (t : ℤ) (hf : ∀ (a : ℤ) (m : M), m ∈ 𝓜.piece a → f m ∈ 𝓜'.piece (a + t)) {c c' : ℤ}
    (hc : c' = c + t) (I : StdCell N) (x : LocMod S N M I.1) (hx : x ∈ degLoc 𝓜 c I) :
    (locMap f I.1).restrictScalars S x ∈ degLoc 𝓜' c' I := by
  refine Submodule.span_induction (p := fun x _ => (locMap f I.1).restrictScalars S x ∈
    degLoc 𝓜' c' I) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨m, s, a, e, hm, hs, hae, rfl⟩
    refine Submodule.subset_span ⟨f m, s, a + t, e, hf a m hm, hs, by omega, ?_⟩
    exact locMap_mk f I.1 m s
  · simp
  · intro x y _ _ hx hy; simpa using add_mem hx hy
  · intro r x _ hx; simpa using Submodule.smul_mem _ r hx

def cohomMapShift {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : M →ₗ[Poly S N] M') (t : ℤ)
    (hf : ∀ (a : ℤ) (m : M), m ∈ 𝓜.piece a → f m ∈ 𝓜'.piece (a + t)) (i : ℕ) {c c' : ℤ}
    (hc : c' = c + t) : cohom 𝓜 i c →ₗ[S] cohom 𝓜' i c' :=
  Cech.mapHdeg (degLoc 𝓜 c) (degLoc 𝓜' c') (fun I => (locMap f I.1).restrictScalars S)
    (locMap_locResS f) (locMap_mem_degLoc f t hf hc) i

variable (𝓜 : GradedPMod S N M) {r : ℕ} (b : Module.Basis (Fin r) (Poly S N) M) (d : Fin r → ℤ)

omit [IsScalarTower S (Poly S N) M] in

theorem coord_mem_piece (hb : ∀ j, b j ∈ 𝓜.piece (d j)) {a : ℤ} {m : M} (hm : m ∈ 𝓜.piece a)
    (j : Fin r) : b.coord j m ∈ (polyGraded S N).piece (a - d j) := by
  classical
  let _ := 𝓜.isInternal.chooseDecomposition
  let _ := (polyGraded S N).isInternal.chooseDecomposition

  have key : ∀ (k : Fin r) (p : Poly S N),
      (DirectSum.decompose 𝓜.piece (p • b k) a : M) =
        (DirectSum.decompose (polyGraded S N).piece p (a - d k) : Poly S N) • b k := by
    intro k p
    induction p using DirectSum.Decomposition.inductionOn (ℳ := (polyGraded S N).piece) with
    | zero => simp
    | @homogeneous e p =>
      have hpk : (p : Poly S N) • b k ∈ 𝓜.piece (d k + e) :=
        smul_mem_of_mem_polyGraded 𝓜 p.2 (hb k)
      by_cases he : d k + e = a
      · subst he
        rw [DirectSum.decompose_of_mem_same _ hpk, show d k + e - d k = e by omega,
          DirectSum.decompose_of_mem_same _ p.2]
      · rw [DirectSum.decompose_of_mem_ne _ hpk he,
          DirectSum.decompose_of_mem_ne _ p.2 (show e ≠ a - d k by omega), zero_smul]
    | add p q hp hq =>
      rw [add_smul, DirectSum.decompose_add, DirectSum.decompose_add, DirectSum.add_apply,
        DirectSum.add_apply, Submodule.coe_add, Submodule.coe_add, add_smul, hp, hq]
  have hsum : m = ∑ k, (DirectSum.decompose (polyGraded S N).piece (b.coord k m) (a - d k) :
      Poly S N) • b k := by
    conv_lhs => rw [← DirectSum.decompose_of_mem_same 𝓜.piece hm, ← b.sum_repr m]
    rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun k _ => key k _
  have hj : b.coord j m =
      (DirectSum.decompose (polyGraded S N).piece (b.coord j m) (a - d j) : Poly S N) := by
    conv_lhs => rw [hsum]
    rw [Module.Basis.coord_apply, ← Module.Basis.equivFun_symm_apply, ← Module.Basis.equivFun_apply,
      LinearEquiv.apply_symm_apply]
  rw [hj]
  exact Submodule.coe_mem _

theorem cohomMapShift_mk {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : M →ₗ[Poly S N] M')
    (t : ℤ) (hf : ∀ (a : ℤ) (m : M), m ∈ 𝓜.piece a → f m ∈ 𝓜'.piece (a + t)) (i : ℕ) {c c' : ℤ}
    (hc : c' = c + t) (z : Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS i) :
    ∃ z' : Cech.cocyDeg (locSys S N M') (degLoc 𝓜' c') locResS i,
      cohomMapShift f t hf i hc (Submodule.Quotient.mk z : cohom 𝓜 i c) =
        (Submodule.Quotient.mk z' : cohom 𝓜' i c') ∧ ∀ I, z'.1 I = locMap f I.1.1 (z.1 I) :=
  ⟨_, rfl, fun _ => rfl⟩

omit [Module S M] [IsScalarTower S (Poly S N) M] in

theorem sum_locMap_basis (I : Finset (Fin (N + 1))) (y : LocMod S N M I) :
    ∑ j, locMap (LinearMap.toSpanSingleton (Poly S N) M (b j)) I (locMap (b.coord j) I y) = y := by
  have h1 : ∀ j, locMap (LinearMap.toSpanSingleton (Poly S N) M (b j)) I (locMap (b.coord j) I y) =
      locMap ((LinearMap.toSpanSingleton (Poly S N) M (b j)).comp (b.coord j)) I y := fun j => by
    simp only [locMap]
    rw [IsLocalizedModule.map_comp' (monos (S := S) I) (LocalizedModule.mkLinearMap (monos (S := S) I) M)
      (LocalizedModule.mkLinearMap (monos (S := S) I) (Poly S N))
      (LocalizedModule.mkLinearMap (monos (S := S) I) M)]
    rfl
  have h2 : ∑ j, (LinearMap.toSpanSingleton (Poly S N) M (b j)).comp (b.coord j) = LinearMap.id := by
    ext m
    simp only [LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply, Module.Basis.coord_apply, LinearMap.id_apply]
    exact b.sum_repr m
  calc ∑ j, locMap (LinearMap.toSpanSingleton (Poly S N) M (b j)) I (locMap (b.coord j) I y)
      = ∑ j, locMap ((LinearMap.toSpanSingleton (Poly S N) M (b j)).comp (b.coord j)) I y :=
        Finset.sum_congr rfl fun j _ => h1 j
    _ = locMap (∑ j, (LinearMap.toSpanSingleton (Poly S N) M (b j)).comp (b.coord j)) I y := by
        simp only [locMap, map_sum]
        exact (LinearMap.sum_apply Finset.univ _ y).symm
    _ = y := by
        rw [h2]
        simp only [locMap, IsLocalizedModule.map_id]
        rfl

variable (hb : ∀ j, b j ∈ 𝓜.piece (d j))
include hb

def freeIncl (i : ℕ) (c : ℤ) (j : Fin r) : cohom (polyGraded S N) i (c - d j) →ₗ[S] cohom 𝓜 i c :=
  cohomMapShift (LinearMap.toSpanSingleton (Poly S N) M (b j)) (d j)
    (fun _ _ hp => by
      rw [LinearMap.toSpanSingleton_apply, add_comm]
      exact smul_mem_of_mem_polyGraded 𝓜 hp (hb j)) i (by ring)

def freeCoord (i : ℕ) (c : ℤ) (j : Fin r) : cohom 𝓜 i c →ₗ[S] cohom (polyGraded S N) i (c - d j) :=
  cohomMapShift (b.coord j) (-d j)
    (fun _ _ hm => by rw [← sub_eq_add_neg]; exact coord_mem_piece 𝓜 b d hb hm j) i (by ring)

theorem sum_freeIncl_freeCoord (i : ℕ) (c : ℤ) (x : cohom 𝓜 i c) :
    ∑ j, freeIncl 𝓜 b d hb i c j (freeCoord 𝓜 b d hb i c j x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    have e : ∀ j, ∃ w : Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS i,
        freeIncl 𝓜 b d hb i c j (freeCoord 𝓜 b d hb i c j (Submodule.Quotient.mk z)) =
          (Submodule.Quotient.mk w : cohom 𝓜 i c) ∧
        ∀ I, w.1 I = locMap (LinearMap.toSpanSingleton (Poly S N) M (b j)) I.1.1
          (locMap (b.coord j) I.1.1 (z.1 I)) := by
      intro j
      obtain ⟨z1, h1, h1'⟩ := cohomMapShift_mk (𝓜 := 𝓜) (𝓜' := polyGraded S N) (b.coord j) (-d j)
        (fun _ _ hm => by rw [← sub_eq_add_neg]; exact coord_mem_piece 𝓜 b d hb hm j) i
        (show c - d j = c + -d j by ring) z
      obtain ⟨z2, h2, h2'⟩ := cohomMapShift_mk (𝓜 := polyGraded S N) (𝓜' := 𝓜)
        (LinearMap.toSpanSingleton (Poly S N) M (b j)) (d j)
        (fun _ _ hp => by
          rw [LinearMap.toSpanSingleton_apply, add_comm]
          exact smul_mem_of_mem_polyGraded 𝓜 hp (hb j)) i (show c = c - d j + d j by ring) z1
      refine ⟨z2, ?_, fun I => by rw [h2', h1']⟩
      change cohomMapShift _ _ _ i _ (cohomMapShift _ _ _ i _ _) = _
      rw [h1, h2]
    choose w hw hw' using e
    have hz : ∑ j, w j = z := by
      apply Subtype.ext
      funext I
      rw [Submodule.coe_sum, Finset.sum_apply]
      simp only [hw']
      exact sum_locMap_basis b I.1.1 (z.1 I)
    refine (Finset.sum_congr rfl fun j _ => hw j).trans ?_
    exact (map_sum (Submodule.mkQ _) w Finset.univ).symm.trans (congrArg _ hz)

omit [IsScalarTower S (Poly S N) M] in

theorem smul_basis_mem (c : ℤ) (j : Fin r) (p : (polyGraded S N).piece (c - d j)) :
    (p : Poly S N) • b j ∈ 𝓜.piece c := by
  have h := smul_mem_of_mem_polyGraded 𝓜 p.2 (hb j)
  rwa [show d j + (c - d j) = c by ring] at h

theorem freeInclusion_toH0 (c : ℤ) (j : Fin r) (p : (polyGraded S N).piece (c - d j)) :
    freeIncl 𝓜 b d hb 0 c j (toH0 (polyGraded S N) (c - d j) p) =
      toH0 𝓜 c ⟨(p : Poly S N) • b j, smul_basis_mem 𝓜 b d hb c j p⟩ := by
  obtain ⟨w, hw, hw'⟩ := cohomMapShift_mk (𝓜 := polyGraded S N) (𝓜' := 𝓜)
    (LinearMap.toSpanSingleton (Poly S N) M (b j)) (d j)
    (fun _ _ hp => by
      rw [LinearMap.toSpanSingleton_apply, add_comm]
      exact smul_mem_of_mem_polyGraded 𝓜 hp (hb j)) 0 (show c = c - d j + d j by ring)
    ⟨constCochain (p : Poly S N), constCochain_mem _ _ _ p.2⟩
  refine hw.trans ?_
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun I => (hw' I).trans (locMap_mk _ _ _ _)))

theorem freeCoordinate_toH0 (c : ℤ) (j : Fin r) (m : 𝓜.piece c) :
    freeCoord 𝓜 b d hb 0 c j (toH0 𝓜 c m) =
      toH0 (polyGraded S N) (c - d j) ⟨b.coord j m, coord_mem_piece 𝓜 b d hb m.2 j⟩ := by
  obtain ⟨w, hw, hw'⟩ := cohomMapShift_mk (𝓜 := 𝓜) (𝓜' := polyGraded S N) (b.coord j) (-d j)
    (fun _ _ hm => by rw [← sub_eq_add_neg]; exact coord_mem_piece 𝓜 b d hb hm j) 0
    (show c - d j = c + -d j by ring) ⟨constCochain (m : M), constCochain_mem _ _ _ m.2⟩
  refine hw.trans ?_
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun I => (hw' I).trans (locMap_mk _ _ _ _)))

end FreeGraded

theorem SerreFree.proof (hP : SerrePoly.Statement.{u}) : SerreFree.Statement.{u, v} := by
  intro S _ _ N M _ _ _ _ 𝓜 r b d hb
  obtain ⟨hfin, hpos⟩ := hP S N
  refine ⟨fun i c => ?_, fun c hc => ⟨fun i hi => ?_, ?_, ?_⟩⟩
  · have : ∀ j, Module.Finite S (cohom (polyGraded S N) i (c - d j)) := fun j => hfin i _
    let Φ : ((j : Fin r) → cohom (polyGraded S N) i (c - d j)) →ₗ[S] cohom 𝓜 i c :=
      ∑ j, (freeIncl 𝓜 b d hb i c j).comp (LinearMap.proj j)
    refine Module.Finite.of_surjective Φ fun x => ⟨fun j => freeCoord 𝓜 b d hb i c j x, ?_⟩
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    exact sum_freeIncl_freeCoord 𝓜 b d hb i c x
  · refine ⟨fun x y => ?_⟩
    rw [← sum_freeIncl_freeCoord 𝓜 b d hb i c x, ← sum_freeIncl_freeCoord 𝓜 b d hb i c y]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : Subsingleton (cohom (polyGraded S N) i (c - d j)) :=
      (hpos (c - d j) (by linarith [hc j])).1 i hi
    rw [Subsingleton.elim (freeCoord 𝓜 b d hb i c j x) (freeCoord 𝓜 b d hb i c j y)]
  · rw [injective_iff_map_eq_zero]
    intro m hm
    apply Subtype.ext
    rw [Submodule.coe_zero, ← b.sum_repr m]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h0 := freeCoordinate_toH0 𝓜 b d hb c j m
    rw [hm, map_zero] at h0
    have hinj := (hpos (c - d j) (by linarith [hc j])).2.1
    have : (⟨b.coord j m, coord_mem_piece 𝓜 b d hb m.2 j⟩ : (polyGraded S N).piece (c - d j)) = 0 :=
      hinj (h0.symm.trans (map_zero _).symm)
    rw [← Module.Basis.coord_apply, show b.coord j m = 0 from congrArg Subtype.val this, zero_smul]
  · intro y
    have hsurj := fun j => (hpos (c - d j) (by linarith [hc j])).2.2
    choose p hp using fun j => hsurj j (freeCoord 𝓜 b d hb 0 c j y)
    refine ⟨∑ j, ⟨(p j : Poly S N) • b j, smul_basis_mem 𝓜 b d hb c j (p j)⟩, ?_⟩
    rw [map_sum, ← sum_freeIncl_freeCoord 𝓜 b d hb 0 c y]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hp j, freeInclusion_toH0]

end

end GroundTheory.Heights₂.Heights.Kleiman
