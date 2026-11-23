import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OmMul
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]

private theorem mapDR_smul' (b : K) (w : DR ℂ K) :
    mapDR ℂ K L (b • w) = algebraMap K L b • mapDR ℂ K L w := by
  rw [map_smul]
  exact (algebraMap_smul L b (mapDR ℂ K L w)).symm

private theorem mapDR_iMulti (q : ℕ) (v : Fin q → K) :
    mapDR ℂ K L (ExteriorAlgebra.ιMulti K q fun j => D ℂ K (v j)) =
      ExteriorAlgebra.ιMulti L q fun j => D ℂ L (algebraMap K L (v j)) := by
  simp only [ExteriorAlgebra.ιMulti_apply]
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext j
  simp [mapDR, map1, ExteriorAlgebra.lift_ι_apply]

private theorem mapDR_om {B : Subalgebra ℂ K} {B' : Subalgebra ℂ L}
    (h : ∀ b ∈ B, algebraMap K L b ∈ B') (q : ℕ) {w : DR ℂ K} (hw : w ∈ omB ℂ K B q) :
    mapDR ℂ K L w ∈ omB ℂ L B' q := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hy
    rw [mapDR_smul', mapDR_iMulti]
    exact Submodule.subset_span ⟨_, h b hb, _, fun j => h _ (hv j), rfl⟩
  | zero => simp
  | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
  | smul c u _ hu =>
    have e := ((mapDR ℂ K L).toLinearMap.restrictScalars ℂ).map_smul c u
    have e' : mapDR ℂ K L (c • u) = c • mapDR ℂ K L u := e
    rw [e']
    exact Submodule.smul_mem _ _ hu
end

section
variable {L : Type} [Field L] [Algebra ℂ L]

private theorem iMulti_mul (p q : ℕ) (u : Fin p → L) (v : Fin q → L) :
    (ExteriorAlgebra.ιMulti L p fun j => D ℂ L (u j)) * (ExteriorAlgebra.ιMulti L q fun j => D ℂ L (v j)) =
      ExteriorAlgebra.ιMulti L (p + q) fun j => D ℂ L (Fin.append u v j) := by
  simp only [ExteriorAlgebra.ιMulti_apply]
  rw [← List.prod_append, ← List.ofFn_fin_append]
  congr 2
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

private theorem om_mul (B : Subalgebra ℂ L) {p q : ℕ} {u w : DR ℂ L} (hu : u ∈ omB ℂ L B p)
    (hw : w ∈ omB ℂ L B q) : u * w ∈ omB ℂ L B (p + q) :=
  _root_.UpperTheory.Reformulated.B.Qe48.om_mul B hu hw
end

section
variable {K K' : Type} [Field K] [Field K'] [Algebra ℂ K] [Algebra ℂ K'] (j2 : K →ₐ[ℂ] K')

private theorem pullback_kahler_smul_alg (b : K) (w : DR ℂ K) : pr2L j2 (b • w) = j2 b • pr2L j2 w := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_smul' (L := K') b w

private theorem pullback_kahler_omegaBounded {B : Subalgebra ℂ K} {B' : Subalgebra ℂ K'} (h : ∀ b ∈ B, j2 b ∈ B') (q : ℕ)
    {w : DR ℂ K} (hw : w ∈ omB ℂ K B q) : pr2L j2 w ∈ omB ℂ K' B' q := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_om (L := K') h q hw
end

private theorem wd_map {ι E E' : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (f : E →ₗ[ℂ] E') (w : ι → Module.End ℂ E) (w' : ι → Module.End ℂ E')
    (h : ∀ i m, f (w i m) = w' i (f m)) (c : Finset ι → E) :
    wd w' (fun s => f (c s)) = fun s => f (wd w c s) := by
  funext t
  simp [wd, h, map_sum]

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private theorem gS_tmul (p q : K) : gS j2 (p ⊗ₜ q) = algebraMap K K' p * j2 q := by
  simp [gS]

private theorem gY_tmul (w' w : DR ℂ K) : gY j2 (w' ⊗ₜ w) = mapDR ℂ K K' w' * pr2L j2 w := by
  simp [gY]

private theorem gS_X (a : ℕ) (i : Fin (d + 1)) :
    gS j2 (((sysZ K x a).X i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = (((sysY x j2 d).X i : K'ˣ) : K') := by
  simp [sysZ, sysY, gS, IsScalarTower.algebraMap_apply F K K']

private theorem gS_Y (a : ℕ) (i : Fin (d + 1)) :
    gS j2 (((sysZ K x a).Y i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = (((sysY x j2 d).Y i : K'ˣ) : K') := by
  simp [sysZ, sysY, gS]

private theorem gY_act (s : K ⊗[ℂ] K) (m : DR ℂ K ⊗[ℂ] DR ℂ K) :
    gY j2 (actZ K s m) = gS j2 s • gY j2 m := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, add_smul, hs, ht]
  | tmul p q =>
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, smul_add, hu, hv]
    | tmul w' w =>
      have e : actZ K (p ⊗ₜ q) (w' ⊗ₜ w) = (p • w') ⊗ₜ[ℂ] (q • w) := by
        simp [actZ, Module.endTensorEndAlgHom_apply]
      rw [e, gY_tmul, gY_tmul, mapDR_smul', pullback_kahler_smul_alg, gS_tmul, smul_mul_smul_comm]

private theorem gS_prod {κ : Type} [LinearOrder κ] (a : ℕ) (n : κ → ℕ × ℕ) (i j : Fin (d + 1)) (t : Finset κ) :
    gS j2 ((∏ l ∈ t, (sysZ K x a).u n i j l : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      ((∏ l ∈ t, (sysY x j2 d).u n i j l : K'ˣ) : K') := by
  simp only [Units.coe_prod, map_prod, Sys.u, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, gS_X, gS_Y]

variable {x j2}

private theorem gY_M (hb : ∀ I, ∀ b ∈ rB ℂ K (xv x) I, algebraMap K K' b ∈ rB ℂ K' (xv x) I ∧ j2 b ∈ R2 (xv x) j2 I)
    {a : ℕ} (ha : a ≤ d) (I J : Finset (Fin (d + 1))) {m : DR ℂ K ⊗[ℂ] DR ℂ K}
    (hm : m ∈ (sysZ K x a).M I J) : gY j2 m ∈ (sysY x j2 d).M I J := by
  have key : (sysZ K x a).M I J ≤ ((sysY x j2 d).M I J).comap (gY j2) := by
    refine Submodule.map₂_le.2 fun u hu w hw => ?_
    show gY j2 (u ⊗ₜ w) ∈ omB ℂ K' (RY (xv x) j2 I J) d
    rw [gY_tmul]
    have e : d - a + a = d := by omega
    have h := om_mul (RY (xv x) j2 I J)
      (mapDR_om (L := K') (B' := RY (xv x) j2 I J)
        (fun b h => (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J) (hb I b h).1) _ hu)
      (pullback_kahler_omegaBounded j2 (B' := RY (xv x) j2 I J)
        (fun b h => (le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J) (hb J b h).2) _ hw)
    rwa [e] at h
  exact key hm

private theorem gY_mix (hb : ∀ I, ∀ b ∈ rB ℂ K (xv x) I, algebraMap K K' b ∈ rB ℂ K' (xv x) I ∧ j2 b ∈ R2 (xv x) j2 I)
    {a : ℕ} (ha : a ≤ d) (s : Finset (Two d)) {m : DR ℂ K ⊗[ℂ] DR ℂ K}
    (h : m ∈ mixF (sysZ K x a).M s) : gY j2 m ∈ mixF (sysY x j2 d).M s := by
  unfold mixF at h ⊢
  split_ifs at h ⊢ with hc
  · exact gY_M hb ha _ _ h
  · rw [Submodule.mem_bot] at h ⊢
    simp [h]

private theorem gY_wt {κ : Type} [LinearOrder κ] (a : ℕ) (z : κ → K ⊗[ℂ] K) (t : Two d ⊕ₗ κ)
    (m : DR ℂ K ⊗[ℂ] DR ℂ K) :
    gY j2 ((sysZ K x a).wt z t m) = (sysY x j2 d).wt (fun l => gS j2 (z l)) t (gY j2 m) := by
  unfold Sys.wt
  cases ofLex t with
  | inl i => rfl
  | inr l => exact gY_act j2 (z l) m
end

theorem UpperTheory.Gal.productCup_of_system.gMap_of :
    RYBasic → WdUni → GMap := by
  intro hB _ F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 h0 a ha
  have hb := (hB F K K' d x j2 h0).2.2.2.1
  refine ⟨fun l => ?_, fun s m => gY_act j2 s m, fun I J s hs => ?_, fun N t ht => ?_, ?_⟩
  · simp [Sys.mu, gS_X, gS_Y, map_sub, map_mul]
  · obtain ⟨t, rfl⟩ := hs
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv =>
      rw [map_add, map_add]
      exact add_mem hu hv
    | tmul p q =>
      have e : gS j2 (Algebra.TensorProduct.map (rB ℂ K (xv x) I).val (rB ℂ K (xv x) J).val (p ⊗ₜ q)) =
          algebraMap K K' p * j2 q := by
        rw [Algebra.TensorProduct.map_tmul, gS_tmul]
        rfl
      refine e ▸ (RY (xv x) j2 I J).mul_mem ?_ ?_
      · exact (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J) (hb I _ p.2).1
      · exact (le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J) (hb J _ q.2).2
  · obtain ⟨y, hy, rfl⟩ := ht
    refine ⟨fun s => gY j2 (y s), fun s _ => ?_, wd_map (gY j2) _ _ (fun _ _ => rfl) y⟩
    have h := hy s (Set.mem_univ s)
    change y s ∈ (if (s.card : ℤ) = N - 1 then mixF (sysZ K x a).M s else ⊥) at h
    change gY j2 (y s) ∈ (if (s.card : ℤ) = N - 1 then mixF (sysY x j2 d).M s else ⊥)
    split_ifs at h ⊢ with hc
    · exact gY_mix hb ha s h
    · rw [Submodule.mem_bot] at h ⊢
      simp [h]
  · intro κ _ _ n z N c hc
    obtain ⟨hc1, hc2⟩ := hc
    refine ⟨fun s _ => ?_, ?_⟩
    · have h := hc1 s (Set.mem_univ s)
      change c s ∈ (if (s.card : ℤ) = N then mixF (fun I J => ((sysZ K x a).M I J).map
        ((sysZ K x a).act ((∏ l ∈ rgt s, (sysZ K x a).u n (pk I) (pk J) l : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K))) (lft s) else ⊥) at h
      change gY j2 (c s) ∈ (if (s.card : ℤ) = N then mixF (fun I J => ((sysY x j2 d).M I J).map
        ((sysY x j2 d).act ((∏ l ∈ rgt s, (sysY x j2 d).u n (pk I) (pk J) l : K'ˣ) : K'))) (lft s) else ⊥)
      split_ifs at h ⊢ with hcard
      · unfold mixF at h ⊢
        split_ifs at h ⊢ with hne
        · obtain ⟨m, hm, hmc⟩ := h
          refine ⟨gY j2 m, gY_M hb ha _ _ hm, ?_⟩
          rw [← hmc]
          have e := gY_act j2 ((∏ l ∈ rgt s, (sysZ K x a).u n (pk (lft (lft s))) (pk (rgt (lft s))) l :
            (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) m
          rw [gS_prod x j2 a] at e
          exact e.symm
        · rw [Submodule.mem_bot] at h ⊢
          simp [h]
      · rw [Submodule.mem_bot] at h ⊢
        simp [h]
    · have e := wd_map (gY j2) ((sysZ K x a).wt z) ((sysY x j2 d).wt fun l => gS j2 (z l))
        (fun t m => gY_wt a z t m) c
      have hc2' : wd ((sysZ K x a).wt z) c = 0 := hc2
      change wd ((sysY x j2 d).wt fun l => gS j2 (z l)) (fun s => gY j2 (c s)) = 0
      rw [e, hc2']
      funext s
      simp
