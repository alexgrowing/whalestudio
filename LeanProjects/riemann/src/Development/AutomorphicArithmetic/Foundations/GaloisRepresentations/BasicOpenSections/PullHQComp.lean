import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private noncomputable def frPow {S : Scheme.{0}} (Fr : S ⟶ S) : ℕ → (S ⟶ S)
  | 0 => 𝟙 S
  | m + 1 => frPow Fr m ≫ Fr

private theorem frPow_bS {S B : Scheme.{0}} (Fr : S ⟶ S) (bS : S ⟶ B) (h : Fr ≫ bS = bS) (m : ℕ) :
    frPow Fr m ≫ bS = bS := by
  induction m with
  | zero => simp [frPow]
  | succ m ih => simp only [frPow, Category.assoc, h, ih]

private theorem frPow_twist {S Y : Scheme.{0}} (Fr : S ⟶ S) (s : S ⟶ Y) {Ω : Type} [Field Ω] (φ : Ω →+* Ω)
    (h : ∀ x : gp Ω ⟶ S, x ≫ Fr ≫ s = twist φ Y (x ≫ s)) (m : ℕ) (u : gp Ω ⟶ S) :
    u ≫ frPow Fr m ≫ s = (twist φ Y)^[m] (u ≫ s) := by
  induction m with
  | zero => simp [frPow]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ← ih, ← Category.assoc u (frPow Fr m) s, ← h]
    simp [frPow]

private theorem pullHQ_comp' (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = (pullHQ l f n i).comp (pullHQ l g n i) := by
  unfold pullHQ
  rw [pullHl_comp, LinearMap.baseChange_comp]

private theorem pullHQ_pow (l : ℕ) [Fact l.Prime] {S : Scheme.{0}} (Fr : S ⟶ S) (k i : ℤ) (m : ℕ) :
    pullHQ l (sch.map (frPow Fr m)) k i =
      (pullHQ l (sch.map Fr) k i : Module.End ℚ_[l] (HQ l (sch.obj S) k i)) ^ m := by
  induction m with
  | zero =>
    simp only [frPow, CategoryTheory.Functor.map_id, pow_zero]
    unfold pullHQ
    rw [pullHl_id, LinearMap.baseChange_id]
    rfl
  | succ m ih =>
    rw [pow_succ, ← ih]
    simp only [frPow, Functor.map_comp]
    rw [pullHQ_comp']
    rfl

theorem UpperTheory.Gal.Mod.esPt :
    CycAll → ESPt := by
  intro hC l _ p f n hp Y π T w hone hpt hdense hπ S B s bS _ _ Fr hl hD hinj hFrB hFrTw c v hpb hf hb hw k i
  have hCE : TranscendenceTraces.CorrEqQ := TranscendenceTraces.all_holds.2.2.2.2.2.2.2.1
  let c' : Fin (n + 1) → TranscendenceTraces.Corr S S := fun j =>
    ⟨(c j).Z, (c j).p, (c j).f ≫ frPow Fr (n - j), (c j).w, (c j).fin, (c j).wt⟩
  have hop : ∀ j : Fin (n + 1), (c' j).opQ l k i = (c j).opQ l k i *
      (pullHQ l (sch.map Fr) k i : Module.End ℚ_[l] (HQ l (sch.obj S) k i)) ^ (n - (j : ℕ)) := by
    intro j
    have e : pullHQ l (sch.map ((c j).f ≫ frPow Fr (n - (j : ℕ)))) k i =
        (pullHQ l (sch.map (c j).f) k i).comp
          ((pullHQ l (sch.map Fr) k i : Module.End ℚ_[l] (HQ l (sch.obj S) k i)) ^ (n - (j : ℕ))) := by
      rw [Functor.map_comp, pullHQ_comp', pullHQ_pow]
    apply LinearMap.ext
    intro x
    show TranscendenceTraces.trHQ l (c j).p (c j).w k i (pullHQ l (sch.map ((c j).f ≫ frPow Fr (n - (j : ℕ)))) k i x) = _
    rw [e]
    rfl
  have hbase : ∀ j : Fin (n + 1), (c' j).f ≫ bS = (c' j).p ≫ bS := by
    intro j
    show ((c j).f ≫ frPow Fr (n - (j : ℕ))) ≫ bS = (c j).p ≫ bS
    rw [Category.assoc, frPow_bS Fr bS hFrB, hb j]
  have key := hCE l k i bS bS (Fin (n + 1)) c' (fun j => co (p ^ f) j) hbase hl _ hD (by
    intro Ω _ _ x y hx
    have hgen : crystallineComparison.GenPt π (pt (x ≫ s)) := by
      have e : pt (x ≫ s) = s (pt x) := rfl
      rw [e]
      exact hx
    obtain ⟨φ, hφ, hcyc⟩ := hC p f n hp Y π T w hone hpt hdense hπ Ω (x ≫ s) hgen
    have hit := frPow_twist Fr s φ (hFrTw Ω φ hφ)
    by_cases hy : y ≫ bS = x ≫ bS
    · rw [← hcyc (y ≫ s)]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      show ∑ᶠ z ∈ {z : gp Ω ⟶ (c j).Z | z ≫ (c j).p = x ∧ z ≫ (c j).f ≫ frPow Fr (n - (j : ℕ)) = y}, (c j).w Ω z = _
      refine finsum_mem_eq_of_bijOn (fun z => z ≫ v j) ⟨?_, ?_, ?_⟩ ?_
      · rintro z ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · show (z ≫ v j) ≫ (T j).p = x ≫ s
          rw [Category.assoc, (hpb j).w, ← Category.assoc, h1]
        · show (twist φ Y)^[n - (j : ℕ)] ((z ≫ v j) ≫ (T j).r) = y ≫ s
          rw [Category.assoc, ← hf j, ← Category.assoc, ← hit, ← h2]
          simp
      · intro z h z' h' e
        exact (hpb j).hom_ext e (h.1.trans h'.1.symm)
      · rintro t ⟨h1, h2⟩
        obtain ⟨L, hL1, hL2⟩ : ∃ L, L ≫ v j = t ∧ L ≫ (c j).p = x :=
          ⟨(hpb j).lift t x h1, (hpb j).lift_fst _ _ _, (hpb j).lift_snd _ _ _⟩
        refine ⟨L, ⟨hL2, ?_⟩, hL1⟩
        apply hinj Ω
        · have e : ((L ≫ (c j).f) ≫ frPow Fr (n - (j : ℕ))) ≫ s = y ≫ s := by
            rw [Category.assoc, hit, Category.assoc, hf j, ← Category.assoc, hL1]
            exact h2
          simpa only [Category.assoc] using e
        · simp only [Category.assoc]
          rw [frPow_bS Fr bS hFrB, hb j, ← Category.assoc, hL2, hy]
      · intro z _
        rw [hw j]
        rfl
    · refine Finset.sum_eq_zero fun j _ => ?_
      have e : {z : gp Ω ⟶ (c' j).Z | z ≫ (c' j).p = x ∧ z ≫ (c' j).f = y} = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2⟩
        apply hy
        rw [← h2, ← h1]
        exact (Category.assoc _ _ _).trans ((congrArg (z ≫ ·) (hbase j)).trans (Category.assoc _ _ _).symm)
      show _ * ∑ᶠ z ∈ {z : gp Ω ⟶ (c' j).Z | z ≫ (c' j).p = x ∧ z ≫ (c' j).f = y}, (c' j).w Ω z = 0
      rw [e]
      simp)
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) key
  rw [hop j]
