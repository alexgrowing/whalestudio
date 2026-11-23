import Formalism.SharpRestriction.LevelLetterCocycles.TmulMemFilV

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

theorem secIn_zero {a : ZMod n} {e d : ℕ} (cond : (ℕ → ℤ) → (Fin d → O) → Prop) :
    SecIn W a e cond (fun _ => 0) :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun k => by simp⟩

theorem secIn_add {a : ZMod n} {e d : ℕ} {cond : (ℕ → ℤ) → (Fin d → O) → Prop} {F F' : Fin d → W.EE}
    (h : SecIn W a e cond F) (h' : SecIn W a e cond F') : SecIn W a e cond (F + F') := by
  obtain ⟨I, g, c₀, α, hg, hF⟩ := h
  obtain ⟨I', g', c₀', α', hg', hF'⟩ := h'
  refine ⟨I + I', Fin.append g g', Fin.append c₀ c₀', Fin.append α α', fun i => ?_, fun k => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; exact hg i
    · simp only [Fin.append_right]; exact hg' i
  · rw [Pi.add_apply, hF k, hF' k, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem inFr_mulA {a : ZMod n} {num den : LetA O n} {f : W.EE} (h : InFr W a num den f) {c : LetA O n}
    (hc : c ∈ W.AΔ) : InFr W a num den (algebraMap (LetA O n) W.EE c * f) := by
  obtain ⟨u, hu, hf⟩ := h
  refine ⟨c * u, W.AΔ.mul_mem hc hu, ?_⟩
  rw [mul_left_comm, hf, ← map_mul]
  congr 1; ring

theorem inFr_add {a : ZMod n} {num den : LetA O n} {f f' : W.EE} (h : InFr W a num den f)
    (h' : InFr W a num den f') : InFr W a num den (f + f') := by
  obtain ⟨u, hu, hf⟩ := h
  obtain ⟨u', hu', hf'⟩ := h'
  refine ⟨u + u', W.AΔ.add_mem hu hu', ?_⟩
  rw [mul_add, hf, hf', ← map_add]
  congr 1; ring

theorem inFr_sub {a : ZMod n} {num den : LetA O n} {f f' : W.EE} (h : InFr W a num den f)
    (h' : InFr W a num den f') : InFr W a num den (f - f') := by
  obtain ⟨u, hu, hf⟩ := h
  obtain ⟨u', hu', hf'⟩ := h'
  refine ⟨u - u', W.AΔ.sub_mem hu hu', ?_⟩
  rw [mul_sub, hf, hf', ← map_sub]
  congr 1; ring

theorem inFr_zero {a : ZMod n} {num den : LetA O n} : InFr W a num den 0 :=
  ⟨0, W.AΔ.zero_mem, by simp⟩

theorem inFr_sum {a : ZMod n} {num den : LetA O n} {ι : Type} (s : Finset ι) (F : ι → W.EE)
    (h : ∀ j ∈ s, InFr W a num den (F j)) : InFr W a num den (∑ j ∈ s, F j) := by
  induction s using Finset.induction_on with
  | empty => simpa using inFr_zero W
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact inFr_add W (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem secIn_mulA {a : ZMod n} {e d : ℕ} {cond : (ℕ → ℤ) → (Fin d → O) → Prop} {F : Fin d → W.EE}
    (h : SecIn W a e cond F) {c : LetA O n} (hc : c ∈ W.AΔ) :
    SecIn W a e cond (fun k => algebraMap (LetA O n) W.EE c * F k) := by
  obtain ⟨I, g, c₀, α, hg, hF⟩ := h
  refine ⟨I, fun i => algebraMap (LetA O n) W.EE c * g i, c₀, α, fun i => ⟨inFr_mulA W (hg i).1 hc, (hg i).2⟩,
    fun k => ?_⟩
  show algebraMap (LetA O n) W.EE c * F k = _
  rw [hF k, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dvO_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + 1) b c₀ = Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V) (dvO W T e b c₀) := by
  unfold dvO dv
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, pow_succ', Module.End.mul_apply]

theorem dvO_add (T : LocLat G Qp LL O) (e s : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + s) b c₀ = ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ s) (dvO W T e b c₀) := by
  induction s with
  | zero => simp
  | succ s ih => rw [← add_assoc, dvO_succ, ih, pow_succ', Module.End.mul_apply]

theorem filS_succ (T : LocLat G Qp LL O) (a : ZMod n) (t : ℕ) (u : ℤ) :
    FilS W T (a + 1) (t + 1) u = (FilS W T a t u).map (Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) := by
  unfold FilS
  rw [show a + 1 - ((t + 1 : ℕ) : ZMod n) = a - (t : ZMod n) by push_cast; ring, ← Submodule.map_comp]
  congr 1
  rw [pow_succ', Module.End.mul_eq_comp]

variable [IsDomain O]

theorem secIn_transport (T : LocLat G Qp LL O) (a : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (H : ℕ) {v : LetA O n} (hv : v ∈ W.AΔ) (hπ : W.π₀ ∈ W.AΔ)
    (hlow : ∀ c₀ : Fin d → O, dvO W T (e + 1) b c₀ ∈ FilS W T (a + 1) 0 (-(H : ℤ))) (F : Fin d → W.EE)
    (hF : SecIn W a e (condNN W T a e b) F) :
    SecIn W (a + 1) (e + 1) (condNN W T (a + 1) (e + 1) b)
      (fun k => algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (F k)) := by
  obtain ⟨I, g, c₀, α, hg, hFe⟩ := hF
  refine ⟨I, fun i => algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (g i), c₀,
    fun i s => if s = 0 then (H : ℤ) else α i (s - 1), fun i => ⟨?_, ?_⟩, fun k => ?_⟩
  · obtain ⟨u, hu, hgu⟩ := (hg i).1
    refine ⟨v * W.φA u, W.AΔ.mul_mem hv (Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ hu), ?_⟩
    have hl : W.φA (letE a : LetA O n) = letE (a + 1) := by
      have := φA_letE W (a + 1); rwa [show a + 1 - 1 = a by ring] at this
    have h1 := congrArg W.φE hgu
    rw [map_mul, φE_alg, φE_alg, map_mul W.φA, map_mul W.φA, hl] at h1
    have hnum : W.φA (∏ s ∈ Finset.range e, ps W s ^ (α i s).toNat) =
        ∏ s ∈ Finset.range e, ps W (s + 1) ^ (α i s).toNat := by
      rw [map_prod]; exact Finset.prod_congr rfl fun s _ => by rw [map_pow, ← ps_succ]
    have hden : W.φA (∏ s ∈ Finset.range e, ps W s ^ (-(α i s)).toNat) =
        ∏ s ∈ Finset.range e, ps W (s + 1) ^ (-(α i s)).toNat := by
      rw [map_prod]; exact Finset.prod_congr rfl fun s _ => by rw [map_pow, ← ps_succ]
    rw [hnum, hden] at h1
    show algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range (e + 1), ps W s ^
        (-(if s = 0 then (H : ℤ) else α i (s - 1))).toNat) *
        (algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (g i)) =
      algebraMap (LetA O n) W.EE ((letE (a + 1) * ∏ s ∈ Finset.range (e + 1), ps W s ^
        (if s = 0 then (H : ℤ) else α i (s - 1)).toNat) * (v * W.φA u))
    rw [Finset.prod_range_succ', Finset.prod_range_succ']
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Int.toNat_natCast,
      Int.toNat_eq_zero.2 (by omega : -(H : ℤ) ≤ 0), pow_zero, mul_one]
    rw [mul_left_comm, h1]
    simp only [map_mul]
    ring
  · intro s hs
    rcases s with _ | t
    · beta_reduce
      simp only [↓reduceIte]
      exact hlow (c₀ i)
    · beta_reduce
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [filS_succ, dvO_succ]
      exact Submodule.mem_map_of_mem ((hg i).2 t (by omega))
  · show algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (F k) = _
    rw [hFe k, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul W.φE, AlgHom.commutes]
    ring

end Formalism.MainNotions.UnusedSlot80.LevC
