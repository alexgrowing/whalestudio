import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.BumpLat
import Development.WeilBound.ThetaLifts.LatticeBasics.NearUnits
import Development.WeilBound.CoreStatements.LocalThetaKernels.ExistsSmallSubgroups

open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA

noncomputable section

namespace UpperTheory.TP.BA.LamTop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}

private theorem sg_one_smul {M : Type} [AddCommGroup M] [Module (AF F) M] {z : M} (h : At (evFin F v) z) : sg v 1 • z = z := by
  have := h (1 - sg v 1) (by rw [map_sub, map_one, PositivityTheory.ThKH.Iwas.ev_sg, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

private theorem eq_sg {a : AF F} (h : At (evFin F v) a) : a = sg v (evFin F v a) := by
  have := sg_one_smul h
  rw [smul_eq_mul, mul_comm, PositivityTheory.ThKH.Iwas.mul_sg, mul_one] at this
  exact this.symm

private theorem continuous_sg (v : Pl F) : Continuous (sg v : Fv F v → AF F) :=
  (continuous_const.prodMk (continuous_singleFin v) : Continuous fun a => ((0 : Ainf F), singleFin v a))

private theorem oh_sub (v : Pl F) : ∃ (ι : Type) (_ : Fintype ι) (o : ι → 𝓞 E), ∀ z ∈ Oh E v, ∃ t : ι → Fv F v,
    (∀ i, t i ∈ v.adicCompletionIntegers F) ∧ z = ∑ i, sg v (t i) • inclR (F := F) (AF F) (o i : E) := by
  classical
  let bs := RingOfIntegers.basis E
  refine ⟨_, inferInstance, fun i => bs i, fun z hz => ?_⟩
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hO, o, rfl⟩ := hz
    refine ⟨fun i => (bs.repr o i : ℤ) • evFin F v a, fun i => zsmul_mem hO _, ?_⟩
    have e : (o : E) = ∑ i, (bs.repr o i : ℤ) • ((bs i : 𝓞 E) : E) := by
      conv_lhs => rw [← bs.sum_repr o]
      simp
    conv_lhs => rw [e]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    beta_reduce
    have e2 : sg v ((bs.repr o i : ℤ) • evFin F v a) = (bs.repr o i : ℤ) • sg v (evFin F v a) :=
      map_zsmul (PositivityTheory.ThKH.Iwas.sg v) _ _
    rw [map_zsmul, e2, smul_assoc, smul_comm a, ← eq_sg ha]
  | zero => exact ⟨0, fun i => zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨t', ht', rfl⟩ := hy
    refine ⟨t + t', fun i => add_mem (ht i) (ht' i), ?_⟩
    simp [add_smul, Finset.sum_add_distrib]
  | neg x _ hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    refine ⟨-t, fun i => neg_mem (ht i), ?_⟩
    simp [neg_smul, Finset.sum_neg_distrib]

private theorem small_oh (v : Pl F) {ϖ : Fv F v} (h1 : Valued.v ϖ < 1) {V : Set (AE F E)} (hV : V ∈ 𝓝 0) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ z ∈ Oh E v, sg v (ϖ ^ k) • z ∈ V := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  obtain ⟨ι, _, o, ho⟩ := oh_sub (E := E) v
  let J : Fv F v × (ι → v.adicCompletionIntegers F) → AE F E :=
    fun p => ∑ i, sg v (p.1 * p.2 i) • inclR (F := F) (AF F) (o i : E)
  have cJ : Continuous J := continuous_finset_sum _ fun i _ => by
    have c1 : Continuous fun p : Fv F v × (ι → v.adicCompletionIntegers F) => sg v (p.1 * (p.2 i : Fv F v)) :=
      (continuous_sg v).comp (continuous_fst.mul (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)))
    exact c1.smul (continuous_const (y := inclR (F := F) (AF F) (o i : E)))
  have h : ∀ᶠ a : Fv F v in 𝓝 0, ∀ y ∈ (Set.univ : Set (ι → v.adicCompletionIntegers F)), J (a, y) ∈ V :=
    isCompact_univ.eventually_forall_of_forall_eventually fun y _ =>
      (cJ.tendsto' (0, y) 0 (by simp [J])).eventually hV
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((Valued.tendsto_zero_pow_of_v_lt_one h1).eventually h)
  refine ⟨N, fun k hk z hz => ?_⟩
  obtain ⟨t, ht, rfl⟩ := ho z hz
  have e : sg v (ϖ ^ k) • ∑ i, sg v (t i) • inclR (F := F) (AF F) (o i : E) = J (ϖ ^ k, fun i => ⟨t i, ht i⟩) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, PositivityTheory.ThKH.Iwas.mul_sg, PositivityTheory.ThKH.Iwas.ev_sg]
  rw [e]
  exact hN k hk _ trivial

variable (F E) in
private theorem exists_basis : ∃ (ι : Type) (_ : Fintype ι) (e : Module.Basis ι F E) (o : ι → 𝓞 E), ∀ i, e i = o i := by
  have h : ∀ i, ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ (y • Module.finBasis F E i) := fun i =>
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic _)).exists_integral_multiple
  choose y y0 hy using h
  let w : _ → Fˣ := fun i => Units.mk0 (y i : F) (by exact_mod_cast y0 i)
  refine ⟨_, inferInstance, (Module.finBasis F E).unitsSMul w, fun i => ⟨_, hy i⟩, fun i => ?_⟩
  rw [Module.Basis.unitsSMul_apply]
  change ((y i : ℤ) : F) • Module.finBasis F E i = y i • Module.finBasis F E i
  exact Int.cast_smul_eq_zsmul F _ _

private theorem open_oh (v : Pl F) : ∃ V ∈ 𝓝 (0 : AE F E), ∀ z ∈ V, At (evFin F v) z → z ∈ Oh E v := by
  classical
  obtain ⟨ι, _, e, o, he⟩ := exists_basis F E
  let bb := Algebra.TensorProduct.basis (AF F) e
  let cc : AE F E → ι → Fv F v := fun z i => evFin F v (bb.repr z i)
  have hc : Continuous cc := continuous_pi fun i =>
    (PositivityTheory.ThKH.Locrep.continuous_evFin' v).comp (IsModuleTopology.continuous_of_linearMap (bb.coord i))
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  refine ⟨cc ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)),
    (hc.isOpen_preimage _ (isOpen_set_pi Set.finite_univ fun _ _ => hO)).mem_nhds ?_, fun z hz ha => ?_⟩
  · intro i _
    simpa [cc] using zero_mem (v.adicCompletionIntegers F)
  rw [← bb.sum_repr z]
  refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨bb.repr z i, fun u hu => ?_, hz i (Set.mem_univ i), o i, ?_⟩
  · have := congrArg (fun t => bb.repr t i) (ha u hu)
    simpa using this
  · rw [← he]
    simp [bb, inclR]

private theorem ent {ι R : Type} [Finite ι] [TopologicalSpace R] [Zero R] {S : Set (ι → R)} (h : S ∈ 𝓝 0) :
    ∃ V ∈ 𝓝 (0 : R), ∀ q : ι → R, (∀ i, q i ∈ V) → q ∈ S := by
  rw [nhds_pi, Filter.mem_pi] at h
  obtain ⟨I, -, t, ht, hs⟩ := h
  exact ⟨⋂ i, t i, Filter.iInter_mem.2 ht, fun q hq => hs fun i _ => Set.mem_iInter.1 (hq i) i⟩

private theorem frame {X : Spc F E n} {b c : Matrix (Fin n) (Fin n) (AE F E)} (h : IsFr X v b c)
    {a : Matrix (Fin n) (Fin n) (AE F E)} (ha : At (evFin F v) a) (t : AF F) : b * (t • (c * a * b)) * c = t • a := by
  have e : b * (c * a * b) * c = (b * c) * a * (b * c) := by simp only [Matrix.mul_assoc]
  rw [Matrix.mul_smul, Matrix.smul_mul, e, h.bc]
  simp only [eM, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, sg_one_smul ha]

private theorem mk_lam {b c : Matrix (Fin n) (Fin n) (AE F E)} {V : Set (AE F E)}
    (hV : ∀ z ∈ V, At (evFin F v) z → z ∈ Oh E v) {s : Fv F v} (s0 : s ≠ 0) {D : Matrix (Fin n) (Fin n) (AE F E)}
    (hD : At (evFin F v) D) (h : ∀ i j, (sg v s⁻¹ • (c * D * b)) i j ∈ V) :
    ∃ a ∈ abelian₂ (E := E) v b c, D = sg v s • a := by
  have ha : At (evFin F v) (sg v s⁻¹ • D) := fun u hu => by rw [smul_comm, hD u hu, smul_zero]
  refine ⟨sg v s⁻¹ • D, ⟨ha, fun i j => hV _ ?_ fun u hu => ?_⟩, ?_⟩
  · have := h i j
    rwa [← Matrix.smul_mul, ← Matrix.mul_smul] at this
  · have e : u • (c * (sg v s⁻¹ • D) * b) = 0 := by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, ha u hu, Matrix.mul_zero, Matrix.zero_mul]
    exact congrFun (congrFun e i) j
  · rw [smul_smul, PositivityTheory.ThKH.Iwas.mul_sg, PositivityTheory.ThKH.Iwas.ev_sg, mul_inv_cancel₀ s0, sg_one_smul hD]

private theorem cont_of (n : ℕ) : Continuous fun f : Fin n × Fin n → AE F E =>
    (Matrix.of (fun i j => f (i, j)) : Matrix (Fin n) (Fin n) (AE F E)) :=
  continuous_matrix fun i j => continuous_apply (i, j)

private theorem cont_frame (b c : Matrix (Fin n) (Fin n) (AE F E)) : Continuous fun f : Fin n × Fin n → AE F E =>
    (1 + b * Matrix.of (fun i j => f (i, j)) * c : Matrix (Fin n) (Fin n) (AE F E)) := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have c1 := (continuous_const (y := b)).matrix_mul (cont_of (F := F) (E := E) n)
  have c2 := c1.matrix_mul (continuous_const (y := c))
  exact continuous_const.add c2

private theorem cont_sel (n : ℕ) (β : Bool) : Continuous fun f : Bool × Fin n × Fin n → AE F E => fun x : Fin n × Fin n => f (β, x) :=
  continuous_pi fun x => continuous_apply (β, x)

private def Ps (b c : Matrix (Fin n) (Fin n) (AE F E)) (f : Fin n × Fin n → AE F E) : Matrix (Fin n) (Fin n) (AE F E) :=
  1 + b * Matrix.of (fun i j => f (i, j)) * c

private def Pp (b c : Matrix (Fin n) (Fin n) (AE F E)) (f : Bool × Fin n × Fin n → AE F E) :
    Matrix (Fin n) (Fin n) (AE F E) × Matrix (Fin n) (Fin n) (AE F E) :=
  (Ps b c fun x => f (true, x), Ps b c fun x => f (false, x))

private theorem cont_Ps (b c : Matrix (Fin n) (Fin n) (AE F E)) : Continuous (Ps b c) := cont_frame b c

private theorem cont_Pp (b c : Matrix (Fin n) (Fin n) (AE F E)) : Continuous (Pp b c) := by
  have h1 : Continuous fun q : Bool × Fin n × Fin n → AE F E => Ps b c fun x => q (true, x) :=
    (cont_Ps b c).comp (cont_sel n true)
  have h2 : Continuous fun q : Bool × Fin n × Fin n → AE F E => Ps b c fun x => q (false, x) :=
    (cont_Ps b c).comp (cont_sel n false)
  exact h1.prodMk h2

private theorem Ps_zero (b c : Matrix (Fin n) (Fin n) (AE F E)) : Ps b c 0 = 1 := by
  have : Matrix.of (fun i j => (0 : Fin n × Fin n → AE F E) (i, j)) = 0 := rfl
  unfold Ps
  rw [this, Matrix.mul_zero, Matrix.zero_mul, add_zero]

private theorem near_gen {ι R A : Type} [Finite ι] [TopologicalSpace R] [Zero R] [Monoid A] [TopologicalSpace A] {U : Set Aˣ}
    (hU : U ∈ 𝓝 (1 : Aˣ)) {Ψ : (ι → R) → A × A} (c : Continuous Ψ) (h0 : Ψ 0 = (1, 1)) :
    ∃ V ∈ 𝓝 (0 : R), ∀ q : ι → R, (∀ i, q i ∈ V) → ∀ g : Aˣ, g.1 = (Ψ q).1 → (g⁻¹).1 = (Ψ q).2 → g ∈ U :=
  ent ((c.tendsto' 0 (1, 1) h0).eventually (GlobalTheory.ThK.Dbl.Bmp.near_units hU))

private theorem part1 {σ : E →ₐ[F] E} {X : Spc F E n} {b c : Matrix (Fin n) (Fin n) (AE F E)} (hF : IsFr X v b c) {ϖ : Fv F v}
    (ϖ1 : Valued.v ϖ < 1) {U : Set (UA σ X.J)} (hU : U ∈ 𝓝 (1 : UA σ X.J)) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ g : UA σ X.J,
      (∃ a ∈ abelian₂ (E := E) v b c, mat g - 1 = sg v (ϖ ^ k) • a) → (∃ a ∈ abelian₂ (E := E) v b c, mat g⁻¹ - 1 = sg v (ϖ ^ k) • a) → g ∈ U := by
  obtain ⟨U', h1, h2⟩ := (mem_nhds_subtype _ _ _).1 hU
  obtain ⟨V, hV, hq⟩ := near_gen h1 (cont_Pp b c) (Prod.ext (Ps_zero b c) (Ps_zero b c))
  obtain ⟨k₀, hk⟩ := small_oh (E := E) v ϖ1 hV
  refine ⟨k₀, fun k hkk g ⟨a, ha, ea⟩ ⟨a', ha', ea'⟩ => h2 ?_⟩
  let f : Bool × Fin n × Fin n → AE F E := fun x =>
    sg v (ϖ ^ k) • (if x.1 then c * a * b else c * a' * b) x.2.1 x.2.2
  have hf := hq f (fun ⟨β, i, j⟩ => by
    cases β
    · exact hk k hkk _ (ha'.2 i j)
    · exact hk k hkk _ (ha.2 i j))
  refine hf g.1 ?_ ?_
  · have e : Matrix.of (fun i j => f (true, i, j)) = sg v (ϖ ^ k) • (c * a * b) := rfl
    change mat g = 1 + b * Matrix.of (fun i j => f (true, i, j)) * c
    rw [e, frame hF ha.1, ← ea, add_sub_cancel]
  · have e : Matrix.of (fun i j => f (false, i, j)) = sg v (ϖ ^ k) • (c * a' * b) := rfl
    change mat g⁻¹ = 1 + b * Matrix.of (fun i j => f (false, i, j)) * c
    rw [e, frame hF ha'.1, ← ea', add_sub_cancel]

private theorem part2 {σ : E →ₐ[F] E} {X : Spc F E n} (b c : Matrix (Fin n) (Fin n) (AE F E)) {ϖ : Fv F v} (ϖ0 : ϖ ≠ 0) (k : ℕ) :
    ∃ O : Set (UA σ X.J), IsOpen O ∧ 1 ∈ O ∧ ∀ g ∈ UAt σ X (evFin F v), g ∈ O →
        (∃ a ∈ abelian₂ (E := E) v b c, mat g - 1 = sg v (ϖ ^ k) • a) ∧ ∃ a ∈ abelian₂ (E := E) v b c, mat g⁻¹ - 1 = sg v (ϖ ^ k) • a := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have mm : ∀ g h : UA σ X.J, mat (g * h) = mat g * mat h := fun _ _ => rfl
  have m1 : mat (1 : UA σ X.J) = 1 := rfl
  obtain ⟨V, hV, hO⟩ := open_oh (E := E) v
  have s0 : ϖ ^ k ≠ 0 := pow_ne_zero _ ϖ0
  let ψ : Matrix (Fin n) (Fin n) (AE F E) → Matrix (Fin n) (Fin n) (AE F E) := fun M => sg v (ϖ ^ k)⁻¹ • (c * (M - 1) * b)
  have c1 : Continuous fun M : Matrix (Fin n) (Fin n) (AE F E) => c * (M - 1) * b :=
    ((continuous_const (y := c)).matrix_mul (continuous_id.sub continuous_const)).matrix_mul (continuous_const (y := b))
  have cψ : Continuous ψ := c1.const_smul (sg v (ϖ ^ k)⁻¹)
  have cm : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have ci : Continuous fun g : UA σ X.J => mat g⁻¹ := Units.continuous_coe_inv.comp continuous_subtype_val
  have ψ1 : ψ 1 = 0 := by simp [ψ]
  refine ⟨⋂ i, ⋂ j, ((fun g => ψ (mat g) i j) ⁻¹' interior V ∩ (fun g => ψ (mat g⁻¹) i j) ⁻¹' interior V),
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_interior.preimage ((cψ.comp cm).matrix_elem i j)).inter (isOpen_interior.preimage ((cψ.comp ci).matrix_elem i j)),
    ?_, fun g hg hgO => ?_⟩
  · have h0 : (0 : AE F E) ∈ interior V := mem_interior_iff_mem_nhds.2 hV
    refine Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun j => ⟨?_, ?_⟩
    · change ψ (mat (1 : UA σ X.J)) i j ∈ interior V
      rw [m1, ψ1]; exact h0
    · change ψ (mat (1 : UA σ X.J)⁻¹) i j ∈ interior V
      rw [inv_one, m1, ψ1]; exact h0
  have hg' : At (evFin F v) (mat g⁻¹ - 1) := fun u hu => by
    have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
      rw [mul_sub, ← mm, inv_mul_cancel, m1, mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]
  have hi := fun i j => Set.mem_iInter.1 (Set.mem_iInter.1 hgO i) j
  exact ⟨mk_lam hO s0 hg fun i j => interior_subset (hi i j).1,
    mk_lam hO s0 hg' fun i j => interior_subset (hi i j).2⟩

end UpperTheory.TP.BA.LamTop

theorem UpperTheory.mem_nhds_one_of_congruence_latticeOrder :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (X : Spc F E n) (v : Pl F) (b c : Matrix (Fin n) (Fin n) (AE F E)), IsFr X v b c → ∀ ϖ : Fv F v, ϖ ≠ 0 → Valued.v ϖ < 1 →
      (∀ U ∈ 𝓝 (1 : UA σ X.J), ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ g ∈ UAt σ X (evFin F v),
        (∃ a ∈ abelian₂ (E := E) v b c, mat g - 1 = sg v (ϖ ^ k) • a) → (∃ a ∈ abelian₂ (E := E) v b c, mat g⁻¹ - 1 = sg v (ϖ ^ k) • a) → g ∈ U) ∧
      ∀ k : ℕ, ∃ O : Set (UA σ X.J), IsOpen O ∧ 1 ∈ O ∧ ∀ g ∈ UAt σ X (evFin F v), g ∈ O →
        (∃ a ∈ abelian₂ (E := E) v b c, mat g - 1 = sg v (ϖ ^ k) • a) ∧ ∃ a ∈ abelian₂ (E := E) v b c, mat g⁻¹ - 1 = sg v (ϖ ^ k) • a := by
  intro F E _ _ _ _ _ σ n X v b c hF ϖ ϖ0 ϖ1
  refine ⟨fun U hU => ?_, fun k => LamTop.part2 b c ϖ0 k⟩
  obtain ⟨k₀, hk⟩ := LamTop.part1 hF ϖ1 hU
  exact ⟨k₀, fun k hkk g _ => hk k hkk g⟩

end
