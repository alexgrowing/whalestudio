import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceBig
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceBound
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.ResTyp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliAuxiliaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW.SliceClasses

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} {S : Set (Pl E)}

private abbrev eS (r s : ℕ) : Fin s ⊕ Fin r ≃ Fin (r + s) :=
  (Equiv.sumComm (Fin s) (Fin r)).trans (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))

private theorem iota_eq (m : GA E s) : CapRes.iota (eS r s) m = lev (Ad E) r s (1, m) := CapRes.emb₂_swap _ _ _

private theorem eS_inl (i : Fin s) : eS r s (.inl i) = Fin.natAdd r i := Fin.ext (by simp)

private theorem ex_rel (r : ℕ) (u : UC E s) : ∃ u' : UC E (r + s), (uC E s u, uC E (r + s) u') ∈ CapRes.relAlg (eS r s) := by
  have hu : u ∈ Algebra.adjoin ℂ {x : UC E s | ∃ τ i j, x = genC τ i j} := by rw [adjoin_genC]; trivial
  induction hu using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, i, j, rfl⟩ := hx
    exact ⟨genC τ _ _, by rw [uC_genC, uC_genC]; exact CapRes.Eop_mem _ τ i j⟩
  | algebraMap c =>
    exact ⟨algebraMap ℂ _ c, by rw [AlgHom.commutes, AlgHom.commutes]; exact (CapRes.relAlg (eS r s)).algebraMap_mem c⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx⟩ := hx
    obtain ⟨y', hy⟩ := hy
    exact ⟨x' + y', by rw [map_add, map_add]; exact (CapRes.relAlg (eS r s)).add_mem hx hy⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx⟩ := hx
    obtain ⟨y', hy⟩ := hy
    exact ⟨x' * y', by rw [map_mul, map_mul]; exact (CapRes.relAlg (eS r s)).mul_mem hx hy⟩

omit [IsTotallyComplex E] in
private theorem lev_loc (w : Pl E) (k : GL (Fin s) (w.adicCompletion E)) :
    lev (Af E) r s (1, locGL E s w k) = locGL E (r + s) w (lev (w.adicCompletion E) r s (1, k)) := by
  have ext : ∀ g h : GL (Fin (r + s)) (Af E),
      (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) g = Matrix.GeneralLinearGroup.map (pLoc E v) h) → g = h :=
    fun g h H => Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun v =>
      congrArg (fun x : GL (Fin (r + s)) (v.adicCompletion E) => x.1 i j) (H v)))
  refine ext _ _ fun v => ?_
  rw [Slice2.map_lev]
  by_cases e : v = w
  · subst e
    simp only [pLoc_locGL, map_one]
  · simp only [pLoc_locGL_of_ne e, map_one]
    exact map_one _

omit [IsTotallyComplex E] in
private theorem lev_KGL (w : Pl E) {k : GL (Fin s) (w.adicCompletion E)} (hk : k ∈ GlobalTheory.LFun.KGL w s) :
    lev (w.adicCompletion E) r s (1, k) ∈ GlobalTheory.LFun.KGL w (r + s) := by
  obtain ⟨k, rfl⟩ := hk
  refine ⟨lev _ r s (1, k), ?_⟩
  refine (Slice2.map_lev _ _).trans ?_
  rw [map_one]
  rfl

private theorem slice_sum (b : Blo S r) (t : ℝ) {ι : Type} (T : Finset ι) (c : ι → ℂ) (φ : ι → Sm E (r + s))
    (h : ∀ i, Umg (φ i)) (m : GA E s) : Umg (∑ i ∈ T, c i • φ i) ∧
      slice b.f.1 t (∑ i ∈ T, c i • φ i).1 m = ∑ i ∈ T, c i * slice b.f.1 t (φ i).1 m := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (umgOps E (r + s)).1, ?_⟩
    simp [slice, AutomorphicForm.constantTerm_zero]
  | insert i T hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, (sliceBound E S r s b).2 _ _ _ (h i) ih.1, ih.2]
    exact ⟨((umgOps E (r + s)).2 _ (((umgOps E (r + s)).2 _ (h i)).2.2.1 _)).2.1 _ ih.1, rfl⟩

end UpperTheory.ConvolutionTheory.BW.SliceClasses

open UpperTheory.ConvolutionTheory.BW UpperTheory.ConvolutionTheory.BW.SliceClasses in
theorem UpperTheory.ConvolutionTheory.BW.sliceUmg :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.SliceUmg E := by
  intro E _ _ _ S r s b t φ hφ
  let G : Sm E (r + s) := ⟨_, big_mem_Sm b t hφ⟩
  let ψ : Sm E s := ⟨_, Slice2.res_mem_Sm G⟩
  have hψ : ψ.1 = slice b.f.1 t φ.1 := funext fun m => (slice_eq _ _ _ m).symm
  have hι : ∀ m, ψ.1 m = G.1 (CapRes.iota (eS r s) m) := fun m => by rw [iota_eq]
  have hrt : ∀ g, (rt E s g ψ).1 = slice b.f.1 t (rt E (r + s) (lev (Ad E) r s (1, g)) φ).1 := fun g => funext fun m => by
    rw [slice_eq, big_rt, ← map_mul, Prod.mk_mul_mk, one_mul]
    rfl
  have hfix : ∀ k, finRep E (r + s) (lev (Af E) r s (1, k)) φ = φ → finRep E s k ψ = ψ := fun k hk => by
    refine Subtype.ext ((hrt (finGL E s k)).trans ?_)
    rw [Slice2.lev_finGL_one, hψ]
    exact congrArg (fun x : Sm E (r + s) => slice b.f.1 t x.1) hk
  refine ⟨ψ, hψ, ⟨fun γ m => ?_, ?_, ?_⟩, fun τ i j => funext fun m => ?_, hrt, fun h w hw k hk => ?_, fun e ρ h x hx g => ?_⟩
  · rw [hψ]
    unfold slice
    congr 1
    funext y
    have := Pair.ct_lev_rat hφ.left 1 γ (zt E r t * ((Quotient.out y : normOneGL E r) : GA E r)) m
    rw [map_one, one_mul] at this
    rw [this]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset
      ((hφ.level.preimage (Slice2.continuous_lev2 (E := E) (r := r) (s := s))).mem_nhds (by simp)) fun k hk => hfix k hk)
  · obtain ⟨N, hN⟩ := hφ.growth
    obtain ⟨C, hC0, hC⟩ := big_le b s t N
    refine ⟨N, fun u => ?_⟩
    obtain ⟨u', hu⟩ := ex_rel r u
    obtain ⟨B, hB⟩ := hN u'
    have hB0 : 0 ≤ B := by simpa [AutomorphicForm.height_one] using (norm_nonneg _).trans (hB 1)
    refine ⟨C * B * AutomorphicForm.heightConst E (r + s) ^ N, fun g => ?_⟩
    have e := hu G ψ hι g
    rw [iota_eq] at e
    change (uC E s u ψ).1 g = (uC E (r + s) u' G).1 _ at e
    rw [e, uC_big b t hφ u']
    refine (hC _ B (((umgOps E (r + s)).2 φ hφ).2.2.2.1 u') hB _).trans ?_
    rw [mul_assoc (C * B), ← mul_pow]
    have e1 := Pair.height_lev (E := E) (r := r) (s := s) 1 g
    rw [AutomorphicForm.height_one, mul_one] at e1
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le e1 N) (by positivity)
  · have e := CapRes.Eop_mem (eS r s) τ i j G ψ hι m
    rw [iota_eq, eS_inl, eS_inl] at e
    change (Eop τ i j ψ).1 m = (Eop τ (Fin.natAdd r i) (Fin.natAdd r j) G).1 _ at e
    rw [e, slice_eq, ← uC_genC, uC_big b t hφ]
  · refine hfix (locGL E s w k) ?_
    rw [lev_loc]
    exact h w hw _ (lev_KGL w hk)
  · have hK : ∀ k : KA E s, lev (Ad E) r s (1, (k : GA E s)) ∈ KA E (r + s) :=
      fun k => (resTyp E r s ⟨0, 1, continuous_const⟩).2.2 1 k
    let j : KA E s → KA E (r + s) := fun k => ⟨_, hK k⟩
    have h0 := h (x.mapDomain j) (by
      rw [Finsupp.sum_mapDomain_index (h := fun k (c : ℂ) => c • ρ k) (fun _ => zero_smul _ _)
        fun _ _ _ => add_smul _ _ _, ← hx]
      exact Finsupp.sum_congr fun k _ => by rw [resR, dif_pos (hK k)])
    have hz : ∑ k ∈ x.support, x k • rt E (r + s) (lev (Ad E) r s (1, (k : GA E s))) φ = 0 := by
      refine Subtype.ext (funext fun g => ?_)
      have := h0 g
      rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _] at this
      rw [Submodule.coe_sum, Finset.sum_apply]
      exact this
    have := (slice_sum b t x.support x (fun k => rt E (r + s) (lev (Ad E) r s (1, (k : GA E s))) φ)
      (fun k => ((umgOps E (r + s)).2 φ hφ).2.2.2.2.1 _) g).2
    rw [hz] at this
    simp only [← hrt, rt_apply] at this
    refine this.symm.trans ?_
    simp [slice, AutomorphicForm.constantTerm_zero]
