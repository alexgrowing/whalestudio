import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.LatIdem

theorem exists_iterate_idem {X : Type*} [Finite X] (u : X → X) : ∃ N : ℕ, 0 < N ∧ u^[2 * N] = u^[N] := by
  obtain ⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧ u^[i] = u^[j] := by
    obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => u^[n])
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact ⟨i, j, h1, h⟩
    · exact ⟨j, i, h1, h.symm⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have key : ∀ m : ℕ, u^[i + m * (k + 1)] = u^[i] := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have : i + (m + 1) * (k + 1) = (i + m * (k + 1)) + (k + 1) := by ring
      rw [this, Function.iterate_add, ih, ← Function.iterate_add, ← add_assoc, ← h]
  refine ⟨(i + 1) * (k + 1), by positivity, ?_⟩
  have e1 : 2 * ((i + 1) * (k + 1)) = (i + (i + 1) * (k + 1)) + (i * k + k + 1) := by ring
  have e2 : (i + 1) * (k + 1) = i + (i * k + k + 1) := by ring
  rw [e1, Function.iterate_add, key, ← Function.iterate_add, ← e2]

theorem exists_idem_mod {M : Type*} [AddCommGroup M] (Λ P : AddSubgroup M) (g : M →+ M)
    (hΛ : ∀ z ∈ Λ, g z ∈ Λ) (hP : ∀ z ∈ P, g z ∈ P) [Finite (Λ.map (QuotientAddGroup.mk' P))] :
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ Λ, g^[2 * N] z - g^[N] z ∈ P := by
  let gb : M ⧸ P →+ M ⧸ P := QuotientAddGroup.map P P g hP
  let u : Λ.map (QuotientAddGroup.mk' P) → Λ.map (QuotientAddGroup.mk' P) := fun x => ⟨gb x, by
    obtain ⟨_, z, hz, rfl⟩ := x
    exact ⟨g z, hΛ z hz, rfl⟩⟩
  have hu : ∀ (n : ℕ) (z : M) (hz : z ∈ Λ), (u^[n] ⟨QuotientAddGroup.mk' P z, z, hz, rfl⟩ : M ⧸ P) =
      QuotientAddGroup.mk' P (g^[n] z) := by
    intro n
    induction n with
    | zero => intro z hz; rfl
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      show gb _ = _
      rw [ih z hz]; rfl
  obtain ⟨N, hN, h⟩ := exists_iterate_idem u
  refine ⟨N, hN, fun z hz => ?_⟩
  have := hu (2 * N) z hz
  rw [h, hu N z hz] at this
  exact QuotientAddGroup.eq_iff_sub_mem.1 this.symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open GlobalTheory.EmbChart GlobalTheory.InertSph

theorem at_atPlace (v : Pl F) (a : Fv F v) : At (evFin F v) (atPlace v a) := by
  intro u hu
  rw [smul_eq_mul, mul_comm, atPlace_mul_right, hu, mul_zero, map_zero]

theorem eq_atPlace (v : Pl F) (a : AF F) (ha : At (evFin F v) a) : a = atPlace v (evFin F v a) := by
  have h := ha (1 - atPlace v 1) (by rw [map_sub, map_one, evFin_atPlace, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, atPlace_mul_right, one_mul, sub_eq_zero] at h
  exact h

omit [NumberField E] in
theorem gen_mem {d : ℕ} (W : Spc F E d) (v : Pl F) (c : v.adicCompletionIntegers F) (y : Fin d → E) (hy : y ∈ W.L) :
    (atPlace v (c : Fv F v) • fun i => inclR (F := F) (AF F) (y i)) ∈ latAt W v :=
  AddSubgroup.subset_closure ⟨_, at_atPlace v _, by rw [evFin_atPlace]; exact c.2, y, hy, rfl⟩

theorem finite_mod {d : ℕ} (W : Spc F E d) (hW : W.L.FG) (v : Pl F) (p : ℕ) (hp : 0 < p) :
    Finite ((latAt W v).map (QuotientAddGroup.mk' ((latAt W v).map (nsmulAddMonoidHom p)))) := by
  set P := (latAt W v).map (nsmulAddMonoidHom p) with hPdef
  have hp0 : (p : v.adicCompletionIntegers F) ≠ 0 := by
    intro h
    have h1 : ((p : v.adicCompletionIntegers F) : Fv F v) = 0 := congrArg Subtype.val h
    have h2 : (p : Fv F v) = 0 := by simpa using h1
    rw [← map_natCast (algebraMap F (Fv F v)), map_eq_zero] at h2
    exact (Nat.cast_ne_zero.2 hp.ne') h2
  have hfin : Finite (v.adicCompletionIntegers F ⧸ Ideal.span {(p : v.adicCompletionIntegers F)}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  obtain ⟨T, hT⟩ : (W.L.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) W.L := Module.Finite.iff_fg.2 hW
    have : Module.Finite ℤ W.L := Module.Finite.trans (𝓞 E) W.L
    exact Module.Finite.iff_fg.1 this
  have hTL : ∀ t ∈ T, t ∈ W.L := fun t ht => by
    have : t ∈ W.L.restrictScalars ℤ := hT ▸ Submodule.subset_span ht
    exact this
  let s : (v.adicCompletionIntegers F ⧸ Ideal.span {(p : v.adicCompletionIntegers F)}) × T → (Fin d → AE F E) ⧸ P :=
    fun x => QuotientAddGroup.mk' P
      (atPlace v ((x.1.out : v.adicCompletionIntegers F) : Fv F v) • fun i => inclR (F := F) (AF F) (x.2.1 i))
  have heq : (latAt W v).map (QuotientAddGroup.mk' P) = AddSubgroup.closure (Set.range s) := by
    apply le_antisymm
    · rw [AddSubgroup.map_le_iff_le_comap, InertSph.latAt, AddSubgroup.closure_le]
      rintro _ ⟨a, ha, hav, y, hy, rfl⟩
      have hy' : y ∈ Submodule.span ℤ (T : Set (Fin d → E)) := hT ▸ hy
      clear hy
      rw [SetLike.mem_coe]
      induction hy' using Submodule.span_induction with
      | mem t ht =>
        let x : v.adicCompletionIntegers F := ⟨_, hav⟩
        let q := Ideal.Quotient.mk (Ideal.span {(p : v.adicCompletionIntegers F)}) x
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out q).symm)
        have hc' : evFin F v a - ((q.out : v.adicCompletionIntegers F) : Fv F v) = p • (c : Fv F v) := by
          have := congrArg Subtype.val hc
          simp only [MulMemClass.coe_mul, SubringClass.coe_natCast, AddSubgroupClass.coe_sub] at this
          rw [nsmul_eq_mul, mul_comm]; exact this.symm
        rw [AddSubgroup.mem_comap]
        refine AddSubgroup.subset_closure ⟨(q, ⟨t, ht⟩), ?_⟩
        refine (QuotientAddGroup.eq_iff_sub_mem.2 ?_).symm
        refine ⟨_, gen_mem W v c t (hTL t ht), ?_⟩
        rw [← sub_smul, eq_atPlace v a ha, ← map_sub, hc', map_nsmul, smul_assoc]
        rfl
      | zero =>
        have : (a • fun i => inclR (F := F) (AF F) ((0 : Fin d → E) i)) = 0 := by
          funext i; simp
        rw [this]; exact zero_mem _
      | add x y _ _ hx hy =>
        have : (a • fun i => inclR (F := F) (AF F) ((x + y) i)) =
            (a • fun i => inclR (F := F) (AF F) (x i)) + (a • fun i => inclR (F := F) (AF F) (y i)) := by
          funext i; simp
        rw [this]; exact add_mem hx hy
      | smul n x _ hx =>
        have : (a • fun i => inclR (F := F) (AF F) ((n • x) i)) =
            n • (a • fun i => inclR (F := F) (AF F) (x i)) := by
          funext i
          simp only [Pi.smul_apply, map_zsmul]
          rw [smul_comm]
        rw [this]; exact zsmul_mem hx n
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨_, gen_mem W v _ _ (hTL _ x.2.2), rfl⟩
  have hfg : ((latAt W v).map (QuotientAddGroup.mk' P)).FG :=
    (AddSubgroup.fg_iff _).2 ⟨_, heq.symm, Set.finite_range s⟩
  have : AddGroup.FG ((latAt W v).map (QuotientAddGroup.mk' P)) := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  refine AddCommGroup.finite_of_fg_isAddTorsion _ ?_
  rintro ⟨_, z, hz, rfl⟩
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨p, hp, Subtype.ext ?_⟩
  show p • QuotientAddGroup.mk' P z = 0
  rw [← map_nsmul]
  exact (QuotientAddGroup.eq_zero_iff _).2 ⟨z, hz, rfl⟩

theorem exists_pow_idem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d),
    W.L.IsLattice E → ∀ (v : Pl F) (p : ℕ), 0 < p → (p : 𝓞 F) ∈ v.asIdeal →
    ∀ f : Matrix (Fin d) (Fin d) (AE F E), (∀ z ∈ GlobalTheory.InertSph.latAt W v, f *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∃ y ∈ GlobalTheory.InertSph.latAt W v, (f ^ (2 * N)) *ᵥ z - (f ^ N) *ᵥ z = p • y := by
  intro F E _ _ _ _ _ d W hW v p hp _ f hf
  have := finite_mod W hW.fg v p hp
  let g : (Fin d → AE F E) →+ (Fin d → AE F E) := (Matrix.mulVecLin f).toAddMonoidHom
  have hg : ∀ (n : ℕ) (z : Fin d → AE F E), g^[n] z = (f ^ n) *ᵥ z := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', ih, pow_succ', ← Matrix.mulVec_mulVec]; rfl
  obtain ⟨N, hN, h⟩ := exists_idem_mod (latAt W v) ((latAt W v).map (nsmulAddMonoidHom p)) g hf (by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨g z, hf z hz, (map_nsmul g p z).symm⟩)
  refine ⟨N, hN, fun z hz => ?_⟩
  obtain ⟨y, hy, e⟩ := h z hz
  rw [hg, hg] at e
  exact ⟨y, hy, e.symm⟩

end GlobalTheory.LatIdem
