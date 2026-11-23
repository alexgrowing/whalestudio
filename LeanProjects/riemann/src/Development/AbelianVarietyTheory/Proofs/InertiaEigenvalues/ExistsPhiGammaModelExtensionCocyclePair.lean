import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPhiGammaModelCharacterEqStandardStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbcStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPreimageOfInjectiveFinDimRepModelHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPushOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapAevalNab

noncomputable section
namespace GlobalTheory.TopSteps.ExtPair
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps
open scoped LaurentSeries PowerSeries

variable {k : Type} [Field k]

theorem exists_proj {m m' : ℕ} (hm : m' = m + 1) (a : (Fin m → k) →ₗ[k] (Fin m' → k)) (e : Fin m' → k)
    (ha : Function.Injective a) (he : e ∉ LinearMap.range a) :
    ∃ p : (Fin m' → k) →ₗ[k] (Fin 1 → k), Function.Exact a p ∧ p e = (fun _ => 1) ∧ Function.Surjective p := by
  obtain ⟨f, hf, hfe⟩ := LinearMap.exists_extend_of_notMem (0 : LinearMap.range a →ₗ[k] k) he 1
  have hfs : Function.Surjective f := fun c => ⟨c • e, by simp [hfe]⟩
  have hle : LinearMap.range a ≤ LinearMap.ker f := fun x hx => by
    simpa using LinearMap.congr_fun hf ⟨x, hx⟩
  have h1 := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 hfs] at h1
  have h2 := LinearMap.finrank_range_of_inj ha
  simp only [finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1 h2
  have heq : LinearMap.range a = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  refine ⟨LinearMap.pi fun _ => f, fun x => ?_, funext fun _ => hfe, fun y => ?_⟩
  · change _ ↔ x ∈ LinearMap.range a
    rw [heq, LinearMap.mem_ker]
    constructor
    · intro h; exact congrFun h 0
    · intro h; exact funext fun _ => h
  · obtain ⟨x, hx⟩ := hfs (y 0)
    exact ⟨x, funext fun j => by rw [Subsingleton.elim j 0]; exact hx⟩

theorem mem_sh_comap {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (N : Submodule k⟦X⟧ (Vc k b)) (s : ℤ) (x : Vc k a) :
    x ∈ sh s (N.comap (φ.restrictScalars k⟦X⟧)) ↔ φ x ∈ sh s N := by
  rw [mem_sh_iff_smul_mem, mem_sh_iff_smul_mem, ← map_smul]; rfl

theorem aeval_nab_mem {a : ℕ} (g : Vc k a →ₗ[k] Vc k a) (N : Submodule k⟦X⟧ (Vc k a)) (hN : CondC g N)
    (f : Polynomial k) (x : Vc k a) (hx : x ∈ N) : Polynomial.aeval (nab g) f x ∈ N := by
  induction f using Polynomial.induction_on generalizing x with
  | C c =>
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact N.smul_of_tower_mem c hx
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply]
    exact N.add_mem (hp x hx) (hq x hx)
  | monomial m c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    exact ih _ ((condC_iff_nab_mem g N).1 hN x hx)

theorem aeval_nab_fixed {a : ℕ} (g : Vc k a →ₗ[k] Vc k a) (f : Polynomial k) (u : Vc k a) (hu : g u = u) :
    Polynomial.aeval (nab g) f u = f.eval 0 • u := by
  apply Module.End.aeval_apply_of_mem_apply_eq_smul
  rw [nab_apply_eq, hu, sub_self, smul_zero, zero_smul]

theorem exists_model_repr_inZZ : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l →
    ∀ (A : Ob k G) (z : G → Fin A.m → k), z ∈ M.twistedModelAdmissibleCocycles A →
      ∃ (N : Lats k n A.m) (b g : ZMod n → Vc k A.m), M.Model A N ∧ Repr F A z b g ∧ InZZ (F.D A) Dt N b g := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 A z hz
  obtain ⟨E, NE, ⟨hm, a, e, ha, hai, he, hez⟩, hNE⟩ := hz
  obtain ⟨p, hex, hpe, hps⟩ := exists_proj hm a e hai he
  have hpa : ∀ y, p (a y) = 0 := hex.apply_apply_eq_zero
  have hp : IsHom E (chr 1) p := by
    intro σ x
    obtain ⟨y, hy⟩ := (hex (x - p x 0 • e)).1 (by
      rw [map_sub, map_smul, hpe]; funext j; rw [Subsingleton.elim j 0]; simp)
    have hx : x = a y + p x 0 • e := by rw [hy]; abel
    have h : p (E.ρ σ x) = p x := by
      conv_lhs => rw [hx]
      conv_rhs => rw [hx]
      rw [map_add, map_smul, ← ha, hez]
      simp only [map_add, map_smul, hpa, add_zero]
    rw [h]
    change _ = (((1 : G →* kˣ) σ : kˣ) : k) • p x
    simp
  obtain ⟨oE, -, hAB, hC⟩ := GlobalTheory.T.obj_and_abc_of_model F M E NE hNE
  have oA := F.obj_sub A E a ha hai oE
  have o1 := F.obj_one
  have hq : M.Model (chr 1) (F.push E (chr 1) p NE) :=
    GlobalTheory.Models.ModTh.model_push_of_surjective F M E (chr 1) p NE hp hps hNE
  have hq' : ∀ χ : G →* kˣ, χ = 1 → M.Model (chr χ) (F.push E (chr 1) p NE) := by
    rintro _ rfl; exact hq
  have hpush : ∀ i, F.push E (chr 1) p NE i = Submodule.span k⟦X⟧ {F.unit i} := fun i => by
    rw [← M.χ_zero i]
    exact congrFun (GlobalTheory.T.twistedPhiGammaModel_character_eq_standard F M h1 h2 h3 0 le_rfl (by exact_mod_cast Dt.one_le_letterBlockLength) _
      (hq' _ (by simp))) i
  have hε : ∀ i, ∃ ε ∈ NE i, F.map E (chr 1) p i ε = F.unit i := fun i => by
    have : F.unit i ∈ F.push E (chr 1) p NE i := by
      rw [hpush]; exact Submodule.mem_span_singleton_self _
    exact this
  choose ε hεN hεp using hε
  have hD := GlobalTheory.Models.DFun.map_exact_middle F A E (chr 1) a p oE ha hp hai hps hex
  have hinj := F.map_inj A E a oA oE ha hai
  have aφ := F.map_φ A E a oA oE ha
  have aγ := F.map_γ A E a oA oE ha
  have pφ := F.map_φ E (chr 1) p oE o1 hp
  have pγ := F.map_γ E (chr 1) p oE o1 hp
  have hb : ∀ i, ∃ b, F.map A E a i b = (F.D E).φ i (ε (i - 1)) - ε i := fun i =>
    (hD i _).1 (by rw [map_sub, pφ, hεp, hεp, F.unit_φ, sub_self])
  have hg : ∀ i, ∃ g, F.map A E a i g = (F.D E).γ i (ε i) - ε i := fun i =>
    (hD i _).1 (by rw [map_sub, pγ, hεp, F.unit_γ, sub_self])
  choose b hb using hb
  choose g hg using hg
  refine ⟨F.pre A E a NE, b, g, GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A E a NE ha hai hNE,
    ⟨E, a, p, e, ε, oE, ha, hp, hai, hex, hpe, hez, fun i => ⟨hεp i, hb i, hg i⟩⟩, fun i => ⟨?_, ?_, ?_, ?_⟩⟩
  · apply hinj i
    rw [map_sub, map_sub, aφ, aγ, hb, hg, hg, map_sub, map_sub, (F.D E).comm]
    abel
  · refine (mem_sh_comap _ _ _ _).2 ?_
    rw [hg]; exact hC i _ (hεN i)
  · intro _
    refine (mem_sh_comap _ _ _ _).2 ?_
    rw [hb]
    have hw : 1 ≤ Dt.w i := (Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2
      ⟨le_rfl, by have := Dt.one_le_letterBlockLength; omega⟩)))).1
    refine Submodule.sub_mem _ ((hAB i).1 (Submodule.subset_span ⟨_, hεN _, rfl⟩)) ?_
    apply sh_le_sh_of_le (a := 0) (by omega)
    rw [sh_zero_eq]; exact hεN i
  · intro hi
    constructor
    · have hdec : ∀ y ∈ pull ((F.D E).φ i) (NE (i - 1)), ∃ m ∈ pull ((F.D A).φ i) (F.pre A E a NE (i - 1)),
          ∃ c : k⸨X⸩, y = F.map A E a i m + c • (F.D E).φ i (ε (i - 1)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨x, hx, rfl⟩ := hy
          have h4 : F.map E (chr 1) p (i - 1) x ∈ F.push E (chr 1) p NE (i - 1) := ⟨x, hx, rfl⟩
          rw [hpush, Submodule.mem_span_singleton] at h4
          obtain ⟨c, hc⟩ := h4
          obtain ⟨m, hm⟩ := (hD (i - 1) (x - c • ε (i - 1))).1 (by
            rw [map_sub, LinearMap.map_smul_of_tower, hεp, hc, sub_self])
          have hmN : m ∈ F.pre A E a NE (i - 1) := by
            change F.map A E a (i - 1) m ∈ NE (i - 1)
            rw [hm]; exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (hεN _))
          refine ⟨(F.D A).φ i m, Submodule.subset_span ⟨m, hmN, rfl⟩, R.φ (algebraMap k⟦X⟧ k⸨X⸩ c), ?_⟩
          rw [aφ, hm, ← (F.D E).φ_semi i, algebraMap_smul, ← map_add, sub_add_cancel]
        | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp⟩
        | add y y' _ _ hy hy' =>
          obtain ⟨m, hm, c, rfl⟩ := hy
          obtain ⟨m', hm', c', rfl⟩ := hy'
          exact ⟨m + m', Submodule.add_mem _ hm hm', c + c', by rw [map_add, add_smul]; abel⟩
        | smul d y _ hy =>
          obtain ⟨m, hm, c, rfl⟩ := hy
          refine ⟨d • m, Submodule.smul_mem _ _ hm, d • c, ?_⟩
          rw [smul_add, LinearMap.map_smul_of_tower, smul_assoc]
      obtain ⟨m, hm, c, hc⟩ := hdec _ ((hAB i).2 (mem_sh_iff_exists.2 ⟨_, hεN i, rfl⟩))
      have h5 := congrArg (F.map E (chr 1) p i) hc
      rw [map_smul, map_add, map_smul, pφ, hεp, hεp, F.unit_φ, (hD i).apply_apply_eq_zero, zero_add] at h5
      have h6 : vv k ^ Dt.wst i = c := smul_left_injective _ (F.unit_ne i) h5
      rw [mem_sh_iff_smul_mem, neg_neg]
      have h7 : vv k ^ Dt.wst i • b i = -m := by
        apply hinj i
        rw [map_smul, hb, smul_sub, hc, h6, map_neg]; abel
      rw [h7]; exact Submodule.neg_mem _ hm
    · obtain ⟨f, hf, hfN⟩ := GlobalTheory.Models.EPolyModel.model_ePoly F M h1 h3 E NE hNE i hi
      obtain ⟨x, hx⟩ := (hD i (ε i - (f.eval 0)⁻¹ • Polynomial.aeval (nab ((F.D E).γ i)) f (ε i))).1 (by
        rw [map_sub, LinearMap.map_smul_of_tower,
          EPolyModel.map_aeval_nab (F.map E (chr 1) p i) _ _ (pγ i), hεp, aeval_nab_fixed _ _ _ (F.unit_γ i),
          smul_smul, inv_mul_cancel₀ hf, one_smul, sub_self])
      refine ⟨x, ?_, (mem_sh_comap _ _ _ _).2 ?_⟩
      · change F.map A E a i x ∈ NE i
        rw [hx]
        exact Submodule.sub_mem _ (hεN i)
          (Submodule.smul_of_tower_mem _ _ (aeval_nab_mem _ _ (hC i) f _ (hεN i)))
      · have h4 := hfN _ (hεN i)
        set y := Polynomial.aeval (nab ((F.D E).γ i)) f (ε i)
        have h5 : (F.D E).γ i y - y ∈ sh (Dt.wst i + 2) (NE i) := by
          rw [show Dt.wst i + 2 = 1 + (Dt.wst i + 1) by ring, ← sh_sh_eq, mem_sh_iff_smul_mem, zpow_neg_one]
          exact h4
        have h6 : F.map A E a i (g i - ((F.D A).γ i x - x)) = (f.eval 0)⁻¹ • ((F.D E).γ i y - y) := by
          rw [map_sub, map_sub, aγ, hg, hx, map_sub, map_smul, smul_sub]; abel
        rw [h6]
        exact Submodule.smul_of_tower_mem _ _ h5

end GlobalTheory.TopSteps.ExtPair
