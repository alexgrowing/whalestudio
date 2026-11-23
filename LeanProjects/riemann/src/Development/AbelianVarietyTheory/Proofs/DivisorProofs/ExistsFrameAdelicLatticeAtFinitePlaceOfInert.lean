import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XmApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocBasis

open GlobalTheory.InertSph

section Alg

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

local instance valRing : ValuationRing (Formalism.UG.intL L) :=
  ValuationRing.of_integers (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) (Valuation.integer.integers _)

local instance fracRing : IsFractionRing (Formalism.UG.intL L) L :=
  inferInstanceAs (IsFractionRing (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring L)

theorem exists_basis_of_fg {n : ℕ} (M : Submodule (Formalism.UG.intL L) (Fin n → L)) (hfg : M.FG)
    (hsp : Submodule.span L (M : Set (Fin n → L)) = ⊤) :
    ∃ P : GL (Fin n) L, ∀ x : Fin n → L,
      (∀ i, x i ∈ Formalism.UG.intL L) ↔ (P : Matrix (Fin n) (Fin n) L) *ᵥ x ∈ M := by
  have : Module.Finite (Formalism.UG.intL L) M := Module.Finite.iff_fg.2 hfg
  have : Module.Free (Formalism.UG.intL L) M := by
    have : Module.Flat (Formalism.UG.intL L) M := by
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
      have ha0 : ((a : Formalism.UG.intL L) : L) ≠ 0 := fun h =>
        nonZeroDivisors.ne_zero a.2 (Subtype.ext h)
      apply Subtype.ext
      funext i
      have h1 := congrFun (congrArg Subtype.val ha) i
      change ((a : Formalism.UG.intL L) : L) * (x : Fin n → L) i = 0 at h1
      exact (mul_eq_zero.1 h1).resolve_left ha0
    exact Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis (Formalism.UG.intL L) M
  let v : Module.Free.ChooseBasisIndex (Formalism.UG.intL L) M → Fin n → L := fun i => (b i : Fin n → L)
  have hR : LinearIndependent (Formalism.UG.intL L) v := b.linearIndependent.map' M.subtype (Submodule.ker_subtype _)
  have hC : LinearIndependent L v := (LinearIndependent.iff_fractionRing (Formalism.UG.intL L) L).1 hR
  have hspR : Submodule.span (Formalism.UG.intL L) (Set.range v) = M := by
    have : Set.range v = M.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspC : Submodule.span L (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower (Formalism.UG.intL L), hspR, hsp]
  let bC := Module.Basis.mk hC (by rw [hspC])
  have hcard : Fintype.card (Fin n) = Fintype.card (Module.Free.ChooseBasisIndex (Formalism.UG.intL L) M) := by
    rw [← Module.finrank_fintype_fun_eq_card (R := L), Module.finrank_eq_card_basis bC]
  let e : Fin n ≃ Module.Free.ChooseBasisIndex (Formalism.UG.intL L) M := Fintype.equivOfCardEq hcard
  let B : Matrix (Fin n) (Fin n) L := Matrix.of fun i j => v (e j) i
  have hli : LinearIndependent L (fun j => v (e j)) := hC.comp e e.injective
  have hu : IsUnit B := Matrix.linearIndependent_cols_iff_isUnit.1 (by
    have hcol : B.col = fun j => v (e j) := by funext j i; rfl
    rw [hcol]; exact hli)
  have hBx : ∀ y : Fin n → L, B *ᵥ y = ∑ j, y j • v (e j) := by
    intro y; funext i; simp [B, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hrg : (Set.range fun j => v (e j)) = Set.range v := e.surjective.range_comp v
  have hspR' : Submodule.span (Formalism.UG.intL L) (Set.range fun j => v (e j)) = M := by rw [hrg, hspR]
  have key : ∀ y, y ∈ M ↔ y ∈ Submodule.span (Formalism.UG.intL L) (Set.range fun j => v (e j)) := fun y => by
    rw [hspR']
  refine ⟨hu.unit, fun x => ?_⟩
  rw [IsUnit.unit_spec, hBx, key]
  constructor
  · intro hx
    refine Submodule.sum_mem _ fun j _ => ?_
    have := Submodule.smul_mem (Submodule.span (Formalism.UG.intL L) (Set.range fun j => v (e j))) (⟨x j, hx j⟩ : (Formalism.UG.intL L))
      (Submodule.subset_span ⟨j, rfl⟩)
    exact this
  · intro hx i
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    have h0 := (Fintype.linearIndependent_iff.1 hli) (fun j => (c j : L) - x j) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero, ← hc]; rfl)
    have := h0 i
    rw [sub_eq_zero] at this
    rw [← this]; exact (c i).2

end Alg

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def genAt (v : Pl F) : Set (AE F E) := {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
  evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}

theorem at_mul {v : Pl F} {z : AE F E} (hz : At (evFin F v) z) (y : AE F E) : At (evFin F v) (z * y) :=
  fun u hu => by rw [← smul_mul_assoc, hz u hu, zero_mul]

theorem at_smul_one {v : Pl F} {a : AF F} (ha : At (evFin F v) a) : At (evFin F v) (a • (1 : AE F E)) :=
  fun u hu => by rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]

theorem mul_incl_mem {v : Pl F} {s : AE F E} (hs : s ∈ AddSubgroup.closure (genAt F E v)) (o : 𝓞 E) :
    s * inclR (F := F) (AF F) (o : E) ∈ AddSubgroup.closure (genAt F E v) := by
  induction hs using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, hev, o', rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a, ha, hev, o' * o, by simp [smul_mul_assoc, map_mul]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem smul_latAt_mem {n : ℕ} (X : Spc F E n) {v : Pl F} {a : AF F} (ha : At (evFin F v) a)
    (hev : evFin F v a ∈ v.adicCompletionIntegers F) {z : Fin n → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt X v) :
    a • z ∈ GlobalTheory.InertSph.latAt X v := by
  unfold GlobalTheory.InertSph.latAt at hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a', ha', hev', y, hy, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨a * a', fun u hu => ?_, ?_, y, hy, by rw [smul_smul]⟩
    · have h0 : u * a = 0 := ha u hu
      rw [smul_eq_mul, ← mul_assoc, h0, zero_mul]
    · rw [map_mul]; exact mul_mem hev hev'
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mul_incl_latAt {n : ℕ} (X : Spc F E n) {v : Pl F} {s : AE F E}
    (hs : s ∈ AddSubgroup.closure (genAt F E v)) {y : Fin n → E} (hy : y ∈ X.L) :
    (fun i => s * inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt X v := by
  induction hs using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, hev, o, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨a, ha, hev, o • y, X.L.smul_mem o hy, ?_⟩
    funext i
    show (a • inclR (F := F) (AF F) (o : E)) * inclR (F := F) (AF F) (y i) = a • inclR (F := F) (AF F) ((o • y) i)
    rw [smul_mul_assoc, ← map_mul]; rfl
  | zero => convert (GlobalTheory.InertSph.latAt X v).zero_mem using 1; funext i; simp
  | add x x' _ _ hx hx' => convert add_mem hx hx' using 1; funext i; simp [add_mul]
  | neg x _ hx => convert neg_mem hx using 1; funext i; simp

theorem mul_latAt {n : ℕ} (X : Spc F E n) {v : Pl F} {s : AE F E}
    (hs : s ∈ AddSubgroup.closure (genAt F E v)) {z : Fin n → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt X v) :
    (fun i => s * z i) ∈ GlobalTheory.InertSph.latAt X v := by
  unfold GlobalTheory.InertSph.latAt at hz
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, hev, y, hy, rfl⟩ := hx
    have h := smul_latAt_mem X ha hev (mul_incl_latAt X hs hy)
    convert h using 1
    funext i
    simp [mul_smul_comm]
  | zero => convert (GlobalTheory.InertSph.latAt X v).zero_mem using 1; funext i; simp
  | add x x' _ _ hx hx' => convert add_mem hx hx' using 1; funext i; simp [mul_add]
  | neg x _ hx => convert neg_mem hx using 1; funext i; simp

end Adelic

theorem exists_basis_at_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (n : ℕ) (X : Spc F E n), X.L.IsLattice E →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ AE F E),
      Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∃ P : GL (Fin n) L, (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) := by
  intro F E _ _ _ _ _ v w _ n X hlat L _ _ ι hinj himg hmul hint
  haveI := hlat
  have hint' : ∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure (genAt F E v) := hint
  have h11 : ι 1 * ι 1 = ι 1 := by rw [← hmul, one_mul]
  have hAt1 : At (evFin F v) (ι 1) := (himg _).2 ⟨1, rfl⟩
  have hpre : ∀ z, At (evFin F v) z → ι (GlobalTheory.InertLocFrame.pre ι z) = z := fun z hz =>
    GlobalTheory.InertLocFrame.pre_spec ι ((himg z).1 hz)
  let κ : E → L := fun c => GlobalTheory.InertLocFrame.pre ι (ι 1 * inclR (F := F) (AF F) c)
  have hκ : ∀ c, ι (κ c) = ι 1 * inclR (F := F) (AF F) c := fun c => hpre _ (at_mul hAt1 _)
  have h1mem : ι 1 ∈ AddSubgroup.closure (genAt F E v) := (hint' 1).1 (Formalism.UG.intL L).one_mem
  have hκR : ∀ o : 𝓞 E, κ (o : E) ∈ Formalism.UG.intL L := fun o =>
    (hint' _).2 (by rw [hκ]; exact mul_incl_mem h1mem o)
  obtain ⟨s, hs⟩ := (Submodule.IsLattice.fg : X.L.FG)
  let M : Submodule (Formalism.UG.intL L) (Fin n → L) :=
    Submodule.span (Formalism.UG.intL L) ((fun t : Fin n → E => fun i => κ (t i)) '' (s : Set (Fin n → E)))
  have key1 : ∀ t ∈ X.L, ∃ y ∈ M, ∀ i, ι (y i) = ι 1 * inclR (F := F) (AF F) (t i) := by
    intro t ht
    rw [← hs] at ht
    induction ht using Submodule.span_induction with
    | mem t ht => exact ⟨_, Submodule.subset_span ⟨t, ht, rfl⟩, fun i => hκ _⟩
    | zero => exact ⟨0, M.zero_mem, fun i => by simp⟩
    | add t t' _ _ h h' =>
      obtain ⟨y, hy, e⟩ := h
      obtain ⟨y', hy', e'⟩ := h'
      exact ⟨y + y', M.add_mem hy hy', fun i => by simp [e, e', mul_add]⟩
    | smul o t _ h =>
      obtain ⟨y, hy, e⟩ := h
      refine ⟨(⟨κ (o : E), hκR o⟩ : Formalism.UG.intL L) • y, M.smul_mem _ hy, fun i => ?_⟩
      have ho : (o • t) i = (o : E) * t i := rfl
      show ι (κ (o : E) * y i) = _
      rw [hmul, hκ, e, ho, map_mul]
      linear_combination (inclR (F := F) (AF F) (o : E) * inclR (F := F) (AF F) (t i)) * h11
  have key2 : ∀ z ∈ GlobalTheory.InertSph.latAt X v, ∃ y ∈ M, (fun i => ι (y i)) = z := by
    intro z hz
    unfold GlobalTheory.InertSph.latAt at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hev, t, ht, rfl⟩ := hz
      obtain ⟨y, hy, e⟩ := key1 t ht
      have hr : ι (GlobalTheory.InertLocFrame.pre ι (a • (1 : AE F E))) = a • 1 := hpre _ (at_smul_one ha)
      have hrR : GlobalTheory.InertLocFrame.pre ι (a • (1 : AE F E)) ∈ Formalism.UG.intL L :=
        (hint' _).2 (by rw [hr]; exact AddSubgroup.subset_closure ⟨a, ha, hev, 1, by simp⟩)
      refine ⟨(⟨_, hrR⟩ : Formalism.UG.intL L) • y, M.smul_mem _ hy, funext fun i => ?_⟩
      show ι (GlobalTheory.InertLocFrame.pre ι (a • (1 : AE F E)) * y i) = (a • fun i => inclR (F := F) (AF F) (t i)) i
      rw [hmul, e, ← mul_assoc, ← hmul, mul_one, hr, smul_mul_assoc, one_mul]
      rfl
    | zero => exact ⟨0, M.zero_mem, by funext i; simp⟩
    | add z z' _ _ h h' =>
      obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨y', hy', rfl⟩ := h'
      exact ⟨y + y', M.add_mem hy hy', by funext i; simp⟩
    | neg z _ h =>
      obtain ⟨y, hy, rfl⟩ := h
      exact ⟨-y, M.neg_mem hy, by funext i; simp⟩
  have hMem : ∀ y : Fin n → L, y ∈ M ↔ (fun i => ι (y i)) ∈ GlobalTheory.InertSph.latAt X v := by
    intro y
    constructor
    · intro hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨t, ht, rfl⟩ := hy
        have htL : t ∈ X.L := hs ▸ Submodule.subset_span ht
        have := mul_incl_latAt X h1mem htL
        convert this using 1
        funext i
        exact hκ _
      | zero => convert (GlobalTheory.InertSph.latAt X v).zero_mem using 1; funext i; simp
      | add y y' _ _ h h' => convert add_mem h h' using 1; funext i; simp
      | smul r y _ h =>
        have := mul_latAt X ((hint' _).1 r.2) h
        convert this using 1
        funext i
        exact hmul (r : L) (y i)
    · intro h
      obtain ⟨y', hy', e⟩ := key2 _ h
      have : y' = y := funext fun i => hinj (congrFun e i)
      rwa [← this]
  have hκadd : ∀ c d, κ (c + d) = κ c + κ d := fun c d => hinj (by rw [map_add, hκ, hκ, hκ, map_add, mul_add])
  have hκmul : ∀ c d, κ (c * d) = κ c * κ d := fun c d => hinj (by
    rw [hmul, hκ, hκ, hκ, map_mul]
    linear_combination (-(inclR (F := F) (AF F) c * inclR (F := F) (AF F) d)) * h11)
  have hκ1 : κ 1 = 1 := hinj (by rw [hκ, (inclR (F := F) (AF F)).map_one, mul_one])
  have hκ0 : κ 0 = 0 := hinj (by rw [hκ, map_zero, mul_zero, map_zero])
  have hκmem : ∀ t ∈ X.L, (fun i => κ (t i)) ∈ M := fun t ht => by
    obtain ⟨y, hy, e⟩ := key1 t ht
    have : y = fun i => κ (t i) := funext fun i => hinj (by rw [e, hκ])
    rwa [← this]
  have hQ : ∀ t : Fin n → E, (fun i => κ (t i)) ∈ Submodule.span L (M : Set (Fin n → L)) := by
    intro t
    have ht : t ∈ Submodule.span E (X.L : Set (Fin n → E)) := by
      rw [Submodule.IsLattice.span_eq_top]; trivial
    induction ht using Submodule.span_induction with
    | mem t ht => exact Submodule.subset_span (hκmem t ht)
    | zero => convert (Submodule.span L (M : Set (Fin n → L))).zero_mem using 1; funext i; simp [hκ0]
    | add t t' _ _ h h' => convert add_mem h h' using 1; funext i; simp [hκadd]
    | smul c t _ h =>
      convert Submodule.smul_mem _ (κ c) h using 1
      funext i; simp [hκmul]
  have hsp : Submodule.span L (M : Set (Fin n → L)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun L (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe]
    have := hQ (Pi.single i 1)
    convert this using 1
    funext j
    rw [Pi.basisFun_apply]
    by_cases hij : j = i
    · subst hij; simp [hκ1]
    · simp [Pi.single_apply, hij, hκ0]
  have hfg : M.FG := Submodule.fg_span ((s.finite_toSet).image _)
  obtain ⟨P, hP⟩ := exists_basis_of_fg M hfg hsp
  exact ⟨P, fun x => (hP x).trans (hMem _)⟩

end GlobalTheory.InertLocBasis
