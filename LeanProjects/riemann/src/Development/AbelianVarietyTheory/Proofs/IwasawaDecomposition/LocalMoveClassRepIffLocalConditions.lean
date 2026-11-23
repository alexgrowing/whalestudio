import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalCondMoveDecoratedLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueEqZeroIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
import Formalism.LocalToGlobal.Columns.AdelicLemmas
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm

open GlobalTheory.Mem.Col2.LevRead

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem entries_int {s : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : Formalism.L2.Herm.Carries s (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n)) (i j : Fin n) :
    (s : Matrix (Fin n) (Fin n) _) i j ∈ Formalism.L2.Herm.intAf F E ∧
      ((s⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j ∈ Formalism.L2.Herm.intAf F E := by
  have hs : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) ↔ ∀ i, z i ∈ Formalism.L2.Herm.intAf F E :=
    fun z => mem_latS_std z
  have he : (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) :=
    (hs _).2 fun i => by
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
  constructor
  · have h1 : (s : Matrix (Fin n) (Fin n) _) *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) := by
      refine (h _).2 ?_
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    simpa [Matrix.mulVec_single] using (hs _).1 h1 i
  · simpa [Matrix.mulVec_single] using (hs _).1 ((h _).1 he) i

theorem carries_mul {g s : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {N : Submodule (𝓞 E) (Sp E n)}
    (hg : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N)
    (hs : Formalism.L2.Herm.Carries s (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n)) :
    Formalism.L2.Herm.Carries (g * s) (Formalism.L2.Col.stdLat E n) N := fun x => by
  rw [hg x, hs, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

theorem carries_cancel {g s : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {N : Submodule (𝓞 E) (Sp E n)}
    (hg : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N)
    (hgs : Formalism.L2.Herm.Carries (g * s) (Formalism.L2.Col.stdLat E n) N) :
    Formalism.L2.Herm.Carries s (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) := fun x => by
  have h1 := hg ((g : Matrix (Fin n) (Fin n) _) *ᵥ x)
  have h2 := hgs ((g : Matrix (Fin n) (Fin n) _) *ᵥ x)
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h1
  rw [h1] at h2
  rw [h2, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Units.val_mul (g⁻¹), inv_mul_cancel,
    Units.val_one, Matrix.mul_one]

end Gen

end GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm

open GlobalTheory.Mem.Col2.LevRead

section Gen2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {n : ℕ}

theorem pullV_int {g : GL (Fin n) (AfE F E)} {N : Submodule (𝓞 E) (Sp E n)}
    (hg : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N) {x : Sp E n} (hx : x ∈ N) (i : Fin n) :
    Col2.pullV g x i ∈ RInt F E := by
  have h1 : (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) N :=
    Submodule.subset_span ⟨x, hx, rfl⟩
  exact (mem_latS_std _).1 ((hg _).1 h1) i

theorem pullV_le {g : GL (Fin n) (AfE F E)} {N : Submodule (𝓞 E) (Sp E n)}
    (hg : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N) {x : Sp E n} (hx : x ∈ N) (P : HeightOneSpectrum (𝓞 E))
    (i : Fin n) : Valued.v (adAt F P (Col2.pullV g x i)) ≤ 1 :=
  (mem_rInt_iff F E _).1 (pullV_int hg hx i) P

theorem exists_near {g : GL (Fin n) (AfE F E)} {N : Submodule (𝓞 E) (Sp E n)}
    (hg : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N) (P : HeightOneSpectrum (𝓞 E)) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := F) N, ∃ x ∈ N, ∀ i, Valued.v (adAt F P
      ((((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i - Col2.pullV g x i)) < 1 := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, fun i => by simp [Col2.pullV]⟩
  | zero =>
    refine ⟨0, zero_mem _, fun i => ?_⟩
    have : (fun k : Fin n => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((0 : Sp E n) k)) = 0 := by
      funext k; simp
    have h0 : Col2.pullV g (0 : Sp E n) = 0 := by
      unfold Col2.pullV
      rw [this]
      exact Matrix.mulVec_zero _
    have h1 : (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ (0 : Fin n → AfE F E)) = 0 :=
      Matrix.mulVec_zero _
    erw [h1, h0]
    simp
  | add y y' _ _ ih ih' =>
    obtain ⟨x, hx, h⟩ := ih
    obtain ⟨x', hx', h'⟩ := ih'
    refine ⟨x + x', add_mem hx hx', fun i => ?_⟩
    have e : (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ (y + y')) i - Col2.pullV g (x + x') i =
        ((((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ y) i - Col2.pullV g x i) +
        ((((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ y') i - Col2.pullV g x' i) := by
      have : (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((x + x') i)) =
          (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) +
          (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x' i)) := by
        funext k; simp
      have e0 : Col2.pullV g (x + x') i = Col2.pullV g x i + Col2.pullV g x' i := by
        simp only [Col2.pullV]
        rw [this, Matrix.mulVec_add, Pi.add_apply]
      rw [e0, Matrix.mulVec_add, Pi.add_apply]
      ring
    rw [e, map_add]
    exact Valuation.map_add_lt _ (h i) (h' i)
  | smul a y _ ih =>
    obtain ⟨x, hx, h⟩ := ih
    obtain ⟨c, r, rfl, hr⟩ := exists_hasRes (F := F) (P := P) (z := (a : AfE F E)) ((mem_rInt_iff F E _).1 a.2 P)
    refine ⟨r • x, N.smul_mem r hx, fun i => ?_⟩
    have e1 : Col2.pullV g (r • x) i =
        Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E r) * Col2.pullV g x i := by
      have : (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((r • x) i)) =
          Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E r) •
            (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) := by
        funext k; simp [Algebra.smul_def]
      simp only [Col2.pullV]
      rw [this, Matrix.mulVec_smul]
      rfl
    have e2 : (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ (a • y)) i =
        (a : AfE F E) * (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ y) i := by
      have : a • y = (a : AfE F E) • y := rfl
      rw [this, Matrix.mulVec_smul]
      rfl
    rw [e1, e2]
    have e : (a : AfE F E) * (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ y) i -
        Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E r) * Col2.pullV g x i =
        (a : AfE F E) * ((((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ y) i - Col2.pullV g x i) +
        ((a : AfE F E) - Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E r)) * Col2.pullV g x i := by
      ring
    rw [e, map_add]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul, map_mul]
      exact (mul_le_of_le_one_left' ((mem_rInt_iff F E _).1 a.2 P)).trans_lt (h i)
    · rw [map_mul, map_mul, map_sub, adAt_inclE]
      exact (mul_le_of_le_one_right' (pullV_le hg hx P i)).trans_lt hr

theorem exists_single {g : GL (Fin n) (AfE F E)} {N : Submodule (𝓞 E) (Sp E n)}
    (hg : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N) (P : HeightOneSpectrum (𝓞 E)) (j : Fin n) :
    ∃ x ∈ N, ∀ i, HasRes P (adAt F P (Col2.pullV g x i)) (if i = j then 1 else 0) := by
  have hz : ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) ∈ Formalism.L2.Herm.hatL (F := F) N := by
    refine (hg _).2 ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    refine (mem_latS_std _).2 fun i => ?_
    rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  obtain ⟨x, hx, h⟩ := exists_near hg P _ hz
  refine ⟨x, hx, fun i => ⟨if i = j then 1 else 0, by split_ifs <;> simp, ?_⟩⟩
  have h1 := h i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, Pi.single_apply] at h1
  rw [Valuation.map_sub_swap]
  convert h1 using 3
  split_ifs <;> simp

theorem apply_eq_sum (f : Sp E n ≃ₗ[E] Sp E n) (v : Sp E n) (i : Fin n) :
    f v i = ∑ k, f (Pi.single k 1) i * v k := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Pi.single k (v k) : Sp E n) = v k • Pi.single k 1 by
    ext m
    by_cases h : m = k <;> simp [h], map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

end Gen2

end GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm

open GlobalTheory.Mem.Col2.LevRead

section Gen3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem entries_le {s : GL (Fin n) (AfE F E)}
    (h : Formalism.L2.Herm.Carries s (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n)) (P : HeightOneSpectrum (𝓞 E)) (i j : Fin n) :
    Valued.v (adAt F P ((s : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1 ∧
      Valued.v (adAt F P (((s⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1 :=
  ⟨(mem_rInt_iff F E _).1 (entries_int h i j).1 P, (mem_rInt_iff F E _).1 (entries_int h i j).2 P⟩

theorem exists_isRed_inv {s : GL (Fin n) (AfE F E)}
    (h : Formalism.L2.Herm.Carries s (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n)) (P : HeightOneSpectrum (𝓞 E)) :
    ∃ A : GL (Fin n) (𝓞 E ⧸ P.asIdeal), IsRed P s⁻¹ A :=
  exists_isRed (fun i j => (entries_le h P i j).2) fun i j => by rw [inv_inv]; exact (entries_le h P i j).1

theorem fr_smul (p : DecoF E n ST SG Q) (h : GLG E n SG) (θ : GLQ E n Q) (P : Q) (v : Sp E n) :
    (((1, h, θ) : UF E n × GLG E n SG × GLQ E n Q) • p).fr P v = p.fr P ((((θ P)⁻¹ : ↥(GLint E n P.1)).1) v) := rfl

theorem adAt_mul_fr {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (hg : IsPtOf hc g p) (θ : GLQ E n Q) (P : Q)
    (i j : Fin n) :
    algebraMap E (P.1.adicCompletion E) (p.fr P ((((θ P)⁻¹ : ↥(GLint E n P.1)).1) (Pi.single j 1)) i) =
      ∑ k, adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i k) *
        algebraMap E _ ((((θ P)⁻¹ : ↥(GLint E n P.1)).1) (Pi.single j 1) k) := by
  rw [apply_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, hg.fr P i k]

theorem conds_of_pts {g s : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {h : GLG E n SG} {θ : GLQ E n Q}
    (hg : IsPtOf hc g p) (hq : IsPtOf hc (g * s) (((1, h, θ) : UF E n × GLG E n SG × GLQ E n Q) • p)) :
    (s ∈ Formalism.L2.Herm.UstdAf hc n ∧ Formalism.L2.Herm.Carries s (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) ∧
      (∀ (P : ST) (r j : Fin n), r.1 + 1 = n →
        HasRes P.1 (adAt F P.1 ((s⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then 1 else 0)) ∧
      ∀ (w : SG) (r j : Fin n), HasRes w.1 (adAt F w.1 ((s⁻¹ : GL (Fin n) (AfE F E)).1 r j)) ((h w).1 r j)) ∧
    ∀ (P : Q) (r j : Fin n), adAt F P.1 ((s : Matrix (Fin n) (Fin n) _) r j) =
      algebraMap E _ ((((θ P)⁻¹ : ↥(GLint E n P.1)).1) (Pi.single j 1) r) := by
  have hl := hq.lat
  rw [smul_N] at hl
  have hs := carries_cancel hg.lat hl
  refine ⟨⟨?_, hs, fun P r j hr => ?_, fun w r j => ?_⟩, fun P r j => ?_⟩
  · have e : s = g⁻¹ * (g * s) := by group
    rw [e]
    exact mul_mem (inv_mem hg.uni) hq.uni
  · obtain ⟨A, hA⟩ := exists_isRed_inv hs P.1
    obtain ⟨x, hx, hxr⟩ := exists_single hg.lat P.1 j
    have h1 := hasRes_pullV (g := g) (m := s⁻¹) hA hxr r
    rw [inv_inv] at h1
    have h2 := hq.f P x (by rw [smul_N]; exact hx) r hr
    have h3 := hg.f P x hx r hr
    have e1 : p.deco.1.f P x = if r = j then 1 else 0 := h3.unique (hxr r)
    have e2 : (((1, h, θ) : UF E n × GLG E n SG × GLQ E n Q) • p).deco.1.f P x = p.deco.1.f P x := rfl
    have e3 : ((A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.1.asIdeal)) *ᵥ fun i => if i = j then 1 else 0) r =
        (A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.1.asIdeal)) r j := by
      simp [Matrix.mulVec, dotProduct]
    have e4 := h1.unique h2
    rw [e3, e2, e1] at e4
    have h4 := hA r j
    rw [e4] at h4
    convert h4 using 2
    exact eq_comm
  · obtain ⟨A, hA⟩ := exists_isRed_inv hs w.1
    have e := eq_red hg (m := s⁻¹) (by rwa [inv_inv]) w hA
    have h1 := hA r j
    rw [e] at h1
    exact h1
  · set φ : Matrix (Fin n) (Fin n) (AfE F E) →+* Matrix (Fin n) (Fin n) (P.1.adicCompletion E) := (adAt F P.1).mapMatrix
    set T : Matrix (Fin n) (Fin n) (P.1.adicCompletion E) :=
      Matrix.of fun k j => algebraMap E _ ((((θ P)⁻¹ : ↥(GLint E n P.1)).1) (Pi.single j 1) k)
    have hgs : φ ((g * s : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) =
        φ (g : Matrix (Fin n) (Fin n) (AfE F E)) * T := by
      ext i j
      rw [Matrix.mul_apply]
      simp only [φ, T, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      rw [hq.fr P i j, fr_smul, adAt_mul_fr hg θ P i j]
    have hinv : φ ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) * φ (g : Matrix (Fin n) (Fin n) (AfE F E)) = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    have key : φ (s : Matrix (Fin n) (Fin n) (AfE F E)) = T := by
      have e : (s : Matrix (Fin n) (Fin n) (AfE F E)) =
          ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) * ((g * s : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) := by
        rw [← Units.val_mul, inv_mul_cancel_left]
      rw [e, map_mul, hgs, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have := congrFun (congrFun key r) j
    simpa [φ, T] using this

theorem pt_of_conds {g s : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {h : GLG E n SG} {θ : GLQ E n Q}
    (hg : IsPtOf hc g p) (h1 : s ∈ Formalism.L2.Herm.UstdAf hc n)
    (h2 : Formalism.L2.Herm.Carries s (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n))
    (h3 : ∀ (P : ST) (r j : Fin n), r.1 + 1 = n →
        HasRes P.1 (adAt F P.1 ((s⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then 1 else 0))
    (h4 : ∀ (w : SG) (r j : Fin n), HasRes w.1 (adAt F w.1 ((s⁻¹ : GL (Fin n) (AfE F E)).1 r j)) ((h w).1 r j))
    (h5 : ∀ (P : Q) (r j : Fin n), adAt F P.1 ((s : Matrix (Fin n) (Fin n) _) r j) =
      algebraMap E _ ((((θ P)⁻¹ : ↥(GLint E n P.1)).1) (Pi.single j 1) r)) :
    IsPtOf hc (g * s) (((1, h, θ) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  refine ⟨mul_mem hg.uni h1, ?_, fun P x hx r hr => ?_, fun w x hx r => ?_, fun P i j => ?_⟩
  · rw [smul_N]
    exact carries_mul hg.lat h2
  · rw [smul_N] at hx
    obtain ⟨A, hA⟩ := exists_isRed_inv h2 P.1
    choose c hc using fun k => exists_hasRes (pullV_le hg.lat hx P.1 k)
    have k1 := hasRes_pullV (g := g) (m := s⁻¹) hA hc r
    rw [inv_inv] at k1
    have eA : ∀ k, (A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.1.asIdeal)) r k = if k = r then 1 else 0 :=
      fun k => (hA r k).unique (h3 P r k hr)
    have e : ((A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.1.asIdeal)) *ᵥ c) r = c r := by
      simp [Matrix.mulVec, dotProduct, eA]
    have e2 : c r = p.deco.1.f P x := (hc r).unique (hg.f P x hx r hr)
    rw [e, e2] at k1
    exact k1
  · rw [smul_N] at hx
    have k1 := hasRes_pullV (g := g) (m := s⁻¹) (A := (h w).1) (h4 w) (hg.be w x hx) r
    rw [inv_inv] at k1
    exact k1
  · rw [Units.val_mul, Matrix.mul_apply, map_sum, fr_smul, adAt_mul_fr hg θ P i j]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, h5 P k j]

end Gen3

end GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

theorem locMv_iff : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m →
    ∀ (c : (I.stp u a i).Cl) (s : GA B (B.R.N i)) (κ : (I.stp u a i).G c.1),
    LocMv I u a i c s κ ↔ ((I.stp u a i).gam c.1 κ = 1 ∧
      cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ∧
      LocalCondMoveDecoratedLattice u (B.R.N i) s κ.2.1.1 ∧ LocCQ (I.Q a) (B.R.N i) s κ.2.2.1) := by
  intro B X I hI u a i _ c s κ
  have hact : (I.stp u a i).gam c.1 κ = 1 → ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1 =
      ((1, κ.2.1.1, κ.2.2.1) : UF B.fields.E (B.R.N i) × GLG B.fields.E (B.R.N i) (B.primes X).vGs ×
        GLQ B.fields.E (B.R.N i) (I.Q a)) • ((I.stp u a i).rep c).1.1 := fun h1 => by
    have e1 : κ.1 = 1 := Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective (h1.trans (map_one _).symm))
    show ((κ.1, κ.2.1.1, κ.2.2.1) : UF B.fields.E (B.R.N i) × GLG B.fields.E (B.R.N i) (B.primes X).vGs ×
        GLQ B.fields.E (B.R.N i) (I.Q a)) • ((I.stp u a i).rep c).1.1 = _
    rw [e1]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨g, hg⟩ := hI.exists_isPtOf u a ((I.stp u a i).rep c).1.1
    have hq := h3 g hg
    rw [hact h1] at hq
    obtain ⟨⟨k1, k2, k3, k4⟩, k5⟩ := LocForm.conds_of_pts hg hq
    exact ⟨h1, h2, ⟨k1, k2, k3, k4⟩, k5⟩
  · rintro ⟨h1, h2, ⟨k1, k2, k3, k4⟩, k5⟩
    refine ⟨h1, h2, fun g hg => ?_⟩
    rw [hact h1]
    exact LocForm.pt_of_conds hg k1 k2 k3 k4 k5

end GlobalTheory.Mem.Col2.TC.ChTw.Match
