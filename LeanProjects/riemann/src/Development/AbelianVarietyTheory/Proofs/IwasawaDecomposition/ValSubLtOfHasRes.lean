import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.PtStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_of_sub {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P a c) (hab : Valued.v (a - b) < 1) : HasRes P b c := by
  obtain ⟨r, hr, hv⟩ := h
  refine ⟨r, hr, ?_⟩
  have e : b - algebraMap E _ (algebraMap (𝓞 E) E r) = (a - algebraMap E _ (algebraMap (𝓞 E) E r)) - (a - b) := by ring
  rw [e]
  exact Valuation.map_sub_lt _ hv hab

theorem val_sub_lt_of_hasRes {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P a c) (h' : HasRes P b c) : Valued.v (a - b) < 1 := by
  obtain ⟨r, hr, hv⟩ := h
  obtain ⟨r', hr', hv'⟩ := h'
  have hmem : r - r' ∈ P.asIdeal := Ideal.Quotient.eq.1 (hr.trans hr'.symm)
  have e : a - b = (a - algebraMap E _ (algebraMap (𝓞 E) E r)) - (b - algebraMap E _ (algebraMap (𝓞 E) E r')) +
      algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r - r')) := by
    simp only [map_sub]
    ring
  rw [e]
  refine Valuation.map_add_lt _ (Valuation.map_sub_lt _ hv hv') ?_
  rw [valued_algebraMap]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hmem

theorem val_sub_lt_of_hatL {n : ℕ} (a b : Matrix (Fin n) (Fin n) (AfE F E)) (P : HeightOneSpectrum (𝓞 E)) (i : Fin n)
    {N : Submodule (𝓞 E) (Fin n → E)}
    (h : ∀ y ∈ N, Valued.v (adAt F P ((a *ᵥ fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y j)) i -
      (b *ᵥ fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y j)) i)) < 1)
    {z : Fin n → AfE F E} (hz : z ∈ Formalism.L2.Herm.hatL (F := F) N) :
    Valued.v (adAt F P ((a *ᵥ z) i - (b *ᵥ z) i)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact h v hv
  | zero => simp
  | add x y _ _ hx hy =>
    have e : (a *ᵥ (x + y)) i - (b *ᵥ (x + y)) i = ((a *ᵥ x) i - (b *ᵥ x) i) + ((a *ᵥ y) i - (b *ᵥ y) i) := by
      simp only [Matrix.mulVec_add, Pi.add_apply]
      ring
    rw [e, map_add (adAt F P)]
    exact Valuation.map_add_lt _ hx hy
  | smul c x _ hx =>
    have e0 : c • x = (c : AfE F E) • x := rfl
    have e : (a *ᵥ (c • x)) i - (b *ᵥ (c • x)) i = (c : AfE F E) * ((a *ᵥ x) i - (b *ᵥ x) i) := by
      rw [e0, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      ring
    rw [e, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((mem_rInt_iff F E _).1 c.2 P)) hx

variable [StarRing E] {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem pullV_mul_stab (g g' h : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (h * (g⁻¹ * g')) x =
      ((g'⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x) := by
  unfold GlobalTheory.Mem.Col2.pullV
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_inv, mul_assoc]

theorem pullV_eq_of_mul (g h : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV h x = ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
                 ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x) := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem val_sub_pullV_lt {g g' h : GL (Fin n) (AfE F E)} {p q : DecoF E n ST SG Q}
    (hg : IsPtOf hc g p) (hh : IsPtOf hc h q) {P : HeightOneSpectrum (𝓞 E)} (i : Fin n)
    (hP : ∀ y ∈ p.deco.1.N, Valued.v (adAt F P (GlobalTheory.Mem.Col2.pullV g y i - GlobalTheory.Mem.Col2.pullV g' y i)) < 1)
    {x : Sp E n} (hx : x ∈ q.deco.1.N) :
    Valued.v (adAt F P (GlobalTheory.Mem.Col2.pullV h x i - GlobalTheory.Mem.Col2.pullV (h * (g⁻¹ * g')) x i)) < 1 := by
  have hu : GlobalTheory.Mem.Col2.pullV h x ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) :=
    (hh.lat _).1 (Submodule.subset_span ⟨x, hx, rfl⟩)
  have hz : (g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N := by
    refine (hg.lat _).2 ?_
    rwa [← pullV_eq_of_mul]
  have := val_sub_lt_of_hatL _ _ P i (fun y hy => hP y hy) hz
  rwa [← pullV_eq_of_mul, ← pullV_mul_stab] at this

theorem isPtOf_mul_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), ∀ (g g' h : GL (Fin n) (AfE F E)) (p q : DecoF E n ST SG Q), IsPtOf hc g p → IsPtOf hc g' p → IsPtOf hc h q → IsPtOf hc (h * (g⁻¹ * g')) q := by
  intro F E _ _ _ _ _ _ hc n ST SG Q g g' h p q hg hg' hh
  refine ⟨mul_mem hh.uni (mul_mem (inv_mem hg.uni) hg'.uni), fun x => ?_, fun P x hx i hi => ?_, fun w x hx i => ?_,
    fun P i j => ?_⟩
  · have e : (((h * (g⁻¹ * g'))⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x =
        ((g'⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (((h⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x)) := by
      simp only [Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [e, hh.lat x, ← hg'.lat, hg.lat, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  · refine hasRes_of_sub (hh.f P x hx i hi) ?_
    rw [← map_sub]
    refine val_sub_pullV_lt hg hh i (fun y hy => ?_) hx
    rw [map_sub]
    exact val_sub_lt_of_hasRes (hg.f P y hy i hi) (hg'.f P y hy i hi)
  · refine hasRes_of_sub (hh.be w x hx i) ?_
    rw [← map_sub]
    refine val_sub_pullV_lt hg hh i (fun y hy => ?_) hx
    rw [map_sub]
    exact val_sub_lt_of_hasRes (hg.be w y hy i) (hg'.be w y hy i)
  · have hgg : (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) =
        (g' : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) := by
      ext a b
      simp only [Matrix.map_apply]
      rw [hg.fr, hg'.fr]
    have hs : (((g⁻¹ * g' : GL (Fin n) (AfE F E))) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) = 1 := by
      rw [Units.val_mul, Matrix.map_mul, ← hgg, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have e : adAt F P.1 (((h * (g⁻¹ * g') : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        ((((h * (g⁻¹ * g') : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))).map (adAt F P.1)) i j := rfl
    rw [e, Units.val_mul, Matrix.map_mul, hs, mul_one, Matrix.map_apply]
    exact hh.fr P i j

end GlobalTheory.Mem.Col2.PtStab

end
