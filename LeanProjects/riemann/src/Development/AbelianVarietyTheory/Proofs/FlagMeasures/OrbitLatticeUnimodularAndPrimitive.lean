import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisBis
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrb.Basic

section Gen

variable {E V : Type*} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

theorem exists_smul_mem_lat (Λ : Submodule (𝓞 E) V) (hL : Submodule.IsLattice E Λ) (v : V) :
    ∃ o : 𝓞 E, o ≠ 0 ∧ o • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.NonzeroSmulMemSpanLattice.exists_ne_zero_smul_mem
  | exact _root_.GlobalTheory.NonzeroSmulMemSpanLattice.exists_ne_zero_smul_mem
  | (apply _root_.GlobalTheory.NonzeroSmulMemSpanLattice.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroSmulMemSpanLattice.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroSmulMemSpanLattice.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroSmulMemSpanLattice.exists_ne_zero_smul_mem ..)

end Gen

variable {D : D7}

theorem hT_span_left {ι : Type*} (v : ι → (VS D).V) (w : (VS D).V) (h : ∀ a, (VS D).hT (v a) w = 0)
    {y : (VS D).V} (hy : y ∈ Submodule.span D.host.E (Set.range v)) : (VS D).hT y w = 0 := by
  have hle : Submodule.span D.host.E (Set.range v) ≤ LinearMap.ker ((VS D).hT.flip w) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simpa using h a
  simpa using hle hy

theorem hT_span_right {ι : Type*} (v : ι → (VS D).V) (w : (VS D).V) (h : ∀ a, (VS D).hT w (v a) = 0)
    {y : (VS D).V} (hy : y ∈ Submodule.span D.host.E (Set.range v)) : (VS D).hT w y = 0 := by
  have hle : Submodule.span D.host.E (Set.range v) ≤ LinearMap.ker ((VS D).hT w) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact h a
  exact hle hy

theorem latSpan_le {r : ℕ} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (v : Fin r → (VS D).V) :
    Formalism.L2.SG.Saturated.latSpan aa v ≤ (Submodule.span D.host.E (Set.range v)).restrictScalars (𝓞 D.host.E) := by
  unfold Formalism.L2.SG.Saturated.latSpan
  rw [Submodule.span_le]
  rintro _ ⟨a, x, -, rfl⟩
  exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)

variable (X : HidaSetting D)

theorem hT_fe (a b : Fin D.R.rS) : (VS D).hT (X.fY b) (X.eX a) = if a = b then 1 else 0 := by
  rw [a_herm, X.ef]
  split_ifs <;> simp

theorem fixed_frame_span (u : D.what₂.Word) : (GlobalTheory.TypeAsm.F0 X u).X = Submodule.span D.host.E (Set.range X.eX) := by
  unfold GlobalTheory.TypeAsm.F0 Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  have h : (fun b : Fin D.R.rS => (GlobalTheory.TypeAsm.frF (lf D (X.Fu u)).fl (GlobalTheory.TypeAsm.tu_ne D u)).e b.castSucc)
      = X.eX := funext fun b => by
    rw [← X.Fu_e u]
    exact GlobalTheory.TypeAsm.fv_cast _ b
  rw [h]
  congr 1
  ext x
  simp

def pr : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ a, ((VS D).hT (X.fY a)).smulRight (X.eX a) - ∑ a, ((VS D).hT (X.eX a)).smulRight (X.fY a)

theorem pr_apply (v : (VS D).V) :
    pr X v = v - ∑ a, (VS D).hT (X.fY a) v • X.eX a - ∑ a, (VS D).hT (X.eX a) v • X.fY a := by
  simp [pr, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]

theorem pr_mem (v : (VS D).V) : pr X v ∈ Wb X := by
  rw [mem_Wb]
  intro b
  constructor
  · rw [pr_apply]
    simp only [map_sub, map_sum, map_smul, X.ee, X.ef, smul_eq_mul, mul_zero, Finset.sum_const_zero, sub_zero,
      mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
  · rw [pr_apply]
    simp only [map_sub, map_sum, map_smul, X.ff, hT_fe, smul_eq_mul, mul_zero, Finset.sum_const_zero, sub_zero,
      mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]

theorem pr_eX (c : Fin D.R.rS) : pr X (X.eX c) = 0 := by
  rw [pr_apply]
  simp only [hT_fe, X.ee, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const_zero, sub_zero, sub_self]

theorem pr_X {x : (VS D).V} (hx : x ∈ Submodule.span D.host.E (Set.range X.eX)) : pr X x = 0 := by
  have hle : Submodule.span D.host.E (Set.range X.eX) ≤ LinearMap.ker (pr X) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact pr_eX X a
  exact hle hx

theorem pr_Wb {w : (VS D).V} (hw : w ∈ Wb X) : pr X w = w := by
  rw [mem_Wb] at hw
  rw [pr_apply]
  simp [(hw _).1, (hw _).2]

def pW : (VS D).V →ₗ[D.host.E] Wb X := LinearMap.codRestrict (Wb X) (pr X) (pr_mem X)

theorem pW_coe (v : (VS D).V) : ((pW X v : Wb X) : (VS D).V) = pr X v := rfl

end GlobalTheory.RowsOrb.Basic

namespace GlobalTheory.RowsOrb.Basic
variable {D : D7} (X : HidaSetting D)

theorem mem_XO (u : D.what₂.Word) (x : (VS D).V) :
    x ∈ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X ↔ x ∈ Submodule.span D.host.E (Set.range X.eX) := by
  rw [← fixed_frame_span X u]
  rfl

theorem lmap_isLattice (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : Submodule.IsLattice D.host.E Λ) : Submodule.IsLattice D.host.E (Lmap X u Λ) := by
  refine ⟨?_, ?_⟩
  · have hfg : (Λ.map ((pW X).restrictScalars (𝓞 D.host.E))).FG := hΛ.fg.map _
    haveI : Module.Finite (𝓞 D.host.E) (Λ.map ((pW X).restrictScalars (𝓞 D.host.E))) := Module.Finite.iff_fg.2 hfg
    haveI : IsNoetherian (𝓞 D.host.E) (Λ.map ((pW X).restrictScalars (𝓞 D.host.E))) :=
      isNoetherian_of_isNoetherianRing_of_finite _ _
    refine Submodule.FG.of_le_of_isNoetherian (T := Λ.map ((pW X).restrictScalars (𝓞 D.host.E))) ?_
    intro w hw
    rw [mem_Lmap] at hw
    obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.1 hw
    refine ⟨l, hl, ?_⟩
    apply Subtype.ext
    change pr X l = (w : (VS D).V)
    have hx0 : pr X x = 0 := pr_X X ((mem_XO X u x).1 hx)
    calc pr X l = pr X (l + x) := by rw [map_add, hx0, add_zero]
      _ = pr X w := by rw [hlx]
      _ = w := pr_Wb X w.2
  · rw [eq_top_iff]
    intro w _
    obtain ⟨o, ho, hmem⟩ := exists_smul_mem_lat Λ hΛ (w : (VS D).V)
    have h1 : o • w ∈ Lmap X u Λ := by
      rw [mem_Lmap]
      exact Submodule.mem_sup_left hmem
    have ho' : ((o : D.host.E)) ≠ 0 := by simpa using ho
    have e : w = ((o : D.host.E)⁻¹) • (o • w) := by
      rw [← algebraMap_smul D.host.E o w, smul_smul]
      have : (o : D.host.E)⁻¹ * algebraMap (𝓞 D.host.E) D.host.E o = 1 := inv_mul_cancel₀ ho'
      rw [this, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

end GlobalTheory.RowsOrb.Basic

namespace GlobalTheory.RowsOrb.Basic
variable {D : D7} (X : HidaSetting D)

theorem mem_orth_iff (U : Submodule D.host.E (VS D).V) (v : (VS D).V) :
    v ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem lmap_prim (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hF : FixedHyp D Λ (lf D (X.Fu u))) (t : D.host.E) :
    t • zb X u ∈ Lmap X u Λ ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  rw [mem_Lmap, Submodule.coe_smul, zb_coe, Submodule.mem_one]
  have hXsp : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range X.eX) := by
    show (X.Fu u).X = _
    rw [FlagG.X, X.Fu_e]
  have hz : (lf D (X.Fu u)).fl.z = X.zu u := X.flagZVector u
  constructor
  · intro h
    obtain ⟨l, hl, x, hx, hsum⟩ := Submodule.mem_sup.1 h
    have hxX := (mem_XO X u x).1 hx
    have hzo : t • X.zu u ∈ orth (VS D) (Submodule.span D.host.E (Set.range X.eX)) := by
      rw [mem_orth_iff]
      intro y hy
      rw [map_smul]
      rw [hT_span_left X.eX (X.zu u) (fun a => (X.zu_orth u a).1) hy, smul_zero]
    have hxo : x ∈ orth (VS D) (Submodule.span D.host.E (Set.range X.eX)) := by
      rw [mem_orth_iff]
      intro y hy
      exact hT_span_left X.eX x (fun a => hT_span_right X.eX (X.eX a) (fun b => X.ee a b) hxX) hy
    have hl' : l = t • X.zu u - x := by rw [← hsum, add_sub_cancel_right]
    have hlo : l ∈ orth (VS D) (Submodule.span D.host.E (Set.range X.eX)) := by
      rw [hl']; exact Submodule.sub_mem _ hzo hxo
    have hmem : t • (lf D (X.Fu u)).fl.z ∈ Lsub Λ (lf D (X.Fu u)) := by
      rw [hz]
      unfold Lsub Lrep
      rw [hXsp]
      refine Submodule.mem_inf.2 ⟨?_, hzo⟩
      rw [← hsum]
      exact Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨hl, hlo⟩) hxX
    obtain ⟨o, ho⟩ := hF.2.2.2.2 t hmem
    exact ⟨o, ho⟩
  · rintro ⟨o, rfl⟩
    apply Submodule.mem_sup_left
    have hzΛ : X.zu u ∈ Λ := by
      have := hF.2.2.1.1
      rwa [hz] at this
    rw [algebraMap_smul]
    exact Λ.smul_mem o hzΛ

end GlobalTheory.RowsOrb.Basic

namespace GlobalTheory.RowsOrb.Basic
variable {D : D7} (X : HidaSetting D)

theorem mem_hdual_iff {W : Type} [AddCommGroup W] [Module D.host.E W] [Module (𝓞 D.host.E) W]
    [IsScalarTower (𝓞 D.host.E) D.host.E W] (h : W →ₗ⋆[D.host.E] W →ₗ[D.host.E] D.host.E)
    (L : Submodule (𝓞 D.host.E) W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem lmap_unimod (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ Y.what₂ u) :
    Formalism.HermitianLatticesTheory.IsUnimodular (hb X) (Lmap X u Λ) := by
  have hrow := (Y.rowsOK u).1 Λ hΛ
  have hU : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hrow.2.1.2.1
  have memΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, (VS D).hT y x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro x
    rw [← mem_hdual_iff, hU]
  obtain ⟨f, L, hff, hef, hL, hz, hΛeq⟩ := Y.split u Λ hΛ
  simp only [X.Fu_e] at hef hL
  rw [X.Fu_e] at hΛeq
  unfold Formalism.HermitianLatticesTheory.IsUnimodular
  apply le_antisymm
  · intro w hw
    rw [mem_hdual_iff] at hw
    have hwW := (mem_Wb X _).1 w.2
    obtain ⟨w', hw'⟩ : ∃ w' : (VS D).V, w' = (w : (VS D).V) - ∑ a, (VS D).hT (f a) w • X.eX a := ⟨_, rfl⟩
    have hfe : ∀ a b, (VS D).hT (f b) (X.eX a) = if a = b then 1 else 0 := by
      intro a b
      rw [a_herm, hef]
      split_ifs <;> simp
    have hw'f : ∀ b, (VS D).hT (f b) w' = 0 := by
      intro b
      rw [hw']
      simp only [map_sub, map_sum, map_smul, hfe, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    have hw'e : ∀ b, (VS D).hT (X.eX b) w' = 0 := by
      intro b
      rw [hw']
      simp only [map_sub, map_sum, map_smul, X.ee, (hwW b).1, smul_eq_mul, mul_zero, Finset.sum_const_zero,
        sub_zero]
    have hw'Λ : w' ∈ Λ := by
      rw [memΛ]
      intro y hy
      rw [hΛeq] at hy
      obtain ⟨y1, hy1, y3, hy3, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨y0, hy0, l, hl, rfl⟩ := Submodule.mem_sup.1 hy1
      have h0 : (VS D).hT y0 w' = 0 := hT_span_left X.eX w' hw'e (latSpan_le (Formalism.L2.SG.Saturated.aaS D) X.eX hy0)
      have h3 : (VS D).hT y3 w' = 0 := hT_span_left f w' hw'f (latSpan_le (fun a => (Formalism.L2.SG.Saturated.aaS D a)⁻¹) f hy3)
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, h0, h3, zero_add, add_zero]
      have hle : ∀ a, (VS D).hT l (X.eX a) = 0 := by
        intro a; rw [a_herm, (hL l hl a).1, star_zero]
      have e1 : (VS D).hT l w' = (VS D).hT l w := by
        rw [hw']
        simp only [map_sub, map_sum, map_smul, hle, smul_zero, Finset.sum_const_zero, sub_zero]
      have hpl : pW X l ∈ Lmap X u Λ := by
        rw [mem_Lmap, pW_coe, pr_apply]
        have e0 : ∑ a, (VS D).hT (X.eX a) l • X.fY a = 0 := by
          simp only [(hL l hl _).1, zero_smul, Finset.sum_const_zero]
        rw [e0, sub_zero]
        refine Submodule.sub_mem_sup ?_ ?_
        · rw [hΛeq]
          exact Submodule.mem_sup_left (Submodule.mem_sup_right hl)
        · rw [mem_XO]
          exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      have h2 := hw _ hpl
      rw [hb_apply, pW_coe, pr_apply] at h2
      have e2 : (VS D).hT (l - ∑ a, (VS D).hT (X.fY a) l • X.eX a - ∑ a, (VS D).hT (X.eX a) l • X.fY a) w =
          (VS D).hT l w := by
        simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply,
          LinearMap.map_smulₛₗ, LinearMap.smul_apply, (hwW _).1, (hwW _).2, smul_zero, Finset.sum_const_zero,
          sub_zero]
      rw [e1, ← e2]
      exact h2
    show (w : (VS D).V) ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X
    have e3 : (w : (VS D).V) = w' + ∑ a, (VS D).hT (f a) w • X.eX a := by rw [hw', sub_add_cancel]
    rw [e3]
    refine Submodule.add_mem_sup hw'Λ ?_
    rw [mem_XO]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro w hw
    rw [mem_hdual_iff]
    intro y hy
    rw [hb_apply]
    rw [mem_Lmap] at hw hy
    obtain ⟨l1, hl1, x1, hx1, h1⟩ := Submodule.mem_sup.1 hy
    obtain ⟨l2, hl2, x2, hx2, h2⟩ := Submodule.mem_sup.1 hw
    have hx1' := (mem_XO X u x1).1 hx1
    have hx2' := (mem_XO X u x2).1 hx2
    have hyW := (mem_Wb X _).1 y.2
    have hwW := (mem_Wb X _).1 w.2

    have ea : (VS D).hT x1 w = 0 := hT_span_left X.eX w (fun a => (hwW a).1) hx1'

    have eb : (VS D).hT (y : (VS D).V) x2 = 0 :=
      hT_span_right X.eX _ (fun a => by rw [a_herm, (hyW a).1, star_zero]) hx2'
    have ec : (VS D).hT x1 x2 = 0 :=
      hT_span_left X.eX x2 (fun a => hT_span_right X.eX (X.eX a) (fun b => X.ee a b) hx2') hx1'
    have ed : (VS D).hT l1 x2 = 0 := by
      have := eb; rw [← h1, map_add, LinearMap.add_apply, ec, add_zero] at this; exact this
    have key : (VS D).hT (y : (VS D).V) w = (VS D).hT l1 l2 := by
      rw [← h1, map_add, LinearMap.add_apply, ea, add_zero, ← h2, map_add, ed, add_zero]
    rw [key]
    exact (memΛ l2).1 hl2 l1 hl1

end GlobalTheory.RowsOrb.Basic

namespace GlobalTheory.RowsOrb.Basic

theorem lmap_basic : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    GlobalTheory.TypeAsm.Std D large₂ → ∀ Λ ∈ Y.what₂ u, Submodule.IsLattice D.host.E (GlobalTheory.RowsOrb.Lmap X u Λ) ∧
      Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) (GlobalTheory.RowsOrb.Lmap X u Λ) ∧
      ∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ GlobalTheory.RowsOrb.Lmap X u Λ ↔
        t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  intro D large₂ X Y u _ Λ hΛ
  have hF : FixedHyp D Λ (lf D (X.Fu u)) := ((Y.rowsOK u).1 Λ hΛ).2.1
  exact ⟨lmap_isLattice X u Λ hF.1, lmap_unimod X Y u Λ hΛ, lmap_prim X u Λ hF⟩

end GlobalTheory.RowsOrb.Basic
