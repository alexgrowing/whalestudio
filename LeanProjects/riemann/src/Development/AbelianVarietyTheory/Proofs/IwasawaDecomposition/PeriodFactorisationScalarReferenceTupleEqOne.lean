import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowE
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
noncomputable section

namespace GlobalTheory.Mem.R3.Rw.NumDef

section Gen

variable {R : Ranks} (D : Rows.Data R)

def buSec (u : D.Word) (φ : D.Mu u) (x : D.EE) : ℂ := D.perCol u D.mu0 φ (D.sec D.mu0 x)

def lamTrace (μ : D.Tup) (j : ℕ) (π : D.FT) : ℝ :=
  (LinearMap.trace ℂ (D.Mj j)
    (D.thetaP μ j ∘ₗ D.thetaT μ j ∘ₗ ((D.isot j π).starProjection : D.Mj j →ₗ[ℂ] D.Mj j))).re /
    (Module.finrank ℂ (D.isot j π) : ℝ)

def ZeFact (u : D.Word) (μ : D.Tup) (c : ℂ) : Prop :=
  (∀ (φ : D.Mu u) (F : D.Amb μ), F ∈ D.V0 μ →
    D.perCol u μ φ F = c * buSec D u φ (D.iota μ ((D.Qsp μ).starProjection F))) ∧
  ∃ (φ : D.Mu u) (F : D.Amb μ), F ∈ D.V0 μ ∧ D.perCol u μ φ F ≠ 0

theorem ZeFact.unique {D : Rows.Data R} {u : D.Word} {μ : D.Tup} {c c' : ℂ} (h : ZeFact D u μ c)
    (h' : ZeFact D u μ c') : c = c' := by
  obtain ⟨φ, F, hF, hne⟩ := h.2
  have e1 := h.1 φ F hF
  have e2 := h'.1 φ F hF
  have hb : buSec D u φ (D.iota μ ((D.Qsp μ).starProjection F)) ≠ 0 := fun h0 => hne (by rw [e1, h0, mul_zero])
  exact mul_right_cancel₀ hb (e1.symm.trans e2)

theorem ZeFact.mu0 {D : Rows.Data R} {u : D.Word} {c : ℂ} (h : ZeFact D u D.mu0 c) : c = 1 := by
  obtain ⟨φ, F, hF, hne⟩ := h.2
  have hq : (D.Qsp D.mu0).starProjection F ∈ D.Qsp D.mu0 := (D.Qsp D.mu0).starProjection_apply_mem F
  have e1 := h.1 φ F hF
  have e2 := h.1 φ _ hq.1
  rw [Submodule.starProjection_eq_self_iff.2 hq] at e2
  unfold buSec at e1 e2
  rw [D.sec_iota _ _ hq] at e1 e2
  have hb : D.perCol u D.mu0 φ ((D.Qsp D.mu0).starProjection F) ≠ 0 := fun h0 => hne (by rw [e1, h0, mul_zero])
  exact (mul_eq_right₀ hb).1 e2.symm

open Classical in

def zeVal (u : D.Word) (μ : D.Tup) : D.LLˣ :=
  if μ = D.mu0 then 1 else if h : ∃ z : D.LLˣ, ZeFact D u μ (D.embLL (z : D.LL)) then h.choose else 1

theorem periodFactorisationScalar_referenceTuple_eq_one (u : D.Word) : zeVal D u D.mu0 = 1 := by
  unfold zeVal
  exact if_pos rfl

@[reducible] def modLL (μ : D.Tup) (j : ℕ) : Module (𝓞 D.LL) (D.MtL μ j) :=
  Module.compHom _ (algebraMap (𝓞 D.LL) D.LL)

attribute [local instance] modLL

theorem smulLL (μ : D.Tup) (j : ℕ) (s : 𝓞 D.LL) (x : D.MtL μ j) : s • x = (s : D.LL) • x := rfl

def TjLat (μ : D.Tup) (j : ℕ) : Submodule (𝓞 D.LL) (D.MtL μ j) :=
  Submodule.span (𝓞 D.LL) {x | D.jMt μ j x ∈ D.TjSet μ j}

def TjSpan (μ : D.Tup) (j : ℕ) : Submodule D.LL (D.MtL μ j) := Submodule.span D.LL (TjLat D μ j : Set (D.MtL μ j))

def TjDualLat (μ : D.Tup) (j : ℕ) : Submodule (𝓞 D.LL) (D.MtL μ j) where
  carrier := {x | x ∈ TjSpan D μ j ∧ ∀ a ∈ TjLat D μ j, ∃ c : 𝓞 D.LL,
    inner ℂ (D.jMt μ j a) (D.jMt μ j x) = D.embLL (c : D.LL)}
  add_mem' := by
    rintro x y ⟨hx, h1⟩ ⟨hy, h2⟩
    refine ⟨(TjSpan D μ j).add_mem hx hy, fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := h1 a ha
    obtain ⟨d, hd⟩ := h2 a ha
    exact ⟨c + d, by rw [map_add, inner_add_right, hc, hd]; simp⟩
  zero_mem' := ⟨(TjSpan D μ j).zero_mem, fun a _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro s x ⟨hx, h1⟩
    refine ⟨by rw [smulLL]; exact (TjSpan D μ j).smul_mem _ hx, fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := h1 a ha
    exact ⟨s * c, by rw [smulLL, LinearMap.map_smulₛₗ, inner_smul_right, hc]; simp⟩

def jwLat (μ : D.Tup) (j : ℕ) (p : Ideal (𝓞 D.LL)) [p.IsPrime] : ℤ :=
  Formalism.HermitianLatticesTheory.lidx p (TjLat D μ j) (TjDualLat D μ j)

end Gen

end GlobalTheory.Mem.R3.Rw.NumDef

namespace GlobalTheory.Mem.R3.Rw.NumDef

section Can

variable {R : Ranks} (Dd : Rows.Data R)

@[reducible] def modMj (j : ℕ) : Module (𝓞 Dd.LL) (Dd.Mj j) :=
  Module.compHom _ (Dd.embLL.comp (algebraMap (𝓞 Dd.LL) Dd.LL))

attribute [local instance] modMj

theorem smulMj (j : ℕ) (s : 𝓞 Dd.LL) (z : Dd.Mj j) : s • z = Dd.embLL (s : Dd.LL) • z := rfl

def latCan (j : ℕ) : Submodule (𝓞 Dd.LL) (Dd.Mj j) where
  carrier := {z | ∃ c : Dd.Mj j → 𝓞 Dd.LL, z = ∑ v ∈ (Dd.MjLat j).gen, Dd.embLL ((c v : 𝓞 Dd.LL) : Dd.LL) • v}
  add_mem' := by
    rintro a b ⟨c, rfl⟩ ⟨d, rfl⟩
    refine ⟨c + d, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [add_smul]
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro s a ⟨c, rfl⟩
    refine ⟨fun v => s * c v, ?_⟩
    rw [smulMj, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [smul_smul]
    simp

def rngSet (j : ℕ) : Set (Dd.Mj j) := {z | ∃ a : Dd.Mj j → Dd.LL, z = ∑ v ∈ (Dd.MjLat j).gen, Dd.embLL (a v) • v}

attribute [local instance] modLL

def thCan (μ : Dd.Tup) (j : ℕ) : Submodule (𝓞 Dd.LL) (Dd.Mj j) where
  carrier := {z | z ∈ rngSet Dd j ∧ ∃ x ∈ TjLat Dd μ j, z = Dd.thetaP μ j (Dd.jMt μ j x)}
  add_mem' := by
    rintro a b ⟨⟨c, rfl⟩, x, hx, hxa⟩ ⟨⟨d, rfl⟩, y, hy, hyb⟩
    refine ⟨⟨c + d, ?_⟩, x + y, (TjLat Dd μ j).add_mem hx hy, ?_⟩
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp [add_smul]
    · rw [map_add, map_add, ← hxa, ← hyb]
  zero_mem' := ⟨⟨0, by simp⟩, 0, (TjLat Dd μ j).zero_mem, by simp⟩
  smul_mem' := by
    rintro s a ⟨⟨c, rfl⟩, x, hx, hxa⟩
    refine ⟨⟨fun v => (s : Dd.LL) * c v, ?_⟩, s • x, (TjLat Dd μ j).smul_mem s hx, ?_⟩
    · rw [smulMj, Finset.smul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [smul_smul, map_mul]
    · rw [smulLL, LinearMap.map_smulₛₗ, LinearMap.map_smul, ← hxa, smulMj]

def ijCan (μ : Dd.Tup) (j : ℕ) (p : Ideal (𝓞 Dd.LL)) [p.IsPrime] : ℤ :=
  Formalism.HermitianLatticesTheory.lidx p (latCan Dd j) (thCan Dd μ j)

end Can

end GlobalTheory.Mem.R3.Rw.NumDef

namespace GlobalTheory.Mem.R3.Rw.NumDef

section Lidx

variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']

theorem mem_locP (p : Ideal R) [p.IsPrime] (L : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl

theorem localization_map_of_injective (p : Ideal R) [p.IsPrime] (f : W →ₗ[R] W') (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f → y ∈ LinearMap.range f)
    (A : Submodule R W) : Formalism.HermitianLatticesTheory.localization₂ p (A.map f) = (Formalism.HermitianLatticesTheory.localization₂ p A).map f := by
  ext y
  simp only [mem_locP, Submodule.mem_map]
  constructor
  · rintro ⟨s, hs, a, ha, hay⟩
    obtain ⟨x, rfl⟩ := hsat s y hs ⟨a, hay⟩
    refine ⟨x, ⟨s, hs, ?_⟩, rfl⟩
    have : f (s • x) = f a := by rw [map_smul, hay]
    rw [hf this]; exact ha
  · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩
    exact ⟨s, hs, s • x, hx, by rw [map_smul]⟩

theorem length_map_inj (f : W →ₗ[R] W') (hf : Function.Injective f) (X Z : Submodule R W) :
    Module.length R (↥(Z.map f) ⧸ (X.map f).comap (Z.map f).subtype) =
      Module.length R (↥Z ⧸ X.comap Z.subtype) := by
  symm
  refine LinearEquiv.length_eq
    (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf Z) ?_)
  ext ⟨w, hw⟩
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨z', hz'⟩, hz'X, he⟩
    have : f z' = f z := congrArg Subtype.val he
    rw [← hf this]
    exact ⟨z', hz'X, rfl⟩
  · rintro ⟨z', hz'X, he⟩
    refine ⟨⟨z, hz⟩, ?_, ?_⟩
    · have := hf he
      simpa [this] using hz'X
    · rfl

theorem lidx_map_inj (p : Ideal R) [p.IsPrime] (f : W →ₗ[R] W') (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f → y ∈ LinearMap.range f)
    (A B : Submodule R W) : Formalism.HermitianLatticesTheory.lidx p (A.map f) (B.map f) = Formalism.HermitianLatticesTheory.lidx p A B := by
  unfold Formalism.HermitianLatticesTheory.lidx Formalism.HermitianLatticesTheory.locLen
  rw [← Submodule.map_inf f hf, localization_map_of_injective p f hf hsat, localization_map_of_injective p f hf hsat,
    localization_map_of_injective p f hf hsat, length_map_inj f hf, length_map_inj f hf]

end Lidx

section Tr

attribute [local instance] modMj modLL

variable (D : D7) (X : DivX D)

def jMO (j : ℕ) : (X.MjH j).V →ₗ[𝓞 D.what₂.LL] D.what₂.Mj j where
  toFun := X.jM j
  map_add' := map_add _
  map_smul' s x := by
    rw [← algebraMap_smul D.what₂.LL s x, LinearMap.map_smulₛₗ]
    rfl

theorem exists_jM (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (a : D.what₂.Mj j → D.what₂.LL) :
    ∃ x, X.jM j x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL (a v) • v := by
  refine Finset.sum_induction _ (fun z => ∃ x, X.jM j x = z) ?_ ?_ ?_
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  · exact ⟨0, map_zero _⟩
  · intro v hv
    obtain ⟨x, hx⟩ := X.MjLat_sub j h1 h2 v hv
    exact ⟨a v • x, by rw [LinearMap.map_smulₛₗ, hx]⟩

theorem jM_mem_rng (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (y : (X.MjH j).V) : X.jM j y ∈ rngSet D.what₂ j := by
  have hy : y ∈ Submodule.span D.what₂.LL ((X.MjH j).L : Set (X.MjH j).V) := by
    rw [(X.MjH_good j).2.2]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc⟩ := (X.jM_lat j h1 h2 x).1 hx
    exact ⟨fun v => ((c v : 𝓞 D.what₂.LL) : D.what₂.LL), hc⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [map_add, ha, hb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [add_smul]
  | smul r x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨fun v => r * a v, ?_⟩
    rw [LinearMap.map_smulₛₗ, ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [smul_smul, map_mul]

theorem lat_map (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : (X.MjH j).L.map (jMO D X j) = latCan D.what₂ j := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (X.jM_lat j h1 h2 x).1 hx
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨x, hx⟩ := exists_jM D X j h1 h2 (fun v => ((c v : 𝓞 D.what₂.LL) : D.what₂.LL))
    exact ⟨x, (X.jM_lat j h1 h2 x).2 ⟨c, hx⟩, hx⟩

theorem th_map (μ : D.what₂.Tup) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (Idx.thTj X μ j).map (jMO D X j) = thCan D.what₂ μ j := by
  ext z
  constructor
  · rintro ⟨y, ⟨x, hx, hxy⟩, rfl⟩
    exact ⟨jM_mem_rng D X j h1 h2 y, x, hx, hxy⟩
  · rintro ⟨⟨a, ha⟩, x, hx, hxz⟩
    obtain ⟨y, hy⟩ := exists_jM D X j h1 h2 a
    refine ⟨y, ⟨x, hx, ?_⟩, ?_⟩
    · rw [hy, ← ha, hxz]
    · show X.jM j y = z
      rw [hy, ← ha]

theorem ijIdx_eq_can (μ : D.what₂.Tup) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (w : D.what₂.places.Pl) :
    Idx.IjIdx X μ j w = ijCan D.what₂ μ j (D.plEq w).asIdeal := by
  unfold Idx.IjIdx ijCan
  rw [← lat_map D X j h1 h2, ← th_map D X μ j h1 h2, lidx_map_inj _ _ (Idx.jM_inj X j)]
  rintro s y hs ⟨a, ha⟩
  have hs0 : (s : D.what₂.LL) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    rw [this]
    exact zero_mem _
  refine ⟨(s : D.what₂.LL)⁻¹ • a, ?_⟩
  have ha' : X.jM j a = D.what₂.embLL (s : D.what₂.LL) • y := ha
  show X.jM j ((s : D.what₂.LL)⁻¹ • a) = y
  rw [LinearMap.map_smulₛₗ, ha', smul_smul, ← map_mul, inv_mul_cancel₀ hs0, map_one, one_smul]

end Tr

theorem zeOf_eq {R : Ranks} (Dd : Rows.Data R) (u : Dd.Word) (μ : Dd.Tup) (c : ℂ)
    (h : ZeFact Dd u μ c) (hc : ∃ z : Dd.LL, Dd.embLL z = c) :
    Dd.embLL (zeVal Dd u μ : Dd.LL) = c := by
  by_cases hμ : μ = Dd.mu0
  · subst hμ
    rw [periodFactorisationScalar_referenceTuple_eq_one, h.mu0]; simp
  · obtain ⟨z, hz'⟩ := hc
    have hc0 : c ≠ 0 := by
      obtain ⟨φ, F, hF, hne⟩ := h.2
      intro h0
      exact hne (by rw [h.1 φ F hF, h0, zero_mul])
    have hz0 : z ≠ 0 := fun h0 => hc0 (by rw [← hz', h0, map_zero])
    have hex : ∃ z : Dd.LLˣ, ZeFact Dd u μ (Dd.embLL (z : Dd.LL)) :=
      ⟨Units.mk0 z hz0, by simpa [hz'] using h⟩
    unfold zeVal
    rw [if_neg hμ, dif_pos hex]
    exact hex.choose_spec.unique h

end GlobalTheory.Mem.R3.Rw.NumDef

namespace GlobalTheory.Mem.R3.Rw.NumDef

variable {B : Base} {C : Cols B} {G : Type} [Group G]

def nums0 (p : PkB B C G) (W₀ : RowsRest B C) : Nums p W₀ where
  Bu := fun _ _ _ => 0
  linL := fun _ _ => ⟨fun _ _ => (add_zero 0).symm, fun _ _ => (smul_zero _).symm⟩
  linR := fun _ _ => ⟨fun _ _ => (add_zero 0).symm, fun _ _ => (smul_zero _).symm⟩
  ze := fun _ _ => 1
  rowsRest_wordColumnUnit_baseTuple := fun _ => rfl
  lamP := fun _ _ _ => 0
  Ij := fun _ _ _ => 0
  jw := fun _ _ _ => 0

abbrev data0 (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) : Rows.Data B.R :=
  (p.what₂ e W₀ (nums0 p W₀) (fun _ _ => 0) (fun _ _ => le_refl 0)).what₂

theorem periodAgainstColumnForm_referenceTuple_eq (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) (u : B.Word) (φ : W₀.Mu u)
    (F : (p.sA true C.mu0).A.T) :
    perOf p e W₀ u C.mu0 φ F = (C.mem u).P.PtilCol ((W₀.eMu u φ : (C.mem u).A.Mram) :
      (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) ((e.e0 u).symm F) := by
  unfold perOf
  rw [dif_pos rfl]
  rfl

theorem perOf_linL (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) (u : B.Word) (F : (p.sA true C.mu0).A.T) :
    IsLinearMap ℂ (fun φ : W₀.Mu u => perOf p e W₀ u C.mu0 φ F) := by
  constructor
  · intro φ ψ
    simp only [periodAgainstColumnForm_referenceTuple_eq, PeriodMap.PtilCol, PeriodMap.Ptil, map_add, Submodule.coe_add,
      Formalism.BasicNotions.Examples₂.NZ.col_add, LinearMap.add_apply]
  · intro s φ
    simp only [periodAgainstColumnForm_referenceTuple_eq, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul,
      Formalism.BasicNotions.Examples₂.NZ.col_smul, LinearMap.smul_apply]

theorem perOf_linR (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) (u : B.Word) (φ : W₀.Mu u) :
    IsLinearMap ℂ (fun F : (p.sA true C.mu0).A.T => perOf p e W₀ u C.mu0 φ F) := by
  constructor
  · intro F F'
    simp only [periodAgainstColumnForm_referenceTuple_eq, PeriodMap.PtilCol, PeriodMap.Ptil, map_add]
  · intro s F
    simp only [periodAgainstColumnForm_referenceTuple_eq, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul]

def numsOf (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C) : Nums p W₀ where
  Bu := buSec (data0 p e W₀)
  linL := fun u F => perOf_linL p e W₀ u _
  linR := fun u φ => by
    have h := perOf_linR p e W₀ u φ
    exact ⟨fun x y => (congrArg (perOf p e W₀ u C.mu0 φ) (((data0 p e W₀).sec C.mu0).map_add x y)).trans (h.map_add _ _),
      fun s x => (congrArg (perOf p e W₀ u C.mu0 φ) (((data0 p e W₀).sec C.mu0).map_smul s x)).trans (h.map_smul _ _)⟩
  ze := zeVal (data0 p e W₀)
  rowsRest_wordColumnUnit_baseTuple := periodFactorisationScalar_referenceTuple_eq_one (data0 p e W₀)
  lamP := lamTrace (data0 p e W₀)
  Ij := fun μ j w => @ijCan _ (data0 p e W₀) μ j (w : HeightOneSpectrum (𝓞 B.LL)).asIdeal (HeightOneSpectrum.isPrime _)
  jw := fun μ j w => @jwLat _ (data0 p e W₀) μ j (w : HeightOneSpectrum (𝓞 B.LL)).asIdeal (HeightOneSpectrum.isPrime _)

end GlobalTheory.Mem.R3.Rw.NumDef

namespace GlobalTheory.Mem.R3.Rw

open NumDef in

theorem exists_nums_numOK : ∀ (B : Base) (C : Cols B) (G : Type) [Group G] (p : PkB B C G) (e : PerD p) (W₀ : RowsRest B C),
    ∃ n : Nums p W₀, ∀ η hη V S N G', NumOK (assemble B C (p.what₂ e W₀ n η hη) V S N G') := by
  intro B C G _ p e W₀
  refine ⟨numsOf p e W₀, fun η hη V S N G' => ?_⟩
  exact
  { lam := fun μ j _ _ π _ => rfl
    bu := fun u φ x => by
      kexactB (rfl : buSec (data0 p e W₀) u φ x = buSec (data0 p e W₀) u φ x)
    ze := fun u μ c h1 h2 h3 => (by with_unfolding_all exact ((zeOf_eq (data0 p e W₀) u μ c ⟨by kexactB h1, by kexactB h2⟩ h3) :))
    idx := fun Y => ⟨fun μ j w h1 h2 => (ijIdx_eq_can _ Y μ j h1 h2 w).symm, fun μ j w _ _ => rfl⟩
    jw := fun μ j w _ _ => rfl }

end GlobalTheory.Mem.R3.Rw
