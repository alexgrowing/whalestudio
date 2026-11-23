import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatchStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransportStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelDatumVectorEqThetaOfTestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinitePointsCarryLatticeVacuumToMovedVacuumStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.LevEig

section Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} {X : Data E r} (L : SW.Level X)

omit [IsCMField E] in

theorem full_smul {𝔞 : Ideal (𝓞 E)} (h : 𝔞 ≠ ⊥) {N : Lt E r}
    (hN : N.FG ∧ Submodule.span E (N : Set (Fin r → E)) = ⊤) :
    (𝔞 • N).FG ∧ Submodule.span E ((𝔞 • N : Lt E r) : Set (Fin r → E)) = ⊤ := by
  refine ⟨Submodule.FG.of_le hN.1 Submodule.smul_le_right, ?_⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have h0 : (a : E) ≠ 0 := by simpa using ha0
  rw [eq_top_iff, ← hN.2, Submodule.span_le]
  exact fun v hv => (Submodule.smul_mem_iff _ h0).1
    (Submodule.subset_span (Submodule.smul_mem_smul ha hv))

end Alg

section Hat

variable {D : D7} {k : ℕ}

theorem mul_mem_intAf {a b : Af D.host.F} (ha : a ∈ intAf D.host.F) (hb : b ∈ intAf D.host.F) :
    a * b ∈ intAf D.host.F := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem tmul_mem_hatV {L : Lt D.host.E k} {a : Af D.host.F} (ha : a ∈ intAf D.host.F) {x : Fin k → D.host.E}
    (hx : x ∈ L) : (fun i => a ⊗ₜ[D.host.F] x i) ∈ hatV L :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem toAf_mem {L : Lt D.host.E k} {x : Fin k → D.host.E} (hx : x ∈ L) : toAf x ∈ hatV L :=
  tmul_mem_hatV one_mem_intAf hx

theorem toAf_sub (x y : Fin k → D.host.E) : toAf (x - y) = toAf x - toAf y := by
  funext i; exact TensorProduct.tmul_sub _ _ _

theorem hatV_map {G : Type} [AddCommGroup G] {L : Lt D.host.E k} (f : (Fin k → AfE D) →+ G) (H : AddSubgroup G)
    (h : ∀ a ∈ intAf D.host.F, ∀ x ∈ L, f (fun i => a ⊗ₜ[D.host.F] x i) ∈ H) {u} (hu : u ∈ hatV L) : f u ∈ H := by
  refine (AddSubgroup.closure_le (H.comap f)).2 ?_ hu
  rintro _ ⟨a, ha, x, hx, rfl⟩
  exact h a ha x hx

theorem smul_mem_hatV {L L' : Lt D.host.E k} (c : 𝓞 D.host.E) (h : ∀ x ∈ L, c • x ∈ L') {u} (hu : u ∈ hatV L) :
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • u ∈ hatV L' := by
  refine hatV_map (DistribSMul.toAddMonoidHom _ ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E))) _
    (fun a ha x hx => ?_) hu
  convert tmul_mem_hatV ha (h x hx) using 1
  funext i
  simp only [DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

theorem nsmul_mem_hatV {L : Lt D.host.E k} {𝔪 : Ideal (𝓞 D.host.E)} {M : ℕ} (hM : (M : 𝓞 D.host.E) ∈ 𝔪) {u}
    (hu : u ∈ hatV L) : M • u ∈ hatV (𝔪 • L) := by
  have := smul_mem_hatV (L' := 𝔪 • L) M (fun x hx => Submodule.smul_mem_smul hM hx) hu
  have e : ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((M : 𝓞 D.host.E) : D.host.E)) = (M : AfE D) :=
    map_natCast ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F)).toRingHom.comp
      (algebraMap (𝓞 D.host.E) D.host.E)) M
  rwa [e, Nat.cast_smul_eq_nsmul] at this

theorem fmt_one (V : HSp D) : fmt V 1 = 1 := by
  simp only [fmt, Formalism.L2.Theta.mt, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

variable {S T : HSp D}

noncomputable def col (j : Fin S.rank) : WO S T →+ (Fin T.rank → AfE D) :=
  AddMonoidHom.mk' (fun w a => finPart D (w a j)) fun _ _ => funext fun _ => RingHom.map_add _ _ _

theorem actO_sub (h : GA D S) (g : GA D T) (w w' : WO S T) :
    actO S T h g (w - w') = actO S T h g w - actO S T h g w' := by
  simp only [actO, Matrix.mul_sub, Matrix.sub_mul]

end Hat

section Mov

variable {D : D7} {S T : HSp D}

theorem isMov_conj {V : HSp D} {g : GA D V} (h : IsMov (fmt V g) (stdL D.host.E V.rank) (stdL D.host.E V.rank)) :
    IsMov (fmtC V g) (stdL D.host.E V.rank) (stdL D.host.E V.rank) := by
  let c : AfE D →+* AfE D := sigR (Af D.host.F) D.sp.cm.sig
  have c2 (x : AfE D) : c (c x) = x := by
    induction x using TensorProduct.induction_on with
    | zero => rw [c.map_zero, c.map_zero]
    | tmul a x => exact congrArg (fun t => a ⊗ₜ[D.host.F] t) (star_star x)
    | add x y hx hy => rw [c.map_add, c.map_add, hx, hy]
  have c3 (x : Formalism.L2.Theta.AE D) : finPart D (cA D x) = c (finPart D x) := by
    induction x using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero, c.map_zero]
    | tmul a x => rfl
    | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, c.map_add, hx, hy]
  have c4 : fmtC V g = (fmt V g).map c := by ext i j; exact c3 _
  have c5 {u} (hu : u ∈ hatV (stdL D.host.E V.rank)) : c ∘ u ∈ hatV (stdL D.host.E V.rank) := by
    refine hatV_map (c.toAddMonoidHom.compLeft _) _ (fun a ha x hx => ?_) hu
    refine tmul_mem_hatV ha (x := fun i => cc (x i)) ?_
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine Submodule.subset_span ⟨i, funext fun j => ?_⟩
      by_cases e : j = i <;> simp [e, cc]
    | zero => simp only [cc, Pi.zero_apply, map_zero]; exact (stdL D.host.E V.rank).zero_mem
    | add x y _ _ hx hy => convert add_mem hx hy; simp [cc]
    | smul b x _ hx =>
      convert Submodule.smul_mem _ (Lev.bar b) hx
      rw [Lev.O_smul, Lev.O_smul, Lev.coe_bar]
      simp [cc]
  have c6 (u : Fin V.rank → AfE D) : c ∘ c ∘ u = u := funext fun i => c2 _
  have c7 (u : Fin V.rank → AfE D) : fmtC V g *ᵥ (c ∘ u) = c ∘ (fmt V g *ᵥ u) := by
    rw [c4]; funext i; exact (RingHom.map_mulVec c _ _ i).symm
  intro u
  constructor
  · intro hu
    obtain ⟨u₀, h0, e⟩ := (h _).1 (c5 hu)
    exact ⟨_, c5 h0, by rw [c7, ← e, c6]⟩
  · rintro ⟨u₀, h0, rfl⟩
    rw [← c6 u₀, c7]
    exact c5 ((h _).2 ⟨_, c5 h0, rfl⟩)

end Mov

section Main

variable {D : D7} {S T : HSp D} (C : Ctx S T) (Lv : SW.Level C.X)

theorem full_Λ : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
  ⟨C.X.Λ_fg, C.X.Λ_span⟩

theorem full_std (n : ℕ) : (stdL D.host.E n).FG ∧
    Submodule.span D.host.E (stdL D.host.E n : Set (Fin n → D.host.E)) = ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [stdL, Submodule.span_span_of_tower]
  convert (Pi.basisFun D.host.E (Fin n)).span_eq
  simp

end Main

end GlobalTheory.Ker.LevEig
