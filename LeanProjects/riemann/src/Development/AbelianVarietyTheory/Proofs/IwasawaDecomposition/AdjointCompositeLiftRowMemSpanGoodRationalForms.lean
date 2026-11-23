import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapOpOfKForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.UpKeep3

section Abstract

theorem mem_span_of_op {K : Type} [Field K] {σ : K →+* ℂ} {V H : Type} [AddCommGroup V] [Module K V] [AddCommGroup H]
    [Module ℂ H] (j : V →ₛₗ[σ] H) {ι : Type} (b : ι → V) (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤)
    (C : H →ₗ[ℂ] H) (φ : V → V) (hC : ∀ z, C (j z) = j (φ z)) (v : H) :
    C v ∈ Submodule.span ℂ (Set.range fun z => j (φ z)) := by
  have hv : v ∈ Submodule.span ℂ (Set.range fun k => j (b k)) := hsp ▸ Submodule.mem_top
  have h : Submodule.span ℂ (Set.range fun k => j (b k)) ≤ (Submodule.span ℂ (Set.range fun z => j (φ z))).comap C := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show C (j (b k)) ∈ Submodule.span ℂ (Set.range fun z => j (φ z))
    rw [hC]
    exact Submodule.subset_span ⟨b k, rfl⟩
  exact h hv

theorem sum_apply_j {K : Type} [Field K] {σ : K →+* ℂ} {G V H : Type} [Group G] [Fintype G] [AddCommGroup V] [Module K V]
    [AddCommGroup H] [Module ℂ H] (j : V →ₛₗ[σ] H) (r : Representation K G V) (ρ : Representation ℂ G H)
    (hj : ∀ g z, j (r g z) = ρ g (j z)) (a : G → K) (z : V) :
    (∑ g, σ (a g) • ρ g) (j z) = j ((∑ g, a g • r g) z) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hj]

theorem adjoint_comm {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (Θ : E →ₗ[ℂ] H) (π : H →ₗ[ℂ] H)
    (hπ : ∀ x, ‖π x‖ = ‖x‖) (ρ : E →ₗ[ℂ] E) (hρ : ∀ y, ‖ρ y‖ = ‖y‖) (h : ∀ y, Θ (ρ y) = π (Θ y)) (x : H) :
    ρ (LinearMap.adjoint Θ x) = LinearMap.adjoint Θ (π x) := by
  have hinj : Function.Injective ρ := (injective_iff_map_eq_zero ρ).2 fun y hy => by
    rw [← norm_eq_zero, ← hρ, hy, norm_zero]
  refine ext_inner_left ℂ fun v => ?_
  obtain ⟨y, rfl⟩ := LinearMap.surjective_of_injective hinj v
  rw [(LinearMap.norm_map_iff_inner_map_map ρ).1 hρ, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right, h,
    (LinearMap.norm_map_iff_inner_map_map π).1 hπ]

theorem mem_span_untwist {s : Bool} {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : ι → E) (z : E)
    (h : Tw.mk s z ∈ Submodule.span ℂ (Set.range fun i => Tw.mk s (f i))) : z ∈ Submodule.span ℂ (Set.range f) := by
  have hle : Submodule.span ℂ (Set.range fun i => Tw.mk s (f i)) ≤ Tw.sub s (Submodule.span ℂ (Set.range f)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (R := ℂ) (M := E) ⟨i, rfl⟩
  exact hle h

theorem adjoint_mem_span {K G V E H ι : Type} [Field K] {σ : K →+* ℂ} [Group G] [Fintype G] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (j : V →ₛₗ[σ] E) (b : ι → V) (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (r : Representation K G V)
    (π : Representation ℂ G H) (hπ : ∀ g x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ) (Θ : E →ₗ[ℂ] H)
    (hρ : ∃ ρ : Representation ℂ G E, (∀ g z, j (r g z) = ρ g (j z)) ∧ (∀ g y, ‖ρ g y‖ = ‖y‖) ∧ ∀ g y, Θ (ρ g y) = π g (Θ y))
    (a l : G → K) (u : H) (ha : ∑ g, σ (a g) • π g u = u) (hl : ∑ g, σ (l g) • π g u = u) :
    LinearMap.adjoint Θ u ∈ Submodule.span ℂ (Set.range fun z => j ((∑ g, a g • r g) ((∑ g, l g • r g) z))) := by
  obtain ⟨ρ, hj, hn, hΘ⟩ := hρ
  have e1 : ∀ g, ρ g (LinearMap.adjoint Θ u) = LinearMap.adjoint Θ (π g u) := fun g =>
    adjoint_comm Θ (π g) ((LinearMap.norm_map_iff_inner_map_map (π g)).2 (hπ g)) (ρ g) (hn g) (hΘ g) u
  have fix : ∀ c : G → K, ∑ g, σ (c g) • π g u = u →
      (∑ g, σ (c g) • ρ g) (LinearMap.adjoint Θ u) = LinearMap.adjoint Θ u := fun c hc => by
    conv_rhs => rw [← hc]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, e1, map_sum, map_smul]
  have h := mem_span_of_op j b hsp ((∑ g, σ (a g) • ρ g) ∘ₗ (∑ g, σ (l g) • ρ g))
    (fun z => (∑ g, a g • r g) ((∑ g, l g • r g) z))
    (fun z => by rw [LinearMap.comp_apply, sum_apply_j j r ρ hj, sum_apply_j j r ρ hj]) (LinearMap.adjoint Θ u)
  rwa [LinearMap.comp_apply, fix l hl, fix a ha] at h

theorem untwist_adjoint {s : Bool} {E H ι κ : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (Θ : E →ₗ[ℂ] H) (u : H) (f : ι → E) (f' : κ → E)
    (hf : ∀ i, ∃ k, f i = f' k)
    (h : LinearMap.adjoint (Tw.map s Θ) (Tw.mk s u) ∈ Submodule.span ℂ (Set.range fun i => Tw.mk s (f i))) :
    LinearMap.adjoint Θ u ∈ Submodule.span ℂ (Set.range f') := by
  rw [Tw.adjoint_map] at h
  refine Submodule.span_mono ?_ (mem_span_untwist (s := s) f _ h)
  rintro _ ⟨i, rfl⟩
  exact (hf i).elim fun k hk => ⟨k, hk.symm⟩

theorem exists_lvl_coord {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (z : S.Forms) :
    ∃ x, S.gaOp r (lvlIdem P ψ) z = S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x) := by
  obtain ⟨w, rfl⟩ := S.basis.equivFun.symm.surjective z
  have h : S.gaMat r (lvlIdem P ψ) *ᵥ w ∈ LinearMap.range (imE (S.gaMat r (lvlIdem P ψ))).mulVecLin := by
    rw [(image_idempotent_spec K _ _).2]
    exact ⟨w, rfl⟩
  obtain ⟨x, hx⟩ := h
  exact ⟨x, (GlobalTheory.Mem.LiftForms.gaOp_coord S r _ w).trans (congrArg _ hx.symm)⟩

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

theorem exists_rowForm {A : FamIn D.what₂.LL G Pl0 T D.R.m} {s : ℕ} (ok : A.fam.Ok s) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)
    (t : T) (z : (A.MtildeCSD t).Forms) :
    ∃ x, (A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (idemOf A.X) ((A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (lvlIdem P ψ) z) =
      rowForm A P ψ t ((rE D A P ψ t).mulVec x) :=
  (exists_lvl_coord (A.MtildeCSD t) (A.leftGroupActionRight t) P ψ z).elim fun x hx =>
    ⟨x, (congrArg ((A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (idemOf A.X)) hx).trans (GoodProj.rowForm_rE ok P ψ t x).symm⟩

variable {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sum_lvl_fix (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (u : (R.toCx3 F).EE) (hu : u ∈ (R.toCx3 F).EEl true) :
    ∑ g, A3.A.fam.v0.embedding ((lvlIdem F.P1 F.ψ1).coeff g) • R.gEx F g u = u := by
  rw [(GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC).2] at hu
  refine GlobalTheory.RowsNonzero.sum_lvlIdem (R.gEx F) F.P1 F.ψ1 fun h => ?_
  have := (Submodule.mem_iInf _).1 hu h
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  exact this

theorem adjoint_mem_tw (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hH : Holds R F) (u : (R.toCx3 F).EE)
    (hu : u ∈ (R.toCx3 F).EEl true) :
    LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) u ∈ Submodule.span ℂ (Set.range fun z => (R.toCx3 F).jR A3.A.fam.μ0
      ((∑ g, (idemOf A3.A.X).coeff g • (A3.A.fam.R A3.A.fam.μ0).r g)
        ((∑ g, (lvlIdem F.P1 F.ψ1).coeff g • (A3.A.fam.R A3.A.fam.μ0).r g) z))) :=
  adjoint_mem_span (V := (A3.A.fam.R A3.A.fam.μ0).S.Forms) (E := (R.toCx3 F).FC A3.A.fam.μ0) ((R.toCx3 F).jR A3.A.fam.μ0)
    (Formalism.IndefR.Cx.CxData.bR (A := A3.fam3.amb3) A3.A.fam.μ0) (RealDat3.kFormR_of (F := F) hC.base.models A3.A.fam.μ0).2
    (A3.A.fam.R A3.A.fam.μ0).r (R.gEx F) hH.prim.gUnit.1 ((R.toCx3 F).Θ A3.A.fam.μ0)
    (GlobalTheory.RowsPosRed.exists_rho R F (s := 1) hH.ok hC.base.models hH.prim.gEquiv)
    (fun g => (idemOf A3.A.X).coeff g) (fun g => (lvlIdem F.P1 F.ψ1).coeff g) u
    (GlobalTheory.RowsPosRed.sum_idem_gEx R F (GlobalTheory.CoreOfWeak.core_of_weak R F hC hH.aux.ex).1 u) (sum_lvl_fix R F hC u hu)

theorem adjoint_mem_of_row (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hH : Holds R F) (w : R.HE.H)
    (hw : R.HE.e w ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) :
    LinearMap.adjoint (R.Th A3.A.μ0) w ∈ Submodule.span ℂ (Set.range fun x =>
      R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 ((rE D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec x))) :=
  untwist_adjoint (s := twAt D.what₂.embLL A3.A.v0) (R.Th A3.A.μ0) w
    (fun z => R.jX A3.A.μ0 ((A3.A.MtildeCSD A3.A.μ0).gaOp (A3.A.leftGroupActionRight A3.A.μ0) (idemOf A3.A.X)
      ((A3.A.MtildeCSD A3.A.μ0).gaOp (A3.A.leftGroupActionRight A3.A.μ0) (lvlIdem F.P1 F.ψ1) z))) _
    (fun z => (exists_rowForm hH.ok.ok2 F.P1 F.ψ1 A3.A.μ0 z).elim fun x hx => ⟨x, congrArg (R.jX A3.A.μ0) hx⟩)
    (adjoint_mem_tw R F hC hH (Tw.mk (twAt D.what₂.embLL A3.A.v0) w) hw)

end GlobalTheory.UpKeep3

namespace GlobalTheory.UpKeep3

theorem adjoint_mem_span_rowForm : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (uE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, (Y.Ish.jE y).1 = PiTensorProduct.lift (R.HE.e (uE y))) → ∀ y, LinearMap.adjoint (R.Th A3.A.μ0) (uE y) ∈ Submodule.span ℂ (Set.range fun x => R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 ((rE D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec x))) := by
  intro _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH uE hread y
  have hrow : R.HE.e (uE y) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) := by
    have h1 := (Y.Ish.jE y).2
    rw [hread y] at h1
    obtain ⟨m, hm, hm'⟩ := h1
    have e : m = R.HE.e (uE y) := (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).injective hm'
    rw [← e]
    exact hm
  exact adjoint_mem_of_row R F hP.char hH (uE y) hrow

end GlobalTheory.UpKeep3

end
