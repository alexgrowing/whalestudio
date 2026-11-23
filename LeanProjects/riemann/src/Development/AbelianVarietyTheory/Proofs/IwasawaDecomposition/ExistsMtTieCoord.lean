import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Formalism.LocalToGlobal.Divisibility.RowSideTie

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftForms

theorem ker_eq_comap {M N H W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup W] [Module ℂ W] (f : M →ₗ[ℂ] N) (g : H →ₗ[ℂ] W) (a : M →ₗ[ℂ] H) (b : N →ₗ[ℂ] W) (hb : Function.Injective b)
    (h : ∀ x, b (f x) = g (a x)) : LinearMap.ker f = (LinearMap.ker g).comap a := by
  ext x
  rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.mem_ker, ← h, map_eq_zero_iff _ hb]

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem jMt_injective (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  have hli := (D.what₂.jMt_basis μ j (Module.Free.chooseBasis _ _)).1
  have := hli.finite
  have := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))
  exact inj_of_li D.what₂.embLL (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _) hli

theorem carrier_subset (μ : D.what₂.Tup) (j : ℕ) : ∀ m ∈ (D.what₂.MtLat μ j).carrier, m ∈ Set.range (D.what₂.jMt μ j) := by
  rintro _ ⟨c, rfl⟩
  refine Finset.sum_induction _ (fun m => m ∈ Set.range (D.what₂.jMt μ j)) ?_ ⟨0, map_zero _⟩ fun v hv => ?_
  · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  · obtain ⟨x, rfl⟩ := D.what₂.MtLat_sub μ j v hv
    exact ⟨D.what₂.OtoLL (c (D.what₂.jMt μ j x)) • x, map_smulₛₗ _ _ _⟩

variable {R : RealDat D A Ks} {F : Face D A}

theorem inner_jV (hC : R.Char F) (i : Fin D.R.m) (t : T) (f g : (A.MtCSD i t).Forms) :
    inner ℂ (R.jV i t f) (R.jV i t g) = D.what₂.embLL ((A.MtCSD i t).csum f g) := by
  refine ((hC.models.HV i t).2.2 _ _).trans ?_
  refine (congrArg₂ _ (hC.models.jV i t f) (hC.models.jV i t g)).trans ?_
  exact (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.2 f g

theorem jV_injective (hC : R.Char F) (i : Fin D.R.m) (t : T) : Function.Injective (R.jV i t) := by
  have hb := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.1.1
  have h1 := inj_of_li D.what₂.embLL (R.B.L i t).pres.extL (A.MtCSD i t).basis hb
  intro f g hfg
  apply h1
  exact (hC.models.jV i t f).symm.trans ((congrArg (R.HV i t).e hfg).trans (hC.models.jV i t g))

theorem mem_Zl (i : Fin D.R.m) (t : T) (f : (A.MtCSD i t).Forms) (hf : f ∈ (R.toCx F).zs.Zl i t) :
    R.jV i t f ∈ (LinearMap.ker (R.thG i t))ᗮ := by
  have h1 : (R.toCx F).jL i t f ∈ LinearMap.range (LinearMap.adjoint ((R.toCx F).θ' i t)) := hf
  rw [← LinearMap.orthogonal_ker] at h1
  intro u hu
  have h2 := h1 (Tw.mk (twAt D.what₂.embLL A.v0) u) hu
  have h3 : cj (twAt D.what₂.embLL A.v0) (inner ℂ u (R.jV i t f)) = 0 := h2
  exact (map_eq_zero _).1 h3

theorem mem_ker_of_orth (hZ : R.LRatZ F) (i : Fin D.R.m) (t : T) (w : (R.HV i t).H)
    (hw : ∀ f ∈ (R.toCx F).zs.Zl i t, inner ℂ (R.jV i t f) w = 0) : w ∈ LinearMap.ker (R.thG i t) := by
  have h1 := hZ.2 i t
  rw [← LinearMap.orthogonal_ker] at h1
  have h2 : (show (R.toCx F).FLC i t from Tw.mk (twAt D.what₂.embLL A.v0) w) ∈ (LinearMap.ker ((R.toCx F).θ' i t))ᗮᗮ := by
    rw [← h1]
    intro u hu
    have hle : Submodule.span ℂ ((R.toCx F).jL i t '' ((R.toCx F).Zl i t : Set _)) ≤
        (Submodule.span ℂ {(show (R.toCx F).FLC i t from Tw.mk (twAt D.what₂.embLL A.v0) w)})ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
      show cj (twAt D.what₂.embLL A.v0) (inner ℂ (R.jV i t f) w) = 0
      rw [hw f hf, map_zero]
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hu)
  rw [Submodule.orthogonal_orthogonal] at h2
  exact h2

set_option maxHeartbeats 1000000 in

theorem exists_coord_tie {s : ℕ} (R : RealDat D A Ks) (F : Face D A) (X0 : BaseLevelRowSide D) (hC : R.Char F) (hOk : A.fam.Ok s)
    (hZ : R.LRatZ F) (hS : R.LStable F) (Y : RowsTie R F X0) :
    ∃ e : ∀ (i : Fin D.R.m) (t : T),
        (Fin ((A.fam.L i t).S.lvlDim (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ) → D.what₂.LL) ≃ₗ[D.what₂.LL]
          D.what₂.MtL (Y.tup t) ((i : ℕ) + 1),
      ∀ (i : Fin D.R.m) (t : T),
        (∀ x, Y.eV i t (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (e i t x)) =
          R.jV i t (lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ x)) ∧
        (∀ x y, inner ℂ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (e i t x)) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (e i t y)) =
          D.what₂.embLL (hform ((A.fam.L i t).S.lvlH (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ) x y)) ∧
        (∀ x, D.what₂.eMt (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (e i t x)) =
          D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (e i t
            ((A.fam.L i t).S.lvlOp (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ (idemOf A.X) *ᵥ x))) ∧
        Submodule.span (𝓞 D.what₂.LL)
            {x | D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (Y.tup t) ((i : ℕ) + 1)).carrier} =
          ((A.fam.L i t).S.lvlNab (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ).map
            ((e i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) ∧
        Idx.Z0 D (Y.tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)
          (e i t ((A.fam.L i t).lE (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t) *ᵥ Pi.single k 1))) ∧
        (∀ y, D.what₂.eMt (Y.tup t) ((i : ℕ) + 1) ((D.what₂.Zj (Y.tup t) ((i : ℕ) + 1)).starProjection y) =
          (Idx.Z0 D (Y.tup t) ((i : ℕ) + 1)).starProjection y) ∧
        (∀ x, (Idx.Z0 D (Y.tup t) ((i : ℕ) + 1)).starProjection (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (e i t x)) =
          D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (e i t ((A.fam.L i t).lE (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t) *ᵥ
            ((A.fam.L i t).lPr (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t) *ᵥ x)))) ∧
        Idx.TjL D (Y.tup t) ((i : ℕ) + 1) =
          (matLat ((A.fam.L i t).lE (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t))
            ((A.fam.L i t).Tl (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t))).map
            ((e i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  have hn : 0 < RealDat.nP F false := RealDat.nP_pos false
  have hjV := jV_injective hC
  have heV : ∀ i t, Function.Injective (Y.eV i t) := fun i t => inj_of_norm_sq _ hn (Y.eV_norm i t)
  have hex := fun i t => exists_coord (B := A.fam.L i t) (ℓ := A.fam.lvlA F.P0 F.ψ0) (R.jV i t) (hjV i t)
    (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)) (jMt_injective _ _) (Y.eV i t) (heV i t) (Y.eV_rat i t)
  choose e he using hex
  refine ⟨e, fun i t => ?_⟩
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA F.P0 F.ψ0) A.v0 s := ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hst : ∀ g, ∀ f ∈ (R.toCx F).zs.Zl i t, (A.fam.L i t).r g f ∈ (R.toCx F).zs.Zl i t :=
    fun g f hf => hS.2 i t (Sum.inr g) ⟨f, hf, rfl⟩
  have hker : LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) = (LinearMap.ker (R.thG i t)).comap (Y.eV i t) := by
    exact ker_eq_comap _ _ _ _ (inj_of_norm_sq _ hn (Y.eW_norm i)) (Y.theta_tie i t)
  have hZj : D.what₂.Zj (Y.tup t) ((i : ℕ) + 1) = ((LinearMap.ker (R.thG i t)).comap (Y.eV i t))ᗮ := by
    rw [← hker, LinearMap.orthogonal_ker]
    rfl
  have hZ0 : Idx.Z0 D (Y.tup t) ((i : ℕ) + 1) =
      ((LinearMap.ker (R.thG i t)).comap (Y.eV i t))ᗮ ⊓ LinearMap.range (D.what₂.eMt (Y.tup t) ((i : ℕ) + 1)) := by
    rw [← hker]
    rfl
  obtain ⟨h1, h2, h3, h4, h5⟩ := coord_facts (Z := (R.toCx F).zs.Zl i t) hB hst (R.jV i t) (inner_jV hC i t)
    (LinearMap.ker (R.thG i t)) (mem_Zl i t) (mem_ker_of_orth hZ i t) (Y.eV i t) (Y.eV_norm i t) (Y.eV_range i t)
    (D.what₂.eMt (Y.tup t) ((i : ℕ) + 1)) (D.what₂.eMt_idem _ _) (D.what₂.eMt_sa _ _) (Y.eMt_tie i t)
    ((D.what₂.jMt (Y.tup t) ((i : ℕ) + 1)).comp (e i t).toLinearMap) (he i t)
  have h6 := coord_lattice (B := A.fam.L i t) (ℓ := A.fam.lvlA F.P0 F.ψ0) (R.jV i t) _ (jMt_injective _ _) (Y.eV i t) (heV i t)
    (e i t) (he i t) _ (carrier_subset _ _) (congrArg id (Y.eV_lat i t))
  have h4' : ∀ y, D.what₂.eMt (Y.tup t) ((i : ℕ) + 1) ((D.what₂.Zj (Y.tup t) ((i : ℕ) + 1)).starProjection y) =
      (Idx.Z0 D (Y.tup t) ((i : ℕ) + 1)).starProjection y := by
    intro y
    simp only [hZj, hZ0]
    exact h4 y
  have h5' : ∀ x, (Idx.Z0 D (Y.tup t) ((i : ℕ) + 1)).starProjection (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (e i t x)) =
      D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (e i t ((A.fam.L i t).lE (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t) *ᵥ
        ((A.fam.L i t).lPr (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t) *ᵥ x))) := by
    intro x
    simp only [hZ0]
    exact h5 x
  refine ⟨he i t, h1, h2, h6, hZ0.trans h3, h4', h5', ?_⟩
  let π : D.what₂.MtL (Y.tup t) ((i : ℕ) + 1) →ₗ[𝓞 D.what₂.LL] D.what₂.MtL (Y.tup t) ((i : ℕ) + 1) :=
    ((e i t).toLinearMap ∘ₗ ((A.fam.L i t).lE (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t)).mulVecLin ∘ₗ
      ((A.fam.L i t).lPr (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t)).mulVecLin ∘ₗ (e i t).symm.toLinearMap).restrictScalars
      (𝓞 D.what₂.LL)
  have hπe : ∀ x, π (e i t x) = e i t ((A.fam.L i t).lE (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t) *ᵥ
      ((A.fam.L i t).lPr (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t) *ᵥ x)) := by
    intro x
    simp only [π, LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Matrix.mulVecLin_apply]
  have hπ : ∀ x, D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (π x) = D.what₂.eMt (Y.tup t) ((i : ℕ) + 1)
      ((D.what₂.Zj (Y.tup t) ((i : ℕ) + 1)).starProjection (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) x)) := by
    intro x
    obtain ⟨x, rfl⟩ := (e i t).surjective x
    rw [h4', h5', hπe]
  have hset : {x | D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) x ∈ D.what₂.TjSet (Y.tup t) ((i : ℕ) + 1)} =
      π '' {x | D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (Y.tup t) ((i : ℕ) + 1)).carrier} := by
    ext x
    constructor
    · rintro ⟨m, hm, hx⟩
      obtain ⟨u, rfl⟩ := carrier_subset _ _ m hm
      exact ⟨u, hm, jMt_injective _ _ ((hπ u).trans hx)⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, hu, (hπ u).symm⟩
  unfold Idx.TjL
  rw [hset, ← Submodule.map_span, h6]
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, (hπe y).symm⟩
  · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, hπe y⟩

end Main

section Comparison₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem basis_of_coord (μ : D.what₂.Tup) (j : ℕ) {n : ℕ} (e : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ j) :
    (LinearIndependent ℂ fun k => ((D.what₂.jMt μ j).comp e.toLinearMap) (Pi.single k 1)) ∧
      Submodule.span ℂ (Set.range fun k => ((D.what₂.jMt μ j).comp e.toLinearMap) (Pi.single k 1)) = ⊤ := by
  obtain ⟨hli, hsp⟩ := D.what₂.jMt_basis μ j (Module.Free.chooseBasis _ _)
  have := hli.finite
  have := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))
  have hspan : Submodule.span ℂ (Set.range fun k => ((D.what₂.jMt μ j).comp e.toLinearMap) (Pi.single k 1)) = ⊤ := by
    have h1 := span_range_mulVec ((D.what₂.jMt μ j).comp e.toLinearMap) (1 : Matrix (Fin n) (Fin n) D.what₂.LL)
    simp only [Matrix.one_mulVec] at h1
    rw [← h1, eq_top_iff, ← hsp]
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    refine ⟨e.symm (Module.Free.chooseBasis _ _ k), ⟨_, rfl⟩, ?_⟩
    simp
  refine ⟨linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge ?_, hspan⟩
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge),
    ← Module.finrank_eq_card_basis (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j)), ← e.finrank_eq]
  simp

theorem oLatTie_of_span (μ : D.what₂.Tup) (j : ℕ) {n : ℕ} (e : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ j)
    (N : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL))
    (h : Submodule.span (𝓞 D.what₂.LL) {x | D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).carrier} =
      N.map (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL))) :
    OLatTie D.what₂.embLL (D.what₂.MtLat μ j) ((D.what₂.jMt μ j).comp e.toLinearMap) N := by
  classical
  refine ⟨fun v hv => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := D.what₂.MtLat_sub μ j v hv
    exact ⟨e.symm y, by simp⟩
  · have hm : e x ∈ Submodule.span (𝓞 D.what₂.LL) {x | D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).carrier} := h ▸ ⟨x, hx, rfl⟩
    show ∃ c : D.what₂.Mt μ j → 𝓞 D.what₂.LL, D.what₂.jMt μ j (e x) = _
    generalize e x = y at hm
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc⟩ := hy
      exact ⟨fun v => ⟨D.what₂.OtoLL (c v), D.O_int _⟩, hc⟩
    | zero => exact ⟨0, by simp⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨c, hc⟩ := h1
      obtain ⟨d, hd⟩ := h2
      refine ⟨c + d, ?_⟩
      rw [map_add, hc, hd, ← Finset.sum_add_distrib]
      simp [add_smul]
    | smul a _ _ h1 =>
      obtain ⟨c, hc⟩ := h1
      refine ⟨fun v => a * c v, ?_⟩
      rw [Idx.smul_def, map_smulₛₗ, hc, Finset.smul_sum]
      simp [mul_smul]
  · rintro ⟨c, hc⟩
    have hc' : D.what₂.jMt μ j (e x) = ∑ v ∈ (D.what₂.MtLat μ j).gen, D.what₂.embLL (c v : D.what₂.LL) • v := hc
    have key : ∃ y ∈ Submodule.span (𝓞 D.what₂.LL) {x | D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).carrier},
        D.what₂.jMt μ j y = ∑ v ∈ (D.what₂.MtLat μ j).gen, D.what₂.embLL (c v : D.what₂.LL) • v := by
      refine Finset.sum_induction _ (fun m => ∃ y ∈ Submodule.span (𝓞 D.what₂.LL)
        {x | D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).carrier}, D.what₂.jMt μ j y = m) ?_ ⟨0, zero_mem _, map_zero _⟩ fun v hv => ?_
      · rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
        exact ⟨y + z, add_mem hy hz, map_add _ _ _⟩
      · obtain ⟨y, hy⟩ := D.what₂.MtLat_sub μ j v hv
        refine ⟨c v • y, Submodule.smul_mem _ _ (Submodule.subset_span ?_), by rw [Idx.smul_def, map_smulₛₗ, hy]⟩
        refine ⟨fun u => if u = v then 1 else 0, ?_⟩
        rw [hy, Finset.sum_eq_single v]
        · simp
        · intro u _ hu
          simp [hu]
        · intro h; exact absurd hv h
    obtain ⟨y, hy, hyx⟩ := key
    have hxy : y = e x := jMt_injective _ _ (hyx.trans hc'.symm)
    rw [hxy, h] at hy
    obtain ⟨z, hz, hzx⟩ := hy
    rwa [← e.injective hzx]

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem mtTie_of_clauses (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup)
    (e : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (h2 : ∀ (i : Fin D.R.m) t x y,
      inner ℂ (D.what₂.jMt (tup t) ((i : ℕ) + 1) (e i t x)) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (e i t y)) =
        D.what₂.embLL (hform ((A.fam.L i t).S.lvlH (A.fam.L i t).r (A.fam.lvlA P ψ).P (A.fam.lvlA P ψ).ψ) x y))
    (h3 : ∀ (i : Fin D.R.m) t x, D.what₂.eMt (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (e i t x)) =
      D.what₂.jMt (tup t) ((i : ℕ) + 1) (e i t
        ((A.fam.L i t).S.lvlOp (A.fam.L i t).r (A.fam.lvlA P ψ).P (A.fam.lvlA P ψ).ψ (idemOf A.X) *ᵥ x)))
    (h4 : ∀ (i : Fin D.R.m) t, Submodule.span (𝓞 D.what₂.LL)
        {x | D.what₂.jMt (tup t) ((i : ℕ) + 1) x ∈ (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier} =
      ((A.fam.L i t).S.lvlNab (A.fam.L i t).r (A.fam.lvlA P ψ).P (A.fam.lvlA P ψ).ψ).map
        ((e i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)))
    (h5 : ∀ (i : Fin D.R.m) t, Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k =>
      D.what₂.jMt (tup t) ((i : ℕ) + 1) (e i t ((A.fam.L i t).lE (A.fam.lvlA P ψ) (Zs.Zl i t) *ᵥ Pi.single k 1)))) :
    MtTie D A P ψ Zs tup e where
  forms i t := ⟨(basis_of_coord _ _ (e i t)).1, (basis_of_coord _ _ (e i t)).2, h2 i t, h3 i t⟩
  lat i t := oLatTie_of_span _ _ (e i t) _ (h4 i t)
  Z0 := h5

theorem exists_mtTie_coord {s : ℕ} (R : RealDat D A Ks) (F : Face D A) (X0 : BaseLevelRowSide D) (hC : R.Char F) (hOk : A.fam.Ok s)
    (hZ : R.LRatZ F) (hS : R.LStable F) (Y : RowsTie R F X0) :
    ∃ eMt, MtTie D A F.P0 F.ψ0 (R.toCx F).zs Y.tup eMt ∧ ∀ (i : Fin D.R.m) (t : T),
      (∀ x, Y.eV i t (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (eMt i t x)) =
        R.jV i t (lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ x)) ∧
      (∀ y, D.what₂.eMt (Y.tup t) ((i : ℕ) + 1) ((D.what₂.Zj (Y.tup t) ((i : ℕ) + 1)).starProjection y) =
        (Idx.Z0 D (Y.tup t) ((i : ℕ) + 1)).starProjection y) ∧
      (∀ x, (Idx.Z0 D (Y.tup t) ((i : ℕ) + 1)).starProjection (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (eMt i t x)) =
        D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (eMt i t ((A.fam.L i t).lE (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t) *ᵥ
          ((A.fam.L i t).lPr (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t) *ᵥ x)))) ∧
      Idx.TjL D (Y.tup t) ((i : ℕ) + 1) =
        (matLat ((A.fam.L i t).lE (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t))
          ((A.fam.L i t).Tl (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t))).map
          ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  have h := exists_coord_tie R F X0 hC hOk hZ hS Y
  refine h.elim fun e he => ?_
  have hm : MtTie D A F.P0 F.ψ0 (R.toCx F).zs Y.tup e :=
    mtTie_of_clauses F.P0 F.ψ0 (R.toCx F).zs Y.tup e (fun i t => (he i t).2.1) (fun i t => (he i t).2.2.1) (fun i t => (he i t).2.2.2.1)
      (fun i t => (he i t).2.2.2.2.1)
  exact ⟨e, hm, fun i t => ⟨(he i t).1, (he i t).2.2.2.2.2⟩⟩

end Comparison₂

end GlobalTheory.Mem.LiftForms

end
