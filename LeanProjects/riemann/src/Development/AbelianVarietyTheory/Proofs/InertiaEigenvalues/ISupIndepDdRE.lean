import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GradedSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLines

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

noncomputable section

namespace GlobalTheory.Per.FilLetUnram

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem act_ι (g : G) (d : V ⊗[Qp] B) :
    actVdR PD ρ g (ιV PD (LL := LL) (V := V) d) = ιV PD (LL := LL) (V := V) (actVB PD ρ g d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp [actVdR, ιV, actVB, PD.ι_comm]

theorem mul_ι (c : K₀) (d : V ⊗[Qp] B) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := V) d) =
      ιV PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp [mulVdR, ιV, mulVB, ← IsScalarTower.algebraMap_apply]

theorem ι_mem_DdRE (hs : Function.Surjective (algebraMap K₀ K)) (τ : K →ₐ[Qp] LL)
    {d : V ⊗[Qp] B} (hd : d ∈ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))) :
    ιV PD (LL := LL) (V := V) d ∈ DdRE PD ρ τ := by
  obtain ⟨h1, h2⟩ := hd
  simp only [Dcris, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at h1 h2
  constructor
  · simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    rw [act_ι, h1 g]
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero]
    intro c
    obtain ⟨c₀, rfl⟩ := hs c
    rw [mul_ι, h2 c₀, map_smul]
    rfl

theorem iSupIndep_DdRE : iSupIndep fun τ : K →ₐ[Qp] LL => DdRE PD ρ τ := by
  have h := iSupIndep.iInf
    (fun (c : K) (a : LL) => Module.End.eigenspace
      (mulVdR (Qp := Qp) (K := K) (BdR := BdR) (V := V) (LL := LL) c) a)
    (fun c => Module.End.eigenspaces_iSupIndep _)
  have h' := h.comp (f := fun τ : K →ₐ[Qp] LL => (τ : K → LL)) DFunLike.coe_injective
  refine h'.mono fun τ x hx => ?_
  have h2 := hx.2
  simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at h2
  simp only [Function.comp, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  exact h2

end Abstract

theorem toDR_FilLet : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (τ : K →ₐ[Qp] LL) (a : ℤ), Function.Surjective (algebraMap K₀ K) → τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i → FildR PD T.ρ τ a = (FilCris PD T.ρ a ⊓ DcrisL PD T.ρ (W.emb i)).map (ιV PD (LL := LL) (V := T.V)) → GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.toDR (PD := PD) T (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.FilLet W T i τ a) = FildR PD T.ρ τ a := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W T i τ a hs hτ hF
  apply le_antisymm
  · rintro _ ⟨x, ⟨hx, hx'⟩, rfl⟩
    have hxD : ιV PD (LL := LL) (V := T.V) x ∈ DdRE PD T.ρ τ :=
      ι_mem_DdRE PD T.ρ hs τ (by rw [hτ]; exact hx)
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (Submodule.mem_comap.1 hx')
    have hzD : z ∈ DdRE PD T.ρ τ := by
      have : z = ιV PD (LL := LL) (V := T.V) x - y := by rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hxD hy.1
    have hz0 : z = 0 := (Submodule.disjoint_def.1 (iSupIndep_DdRE PD T.ρ τ)) z hzD hz
    rw [← hyz, hz0, add_zero]
    exact hy
  · intro y hy
    have hy' := hy
    rw [hF] at hy'
    obtain ⟨x, hx, rfl⟩ := hy'
    exact ⟨x, ⟨hx.2, Submodule.mem_comap.2 (Submodule.mem_sup_left hy)⟩, rfl⟩

end GlobalTheory.Per.FilLetUnram
