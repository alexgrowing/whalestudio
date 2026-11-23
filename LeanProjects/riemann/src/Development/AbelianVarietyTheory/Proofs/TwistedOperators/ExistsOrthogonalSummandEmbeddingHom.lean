import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEquivEqSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqFinClSumAvg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMeasDefOfIsTermVol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RealType
open GlobalTheory.AutMult (toFin toInf)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel IsDefiniteSpace)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopIntegral

theorem isBlock_unique {R : Type} [Zero R] {N n : ℕ} {hN : N = n + 1} {A' B' : Matrix (Fin N) (Fin N) R}
    {A : Matrix (Fin n) (Fin n) R} {t : R} (h : GlobalTheory.BranchFormula.IsBlock hN A' A t) (h' : GlobalTheory.BranchFormula.IsBlock hN B' A t) :
    A' = B' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  have cover : ∀ i : Fin N, (∃ a : Fin n, i = Formalism.L2.Col.Br.iC hN a) ∨ i = Formalism.L2.Col.Br.iL hN := by
    intro i
    by_cases hi : i.val < n
    · exact Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    · right
      apply Fin.ext
      show i.val = n
      have := i.isLt
      omega
  ext i j
  rcases cover i with ⟨a, rfl⟩ | rfl <;> rcases cover j with ⟨b, rfl⟩ | rfl
  · rw [h1, h1']
  · rw [(h2 a).1, (h2' a).1]
  · rw [(h2 b).2, (h2' b).2]
  · rw [h3, h3']

theorem exists_avg_form {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [MeasurableSpace H]
    [BorelSpace H] (κ : Measure H) [κ.IsMulLeftInvariant] [IsFiniteMeasure κ] {A B : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (ρ : H →* Module.End ℂ A) (ρ' : H →* Module.End ℂ B) (Λ : Module.Dual ℂ A)
    (Λ' : Module.Dual ℂ B) (hc : ∀ v v', Continuous fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v')) :
    ∃ β : A →ₗ[ℂ] B →ₗ[ℂ] ℂ, (∀ v v', β v v' = ∫ k, Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') ∂κ) ∧
      ∀ k v v', β (ρ k v) (ρ' k v') = β v v' := by
  have hint : ∀ v v', Integrable (fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v')) κ := fun v v' =>
    (hc v v').integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  refine ⟨LinearMap.mk₂ ℂ (fun v v' => ∫ k, Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') ∂κ) ?_ ?_ ?_ ?_, fun v v' => rfl, ?_⟩
  · intro v₁ v₂ v'
    simp only [map_add, add_mul]
    exact integral_add (hint _ _) (hint _ _)
  · intro c v v'
    simp only [map_smul, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext k
    ring
  · intro v v₁ v₂
    simp only [map_add, mul_add]
    exact integral_add (hint _ _) (hint _ _)
  · intro c v v'
    simp only [map_smul, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext k
    ring
  · intro k v v'
    simp only [LinearMap.mk₂_apply]
    have e : ∀ j : H, Λ (ρ j⁻¹ (ρ k v)) * Λ' (ρ' j⁻¹ (ρ' k v')) =
        (fun j => Λ (ρ j⁻¹ v) * Λ' (ρ' j⁻¹ v')) (k⁻¹ * j) := by
      intro j
      simp only [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
    simp_rw [e]
    exact integral_mul_left_eq_self (μ := κ) (fun j => Λ (ρ j⁻¹ v) * Λ' (ρ' j⁻¹ v')) k⁻¹

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T}

theorem exists_orthogonal_summand_embedding_hom {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) :
    ∃ s : GA D A →* GA D B, Continuous s ∧ (∀ h, stabilizerEmbedding d h = s h) ∧ ∀ γ ∈ GQ A, s γ ∈ GQ B := by
  obtain ⟨s, hs, hrel, hrat⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A d.ι d.isom
  refine ⟨s, hs, fun h => ?_, hrat⟩
  exact ((hrel h _).1 ((embRel_iff d h _).2 rfl))

variable (G) in

theorem isV_last : (G.node (.grid D.R.m D.R.m)).IsV (rankV D D.R.m D.R.m) 0 := by
  have h := G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ (by
    intro j hj
    injection hj with h1 h2
    have := D.R.two_le_m
    omega)
  simpa [Node.neg, Node.rank] using h

variable (G) in

theorem isDefinite_last : IsDefiniteSpace (G.V (.grid D.R.m D.R.m)) := GlobalTheory.RowClaim.TermVolDef.isDefiniteSpace_of_isV (isV_last G)

variable (G) in

theorem one_le_rank_last : 1 ≤ (G.V (.grid D.R.m D.R.m)).rank := by
  rw [(isV_last G).rank, rankV, sLen]
  have := D.R.two_le_m
  nlinarith
private theorem isBlock_embGL' {n N : ℕ} (hN : N = n + 1) (g : GL (Fin n) ℂ) :
    GlobalTheory.BranchFormula.IsBlock hN (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g : Matrix (Fin N) (Fin N) ℂ)
      (g : Matrix (Fin n) (Fin n) ℂ) 1 := by
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [GlobalTheory.Branching.embGL_apply, dif_pos ⟨a.2, b.2⟩]
    rfl
  · rw [GlobalTheory.Branching.embGL_apply, dif_neg (fun h => absurd h.2 (lt_irrefl _)),
      if_neg (fun h => (ne_of_lt a.2) (congrArg Fin.val h))]
  · rw [GlobalTheory.Branching.embGL_apply, dif_neg (fun h => absurd h.1 (lt_irrefl _)),
      if_neg (fun h => (ne_of_lt a.2) (congrArg Fin.val h).symm)]
  · rw [GlobalTheory.Branching.embGL_apply, dif_neg (fun h => absurd h.1 (lt_irrefl _)), if_pos rfl]

variable {θ : InfFam D} (hθ : IsInfFam θ) (N : Std G U)
include hθ

theorem exists_real_point (u : D.what₂.Tau → Matrix.unitaryGroup (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) :
    ∃ k : GinfC (G.V (.grid D.R.m D.R.m)),
      rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec k) = rhoK (wt G (.top D.R.m)) (GlobalTheory.BrUnique.diagU G.sp.topDec.rank.symm u) ∧
      rhoAt θ N (.grid D.R.m D.R.m) k = rhoK (wt G (.grid D.R.m D.R.m)) (GlobalTheory.BrUnique.uGL u) := by
  have hX : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  have hu : ∀ τ, (invTrK (GlobalTheory.BrUnique.uGL u) τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) ∈
      Matrix.unitaryGroup (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ := by
    intro τ
    have e1 : (invTrK (GlobalTheory.BrUnique.uGL u) τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) =
        (star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ)).transpose := rfl
    have h1 : (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) *
        star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (u τ).2
    rw [e1, Matrix.mem_unitaryGroup_iff]
    have h2 : star (star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ)).transpose =
        (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ).transpose := by
      ext i j
      simp [Matrix.star_apply]
    rw [h2, ← Matrix.transpose_mul, h1, Matrix.transpose_one]
  obtain ⟨k, hk⟩ := GlobalTheory.RealType.exists_realAt_eq (hθ := hθ) (N := N) hX (invTrK (GlobalTheory.BrUnique.uGL u)) hu
  refine ⟨k, ?_, ?_⟩
  · rw [GlobalTheory.RealType.rhoAt_apply]
    refine congrArg (rhoK (wt G (.top D.R.m))) (funext fun τ => Units.ext ?_)
    have hb := GlobalTheory.RealType.isBlock_invTrK_realAt hθ N (k : GA D (G.V (.grid D.R.m D.R.m))) τ
    rw [hk, GlobalTheory.BrUnique.invTrK_invTrK] at hb
    exact isBlock_unique hb (isBlock_embGL' _ _)
  · rw [GlobalTheory.RealType.rhoAt_apply, hk, GlobalTheory.BrUnique.invTrK_invTrK]

theorem continuous_integrand (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) (v : VV ℂ (wt G (.top D.R.m)))
    (v' : VV ℂ (wt G (.grid D.R.m D.R.m))) : Continuous fun h : GA D (G.V (.grid D.R.m D.R.m)) =>
      Λ (rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec h)⁻¹ v) * Λ' (rhoAt θ N (.grid D.R.m D.R.m) h⁻¹ v') := by
  obtain ⟨s, hs, he, -⟩ := exists_orthogonal_summand_embedding_hom G.sp.topDec
  simp_rw [he]
  exact ((GlobalTheory.RealType.continuous_rhoAt (hθ := hθ) (N := N) (Λ := Λ) v).comp hs.inv).mul
    ((GlobalTheory.RealType.continuous_rhoAt (hθ := hθ) (N := N) (Λ := Λ') v').comp continuous_inv)

theorem real_average (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) (κ : Measure (GinfC (G.V (.grid D.R.m D.R.m))))
    [κ.IsMulLeftInvariant] [IsFiniteMeasure κ] :
    ∃ c : ℂ, ∀ (v : VV ℂ (wt G (.top D.R.m))) (v' : VV ℂ (wt G (.grid D.R.m D.R.m))),
      ∫ k, Λ (rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec k)⁻¹ v) * Λ' (rhoAt θ N (.grid D.R.m D.R.m) (k : GA D _)⁻¹ v') ∂κ =
        c * brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) v v' := by
  have hV := isDefinite_last G
  have : CompactSpace (GinfC (G.V (.grid D.R.m D.R.m))) :=
    isCompact_iff_compactSpace.mp (Formalism.IndefR.Eqv.isCompact_GinfC hV.1 hV.2)
  obtain ⟨s, -, he, -⟩ := exists_orthogonal_summand_embedding_hom G.sp.topDec
  let ρ : GinfC (G.V (.grid D.R.m D.R.m)) →* Module.End ℂ (VV ℂ (wt G (.top D.R.m))) :=
    (rhoAt θ N (.top D.R.m)).comp (s.comp (GinfC (G.V (.grid D.R.m D.R.m))).subtype)
  let ρ' : GinfC (G.V (.grid D.R.m D.R.m)) →* Module.End ℂ (VV ℂ (wt G (.grid D.R.m D.R.m))) :=
    (rhoAt θ N (.grid D.R.m D.R.m)).comp (GinfC (G.V (.grid D.R.m D.R.m))).subtype
  have e1 : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ k = rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec (k : GA D (G.V (.grid D.R.m D.R.m)))) := by
    intro k
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, he]
  have e1' : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ k⁻¹ = rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec (k : GA D (G.V (.grid D.R.m D.R.m))))⁻¹ := by
    intro k
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, map_inv, he]
  have e2 : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ' k = rhoAt θ N (.grid D.R.m D.R.m) (k : GA D (G.V (.grid D.R.m D.R.m))) := fun k => rfl
  have e2' : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ' k⁻¹ = rhoAt θ N (.grid D.R.m D.R.m) (k : GA D (G.V (.grid D.R.m D.R.m)))⁻¹ := fun k => rfl
  have hc : ∀ v v', Continuous fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') := by
    intro v v'
    simp_rw [e1', e2']
    exact (continuous_integrand hθ N Λ Λ' v v').comp continuous_subtype_val
  obtain ⟨β, hβ, hinv⟩ := exists_avg_form κ ρ ρ' Λ Λ' hc
  obtain ⟨c, hc'⟩ := GlobalTheory.BrUnique.brPair_unique G.sp.topDec.rank.symm (one_le_rank_last G)
    (fun τ => (GlobalTheory.WtInterlaceC.weights_top_grid G τ).1) (fun τ => (GlobalTheory.WtInterlaceC.weights_top_grid G τ).2) β (by
      intro u v f
      obtain ⟨k, hk1, hk2⟩ := exists_real_point hθ N u
      have h := hinv k v f
      rw [e1, e2, hk1, hk2] at h
      exact h)
  refine ⟨c, fun v v' => ?_⟩
  have h := hβ v v'
  simp_rw [e1', e2'] at h
  rw [← h]
  exact (DFunLike.congr_fun (DFunLike.congr_fun hc' v) v').trans rfl

end GlobalTheory.TopIntegral

end
