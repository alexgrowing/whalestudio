import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDecoratedLatticeForms
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RowTest.ColField

open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coeff

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem coeff_bVV_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (i : VVIdx lam) (m) :
    coeff m ((bVV ℂ lam i : VV ℂ lam) : Pol ℂ ι n) ∈ A := by
  obtain ⟨P, hP⟩ := bVVfun_int ℂ lam i
  rw [bVV_coe, hP, coeff_map]
  exact intCast_mem A _

theorem coeff_mem_of_repr_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (v : VV ℂ lam)
    (h : ∀ i, (bVV ℂ lam).repr v i ∈ A) (m) : coeff m (v : Pol ℂ ι n) ∈ A := by
  have e := congrArg (fun x : VV ℂ lam => coeff m (x : Pol ℂ ι n)) ((bVV ℂ lam).sum_repr v)
  simp only [Submodule.coe_sum, Submodule.coe_smul, coeff_sum, coeff_smul, smul_eq_mul] at e
  rw [← e]
  exact sum_mem fun i _ => mul_mem (h i) (coeff_bVV_mem A lam i m)

theorem repr_mem_of_coeff_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (v : VV ℂ lam)
    (h : ∀ m, coeff m (v : Pol ℂ ι n) ∈ A) (i : VVIdx lam) : (bVV ℂ lam).repr v i ∈ A := by
  classical
  choose P hP using fun j => bVVfun_int ℂ lam j
  let s : A →+* ℂ := A.subtype
  let b' : VVIdx lam → MvPolynomial (ι × Fin n × Fin n) A := fun j => map (Int.castRingHom A) (P j)
  have hb' : ∀ j, map s (b' j) = ((bVV ℂ lam j : VV ℂ lam) : Pol ℂ ι n) := fun j => by
    rw [bVV_coe, hP, map_map]
    congr 1
  obtain ⟨v', hv'⟩ : ∃ v' : MvPolynomial (ι × Fin n × Fin n) A, map s v' = (v : Pol ℂ ι n) := by
    obtain ⟨F', hF'⟩ := (mem_range_map_iff_coeffs_subset (f := s)).2 (fun c hc => by
      obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
      exact ⟨⟨_, h m⟩, rfl⟩)
    exact ⟨F', hF'⟩
  have hliC : LinearIndependent ℂ fun j => ((bVV ℂ lam j : VV ℂ lam) : Pol ℂ ι n) :=
    (bVV ℂ lam).linearIndependent.map' (VV ℂ lam).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent A b' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have e := congrArg (map s) hg
    simp only [map_sum, map_zero, smul_eq_C_mul, map_mul, map_C, hb'] at e
    have e' : ∑ k, (s (g k)) • ((bVV ℂ lam k : VV ℂ lam) : Pol ℂ ι n) = 0 := by
      simpa only [smul_eq_C_mul] using e
    have := Fintype.linearIndependent_iff.1 hliC (fun k => s (g k)) e' j
    exact Subtype.ext this
  have hspan : v' ∈ Submodule.span A (Set.range b') := by
    by_contra hn
    have hopt : LinearIndependent A (fun o : Option (VVIdx lam) => Option.casesOn' o v' b') :=
      (linearIndependent_option' (x := v') (v := b')).2 ⟨hli, hn⟩
    have hC := Formalism.L2.Col.linearIndependent_map s _ hopt
    have hC' : LinearIndependent ℂ (fun o : Option (VVIdx lam) =>
        Option.casesOn' o (map s v') fun j => map s (b' j)) := by
      convert hC using 1
      funext o
      cases o <;> rfl
    obtain ⟨-, hnot⟩ := (linearIndependent_option' (x := map s v') (v := fun j => map s (b' j))).1 hC'
    apply hnot
    rw [hv']
    have hvs := congrArg (fun x : VV ℂ lam => (x : Pol ℂ ι n)) ((bVV ℂ lam).sum_repr v)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hvs
    rw [← hvs]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hb' j⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hspan
  have hvc : v = ∑ j, (s (c j)) • bVV ℂ lam j := by
    apply Subtype.ext
    rw [← hv', ← hc, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, ← hb', smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  rw [hvc, (bVV ℂ lam).repr_sum_self]
  exact (c i).2

theorem coeff_map_mem {ι' : Type} [Fintype ι'] {n' : ℕ} (A : Subfield ℂ) (lam : ι → DomWeight n)
    (mu : ι' → DomWeight n') (f : VV ℂ lam →ₗ[ℂ] VV ℂ mu)
    (hf : ∀ a b, LinearMap.toMatrix (bVV ℂ lam) (bVV ℂ mu) f a b ∈ A) (v : VV ℂ lam)
    (hv : ∀ m, coeff m (v : Pol ℂ ι n) ∈ A) (m) : coeff m ((f v : VV ℂ mu) : Pol ℂ ι' n') ∈ A := by
  classical
  refine coeff_mem_of_repr_mem A mu (f v) (fun a => ?_) m
  rw [← LinearMap.toMatrix_mulVec_repr (bVV ℂ lam) (bVV ℂ mu) f v, Matrix.mulVec, dotProduct]
  exact sum_mem fun b _ => mul_mem (hf a b) (repr_mem_of_coeff_mem A lam v hv b)

theorem coeff_rhoVr_mem {E : Type} [Field E] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) (A : Subfield ℂ)
    (hA : ∀ τ x, emb τ x ∈ A) (γE : GL (Fin n) E) (v : VV ℂ lam) (hv : ∀ m, coeff m (v : Pol ℂ ι n) ∈ A) (m) :
    coeff m ((rhoVr emb lam γE v : VV ℂ lam) : Pol ℂ ι n) ∈ A := by
  classical
  let R₀ : Subring (Pol ℂ ι n) := (MvPolynomial.map A.subtype).range
  have memR : ∀ F : Pol ℂ ι n, F ∈ R₀ ↔ ∀ m, coeff m F ∈ A := by
    intro F
    constructor
    · rintro ⟨F', rfl⟩ m
      rw [coeff_map]
      exact (coeff m F').2
    · intro h
      obtain ⟨F', hF'⟩ := (mem_range_map_iff_coeffs_subset (f := A.subtype)).2 (fun c hc => by
        obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
        exact ⟨⟨_, h m⟩, rfl⟩)
      exact ⟨F', hF'⟩
  have hblock : ∀ M : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ a b, M τ a b ∈ A) → ∀ F ∈ R₀,
      Formalism.GradedWeylDivisibility.blockAct ℂ M F ∈ R₀ := by
    intro M hM F hF
    obtain ⟨F', rfl⟩ := hF
    induction F' using MvPolynomial.induction_on with
    | C a =>
      rw [map_C, Formalism.GradedWeylDivisibility.blockAct, aeval_C]
      exact ⟨C a, by rw [map_C]; rfl⟩
    | add p q hp hq =>
      rw [map_add, map_add]
      exact add_mem hp hq
    | mul_X p w hp =>
      rw [map_mul, map_mul, map_X]
      refine mul_mem hp ?_
      rw [Formalism.GradedWeylDivisibility.blockAct, aeval_X]
      exact sum_mem fun b _ => mul_mem ⟨C ⟨_, hM _ _ _⟩, by rw [map_C]; rfl⟩ ⟨X _, map_X _ _⟩
  have hent : ∀ τ a b, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b ∈ A := by
    intro τ a b
    show ((((Formalism.UG.bc (emb τ) γE)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) b a ∈ A
    rw [← map_inv]
    exact hA τ _
  have hdet : ∀ τ, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ∈ A := by
    intro τ
    have e := RingHom.map_det A.subtype (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A))
    rw [show A.subtype.mapMatrix (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A)) =
      ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) from Matrix.ext fun a b => rfl] at e
    rw [← e]
    exact SetLike.coe_mem _
  have hdt : detTwK lam (invTrK (embGL emb γE)) ∈ A := by
    unfold detTwK
    refine prod_mem fun τ _ => ?_
    unfold Formalism.BasicNotions.detPow
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
    exact zpow_mem (hdet τ) _
  have htr : Formalism.L2.DIV.trAct (invTrK (embGL emb γE)) (v : Pol ℂ ι n) ∈ R₀ :=
    hblock _ (fun τ a b => hent τ b a) _ ((memR _).2 hv)
  show coeff m (Formalism.L2.DIV.actP lam (invTrK (embGL emb γE)) (v : Pol ℂ ι n)) ∈ A
  rw [Formalism.L2.DIV.actP, LinearMap.smul_apply, coeff_smul, smul_eq_mul]
  exact mul_mem hdt ((memR _).1 htr m)

end Coeff

theorem chainTo_preserves {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1))
    (P : ∀ j, V j → Prop) (hk : ∀ j v, P j v → P (j + 1) (k j v)) : ∀ N v, P 0 v → P N (GlobalTheory.FunObj.chainTo k N v)
  | 0, _, hv => hv
  | N + 1, v, hv => hk N _ (chainTo_preserves k P hk N v hv)

end GlobalTheory.RowTest.ColField

namespace GlobalTheory.RowTest.ColField

open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colMap_coeff_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (u : VV ℂ (wt ch.G (.top 0))), (∀ m, MvPolynomial.coeff m u.1 ∈ Set.range D.what₂.embLL) → ∀ m, MvPolynomial.coeff m (ch.S.colMap d (ch.S.ptTop c) u).1 ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ hF t Φ _ β hβ τ hτ d hd c u hu
  let K : Subfield ℂ := D.what₂.embLL.fieldRange
  have memK : ∀ z : ℂ, z ∈ K ↔ z ∈ Set.range D.what₂.embLL := fun z => Iff.rfl
  have hE : ∀ (σ : D.what₂.Tau) (x : D.host.E), tauE D σ x ∈ K := fun σ x =>
    ⟨labLL D σ x, GlobalTheory.Mem.R3.BrgRead.embLL_labLL_eq σ x⟩
  have hrat := (hF.isRatAt hβ hτ hd c).1
  have hu' : ∀ m, coeff m (u : Pol ℂ D.what₂.Tau (ch.G.V (.top 0)).rank) ∈ K := fun m => (memK _).2 (hu m)
  have h0 := coeff_rhoVr_mem (tauE D) (wt ch.G (.top 0)) K hE (ch.S.N.fr (.top 0))⁻¹ u hu'
  have hchain := chainTo_preserves (V := fun j => VV ℂ (wt ch.G (.top j)))
    (fun j => if h : j < D.R.m then ch.S.Z.kkMap 1 (d.1 ⟨j, h⟩) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) else 0)
    (fun j v => ∀ m, coeff m (v : Pol ℂ D.what₂.Tau (ch.G.V (.top j)).rank) ∈ K) (fun j v hv => by
      by_cases h : j < D.R.m
      · simp only [dif_pos h]
        exact coeff_map_mem K _ _ _ (fun a b => (memK _).2 (hrat ⟨j, h⟩ a b)) v hv
      · simp only [dif_neg h, LinearMap.zero_apply, ZeroMemClass.coe_zero, coeff_zero]
        exact fun _ => zero_mem K) D.R.m _ h0
  intro m
  exact (memK _).1 (hchain m)

end GlobalTheory.RowTest.ColField
