import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamRdefEqSgTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowActSmulOfWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSelfDualLatticeCoordsIffIntegralPosSpace

noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.RowStd

section Cast

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] {n n' : ℕ}

def castSp (h : n = n') : (Fin n → E) ≃ₗ[E] (Fin n' → E) :=
  LinearEquiv.funCongrLeft E E (finCongr h).symm

def SameWt (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n') : Prop :=
  ∀ τ i, (lam' τ).w i = (lam τ).w (Fin.cast h.symm i)

theorem sameWt_eq (lam lam' : ι → DomWeight n) (hl : SameWt rfl lam lam') : lam' = lam := by
  funext τ
  cases h1 : lam' τ with
  | mk w a =>
    cases h2 : lam τ with
    | mk w' a' =>
      have : w = w' := funext fun i => by
        have := hl τ i
        rw [h1, h2] at this
        simpa using this
      subst this
      rfl

def vvCast (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n') (hl : SameWt h lam lam') :
    VV K lam ≃ₗ[K] VV K lam' := by
  subst h
  exact LinearEquiv.ofEq _ _ (by rw [sameWt_eq lam lam' hl])

end Cast

section CastLemmas

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] {n n' : ℕ}

theorem vvCast_self (lam : ι → DomWeight n) (hl : SameWt rfl lam lam) :
    vvCast (K := K) rfl lam lam hl = LinearEquiv.refl K (VV K lam) := by
  ext x
  rfl

theorem vvCast_rhoV (emb : ι → E →+* K) (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (hl : SameWt h lam lam') (g : GL (Fin n) E) (g' : GL (Fin n') E) (hg : MatEq g' g) (v : VV K lam) :
    vvCast h lam lam' hl (rhoV emb lam g v) = rhoV emb lam' g' (vvCast h lam lam' hl v) := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  have hg' : g' = g := Units.ext (Matrix.ext fun i j => hg.2 i j i j rfl rfl)
  subst hg'
  rw [vvCast_self]
  rfl

end CastLemmas

section CastLemmas2

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] {n n' : ℕ}

theorem castSp_self : castSp (E := E) (rfl : n = n) = LinearEquiv.refl E (Fin n → E) := by
  ext x i
  rfl

theorem vvCast_pairV [StarRing K] (emb : ι → E →+* K) (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (hl : SameWt h lam lam') (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E)
    (hJ : ∀ i j, J' i j = J (Fin.cast h.symm i) (Fin.cast h.symm j)) (x y : VV K lam) :
    pairV emb lam' J' (vvCast h lam lam' hl x) (vvCast h lam lam' hl y) = pairV emb lam J x y := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  have hJ' : J' = J := Matrix.ext fun i j => hJ i j
  subst hJ'
  rw [vvCast_self]
  rfl

theorem vvCast_bVV_repr [StarRing K] (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (hl : SameWt h lam lam') (i : VVIdx lam) (j : VVIdx lam') :
    (bVV K lam').repr (vvCast h lam lam' hl (bVV K lam i)) j ∈ Formalism.DivisionValues.cmMax K := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  rw [vvCast_self, LinearEquiv.refl_apply, Module.Basis.repr_self]
  by_cases hij : i = j
  · subst hij
    rw [Finsupp.single_eq_same]
    exact (Formalism.DivisionValues.cmMax K).one_mem
  · rw [Finsupp.single_eq_of_ne (Ne.symm hij)]
    exact (Formalism.DivisionValues.cmMax K).zero_mem

theorem vvCast_nabAt [NumberField K] (emb : ι → E →+* K) (h : n = n') (lam : ι → DomWeight n)
    (lam' : ι → DomWeight n') (hl : SameWt h lam lam') (N : Submodule (𝓞 E) (Fin n → E)) :
    (nabAt emb lam N).map (((vvCast (K := K) h lam lam' hl).toLinearMap).restrictScalars (𝓞 K)) =
      nabAt emb lam' (N.map (((castSp (E := E) h).toLinearMap).restrictScalars (𝓞 E))) := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  rw [vvCast_self, castSp_self]
  simp only [LinearEquiv.refl_toLinearMap, LinearMap.restrictScalars_id, Submodule.map_id]

theorem vvCast_delAt [NumberField K] (emb : ι → E →+* K) (h : n = n') (lam : ι → DomWeight n)
    (lam' : ι → DomWeight n') (hl : SameWt h lam lam') (N : Submodule (𝓞 E) (Fin n → E)) :
    (delAt emb lam N).map (((vvCast (K := K) h lam lam' hl).toLinearMap).restrictScalars (𝓞 K)) =
      delAt emb lam' (N.map (((castSp (E := E) h).toLinearMap).restrictScalars (𝓞 E))) := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  rw [vvCast_self, castSp_self]
  simp only [LinearEquiv.refl_toLinearMap, LinearMap.restrictScalars_id, Submodule.map_id]

end CastLemmas2

section CastLemmas3

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] {n n' : ℕ}

theorem vvCast_bVV (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n') (hl : SameWt h lam lam') :
    ∃ f : VVIdx lam ≃ VVIdx lam', ∀ i, vvCast (K := K) h lam lam' hl (bVV K lam i) = bVV K lam' (f i) := by
  subst h
  have e := sameWt_eq lam lam' hl
  subst e
  exact ⟨Equiv.refl _, fun i => by rw [vvCast_self]; rfl⟩

theorem one_cast (h : n = n') (i j : Fin n') :
    (1 : Matrix (Fin n') (Fin n') E) i j = (1 : Matrix (Fin n) (Fin n) E) (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  simp only [Matrix.one_apply, Fin.cast_inj]

end CastLemmas3

section Gram

open GlobalTheory.Mem GlobalTheory.Mem.Col2

theorem gram_X'_eq_one (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (h : I.Ok) : X.toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := h.spaces
  change X.B.sp.X'.gram = 1
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

end Gram

end GlobalTheory.Mem.R3.RowStd

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowStd

theorem sameWt_true (X : Stages) :
    SameWt (RowAd.rank_X' X).symm X.B.wts.sgTrue (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) :=
  RowWeight.lamRdef_eq_sgTrue X

def wtCast (X : Stages) :
    VV X.toD7.what₂.LL X.B.wts.sgTrue ≃ₗ[X.toD7.what₂.LL] VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) :=
  vvCast (RowAd.rank_X' X).symm _ _ (sameWt_true X)

set_option maxHeartbeats 4000000 in

theorem exists_coef : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∃ c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W,
      (∀ v, c v = c0R (wtCast X v)) ∧
      (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E),
        Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) ∧
      LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) ∧
      Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ ∧
      (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) ∧
      ∀ t (P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ),
        (∀ x, P.coef x = c x) →
        (∀ c', RowAd.decoAd X I t (P.y c') = (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).outSec.rep c') →
        Bridge.CoefTie X.toD7.sp.X' cX.coef P (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
          (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) := by
  intro X px I hX U Xg tr L hI cX gramR c0R hc hgr hM hin
  have hw := sameWt_true X
  let e0 : VV X.toD7.what₂.LL X.B.wts.sgTrue ≃ₗ[X.toD7.what₂.LL] VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) :=
    vvCast (RowAd.rank_X' X).symm _ _ hw
  let c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W := (by with_unfolding_all exact (c0R.comp e0.toLinearMap :))
  have hgram := gram_X'_eq_one X I hI
  have hpair : ∀ x y, pairV (labLL X.toD7) (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) gramR (e0 x) (e0 y) =
      pairV X.B.fields.emb X.B.wts.sgTrue 1 x y := by
    intro x y
    rw [GlobalTheory.RowsSign.pairV_gramR_eq X px I hI cX gramR c0R hc hgr hM hin, hgram]
    exact vvCast_pairV (labLL X.toD7) _ _ _ hw 1 1 (one_cast (RowAd.rank_X' X).symm) x y
  have hInter : ∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E),
      Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v) := by
    intro γ γE g hγ hm v
    have key := vvCast_rhoV (labLL X.toD7) _ _ _ hw g γE hm v
    exact (congrArg c0R key).trans (hM.1 γ γE hγ _)
  obtain ⟨f, hf⟩ := vvCast_bVV (K := X.toD7.what₂.LL) (RowAd.rank_X' X).symm _ _ hw
  have hcf : (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) =
      (fun j => c0R (bVV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) j)) ∘ f := by
    funext i
    exact congrArg c0R (hf i)
  have hli : LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) := by
    rw [hcf]
    exact hM.2.1.comp f f.injective
  have hsp : Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ := by
    have h2 := f.surjective.range_comp (fun j => c0R (bVV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) j))
    rw [hcf]
    refine Eq.trans ?_ hM.2.2
    exact congrArg (Submodule.span ℂ) h2
  have hinn : ∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y) := by
    intro x y
    exact (hin _ _).trans (congrArg X.toD7.what₂.embLL (hpair x y))
  refine ⟨c, fun v => rfl, hInter, hli, hsp, hinn, fun t P hPc hPy => ⟨e0, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i j
    exact vvCast_bVV_repr _ _ _ hw i j
  · intro x
    exact hPc x
  · intro x x'
    exact hpair x x'
  · intro c'
    rw [RowLat.hLat_eq_decoAd_N X px I hX hI U t (P.y c'), hPy c']
    exact vvCast_nabAt (labLL X.toD7) _ _ _ hw _
  · intro c'
    rw [RowLat.hLat_eq_decoAd_N X px I hX hI U t (P.y c'), hPy c']
    exact vvCast_delAt (labLL X.toD7) _ _ _ hw _

end GlobalTheory.Mem.R3.RowStd
