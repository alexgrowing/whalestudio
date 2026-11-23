import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.DataParams
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Satake

abbrev Sys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

def SpanAt (V : HSp D) (e : AE D) (M : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (γ : GA D V) : Prop :=
  (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z, IntVec z ∧
    (fun a => finPart D e * (finMat D.sp.cm.sig V.gram γ).mulVec y a) = fun a => finPart D e * M.mulVec z a) ∧
  (∀ z, IntVec z → ∃ y ∈ Formalism.L2.NTheta.LamHat V,
    (fun a => finPart D e * (finMat D.sp.cm.sig V.gram γ).mulVec y a) = fun a => finPart D e * M.mulVec z a)

def IsFlagBasis (V : HSp D) (e : AE D) (B : Matrix (Fin V.rank) (Fin V.rank) (AE D)) : Prop :=
  SpanAt V e (B.map (finPart D)) 1 ∧
    (cA D e = e → ∀ i j : Fin V.rank, (i : ℕ) + j + 1 < V.rank →
      e * ∑ a, ∑ b, cA D (B a i) * incA D (V.gram a b) * B b j = 0)

def IwExp (V : HSp D) (e : AE D) (ϖ : D.host.E) (B : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (γ : GA D V)
    (a : Fin V.rank → ℤ) : Prop :=
  ∃ N : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
    (∀ i, N i i = 1) ∧ (∀ i j, j < i → N i j = 0) ∧
    SpanAt V e (B.map (finPart D) * N * Matrix.diagonal fun i => finPart D (incA D (ϖ ^ a i))) γ

open Classical in

def sphVal {n : ℕ} (inert : Prop) (q : ℕ) (α : Fin n → ℂ) (a : Fin n → ℤ) : ℂ :=
  ∏ i : Fin n, if inert → 2 * (i : ℕ) + 1 < n then
    (α i * (((q : ℝ) ^ (-(((n : ℝ) - 1 - 2 * (i : ℕ)) / 2)) : ℝ) : ℂ)) ^ a i else 1

def HasPar (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : Sys D) (P : HeightOneSpectrum (𝓞 D.host.E)) (s : Multiset ℂ) : Prop :=
  ∃ (α : Fin V.rank → ℂ) (e f : AE D) (ϖ : 𝓞 D.host.E) (B : Matrix (Fin V.rank) (Fin V.rank) (AE D)),
    Finset.univ.val.map α = s ∧ (∀ i, α i ≠ 0) ∧
    IsPrimeIdem P e f ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ IsFlagBasis V e B ∧
    (cA D e = e → (∀ i, α i * α i.rev = 1) ∧ ∀ i, i.rev = i → α i = 1) ∧
    ∀ (d : List ℤ) (Rp : Finset (GA D V)), Hecke₂ V J χ S P d Rp →
      ∃ a : GA D V → Fin V.rank → ℤ, (∀ γ ∈ Rp, IwExp V e (ϖ : D.host.E) B γ (a γ)) ∧
        c P d = ∑ γ ∈ Rp, sphVal (cA D e = e) (Ideal.absNorm P.asIdeal) α (a γ)

def str (x : ℂ) (q t : ℕ) : Multiset ℂ :=
  (Multiset.range t).map fun k => x * (((q : ℝ) ^ (((t : ℝ) - 1) / 2 - (k : ℝ)) : ℝ) : ℂ)

def typeSub (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) : Submodule ℂ (GA D V → ℂ) where
  carrier := {F | HasType V β L F}
  add_mem' := by
    intro F F' hF hF' κ hκ h
    simp only [Pi.add_apply, hF κ hκ h, hF' κ hκ h, mul_add]
  zero_mem' := by intro κ _ h; simp
  smul_mem' := by
    intro a F hF κ hκ h
    simp only [Pi.smul_apply, smul_eq_mul, hF κ hκ h]
    ring

def eigSub (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : Sys D) : Submodule ℂ (GA D V → ℂ) :=
  ⨅ (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D V)) (_ : Hecke₂ V J χ S P d Rp),
    LinearMap.ker (heckeLin V Rp - c P d • LinearMap.id)

example (α : Fin 2 → ℂ) : 4 * sphVal False 4 α ![1, 0] + sphVal False 4 α ![0, 1] = 2 * (α 0 + α 1) := by
  have h1 : (4 : ℝ) ^ (-((1 : ℝ) / 2)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  have h2 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e1 : -((((2 : ℕ) : ℝ) - 1 - 2 * (((0 : Fin 2) : ℕ) : ℝ)) / 2) = -((1 : ℝ) / 2) := by norm_num
  have e2 : -((((2 : ℕ) : ℝ) - 1 - 2 * (((1 : Fin 2) : ℕ) : ℝ)) / 2) = (1 : ℝ) / 2 := by norm_num
  have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  simp only [sphVal, Fin.prod_univ_two, false_imp_iff, if_true, e1, e2, h4, h1, h2]
  simp
  ring

example (x : ℂ) (q t : ℕ) : (str x q t).card = t := by simp [str]

end Satake

section Spaces

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

open Classical in

def badS (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Pg ∪ R.Q t).image fun PP => PP.under (𝓞 D.host.F)

def lvlP : Option Bool → LevelP R.Pg D.R.r ℂ
  | none => R.triv
  | some b => R.levL F b (sg0 D A)

variable (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ)

def JW : Set (GA D (Wc D i)) := levS _ (R.βW i) (R.datWp i P)

def chW : GA D (Wc D i) → ℂ := levChi _ (R.βW i) (R.datWp i P)

def datV : LevDat D.host.E ℂ (Vc D i).rank := withP (R.datVt i t) P

def JV : Set (GA D (Vc D i)) := levS _ (R.βV i) (datV R i t P)

def chV : GA D (Vc D i) → ℂ := levChi _ (R.βV i) (datV R i t P)

def MW : Submodule ℂ (R.HW i (sg0 D A)).H := (R.Wat i (sg0 D A) P).comap (R.HW i (sg0 D A)).e

def MWc (c : Sys D) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (partFull R.θ (R.MW i (sg0 D A)) (JW R i P) (chW R i P) (badS R t) c ⊓ R.Wat i (sg0 D A) P).comap
    (R.HW i (sg0 D A)).e

def IxW : Set (Sys D) := IxFull R.θ (R.MW i (sg0 D A)) (JW R i P) (chW R i P) (badS R t) (R.eWf i (sg0 D A))

def cmpV (ℓ : (R.cV i).W →ₗ[ℂ] ℂ) : (R.HV i t).H →ₗ[ℂ] (GA D (Vc D i) → ℂ) :=
  ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i t

def eV : (GA D (Vc D i) → ℂ) →ₗ[ℂ] (GA D (Vc D i) → ℂ) :=
  gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (RealDat.eC (A := A) (sg0 D A))

def XV : Submodule ℂ (R.HV i t).H :=
  ⨅ ℓ : (R.cV i).W →ₗ[ℂ] ℂ, (typeSub _ (R.βV i) (datV R i t P)).comap (cmpV R i t ℓ)

def V0 : Submodule ℂ (R.HV i t).H :=
  XV R i t P ⊓ ⨅ ℓ : (R.cV i).W →ₗ[ℂ] ℂ, (LinearMap.ker (eV R i t - LinearMap.id)).comap (cmpV R i t ℓ)

def XVc (c' : Sys D) : Submodule ℂ (R.HV i t).H :=
  XV R i t P ⊓ ⨅ ℓ : (R.cV i).W →ₗ[ℂ] ℂ,
    (eigSub _ (JV R i t P) (chV R i t P) (badS R t) c').comap (cmpV R i t ℓ)

def projectedFormsSystemPart (c' : Sys D) : Submodule ℂ (R.HV i t).H := V0 R i t P ⊓ XVc R i t P c'

def Transfer (c c' : Sys D) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 D.host.E), OffS D (badS R t) w → ∃ s : Multiset ℂ,
    HasPar (Wc D i) (JW R i P) (chW R i P) (badS R t) c w s ∧
    HasPar (Vc D i) (JV R i t P) (chV R i t P) (badS R t) c' w
      ((s + str (((R.C.mu0 i * R.xiH t).val w : ℂˣ) : ℂ) (Ideal.absNorm w.asIdeal) D.R.t).map
        fun z => z * (((R.C.eta.val w)⁻¹ : ℂˣ) : ℂ))

def thStar : (R.HW i (sg0 D A)).H →ₗ[ℂ] (R.HV i t).H := LinearMap.adjoint (R.thG i t)

def Z0 : Submodule ℂ (R.HV i t).H := (MW R i P).map (thStar R i t)

def OntoPartAt : Prop :=
  ∀ c ∈ IxW R i t P, (∃ c', Transfer R i t P c c') ∧
    ∀ c', Transfer R i t P c c' → (MWc R i t P c).map (thStar R i t) = projectedFormsSystemPart R i t P c'

def InjPartAt : Prop :=
  ∀ c ∈ IxW R i t P, (∃ c', Transfer R i t P c c') ∧
    ∀ c', Transfer R i t P c c' → Disjoint (projectedFormsSystemPart R i t P c') (LinearMap.ker (R.thG i t))

def SumAt : Prop :=
  (Z0 R i t P = ⨆ (c : IxW R i t P) (c' : Sys D) (_ : Transfer R i t P c c'), projectedFormsSystemPart R i t P c') ∧
    iSupIndep fun c : IxW R i t P => ⨆ (c' : Sys D) (_ : Transfer R i t P c c'), projectedFormsSystemPart R i t P c'

def KerAt : Prop :=
  let I : Set (Sys D) := {c' | (∀ w d, (¬ ∃ Rp, Hecke₂ (Vc D i) (JV R i t P) (chV R i t P) (badS R t) w d Rp) →
    c' w d = 0) ∧ ¬ ∃ c ∈ IxW R i t P, Transfer R i t P c c'}
  (LinearMap.ker (R.thG i t) ⊓ V0 R i t P = ⨆ c' : I, projectedFormsSystemPart R i t P c') ∧ iSupIndep fun c' : I => projectedFormsSystemPart R i t P c'

def AllGoodAt : Prop :=
  ∀ c ∈ IxW R i t P, ∀ c', Transfer R i t P c c' → XVc R i t P c' ≤ V0 R i t P

def BijAt : Prop :=
  Disjoint (MW R i P) (LinearMap.ker (thStar R i t)) ∧
    Module.finrank ℂ (Z0 R i t P) = Module.finrank ℂ (MW R i P)

def ThetaOntoAt : Prop := (V0 R i t P).map (R.thG i t) = MW R i P

def GoodTypes : Prop :=
  ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k ∧
      (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∀ (v : D.nd.PlG k) (j : Fin D.R.m) (a : (ZMod (D.host.g k))ˣ),
        algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (a : ZMod (D.host.g k)) = L.gen 1 →
        L.teich (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
            ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
          ((R.C.W.om k a ^ (2 * ((j : ℕ) + 1)) : ℂˣ) : ℂ) ∨
        L.teich (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
            ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
          (((R.C.W.om k a ^ (2 * ((j : ℕ) + 1)))⁻¹ : ℂˣ) : ℂ)

structure HidaSetting : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP
  scal : R.IsScal F
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  good : GoodTypes R

def LiftOnto : Prop := HidaSetting R F → ∀ i t b, OntoPartAt R i t (lvlP R F b)

def LiftInj : Prop := HidaSetting R F → ∀ i t b, InjPartAt R i t (lvlP R F b)

def ThetaOnto : Prop := HidaSetting R F → ∀ i t b, ThetaOntoAt R i t (lvlP R F b)

def FullEigenspaces : Prop :=
  HidaSetting R F → ∀ i t b, SumAt R i t (lvlP R F b) ∧ KerAt R i t (lvlP R F b) ∧ AllGoodAt R i t (lvlP R F b) ∧
    BijAt R i t (lvlP R F b)

end Spaces

end GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes

end
