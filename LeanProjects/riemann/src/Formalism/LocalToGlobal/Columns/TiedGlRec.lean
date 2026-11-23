import Formalism.LocalToGlobal.Columns.TiedCls
import Formalism.LocalToGlobal.Columns.TiedXp
import Formalism.LocalToGlobal.Columns.TiedGlev
import Formalism.LocalToGlobal.Columns.TiedGlChi

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.UG Formalism.L2.DIV
open Formalism.L2.Forms (aOf skipOf fcOf InJ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} {hc : CMData X.F X.E} (hX : X.Ok) (hPr : Pr.Ok) (S : GSplit (Pr := Pr) hc) {m : ℕ}
  (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (hCh : Ch.Ok) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

def glevG (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
    (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.L) (a t nb skip fc : ℕ) (zl : Bool)
    (c : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal → (v.adicCompletionIntegers X.F)ˣ)
    (hc1 : ∀ i v h, IsLocalRing.residue (v.adicCompletionIntegers X.F) (c i v h) = 1)
    (hmem : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)), M ∈ (Λ (gwOf hc hPr i v h)).H ↔
      InJ a t fc zl ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h)))
    (hlam : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)) (hM : M ∈ (Λ (gwOf hc hPr i v h)).H),
      σ₀ (((Λ (gwOf hc hPr i v h)).lam ⟨M, hM⟩ : X.Kˣ) : X.K) =
        Formalism.L2.Forms.lamJ (glmPsi (S.eK hPr i v h) σ₀ (Ch.psi0 (gwOf hc hPr i v h)))
          (fun s => glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) s)) a t nb skip
          ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h))) :
    Formalism.L2.Forms.GLev (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev (tieGLoc hPr S Ch σ₀ hCh) a t nb skip fc zl := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact glevOf hPr S Ch σ₀ hCh Λ (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => (hPr.vT_norm u P hP : Ideal.absNorm P.asIdeal = Pr.T u)) (rls_T_notUnder hPr u)
    (colBase_index hc n hPr u) a t nb skip fc zl c hc1 hmem hlam

theorem glevG_fr (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
    (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.L) (a t nb skip fc : ℕ) (zl : Bool) (c) (hc1) (hmem) (hlam) :
    (glevG hX hPr S Ch σ₀ hCh u Λ c₀ s hS hs Q a t nb skip fc zl c hc1 hmem hlam).fr = fun i v h => glvD n v (c i v h) := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

def glevPG (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet X.E n (∅ : Finset (Pl X.E)) Pr.vGs)
    (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) (a t nb skip fc : ℕ) (zl : Bool)
    (hmem : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)), M ∈ (Λ (gwOf hc hPr i v h)).H ↔
      InJ a t fc zl ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h)))
    (hlam : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)) (hM : M ∈ (Λ (gwOf hc hPr i v h)).H),
      σ₀ (((Λ (gwOf hc hPr i v h)).lam ⟨M, hM⟩ : X.Kˣ) : X.K) =
        Formalism.L2.Forms.lamJ (glmPsi (S.eK hPr i v h) σ₀ (Ch.psi0 (gwOf hc hPr i v h)))
          (fun s => glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) s)) a t nb skip
          ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h))) :
    Formalism.L2.Forms.GLev (clsPG hc σ₀ Λ s hS hs Q).lev (tieGLoc hPr S Ch σ₀ hCh) a t nb skip fc zl := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact glevOf hPr S Ch σ₀ hCh Λ (ST := ∅) (π := 1) xp_basePi_one (by rw [map_one, mul_one, Nat.cast_one])
    (fun P => ⟨fun h => absurd h (Finset.notMem_empty P), fun h => absurd h (one_notMem P)⟩)
    (fun P hP => absurd hP (Finset.notMem_empty P))
    (fun v h => absurd (by rwa [Nat.cast_one] at h) ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top))
    (by rw [baseLb_index hc n ∅ (fun P => absurd P.2 (Finset.notMem_empty P.1))]; simp)
    a t nb skip fc zl (fun _ _ _ => 1) (fun _ _ _ => by rw [Units.val_one, map_one]) hmem hlam

theorem glevPG_fr (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet X.E n (∅ : Finset (Pl X.E)) Pr.vGs)
    (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) (a t nb skip fc : ℕ) (zl : Bool) (hmem) (hlam) :
    (glevPG hPr S Ch σ₀ hCh Λ s hS hs Q a t nb skip fc zl hmem hlam).fr = fun _ _ _ => 1 := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  funext i v h
  exact glvD_one n v

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hCh : d.Ch.Ok)
  (hl : d.lev = colLevS d.Ch) (hlP : d.levP = (rowTyG d.Ch (rPsharp d.Ch)).inv)

def recGLoc : Formalism.L2.Forms.GLoc d.host.F d.host.E (CF.sigD (d.colRec a)) d.host.g :=
  tieGLoc d.hPr S d.Ch d.σ₀ hCh

theorem recGLoc_K (hH : HostHyp d) (i : Fin 2) : ((recGLoc a S hCh).piG i : d.host.E) ∈ d.host.K := hH.piG_K i

theorem recGLoc_chi : Formalism.L2.Forms.CharacterCompatible (recGLoc a S hCh) d.R.m := tieGLoc_chiTied d.hPr S d.Ch d.σ₀ hCh

def recUnit (u : d.what₂.Word) (i : ℕ) (j : Fin 2) (v : HeightOneSpectrum (𝓞 d.X.F)) (h : (d.Pr.g j : 𝓞 d.X.F) ∈ v.asIdeal) :
    (v.adicCompletionIntegers d.X.F)ˣ :=
  if i = d.R.m then S.unitOf d.hPr j v h (d.Pr.piT u) (glk_piT_cong d.hPr u j) else 1

theorem recUnit_res (u : d.what₂.Word) (i : ℕ) (j : Fin 2) (v : HeightOneSpectrum (𝓞 d.X.F)) (h : (d.Pr.g j : 𝓞 d.X.F) ∈ v.asIdeal) :
    IsLocalRing.residue (v.adicCompletionIntegers d.X.F) (recUnit S u i j v h) = 1 := by
  unfold recUnit
  split_ifs
  · exact S.unitOf_res d.hPr j v h _ _
  · rw [Units.val_one, map_one]

def recGLev (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    Formalism.L2.Forms.GLev (classAgreement a hS hH hP u i hi).lev (recGLoc a S hCh) (aOf d.R i) d.R.t i (skipOf d.R i) (fcOf d.R i)
      (decide (i = d.R.m)) :=
  glevG d.hX d.hPr S d.Ch d.σ₀ hCh u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (stepCrd a hS hH u i hi) _ _ _ _ _ _
    (recUnit S u i) (recUnit_res S u i)
    (fun _ _ _ M => by rw [hl]; exact colLevS_mem_iff d.Ch hi _ _ M)
    (fun _ _ _ M hM => by revert hM; rw [hl]; intro hM; exact colLevS_lam_eq d.Ch hi _ _ d.σ₀ M hM)

theorem recGLev_fr (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    (recGLev a S hCh hl hS hH hP u i hi).fr = fun j v h => glvD (d.R.N i) v (recUnit S u i j v h) :=
  glevG_fr d.hX d.hPr S d.Ch d.σ₀ hCh u (d.lev i) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem recGLev_fr_const (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u u' : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m)
    (him : i < d.R.m) : (recGLev a S hCh hl hS hH hP u i hi).fr = (recGLev a S hCh hl hS hH hP u' i hi).fr := by
  rw [recGLev_fr, recGLev_fr]
  funext j v h
  unfold recUnit
  rw [if_neg him.ne, if_neg him.ne]

def recGLevP (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (u : d.what₂.Word) :
    Formalism.L2.Forms.GLev (parabolicClassAgreement a hS hH hP u).lev (recGLoc a S hCh) d.R.r d.R.t d.R.m (d.R.N d.R.m) (fcOf d.R d.R.m) false :=
  glevPG d.hPr S d.Ch d.σ₀ hCh d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c) (crdPr a hS hH) _ _ _ _ _ _
    (fun _ _ _ M => by rw [hlP]; exact rowTyG_sharp_mem_iff d.Ch _ _ M)
    (fun _ _ _ M hM => by
      revert hM; rw [hlP]; intro hM
      have e : ((rowTyG d.Ch (rPsharp d.Ch)).inv.inv _).lam ⟨M, hM⟩ = (rowTyG d.Ch (rPsharp d.Ch) _).lam ⟨M, hM⟩ := by
        show (((rowTyG d.Ch (rPsharp d.Ch) _).lam)⁻¹)⁻¹ ⟨M, hM⟩ = _
        rw [inv_inv]
      rw [e]
      exact rowTyG_sharp_lam_eq d.Ch _ _ d.σ₀ M hM)

theorem recGLevP_fr (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (u : d.what₂.Word) :
    (recGLevP a S hCh hlP hS hH hP u).fr = fun _ _ _ => 1 :=
  glevPG_fr d.hPr S d.Ch d.σ₀ hCh d.levP.inv _ _ _ _ _ _ _ _ _ _ _ _

end Rec

end Formalism.L2.Col
