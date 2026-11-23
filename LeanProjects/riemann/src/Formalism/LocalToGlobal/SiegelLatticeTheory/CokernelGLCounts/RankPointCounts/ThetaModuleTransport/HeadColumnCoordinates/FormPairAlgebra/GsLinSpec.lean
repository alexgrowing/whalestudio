import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.LamSZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.MulVecSingleApply

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def lamSL (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) : (Fin (r + 1) → O) →ₗ[O] E where
  toFun := lamS O cj Z
  map_add' a b := by simp [lamS, lamStarC, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by rw [lamS_smul, RingHom.id_apply, Subring.smul_def, smul_eq_mul]

variable (hO : ∀ x ∈ O, cj x ∈ O)
include hO

def lamSQ (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det) :
    MbMod (cjT O cj hO Z) →ₗ[O] E :=
  (headCols (cjT O cj hO Z)).liftQ (lamSL O cj Z) (fun k hk => by
    rw [LinearMap.mem_ker]; exact lamS_K O cj Z hO hu k hk)

omit hO in

def lamLQ (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det) :
    MbMod Z →ₗ[O] E :=
  (headCols Z).liftQ (lamL O Z) (fun k hk => by rw [LinearMap.mem_ker]; exact lamL_K O Z hu k hk)

theorem lamSQ_mk (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (y : Fin (r + 1) → O) : lamSQ O cj hO Z hu (Submodule.Quotient.mk y) = lamS O cj Z y := rfl

omit hO in
theorem lamLQ_mk (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (y : Fin (r + 1) → O) : lamLQ O Z hu (Submodule.Quotient.mk y) = lamL O Z y := rfl

theorem uniqL (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det) (t t' : O)
    (hη : EtaNZD O cj Z t t') (m m' : MbMod Z) (h : iL O cj hO Z t t' m = iL O cj hO Z t t' m')
    (hl : lamLQ O Z hu m = lamLQ O Z hu m') : m = m' := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m'
  rw [iL_mk, iL_mk, ← sub_eq_zero, ← Submodule.Quotient.mk_sub] at h
  rw [lamLQ_mk, lamLQ_mk] at hl
  have h' : (Submodule.Quotient.mk (Sum.elim (u - v) (0 : Fin (r + 1) → O)) :
      (Ix r → O) ⧸ relC O cj (Z.map O.subtype) t t') = 0 := by
    rw [← h]; congr 1; funext i; rcases i with i | i <;> simp
  have := (ker_zero O cj hO Z hu t t' hη (u - v) 0 h' (by rw [map_sub, hl, sub_self])
    (lamS_zero O cj Z)).1
  rwa [Submodule.Quotient.mk_sub, sub_eq_zero] at this

theorem uniqR (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det) (t t' : O)
    (hη : EtaNZD O cj Z t t') (m m' : MbMod (cjT O cj hO Z)) (h : iR O cj hO Z t t' m = iR O cj hO Z t t' m')
    (hl : lamSQ O cj hO Z hu m = lamSQ O cj hO Z hu m') : m = m' := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ m'
  rw [iR_mk, iR_mk, ← sub_eq_zero, ← Submodule.Quotient.mk_sub] at h
  rw [lamSQ_mk, lamSQ_mk] at hl
  have h' : (Submodule.Quotient.mk (Sum.elim (0 : Fin (r + 1) → O) (u - v)) :
      (Ix r → O) ⧸ relC O cj (Z.map O.subtype) t t') = 0 := by
    rw [← h]; congr 1; funext i; rcases i with i | i <;> simp
  have := (ker_zero O cj hO Z hu t t' hη 0 (u - v) h' (map_zero _) (by rw [lamS_sub, hl, sub_self])).2
  rwa [Submodule.Quotient.mk_sub, sub_eq_zero] at this

section Build

variable (t t' : O) (Za Zb : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
  (hua : IsUnit (Za.map O.subtype).det) (hub : IsUnit (Zb.map O.subtype).det) (hηb : EtaNZD O cj Zb t t')
  (θ : DDc O cj (Za.map O.subtype) t t' →ₗ[O] DDc O cj (Zb.map O.subtype) t t')
include hηb

theorem gs_ex (hΓ : ∀ p ∈ GamC O cj (Za.map O.subtype) t t', (θ p.1, p.2) ∈ GamC O cj (Zb.map O.subtype) t t')
    (m : MbMod (cjT O cj hO Za)) :
    ∃ n : MbMod (cjT O cj hO Zb), θ (iR O cj hO Za t t' m) = iR O cj hO Zb t t' n ∧
      lamSQ O cj hO Zb hub n = lamSQ O cj hO Za hua m := by
  obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have hp : ((Submodule.Quotient.mk (Sum.elim (0 : Fin (r + 1) → O) y') : DDc O cj (Za.map O.subtype) t t'),
      ((0 : E), lamStarC cj (Za.map O.subtype) (fun b => (y' b : E)))) ∈ GamC O cj (Za.map O.subtype) t t' :=
    ⟨Sum.elim 0 y', fun a => rfl, by simp⟩
  obtain ⟨Y₂, hY₂, he⟩ := hΓ _ hp
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2, h3⟩ := he
  have hl : Y₂ (Sum.inl (Fin.last r)) = 0 := Subtype.ext h2.symm
  have hY : Y₂ = Sum.elim (0 : Fin (r + 1) → O) (fun b => Y₂ (Sum.inr b)) := by
    funext i
    rcases i with i | i
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hl
      · simpa using hY₂ j
    · rfl
  refine ⟨Submodule.Quotient.mk (fun b => Y₂ (Sum.inr b)), ?_, ?_⟩
  · rw [iR_mk, iR_mk, h1, ← hY]
  · rw [lamSQ_mk, lamSQ_mk]; exact h3.symm

theorem g_ex (hΓ : ∀ p ∈ GamC' O cj (Za.map O.subtype) t t', (θ p.1, p.2) ∈ GamC' O cj (Zb.map O.subtype) t t')
    (m : MbMod Za) :
    ∃ n : MbMod Zb, θ (iL O cj hO Za t t' m) = iL O cj hO Zb t t' n ∧ lamLQ O Zb hub n = lamLQ O Za hua m := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have hp : ((Submodule.Quotient.mk (Sum.elim y (0 : Fin (r + 1) → O)) : DDc O cj (Za.map O.subtype) t t'),
      (lamC (Za.map O.subtype) (fun a => (y a : E)), (0 : E))) ∈ GamC' O cj (Za.map O.subtype) t t' :=
    ⟨Sum.elim y 0, fun b => rfl, by simp⟩
  obtain ⟨Y₂, hY₂, he⟩ := hΓ _ hp
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2, h3⟩ := he
  have hl : Y₂ (Sum.inr (Fin.last r)) = 0 := Subtype.ext h3.symm
  have hY : Y₂ = Sum.elim (fun a => Y₂ (Sum.inl a)) (0 : Fin (r + 1) → O) := by
    funext i
    rcases i with i | i
    · rfl
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hl
      · simpa using hY₂ j
  refine ⟨Submodule.Quotient.mk (fun a => Y₂ (Sum.inl a)), ?_, ?_⟩
  · rw [iL_mk, iL_mk, h1, ← hY]
  · rw [lamLQ_mk, lamLQ_mk, lamL_apply, lamL_apply]; exact h2.symm

theorem addR (f : MbMod (cjT O cj hO Za) → MbMod (cjT O cj hO Zb))
    (hf : ∀ m, θ (iR O cj hO Za t t' m) = iR O cj hO Zb t t' (f m) ∧ lamSQ O cj hO Zb hub (f m) = lamSQ O cj hO Za hua m)
    (m m' : MbMod (cjT O cj hO Za)) : f (m + m') = f m + f m' := by
  apply uniqR O cj hO Zb hub t t' hηb
  · rw [map_add (iR O cj hO Zb t t'), ← (hf (m + m')).1, ← (hf m).1, ← (hf m').1, map_add (iR O cj hO Za t t'), map_add θ]
  · rw [map_add (lamSQ O cj hO Zb hub), (hf (m + m')).2, (hf m).2, (hf m').2, map_add (lamSQ O cj hO Za hua)]

theorem smulR (f : MbMod (cjT O cj hO Za) → MbMod (cjT O cj hO Zb))
    (hf : ∀ m, θ (iR O cj hO Za t t' m) = iR O cj hO Zb t t' (f m) ∧ lamSQ O cj hO Zb hub (f m) = lamSQ O cj hO Za hua m)
    (c : O) (m : MbMod (cjT O cj hO Za)) : f (c • m) = c • f m := by
  apply uniqR O cj hO Zb hub t t' hηb
  · rw [map_smul (iR O cj hO Zb t t'), ← (hf (c • m)).1, ← (hf m).1, map_smul (iR O cj hO Za t t'), map_smul θ]
  · rw [map_smul (lamSQ O cj hO Zb hub), (hf (c • m)).2, (hf m).2, map_smul (lamSQ O cj hO Za hua)]

theorem addL (f : MbMod Za → MbMod Zb)
    (hf : ∀ m, θ (iL O cj hO Za t t' m) = iL O cj hO Zb t t' (f m) ∧ lamLQ O Zb hub (f m) = lamLQ O Za hua m)
    (m m' : MbMod Za) : f (m + m') = f m + f m' := by
  apply uniqL O cj hO Zb hub t t' hηb
  · rw [map_add (iL O cj hO Zb t t'), ← (hf (m + m')).1, ← (hf m).1, ← (hf m').1, map_add (iL O cj hO Za t t'), map_add θ]
  · rw [map_add (lamLQ O Zb hub), (hf (m + m')).2, (hf m).2, (hf m').2, map_add (lamLQ O Za hua)]

theorem smulL (f : MbMod Za → MbMod Zb)
    (hf : ∀ m, θ (iL O cj hO Za t t' m) = iL O cj hO Zb t t' (f m) ∧ lamLQ O Zb hub (f m) = lamLQ O Za hua m)
    (c : O) (m : MbMod Za) : f (c • m) = c • f m := by
  apply uniqL O cj hO Zb hub t t' hηb
  · rw [map_smul (iL O cj hO Zb t t'), ← (hf (c • m)).1, ← (hf m).1, map_smul (iL O cj hO Za t t'), map_smul θ]
  · rw [map_smul (lamLQ O Zb hub), (hf (c • m)).2, (hf m).2, map_smul (lamLQ O Za hua)]

def gsLin (hΓ : ∀ p ∈ GamC O cj (Za.map O.subtype) t t', (θ p.1, p.2) ∈ GamC O cj (Zb.map O.subtype) t t') :
    MbMod (cjT O cj hO Za) →ₗ[O] MbMod (cjT O cj hO Zb) where
  toFun m := (gs_ex O cj hO t t' Za Zb hua hub hηb θ hΓ m).choose
  map_add' := addR O cj hO t t' Za Zb hua hub hηb θ _ (fun m => (gs_ex O cj hO t t' Za Zb hua hub hηb θ hΓ m).choose_spec)
  map_smul' c m := by
    rw [RingHom.id_apply]
    exact smulR O cj hO t t' Za Zb hua hub hηb θ _ (fun m => (gs_ex O cj hO t t' Za Zb hua hub hηb θ hΓ m).choose_spec) c m

def gLin (hΓ : ∀ p ∈ GamC' O cj (Za.map O.subtype) t t', (θ p.1, p.2) ∈ GamC' O cj (Zb.map O.subtype) t t') :
    MbMod Za →ₗ[O] MbMod Zb where
  toFun m := (g_ex O cj hO t t' Za Zb hua hub hηb θ hΓ m).choose
  map_add' := addL O cj hO t t' Za Zb hua hub hηb θ _ (fun m => (g_ex O cj hO t t' Za Zb hua hub hηb θ hΓ m).choose_spec)
  map_smul' c m := by
    rw [RingHom.id_apply]
    exact smulL O cj hO t t' Za Zb hua hub hηb θ _ (fun m => (g_ex O cj hO t t' Za Zb hua hub hηb θ hΓ m).choose_spec) c m

theorem gsLin_spec (hΓ : ∀ p ∈ GamC O cj (Za.map O.subtype) t t', (θ p.1, p.2) ∈ GamC O cj (Zb.map O.subtype) t t')
    (m : MbMod (cjT O cj hO Za)) :
    θ (iR O cj hO Za t t' m) = iR O cj hO Zb t t' (gsLin O cj hO t t' Za Zb hua hub hηb θ hΓ m) ∧
      lamSQ O cj hO Zb hub (gsLin O cj hO t t' Za Zb hua hub hηb θ hΓ m) = lamSQ O cj hO Za hua m := (gs_ex O cj hO t t' Za Zb hua hub hηb θ hΓ m).choose_spec

theorem gLin_spec (hΓ : ∀ p ∈ GamC' O cj (Za.map O.subtype) t t', (θ p.1, p.2) ∈ GamC' O cj (Zb.map O.subtype) t t')
    (m : MbMod Za) :
    θ (iL O cj hO Za t t' m) = iL O cj hO Zb t t' (gLin O cj hO t t' Za Zb hua hub hηb θ hΓ m) ∧
      lamLQ O Zb hub (gLin O cj hO t t' Za Zb hua hub hηb θ hΓ m) = lamLQ O Za hua m := (g_ex O cj hO t t' Za Zb hua hub hηb θ hΓ m).choose_spec

end Build

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
