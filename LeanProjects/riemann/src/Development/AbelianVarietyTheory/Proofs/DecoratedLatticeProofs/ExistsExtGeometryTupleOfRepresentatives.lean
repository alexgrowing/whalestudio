import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDoubleDescentRanksOneThreeFive
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsCombAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteQuotientCosetsScaledStandardLatticeBox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenFix
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOneCombSphLevel

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QExtEx

section Orbits
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem corner_mul (g h : GL (n ⊕ Fin 0) k) :
    (g * h).val.toBlocks₁₁ = g.val.toBlocks₁₁ * h.val.toBlocks₁₁ := by
  rw [Units.val_mul, mul_toBlocks₁₁]
  have : g.val.toBlocks₁₂ * h.val.toBlocks₂₁ = 0 := by
    ext i j; simp [Matrix.mul_apply]
  rw [this, add_zero]

theorem corner_one : (1 : GL (n ⊕ Fin 0) k).val.toBlocks₁₁ = 1 := by
  ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem mulVec_mem_box {A : Matrix n n k} (hA : IntM A) {c : kˣ} {y : n → k} (hy : y ∈ box n c) :
    A *ᵥ y ∈ box n c := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le (hA i l) (hy l)

theorem sameOrb_equivalence (J : Subgroup (GL (n ⊕ Fin 0) k)) (hJ : J ≤ KO k _) (c : kˣ) :
    Equivalence (SameOrb J (box n c)) := by
  refine ⟨fun yb => ?_, fun {yb yb'} H => ?_, fun {yb yb' yb''} H H' => ?_⟩
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ yb
    exact ⟨1, one_mem _, y, rfl, by rw [corner_one, one_mulVec]⟩
  · obtain ⟨g, hg, y, rfl, e⟩ := H
    refine ⟨g⁻¹, inv_mem hg, g.val.toBlocks₁₁ *ᵥ y, e, ?_⟩
    rw [mulVec_mulVec, ← corner_mul, inv_mul_cancel, corner_one, one_mulVec]
  · obtain ⟨g, hg, y, rfl, e1⟩ := H
    obtain ⟨h, hh, y', e2, e3⟩ := H'
    refine ⟨h * g, mul_mem hh hg, y, rfl, ?_⟩
    rw [← e3, corner_mul, ← mulVec_mulVec, Submodule.Quotient.eq, ← mulVec_sub]
    have hI : IntM h.val.toBlocks₁₁ := fun i j => intM_of_mem_KO (hJ hh) (.inl i) (.inl j)
    refine mulVec_mem_box hI ?_
    rw [← e1] at e2
    exact (Submodule.Quotient.eq _).1 e2.symm

def orbSetoid (J : Subgroup (GL (n ⊕ Fin 0) k)) (hJ : J ≤ KO k _) (c : kˣ) : Setoid ((n → k) ⧸ box n c) :=
  ⟨SameOrb J (box n c), sameOrb_equivalence J hJ c⟩

def Orb (J : Subgroup (GL (n ⊕ Fin 0) k)) (hJ : J ≤ KO k _) (c₁ c₂ : kˣ) : Type :=
  ↥((Quotient.mk (orbSetoid J hJ c₂)) '' {yb | ∃ y ∈ box n c₁, Submodule.Quotient.mk y = yb})

instance (J : Subgroup (GL (n ⊕ Fin 0) k)) (hJ : J ≤ KO k _) (c₁ c₂ : kˣ) : Finite (Orb J hJ c₁ c₂) :=
  ((GlobalTheory.BoxCosets.finite_cosets k n c₁ c₂).image _).to_subtype

end Orbits

section Chars
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stabLat_one {Y : Type} [Fintype Y] [DecidableEq Y] : stabLat (1 : GL Y k) = KO k Y := by
  ext h; simp [mem_stabLat]

end Chars

section Level
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {κ t : Type} [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]

theorem twist_lev_le (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (j c : ℕ) (h : j + c = s + 1) :
    ((twistChain s t κ δ hδ η).lev j c h).J ≤ KO k _ := by
  have := (TypeDatum.map_conj (parahoric (κ ⊕ Fin (s + 1)) (Fin j × t) δ hδ) (plainFrame (stdOrd κ t j c h))).2.2
  rwa [show (plainFrame (stdOrd κ t j c h) : LatFrame k _ _).bas = 1 from rfl, stabLat_one] at this

theorem twist_lev_zero (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (c : ℕ) (h : 0 + c = s + 1) :
    ((twistChain s t κ δ hδ η).lev 0 c h).J = KO k _ ∧ ∀ x, ((twistChain s t κ δ hδ η).lev 0 c h).lam x = 1 := by
  have e1 : ∀ x, (plainFrame (stdOrd κ t 0 c h) : LatFrame k _ _).conj.symm x = (reGL (stdOrd κ t 0 c h)).symm x := by
    intro x; simp [LatFrame.conj, plainFrame]; rfl
  refine ⟨le_antisymm (twist_lev_le δ hδ η 0 c h) fun x hx => ?_, fun x => ?_⟩
  · change (plainFrame (stdOrd κ t 0 c h) : LatFrame k _ _).conj.symm x ∈ (parahoric (κ ⊕ Fin (s + 1)) (Fin 0 × t) δ hδ).J
    rw [e1, mem_parahoric]
    refine ⟨mem_KO.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i _ => i.1.elim0⟩
    · rw [reGL_symm_val]; exact (mem_KO.1 hx).1 _ _
    · rw [← map_inv, reGL_symm_val]; exact (mem_KO.1 hx).2 _ _
  · change (parahoric (κ ⊕ Fin (s + 1)) (Fin 0 × t) δ hδ).lam ⟨_, x.2⟩ = 1
    rw [parahoric_lam _ 1 (by ext i; exact i.1.elim0), map_one, map_one]

end Level

section Data
variable {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : QGeo v B PP)
  (δ : G.kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → G.kˣ →* ℂˣ) (A : RepFam G.k G.s (XIx (Fin D.R.k) (Fin D.R.t))) (M : ℕ)

def PiA (j : ℕ) : Type :=
  {g : ∀ d (_ : j + d = G.s), GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (d + 1)) G.k // ∀ d h, g d h ∈ A j d h}

theorem piA_finite (hfin : ∀ j d h, (A j d h).Finite) (j : ℕ) : Finite (PiA G A j) := by
  by_cases hj : j ≤ G.s
  · haveI := (hfin j (G.s - j) (by omega)).to_subtype
    refine Finite.of_injective (fun x : PiA G A j => (⟨x.1 (G.s - j) (by omega), x.2 _ _⟩ : ↥(A j (G.s - j) (by omega)))) ?_
    intro x y e
    apply Subtype.ext; funext d h
    obtain rfl : d = G.s - j := by omega
    exact congrArg Subtype.val e
  · exact @Finite.of_subsingleton _ ⟨fun x y => Subtype.ext (funext fun d => funext fun h => absurd h (by omega))⟩

def ChT (j : ℕ) : Type :=
  {x : PiA G A j // j ≠ G.s + 1} ⊕
    {o : Orb ((G.T δ hδ η).lev (G.s + 1) 0 rfl).J (twist_lev_le δ hδ η (G.s + 1) 0 rfl) (G.ϖ ^ M)⁻¹ (G.ϖ ^ M) // j = G.s + 1}

theorem chT_finite (hfin : ∀ j d h, (A j d h).Finite) (j : ℕ) : Finite (ChT G δ hδ η A M j) := by
  haveI := piA_finite G A hfin j; unfold ChT; infer_instance

def repT (j d : ℕ) (h : j + d = G.s) : ChT G δ hδ η A M j → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (d + 1)) G.k :=
  Sum.elim (fun x => x.1.1 d h) (fun o => False.elim (by have := o.2; omega))

def cosT : ChT G δ hδ η A M (G.s + 1) →
    (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) → G.k) ⧸ box (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1)) (G.ϖ ^ M) :=
  Sum.elim (fun x => absurd rfl x.2) (fun o => Quotient.out o.1.1)

def idxT (j : ℕ) : ℕ :=
  if h : j ≤ G.s + 1 then ((G.T δ hδ η).lev j (G.s + 1 - j) (by omega)).J.relIndex (KO G.k _)
  else (G.T δ hδ η).levTop.J.relIndex (KO G.k _)

def mT (j : ℕ) : Measure (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) :=
  haveI := G.unitVol.1; (Model.exists_haar G.ν (XIx (Fin D.R.k) (Fin D.R.t) j)).choose

theorem mT_spec (j : ℕ) : (mT G j).IsHaarMeasure ∧ mT G j (KO G.k (XIx (Fin D.R.k) (Fin D.R.t) j) : Set _) = 1 := by
  haveI := G.unitVol.1; exact (Model.exists_haar G.ν _).choose_spec

def wtT (j : ℕ) (α : ChT G δ hδ η A M j) : ℂ :=
  if h : j ≤ G.s then
    (((mT G j (prX (Cgrp ((G.T δ hδ η).lev j (G.s - j + 1) (by omega)).J
      (repT G δ hδ η A M j (G.s - j) (by omega) α)))).toReal⁻¹ : ℝ) : ℂ)
  else if h2 : j = G.s + 1 then (by
    subst h2
    exact (idxT G δ hδ η (G.s + 1) : ℂ) *
      (Nat.card {yb | SameOrb ((G.T δ hδ η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (cosT G δ hδ η A M α) yb} : ℂ))
  else (idxT G δ hδ η (G.s + 1 + 1) : ℂ)

open Classical in

def epsT (j : ℕ) (α : ChT G δ hδ η A M j) : GA D (c.V j) →₀ ℂ :=
  if j = 0 then Finsupp.single 1 1 else
  if hj : j ≤ G.s then
    (if H : ∃ e, IsOneComb G.ψk G.ν ((D.R.m - j) / 2) ((G.T δ hδ η).lev j (G.s - j + 1) (by omega))
        (repT G δ hδ η A M j (G.s - j) (by omega) α) e then
      H.choose.mapDomain (G.gl j (G.s - j + 1) (by omega)) else 0)
  else 0

def combOf (hstd : IsStdChar D c.ψ (-1)) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : Frame G.k S.rank Y') (FT : Frame G.k T.rank Y) (Ξ : Matrix Y Y' G.k → ℂ) : WO S T →₀ ℂ :=
  (CombAt.exists_isCombAt (ofSplit G.q) hstd FS FT Ξ).choose

theorem combOf_spec (hstd : IsStdChar D c.ψ (-1)) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] (FS : Frame G.k S.rank Y') (FT : Frame G.k T.rank Y) (Ξ : Matrix Y Y' G.k → ℂ) :
    (ofSplit G.q).IsCombAt c.ψ FS FT (combOf G hstd FS FT Ξ) Ξ :=
  (CombAt.exists_isCombAt (ofSplit G.q) hstd FS FT Ξ).choose_spec

def eLT (hstd : IsStdChar D c.ψ (-1)) (j : ℕ) : WO (c.V j) (c.V (j + 1)) →₀ ℂ :=
  if hj : j ≤ G.s then combOf G hstd (G.FY j (G.s - j + 1) (by omega)) (G.FY (j + 1) (G.s - j) (by omega))
    ((G.T δ hδ η).Phi j (G.s - j) (by omega)) else 0

def dLT (hstd : IsStdChar D c.ψ (-1)) (j : ℕ) (α : ChT G δ hδ η A M j) (γ : ChT G δ hδ η A M (j + 1)) :
    WO (c.X j) (c.X (j + 1)) →₀ ℂ :=
  if hj : j + 1 ≤ G.s then combOf G hstd (G.FX j (by omega)) (G.FX (j + 1) (by omega))
    ((G.T δ hδ η).entry G.ψk G.ν j (G.s - (j + 1)) (by omega) (repT G δ hδ η A M j (G.s - (j + 1) + 1) (by omega) α)
      (repT G δ hδ η A M (j + 1) (G.s - (j + 1)) (by omega) γ))
  else if h2 : j = G.s then (by
    subst h2
    exact combOf G hstd (G.FX G.s (by omega)) (G.FX (G.s + 1) le_rfl)
      ((G.T δ hδ η).xiPen (box _ (G.ϖ ^ M)) (repT G δ hδ η A M G.s 0 rfl α) (cosT G δ hδ η A M γ)))
  else if h3 : j = G.s + 1 then (by
    subst h3
    exact combOf G hstd (G.FX (G.s + 1) le_rfl) G.FM
      ((G.T δ hδ η).xiTop (box _ (G.ϖ ^ M)) G.ψk G.ν (-1) (cosT G δ hδ η A M α)))
  else 0

end Data

section Main

theorem repT_mem {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : QGeo v B PP)
    (δ : G.kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → G.kˣ →* ℂˣ) (A : RepFam G.k G.s (XIx (Fin D.R.k) (Fin D.R.t))) (M : ℕ)
    (j d : ℕ) (h : j + d = G.s) (α : ChT G δ hδ η A M j) : repT G δ hδ η A M j d h α ∈ A j d h := by
  rcases α with x | o
  · exact x.1.2 d h
  · exact absurd o.2 (by omega)

set_option maxHeartbeats 4000000 in

theorem exists_qExt : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle), c.Is → ∀ (δ : G.kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → G.kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → (∀ j, j ≤ G.s + 1 → (ofSplit G.q).IsComp (χ j)⁻¹ (η (j + 1) * δ)) → ∀ A, (G.T δ hδ η).IsRepSystem A G.ψk G.ν → ∀ M : ℕ, (G.T δ hδ η).Adapted A (box _ (G.ϖ ^ M)⁻¹) (box _ (G.ϖ ^ M)) → ∃ E : QExt G χ, E.δ = δ ∧ E.η = η ∧ E.A = A ∧ E.M = M := by
  intro D c v B PP G χ hc δ hδ η hη hcomp A hA M hM
  haveI := G.unitVol.1
  have hs := G.hs
  have hreg : (G.T δ hδ η).Regular := Chain.ofTwist_regular _ _ _ _ _
  have hlaws : (G.T δ hδ η).Laws := Chain.ofTwist_laws _ _ _ hη _ _
  have hfin : ∀ j d h, (A j d h).Finite :=
    (((GlobalTheory.UnfoldedEntries.chainFinite (ν := G.ν) G.cond) G.s _ _ (G.T δ hδ η) hreg hlaws).2 A hA).1
  have hstd := hc.std
  refine ⟨{
    δ := δ, tame := hδ, η := η, unr := hη, mu_comp := hcomp
    A := A, reps := hA
    Ch := ChT G δ hδ η A M
    fC := fun j => @Fintype.ofFinite _ (chT_finite G δ hδ η A M hfin j)
    rep := repT G δ hδ η A M
    rep_bij := ?_
    M := M, adapt := hM
    cos := cosT G δ hδ η A M
    cos_inj := ?_, cos_all := ?_, one := ?_
    eL := eLT G δ hδ η hstd
    eLT := combOf G hstd (G.FY (G.s + 1) 0 rfl) G.FT (G.T δ hδ η).PhiTop
    eL_at := ?_, eLT_at := combOf_spec _ _ _ _ _
    dL := dLT G δ hδ η A M hstd
    dL_mid := ?_, dL_pen := ?_, dL_top := ?_
    εL := epsT G δ hδ η A M
    εL_at := ?_, εL_zero := ?_
    idx := idxT G δ hδ η
    idx_mid := ?_, idx_top := ?_
    m := mT G, haar := mT_spec G
    wt := wtT G δ hδ η A M
    wt_mid := ?_, wt_pen := ?_, wt_top := ?_ }, rfl, rfl, rfl, rfl⟩
  ·
    intro j d h
    refine ⟨fun α _ => repT_mem G δ hδ η A M j d h α, fun α _ β _ e => ?_, fun g hg => ?_⟩
    · rcases α with x | o
      · rcases β with y | o'
        · exact congrArg Sum.inl (Subtype.ext (Subtype.ext (funext fun d' => funext fun h' => by
            obtain rfl : d' = d := by omega
            exact e)))
        · exact absurd o'.2 (by omega)
      · exact absurd o.2 (by omega)
    · have hx : ∃ x : PiA G A j, x.1 d h = g := by
        refine ⟨⟨fun d' _ => (show d' = d by omega) ▸ g, fun d' h' => ?_⟩, rfl⟩
        obtain rfl : d' = d := by omega
        exact hg
      obtain ⟨x, hx⟩ := hx
      exact ⟨.inl ⟨x, by omega⟩, trivial, hx⟩
  ·
    intro y y' H
    rcases y with x | o
    · exact absurd rfl x.2
    rcases y' with x' | o'
    · exact absurd rfl x'.2
    have e : Quotient.mk (orbSetoid _ (twist_lev_le δ hδ η (G.s + 1) 0 rfl) (G.ϖ ^ M)) (Quotient.out o.1.1) =
        Quotient.mk _ (Quotient.out o'.1.1) := Quotient.sound H
    rw [Quotient.out_eq, Quotient.out_eq] at e
    exact congrArg Sum.inr (Subtype.ext (Subtype.ext e))
  ·
    intro z hz
    exact ⟨.inr ⟨⟨Quotient.mk _ (Submodule.Quotient.mk z), ⟨_, ⟨z, hz, rfl⟩, rfl⟩⟩, rfl⟩,
      Quotient.mk_out (s := orbSetoid _ (twist_lev_le δ hδ η (G.s + 1) 0 rfl) (G.ϖ ^ M)) _⟩
  ·
    haveI := chT_finite G δ hδ η A M hfin (G.s + 1 + 1)
    letI := Fintype.ofFinite (ChT G δ hδ η A M (G.s + 1 + 1))
    refine Fintype.card_eq_one_iff.2 ⟨.inl ⟨⟨fun d h => absurd h (by omega), fun d h => absurd h (by omega)⟩, by omega⟩, ?_⟩
    rintro (x | o)
    · exact congrArg Sum.inl (Subtype.ext (Subtype.ext (funext fun d => funext fun h => absurd h (by omega))))
    · exact absurd o.2 (by omega)
  ·
    intro j d h
    obtain rfl : d = G.s - j := by omega
    unfold eLT
    rw [dif_pos (by omega)]
    exact combOf_spec _ _ _ _ _
  ·
    intro j d H α γ
    obtain rfl : d = G.s - (j + 1) := by omega
    unfold dLT
    rw [dif_pos (by omega)]
    exact combOf_spec _ _ _ _ _
  ·
    intro α y
    unfold dLT
    rw [dif_neg (by omega), dif_pos rfl]
    exact combOf_spec _ _ _ _ _
  ·
    intro y u
    unfold dLT
    rw [dif_neg (by omega), dif_neg (by omega), dif_pos rfl]
    exact combOf_spec _ _ _ _ _
  ·
    intro j ρ hρ d h α
    obtain rfl : d = G.s - j := by omega
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨Finsupp.single 1 1, ?_, ?_⟩
      · have hr : repT G δ hδ η A M 0 (G.s - 0) h α = 1 := by
          have := repT_mem G δ hδ η A M 0 (G.s - 0) h α
          rwa [hA.zero] at this
        rw [hr]
        obtain ⟨hJ, hl⟩ := twist_lev_zero (s := G.s) (κ := Fin D.R.k) (t := Fin D.R.t) δ hδ η (G.s - 0 + 1) (by omega)
        exact (GlobalTheory.QPl.SphOne.isOneComb_sph_level G.k _ _ (ρ + 1) (by omega) (by omega) G.ψk G.cond.continuous G.cond G.ν G.unitVol _ hJ hl).1
      · unfold epsT
        rw [if_pos rfl]
        simp
    · have hP : (D.R.m - j) / 2 = ρ + 1 := by omega
      have H : ∃ e, IsOneComb G.ψk G.ν ((D.R.m - j) / 2) ((G.T δ hδ η).lev j (G.s - j + 1) (by omega))
          (repT G δ hδ η A M j (G.s - j) (by omega) α) e := by
        rw [hP]
        exact GlobalTheory.QPl.OneComb.exists_isOneComb G.k _ _ (ρ + 1) (by omega) (by omega) G.ψk G.cond.continuous G.cond.ne_one G.ν
          (isSelfDual_of_isUnitVol G.ν G.cond G.unitVol) _ ⟨(hreg.2.2 _ _ _).1, (hreg.2.2 _ _ _).2.1⟩ _
      refine ⟨H.choose, ?_, ?_⟩
      · have H2 := H.choose_spec
        revert H2
        generalize H.choose = e
        rw [hP]
        exact id
      unfold epsT
      rw [if_neg hj0, dif_pos (by omega), dif_pos H]
  ·
    intro α
    unfold epsT
    rw [if_pos rfl]
  ·
    intro j d h
    obtain rfl : d = G.s + 1 - j := by omega
    unfold idxT
    rw [dif_pos (by omega)]
  ·
    unfold idxT
    rw [dif_neg (by omega)]
  ·
    intro j d h α
    obtain rfl : d = G.s - j := by omega
    unfold wtT
    rw [dif_pos (by omega)]
  ·
    intro y
    unfold wtT
    rw [dif_neg (by omega), dif_pos rfl]
  ·
    intro u
    unfold wtT
    rw [dif_neg (by omega), dif_neg (by omega)]

end Main

end GlobalTheory.QExtEx
