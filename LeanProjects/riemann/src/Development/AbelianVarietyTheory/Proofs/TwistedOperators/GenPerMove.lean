import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtCastMulReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Outer

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem outer_move (M : Vol G) {K : Subgroup (GL (Fin (G.V (.grid D.R.m D.R.m)).rank) (Lev.EAf D))}
    (hK : M.IsAt (.grid D.R.m D.R.m) K) (k : GA D (G.V (.grid D.R.m D.R.m))) (k' : GA D (G.V (.top D.R.m)))
    (hk : MeasurePreserving (fun h : GA D (G.V (.grid D.R.m D.R.m)) => h * k) (M.ν (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m)))
    (hk' : Measurable (fun h : GA D (G.V (.grid D.R.m D.R.m)) => h * k⁻¹))
    (ι : GA D (G.V (.grid D.R.m D.R.m)) → GA D (G.V (.top D.R.m)))
    (hι : ∀ h, ι h * k' = ι (h * k))
    (P P' : Fn G (.top D.R.m)) (S S' : Fn G (.grid D.R.m D.R.m))
    (hP : ∀ h, P (h * k') = P' h) (hS : ∀ h, S (h * k) = S' h)
    (hPl : ∀ γ ∈ GQ (G.V (.grid D.R.m D.R.m)), ∀ h, P (ι (γ * h)) = P (ι h))
    (hSl : ∀ γ ∈ GQ (G.V (.grid D.R.m D.R.m)), ∀ h, S (γ * h) = S h) :
    ∫ h in M.fd (.grid D.R.m D.R.m), P' (ι h) * S' h ∂M.ν (.grid D.R.m D.R.m) =
      ∫ h in M.fd (.grid D.R.m D.R.m), P (ι h) * S h ∂M.ν (.grid D.R.m D.R.m) := by
  rw [← setIntegral_fd_mul_right M hK k hk hk' (fun h => P (ι h) * S h) ?_]
  · congr 1
    funext h
    rw [← hP, ← hS, hι]
  · intro γ hγ h
    simp only [hPl γ hγ h, hSl γ hγ h]

end Outer

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Main

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem genPer_move (ch : Choice R)
    {μ0 : T} (hL : R.toLevCh.Is μ0) (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H)
    (hMr : ∀ j : Fin D.R.m, ∃ K, M.IsAt (.top j) K) (hMc : ∀ i : Fin (D.R.m + 1), ∃ K, M.IsAt (.grid i D.R.m) K)
    (hd1 : ∀ j, ch.S.toGridChoice.Z.HasVec (d.1 j)) (hd2 : ∀ i, ch.S.toGridChoice.Z.HasVec (d.2 i))
    (hξ : ∀ ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g)
    (hη : ∀ η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g)
    (g : Gc D.what₂.Tau (rowSizes D)) (Q Q' : PolCol ch.G × PolRow ch.G)
    (h1 : ∀ j : Fin D.R.m, ch.W.om (.top t j) (ch.G.toPair (.top t j) (ptTop ch.W g j) (ptTop ch.W g (j + 1)))
        (ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j)) =
      ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q'.1 j))
    (h2 : ∀ i : Fin D.R.m, ch.W.om (.chi i D.R.m) (ch.G.toPair (.chi i D.R.m) (ptGrid ch.W g i) (ptGrid ch.W g (i + 1)))
        (ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) =
      ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q'.2 i))
    (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W) (η : Module.Dual ℂ R.cX.W) :
    genPer ch t a M d y Q' (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹)
      (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹) =
      genPer ch t a M d y Q ξ η := by

  have hfc : ∀ (P : PolCol ch.G) (j : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.top t j)) (ch.G.pT (.top t j))
      (ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (P j)) := fun P j =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO ch.W.ψ_std ch.W.θ_is _ _ _ _
      (movedVec_theta_fockVac ch.W ch.S.toGridChoice t (.top t j) j.2 (d.1 j) (hd1 j)).1 (P j)
  have hfr : ∀ (P : PolRow ch.G) (i : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.chi i D.R.m)) (ch.G.pT (.chi i D.R.m))
      (ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (P i)) := fun P i =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO ch.W.ψ_std ch.W.θ_is _ _ _ _
      (movedVec_theta_fockVac ch.W ch.S.toGridChoice t (.chi i D.R.m) ⟨i.2, rfl⟩ (d.2 i) (hd2 i)).1 (P i)

  have hφ' : pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹) (ch.col a) = fun x => (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (x * ptTop ch.W g 0) :=
    funext (pairVec_mul_real (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (ptTop_mem ch.W g 0))
  have hF' : formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹) =
      fun x => (formGen ch t y η) (x * ptGrid ch.W g 0) :=
    funext (formGen_mul_real ch t y η (ptGrid_mem ch.W g 0))

  have hcol := pathLift_column_translate ch.W M t (ptTop ch.W g) D.R.m le_rfl
    (fun j hj => by
      obtain ⟨K, hK⟩ := hMr ⟨j, hj⟩
      refine ⟨⟨K, hK⟩, ?_⟩
      rw [ptTop_lt ch.W g hj]
      exact kappa_fst_move ch.W g ⟨j, hj⟩ hK)
    _ _ (hfc Q.1) h1 (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (hξ ξ)
  have hrow := pathLift_row_translate ch.W M (ptGrid ch.W g) D.R.m le_rfl
    (fun i hi => by
      obtain ⟨K, hK⟩ := hMc ⟨i, by omega⟩
      refine ⟨⟨K, hK⟩, ?_⟩
      rw [ptGrid_le ch.W g (by omega : i < D.R.m + 1)]
      exact kappa_snd_move ch.W g ⟨i, by omega⟩ hK)
    _ _ (hfr Q.2) h2 (formGen ch t y η) (hη η)

  have htop : ∀ h, stabilizerEmbedding ch.G.sp.topDec h * ptTop ch.W g D.R.m = stabilizerEmbedding ch.G.sp.topDec (h * ptGrid ch.W g D.R.m) := by
    intro h
    rw [ptTop_m, kappaTop_apply, ptGrid_le ch.W g (Nat.lt_succ_self D.R.m), GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul]
    rfl

  obtain ⟨K, hK⟩ : ∃ K, M.IsAt (.grid D.R.m D.R.m) K := hMc (Fin.last D.R.m)
  have hmv : MeasurePreserving (fun h : GA D (ch.G.V (.grid D.R.m D.R.m)) => h * ptGrid ch.W g D.R.m)
        (M.ν (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m)) ∧
      Measurable (fun h : GA D (ch.G.V (.grid D.R.m D.R.m)) => h * (ptGrid ch.W g D.R.m)⁻¹) := by
    rw [ptGrid_le ch.W g (Nat.lt_succ_self D.R.m)]
    exact kappa_snd_move ch.W g (Fin.last D.R.m) hK
  show defPer t ch.S.toGridChoice M Q' d (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹) (ch.col a))
      (formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹)) =
    defPer t ch.S.toGridChoice M Q d (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (formGen ch t y η)
  rw [hφ', hF']
  have hPl := fun (γ : GA D (ch.G.V (.grid D.R.m D.R.m))) (hγ : γ ∈ GQ (ch.G.V (.grid D.R.m D.R.m)))
      (h : GA D (ch.G.V (.grid D.R.m D.R.m))) =>
    (congrArg _ (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul ch.G.sp.topDec γ h)).trans
      (pathLift_column_leftInvariant ch.W M t D.R.m le_rfl _ (hfc Q.1) (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (hξ ξ) _
        (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational ch.G.sp.topDec γ hγ) (stabilizerEmbedding ch.G.sp.topDec h))
  have hSl := pathLift_row_leftInvariant ch.W M D.R.m le_rfl _ (hfr Q.2) (formGen ch t y η) (hη η)
  exact outer_move M hK (ptGrid ch.W g D.R.m) (ptTop ch.W g D.R.m) hmv.1 hmv.2 (stabilizerEmbedding ch.G.sp.topDec) htop _ _ _ _
    hcol hrow hPl hSl

end Main

end GlobalTheory.RowReal
