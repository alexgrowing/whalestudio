import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Gen
variable {F : Type} [Field F] [NumberField F] {Δ : F}

private theorem eD_congr {K : Type} [Field K] {Δ s s' : K} (h : s * s = Δ) (h' : s' * s' = Δ) (e : s = s') :
    Sig.eD h = Sig.eD h' := by
  subst e; rfl

private theorem mem_lvS (A : SD Δ) (y : DA Δ) (g : SA Δ) :
    g ∈ A.lvS y ↔ y⁻¹ * (g : DA Δ) * y ∈ A.dat.U2 := by
  unfold SD.lvS
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  show (MulAut.conj y⁻¹) (g : DA Δ) ∈ _ ↔ _
  rw [MulAut.conj_apply, inv_inv]

private theorem conj_at (y g : DA Δ) (v : Pl F) (h : y.1 v = 1) : (y⁻¹ * g * y).1 v = g.1 v := by
  have : (y⁻¹ * g * y).1 v = (y.1 v)⁻¹ * g.1 v * y.1 v := rfl
  rw [this, h, inv_one, one_mul, mul_one]

private theorem up (A A₀ : SD Δ) (hA : A.Ok) (hA₀ : A₀.Ok) (hE : A.Ext A₀) (x : DA Δ) (h0 : x ∈ A₀.dat.U2)
    (hn : ∀ v (h : v ∈ A.Sg), v ∉ A₀.Sg → Sig.eD (A.hs v h) (x.1 v) ∈ (Sig.Lev.iw (Kv v)).J 2) : x ∈ A.dat.U2 := by
  have d0 := ((datOk F Δ A₀ hA₀).2.2.2.2 x).1 h0
  refine ((datOk F Δ A hA).2.2.2.2 x).2 ⟨fun v hv => ?_, fun v hv => d0.2 v fun h => hv (hE.sub h)⟩
  by_cases h : v ∈ A₀.Sg
  · rw [hE.V v h, eD_congr (A.hs v hv) (A₀.hs v h) (hE.s v h)]
    exact d0.1 v h
  · rw [hE.iw v hv h]
    exact hn v hv h

end Gen

section Br
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L}

private theorem spl (hB : B.Ok) (w : Plc L) (R : B.toRingBr.Split w) (g : SA B.Δ)
    (h : cLoc w (B.bS g : UA L 2) ∈ (iw w).J 2) :
    Sig.eD R.hs ((g : DA B.Δ).1 (un w)) ∈ (Sig.Lev.iw (Kv (un w))).J 2 := by
  rw [hB.splS w R g] at h
  exact (R.J (Sig.Lev.iw _) (iw w) rfl (fun a => R.Uo a) 2 _).1 h

private theorem lev_mem {n : ℕ} {U : Subgroup (UA L n)} {S : Finset (Plc L)} {V : ∀ w : Plc L, Sig.Lev (Kw w)} {x : UA L n}
    (h : x ∈ lev U S V) : x ∈ U ∧ ∀ w ∈ S, cLoc w x ∈ (V w).J n := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h
  refine ⟨h1, fun w hw => ?_⟩
  simp only [Subgroup.mem_iInf] at h2
  exact h2 w hw

end Br

set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.Z.Sym.So.levExt :
    UpperTheory.V.Z.Sym.So.LevExt := by
  intro L _ _ _ B hB T S VL A hA hF A₀ hA₀ hE S₁ h1 _ U y hy hU g hg
  obtain ⟨hgU, hgJ⟩ := lev_mem hg
  refine (mem_lvS A y g).2 (up A A₀ hA hA₀ hE _ ((mem_lvS A₀ y g).1 (hU g hgU)) ?_)
  intro v hv h0
  obtain ⟨w, hwS, rfl⟩ := (hF.sg v).1 hv
  have hsp : IsSplitAt w := hF.pl.split w hwS
  rw [conj_at y (g : DA B.Δ) _ (hy _ hv), eD_congr (A.hs _ hv) (T w hsp).hs (hF.s w hwS hsp)]
  exact spl hB w (T w hsp) g (hgJ w ((h1 w hwS).resolve_right h0))

end
