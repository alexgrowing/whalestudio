import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L} (T : Spl B)
  {S : Finset (Plc L)} {VL : ∀ w : Plc L, Lev (Kw w)} {A : SD B.Δ}

private theorem eU_congr {K : Type} [Field K] {Δ s s' : K} (e : s = s') (h : s * s = Δ) (h' : s' * s' = Δ) :
    eU h = eU h' := by subst e; rfl

private theorem eD_congr {K : Type} [Field K] {Δ s s' : K} (e : s = s') (h : s * s = Δ) (h' : s' * s' = Δ) :
    eD h = eD h' := by subst e; rfl

private theorem map_dg {k k' : Type} [Field k] [Field k'] {n : ℕ} (i : k ≃+* k') (d : Fin n → kˣ) :
    Matrix.GeneralLinearGroup.map (i : k →+* k') (diagT k (Fin n) d) =
      diagT k' (Fin n) fun a => Units.map (i : k →* k') (d a) := by
  ext a b
  simp only [Matrix.GeneralLinearGroup.map_apply, val_diagT]
  by_cases h : a = b
  · subst h; simp
  · simp [Matrix.diagonal_apply_ne _ h]

private theorem map_inj {k k' : Type} [Field k] [Field k'] {n : ℕ} (i : k ≃+* k') :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n) (i : k →+* k')) := by
  intro g g' h
  ext a b
  have := congrArg (fun x : GL (Fin n) k' => (x : Matrix (Fin n) (Fin n) k') a b) h
  simpa using this

private theorem levCore (hF : Fit T S VL A) {n : ℕ} (x : UA L n) (hx : x ∈ finU L n)
    (P : Pl (Lp L) → Prop) (E : ∀ v, v ∈ A.Sg → GL (Fin n) (Kv v))
    (hK : ∀ v, P v ↔ ∀ w, un w = v → cLoc w x ∈ GlobalTheory.LFun.KGL w n)
    (hE : ∀ w (_ : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg),
      cLoc w x = Matrix.GeneralLinearGroup.map ((T w h).i : Kv (un w) →+* Kw w) (E (un w) hv)) :
    ((∀ v (h : v ∈ A.Sg), E v h ∈ (A.V v).J n) ∧ ∀ v ∉ A.Sg, P v) ↔ x ∈ lev (Kall L n) S VL := by
  have memL : x ∈ lev (Kall L n) S VL ↔
      (x ∈ finU L n ∧ ∀ w, cLoc w x ∈ GlobalTheory.LFun.KGL w n) ∧ ∀ w ∈ S, cLoc w x ∈ (VL w).J n := by
    simp [lev, Kall, Subgroup.mem_inf, Subgroup.mem_iInf]
  rw [memL]
  have loc : ∀ w (hw : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg),
      cLoc w x ∈ (VL w).J n ↔ E (un w) hv ∈ (A.V (un w)).J n := by
    intro w hw h hv
    rw [hE w hw h hv]
    exact (T w h).J _ _ (hF.c w hw) (hF.H w hw h) n _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨hx, fun w => ?_⟩, fun w hw => ?_⟩
    · by_cases hv : un w ∈ A.Sg
      · obtain ⟨w0, hw0, e⟩ := (hF.sg _).1 hv
        have sp := hF.pl.split w0 hw0
        have hv0 : un w0 ∈ A.Sg := e ▸ hv
        have hk : cLoc w0 x ∈ GlobalTheory.LFun.KGL w0 n := by
          rw [hE w0 hw0 sp hv0]
          exact ((T w0 sp).K n _).2 (((Sig.finFacts _ (A.V (un w0))).2.2.2.2.2 n).2.2.2 (h1 _ hv0))
        exact (Br.uaFacts L n).2.2.2.2.2.2.2 w0 sp x hk w e.symm
      · exact (hK _).1 (h2 _ hv) w rfl
    · exact (loc w hw (hF.pl.split w hw) ((hF.sg _).2 ⟨w, hw, rfl⟩)).2 (h1 _ _)
  · rintro ⟨⟨_, h1⟩, h2⟩
    refine ⟨fun v hv => ?_, fun v _ => (hK v).2 fun w _ => h1 w⟩
    obtain ⟨w0, hw0, rfl⟩ := (hF.sg _).1 hv
    exact (loc w0 hw0 (hF.pl.split w0 hw0) hv).1 (h2 w0 hw0)

private theorem elCore (hF : Fit T S VL A) {n : ℕ} (x : UA L n) (hx : x ∈ finU L n)
    (O : Pl (Lp L) → Prop) (E : ∀ v, v ∈ A.Sg → GL (Fin n) (Kv v)) (d : ParN (Lp L) n)
    (hO : ∀ v, O v ↔ ∀ w, un w = v → cLoc w x = 1)
    (hE : ∀ w (_ : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg),
      cLoc w x = Matrix.GeneralLinearGroup.map ((T w h).i : Kv (un w) →+* Kw w) (E (un w) hv)) :
    ((∀ v (h : v ∈ A.Sg), E v h = Sig.dg (d v)) ∧ ∀ v ∉ A.Sg, O v) ↔
      OnS S x ∧ ∀ w ∈ S, ∀ h, cLoc w x = Sig.dg fun i => iu T w h (d (un w) i) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨hx, fun u hu => ?_⟩, fun w hw h => ?_⟩
    · have hv : un u ∉ A.Sg := fun hv => by
        obtain ⟨w, hw, e⟩ := (hF.sg _).1 hv
        exact hu w hw e.symm
      exact (hO _).1 (h2 _ hv) u rfl
    · have hv : un w ∈ A.Sg := (hF.sg _).2 ⟨w, hw, rfl⟩
      rw [hE w hw h hv, h1 _ hv]
      exact map_dg (T w h).i (d (un w))
  · rintro ⟨⟨_, h1⟩, h2⟩
    refine ⟨fun v hv => ?_, fun v hv => (hO v).2 fun w e => h1 w fun w' hw' e' => hv ?_⟩
    · obtain ⟨w0, hw0, rfl⟩ := (hF.sg _).1 hv
      have sp := hF.pl.split w0 hw0
      apply map_inj (T w0 sp).i
      rw [← hE w0 hw0 sp hv, h2 w0 hw0 sp]
      exact (map_dg (T w0 sp).i (d (un w0))).symm
    · exact (hF.sg _).2 ⟨w', hw', by rw [← e', e]⟩

private theorem expo_map {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k')
    (habs : ∀ (z : ℂ) (a : kˣ), absPow k' z (Units.map (i : k →* k') a) = absPow k z a)
    {n : ℕ} (ψ : Fin n → k'ˣ →* ℂˣ) (d : Fin n → kˣ) :
    Dict.expo ψ (fun a => Units.map (i : k →* k') (d a)) = Dict.expo (fun a => (ψ a).comp (Units.map (i : k →* k'))) d := by
  have hdet : ∀ {R : Type} [CommRing R] (t : Fin n → Rˣ) (a : Fin n),
      Matrix.GeneralLinearGroup.det ((leviTorus R (Fin n)) t a) = t a := fun t a =>
    congrFun ((leviTorus _ (Fin n)).symm_apply_apply t) a
  have h1 : torusChar ψ (fun a => Units.map (i : k →* k') (d a)) =
      torusChar (fun a => (ψ a).comp (Units.map (i : k →* k'))) d := by
    simp [torusChar_apply]
  have h2 : ((deltaHalf k' fun _ : Fin n => Unit).comp (leviTorus k' (Fin n)).toMonoidHom)
        (fun a => Units.map (i : k →* k') (d a)) =
      ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) d := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, deltaHalf_apply, deltaHalf_apply]
    refine Finset.prod_congr rfl fun a _ => ?_
    have e1 := hdet (fun a => Units.map (i : k →* k') (d a)) a
    have e2 := hdet d a
    simp only [MulEquiv.coe_toMonoidHom]
    rw [e1, e2]
    exact habs _ _
  simp only [Dict.expo]
  rw [h1, h2]

end SlopeTestRemainingChoices

section Main

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {B : Bridge L} (hB : B.Ok) (T : Spl B)
  {S : Finset (Plc L)} {VL : ∀ w : Plc L, Lev (Kw w)} {A : SD B.Δ} (hF : Fit T S VL A)

include hB hF in
private theorem hsG (w : Plc L) (hw : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg) (g : GA B.Δ) :
    cLoc w (B.bG g : UA L 3) =
      Matrix.GeneralLinearGroup.map ((T w h).i : Kv (un w) →+* Kw w) (eU (A.hs _ hv) (g.1 (un w))) := by
  rw [hB.splG w (T w h) g, eU_congr (hF.s w hw h) (A.hs _ hv) (T w h).hs]

include hB hF in
private theorem hsS (w : Plc L) (hw : w ∈ S) (h : IsSplitAt w) (hv : un w ∈ A.Sg) (g : SA B.Δ) :
    cLoc w (B.bS g : UA L 2) =
      Matrix.GeneralLinearGroup.map ((T w h).i : Kv (un w) →+* Kw w) (eD (A.hs _ hv) ((g : DA B.Δ).1 (un w))) := by
  rw [hB.splS w (T w h) g, eD_congr (hF.s w hw h) (A.hs _ hv) (T w h).hs]

private theorem hfS (g : SA B.Δ) : (B.bS g : UA L 2) ∈ finU L 2 := (B.bS g).2.1

include hB hF in
private theorem cl1 (hA : A.Ok) (g : GA B.Δ) : g ∈ A.dat.UG ↔ (B.bG g : UA L 3) ∈ lev (Kall L 3) S VL :=
  ((datOk _ _ A hA).2.2.2.1 g).trans (levCore T hF _ (B.bG g).2 (fun v => g.1 v ∈ KU (Ov v) _)
    (fun v h => eU (A.hs v h) (g.1 v)) (fun v => hB.KG g v) (fun w hw h hv => hsG hB T hF w hw h hv g))

include hB hF in
private theorem cl2 (hA : A.Ok) (g : SA B.Δ) :
    (g : DA B.Δ) ∈ A.dat.U2 ↔ (B.bS g : UA L 2) ∈ lev (Kall L 2) S VL :=
  ((datOk _ _ A hA).2.2.2.2 (g : DA B.Δ)).trans (levCore T hF _ (hfS g) (fun v => (g : DA B.Δ).1 v ∈ KD _ (Ov v))
    (fun v h => eD (A.hs v h) ((g : DA B.Δ).1 v)) (fun v => hB.KS g v) (fun w hw h hv => hsS hB T hF w hw h hv g))

include hB hF in
private theorem cl3 (g : GA B.Δ) (d : ParN (Lp L) 3) : A.IsElG g d ↔ OnS S (B.bG g : UA L 3) ∧
    ∀ w ∈ S, ∀ h, cLoc w (B.bG g : UA L 3) = Sig.dg fun i => iu T w h (d (un w) i) :=
  elCore T hF _ (B.bG g).2 (fun v => g.1 v = 1) (fun v h => eU (A.hs v h) (g.1 v)) d (fun v => hB.oneG g v)
    (fun w hw h hv => hsG hB T hF w hw h hv g)

include hB hF in
private theorem cl4 (g : SA B.Δ) (d : ParN (Lp L) 2) : A.IsElD g d ↔ OnS S (B.bS g : UA L 2) ∧
    ∀ w ∈ S, ∀ h, cLoc w (B.bS g : UA L 2) = Sig.dg fun i => iu T w h (d (un w) i) :=
  elCore T hF _ (hfS g) (fun v => (g : DA B.Δ).1 v = 1) (fun v h => eD (A.hs v h) ((g : DA B.Δ).1 v)) d
    (fun v => hB.oneS g v) (fun w hw h hv => hsS hB T hF w hw h hv g)

end Main

set_option maxHeartbeats 2000000 in
theorem levG : LevG := by
  intro L _ _ _ B hB T S VL A hA hF
  refine ⟨?_, ?_, ?_, ?_, fun w h n ψ d _ => expo_map (T w h).i (T w h).abs ψ d⟩
  · with_reducible exact cl1 hB T hF hA
  · with_reducible exact cl2 hB T hF hA
  · with_reducible exact cl3 hB T hF
  · with_reducible exact cl4 hB T hF

end UpperTheory.V.Z.Sym.So

end
