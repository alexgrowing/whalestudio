import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.DoubledUnramifiedFrames
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.StepData (XIx Ix latOf box LatFrame)
open GlobalTheory.LocMod (GAt PinGBy ofSplit MovedTo)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastPair lastKer)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences (IsFockOver StepsAll vec atW IsMoved InAt InvOnUnits IsBesFrame IsJacFrame FrameMapsPrefix jacLat ptBF ptFB)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RouteCompare

variable {D : D7}

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def toFin (p : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank n) : Frame p S n :=
  ⟨F.β, F.γ, F.βγ, F.γβ, (GlobalTheory.LocGrp.exists_hom (ofSplit p) F).choose,
    fun g => ((GlobalTheory.LocGrp.exists_hom (ofSplit p) F).choose_spec g).1,
    fun g => ((GlobalTheory.LocGrp.exists_hom (ofSplit p) F).choose_spec g).2⟩

def move {p : SplitPt D k} {S : HSp D} (β : Frame p S n) (g : GA D S) : Frame p S n :=
  toFin p S ⟨(mt S g).map p.pr * β.b, β.b' * (mt S g⁻¹).map p.pr,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, ← Matrix.map_mul]; simp [Formalism.L2.Theta.mt],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ β.b, ← Matrix.map_mul]; simp [Formalism.L2.Theta.mt, β.b'b]⟩

theorem isMoved_move {p : SplitPt D k} {S : HSp D} (β : Frame p S n) (g : GA D S) : IsMoved g β (move β g) := rfl

theorem isMoved_back {p : SplitPt D k} {S : HSp D} (β : Frame p S n) (g : GA D S) : IsMoved g (move β g⁻¹) β := by
  change β.b = (mt S g).map p.pr * ((mt S g⁻¹).map p.pr * β.b)
  rw [← Matrix.mul_assoc, ← Matrix.map_mul]
  simp [Formalism.L2.Theta.mt]

def IsCharBy (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle) (θ : k) : Prop :=
  ∀ a, (χ a : ℂ) = psiE ψ (p.sec (θ * a))

def BesCols {p : SplitPt D k} {ρ : ℕ} (B : BesLev D ρ) (θ s : k) (α : Frame p B.A n) (β : Frame p B.V (n ⊕ Fin c)) : Prop :=
  c = 2 * ρ + 1 ∧ (∀ r a, β.b r (Sum.inl a) = ((B.d.i₀ * B.o.iA).map (ofSplit p).pr * α.b) r a) ∧
    (∀ (i : Fin ρ) (j : Fin c), j.val = i.val → ∀ r, β.b r (Sum.inr j) = s * θ ^ (ρ - i.val) * (ofSplit p).pr (B.d.e r i)) ∧
    (∀ j : Fin c, j.val = ρ → ∀ r, β.b r (Sum.inr j) = s * (ofSplit p).pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r)) ∧
    ∀ (i : Fin ρ) (j : Fin c), j.val + i.val = 2 * ρ → ∀ r,
      β.b r (Sum.inr j) = s * (-(ofSplit p).hz B / θ) * (-1 / θ) ^ (ρ - 1 - i.val) * (ofSplit p).pr (B.d.e' r i)

def JacCols {p : SplitPt D k} {ρ : ℕ} (J : JacLev D ρ) (θ s a : k) (α : Frame p J.W₀ n) (β : Frame p J.W (n ⊕ Fin c)) : Prop :=
  c = 2 * ρ ∧ (∀ r b, β.b r (Sum.inl b) = (J.d.i₀.map (ofSplit p).pr * α.b) r b) ∧
    (∀ (i : Fin ρ) (j : Fin c), j.val = i.val → ∀ r, β.b r (Sum.inr j) = s * θ ^ (ρ - i.val) * (ofSplit p).pr (J.d.e r i)) ∧
    ∀ (i : Fin ρ) (j : Fin c), j.val + i.val + 1 = 2 * ρ → ∀ r,
      β.b r (Sum.inr j) = s * a * (-1 / θ) ^ (ρ - 1 - i.val) * (ofSplit p).pr (J.d.e' r i)

theorem besCols_toFin {p : SplitPt D k} {ρ : ℕ} (B : BesLev D ρ) (s : k) (α : GlobalTheory.LocMod.Frame k B.A.rank n)
    (β : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin c)) :
    BesCols B (ofSplit p).xi s (toFin p _ α) (toFin p _ β) ↔ (ofSplit p).IsBesFrame B s α β := Iff.rfl

theorem jacCols_toFin {p : SplitPt D k} {ρ : ℕ} (J : JacLev D ρ) (s h : k) (α : GlobalTheory.LocMod.Frame k J.W₀.rank n)
    (β : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin c)) :
    JacCols J (ofSplit p).xi s (h / (ofSplit p).xi) (toFin p _ α) (toFin p _ β) ↔ (ofSplit p).IsJacFrame J s h α β := Iff.rfl

open GlobalTheory.LocMod.Witness in

theorem exists_jacCols {p : SplitPt D k} {ρ : ℕ} (J : JacLev D ρ) {θ s a : k} (hθ : θ ≠ 0) (hs : s ≠ 0) (ha : a ≠ 0)
    (α : Frame p J.W₀ n) (hc : c = 2 * ρ) : ∃ β : Frame p J.W (n ⊕ Fin c), JacCols J θ s a α β := by
  subst hc
  obtain ⟨G, hG⟩ := exists_witt (ofSplit p) J.d (GlobalTheory.LocMod.Frame.ofFinPl α)
  obtain ⟨F, hF⟩ := exists_scaled' G
    (Sum.map id (Sum.elim (fun i : Fin ρ => (⟨i.val, by omega⟩ : Fin (2 * ρ))) fun i : Fin ρ => ⟨2 * ρ - 1 - i.val, by omega⟩))
    (by
      rintro (a | a | a) (b | b | b) h <;> simp [Fin.ext_iff] at h ⊢ <;> first | exact h | omega)
    (by simp; ring)
    (Sum.elim (fun _ => 1) (Sum.elim (fun i => s * θ ^ (ρ - i.val)) fun i => s * a * (-1 / θ) ^ (ρ - 1 - i.val)))
    (by rintro (a | a | a) <;> simp [hs, ha, hθ])
  rw [hG] at hF
  refine ⟨toFin p _ F, rfl, fun r a => (hF r (Sum.inl a)).trans (one_mul _), fun i j h r => ?_, fun i j h r => ?_⟩
  · rw [show j = ⟨i.val, by omega⟩ from Fin.ext h]
    exact hF r (Sum.inr (Sum.inl i))
  · rw [show j = ⟨2 * ρ - 1 - i.val, by omega⟩ from Fin.ext (by simp only; omega)]
    exact hF r (Sum.inr (Sum.inr i))

open GlobalTheory.LocMod.Witness in

theorem exists_besCols {p : SplitPt D k} {ρ : ℕ} (B : BesLev D ρ) {θ s : k} (hθ : θ ≠ 0) (hs : s ≠ 0)
    (α : Frame p B.A n) (hc : c = 2 * ρ + 1) : ∃ β : Frame p B.V (n ⊕ Fin c), BesCols B θ s α β := by
  subst hc
  obtain ⟨F₀, h₀⟩ := exists_core (ofSplit p) B one_ne_zero (GlobalTheory.LocMod.Frame.ofFinPl α)
  obtain ⟨G, hG⟩ := exists_witt (ofSplit p) B.d F₀
  have hz := hz_ne (ofSplit p) B
  obtain ⟨F, hF⟩ := exists_scaled' G
    (Sum.elim (Sum.map id fun _ => (⟨ρ, by omega⟩ : Fin (2 * ρ + 1)))
      (Sum.elim (fun i : Fin ρ => Sum.inr (⟨i.val, by omega⟩ : Fin (2 * ρ + 1)))
        fun i : Fin ρ => Sum.inr ⟨2 * ρ - i.val, by omega⟩))
    (by
      rintro ((a | a) | a | a) ((b | b) | b | b) h <;> simp [Fin.ext_iff] at h ⊢ <;> first | exact h | omega)
    (by simp; ring)
    (Sum.elim (Sum.elim (fun _ => 1) fun _ => s)
      (Sum.elim (fun i => s * θ ^ (ρ - i.val)) fun i => s * (-(ofSplit p).hz B / θ) * (-1 / θ) ^ (ρ - 1 - i.val)))
    (by rintro ((a | a) | a | a) <;> simp [hs, hz, hθ])
  rw [hG] at hF
  refine ⟨toFin p _ F, rfl, fun r a => ((hF r (Sum.inl (Sum.inl a))).trans (one_mul _)).trans ?_, fun i j h r => ?_,
    fun j h r => ?_, fun i j h r => ?_⟩
  · change (B.d.i₀.map (prH (ofSplit p)) * F₀.β) r (Sum.inl a) = ((B.d.i₀ * B.o.iA).map (prH (ofSplit p)) * α.b) r a
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun u _ => by rw [h₀.1]; rfl
  · rw [show j = ⟨i.val, by omega⟩ from Fin.ext h]
    exact hF r (Sum.inr (Sum.inl i))
  · rw [show j = ⟨ρ, by omega⟩ from Fin.ext h]
    refine (hF r (Sum.inl (Sum.inr ()))).trans (congrArg (s * ·) ?_)
    change (B.d.i₀.map (prH (ofSplit p)) * F₀.β) r (Sum.inr ()) = prH (ofSplit p) (∑ u, B.d.i₀ r u * vecB B.o B.ζ u)
    rw [Matrix.mul_apply, map_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [h₀.2, one_mul, map_mul]; rfl
  · rw [show j = ⟨2 * ρ - i.val, by omega⟩ from Fin.ext (by simp only; omega)]
    exact hF r (Sum.inr (Sum.inr i))

end Local

def PrimCol {S : HSp D} {ρ : ℕ} (L : Lat S) (v : Pl D) (x : Mx D S.rank ρ) (i : Fin ρ) : Prop :=
  ∀ a ∈ idAt D (· = v), colMul x i a ∈ latV S L (· = v) ↔ a ∈ intAt D (· = v)

def AgreeSplit (χ χ' : (AE D)ˣ →* Circle) : Prop :=
  ∀ e, IsSplitIdem D e → ∀ u x : (AE D)ˣ, (x : AE D) = e * u + (1 - e) → χ x = χ' x

def FockMap (ψ : AddChar (AF D.host.F) ℂ) {S T S' T' : HSp D} (LS : Lat S) (LT : Lat T) (LS' : Lat S') (LT' : Lat T')
    (𝔉 : (WO S T → ℂ) → WO S' T' → ℂ) : Prop :=
  ∀ (θ : InfFam D) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) →
    ∃ (sS' BS' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ)
      (sT' BT' : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ),
      (∀ τ, IsCartanInv (gramAt D S' τ) (sS' τ)) ∧ (∀ τ, IsCartanInv (gramAt D T' τ) (sT' τ)) ∧
      (∀ τ, IsONBasis (gramAt D S' τ) (sS' τ) (BS' τ) (pS τ)) ∧ (∀ τ, IsONBasis (gramAt D T' τ) (sT' τ) (BT' τ) (pT τ)) ∧
      (∀ f₀, IsVacO ψ θ S T sS sT (LS : Set _) (LT : Set _) f₀ → IsVacO ψ θ S' T' sS' sT' (LS' : Set _) (LT' : Set _) (𝔉 f₀)) ∧
      ∀ P, ∃ P', ∀ f, IsThetaFunO ψ S T f →
        𝔉 (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S' T' sS' sT' BS' BT' (𝔉 f) P'

open Classical in

def stepDat (c : GlobalTheory.ChainOnto.Com D) (s s' : GlobalTheory.ChainOnto.PiLocalization₂ D) (j : ℕ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (e : AE D) (x : WO s.V s'.V) : ℂ :=
  if IsHalf e x ∧ IsIntM (frMapO s.V s'.V s.β s'.β x) then
    omegaG s.L (c.chi (j + 1)) (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x)) *
      omegaQ ∅ s.L.r ξ 1 (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x))
  else 0

open Classical in
theorem isStepVecOf_iff (c : GlobalTheory.ChainOnto.Com D) (s s' : GlobalTheory.ChainOnto.PiLocalization₂ D) (j : ℕ) (ξ f₀ f) :
    IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (j + 1)) ∅ ξ f₀ f ↔
      IsVacO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ f₀ ∧ ∃ e : AE D, IsIdemSum e (s.L.Pg ∪ ∅) ∧
        IsThetaAt c.ψ (symplO s.V s'.V) (heisO c.ψ s.V s'.V) e (latO s.V s'.V s.Λ s'.Λ fun _ => True) 1 f₀
          (stepDat c s s' j ξ e) f := Iff.rfl

variable {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}
  {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP)

def FrAt (s : GlobalTheory.ChainOnto.PiLocalization₂ D) (j : ℕ) {Y : Type} [Fintype Y] [DecidableEq Y] (γ : Frame G.q s.V Y)
    (L : LatFrame G.k (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j) Y) : Prop :=
  ∃ e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j ≃ Fin s.V.rank, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧
    MovedTo (ofSplit G.q) s.V 1 s.β ((γ.b * L.bas.val).submatrix id fun i => L.ord (e.symm i))

def locLev (j : ℕ) {Y : Type} [Fintype Y] [DecidableEq Y] (L : LatFrame G.k (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j) Y) :
    Subgroup (GL Y G.k) :=
  ((G.S.P.iter (Fin D.R.t) G.S.μ G.S.tame j).toLevel.map L.conj).J

def locPhi (j : ℕ) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (L : LatFrame G.k (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j) Y)
    (L' : LatFrame G.k (Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (j + 1)) Y') : Matrix Y' Y G.k → ℂ :=
  L'.transport L (G.S.P.iterPhi (Fin D.R.t) G.S.μ G.S.tame j)

def LevLoc (s : GlobalTheory.ChainOnto.PiLocalization₂ D) (j : ℕ) (A : GA D s.V → Prop) : Prop :=
  ∃ (Y : Type) (_ : Fintype Y) (_ : DecidableEq Y) (γ : Frame G.q s.V Y) (L : LatFrame G.k _ Y),
    FrAt G s j γ L ∧ ∀ g, A g ↔ InAt γ (locLev G j L) g

def StepLoc (s s' : GlobalTheory.ChainOnto.PiLocalization₂ D) (j : ℕ) (R : (WO s.V s'.V → ℂ) → (WO s.V s'.V → ℂ) → Prop) : Prop :=
  ∃ (Y Y' : Type) (_ : Fintype Y) (_ : DecidableEq Y) (_ : Fintype Y') (_ : DecidableEq Y') (γ : Frame G.q s.V Y)
    (γ' : Frame G.q s'.V Y') (L : LatFrame G.k _ Y) (L' : LatFrame G.k _ Y'), FrAt G s j γ L ∧ FrAt G s' (j + 1) γ' L' ∧
      ∀ f₀ f, R f₀ f ↔ Over d.c.ψ γ γ' s.Λ s'.Λ f₀ (locPhi G j L L') f

example (j c : ℕ) (h : j + c = G.s + 1) : ((G.S.T (Fin D.R.t)).lev j c h).J =
    locLev G j (GlobalTheory.StepData.typeFrame G.S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) j c h)) := rfl

example (j c : ℕ) (h : j + c = G.s) : (G.S.T (Fin D.R.t)).Phi j c h =
    locPhi G j (GlobalTheory.StepData.typeFrame G.S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) j (c + 1) (by omega)))
      (GlobalTheory.StepData.typeFrame G.S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) (j + 1) c (by omega))) := rfl

example (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (LS : Lat S) (LT : Lat T) : FockMap ψ LS LT LS LT id :=
  fun _ sS BS sT BT _ _ _ a b c e => ⟨sS, BS, sT, BT, a, b, c, e, fun _ h => h, fun P => ⟨P, fun _ _ => rfl⟩⟩

end GlobalTheory.RouteCompare

end
