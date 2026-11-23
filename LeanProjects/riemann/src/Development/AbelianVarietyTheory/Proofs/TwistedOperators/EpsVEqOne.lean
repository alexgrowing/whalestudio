import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingPiProdSplit

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlatPlace

open GlobalTheory.LocMod (Place Frame IsOne)
open GlobalTheory.SplitWeil (SB)
open GlobalTheory.SplitFlip (Grid Edge oppositePath)

section Local

variable {k : Type} [Field k]

def datC {a b c c' N N' : ℕ} (h : a + c = N') (h' : b + c' = N) (φ : Matrix (Fin N) (Fin N') k → ℂ)
    (z : Matrix (Fin a ⊕ Fin c) (Fin b ⊕ Fin c') k) : ℂ := φ (z.reindex (frame h) (frame h'))ᵀ

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def phiM (Γ : Grid k) (g' g : Γ.VertexGroup) (φ : ∀ b : Edge, Matrix (Fin (Γ.rank b.tgt)) (Fin (Γ.rank b.src)) k → ℂ) :
    ∀ b : Edge, Matrix (Fin (Γ.rank b.tgt)) (Fin (Γ.rank b.src)) k → ℂ := fun b x =>
  Γ.edgeFactor .one g' b * φ b ((g b.tgt).valᵀ * x * ((g b.src)⁻¹).valᵀ)

def zetaLoc (Γ : Grid k) (keep : Bool) (ε g : Γ.VertexGroup) : ℂ :=
  ((oppositePath Γ.m).map (Γ.edgeFactor .one ε)).prod * if keep then 1 else ((charFactor Γ g : ℂˣ) : ℂ)

variable [MeasurableSpace k] [BorelSpace k]

def locA (Γ : Grid k) (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k)
    (φ : ∀ b : Edge, Matrix (Fin (Γ.rank b.tgt)) (Fin (Γ.rank b.src)) k → ℂ) (j : ℕ)
    (q : Matrix (Fin (topRank Γ (j + 1))) (Fin (topRank Γ j)) k × Matrix (Fin (topRank Γ (j + 1 + 1))) (Fin (topRank Γ (j + 1))) k) : ℂ :=
  if h0 : j + 2 * 0 + 2 = Γ.m then
    φ (.theta Γ.m (j + 1)) (q.2.submatrix
        (Fin.castLE (show Γ.rank (Γ.m, j + 1 + 1) ≤ _ by have := topRank_add hs (j + 1 + 1); omega))
        (Fin.cast (show Γ.rank (Γ.m, j + 1) = _ by have := topRank_add hs (j + 1); omega)))ᵀ *
      GlobalTheory.StepData.hat ψ ν (-1) (fun u => GlobalTheory.LocFlat.flCol ψ ν (0 + 1)
        (datC (c := 0) (c' := 0 + 1) (show _ = Γ.rank (Γ.m, j + 1) by have := topRank_add hs (j + 1); omega)
          (show _ = Γ.rank (Γ.m, j) by have := topRank_add hs j; omega) (φ (.theta Γ.m j)))
        (fromCols q.1 (Matrix.of fun r _ => u r))) (q.2 (topLast Γ (j + 1 + 1)))
  else if hj : j + 2 * ((Γ.m - 4 - j) / 2 + 1) + 2 = Γ.m then
    GlobalTheory.LocFlat.contr ψ ν
      (GlobalTheory.LocFlat.flCol ψ ν ((Γ.m - 4 - j) / 2 + 1 + 1)
        (datC (c := 2 * ((Γ.m - 4 - j) / 2) + 1 + 1) (c' := 2 * ((Γ.m - 4 - j) / 2) + 1 + 1 + 1)
          (show _ = Γ.rank (Γ.m, j + 1) by have := topRank_add hs (j + 1); omega)
          (show _ = Γ.rank (Γ.m, j) by have := topRank_add hs j; omega) (φ (.theta Γ.m j))))
      (GlobalTheory.LocFlat.flRow ψ ν ((Γ.m - 4 - j) / 2 + 1)
        (datC (c := 2 * ((Γ.m - 4 - j) / 2) + 1) (c' := 2 * ((Γ.m - 4 - j) / 2) + 1 + 1)
          (show _ = Γ.rank (Γ.m, j + 1 + 1) by have := topRank_add hs (j + 1 + 1); omega)
          (show _ = Γ.rank (Γ.m, j + 1) by have := topRank_add hs (j + 1); omega) (φ (.theta Γ.m (j + 1))))) q
  else 0

end Local

section Frames

variable {D : D7}

def IsPlc (w : Pl D.host.E) (p : Place D (Kw w)) : Prop :=
  Formalism.L2.NTheta.IsIdemAt p.e w ∧ (∀ a, p.π a = cpt w (toEAf D a)) ∧ ∀ x, p.ι x = atPl w x

def frOf {n N : ℕ} (h : N = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) : Frame (Kw w) n (Fin N) where
  β := (loc w β).val.submatrix id (Fin.cast h)
  γ := ((loc w β)⁻¹).val.submatrix (Fin.cast h) id
  βγ := by subst h; exact (loc w β).mul_inv
  γβ := by subst h; exact (loc w β).inv_mul

def mvFr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) {S : HSp D}
    {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z] (a : GA D S) (F : Frame k S.rank Y) (ε : GL Y k)
    (σ : Z ≃ Y) : Frame k S.rank Z where
  β := ((mt S a).map p.π * F.β * ε.val).submatrix id σ
  γ := ((ε⁻¹).val * F.γ * (mt S a⁻¹).map p.π).submatrix σ id
  βγ := by
    have h : (mt S a).map p.π * (mt S a⁻¹).map p.π = 1 := by
      rw [← Matrix.map_mul]
      have : mt S a * mt S a⁻¹ = 1 := by simp [Formalism.L2.Theta.mt]
      rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [submatrix_mul_equiv, submatrix_id_id, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc ε.val, ← Matrix.mul_assoc ε.val,
      Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc F.β, F.βγ, Matrix.one_mul, h]
  γβ := by
    have h : (mt S a⁻¹).map p.π * (mt S a).map p.π = 1 := by
      rw [← Matrix.map_mul]
      have : mt S a⁻¹ * mt S a = 1 := by simp [Formalism.L2.Theta.mt]
      rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc ((mt S a⁻¹).map p.π),
      ← Matrix.mul_assoc ((mt S a⁻¹).map p.π), h, Matrix.one_mul, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, Units.inv_mul,
      submatrix_one_equiv]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def frTop (S : GridChoice W U) (t : T) (w : Pl D.host.E) (j : ℕ) (hj : j ≤ D.R.m) :
    Frame (Kw w) (G.V (.top j)).rank (Fin (topRank (locGrid G t w) j)) := frOf (topRank_eq G t w hj) (S.βp j) w

def frRow (B : Frames G) (t : T) (w : Pl D.host.E) (j : ℕ) (hj : j ≤ D.R.m) :
    Frame (Kw w) (G.V (.grid D.R.m j)).rank (Fin ((locGrid G t w).rank (D.R.m, j))) :=
  frOf (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (B.β D.R.m j) w

variable (G) in
open Classical in

def epsV (t : T) (w : Pl D.host.E) : (locGrid G t w).VertexGroup :=
  onColumn (G := locGrid G t w) fun j => if j ∈ idx D then sgnAt G t (-1) w j else 1

variable (G) in

def baseM (t : T) (w : Pl D.host.E) (j : ℕ) : GL (Fin ((locGrid G t w).rank (D.R.m, j))) (Kw w) :=
  if j = 0 then (stair (locGrid G t w) (unifAt w) (cosExp G w) j)⁻¹ else 1

open Classical in

theorem epsV_apply (t : T) (w : Pl D.host.E) (j : ℕ) :
    epsV G t w (D.R.m, j) = if j ∈ idx D then sgnAt G t (-1) w j else 1 := by
  unfold epsV
  exact onColumn_apply (G := locGrid G t w) _ j

theorem mem_idx {j : ℕ} : j ∈ idx D ↔ 1 ≤ j ∧ j + 2 ≤ D.R.m := by
  unfold idx
  rw [List.mem_range'_1]
  omega

theorem epsV_mem (t : T) (w : Pl D.host.E) (X : ℕ × ℕ) : epsV G t w X ∈ GlobalTheory.SplitWeil.KO (Kw w) _ := by
  obtain ⟨a, j⟩ := X
  by_cases ha : a = D.R.m
  · subst ha
    rw [epsV_apply]
    split_ifs
    · let u : Fin ((locGrid G t w).rank (D.R.m, j)) → (Valuation.integer (ValuativeRel.valuation (Kw w)))ˣ := fun b =>
        if Odd j ∧ topRank (locGrid G t w) j + (D.R.m - 1 - j) / 2 ≤ b.1 then -1 else 1
      refine ⟨⟨diagonal fun b => (u b : Valuation.integer (ValuativeRel.valuation (Kw w))),
        diagonal fun b => ((u b)⁻¹ : (Valuation.integer (ValuativeRel.valuation (Kw w)))ˣ), ?_, ?_⟩, ?_⟩
      · rw [diagonal_mul_diagonal]; simp
      · rw [diagonal_mul_diagonal]; simp
      · ext r q
        by_cases hrq : r = q
        · subst hrq
          simp [sgnAt, u]
          split_ifs <;> simp
        · simp [sgnAt, diagonal_apply_ne _ hrq]
    · exact one_mem _
  · have h1 : epsV G t w (a, j) = 1 := by
      unfold epsV onColumn
      exact dif_neg ha
    rw [h1]
    exact one_mem _

theorem elt_eq_one (t : T) (w : Pl D.host.E) (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w)) {j : ℕ}
    (hj : D.R.m ≤ j + 1) : (repsAt G t w).elt β (D.R.m, j) = 1 := by
  have h2 := D.R.two_le_m
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  unfold Reps.elt
  refine (onColumn_apply (G := locGrid G t w) _ (i + 1)).trans ?_
  dsimp only
  have hi : ¬ i < (locGrid G t w).m - 2 := by
    show ¬ i < D.R.m - 2
    omega
  exact dif_neg hi

theorem epsV_eq_one (t : T) (w : Pl D.host.E) {j : ℕ} (hj : D.R.m ≤ j + 1) : epsV G t w (D.R.m, j) = 1 := by
  rw [epsV_apply, if_neg]
  rw [mem_idx]
  omega

end Frames

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

abbrev EdgeDat (t : T) (w : Pl D.host.E) : Type :=
  ∀ b : Edge, Matrix (Fin ((locGrid ch.G t w).rank b.tgt)) (Fin ((locGrid ch.G t w).rank b.src)) (Kw w) → ℂ

open Classical in

def IsArrVec (t : T) (w : Pl D.host.E) (e : AE D) (φ : EdgeDat ch t w) (j : ℕ) (hj : j < D.R.m)
    (v f : WO (ch.G.V (.grid D.R.m j)) (ch.G.V (.grid D.R.m (j + 1))) → ℂ) : Prop :=
  IsThetaFunO ch.W.ψ _ _ v ∧ IsLocVec ch.W (.mu t D.R.m j) e v (fun y => if IsHalf e y then φ (.theta D.R.m j)
    (ch.S.B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, hj⟩ ⟨le_rfl, hj.le⟩
      (y.map fun a => cpt w (toEAf D a))) else 0) f

open Classical in

def IsPts (t : T) (w : Pl D.host.E) (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (e : AE D)
    (r r₀ h : Pts ch.G) : Prop :=
  OneLoc t w e r (fun j => if j ∈ idx D then sgnAt ch.G t (-1) w j * (repsAt ch.G t w).elt β (D.R.m, j) else 1) ∧
  OneLoc t w e r₀ (fun j => if j = 0 then (stair (locGrid ch.G t w) (unifAt w) (cosExp ch.G w) j)⁻¹ else 1) ∧
  ∀ j, j ≤ D.R.m → ∃ δ, IsTilt ch.G j δ ∧ δ⁻¹ * h j ∈ GlobalTheory.FinPl.grpOff _ (· = w.under (𝓞 D.host.F))

def LatP : Prop := ∀ t, ∀ w ∈ locPl ch.G t, ∀ p, IsPlc w p → ∀ j (hj : j < D.R.m),
  (∀ x, p.up (frRow ch.S.B t w j hj.le) (frRow ch.S.B t w (j + 1) hj) x ∈
      latO _ _ (ch.G.Λ (.grid D.R.m j) : Set _) (ch.G.Λ (.grid D.R.m (j + 1)) : Set _) (fun _ => True) ↔
    ∀ a b, x a b ∈ Valuation.integer (ValuativeRel.valuation (Kw w))) ∧
  ∀ x, p.up (frTop ch.S.toGridChoice t w j hj.le) (frTop ch.S.toGridChoice t w (j + 1) hj) x ∈
      latO _ _ (ch.G.Λ (.top j) : Set _) (ch.G.Λ (.top (j + 1)) : Set _) (fun _ => True) ↔
    ∀ a b, x a b ∈ Valuation.integer (ValuativeRel.valuation (Kw w))

def ChrP : Prop := ∀ t, ∀ w ∈ locPl ch.G t, ∀ p, IsPlc w p →
  p.IsChar ch.W.ψ (psiAt ch.W w) ∧ GlobalTheory.SplitWeil.HasConductor (psiAt ch.W w) 1 ∧ ∀ j, j < D.R.m →
    p.IsComp (ch.G.chrS (.mu t D.R.m j)) ((locGrid ch.G t w).kappa (.theta D.R.m j) (D.R.m, j + 1)) ∧
    p.IsComp (ch.G.chrT (.mu t D.R.m j)) ((locGrid ch.G t w).kappa (.theta D.R.m j) (D.R.m, j))

def ArrP : Prop := ∀ t, ∀ w ∈ locPl ch.G t, ∀ p, IsPlc w p → ∀ (φ : EdgeDat ch t w) j (hj : j < D.R.m) v f,
  IsArrVec ch t w p.e φ j hj v f → ∀ ε g : (locGrid ch.G t w).VertexGroup, (∀ X, ε X ∈ GlobalTheory.SplitWeil.KO (Kw w) _) →
  ∀ a ρ a' ρ', p.IsLoc (frRow ch.S.B t w j hj.le) ρ ((ε * g) (D.R.m, j)) →
    p.IsLoc (frRow ch.S.B t w (j + 1) hj) ρ' ((ε * g) (D.R.m, j + 1)) →
  ∀ (Z Z' : Type) [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (σ : Z ≃ Fin ((locGrid ch.G t w).rank (D.R.m, j)))
    (σ' : Z' ≃ Fin ((locGrid ch.G t w).rank (D.R.m, j + 1))),
    ∃ Tm, p.IsModel ch.W.ψ (mvFr p a (frRow ch.S.B t w j hj.le) (ε (D.R.m, j)) σ)
        (mvFr p a' (frRow ch.S.B t w (j + 1) hj) (ε (D.R.m, j + 1)) σ') Tm ∧
      (∀ O, IsOne O → Tm O = ch.W.om (.mu t D.R.m j) (a, a') v) ∧
      ∃ Φ : SB (Matrix Z' Z (Kw w)), (∀ z, Φ.1 z = phiM (locGrid ch.G t w) (ε * g) g φ (.theta D.R.m j) (z.reindex σ' σ)ᵀ) ∧
        Tm Φ = ch.W.om (.mu t D.R.m j) (a * ρ, a' * ρ') f

open Classical in

def LocP : Prop := ∀ t, ∀ w ∈ locPl ch.G t, ∀ p, IsPlc w p → ∀ β r r₀ h, IsPts ch t w β p.e r r₀ h → ∀ j (hj : j ≤ D.R.m),
  p.IsLoc (frRow ch.S.B t w j hj) ((r₀ j)⁻¹ * r j) ((epsV ch.G t w * (repsAt ch.G t w).elt β) (D.R.m, j)) ∧
  (Even j → (mt _ (h j * r₀ j)).map p.π * (frRow ch.S.B t w j hj).β = (frRow ch.S.B t w j hj).β *
    (baseM ch.G t w j).val) ∧
  (Odd j → ∃ δ, IsTilt ch.G j δ ∧ (mt _ (h j * r₀ j)).map p.π = (mt _ δ).map p.π)

open Classical in

def BesP : Prop := ∀ t, ∀ w ∈ locPl ch.G t, ∀ p, IsPlc w p → ∀ (M : Vol ch.G) (hM : M.Is t) j σ (hj : j + 2 * σ + 2 = D.R.m) vN
  (a : GA D (ch.G.V (.grid D.R.m j))), (mt (ch.G.V (.grid D.R.m j)) a).map p.π * (frRow ch.S.B t w j (by omega)).β = (frRow ch.S.B t w j (by omega)).β *
    (baseM ch.G t w j).val →
  ∀ c (hc : topRank (locGrid ch.G t w) j + c = (locGrid ch.G t w).rank (D.R.m, j)),
    p.IsBesFrame (besAt ch.G hM j σ hj vN) (p.xi ^ σ)⁻¹ (frTop ch.S.toGridChoice t w j (by omega))
      (mvFr p a (frRow ch.S.B t w j (by omega)) (epsV ch.G t w (D.R.m, j)) (frame hc))

def JacP : Prop := ∀ t, ∀ w ∈ locPl ch.G t, ∀ p, IsPlc w p → ∀ (M : Vol ch.G) (hM : M.Is t) j σ (hj : j + 2 * σ + 2 = D.R.m) vN
  (a : GA D (ch.G.V (.grid D.R.m (j + 1)))), (σ = 0 ∧ a = 1) ∨ (∃ δ, IsTilt ch.G (j + 1) δ ∧ (mt _ a).map p.π = (mt _ δ).map p.π) →
  ∀ c (hc : topRank (locGrid ch.G t w) (j + 1) + c = (locGrid ch.G t w).rank (D.R.m, j + 1)),
    p.IsJacFrame (jacAt ch.G hM (j + 1) σ (by omega)) (p.xi ^ σ)⁻¹ (p.hz (besAt ch.G hM j σ hj vN))
      (frTop ch.S.toGridChoice t w (j + 1) (by omega))
      (mvFr p a (frRow ch.S.B t w (j + 1) (by omega)) (epsV ch.G t w (D.R.m, j + 1)) (frame hc))

variable {ch} in

def Expands {t : T} {w : Pl D.host.E} (p : Place D (Kw w)) (j : ℕ) (hj : j + 1 < D.R.m)
    (a : Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j)) (Kw w) ×
      Matrix (Fin (topRank (locGrid ch.G t w) (j + 1 + 1))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w) → ℂ)
    (X C : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) → WO (ch.G.V (.top (j + 1))) (ch.G.V (.top (j + 1 + 1))) → ℂ) : Prop :=
  ∀ (I : Type) (S : Finset I) (x : I → ℂ) (Ξ₁ : I → SB (Matrix _ _ (Kw w))) (Ξ₂ : I → SB (Matrix _ _ (Kw w)))
    (c₁ : I → WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ) (c₂ : I → WO (ch.G.V (.top (j + 1))) (ch.G.V (.top (j + 1 + 1))) →₀ ℂ),
    (∀ i ∈ S, p.IsCombAt ch.W.ψ (frTop ch.S.toGridChoice t w j (by omega)) (frTop ch.S.toGridChoice t w (j + 1) hj.le) (c₁ i) (Ξ₁ i).1 ∧
      p.IsCombAt ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) hj.le) (frTop ch.S.toGridChoice t w (j + 1 + 1) hj) (c₂ i) (Ξ₂ i).1) →
    ((∀ q₁ q₂, ∑ i ∈ S, x i * ((Ξ₁ i).1 q₁ * (Ξ₂ i).1 q₂) = 0) → ∑ i ∈ S, x i • biComb ch.W.ψ _ _ _ (c₁ i) (c₂ i) C = 0) ∧
    ((∀ q, a q = ∑ i ∈ S, x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2)) → X = ∑ i ∈ S, x i • biComb ch.W.ψ _ _ _ (c₁ i) (c₂ i) C)

abbrev facAt (t : T) (w : Pl D.host.E) (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (φ : EdgeDat ch t w)
    (j : ℕ) :=
  locA (locGrid ch.G t w) one_le_sLen (psiAt ch.W w) (unitVol w)
    (phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ) j

def DblP : Prop := ∀ t, ∀ w ∈ locPl ch.G t, ∀ p, IsPlc w p → ∀ β r r₀ h, IsPts ch t w β p.e r r₀ h →
  ∀ (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t), (∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j)) →
  ∀ j, Even j → ∀ hj : j + 2 < D.R.m,
    Expands p j (by omega) (facAt ch t w β φ j) (conAt ch.W hM f (h * r) j) (conAt ch.W hM v (h * r₀) j)

def LastP : Prop := ∀ t, ∀ w ∈ locPl ch.G t, ∀ p, IsPlc w p → ∀ β r r₀ h, IsPts ch t w β p.e r r₀ h →
  ∀ (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t), (∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j)) →
  ∀ j (hj : j + 2 = D.R.m),
    Expands p j (by omega) (facAt ch t w β φ j) (conAt ch.W hM f (h * r) j) (conAt ch.W hM v (h * r₀) j)

def CombP : Prop := ∀ t, ∀ w ∈ locPl ch.G t, ∀ p, IsPlc w p → ∀ j (hj : j < D.R.m) (d : FinDatum ch.G t (.top t j)) c, d.e = p.e →
  IsCombOf ch.W d c → ∃ Ξ : SB (Matrix _ _ (Kw w)),
    (∀ x, Ξ.1 x = d.fn (p.up (frTop ch.S.toGridChoice t w j hj.le) (frTop ch.S.toGridChoice t w (j + 1) hj) x)) ∧
    p.IsCombAt ch.W.ψ (frTop ch.S.toGridChoice t w j hj.le) (frTop ch.S.toGridChoice t w (j + 1) hj) c Ξ.1

def ScalP : Prop :=
  ∃ (κ : Pl D.host.E → ℂ) (z : T → Pl D.host.E → ℂˣ), (∀ t w, z t w ∈ xiVals R.toLevCh t) ∧ (∀ w, w ∉ ch.G.pl.W0 → κ w = 1) ∧
    ∀ t, ∀ w ∈ locPl ch.G t, ∀ β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w),
      (w ∈ ch.G.pl.W0 → ∀ i, β i = DoubleCoset.mk _ _ (stair (locGrid ch.G t w) (unifAt w) (cosExp ch.G w) (i + 1))) →
        zetaLoc (locGrid ch.G t w) (keepAt ch.G w) (epsV ch.G t w) ((repsAt ch.G t w).elt β) = κ w * (z t w : ℂ)⁻¹

end GlobalTheory.FlatPlace

end
