import Formalism.SharpRestriction.GrowthBounds.CountingStatementReduction
import Formalism.MahlerMeasure.LevelLattice

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def gmL {N : ℕ} (LL : ChainLetters N) : Formalism.GM.M.Letters N := ⟨LL.vec, LL.deg⟩

def gmT (T : TieData) : Formalism.GM.M.TieData := ⟨T.t, T.pos, T.z, T.q, T.J, T.thr⟩

def gmB {N : ℕ} (D : BlockData N) : Formalism.GM.M.BlockData N := ⟨gmL D.LL, gmT D.T, D.uPos, D.B, D.zPlus⟩

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

def Ljj (j : Fin G.T.t → ℕ) (jp : ℕ) : Submodule ℤ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] {x | ∃ y ∈ Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr,
    ∃ g ∈ Formalism.GM.M.XiPolZ p N r G.T.t (G.B - jp), x = rename (Formalism.GM.M.chainEmb N r G.T.t) y * g}

def degFact (j : Fin G.T.t → ℕ) (jp : ℕ) : ℕ :=
  (∏ a, ((G.lettersAt j jp).deg a).factorial) * (G.B - jp).factorial

def bejj (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) : ℚ_[p] :=
  Formalism.GM.M.fockK (G.phiAll p (r := r) j jp u) v / (degFact G j jp : ℚ_[p])

def badLvl (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) : ℕ := Formalism.GM.M.bad p (bejj p (r := r) G j jp) (Ljj p (r := r) G j jp) D

def badY (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) : ℕ :=
  Formalism.GM.M.bad p (fun F F' => Formalism.GM.M.fockN p (G.lettersAt j jp) (G.T.phis p (r := r) (G.lettersAt j jp) F) F')
    (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) D

def dimY (j : Fin G.T.t → ℕ) (jp : ℕ) : ℕ :=
  Module.finrank ℚ_[p] (Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr)

end Level

def dXi (r n : ℕ) : ℕ := Nat.choose (n + r - 1) (r - 1)

open Classical in

def levels {N : ℕ} (G : Formalism.GM.M.BlockData N) : Finset ((Fin G.T.t → ℕ) × ℕ) :=
  ((Fintype.piFinset fun _ : Fin G.T.t => Finset.range ((∑ a, G.LL.deg a) + 1)) ×ˢ Finset.range (G.B + 1)).filter
    fun x => G.LevelOK x.1 x.2

section Inst

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def gB (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) : Formalism.GM.M.BlockData (2 * X.s + 1) :=
  gmB (blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b)

abbrev Lv : Type := (Fin (X.S C0 CE1 CE2).t → ℕ) × ℕ

def lv (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) : Finset (Lv C0 CE1 CE2 X) := levels (gB C0 CE1 CE2 X aTop 0 b)

def bLvl (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (D : ℤ) : ℕ :=
  badLvl X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) x.1 x.2 D

def bY (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (D : ℤ) : ℕ :=
  badY X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 b) x.1 x.2 D

def rL (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) : ℕ :=
  dimY X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 b) x.1 x.2 * dXi X.r ((X.S C0 CE1 CE2).bPlus - x.2)

def blockBadness (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) (D : ℤ) : ℕ :=
  ∑ x ∈ lv C0 CE1 CE2 X aTop b, bLvl C0 CE1 CE2 X aTop aPlus b x D

def kapS : ℝ := 3 * ((X.s : ℝ) + 2) * (X.r : ℝ) ^ 2 * lgA X.p X.L.a X.r

def D1r (CM : ℝ) : ℝ :=
  ((X.S C0 CE1 CE2).t : ℝ) * (X.L.Y * kapS X + CM * kapS X) + CM * kapS X

def levelPassageLoss : ℝ := 10 * ((X.s : ℝ) + 1) * ((X.r : ℝ) + 1) * lgA X.p X.L.a X.r + kappaZeroExponent X.p X.L.a X.Nt X.r

open Classical in

def cbox (dl : DCl X) : Finset (Fin X.s → ℕ) :=
  (Fintype.piFinset (fun _ : Fin X.s => X.winA)).filter (fun aTop => Compat C0 CE1 CE2 X dl aTop)

open Classical in

def topA (dl : DCl X) (l : Fin X.s) : ℕ :=
  (X.winA.filter fun x => ∑ c, dl.2 l c ≤ x ∧ (X.S C0 CE1 CE2).P X.p l ∣ x - ∑ c, dl.2 l c).sup id

def upd (dl : DCl X) (aTop : Fin X.s → ℕ) (i : Fin (X.S C0 CE1 CE2).t) : Fin X.s → ℕ :=
  Function.update aTop (uTop (X.S C0 CE1 CE2) i) (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i))

open Classical in

def idx (dl : DCl X) (aTop : Fin X.s → ℕ) : Finset (Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X) :=
  ((keptSet X.p X.r (X.S C0 CE1 CE2) aTop).filter (fun b => (b.rz, b.ry) = dl)).sigma
    (fun b => lv C0 CE1 CE2 X aTop b)

def BlockBoundUniformiser : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b → ∀ D : ℤ, 0 ≤ D →
      ∃ L₂ : Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)),
        GoodSub X.p (blockForm X.O X.p X.r (X.S C0 CE1 CE2) b)
          (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) L₂ ((D : ℝ) + levelPassageLoss X) ∧
        Module.finrank X.O (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) ≤
          Module.finrank X.O L₂ + blockBadness C0 CE1 CE2 X aTop aPlus b D

def BlockBoundIntegers : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b → ∀ D : ℤ, 0 ≤ D →
      ∃ (n : ℕ) (x y : Fin n → MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])
        (e : ℤ),
        (∀ i, x i ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r)) ∧
        (∀ i, y i ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r)) ∧
        (∀ i j, Formalism.GM.M.fockK (x i) (y j) = if i = j then (X.p : ℚ_[X.p]) ^ e else 0) ∧
        (∀ z ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r), ∀ μ ∈ z.support,
          (e : ℝ) ≤ (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) + D + levelPassageLoss X) ∧
        ∑ l ∈ lv C0 CE1 CE2 X aTop b,
            Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) ≤
          n + blockBadness C0 CE1 CE2 X aTop aPlus b D

def RestBCdim : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      Module.finrank X.O (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) ≤
        ∑ l ∈ lv C0 CE1 CE2 X aTop b,
          Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2)

def RestPlus (CM : ℝ) : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    (∑ aPlus ∈ X.winA, (bLvl C0 CE1 CE2 X aTop aPlus x.1 x.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ)) ≤
      (X.winA.card : ℝ) * ((bY C0 CE1 CE2 X aTop x.1 x.2 ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ) *
          dXi X.r ((X.S C0 CE1 CE2).bPlus - x.2.2) + 5 / X.L.Y * rL C0 CE1 CE2 X aTop x.1 x.2)

def RestTM (CM : ℝ) : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a0 ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a0,
    (∑ aTop ∈ cbox C0 CE1 CE2 X dl, (bY C0 CE1 CE2 X aTop x.1 x.2 ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ)) ≤
      (30 + CM) / X.L.Y * ∑ i : Fin (X.S C0 CE1 CE2).t, ∑ aTop ∈ cbox C0 CE1 CE2 X dl,
        (dimY X.p (r := X.r) (gB C0 CE1 CE2 X (upd C0 CE1 CE2 X dl aTop i) 0 x.1) x.2.1 x.2.2 : ℝ)

def RestDir : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∑ x ∈ lv C0 CE1 CE2 X aTop b, rL C0 CE1 CE2 X aTop b x ≤ bRank C0 CE1 CE2 X aTop aPlus b

def RestFree : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ aTop' ∈ cbox C0 CE1 CE2 X dl,
    idx C0 CE1 CE2 X dl aTop = idx C0 CE1 CE2 X dl aTop'

def RestRatio : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ i : Fin (X.S C0 CE1 CE2).t,
    upd C0 CE1 CE2 X dl aTop i ∈ cbox C0 CE1 CE2 X dl ∧
    (mCl C0 CE1 CE2 X dl (upd C0 CE1 CE2 X dl aTop i) : ℝ) ≤ Real.exp 3 * mCl C0 CE1 CE2 X dl aTop

def RestDepth (CM C : ℝ) : Prop :=
  0 ≤ D1r C0 CE1 CE2 X CM ∧
  X.L.Y * D1r C0 CE1 CE2 X CM + levelPassageLoss X ≤ depthD C X.p X.L.a X.Nt X.N₁ X.r X.L.Y

end Inst

end Formalism.MainNotions.G.SymmetricFormBlocks

end
