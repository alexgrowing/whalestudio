import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit
import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EdgeFactorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridIsAdmissibleFlipTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexWeilOrbitValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData
open GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FirstRowEndLaw

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {Γ : Grid k}

theorem flipTensor_smul (s : Assignment) (ψ : AddChar k Circle) (ϖ : kˣ) (e i j : ℕ) (J : Γ.Level) (c : ℂ)
    (T : Γ.Args → ℂ) : Γ.flipTensor s ψ ϖ e i j J (c • T) = c • Γ.flipTensor s ψ ϖ e i j J T := by
  funext x
  exact GlobalTheory.FlipAdm.squareFlip_const_mul _ _ _ _ _ _ _ c _ _

theorem flips_law {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (he : 1 ≤ e)
    (g : Γ.VertexGroup) (hK : ∀ Y, g Y ∈ KO k _) (c : ℂ) :
    ∀ (l : List (ℕ × ℕ)) (St : Γ.PiLocalization₂), (∀ x ∈ l, CondLE ϖ e (Γ.nu x.1 x.2)) → (∀ x ∈ l, g x = 1) →
      CanFlip St.path l → (∀ X, IsOpen (St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ St.level X ≤ KO k _) →
      St.IsAdmissible .one ϖ e → Γ.pathAct .one St.path g St.tensor = c • St.tensor →
      Γ.pathAct .one (St.flips .one ψ ϖ e l).path g (St.flips .one ψ ϖ e l).tensor =
        c • (St.flips .one ψ ϖ e l).tensor := by
  intro l
  induction l with
  | nil => intro St _ _ _ _ _ h; exact h
  | cons x l ih =>
    intro St hν hg hc hJ hT hlaw
    obtain _ | ⟨hp, hc'⟩ := hc
    have hJ' : ∀ X, IsOpen ((St.flip .one ψ ϖ e x).level X : Set (GL (Fin (Γ.rank X)) k)) ∧
        (St.flip .one ψ ϖ e x).level X ≤ KO k _ := fun X => by
      change IsOpen (Γ.flipLevel x.1 x.2 St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ Γ.flipLevel x.1 x.2 St.level X ≤ _
      by_cases hX : X = (x.1 + 1, x.2 + 1)
      · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
      · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X
    refine ih (St.flip .one ψ ϖ e x) (fun y hy => hν y (List.mem_cons_of_mem _ hy))
      (fun y hy => hg y (List.mem_cons_of_mem _ hy)) hc' hJ'
      (GlobalTheory.FlipAdm.isAdmissible_flip ψ ϖ e hϖ hψ he St x (hν x List.mem_cons_self) hp hJ hT) ?_
    have hν0 := hν x List.mem_cons_self
    have hg0 := hg x List.mem_cons_self
    obtain ⟨i, j⟩ := x
    obtain ⟨γ, J, T⟩ := St
    obtain ⟨l₁, l₂, hγ, hfl⟩ := GlobalTheory.FlipAdm.exists_split hT.path hp
    have hTt := hT.tensor
    simp only at hγ hfl hlaw hTt hν0 hg0 hJ
    change Γ.pathAct .one (flipPath i j γ) g (Γ.flipTensor .one ψ ϖ e i j J T) = c • Γ.flipTensor .one ψ ϖ e i j J T
    rw [hfl]
    subst hγ
    rw [GlobalTheory.FlipAdm.pathAct_flipTensor hϖ hψ he hν0 (hJ (i, j)).1 (hJ (i, j)).2 l₁ l₂ hTt g hg0 hK, hlaw,
      flipTensor_smul]

end Local

end GlobalTheory.FirstRowEndLaw

namespace GlobalTheory.FirstRowEndLaw

open GlobalTheory.FunObj.GivenAdm

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}
variable {μ₀ : T} {G : GridData L sc} {t : T} {w : Pl D.host.E}

theorem stepType_laws (hL : L.Is μ₀) (hw : w ∈ locPl G t) (j : ℕ) :
    (∀ i, (stepType L t w i).J = stepGroup L t w i) ∧
      ∃ ν : (Kw w)ˣ →* ℂˣ, (∀ x : (Kw w)ˣ, valuation (Kw w) (x : Kw w) = 1 → (locGrid G t w).mu (j + 1) x = (ν x)⁻¹) ∧
        HasTypes ν (stepType L t w j).toLevel (stepType L t w (j + 1)).toLevel (stepFn L t w j) := by
  have hmu : ∀ j x, (locGrid G t w).mu j x = (muBase L j).loc w x * (L.xiH t).loc w x := fun _ _ => rfl
  by_cases hP : w ∈ L.Pg
  · have hQ : w ∉ L.Q t := fun h => (over_of_mem_Pg hL hP).elim fun i hi => not_over_of_mem_Q hL h i hi
    have h0 : w ∈ G.pl.W0 := (mem_locPl.1 hw).resolve_right hQ
    refine ⟨fun i => by simp only [stepType, stepGroup, if_pos hP], ?_⟩
    simp only [stepType, stepFn, if_pos hP]
    exact ⟨_, fun x hx => by simp [hmu, xi_unr hL h0 hQ x hx], TypeDatum.hasTypes_iterPhi _ _ _ j⟩
  by_cases hQ : w ∈ L.Q t
  · have hδ : IsTame ((L.xiH t).loc w)⁻¹ := fun x hx => by
      rw [MonoidHom.inv_apply, isTame_loc (hL.xi_tame t w) x hx, inv_one]
    refine ⟨fun i => by simp only [stepType, stepGroup, if_neg hP, if_pos hQ, dif_pos (And.intro hQ hδ)]; rfl, ?_⟩
    simp only [stepType, stepFn, if_neg hP, if_pos hQ, dif_pos (And.intro hQ hδ)]
    exact ⟨_, fun x hx => by simp [hmu, muBase_unr hL hw hP _ x hx],
      hasTypes_parPhi hδ (ν := 1) fun _ _ => rfl⟩
  · have hn : ¬ (w ∈ L.Q t ∧ IsTame ((L.xiH t).loc w)⁻¹) := fun h => hQ h.1
    refine ⟨fun i => by simp only [stepType, stepGroup, if_neg hP, if_neg hQ, dif_neg hn]; rfl, ?_⟩
    simp only [stepType, stepFn, if_neg hP, if_neg hQ, dif_neg hn]
    exact ⟨1, fun x hx => by
      simp [hmu, muBase_unr hL hw hP _ x hx, xi_unr hL ((mem_locPl.1 hw).resolve_right hQ) hQ x hx], hasTypes_vacuum⟩

end GlobalTheory.FirstRowEndLaw

namespace GlobalTheory.FirstRowEndLaw

open GlobalTheory.FunObj.GivenAdm

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} {G : GridData L sc} {t : T} {w : Pl D.host.E}

theorem givenPath_succ (n : ℕ) : SplitFlip.givenPath (n + 1) =
    Edge.theta 0 n :: ((List.range n).reverse.map (Edge.theta 0) ++ (List.range (n + 1)).map (Edge.ex · 0)) := by
  simp [SplitFlip.givenPath, List.range_succ]

theorem not_touch_rest (n : ℕ) : ∀ b ∈ (List.range n).reverse.map (Edge.theta 0) ++ (List.range (n + 1)).map (Edge.ex · 0),
    b.src ≠ (0, n + 1) ∧ b.tgt ≠ (0, n + 1) := by
  intro b hb
  simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_range] at hb
  rcases hb with ⟨j, hj, rfl⟩ | ⟨i, -, rfl⟩
  · simp [Edge.src, Edge.tgt]; omega
  · simp [Edge.src, Edge.tgt]

theorem given_law_at (hL : L.Is μ₀) (B : Frames G) (Φ : G.Datum) (hw : w ∈ locPl G t) :
    ∀ (m : ℕ), m ≠ 0 → ∀ (κ : GL (Fin ((locGrid G t w).rank (0, m))) (Kw w)), κ ∈ givenLevel G t w (0, m) →
    (locGrid G t w).pathAct .one (SplitFlip.givenPath m) (Pi.mulSingle (0, m) κ)
        ((locGrid G t w).lines₂ (SplitFlip.givenPath m) (givenDatum t w B Φ)) =
      endLamAt G t w m κ • (locGrid G t w).lines₂ (SplitFlip.givenPath m) (givenDatum t w B Φ)
  | 0, h => absurd rfl h
  | n + 1, _ => fun κ hκ => by
    obtain ⟨hJ, ν, hν, H⟩ := stepType_laws (G := G) hL hw n
    have hKO : ∀ Y, (Pi.mulSingle (0, n + 1) κ : (locGrid G t w).VertexGroup) Y ∈ KO (Kw w) _ := fun Y => by
      by_cases hY : Y = (0, n + 1)
      · subst hY; simpa using (givenLevel_open hL hw (0, n + 1)).2 hκ
      · rw [Pi.mulSingle_eq_of_ne hY]; exact one_mem _
    have hκ' : (reGL (ixFin G t w (n + 1))).symm κ ∈ (stepType L t w (n + 1)).J := by
      rw [hJ]
      obtain ⟨y, hy, rfl⟩ := hκ
      simpa using hy
    have h1 : (1 : GL (Ix (Fin D.R.r) (Fin D.R.t) n) (Kw w)) ∈ (stepType L t w n).J := one_mem _
    have key : ∀ x : (locGrid G t w).Args,
        (locGrid G t w).edgeFactor .one (Pi.mulSingle (0, n + 1) κ) (.theta 0 n) *
            givenDatum t w B Φ (.theta 0 n) ((locGrid G t w).moveArgs .one (Pi.mulSingle (0, n + 1) κ) x (.theta 0 n)) =
          endLamAt G t w (n + 1) κ * givenDatum t w B Φ (.theta 0 n) (x (.theta 0 n)) := by
      intro x
      have e := law_of_hasTypes H ⟨1, h1⟩ ⟨_, hκ'⟩
        ((x (.theta 0 n))ᵀ.submatrix (ixFin G t w (n + 1)) (ixFin G t w n))
      have hd : gdet ((reGL (ixFin G t w (n + 1))).symm κ) = gdet κ :=
        (det_reGL (ixFin G t w (n + 1)) _).symm.trans (by rw [MulEquiv.apply_symm_apply])
      rw [edgeFactor_eq hKO, endLamAt, dif_pos hκ']
      simp only [Edge.src, Edge.tgt, Grid.blockChar, Pi.mulSingle_eq_same,
        Pi.mulSingle_eq_of_ne (show ((0 : ℕ), n) ≠ (0, n + 1) by simp)]
      have hv : valuation (Kw w) (gdet κ : Kw w) = 1 := valuation_gdet_of_mem_KO (by simpa using hKO (0, n + 1))
      have hl1 : (stepType L t w n).lam ⟨1, h1⟩ = 1 := map_one _
      set κ' := (reGL (ixFin G t w (n + 1))).symm κ with hκ'def
      set X := (x (.theta 0 n))ᵀ.submatrix (ixFin G t w (n + 1)) (ixFin G t w n) with hX
      have e' : ((ν (gdet (1 : GL (Ix (Fin D.R.r) (Fin D.R.t) n) (Kw w)))) : ℂ) * (((ν (gdet κ'))⁻¹ : ℂˣ) : ℂ) *
          stepFn L t w n ((κ'⁻¹).val * X * (1 : GL (Ix (Fin D.R.r) (Fin D.R.t) n) (Kw w)).val) =
          (((stepType L t w n).lam ⟨1, h1⟩ / (stepType L t w (n + 1)).lam ⟨κ', hκ'⟩ : ℂˣ) : ℂ) * stepFn L t w n X := e
      have hmv : givenDatum t w B Φ (.theta 0 n)
          ((locGrid G t w).moveArgs .one (Pi.mulSingle (0, n + 1) κ) x (.theta 0 n)) =
          stepFn L t w n ((κ'⁻¹).val * X) := by
        simp only [givenDatum]
        congr 1
        rw [hκ'def, ← map_inv, reGL_symm_val, hX, submatrix_mul_equiv]
        simp only [Grid.moveArgs, Assignment.read, Edge.src, Edge.tgt, Pi.mulSingle_eq_same,
          Pi.mulSingle_eq_of_ne (show ((0 : ℕ), n) ≠ (0, n + 1) by simp), invT_val, invT_inv_val, transpose_mul,
          transpose_transpose, Matrix.mul_assoc, map_one, inv_one, Units.val_one, Matrix.mul_one, Matrix.one_mul]
      have hg1 : ∀ {a : Type} [Fintype a] [DecidableEq a], gdet (1 : GL a (Kw w)) = 1 := fun {_ _ _} => map_one _
      rw [hmv]
      simp only [hl1, hd, hg1, map_one, inv_one, Units.val_one, mul_one, one_mul, one_div, Matrix.mul_one] at e'
      rw [hν _ hv, hg1, map_one, inv_one, Units.val_one, mul_one, e']
      rfl
    funext x
    rw [givenPath_succ]
    simp only [Grid.pathAct, Grid.lines₂, Pi.smul_apply, smul_eq_mul, List.map_cons, List.prod_cons]
    have hr1 : (((List.range n).reverse.map (Edge.theta 0) ++ (List.range (n + 1)).map (Edge.ex · 0)).map
        ((locGrid G t w).edgeFactor .one (Pi.mulSingle (0, n + 1) κ))).prod = 1 :=
      List.prod_eq_one fun c hc => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
        obtain ⟨hs, ht⟩ := not_touch_rest n b (by simpa using hb)
        simp [Grid.edgeFactor, Pi.mulSingle_eq_of_ne hs, Pi.mulSingle_eq_of_ne ht]
    have hr2 : ((List.range n).reverse.map (Edge.theta 0) ++ (List.range (n + 1)).map (Edge.ex · 0)).map
        (fun b => givenDatum t w B Φ b ((locGrid G t w).moveArgs .one (Pi.mulSingle (0, n + 1) κ) x b)) =
        ((List.range n).reverse.map (Edge.theta 0) ++ (List.range (n + 1)).map (Edge.ex · 0)).map
          (fun b => givenDatum t w B Φ b (x b)) :=
      List.map_congr_left fun b hb => by
        obtain ⟨hs, ht⟩ := not_touch_rest n b hb
        congr 1
        simp [Grid.moveArgs, Pi.mulSingle_eq_of_ne hs, Pi.mulSingle_eq_of_ne ht]
    rw [hr1, hr2, mul_one, ← mul_assoc, key x]
    ring

end GlobalTheory.FirstRowEndLaw

namespace GlobalTheory.FirstRowEndLaw

open GlobalTheory.FunObj.GivenAdm

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} {G : GridData L sc} {w : Pl D.host.E}

theorem Tflip_law (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (hw : w ∈ locPl G t)
    (κ : GL (Fin ((locGrid G t w).rank (0, D.R.m))) (Kw w)) (hκ : κ ∈ givenLevel G t w (0, D.R.m)) :
    (locGrid G t w).pathAct .one (oppositePath D.R.m) (Pi.mulSingle (0, D.R.m) κ) (Tflip W B t Φ w) =
      endLam G t w κ • Tflip W B t Φ w := by
  have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt G w) ((locGrid G t w).nu x.1 x.2) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    rw [← Grid.alpha_div_beta]
    exact (hg.square i hi j hj).condν
  have hg1 : ∀ x ∈ flipOrder D.R.m, (Pi.mulSingle (0, D.R.m) κ : (locGrid G t w).VertexGroup) x = 1 := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    exact Pi.mulSingle_eq_of_ne (by simp; omega) _
  have hK : ∀ Y, (Pi.mulSingle (0, D.R.m) κ : (locGrid G t w).VertexGroup) Y ∈ KO (Kw w) _ := fun Y => by
    by_cases hY : Y = (0, D.R.m)
    · subst hY; simpa using (givenLevel_open hL hw (0, D.R.m)).2 hκ
    · rw [Pi.mulSingle_eq_of_ne hY]; exact one_mem _
  have hbase := given_law_at hL B Φ hw D.R.m hm.ne' κ hκ
  have key := flips_law h00.unif h00.cond h00.one_le _ hK (endLam G t w κ) (flipOrder D.R.m) (givenStage t w B Φ) hν hg1
    (canFlip_flipOrder _).1 (fun X => givenLevel_open hL hw X) (givenStage_isAdmissible hL B t Φ hw) hbase
  change (locGrid G t w).pathAct .one (flipStage t w B W Φ).path _ (flipStage t w B W Φ).tensor =
    _ • (flipStage t w B W Φ).tensor at key
  rw [(flipStage_path_level t w B W Φ).1] at key
  exact key

end GlobalTheory.FirstRowEndLaw

namespace GlobalTheory.FirstRowEndLaw

open Formalism.MainNotions in

theorem pde_ne_q' {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {large₂ : SizeData₂ D} {F : Face D A}
    (h : GlobalTheory.RowClaim.HidaSetting large₂ R F) : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
  obtain ⟨⟨P, -, -⟩, -⟩ := h.size
  have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
  exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩

set_option maxHeartbeats 1600000 in

theorem core : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (a : Fin ch.n) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
      ∃ lam : locPl ch.G t → ℂ,
        (∀ w : locPl ch.G t, (locGrid ch.G t w).pathAct .one (GlobalTheory.SplitFlip.oppositePath D.R.m)
            (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (Tflip ch.W ch.S.B t (ch.Phi a) w) =
          lam w • Tflip ch.W ch.S.B t (ch.Phi a) w) ∧
        (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c * ∏ w, lam w =
          ∏ w : locPl ch.G t, (locGrid ch.G t w).edgeFactor .one
            (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (.ex 0 D.R.m) := by
  intro hP hS
  obtain ⟨CF0, hsc⟩ := GlobalTheory.T.first_vertex_weil_orbit_value hP hS
  refine ⟨CF0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, hsc⟩ := hsc ε CF hC
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hat => ?_⟩
  have hs := hsc D large₂ he hx Γ Pl0 T A Ks R F s ch hch hat
  intro t a k hk hk' c hc
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := pde_ne_q' s
  have hcg : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  refine ⟨fun w => endLam ch.G t w.1 (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w.1 k), fun w => ?_, hs t k hk hk' c hc⟩
  exact Tflip_law hL ch.W ch.S.B t (ch.Phi a) hde hcg w.2 _ (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk).1 w)

end GlobalTheory.FirstRowEndLaw
