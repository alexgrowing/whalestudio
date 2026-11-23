import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
namespace GlobalTheory.Mem.R3.Rw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt}

set_option maxHeartbeats 2000000 in

theorem ExtModel.same_carriers (h : Enl B B') : HEq (w'.st Z').toD7.host (w.st Z).toD7.host ∧ HEq (w'.st Z').toD7.sp (w.st Z).toD7.sp ∧
    HEq (tauE (w'.st Z').toD7) (tauE (w.st Z).toD7) ∧ HEq (fun V => GA (w'.st Z').toD7 V) (fun V => GA (w.st Z).toD7 V) ∧
    HEq (PolF (w'.st Z').toD7) (PolF (w.st Z).toD7) ∧ HEq (@Formalism.IndefR.Datum.WO (w'.st Z').toD7) (@Formalism.IndefR.Datum.WO (w.st Z).toD7) ∧
    HEq (@Bridge.Gf (w'.st Z').toD7) (@Bridge.Gf (w.st Z).toD7) ∧ HEq (w'.st Z').toD7.hc (w.st Z).toD7.hc ∧
    Formalism.IndefR.Datum.InfFam (w'.st Z').toD7 = Formalism.IndefR.Datum.InfFam (w.st Z).toD7 ∧
    HEq (@lieAt (w'.st Z').toD7) (@lieAt (w.st Z).toD7) ∧
    HEq (Formalism.L2.Pj.hostOfRecord (w'.st Z').toD7) (Formalism.L2.Pj.hostOfRecord (w.st Z).toD7) ∧
    HEq (Formalism.L2.Pj.datumOfRecord (w'.st Z').toD7) (Formalism.L2.Pj.datumOfRecord (w.st Z).toD7) := by
  obtain ⟨e, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e
  subst e
  refine ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem ExtModel.QE_one (sel) : Formalism.L2.Col.QE (X := B.fields) sel 1 = ∅ := by
  unfold Formalism.L2.Col.QE
  split
  · rename_i h
    have : Qprime (1 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := by
      ext v; simp [Qprime]
    simp [this]
  · rfl

theorem ExtModel.rowSG_ref (U : Set w.I.ι) :
    Formalism.L2.Col.rowSG (B.primes w.px) w.I.sel (mu0F (X := B.fields) (tuOf w.I U)).1 = (B.primes w.px).vGs := by
  show Formalism.L2.Col.uSG _ (Formalism.L2.Col.QE (X := B.fields) w.I.sel 1) = _
  rw [ExtModel.QE_one]
  simp [Formalism.L2.Col.uSG]

set_option maxHeartbeats 2000000 in

theorem ExtModel.deco_eq (h : Enl B B') (hp : HEq w'.px w.px) (U : Set w.I.ι) (U' : Set w'.I.ι) (j : ℕ) :
    (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I U')).1 j).D =
      (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I U)).1 j).D ∧
    Gc B' w'.px = Gc B w.px := by
  have a := ExtModel.rowSG_ref (w := w) U
  have a' := ExtModel.rowSG_ref (w := w') U'
  show (letI := B'.fields.starE; Formalism.L2.Col.DecoSet B'.fields.E B'.R.nV ∅ (Formalism.L2.Col.rowSG (B'.primes w'.px) w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I U')).1)) =
    (letI := B.fields.starE; Formalism.L2.Col.DecoSet B.fields.E B.R.nV ∅ (Formalism.L2.Col.rowSG (B.primes w.px) w.I.sel (mu0F (X := B.fields) (tuOf w.I U)).1)) ∧ _
  rw [a, a']
  clear a a'
  generalize w'.px = p' at hp ⊢
  generalize w.px = p at hp ⊢
  obtain ⟨e, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e
  subst e
  cases hp
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 2000000 in

theorem ExtModel.par_eq (h : Enl B B') :
    HEq (fun W : HSp (w'.st Z').toD7 => parAt W (w'.st Z').toD7.what₂.embLL) (fun W : HSp (w.st Z).toD7 => parAt W (w.st Z).toD7.what₂.embLL) := by
  have a : labE (D := (w.st Z).toD7) (w.st Z).toD7.what₂.embLL = tauE (w.st Z).toD7 := funext fun τ => B.fields_embC τ
  have a' : labE (D := (w'.st Z').toD7) (w'.st Z').toD7.what₂.embLL = tauE (w'.st Z').toD7 := funext fun τ => B'.fields_embC τ
  unfold parAt kapAt lab
  rw [a, a']
  clear a a'
  obtain ⟨e, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e
  subst e
  exact HEq.rfl

variable {hX : B.fields.Ok} {Wt W₁ : Set B.places.Pl}

theorem ExtModel.not_ext {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w.st Z) w.I hX T W₁}
    (h : z'.R.ψ ≠ z.R.ψ ∨ z'.R.nW ≠ z.R.nW) : ¬ Ext z z' :=
  fun e => h.elim (fun q => q (eq_of_heq e.ψ)) fun q => q (eq_of_heq e.nW)

theorem ExtModel.nonzeroIndexPlaces_adelicDataResized_eq {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w.st Z) w.I hX T W₁} (e : Ext z z') :
    z.W1 (fun _ _ => 0) = z'.W1 fun _ _ => 0 :=
  Set.ext fun v => e.W1 v v fun x x' q => by
    have : x = x' := RingOfIntegers.ext ((w.D Z).what₂.embLL.injective q)
    rw [this]

theorem ExtModel.below_exists (D D' : D7) (h : Set.range D.what₂.embLL ⊆ Set.range D'.what₂.embLL) (v' : D'.what₂.places.Pl) :
    ∃! v, Below D D' v v' := by
  choose g hg using fun x => h ⟨x, rfl⟩
  have inj := D'.what₂.embLL.injective
  let ι : D.what₂.LL →+* D'.what₂.LL :=
    { toFun := g
      map_one' := inj (by rw [hg, map_one, map_one])
      map_mul' := fun a b => inj (by rw [hg, map_mul, map_mul, hg, hg])
      map_zero' := inj (by rw [hg, map_zero, map_zero])
      map_add' := fun a b => inj (by rw [hg, map_add, map_add, hg, hg]) }
  letI : Algebra D.what₂.LL D'.what₂.LL := ι.toAlgebra
  have key : ∀ (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL), D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) ↔
      algebraMap (𝓞 D.what₂.LL) (𝓞 D'.what₂.LL) x = x' := fun x x' => by
    constructor
    · intro q
      exact RingOfIntegers.ext (inj ((hg _).trans q))
    · rintro rfl
      exact (hg _).symm
  refine ⟨D.plEq.symm ((D'.plEq v').under (𝓞 D.what₂.LL)), fun x x' q => ?_, fun v hv => ?_⟩
  · rw [Equiv.apply_symm_apply, ← (key x x').1 q]
    rfl
  · rw [Equiv.eq_symm_apply]
    ext x
    exact hv x _ ((key x _).2 rfl)

set_option maxHeartbeats 4000000 in

theorem ExtModel.mmap_eq (h : Enl B B') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → SPar} {S' : (w'.st Z').toD7.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel (Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (l : HEq M'.lam M.lam) (e : HEq M'.ε M.ε)
    (g : HEq M'.fr M.fr) :
    Formalism.IndefR.Mult.MMap M' = Formalism.IndefR.Mult.MMap M ∧ LowT M' = LowT M ∧ M'.Vec = M.Vec ∧
      HEq (inferInstance : Module ℂ (Formalism.IndefR.Mult.MMap M')) (inferInstance : Module ℂ (Formalism.IndefR.Mult.MMap M)) ∧
      HEq (inferInstance : Module ℂ (LowT M')) (inferInstance : Module ℂ (LowT M)) := by
  obtain ⟨q, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d l e g
  cases a; cases b; cases c; cases d; cases l; cases e; cases g
  exact ⟨rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩

theorem ExtModel.sign_at_base_place_eq_embedding (z : Dat (w.st Z) w.I hX T Wt) :
    sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A = (w.st Z).toD7.what₂.embLL :=
  if_pos z.R.hv0

set_option maxHeartbeats 4000000 in

theorem ExtModel.more_carriers (h : Enl B B') (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    (k : WeightFamilies.Wt (w.st Z).toD7 ((i : ℕ) + 1)) :
    (∃ k' : WeightFamilies.Wt (w'.st Z').toD7 ((i' : ℕ) + 1), HEq k'.aP k.aP ∧ HEq k'.aM k.aM ∧ k'.n = k.n) ∧
    Measure (GA (w'.st Z').toD7 (Vc (w'.st Z').toD7 i')) = Measure (GA (w.st Z).toD7 (Vc (w.st Z).toD7 i)) ∧
    Measure (GA (w'.st Z').toD7 (Wc (w'.st Z').toD7 i')) = Measure (GA (w.st Z).toD7 (Wc (w.st Z).toD7 i)) := by
  obtain ⟨q, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  exact ⟨⟨{ k with }, HEq.rfl, HEq.rfl, rfl⟩, rfl, rfl⟩

set_option maxHeartbeats 4000000 in

theorem ExtModel.pol_eq (h : Enl B B') (n : ℕ) :
    Formalism.L2.DIV.Pol ℂ B'.fields.Tau n = Formalism.L2.DIV.Pol ℂ B.fields.Tau n ∧ HEq B'.wts.lamV B.wts.lamV := by
  obtain ⟨q, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  exact ⟨rfl, HEq.rfl⟩

theorem ExtModel.meas_eq {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w.st Z) w.I hX T W₁} (e : Ext z z') (i : Fin (w.st Z).toD7.R.m) :
    z'.R.νW i = z.R.νW i ∧ z'.R.fdW i = z.R.fdW i ∧ z'.R.ΛY = z.R.ΛY :=
  ⟨eq_of_heq (e.ref i i rfl).2.2.2.2.2.2.1, eq_of_heq (e.ref i i rfl).2.2.2.2.2.2.2, eq_of_heq e.ΛY⟩

set_option maxHeartbeats 4000000 in

theorem ExtModel.premise_zero (h : Enl B B') (U : Set w.I.ι) (U' : Set w'.I.ι) (j : ℕ) (d d') :
    HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ)
      ((0 : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I U')).1 j).EqFun).1 d').1)
      (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ)
      ((0 : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I U)).1 j).EqFun).1 d).1) := by
  refine HEq.trans (heq_of_eq (map_zero _)) (HEq.trans ?_ (heq_of_eq (map_zero _)).symm)
  clear d d'
  obtain ⟨q, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  exact HEq.rfl

end GlobalTheory.Mem.R3.Rw
end
