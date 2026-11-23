import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasChainW

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ChainPts

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def coef {X : Scheme.{0}} {F : X.Modules} {r : ℕ} (d : Bool) {V V' : X.Opens} {e : Fin r → Γ(F, V)} {s : Fin r → Γ(F, V')}
    (he : GlobalTheory.VB.IsFrame e) (hs : GlobalTheory.VB.IsFrame s) (l i : Fin r) : Γ(X, V ⊓ V') :=
  match d with
  | false => (he.basis inf_le_left).repr (resM F inf_le_right (s i)) l
  | true => (hs.basis inf_le_right).repr (resM F inf_le_left (e l)) i

structure IsLat (Z : LocM.Mdl Y i₀) {X : Scheme.{0}} (h : X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (d b : Bool)
    (F : X.Modules) (s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)) : Prop where

  frame : ∀ a, GlobalTheory.VB.IsFrame (s a)

  glue : ∀ (k : Type) [Field k] (w : Sp k ⟶ X) (a a' : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k)
    (φ' : Γ(Z.X, (Z.U a').1) →+* k), spMap φ ≫ Z.chart a = w ≫ h → spMap φ' ≫ Z.chart a' = w ≫ h → ∀ j,
      IsCombAtG (Y Z.i).t (w ≫ h ≫ Z.π) (fun i => (Z.fr a).bc φ (x i).1 (x i).2)
        (fun i => valF w _ (coef d (frame a) (frame a') i j)) ((Z.fr a').bc φ' (x j).1 (x j).2)

  norm : ∀ (y : Z.Pt) (w : Sp ↥(intO ↥y.C.S) ⟶ X), w ≫ h = y.z → ∀ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S),
    spMap φ ≫ Z.chart a = y.gen → ∀ (V : X.Opens) (e : Fin r → Γ(F, V)) (he : GlobalTheory.VB.IsFrame e), ⊤ ≤ w ⁻¹ᵁ V →
      ∀ (cf : Fin r → ↥y.C.S) (v : Sp (DualNumber ↥y.C.S) ⟶ (Y Z.i).t.G.left),
        IsCombAtG (Y Z.i).t (y.gen ≫ Z.π) (fun i => (Z.fr a).bc φ (x i).1 (x i).2) cf v →
          (v ∈ lat (Y Z.i).t p (y.gen ≫ Z.π) b ↔
            ∀ l, ‖∑ i, cf i * valF (spMap (intO ↥y.C.S).subtype ≫ w) _ (coef d he (frame a) l i)‖ ≤ 1)

def IsLatPres (Z : LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O}
    (h : B.X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (d : Bool) (P : Pres B) : Prop :=
  P.r = r ∧ ∃ s : ∀ a : Fin Z.m, Fin r → Γ(P.E', h ⁻¹ᵁ (Z.U a).1),
    IsLat Z h x d d P.E' s ∧ IsLat Z h x d (!d) P.E fun a i => P.ψ.app _ (s a i)

def Initial {r : ℕ} (x : Fin r → Letter Dw) : Prop :=
  Function.Injective x ∧ ∀ (i : Fin r) (k : Fin (Dw.mult (x i).1)), k < (x i).2 → ∃ i' < i, x i' = ⟨(x i).1, k⟩

def StepNorms (Dw : Datum H) (p : ℕ) {r : ℕ} (st : Fin r → ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Fin r → Letter Dw) : Prop :=
  ∀ (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (w : Sp C ⟶ X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) (b : Bool) (i : Fin r),
    lnStep t w u p b (st i) = Real.log (GlobalTheory.ShFam.Pad.grNorm t w (lat t p w b) (fun k => u (x k).1 (x k).2) i)

example : Initial (Dw := Dw) (r := 0) finZeroElim ∧ StepNorms Dw p (r := 0) finZeroElim finZeroElim :=
  ⟨⟨fun i => i.elim0, fun i => i.elim0⟩, fun _ _ _ _ _ _ _ _ i => i.elim0⟩

theorem grNorm_comp_cast {X : Scheme.{0}} {t : SAB H X} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (w : Sp C ⟶ X) (Λ : Set (Sp (DualNumber C) ⟶ t.G.left)) {m n : ℕ} (e : m = n)
    (u : Fin n → (Sp (DualNumber C) ⟶ t.G.left)) (i : Fin m) :
    GlobalTheory.ShFam.Pad.grNorm t w Λ (fun k => u (k.cast e)) i = GlobalTheory.ShFam.Pad.grNorm t w Λ u (i.cast e) := by
  subst e
  rfl

theorem initial_cast {m : ℕ} (τ : E →+* ℂ) (e : m = Dw.mult τ) : Initial fun i : Fin m => (⟨τ, i.cast e⟩ : Letter Dw) :=
  ⟨fun _ _ h => Fin.ext (congrArg (fun x : Letter Dw => (x.2 : ℕ)) h), fun _ k hk => ⟨k.cast e.symm, hk, rfl⟩⟩

theorem stepNorms_cast {m : ℕ} (τ : E →+* ℂ) (e : m = Dw.mult τ) (h : τ (H.rt : E) = H.rt0 → vDiff E p = 0) :
    StepNorms Dw p (fun i : Fin m => .inl (τ, i)) fun i => ⟨τ, i.cast e⟩ := by
  intro X t C _ _ w u b i
  have h₀ : (if b = true ∧ τ (H.rt : E) = H.rt0 then vDiff E p * Real.log p else 0) = 0 := by
    split_ifs with h'
    · rw [h h'.2, zero_mul]
    · rfl
  simp only [lnStep]
  rw [dif_pos (show (i : ℕ) < _ from (i.cast e).2), h₀, sub_zero]
  exact congrArg Real.log (grNorm_comp_cast w _ e (u τ) i).symm

theorem pairwise_letters : (letters Dw).Pairwise fun x y => x.1 = y.1 → (x.2 : ℕ) < y.2 := by
  refine List.pairwise_flatMap.2 ⟨fun a _ => ?_, (List.nodup_finRange _).imp fun hne x hx y hy e => ?_⟩
  · refine List.pairwise_map.2 ((List.pairwise_lt_finRange _).imp ?_)
    exact fun h _ => h
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hy
    exact absurd ((Fintype.equivFin (E →+* ℂ)).symm.injective e) hne

example (τ : E →+* ℂ) (h : 1 < Dw.mult τ) : ¬ Initial fun _ : Fin 1 => (⟨τ, ⟨1, h⟩⟩ : Letter Dw) := fun H' => by
  obtain ⟨i, hi, -⟩ := H'.2 0 ⟨0, zero_lt_one.trans h⟩ Nat.zero_lt_one
  exact absurd hi (Fin.not_lt_zero i)

end Free

section admitted

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
  {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits}

def xLie (jc : KW p →+* ℂ) (τ : Emb D p) (i : Fin (rkOf (PsiOf D jc) N j τ)) : Letter S.Dw :=
  ⟨jc.comp τ, i.cast (mult_comp S jc τ).symm⟩

def xOm (jc : KW p →+* ℂ) (τ : Emb D p) (i : Fin (N - rkOf (PsiOf D jc) N j τ)) : Letter S.Dw :=
  ⟨conjEmb (jc.comp τ), i.rev.cast (mult_conj_comp S jc τ).symm⟩

def xAll (k : Fin (D.R.f * N)) : Letter S.Dw := (letters S.Dw).get (k.cast (length_letters S).symm)

theorem xLie_initial (jc : KW p →+* ℂ) (τ : Emb D p) : Initial (xLie S jc τ) := initial_cast _ _

theorem xOm_initial (jc : KW p →+* ℂ) (τ : Emb D p) : Initial fun i => xOm S jc τ (Fin.rev i) := by
  simp only [xOm, Fin.rev_rev]
  exact initial_cast _ _

theorem xAll_bijective : Function.Bijective (xAll S) :=
  (List.Nodup.getBijectionOfForallMemList _ (GlobalTheory.Proof.LetterConjugation.nodup_letters S.Dw) (GlobalTheory.Proof.LetterConjugation.mem_letters S.Dw)).2.comp
    (finCongr (length_letters S).symm).bijective

theorem xAll_initial : Initial (xAll S) := by
  refine ⟨(xAll_bijective S).1, fun i k hk => ?_⟩
  obtain ⟨i', hi'⟩ := (xAll_bijective S).2 ⟨(xAll S i).1, k⟩
  refine ⟨i', lt_of_not_ge fun h => ?_, hi'⟩
  have e : ((xAll S i').2 : ℕ) = k := congrArg (fun x : Letter S.Dw => (x.2 : ℕ)) hi'
  have hk' : (k : ℕ) < (xAll S i).2 := hk
  rcases h.eq_or_lt with rfl | h
  · omega
  · have : ((xAll S i).2 : ℕ) < (xAll S i').2 :=
      List.pairwise_iff_get.1 pairwise_letters _ _ (show i.cast (length_letters S).symm < i'.cast _ from h)
        (congrArg Sigma.fst hi').symm
    omega

theorem xLie_stepNorms (jc : KW p →+* ℂ) (τ : Emb D p) (h : vDiff D.host.E p = 0) :
    StepNorms S.Dw p (fun i => .inl (jc.comp τ, i)) (xLie S jc τ) := stepNorms_cast _ _ fun _ => h

theorem xOm_stepNorms (jc : KW p →+* ℂ) (τ : Emb D p) (h : vDiff D.host.E p = 0) :
    StepNorms S.Dw p (fun i => .inl (conjEmb (jc.comp τ), (Fin.rev (Fin.rev i) : Fin _))) fun i => xOm S jc τ (Fin.rev i) := by
  simp only [xOm, Fin.rev_rev]
  exact stepNorms_cast _ _ fun _ => h

theorem xAll_stepNorms (p : ℕ) : StepNorms S.Dw p (fun k : Fin (D.R.f * N) => .inr k) (xAll S) := by
  intro X t C _ _ w u b i
  simp only [lnStep]
  rw [dif_pos (show (i : ℕ) < _ from (i.cast (length_letters S).symm).2)]
  exact congrArg Real.log (grNorm_comp_cast w _ (length_letters S).symm
    (fun i => u ((letters S.Dw).get i).1 ((letters S.Dw).get i).2) i).symm

variable {S}

def HasChainPts (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ) (o : ℕ) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
  ∀ c : (nmodel z.Z).Comp, ∃ (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c))
    (Ch : Chain p B (phiPow D (p := p) 1) o), GlobalTheory.IsNormalScheme B.X ∧ f.relDim = 0 ∧ ∀ τ,
      IsLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) (xLie S jc τ) false (Ch.lw τ) ∧
      IsLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) (xOm S jc τ) true (Ch.oo τ)

def HasChainPtsW (z : AdmAt S κ hp hW) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
  ∀ c : (nmodel z.Z).Comp, ∃ (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c))
    (Ch : Chain p B (id : Unit → Unit) 1), GlobalTheory.IsNormalScheme B.X ∧ f.relDim = 0 ∧
      IsLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) (xAll S) false (Ch.lw ()) ∧
      IsLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) (fun k => xAll S k.rev) true (Ch.oo ())

def ReadsLie (z : AdmAt S κ hp hW) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
  ∀ (d r : ℕ) (st : Fin r → ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ) (x : Fin r → Letter S.Dw)
    (h : ∀ i, letterOf S.Dw (st i) = some (x i)), Initial x → StepNorms S.Dw p st x →
    ∀ (c : (nmodel z.Z).Comp) (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c)),
      GlobalTheory.IsNormalScheme B.X → f.relDim = 0 → ∀ P : Pres B, IsLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) x false P →
        Reads p (z.stepPair hp hW d h) (fun q => picSymPull f.f (picSymPull ((nmodel z.Z).compι c) q))
          (fun e => Vert.Model.vPullQ f.comp_str (NModel.vResQ c e))
          (haveI := P.iso; (Vert.Model.GenIso.ofHom P.ψ).symm)

def ReadsOm (z : AdmAt S κ hp hW) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
  ∀ (d r : ℕ) (st : Fin r → ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ) (x : Fin r → Letter S.Dw)
    (h : ∀ i, letterOf S.Dw (st i) = some (x i)), Initial (fun i : Fin r => x i.rev) →
    StepNorms S.Dw p (fun i : Fin r => st i.rev) (fun i => x i.rev) →
    ∀ (c : (nmodel z.Z).Comp) (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c)),
      GlobalTheory.IsNormalScheme B.X → f.relDim = 0 → ∀ P : Pres B, IsLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) x true P →
        Reads p (z.dualPair hp hW d h) (fun q => picSymPull f.f (picSymPull ((nmodel z.Z).compι c) q))
          (fun e => Vert.Model.vPullQ f.comp_str (NModel.vResQ c e))
          (haveI := P.iso; Vert.Model.GenIso.ofHom P.ψ)

end admitted

def ChainPtsSt : Prop := AtGood fun _ _ _ _ _ _ jc z => ∀ o, HasChainPts z jc o

def ChainPtsWSt : Prop := AtAll fun _ _ _ _ _ _ _ z => HasChainPtsW z

def ReadsLieSt : Prop := AtAll fun _ _ _ _ _ _ _ z => ReadsLie z

def ReadsOmSt : Prop := AtAll fun _ _ _ _ _ _ _ z => ReadsOm z

end GlobalTheory.ChainPts

end
