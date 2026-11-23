import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTuple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointEqProdSplitComponentsMulOff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.DiaReduce

theorem conj_level {G ι : Type*} [Group G] (U : Subgroup G) (χ : U →* ℂˣ) (J : List ι) (f : ι → G) (x κ' : G) (κ : U)
    (hκ : κ.1 = (J.map f).prod * κ') (hc : x * κ' = κ' * x)
    (h1 : ∀ i, ∃ h : f i ∈ U, χ ⟨_, h⟩ = 1) (h2 : ∀ i, ∃ h : x⁻¹ * f i * x ∈ U, χ ⟨_, h⟩ = 1) :
    ∃ κ'' : U, κ.1 * x = x * κ''.1 ∧ χ κ'' = χ κ := by
  let K : Subgroup G := χ.ker.map U.subtype
  have hK : ∀ g, (∃ h : g ∈ U, χ ⟨_, h⟩ = 1) → g ∈ K := fun g ⟨h, h'⟩ => ⟨⟨g, h⟩, h', rfl⟩
  have hP : (J.map f).prod ∈ K := K.list_prod_mem fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact hK _ (h1 i)
  have hP' : (J.map f).prod ∈ K.comap (MulAut.conj x⁻¹).toMonoidHom := Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    have := hK _ (h2 i)
    simpa using this
  have hP'' : x⁻¹ * (J.map f).prod * x ∈ K := by simpa using hP'
  obtain ⟨m, hm, hm'⟩ := K.mul_mem hP'' (K.inv_mem hP)
  have hm1 : χ m = 1 := hm
  have hm2 : m.1 = x⁻¹ * (J.map f).prod * x * (J.map f).prod⁻¹ := hm'
  refine ⟨m * κ, ?_, by rw [map_mul, hm1, one_mul]⟩
  rw [Subgroup.coe_mul, hm2, hκ, mul_assoc, ← hc]
  group

variable {D : D7}

theorem real_le_off (V : HSp D) (P : Pl D → Prop) : GinfC V ≤ grpOff V P := by
  intro a ha
  rw [GinfC, MonoidHom.mem_ker] at ha
  rw [grpOff, GlobalTheory.FinPl.LocProd.mem_congGrp_entries]
  intro i j
  have h2 : finPart D (Formalism.L2.Theta.mt V a i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun x : GL (Fin V.rank) _ => x.1 i j) ha
  rw [idOff, Ideal.mem_iInf]
  intro w
  rw [RingHom.mem_ker, Matrix.sub_apply, GlobalTheory.FinPl.compAt, RingHom.comp_apply, RingHom.map_sub, h2]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, sub_self, RingHom.map_zero]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero, sub_self, RingHom.map_zero]

theorem grpOff_anti (V : HSp D) {P P' : Pl D → Prop} (h : ∀ w, P' w → P w) : grpOff V P ≤ grpOff V P' := by
  apply GlobalTheory.FinPl.LocProd.congGrp_mono
  intro a ha
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall] at ha ⊢
  exact fun w hw => ha w (h w hw)

end GlobalTheory.AdForm.DiaReduce

open GlobalTheory.AdForm.DiaReduce in

theorem GlobalTheory.AdForm.DiaReduce.rd_laws {B : Base} {X : PreX B.toPre} (I : TC B X) (hok : I.Ok) (hpins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is)
    (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ) (i : ℕ) (hi : i ≤ B.R.m) (φ) (hφ : φ ∈ (I.fm l u a).Fi i) (β : Ch i)
    (y : (I.chain l u a).Y i) (k : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) (hk : k ∈ GinfC ((I.rec7 l Z).sp.X i)) :
    ∃ y' : (I.chain l u a).Y i, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X i), ∀ g, ∀ κ : A.U i β,
      A.rd θ i hi β φ y (γ * (g * k * κ.1)) = (A.chi i β κ : ℂ) * A.rd θ i hi β φ y' g := by
  let eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hok hpins l Z u a i hi (A.bad i) (Ch i) (A.chOf i) (A.K i hi) eY
    ⟨A.kb i, hA.reads i hi⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  have laws := GlobalTheory.AdForm.RdLaw.rdS_laws (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X i) (B.R.N i) (rankN (I.rec7 l Z) i hi)
    (gramN (I.rec7 l Z) i hi) rfl (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev {c // A.chOf i c = β}
    (A.K i hi β).y (A.K i hi β).y_bij _ (fun c z => φ c.1 ⟨z.1, z.2⟩) (hF β) ⟨y.1, y.2⟩
  obtain ⟨hL, hK, hR, -⟩ := laws
  let z := GlobalTheory.AdForm.Model.trFr θ ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) k (eY y)
  refine ⟨eY.symm z, fun γ hγ g κ => ?_⟩
  obtain ⟨hκf, κ', hκ'⟩ := (hA.U i hi β κ.1).1 κ.2
  have hchi := hA.chi i hi β κ κ' hκ'
  have e1 := hL γ hγ (g * k * κ.1)
  have e2 := hK κ.1 hκf κ' hκ' (g * k)
  have e3 := hR k hk z (fun τ => rfl) g
  exact e1.trans (e2.trans (congrArg₂ (· * ·) (congrArg (fun x : ℂˣ => (x : ℂ)) hchi.symm) e3))

open GlobalTheory.AdForm.DiaReduce in

theorem GlobalTheory.AdForm.diaSum_eq_zero_of_reps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b y, (∀ (c : {c // A.chOf j c = b}) y', ∑ᶠ s, A.rd θ j hj b φ y' (A.h j b c * (β j i).gl (g s)) = 0) → ∀ x, ∑ᶠ s, A.rd θ j hj b φ y (x * (β j i).gl (g s)) = 0 := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj φ hφ i v _ g hg b y h0 x
  have hinj := GlobalTheory.AdForm.StdT.places_injective I hok hpins l Z u p β Q L hS
  obtain ⟨e, -⟩ := hS.1
  haveI : Finite ι := Finite.of_equiv _ e.symm
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨hst, hdec⟩ := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hok hpins l Z u a Ch A hA k ι p β Q L hS (Finset.univ.toList) (Finset.nodup_toList _)
    (fun i => Finset.mem_toList.2 (Finset.mem_univ i)) j hj b
  obtain ⟨γ, hγ, c, r, hr, κ, hκ, rfl⟩ := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hok hpins l Z u a Ch A hA j hj b).1.dec x
  obtain ⟨g', hg', κ', hκ', hκe⟩ := hdec κ hκ
  obtain ⟨y', hy'⟩ := rd_laws I hok hpins l Z u a Ch A hA θ hθ j hj φ hφ b y r hr
  have hAt : ∀ i' t, (β j i').gl t ∈ grpAt ((I.rec7 l Z).sp.X j) (· = (p i').v) := fun i' t =>
    GlobalTheory.FinPl.FrameLat.gl_mem_grpAt (β j i') t
  have hcomm := ((GlobalTheory.FinPl.localComponents (I.rec7 l Z) (· = (p i).v)).2 ((I.rec7 l Z).sp.X j)).2.1
  have key : ∀ s, A.rd θ j hj b φ y (γ * (A.h j b c * r) * κ * (β j i).gl (g s)) =
      (A.chi j b ⟨κ, hκ⟩ : ℂ) * A.rd θ j hj b φ y' (A.h j b c * (β j i).gl (g s)) := by
    intro s
    obtain ⟨κ'', h1, h2⟩ := conj_level (A.U j b) (A.chi j b) Finset.univ.toList (fun i' => (β j i').gl (g' i'))
      ((β j i).gl (g s)) κ' ⟨κ, hκ⟩ hκe
      (hcomm _ (hAt i _) _ (grpOff_anti _ (fun w hw => ⟨i, hw⟩) hκ')) (fun i' => hst i' _ (hg' i')) (fun i' => by
        by_cases hi : i' = i
        · subst hi
          rw [← map_inv, ← map_mul, ← map_mul]
          refine hst i' _ ?_
          rw [mul_smul, mul_smul, hg, smul_comm (g' i') s, hg', ← hg, inv_smul_smul]
        · have hc := hcomm _ (hAt i (g s)) _ (GlobalTheory.FinPl.LocProd.grpAt_le_grpOff' _ _ _
            (fun w hw hw' => hi (hinj (hw.symm.trans hw'))) (hAt i' (g' i')))
          rw [mul_assoc, ← hc, inv_mul_cancel_left]
          exact hst i' _ (hg' i'))
    have hc := hcomm _ (hAt i (g s)) r (real_le_off _ _ hr)
    have h1' : κ * (β j i).gl (g s) = (β j i).gl (g s) * κ''.1 := h1
    have e1 : γ * (A.h j b c * r) * κ * (β j i).gl (g s) = γ * (A.h j b c * (β j i).gl (g s) * r * κ''.1) := by
      rw [mul_assoc, h1', mul_assoc (A.h j b c), hc]
      simp only [mul_assoc]
    rw [e1, hy' γ hγ, h2]
  simp only [key]
  rw [← mul_finsum' _ _ (Set.toFinite _), h0, mul_zero]

end
