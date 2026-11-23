import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTupleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsTransportAdelicCorrection

namespace GlobalTheory.AdForm.StabTrans
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Col2.BwLat GlobalTheory.LvT.Built.ValLat Formalism.HermitianLatticesTheory GlobalTheory.Mem.Col2.ValTie

theorem chi_stab {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} (chOf : (I.stp u a i).Cl → Ch)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (k : Ch → GA B (B.R.N i))
    (hR : I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
      (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k)
    (c : (I.stp u a i).Cl) (s : (I.stp u a i).Stab c) (κ : (K (chOf c)).lev.U)
    (hy : (fun g y x : GA B (B.R.N i) => y = g * y * x) (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
          ((I.stp u a i).gam c.1 s.1)) ((K (chOf c)).y ⟨c, rfl⟩).1 κ.1) :
    ((K (chOf c)).lev.chi κ : ℂ) = B.embLL ((I.stp u a i).chr c.1 s.1 : B.LLˣ) := by
  have h0 := (hR.pt c).of_extTo (I.Q_subset_SQ a) ((LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a))
  have h1 := RatMove.isPtOf_ratAd _ _ B.sp.cm _ _ _ _ s.1.1⁻¹ _ _ h0
  have h2 := lev_part_smul _ _ s.1 ((I.stp u a i).rep c).1.1 (congrArg (fun q => q.1.1) s.2)
  have h3 : ∀ g y x k : GA B (B.R.N i), y = g * y * x → g⁻¹ * (y * k) = y * x * k := fun g y x k h => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← h]
  have h4 : ratAd B.host.F (s.1.1⁻¹) = (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
      ((I.stp u a i).gam c.1 s.1))⁻¹ := by
    rw [ratAd, map_inv, map_inv]
    rfl
  rw [h4, h3 _ _ _ _ hy, ← h2] at h1
  exact hR.chr c κ (1, s.1.2) (map_one (_root_.Formalism.L2.Col.ufGL B.fields.E (B.R.N i))) h1

end GlobalTheory.AdForm.StabTrans

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StabTrans
open Formalism.L2.Theta

theorem finM_mul' {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.finM_mul V g h

theorem rTrans_mul {G : Type} [Monoid G] (a b : G) (F : G → ℂ) : rTrans (a * b) F = rTrans a (rTrans b F) := by
  funext x
  simp only [rTrans, mul_assoc]

theorem rTrans_one {G : Type} [Monoid G] (F : G → ℂ) : rTrans (1 : G) F = F := by
  funext x
  simp only [rTrans, mul_one]

theorem rTrans_list_prod {G α : Type} [Monoid G] (f : α → G) (F : G → ℂ) (h : ∀ i, rTrans (f i) F = F) :
    ∀ L : List α, rTrans (L.map f).prod F = F
  | [] => by simpa using rTrans_one F
  | i :: L => by
    rw [List.map_cons, List.prod_cons, rTrans_mul, rTrans_list_prod f F h L, h i]

end GlobalTheory.AdForm.StabTrans

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.AdForm.trans_stab : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ (e : (I.stp u a j).Cl) (s : (I.stp u a j).Stab e), (I.stp u a j).tr B.fields.emb B.embLL e.1 s.1 ((fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e) = (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hT j hj c hc φ hφ hinv e s
  let eY : (I.chain l u a).Y j ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) j hj :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hR := hA.reads j hj
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hI hP l Z u a j hj (A.bad j) (Ch j) (A.chOf j) (A.K j hj) eY ⟨A.kb j, hR⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF (A.chOf j e))
  have hAd : Ψ ∈ AdFun (A.K j hj (A.chOf j e)).lev (embT (I.rec7 l Z)) := (Submodule.mem_inf.1 hΨ).1
  have hfun : (fun (c : {c // A.chOf j c = A.chOf j e}) (z : Frames (gramC (gramN (I.rec7 l Z) j hj) (embT (I.rec7 l Z)))) =>
      φ c.1 ⟨z.1, z.2⟩) = fun c => Ψ ((A.K j hj (A.chOf j e)).y c) := he.symm
  have rdΨ : ∀ (w : (I.chain l u a).Y j) (g0 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), g0 ∈ GfC _ →
      ∀ x : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F),
      x.1.1 = finM _ (rankN (I.rec7 l Z) j hj) g0 →
      A.rd θ j hj (A.chOf j e) φ w g0 = Ψ x ⟨w.1, w.2⟩ := by
    intro w g0 hg0 x hx
    have hval := (GlobalTheory.AdForm.rdS_val (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X j) (B.R.N j) (rankN (I.rec7 l Z) j hj)
      (gramN (I.rec7 l Z) j hj) rfl (B.T u) (I.rec7 l Z).R.f (A.bad j) (A.K j hj (A.chOf j e)).lev _
      (A.K j hj (A.chOf j e)).y (A.K j hj (A.chOf j e)).y_bij Ψ hAd ⟨w.1, w.2⟩ g0).2.2 x ⟨w.1, w.2⟩ hx (fun τ => by
        have h1 := GlobalTheory.AdForm.ChartVal.infM_fin' θ _ (rankN (I.rec7 l Z) j hj) g0 hg0 τ
        show w.1 τ = infM θ _ _ g0 τ * w.1 τ
        erw [h1, Matrix.one_mul])
    show rdS θ _ (rankN (I.rec7 l Z) j hj) (A.K j hj (A.chOf j e)).lev (A.K j hj (A.chOf j e)).y
      (fun c z => φ c.1 ⟨z.1, z.2⟩) ⟨w.1, w.2⟩ g0 = _
    rw [hfun]
    exact hval
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = Formalism.L2.Col.embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  refine ((GlobalTheory.Mem.Col2.ValTie.stab_inv_iff (E := B.host.E) (F := B.host.F) (sg := sigD (I.rec7 l Z)) (J := gramN (I.rec7 l Z) j hj) (I.stp u a j) B.fields.emb B.embLL e (A.K j hj (A.chOf j e)).lev hemb
    ((A.K j hj (A.chOf j e)).y ⟨e, rfl⟩).1 ((A.K j hj (A.chOf j e)).stabI ⟨e, rfl⟩) (hR.stab e)
    ((A.K j hj (A.chOf j e)).stabI_range ⟨e, rfl⟩)
    (GlobalTheory.AdForm.StabTrans.chi_stab I hI l Z u a j hj (A.chOf j) (A.K j hj) (A.kb j) hR e)
    _ (fun z => ⟨z.1, z.2⟩) (fun _ => rfl)).2 ?_) s
  intro γ hγ κ hy z z' hz

  clear hF hV he hΨ
  obtain ⟨⟨eι, -⟩, -⟩ := id hT
  haveI : Fintype ι := Fintype.ofEquiv _ eι.symm
  classical
  have hJnd : (Finset.univ : Finset ι).toList.Nodup := Finset.nodup_toList _
  have hJall : ∀ i, i ∈ (Finset.univ : Finset ι).toList := fun i => Finset.mem_toList.2 (Finset.mem_univ i)
  obtain ⟨hlev1, hlev2⟩ := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hI hP l Z u a Ch A hA k ι p β Q L hT _ hJnd hJall j hj (A.chOf j e)
  obtain ⟨kA, hkAf, hkAe⟩ := GlobalTheory.Core.Mi.PinModel.exists_finM ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj)
    ⟨κ.1, (((A.K j hj (A.chOf j e)).lev.U_eq κ.1).1 κ.2).1⟩
  have hkAU : kA ∈ A.U j (A.chOf j e) := (hA.U j hj _ kA).2 ⟨hkAf, κ, hkAe.symm⟩
  obtain ⟨g, hg, κ', hκ'off, hdec⟩ := hlev2 kA hkAU
  have hPK : ((Finset.univ : Finset ι).toList.map fun i => (β j i).gl (g i)).prod ∈
      (A.chi j (A.chOf j e)).ker.map (A.U j (A.chOf j e)).subtype := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨h, h1⟩ := hlev1 i (g i) (hg i)
    exact ⟨⟨_, h⟩, h1, rfl⟩
  obtain ⟨P0, hP0chi, hP0e⟩ := Subgroup.mem_map.1 hPK
  rw [MonoidHom.mem_ker] at hP0chi
  set P := ((Finset.univ : Finset ι).toList.map fun i => (β j i).gl (g i)).prod with hPdef
  have hP0e' : P0.1 = P := hP0e
  have hκ'U : κ' ∈ A.U j (A.chOf j e) := by
    have : κ' = P0.1⁻¹ * kA := by rw [hdec, hP0e']; group
    rw [this]
    exact mul_mem (inv_mem P0.2) hkAU
  obtain ⟨κ'', hκ''⟩ := ((hA.U j hj _ κ').1 hκ'U).2
  have hchi : ((A.K j hj (A.chOf j e)).lev.chi κ : ℂ) = ((A.K j hj (A.chOf j e)).lev.chi κ'' : ℂ) := by
    rw [← hA.chi j hj _ ⟨kA, hkAU⟩ κ hkAe.symm, ← hA.chi j hj _ ⟨κ', hκ'U⟩ κ'' hκ'']
    have e1 : (⟨kA, hkAU⟩ : A.U j (A.chOf j e)) = P0 * ⟨κ', hκ'U⟩ := Subtype.ext (by
      show kA = P0.1 * κ'
      rw [hP0e', hdec])
    rw [e1, map_mul, hP0chi, one_mul]

  obtain ⟨-, -, hAtF, -, hcm, -, -, hOff, -⟩ := GlobalTheory.FinPl.SetCut.grp_split (I.rec7 l Z) ((I.rec7 l Z).sp.X j) (Finset.univ.image fun i => (p i).v)
  have hPQ : (fun x => ∃ i, x = (p i).v) = (· ∈ (Finset.univ.image fun i => (p i).v)) := by
    funext x
    apply propext
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  have hκ'at : κ' ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∉ (Finset.univ.image fun i => (p i).v)) := by
    have h1 : κ' ∈ GfC _ ⊓ grpOff ((I.rec7 l Z).sp.X j) (fun x => ∃ i, x = (p i).v) :=
      ⟨((hA.U j hj _ κ').1 hκ'U).1, hκ'off⟩
    rw [hOff] at h1
    have hPQn : (fun x => ¬ ∃ i, x = (p i).v) = (· ∉ (Finset.univ.image fun i => (p i).v)) :=
      funext fun x => congrArg Not (congrFun hPQ x)
    rw [hPQn] at h1
    exact h1
  have hcomm : ∀ g' ∈ c.support, g' * κ' = κ' * g' := fun g' hg' => hcm g' (hPQ ▸ hc g' hg') κ' hκ'at
  have hsuppF : ∀ g' ∈ c.support, g' ∈ GfC ((I.rec7 l Z).sp.X j) := fun g' hg' => hAtF (hPQ ▸ hc g' hg')
  have hPf : P ∈ GfC ((I.rec7 l Z).sp.X j) := hP0e' ▸ ((hA.U j hj _ P0.1).1 P0.2).1
  have hhe := hA.h j hj (A.chOf j e) ⟨e, rfl⟩
  have term : ∀ g' ∈ c.support, A.rd θ j hj (A.chOf j e) φ ⟨z.1, z.2⟩ (A.h j (A.chOf j e) ⟨e, rfl⟩ * g') =
      ((A.K j hj (A.chOf j e)).lev.chi κ'' : ℂ) * A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩ (A.h j (A.chOf j e) ⟨e, rfl⟩ * P * g') := by
    intro g' hg'
    obtain ⟨x1, hx1⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl
      (A.h j (A.chOf j e) ⟨e, rfl⟩ * g')
    obtain ⟨x2, hx2⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl
      (A.h j (A.chOf j e) ⟨e, rfl⟩ * P * g')
    have a1 := rdΨ ⟨z.1, z.2⟩ _ (mul_mem hhe.1 (hsuppF g' hg')) x1 hx1
    have a2 := rdΨ ⟨z'.1, z'.2⟩ _ (mul_mem (mul_mem hhe.1 hPf) (hsuppF g' hg')) x2 hx2
    rw [a1, a2]
    refine hAd γ hγ x2 x1 κ'' ?_ z z' hz
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hx1, hx2, hκ'']
    have hyv := congrArg Units.val hy
    erw [Units.val_mul, Units.val_mul] at hyv
    have hk : kA * g' = P * g' * κ' := by rw [hdec, mul_assoc, ← hcomm g' hg', ← mul_assoc]
    have e2 := congrArg (finM ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj)) hk
    simp only [StabTrans.finM_mul'] at e2 ⊢
    conv_lhs => rw [hhe.2, hyv, ← hhe.2]
    erw [← hkAe]
    simp only [Matrix.mul_assoc] at e2 ⊢
    rw [← e2]
    try rfl
  have hinvP := congrFun (StabTrans.rTrans_list_prod (fun i => (β j i).gl (g i)) (trc c (A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩))
    (fun i => hinv _ _ i (g i) (hg i)) (Finset.univ : Finset ι).toList) (A.h j (A.chOf j e) ⟨e, rfl⟩)
  rw [← hPdef] at hinvP
  show trc c (A.rd θ j hj (A.chOf j e) φ ⟨z.1, z.2⟩) (A.h j (A.chOf j e) ⟨e, rfl⟩) =
    ((A.K j hj (A.chOf j e)).lev.chi κ : ℂ) * trc c (A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩) (A.h j (A.chOf j e) ⟨e, rfl⟩)
  rw [← hinvP, hchi]
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g' hg' => ?_
  rw [term g' hg']
  ring
