import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NearPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMidLevOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MidLevMulBeforeLast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PenultimateChartLocalGroupMemNearLevelSetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherPlacePenultimateChartCharacterInverseValuStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi

open GlobalTheory.Mem.Col2.ChartLevel in

theorem chi_eq_prod_eval {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (Q : Finset (HeightOneSpectrum (𝓞 F))) (G : Q → Type) [∀ v, Group (G v)]
    (ψv : ∀ v : Q, G v →* ℂˣ) (κ : S.U) (z : ∀ v : Q, G v)
    (hoff : ∀ v, v ∉ Q → bc (prV (E := E) v) κ.1 = 1)
    (h : ∀ v : Q, S.chi (embU S v.1 (cmp S v.1 κ)) = ψv v (z v)) :
    S.chi κ = (∏ v : Q, (ψv v).comp (Pi.evalMonoidHom G v)) z := by
  rw [MonoidHom.finsetProd_apply, chi_eq_prod S Q κ (fun w _ hw => hoff w hw), ← Finset.prod_coe_sort Q]
  exact Finset.prod_congr rfl fun v _ => h v

set_option maxHeartbeats 1000000 in

theorem exists_locChi : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∃ ψv : ↥(⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) →* ℂˣ, ∀ β (x : (K β).lev.Uloc v) (w : ↥(⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)), reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ w.1 = x.1 → (K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) = ψv w := by
  intro B X I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hF hU hchi Lb0 hLb v hv
  have hB := GlobalTheory.Mem.Col2.QChi.nearSet_closed I hOk l Z a v
  have hC := GlobalTheory.Mem.Col2.QChi.valV_mul I hOk l Z a v
  let G' : Subgroup (GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) :=
    { carrier := GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v
      one_mem' := hB.1
      mul_mem' := fun {x y} hx hy => hB.2.1 x y hx hy
      inv_mem' := fun {x} hx => hB.2.2 x hx }
  let G'' := G'.comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom
  have hle : (⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) ≤ G'' :=
    iSup_le fun β' => Subgroup.comap_mono fun x hx => GlobalTheory.T.penultimateChart_localGroup_mem_nearLevelSet I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hU hchi Lb0 hLb v hv β' ⟨x, hx⟩
  let f : G'' →* ℂ :=
    { toFun := fun w => GlobalTheory.Mem.Col2.QChi.valV I l Z a v (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ w.1)
      map_one' := by
        show GlobalTheory.Mem.Col2.QChi.valV I l Z a v (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ 1) = 1
        rw [map_one]
        exact hC.1
      map_mul' := fun x y => by
        show GlobalTheory.Mem.Col2.QChi.valV I l Z a v (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (x.1 * y.1)) = _
        rw [map_mul]
        exact hC.2 _ _ x.2 y.2 }
  refine ⟨(f.toHomUnits)⁻¹.comp (Subgroup.inclusion hle), fun β x w hw => ?_⟩
  have hd := GlobalTheory.T.furtherPlace_penultimateChart_character_inverseValue I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hF hU hchi Lb0 hLb v hv β x
  show _ = (f.toHomUnits (Subgroup.inclusion hle w))⁻¹
  refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
  show (((K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) : ℂˣ) : ℂ) * GlobalTheory.Mem.Col2.QChi.valV I l Z a v (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ w.1) = 1
  exact (congrArg (fun y => (((K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) : ℂˣ) : ℂ) * GlobalTheory.Mem.Col2.QChi.valV I l Z a v y) hw).trans hd

set_option maxHeartbeats 1000000 in

theorem exists_chi_further : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∃ ψ : (∀ v : Q, ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)) →* ℂˣ, ∀ β (κ : (K β).lev.U) (z : ∀ v : Q, ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)), (∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (z v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) → (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ψ z := by
  intro B X I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hF hU hchi Lb0 hLb
  choose ψv hψv using fun (v : Q) => exists_locChi I hOk hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hF hU hchi Lb0 hLb v.1 v.2
  refine ⟨∏ v : Q, (ψv v).comp (Pi.evalMonoidHom (fun v : Q => ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)) v), ?_⟩
  intro β κ z hz hoff
  exact chi_eq_prod_eval (K β).lev Q _ ψv κ z hoff (fun v => hψv v β _ (z v) (hz v))

end GlobalTheory.Mem.Col2.QChi

end
