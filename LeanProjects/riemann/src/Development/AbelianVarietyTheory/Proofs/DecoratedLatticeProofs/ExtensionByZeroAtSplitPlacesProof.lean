import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChangeBaseVacuumHeisenbergCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCombinationExtendByZeroOrthSumLineStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOSourceSliceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOTargetSliceOrthogonalSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroLeftMemCoreLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroRightMemCoreLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeOrthogonalSumLineAtSplitPlaceStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl.ExtZero

namespace GlobalTheory.FinPl.ExtAllPf

variable {D : D7}

theorem vac_zero' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} (P : Pl D → Prop) :
    Vac ψ S T LS LT P 0 := by
  have h : ∀ u, heisO ψ S T u 0 = 0 := fun u => by funext w; simp [heisO]
  exact ⟨⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun u _ _ => h u⟩, continuous_const, fun _ _ _ _ _ => contDiff_const⟩,
    fun u _ => h _, fun _ _ u _ _ => h u⟩

theorem vac_at' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {v : Pl D}
    {f : WO S T → ℂ} (hv : P v) (h : Vac ψ S T LS LT P f) : Vac ψ S T LS LT (· = v) f := by
  have hle : latO S T (LS : Set _) (LT : Set _) (· = v) ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hz, rest⟩
    exact ⟨α, hα, fun v' hv' => hz v' (fun e => hv' (by subst e; exact hv)), rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem idAt_mono' {P Q : Pl D → Prop} (h : ∀ v, P v → Q v) : idAt D P ≤ idAt D Q := by
  intro a ha
  simp only [idAt, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun hp => w.2 (h _ hp)⟩⟩

theorem combAt_extS {P : Pl D → Prop} {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) {c : WO A T →₀ ℂ}
    (hc : CombAt P c) : CombAt P (extS o T c) := by
  classical
  intro u hu
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  intro i j
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hc x hx i k)

theorem combAt_extT {P : Pl D → Prop} {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {c : WO S A →₀ ℂ}
    (hc : CombAt P c) : CombAt P (extT o S c) := by
  classical
  intro u hu
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hu)
  intro i j
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hc x hx k j)

theorem comb_eq_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (F : WO S T → ℂ) :
    comb ψ S T c F = c.sum (fun u a => a • heisO ψ S T u F) := rfl

theorem comb_extS_slice (ψ : AddChar (AF D.host.F) ℂ) {S A L T : HSp D} (o : OrthDec S A L) (c : WO A T →₀ ℂ)
    (F : WO S T → ℂ) (w : WO A T) (y : WO L T) :
    comb ψ S T (extS o T c) F ((o.resS T).symm (w, y)) = comb ψ A T c (fun w' => F ((o.resS T).symm (w', y))) w := by
  rw [comb_eq_sum, comb_eq_sum, extS, Finsupp.sum_mapDomain_index (h := fun u a => a • heisO ψ S T u F) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [heisO_resS_symm]

theorem comb_extT_slice (ψ : AddChar (AF D.host.F) ℂ) {S A L T : HSp D} (o : OrthDec S A L) (c : WO T A →₀ ℂ)
    (F : WO T S → ℂ) (w : WO T A) (y : WO T L) :
    comb ψ T S (extT o T c) F ((o.resT T).symm (w, y)) = comb ψ T A c (fun w' => F ((o.resT T).symm (w', y))) w := by
  rw [comb_eq_sum, comb_eq_sum, extT, Finsupp.sum_mapDomain_index (h := fun u a => a • heisO ψ T S u F) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [heisO_resT_symm]

section Lists

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem overAll_sb {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S} {LT : Lat T}
    {Ψ : ι → Matrix n n' k → ℂ} : ∀ (l : List ι) (f f' : WO S T → ℂ), OverAll ψ α β LS LT Ψ l f f' →
      ∀ i ∈ l, Ψ i ∈ SB (Matrix n n' k) := by
  intro l
  induction l with
  | nil => intro f f' _ i hi; simp at hi
  | cons j l ih =>
    intro f f' h i hi
    obtain ⟨g, hg, hO⟩ := h
    rcases List.mem_cons.1 hi with rfl | hi
    · exact hO.2.2.2.1
    · exact ih f g hg i hi

def chainOp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : ι → WO S T →₀ ℂ) (l : List ι) (f : WO S T → ℂ) :
    WO S T → ℂ :=
  l.foldr (fun i g => comb ψ S T (e i) g) f

theorem chainOp_vac {LS : Lat S} {LT : Lat T} (e : ι → WO S T →₀ ℂ)
    (hpres : ∀ i j, i ≠ j → ∀ g, Vac ψ S T LS LT (· = (p j).v) g → Vac ψ S T LS LT (· = (p j).v) (comb ψ S T (e i) g)) :
    ∀ (l : List ι) (f : WO S T → ℂ), (∀ i, Vac ψ S T LS LT (· = (p i).v) f) →
      ∀ j, j ∉ l → Vac ψ S T LS LT (· = (p j).v) (chainOp ψ S T e l f) := by
  intro l
  induction l with
  | nil => intro f hf j _; exact hf j
  | cons i l ih =>
    intro f hf j hj
    have hij : i ≠ j := fun h => hj (h ▸ List.mem_cons_self)
    exact hpres i j hij _ (ih f hf j fun h => hj (List.mem_cons_of_mem _ h))

theorem overAll_chain (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T)
    (Φ : ι → Matrix n n' k → ℂ) (e : ι → WO S T →₀ ℂ)
    (hE : ∀ i f₀, Vac ψ S T LS LT (· = (p i).v) f₀ → Over ψ (α i) (β i) LS LT f₀ (Φ i) (comb ψ S T (e i) f₀))
    (hpres : ∀ i j, i ≠ j → ∀ g, Vac ψ S T LS LT (· = (p j).v) g → Vac ψ S T LS LT (· = (p j).v) (comb ψ S T (e i) g)) :
    ∀ (l : List ι), l.Nodup → ∀ f, (∀ i, Vac ψ S T LS LT (· = (p i).v) f) →
      OverAll ψ α β LS LT Φ l f (chainOp ψ S T e l f) := by
  intro l
  induction l with
  | nil => intro _ f _; rfl
  | cons i l ih =>
    intro hl f hf
    obtain ⟨hi, hl'⟩ := List.nodup_cons.1 hl
    exact ⟨chainOp ψ S T e l f, ih hl' f hf, hE i _ (chainOp_vac e hpres l f hf i hi)⟩

set_option maxHeartbeats 1000000 in
theorem pres_of_allComb (hAC : AllComb D) {I : List ι} {P : Pl D → Prop} (hP : Places p I P)
    (hψ : IsStdChar D ψ (-1)) (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) {LS : Lat S} {LT : Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (e : ι → WO S T →₀ ℂ) (he : ∀ i, CombAt (· = (p i).v) (e i)) :
    ∀ i j, i ≠ j → ∀ g, Vac ψ S T LS LT (· = (p j).v) g → Vac ψ S T LS LT (· = (p j).v) (comb ψ S T (e i) g) := by
  intro i j hij g hg
  have hPl : Places (fun _ : Unit => p j) [()] (· = (p j).v) :=
    ⟨List.nodup_singleton _, fun _ => List.mem_singleton.2 rfl, fun a b _ => Subsingleton.elim a b,
      fun x => ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩, fun _ => hP.unit j⟩
  have hc : CombAt (fun x => ¬ (x = (p j).v)) (e i) := by
    intro u hu a b
    have h1 := he i u hu a b
    exact idAt_mono' (P := (· = (p i).v)) (Q := fun x => ¬ (x = (p j).v))
      (fun v hv hvj => hij (hP.inj (show (p i).v = (p j).v from hv.symm.trans hvj))) h1
  exact ((hAC k Unit (fun _ => p j) [()] (· = (p j).v) hPl n n' ψ hψ S T (fun _ => α j) (fun _ => β j) LS LT hS hT
    (fun _ => 0)).2.2 (e i) hc g hg).1

end Lists

theorem chainOp_sliceS (ψ : AddChar (AF D.host.F) ℂ) {ι : Type} {S A L T : HSp D} (o : OrthDec S A L)
    (d : ι → WO A T →₀ ℂ) (y : WO L T) : ∀ (l : List ι) (h : WO S T → ℂ) (w : WO A T),
    chainOp ψ S T (fun i => extS o T (d i)) l h ((o.resS T).symm (w, y)) =
      chainOp ψ A T d l (fun w' => h ((o.resS T).symm (w', y))) w := by
  intro l
  induction l with
  | nil => intro h w; rfl
  | cons i l ih =>
    intro h w
    simp only [chainOp, List.foldr_cons] at ih ⊢
    rw [comb_extS_slice]
    exact congrArg (fun F => comb ψ A T (d i) F w) (funext fun w' => ih h w')

theorem chainOp_sliceT (ψ : AddChar (AF D.host.F) ℂ) {ι : Type} {S A L T : HSp D} (o : OrthDec S A L)
    (d : ι → WO T A →₀ ℂ) (y : WO T L) : ∀ (l : List ι) (h : WO T S → ℂ) (w : WO T A),
    chainOp ψ T S (fun i => extT o T (d i)) l h ((o.resT T).symm (w, y)) =
      chainOp ψ T A d l (fun w' => h ((o.resT T).symm (w', y))) w := by
  intro l
  induction l with
  | nil => intro h w; rfl
  | cons i l ih =>
    intro h w
    simp only [chainOp, List.foldr_cons] at ih ⊢
    rw [comb_extT_slice]
    exact congrArg (fun F => comb ψ T A (d i) F w) (funext fun w' => ih h w')

theorem vac_sliceS {ψ : AddChar (AF D.host.F) ℂ} {S A L T : HSp D} (o : OrthDec S A L) {P : Pl D → Prop}
    {LA : Lat A} {LS : Lat S} {LT : Lat T} (hA : IsSelfDualC A LA) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hO : ∀ v, P v → ∃ LL, OrthAt o LS LA LL v) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) (y : WO L T) :
    Vac ψ A T LA LT P (fun w => f ((o.resS T).symm (w, y))) := by
  have latS := GlobalTheory.ContrComb.extL_mem_latO D S A L T o P LA LT LS hA hT hS hO
  refine ⟨GlobalTheory.T.isThetaFunO_source_slice D ψ S A L T o f y hf.1, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · funext w
    rw [← heisO_resS_symm ψ o (2 • u) f w y]
    have h2 : (o.resS T).symm (2 • u, 0) = 2 • (o.resS T).symm (u, 0) := by
      rw [← map_nsmul]; simp
    rw [h2, hf.2.1 _ (latS u hu)]
  · funext w
    rw [← heisO_resS_symm ψ o u f w y, hf.2.2 e' he' _ (latS u hu) (half_resS_symm o hh)]

theorem vac_sliceT {ψ : AddChar (AF D.host.F) ℂ} {S A L T : HSp D} (o : OrthDec S A L) {P : Pl D → Prop}
    {LA : Lat A} {LS : Lat S} {LT : Lat T} (hA : IsSelfDualC A LA) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hO : ∀ v, P v → ∃ LL, OrthAt o LS LA LL v) {f : WO T S → ℂ} (hf : Vac ψ T S LT LS P f) (y : WO T L) :
    Vac ψ T A LT LA P (fun w => f ((o.resT T).symm (w, y))) := by
  have latT := GlobalTheory.ContrComb.LatT.latO_extR D S A L T o P LA LT LS hA hT hS hO
  refine ⟨GlobalTheory.T.isThetaFunO_target_slice_orthogonal_sum D ψ S A L T o f y hf.1, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · funext w
    rw [← heisO_resT_symm ψ o (2 • u) f w y]
    have h2 : (o.resT T).symm (2 • u, 0) = 2 • (o.resT T).symm (u, 0) := by
      rw [← map_nsmul]; simp
    rw [h2, hf.2.1 _ (latT u hu)]
  · funext w
    rw [← heisO_resT_symm ψ o u f w y, hf.2.2 e' he' _ (latT u hu) (half_resT_symm o hh)]

end GlobalTheory.FinPl.ExtAllPf

namespace GlobalTheory.FinPl.ExtAllPf

set_option maxHeartbeats 2000000 in

theorem ext_all : ∀ D : D7, GlobalTheory.FinPl.ExtAll D := by
  intro D k _ _ _ _ ι p I P hP n n' _ _ _ _ ψ hψ S A L T o ζ hζ α α₀ β hsum LA LS LT ΛA ΛT hA hS hT hlat
  have hAC := GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D
  have hO : ∀ x, P x → ∃ LL, OrthAt o LS LA LL x := by
    intro x hx
    obtain ⟨i, rfl⟩ := (hP.mem x).1 hx
    exact GlobalTheory.T.lattice_orthogonal_sum_line_at_split_place D k (p i) n' S A L o ζ hζ (α i) (α₀ i) (hsum i) (hP.unit i) LA LS (ΛA i) hA hS (hlat i).1
      (hlat i).2.1
  have hv : ∀ {U V : HSp D} {LU : Lat U} {LV : Lat V} {f : WO U V → ℂ}, Vac ψ U V LU LV P f →
      ∀ i, Vac ψ U V LU LV (· = (p i).v) f := fun hf i => vac_at' ((hP.mem _).2 ⟨i, rfl⟩) hf
  refine ⟨hO, fun Ψ c hc => ?_, fun Ψ c hc => ?_⟩
  · have hSB : ∀ i, Ψ i ∈ SB (Matrix n n' k) := fun i => overAll_sb I 0 _ (hc.2 0 (vac_zero' P)) i (hP.all i)
    choose d hd using fun i => (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) n n' ψ hψ (hP.unit i) A T (α i) (β i) LA LA LT LT hA hT hA
      hT).2 (Ψ i) (hSB i)
    have hext : ∀ i f₀, Vac ψ S T LS LT (· = (p i).v) f₀ → Over ψ (α₀ i) (β i) LS LT f₀ (tensCol (Ψ i) (vecInd (ΛT i)))
        (comb ψ S T (extS o T (d i)) f₀) := fun i => (GlobalTheory.T.splitPlace_combination_extendByZero_orthSum_line D k (p i) n n' ψ hψ (hP.unit i) S A L T o ζ hζ (α i)
      (α₀ i) (β i) (hsum i) LA LS LT (ΛA i) (ΛT i) hA hS hT (hlat i).1 (hlat i).2.1 (hlat i).2.2).1 (Ψ i) (d i) (hd i).1
      (hd i).2
    have presA := pres_of_allComb hAC hP hψ α β hA hT d (fun i => (hd i).1)
    have presS := pres_of_allComb hAC hP hψ α₀ β hS hT (fun i => extS o T (d i)) (fun i => combAt_extS o T (hd i).1)
    refine ⟨combAt_extS o T hc.1, fun f hf => ?_⟩
    have key : comb ψ S T (extS o T c) f = chainOp ψ S T (fun i => extS o T (d i)) I f := by
      funext t
      obtain ⟨⟨w, y⟩, rfl⟩ : ∃ q, (o.resS T).symm q = t := ⟨_, (o.resS T).symm_apply_apply t⟩
      rw [comb_extS_slice, chainOp_sliceS]
      have hfy := vac_sliceS o hA hS hT hO hf y
      have := (hAC k ι p I P hP n n' ψ hψ A T α β LA LT hA hT Ψ).2.1 _ _ _ (hc.2 _ hfy)
        (overAll_chain α β LA LT Ψ d (fun i => (hd i).2) presA I hP.nodup _ (hv hfy))
      exact congrFun this w
    rw [key]
    exact overAll_chain α₀ β LS LT _ _ hext presS I hP.nodup f (hv hf)
  · have hSB : ∀ i, Ψ i ∈ SB (Matrix n' n k) := fun i => overAll_sb I 0 _ (hc.2 0 (vac_zero' P)) i (hP.all i)
    choose d hd using fun i => (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) n' n ψ hψ (hP.unit i) T A (β i) (α i) LT LT LA LA hT hA hT
      hA).2 (Ψ i) (hSB i)
    have hext : ∀ i f₀, Vac ψ T S LT LS (· = (p i).v) f₀ → Over ψ (β i) (α₀ i) LT LS f₀ (tensRow (Ψ i) (dualInd (ΛT i)))
        (comb ψ T S (extT o T (d i)) f₀) := fun i => (GlobalTheory.T.splitPlace_combination_extendByZero_orthSum_line D k (p i) n n' ψ hψ (hP.unit i) S A L T o ζ hζ (α i)
      (α₀ i) (β i) (hsum i) LA LS LT (ΛA i) (ΛT i) hA hS hT (hlat i).1 (hlat i).2.1 (hlat i).2.2).2 (Ψ i) (d i) (hd i).1
      (hd i).2
    have presA := pres_of_allComb hAC hP hψ β α hT hA d (fun i => (hd i).1)
    have presS := pres_of_allComb hAC hP hψ β α₀ hT hS (fun i => extT o T (d i)) (fun i => combAt_extT o T (hd i).1)
    refine ⟨combAt_extT o T hc.1, fun f hf => ?_⟩
    have key : comb ψ T S (extT o T c) f = chainOp ψ T S (fun i => extT o T (d i)) I f := by
      funext t
      obtain ⟨⟨w, y⟩, rfl⟩ : ∃ q, (o.resT T).symm q = t := ⟨_, (o.resT T).symm_apply_apply t⟩
      rw [comb_extT_slice, chainOp_sliceT]
      have hfy := vac_sliceT o hA hS hT hO hf y
      have := (hAC k ι p I P hP n' n ψ hψ T A β α LT LA hT hA Ψ).2.1 _ _ _ (hc.2 _ hfy)
        (overAll_chain β α LT LA Ψ d (fun i => (hd i).2) presA I hP.nodup _ (hv hfy))
      exact congrFun this w
    rw [key]
    exact overAll_chain β α₀ LT LS _ _ hext presS I hP.nodup f (hv hf)

end GlobalTheory.FinPl.ExtAllPf

end
