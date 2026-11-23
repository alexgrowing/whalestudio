import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumExistsAtLevelPrimePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChangeBaseVacuumHeisenbergCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiCombEqLOpROp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaConstMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOConstMul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastTAllPf

variable {D : D7}

theorem vac_sum {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {κ : Type*}
    (s : Finset κ) (a : κ → ℂ) (F : κ → WO S T → ℂ) (hF : ∀ i ∈ s, Vac ψ S T LS LT P (F i)) :
    Vac ψ S T LS LT P (fun w => ∑ i ∈ s, a i * F i w) := by
  refine ⟨GlobalTheory.SeeSawFold.theta_sum' s _ fun i hi => GlobalTheory.SeeSawFold.theta_const_mul' (a i) (hF i hi).1, ?_, ?_⟩
  · intro u hu
    funext w
    simp only [heisO, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h := congrFun ((hF i hi).2.1 u hu) w
    simp only [heisO] at h
    rw [mul_left_comm, h]
  · intro e he u hu hh
    funext w
    simp only [heisO, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h := congrFun ((hF i hi).2.2 e he u hu hh) w
    simp only [heisO] at h
    rw [mul_left_comm, h]

theorem vac_zero {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} :
    Vac ψ S T LS LT P 0 := by
  have h := vac_sum (ψ := ψ) (LS := LS) (LT := LT) (P := P) (∅ : Finset Unit) (fun _ => 0) (fun _ => 0) (by simp)
  convert h using 1
  funext w
  simp

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P Q : Pl D → Prop}
    (h : ∀ x, Q x → P x) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT Q f := by
  have hmono : latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (h v hq), rest⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hmono hu), fun e he u hu hh => hf.2.2 e he u (hmono hu) hh⟩

theorem biVac_biComb_off {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {A S A' : HSp D} {LA : Lat A}
    {LS : Lat S} {LA' : Lat A'} {Q P' : Pl D → Prop} (hd : ∀ x, Q x → ¬ P' x) {d : WO A S →₀ ℂ} {d' : WO S A' →₀ ℂ}
    (hd1 : CombAt Q d) (hd2 : CombAt Q d') {Y : WO A S → WO S A' → ℂ} (hY : BiVacAt ψ LA LS LA' P' Y) :
    BiVacAt ψ LA LS LA' P' (biComb ψ A S A' d d' Y) := by
  have M1 := GlobalTheory.DisjComb.main D ψ hψ A S Q P' hd
  have M2 := GlobalTheory.DisjComb.main D ψ hψ S A' Q P' hd
  constructor
  · intro v
    have hG : Vac ψ A S LA LS P' (fun u' => comb ψ S A' d' (Y u') v) := by
      have e : (fun u' => comb ψ S A' d' (Y u') v) =
          fun u' => ∑ y ∈ d'.support, (d' y * ψ (symplOH S A' v y)) * Y u' (v + y) := by
        funext u'
        simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [e]
      exact vac_sum d'.support (fun y => d' y * ψ (symplOH S A' v y)) (fun y u'' => Y u'' (v + y))
        fun y _ => hY.1 (v + y)
    exact (M1.2.1 d hd1).2 LA LS _ hG
  · intro u
    have e : biComb ψ A S A' d d' Y u =
        fun v => ∑ x ∈ d.support, (d x * ψ (symplOH A S u x)) * comb ψ S A' d' (Y (u + x)) v := by
      funext v
      simp only [biComb, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e]
    exact vac_sum d.support (fun x => d x * ψ (symplOH A S u x)) (fun x => comb ψ S A' d' (Y (u + x)))
      fun x _ => (M2.2.1 d' hd2).2 LS LA' _ (hY.2 (u + x))

theorem vac_of_list {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T}
    (hLS : IsSelfDualC S LS) (hLT : IsSelfDualC T LT) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∀ (l : List (Pl D)), l.Nodup → ∀ (P : Pl D → Prop), (∀ x, P x ↔ x ∈ l) →
      (∀ x ∈ l, Vac ψ S T LS LT (· = x) f) → Vac ψ S T LS LT P f := by
  intro l
  induction l with
  | nil =>
    intro _ P hP _
    have hb : latO S T (LS : Set _) (LT : Set _) P = ⊥ := by
      rw [latO, AddSubgroup.closure_eq_bot_iff]
      rintro w ⟨α, -, hα, a, -, s, -, t, -, rfl⟩
      have h0 : α = 0 := RestrictedProduct.ext _ _ fun v => hα v fun h => by simpa using (hP v).1 h
      subst h0
      ext i j
      simp only [pairA, Prod.mk_zero_zero, Matrix.of_apply, Matrix.zero_apply]
      exact TensorProduct.zero_tmul _ _
    have h0 : ∀ w : WO S T, symplOH S T w 0 = 0 := fun w => by simp [symplOH, symplO, hO]
    refine ⟨hf, fun u hu => ?_, fun e _ u hu _ => ?_⟩
    · rw [hb, AddSubgroup.mem_bot] at hu
      subst hu
      funext w
      simp [heisO, h0]
    · rw [hb, AddSubgroup.mem_bot] at hu
      subst hu
      funext w
      simp [heisO, h0]
  | cons x l ih =>
    intro hnd P hP hv
    obtain ⟨hx, hl⟩ := List.nodup_cons.1 hnd
    have e : P = fun y => y = x ∨ y ∈ l := funext fun y => propext ((hP y).trans List.mem_cons)
    subst e
    have M := (GlobalTheory.DisjComb.main D ψ hψ S T (· = x) (· ∈ l) (fun y hy hy' => hx (hy ▸ hy'))).2.2.2.2 LS LT f hLS hLT
    exact M.2 ⟨hv x List.mem_cons_self, ih hl (· ∈ l) (fun _ => Iff.rfl) fun y hy => hv y (List.mem_cons_of_mem _ hy)⟩

open GlobalTheory.SeeSawFold in

theorem biComb_eq_foldr_vac {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {LA : Lat A} {LS : Lat S} {LA' : Lat A'}
    {P : Pl D → Prop} (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ)))
    (hc : ∀ f, Vac ψ A S LA LS P f → comb ψ A S c f = l.foldr (fun p f' => comb ψ A S p.1 f') f)
    (hc' : ∀ f, Vac ψ S A' LS LA' P f → comb ψ S A' c' f = l.foldr (fun p f' => comb ψ S A' p.2 f') f)
    (Y : WO A S → WO S A' → ℂ) (hY : BiVacAt ψ LA LS LA' P Y) :
    biComb ψ A S A' c c' Y = l.foldr (fun p C => biComb ψ A S A' p.1 p.2 C) Y := by
  have hR : opR ψ A S A' c' Y = l.foldr (fun p C => opR ψ A S A' p.2 C) Y := by
    funext u v
    show comb ψ S A' c' (Y u) v = _
    rw [hc' _ (hY.2 u), foldR_apply]
  have vac_opR : ∀ (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ), (∀ v, Vac ψ A S LA LS P (fun u => C u v)) →
      ∀ v, Vac ψ A S LA LS P (fun u => opR ψ A S A' b C u v) := by
    intro b C hC v
    have e : (fun u => opR ψ A S A' b C u v) = fun u => ∑ y ∈ b.support, (b y * ψ (symplOH S A' v y)) * C u (v + y) := by
      funext u
      simp only [opR, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [e]
    exact vac_sum b.support (fun y => b y * ψ (symplOH S A' v y)) (fun y u => C u (v + y)) fun y _ => hC (v + y)
  have vac_foldR : ∀ (l' : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) v,
      Vac ψ A S LA LS P (fun u => l'.foldr (fun p C => opR ψ A S A' p.2 C) Y u v) := by
    intro l'
    induction l' with
    | nil => exact fun v => hY.1 v
    | cons p l' ih => exact vac_opR p.2 _ ih
  rw [← foldL_foldR, biComb_eq, hR]
  funext u v
  rw [foldL_apply]
  exact congrFun (hc _ (vac_foldR l v)) u

section Lists

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S}
  {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ}

theorem overAll_cons' {i : ι} {J : List ι} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ (i :: J) f f' ↔
      ∃ g, OverAll ψ α β LS LT Ψ J f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' := Iff.rfl

theorem overAll_steps : ∀ (J : List ι) (f f' : WO S T → ℂ), OverAll ψ α β LS LT Ψ J f f' →
    ∀ j ∈ J, ∃ g g', Over ψ (α j) (β j) LS LT g (Ψ j) g' := by
  intro J
  induction J with
  | nil => intro _ _ _ j hj; simp at hj
  | cons i J ih =>
    intro f f' h j hj
    obtain ⟨g, hg, h⟩ := overAll_cons'.1 h
    rcases List.mem_cons.1 hj with rfl | hj
    · exact ⟨g, f', h⟩
    · exact ih f g hg j hj

theorem vac_foldr_off (hψ : IsStdChar D ψ (-1)) {x : Pl D} {κ : Type} (r : κ → WO S T →₀ ℂ) (P' : κ → Pl D → Prop)
    (l : List κ) (hr : ∀ j ∈ l, CombAt (P' j) (r j)) (hd : ∀ j ∈ l, ¬ P' j x) {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (· = x) f) : Vac ψ S T LS LT (· = x) (l.foldr (fun j f' => comb ψ S T (r j) f') f) := by
  induction l with
  | nil => exact hf
  | cons j l ih =>
    have M := GlobalTheory.DisjComb.main D ψ hψ S T (P' j) (· = x) (fun y hy hy' => hd j List.mem_cons_self (hy' ▸ hy))
    exact (M.2.1 (r j) (hr j List.mem_cons_self)).2 LS LT _
      (ih (fun j' hj' => hr j' (List.mem_cons_of_mem _ hj')) fun j' hj' => hd j' (List.mem_cons_of_mem _ hj'))

theorem overAll_foldr (hψ : IsStdChar D ψ (-1)) (hinj : Function.Injective fun i => (p i).v) (r : ι → WO S T →₀ ℂ)
    (hr1 : ∀ i, CombAt (· = (p i).v) (r i))
    (hr2 : ∀ i f₀, Vac ψ S T LS LT (· = (p i).v) f₀ → Over ψ (α i) (β i) LS LT f₀ (Ψ i) (comb ψ S T (r i) f₀)) :
    ∀ (l : List ι), l.Nodup → ∀ f, (∀ i ∈ l, Vac ψ S T LS LT (· = (p i).v) f) →
      OverAll ψ α β LS LT Ψ l f (l.foldr (fun i f' => comb ψ S T (r i) f') f) := by
  intro l
  induction l with
  | nil => intro _ f _; exact rfl
  | cons i l ih =>
    intro hl f hf
    obtain ⟨hi, hl'⟩ := List.nodup_cons.1 hl
    refine overAll_cons'.2 ⟨_, ih hl' f fun j hj => hf j (List.mem_cons_of_mem _ hj), hr2 i _ ?_⟩
    exact vac_foldr_off hψ r (fun j => (· = (p j).v)) l (fun j _ => hr1 j)
      (fun j hj h => hi (by rw [hinj h]; exact hj)) (hf i List.mem_cons_self)

variable {I : List ι} {P : Pl D → Prop}

theorem comb_eq_foldr (hP : Places p I P) (hψ : IsStdChar D ψ (-1)) (hLS : IsSelfDualC S LS) (hLT : IsSelfDualC T LT)
    {c : WO S T →₀ ℂ} (hc : Reps ψ α β LS LT Ψ I P c) (r : ι → WO S T →₀ ℂ) (hr1 : ∀ i, CombAt (· = (p i).v) (r i))
    (hr2 : ∀ i f₀, Vac ψ S T LS LT (· = (p i).v) f₀ → Over ψ (α i) (β i) LS LT f₀ (Ψ i) (comb ψ S T (r i) f₀)) :
    ∀ f, Vac ψ S T LS LT P f → comb ψ S T c f = I.foldr (fun i f' => comb ψ S T (r i) f') f := by
  intro f hf
  have hAC := GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι p I P hP n n' ψ hψ S T α β LS LT hLS hLT Ψ
  exact hAC.2.1 f _ _ (hc.2 f hf) (overAll_foldr hψ hP.inj r hr1 hr2 I hP.nodup f fun i _ =>
    vac_mono (fun x hx => (hP.mem x).2 ⟨i, hx⟩) hf)

theorem over_of_overAll (hP : Places p I P) (hψ : IsStdChar D ψ (-1)) {f Ξ : WO S T → ℂ} (hf : Vac ψ S T LS LT P f)
    (hΞ : OverAll ψ α β LS LT Ψ I f Ξ) (i : ι) : ∃ g, Over ψ (α i) (β i) LS LT g (Ψ i) Ξ := by
  classical
  have hstep := overAll_steps I f Ξ hΞ
  obtain ⟨g0, g0', h0⟩ := hstep i (hP.all i)
  have hLS : IsSelfDualC S LS := h0.1
  have hLT : IsSelfDualC T LT := h0.2.1
  have hSB : ∀ j, Ψ j ∈ SB (Matrix n n' k) := fun j => by
    obtain ⟨g, g', h⟩ := hstep j (hP.all j)
    exact h.2.2.2.1
  choose r hr1 hr2 using fun j => (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p j) n n' ψ hψ (hP.unit j) S T (α j) (β j) LS LS LT LT hLS hLT hLS hLT).2
    (Ψ j) (hSB j)
  have hAC := GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D k ι p I P hP n n' ψ hψ S T α β LS LT hLS hLT Ψ
  have hE : Ξ = I.foldr (fun j f' => comb ψ S T (r j) f') f := hAC.2.1 f _ _ hΞ
    (overAll_foldr hψ hP.inj r hr1 hr2 I hP.nodup f fun j _ => vac_mono (fun x hx => (hP.mem x).2 ⟨j, hx⟩) hf)
  have hcomm : ∀ x ∈ I, ∀ y ∈ I, ∀ z : WO S T → ℂ,
      comb ψ S T (r y) (comb ψ S T (r x) z) = comb ψ S T (r x) (comb ψ S T (r y) z) := by
    intro x _ y _ z
    by_cases hxy : x = y
    · subst hxy; rfl
    · exact (GlobalTheory.DisjComb.main D ψ hψ S T (· = (p y).v) (· = (p x).v)
        (fun w h1 h2 => hxy (hP.inj (h2.symm.trans h1)))).1 (r y) (r x) (hr1 y) (hr1 x) z
  have hperm : I.Perm (i :: I.erase i) := List.perm_cons_erase (hP.all i)
  rw [hperm.foldr_eq' hcomm f, List.foldr_cons] at hE
  refine ⟨_, hE ▸ hr2 i _ ?_⟩
  refine vac_foldr_off hψ r (fun j => (· = (p j).v)) (I.erase i) (fun j _ => hr1 j) (fun j hj h => ?_)
    (vac_mono (fun x hx => (hP.mem x).2 ⟨i, hx⟩) hf)
  exact ((hP.nodup.mem_erase_iff).1 hj).1 (hP.inj h).symm

end Lists

end GlobalTheory.LastTAllPf

namespace GlobalTheory.LastTAllPf

set_option maxHeartbeats 1000000 in

theorem main : ∀ D : D7, GlobalTheory.FinPl.LastTAll D := by
  intro D k _ _ _ _ ι p I P hP q ψ hψ χ hχ hchar n n' n'' _ _ _ _ _ _ V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hlam
    hunit hτ
  have hloc := fun i => GlobalTheory.T.lastSeeSawDatum_exists_at_levelPrimePlace D k (p i) q ψ hψ (hP.unit i) (χ i) (hχ i) (hchar i) n n' n'' V₀ A L S X T L'' o o''
    ζ ζ₀ hζ hζ₀ τ lam hlam (hunit i) hτ
  choose ε hε using hloc
  refine ⟨ε, ?_⟩
  intro α α₀ β γ γ₀ hfr Q Λ _ Ψ LA LS LT LX L₁ hLA hLS hLT hLX hL₁ hlat c c' hc hc'
  have hdisj : ∀ i j, i ≠ j → ∀ x, x = (p i).v → ¬ x = (p j).v := fun i j h x h1 h2 => h (hP.inj (h1.symm.trans h2))
  have hSB : ∀ i, Ψ i ∈ SB (Matrix n n' k) := fun i => by
    obtain ⟨g, g', h⟩ := overAll_steps I 0 _ (hc.2 0 vac_zero) i (hP.all i)
    exact h.2.2.2.1
  have hSB' : ∀ i, phiOne (ε i • Q i) (lastPair q (Λ i)) ∈ SB _ := fun i => by
    obtain ⟨g, g', h⟩ := overAll_steps I 0 _ (hc'.2 0 vac_zero) i (hP.all i)
    exact h.2.2.2.1
  choose r hr1 hr2 using fun i => (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) n n' ψ hψ (hP.unit i) A S (α i) (β i) LA LA LS LS hLA hLS hLA
    hLS).2 (Ψ i) (hSB i)
  choose r' hr1' hr2' using fun i => (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) (n'' ⊕ Fin 1) n ψ hψ (hP.unit i) S X (β i) (γ₀ i) LS LS LX LX
    hLS hLX hLS hLX).2 _ (hSB' i)
  choose e₁ e₂ he₁ he₂ hE using fun i => hε i (α i) (α₀ i) (β i) (γ i) (γ₀ i) (hfr i).1 (hfr i).2 (Q i) (Λ i) (Ψ i) LA LS
    LT LX hLA hLS hLT hLX (hlat i).1 (hlat i).2 (r i) (r' i) (hr1 i) (hr1' i) (hr2 i) (hr2' i)
  have hbc : ∀ i j, i ≠ j → ∀ (a b : WO A S →₀ ℂ) (a' b' : WO S X →₀ ℂ), CombAt (· = (p i).v) a →
      CombAt (· = (p i).v) a' → CombAt (· = (p j).v) b → CombAt (· = (p j).v) b' → ∀ C,
      biComb ψ A S X a a' (biComb ψ A S X b b' C) = biComb ψ A S X b b' (biComb ψ A S X a a' C) :=
    fun i j h a b a' b' ha ha' hb hb' C => GlobalTheory.ProdLocInv.biComb_comm ψ A S X a b a' b'
      ((GlobalTheory.DisjComb.main D ψ hψ A S _ _ (hdisj i j h)).1 a b ha hb)
      ((GlobalTheory.DisjComb.main D ψ hψ S X _ _ (hdisj i j h)).1 a' b' ha' hb') C
  let Vl : ι → Set (WO A S → WO S X → ℂ) := fun i => {C | BiVacAt ψ LA LS LX (· = (p i).v) C}
  let Cl : ι → Set (WO A S → WO S X → ℂ) := fun i => {C | biComb ψ A S X (e₁ i) (e₂ i) C ∈ Vl i ∧
    C = biComb ψ A S X (r i) (r' i) (biComb ψ A S X (e₁ i) (e₂ i) C)}
  let Dt : ι → Matrix n (n' ⊕ Fin 1) k → ℂ := fun i => tensCol (Ψ i) (charInd (resChar (χ i) (hχ i) q) (Q i))
  let Tp := {t : (WO V₀ S → ℂ) × (WO V₀ S → ℂ) × (WO S T → ℂ) // Vac ψ V₀ S L₁ LS P t.1 ∧
    OverAll ψ α₀ β L₁ LS Dt I t.1 t.2.1 ∧ Vac ψ S T LS LT P t.2.2}
  obtain ⟨e, e', hes, hes', hmain⟩ := GlobalTheory.ProdLocInv.main D ψ A S X ι Tp I
    (fun t => lastBi o o'' τ t.1.2.1 t.1.2.2) e₁ r e₂ r' Cl Vl hP.nodup
    (fun i _ i' _ hne => ⟨fun x hx y hy => GlobalTheory.DisjComb.symplO_disj (hdisj i i' hne) (hx.elim (he₁ i x) (hr1 i x))
      (he₁ i' y hy), fun x hx y hy => GlobalTheory.DisjComb.symplO_disj (hdisj i i' hne) (hx.elim (he₂ i x) (hr1' i x))
      (he₂ i' y hy)⟩)
    (fun i _ t => by
      obtain ⟨g, hg⟩ := over_of_overAll hP hψ t.2.1 t.2.2.1 i
      exact hE i L₁ LS g _ _ hg (vac_mono (fun x hx => (hP.mem x).2 ⟨i, hx⟩) t.2.2.2))
    (fun i _ C hC => hC)
    (fun i _ i' _ hne C hC => by
      refine ⟨?_, ?_⟩
      · show BiVacAt ψ LA LS LX (· = (p i).v) (biComb ψ A S X (e₁ i) (e₂ i) (biComb ψ A S X (e₁ i') (e₂ i') C))
        rw [hbc i i' hne _ _ _ _ (he₁ i) (he₂ i) (he₁ i') (he₂ i')]
        exact biVac_biComb_off hψ (hdisj i' i fun h => hne h.symm) (he₁ i') (he₂ i') hC.1
      · show biComb ψ A S X (e₁ i') (e₂ i') C = biComb ψ A S X (r i) (r' i)
          (biComb ψ A S X (e₁ i) (e₂ i) (biComb ψ A S X (e₁ i') (e₂ i') C))
        rw [hbc i i' hne _ _ _ _ (he₁ i) (he₂ i) (he₁ i') (he₂ i'),
          hbc i i' hne _ _ _ _ (hr1 i) (hr1' i) (he₁ i') (he₂ i'), ← hC.2])
  have hcl : ∀ {S' T' : HSp D} (E : ι → WO S' T' →₀ ℂ), (∀ i, CombAt (· = (p i).v) (E i)) → ∀ w,
      w ∈ AddSubmonoid.closure (⋃ i ∈ I, ((E i).support : Set (WO S' T'))) → MxAt P w := by
    intro S' T' E hE' w hw
    induction hw using AddSubmonoid.closure_induction with
    | mem x hx =>
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, -, hx⟩ := hx
      exact GlobalTheory.DisjComb.mxAt_mono (fun y hy => (hP.mem y).2 ⟨i, hy⟩) (hE' i x hx)
    | zero => intro a b; simp
    | add x y _ _ hx hy => intro a b; exact Ideal.add_mem _ (hx a b) (hy a b)
  refine ⟨e, e', fun w hw => hcl e₁ he₁ w (hes w hw), fun w hw => hcl e₂ he₂ w (hes' w hw),
    fun f₁ Ξ Φ₂ hf₁ hΞ hΦ => ?_⟩
  have hY := hmain ⟨(f₁, Ξ, Φ₂), hf₁, hΞ, hΦ⟩
  have hth : (∀ v, IsThetaFunO ψ A S (fun u => biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂) u v)) ∧
      ∀ u, IsThetaFunO ψ S X (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂) u) := by
    by_cases hne : Nonempty ι
    · obtain ⟨i⟩ := hne
      have hv := hY.1 i (hP.all i)
      exact ⟨fun v => (hv.1 v).1, fun u => (hv.2 u).1⟩
    · have hl : I = [] := List.eq_nil_iff_forall_not_mem.2 fun i _ => hne ⟨i⟩
      have hXY := hY.2
      simp only [hl, List.foldr_nil] at hXY
      rw [← hXY]
      have hΞ' : Ξ = f₁ := by
        have h := hΞ
        rw [hl] at h
        exact h
      subst hΞ'
      have hΞθ := hf₁.1
      have hΦθ := hΦ.1
      exact ⟨fun v => GlobalTheory.LastSeeSaw.isThetaFunO_const_mul (Φ₂ ((o''.resT S v).1))
          (GlobalTheory.BoxSlice.isThetaFunO_slice_left o hΞθ (kap τ S ((o''.resT S v).2))),
        fun w => OrthDec.isThetaFunO_boxT o'' hΦθ
          (GlobalTheory.LastSeeSaw.isThetaFunO_kap τ hτ S (GlobalTheory.BoxSlice.isThetaFunO_slice_right o hΞθ w))⟩
  have hPl : ∀ x, P x ↔ x ∈ I.map fun i => (p i).v := fun x => (hP.mem x).trans
    ⟨fun ⟨i, h⟩ => List.mem_map.2 ⟨i, hP.all i, h.symm⟩, fun h => by
      obtain ⟨i, -, h⟩ := List.mem_map.1 h
      exact ⟨i, h.symm⟩⟩
  have hnd : (I.map fun i => (p i).v).Nodup := hP.nodup.map hP.inj
  have hBV : BiVacAt ψ LA LS LX P (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) := by
    refine ⟨fun v => ?_, fun u => ?_⟩
    · refine vac_of_list hψ hLA hLS (hth.1 v) _ hnd P hPl fun x hx => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact (hY.1 i (hP.all i)).1 v
    · refine vac_of_list hψ hLS hLX (hth.2 u) _ hnd P hPl fun x hx => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact (hY.1 i (hP.all i)).2 u
  refine ⟨hBV, ?_⟩
  have hF := biComb_eq_foldr_vac (P := P) c c' (I.map fun i => (r i, r' i))
    (fun f hf => by rw [List.foldr_map]; exact comb_eq_foldr hP hψ hLA hLS hc r hr1 hr2 f hf)
    (fun f hf => by rw [List.foldr_map]; exact comb_eq_foldr hP hψ hLS hLX hc' r' hr1' hr2' f hf) _ hBV
  rw [hF, List.foldr_map]
  exact hY.2

end GlobalTheory.LastTAllPf
