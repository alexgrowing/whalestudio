import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChangeBaseVacuumHeisenbergCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasisStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeAtPlacesCongrLocalLatticesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacRebase

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem zero_placeModel {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 0 0 := by
  refine ⟨fun _ _ _ _ => ?_, fun _ _ _ _ => ?_, ?_⟩
  · funext w; simp [heisO]
  · funext w; simp [heisO]
  · simp

theorem local_step {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M N : GlobalTheory.FinPl.Lat S} {M' N' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hN : IsSelfDualC S N)
    (hM' : IsSelfDualC T M') (hN' : IsSelfDualC T N') (p : GlobalTheory.FinPl.Pl D)
    (hsp : ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε)
    (hu1 : ∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧
      incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p))
    (hu2 : ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p)) :
    ∃ c : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· = p) c ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f →
      GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T c f) ∧ (f ≠ 0 → comb ψ S T c f ≠ 0) := by
  obtain ⟨e, ε, he, hε, hs⟩ := hsp
  obtain ⟨q, -, hq⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D p e ε he hε hs
  have hU : q.UnitAA := by
    unfold GlobalTheory.FinPl.SplitPt.UnitAA
    rw [hq]
    exact ⟨hu1, hu2⟩
  rw [← hq]
  obtain ⟨glS, hS1, hS2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D _ q S (Fin S.rank) 1 1 (Matrix.mul_one 1) (Matrix.mul_one 1)
  obtain ⟨glT, hT1, hT2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D _ q T (Fin T.rank) 1 1 (Matrix.mul_one 1) (Matrix.mul_one 1)
  let α : GlobalTheory.FinPl.Frame q S (Fin S.rank) := ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, glS, hS1, hS2⟩
  let β : GlobalTheory.FinPl.Frame q T (Fin T.rank) := ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, glT, hT1, hT2⟩
  obtain ⟨ΛS, hl1, hαN, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q S _ α N hN
  obtain ⟨ΛT, hl2, hβN, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q T _ β N' hN'
  obtain ⟨ΛSm, hl3, hαM, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q S _ α M hM
  obtain ⟨ΛTm, hl4, hβM, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q T _ β M' hM'
  haveI := hl1
  haveI := hl2
  haveI := hl3
  haveI := hl4
  have R := GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D _ q (Fin T.rank) (Fin S.rank) ψ hψ hU S T α β M N M' N' hM hM' hN hN'
  obtain ⟨c, hc, hov⟩ := R.2 (GlobalTheory.LatPair.latInd ΛS ΛT) (GlobalTheory.LatPair.latInd_mem_SB ΛS ΛT)
  refine ⟨c, hc, fun f hf => ?_⟩
  have hO := hov f hf
  have h1 := R.1 ΛS ΛT hαN hβN f _ hO
  refine ⟨h1.1, fun hf0 hg => hf0 ?_⟩
  obtain ⟨⟨Tm, hTm⟩, -⟩ := hO.2.2.2.2
  have hOf : GlobalTheory.FinPl.Over ψ α β M M' f (GlobalTheory.LatPair.latInd ΛSm ΛTm) f := by
    refine ⟨hM, hM', hf, GlobalTheory.LatPair.latInd_mem_SB _ _, ⟨Tm, hTm⟩, fun T' hT' => ?_⟩
    rw [GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd D _ q _ _ S T α β M M' hM hM' hU ΛSm ΛTm hαM hβM]
    have hv := hT'.vac
    rw [one_smul] at hv
    exact hv.symm
  have hN0 := h1.2 _ _ hOf
  rw [hg] at hN0
  have := hN0.2.2.2.2.2 0 (zero_placeModel ψ S T _ _)
  simpa using this

end GlobalTheory.VacRebase

namespace GlobalTheory.VacRebase

theorem idAt_mono' {D : D7} {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, P v → P' v) :
    GlobalTheory.FinPl.idAt D P ≤ GlobalTheory.FinPl.idAt D P' := by
  unfold GlobalTheory.FinPl.idAt
  exact inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hp => w.2 (h _ hp)⟩ le_rfl)

theorem foldr_vac_off {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (c : GlobalTheory.FinPl.Pl D → WO S T →₀ ℂ) (X : GlobalTheory.FinPl.Pl D → Prop) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) :
    ∀ l : List (GlobalTheory.FinPl.Pl D), (∀ p ∈ l, GlobalTheory.FinPl.CombAt (· = p) (c p)) → (∀ p ∈ l, ¬ X p) → ∀ f,
      GlobalTheory.FinPl.Vac ψ S T LS LT X f → GlobalTheory.FinPl.Vac ψ S T LS LT X (l.foldr (fun p g => comb ψ S T (c p) g) f) := by
  intro l
  induction l with
  | nil => intro _ _ f hf; exact hf
  | cons p l ih =>
    intro hc hX f hf
    rw [List.foldr_cons]
    have hd : ∀ x, x = p → ¬ X x := fun x hx => hx ▸ hX p List.mem_cons_self
    exact ((GlobalTheory.DisjComb.main D ψ hψ S T (· = p) X hd).2.1 (c p) (hc p List.mem_cons_self)).2 LS LT _
      (ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)) (fun x hx => hX x (List.mem_cons_of_mem _ hx)) f hf)

theorem foldr_vac_on {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M N : GlobalTheory.FinPl.Lat S} {M' N' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hN : IsSelfDualC S N)
    (hM' : IsSelfDualC T M') (hN' : IsSelfDualC T N') (c : GlobalTheory.FinPl.Pl D → WO S T →₀ ℂ) :
    ∀ l : List (GlobalTheory.FinPl.Pl D), l.Nodup → (∀ p ∈ l, GlobalTheory.FinPl.CombAt (· = p) (c p) ∧ ∀ f,
      GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f → GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T (c p) f) ∧
        (f ≠ 0 → comb ψ S T (c p) f ≠ 0)) → ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (· ∈ l) f →
      GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ l) (l.foldr (fun p g => comb ψ S T (c p) g) f) ∧
        (f ≠ 0 → l.foldr (fun p g => comb ψ S T (c p) g) f ≠ 0) := by
  intro l
  induction l with
  | nil =>
    intro _ _ f hf
    refine ⟨⟨hf.1, ?_⟩, fun h => h⟩
    rw [GlobalTheory.T.homLatticeAtPlaces_congr_localLattices D S T N M N' M' hN hM hN' hM' _ (fun x hx => absurd hx List.not_mem_nil)]
    exact hf.2
  | cons p l ih =>
    intro hnd hc f hf
    have hpl : p ∉ l := (List.nodup_cons.1 hnd).1
    have hd : ∀ x, x = p → ¬ x ∈ l := fun x hx => hx ▸ hpl
    have DC := GlobalTheory.DisjComb.main D ψ hψ S T (· = p) (· ∈ l) hd
    have hfun : (fun x => x ∈ p :: l) = fun x => x = p ∨ x ∈ l := by
      funext x; exact propext List.mem_cons
    rw [hfun] at hf ⊢
    have hf2 := (DC.2.2.2.2 M M' f hM hM').1 hf
    obtain ⟨ihv, ihn⟩ := ih (List.nodup_cons.1 hnd).2 (fun x hx => hc x (List.mem_cons_of_mem _ hx)) f hf2.2
    have hgp := foldr_vac_off hψ c (· = p) M M' l (fun x hx => (hc x (List.mem_cons_of_mem _ hx)).1)
      (fun x hx hxp => hpl (hxp ▸ hx)) f hf2.1
    obtain ⟨hcp, hloc⟩ := hc p List.mem_cons_self
    obtain ⟨hv1, hn1⟩ := hloc _ hgp
    rw [List.foldr_cons]
    refine ⟨(DC.2.2.2.2 N N' _ hN hN').2 ⟨hv1, (DC.2.1 (c p) hcp).2 N N' _ ihv⟩, fun h0 => hn1 (ihn h0)⟩

end GlobalTheory.VacRebase

theorem GlobalTheory.VacRebase.rebase_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)), IsSelfDualC S M → IsSelfDualC S N → IsSelfDualC T M' → IsSelfDualC T N' → (∀ p ∈ Q, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p)) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p))) → (∀ p, p ∉ Q → GlobalTheory.FinPl.latV S M (· = p) = GlobalTheory.FinPl.latV S N (· = p) ∧ GlobalTheory.FinPl.latV T M' (· = p) = GlobalTheory.FinPl.latV T N' (· = p)) → ∃ o : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· ∈ Q) o ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) f → GlobalTheory.FinPl.Vac ψ S T N N' (fun _ => True) (comb ψ S T o f) ∧ (f ≠ 0 → comb ψ S T o f ≠ 0) := by
  intro D ψ hψ S T M N M' N' Q hM hN hM' hN' hQ hoff
  have hc : ∀ p : GlobalTheory.FinPl.Pl D, ∃ c : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· = p) c ∧ (p ∈ Q → ∀ f,
      GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f → GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T c f) ∧
        (f ≠ 0 → comb ψ S T c f ≠ 0)) := by
    intro p
    by_cases hp : p ∈ Q
    · obtain ⟨h1, h2, h3⟩ := hQ p hp
      obtain ⟨c, hc1, hc2⟩ := GlobalTheory.VacRebase.local_step hψ hM hN hM' hN' p h1 h2 h3
      exact ⟨c, hc1, fun _ => hc2⟩
    · exact ⟨0, fun u hu => by simp at hu, fun h => absurd h hp⟩
  choose c hc1 hc2 using hc
  let l := Q.toList
  have hmem : ∀ p, p ∈ l ↔ p ∈ Q := fun p => Finset.mem_toList
  refine ⟨convList ψ S T (l.map c), ?_, fun f hf => ?_⟩
  · refine support_convList (p := GlobalTheory.FinPl.MxAt (· ∈ Q)) (fun i j => Ideal.zero_mem _)
      (fun x y hx hy i j => by rw [Matrix.add_apply]; exact Ideal.add_mem _ (hx i j) (hy i j)) ?_
    intro c' hc' x hx i j
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc'
    exact GlobalTheory.VacRebase.idAt_mono' (fun v hv => hv ▸ (hmem p).1 hp) (hc1 p x hx i j)
  rw [comb_convList]
  have DC := GlobalTheory.DisjComb.main D ψ hψ S T (· ∈ l) (· ∉ l) (fun x h1 h2 => h2 h1)
  have hfun : (fun x => x ∈ l ∨ x ∉ l) = fun _ => True := by
    funext x; exact propext ⟨fun _ => trivial, fun _ => em _⟩
  have hf' : GlobalTheory.FinPl.Vac ψ S T M M' (fun x => x ∈ l ∨ x ∉ l) f := by rw [hfun]; exact hf
  obtain ⟨hin, hout⟩ := (DC.2.2.2.2 M M' f hM hM').1 hf'
  obtain ⟨v1, n1⟩ := GlobalTheory.VacRebase.foldr_vac_on hψ hM hN hM' hN' c l (Finset.nodup_toList Q)
    (fun p hp => ⟨hc1 p, hc2 p ((hmem p).1 hp)⟩) f hin
  have hout' : GlobalTheory.FinPl.Vac ψ S T N N' (· ∉ l) f := by
    refine ⟨hout.1, ?_⟩
    rw [GlobalTheory.T.homLatticeAtPlaces_congr_localLattices D S T N M N' M' hN hM hN' hM' _ (fun x hx => by
      obtain ⟨a, b⟩ := hoff x (fun h => hx ((hmem x).2 h)); exact ⟨a.symm, b.symm⟩)]
    exact hout.2
  have v2 := GlobalTheory.VacRebase.foldr_vac_off hψ c (· ∉ l) N N' l (fun p _ => hc1 p) (fun p hp h => h hp) f hout'
  refine ⟨?_, n1⟩
  rw [← hfun]
  exact (DC.2.2.2.2 N N' _ hN hN').2 ⟨v1, v2⟩
