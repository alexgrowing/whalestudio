import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfTwistConjugatePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMapGLSpl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThUContinuousInvol

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA GlobalTheory.CompanionTheory.ActTr
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.FactorAction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def fHm (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Hf E a b →* H E a b :=
  (finGL E a).prodMap (finGL E b)

def epsS {S : Set (Pl E)} (a b : ℕ) : ∀ i : Slot S, GLw a i.pl × GLw b i.pl →* Hf E a b
  | .inl w => (locGL E a w.1).prodMap (locGL E b w.1)
  | .inr w => ((thF E a).comp (locGL E a w.1)).prodMap ((thF E b).comp (locGL E b w.1))

def selS {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) : ∀ i : Slot S, LF a b i.pl
  | .inl w => φ₁ w.1
  | .inr w => φ₂ w.1

theorem continuous_thF (n : ℕ) : Continuous (thF E n) :=
  GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)

theorem continuous_loc (n : ℕ) (w : Pl E) : Continuous (locGL E n w) :=
  GlobalTheory.EulerTw.continuous_locGL_spl E n w

theorem continuous_epsS {S : Set (Pl E)} (i : Slot S) : Continuous (epsS a b i) := by
  rcases i with w | w
  · exact (continuous_loc a w.1).prodMap (continuous_loc b w.1)
  · exact ((continuous_thF a).comp (continuous_loc a w.1)).prodMap ((continuous_thF b).comp (continuous_loc b w.1))

theorem embT_prod (w : Pl E) : (embT a w).prodMap (embT b w) =
    (fHm E a b).comp (((thF E a).comp (locGL E a w)).prodMap ((thF E b).comp (locGL E b w))) := by
  refine MonoidHom.ext fun m => Prod.ext ?_ ?_
  · exact GlobalTheory.ThetaPull.thetaA_finGL _
  · exact GlobalTheory.ThetaPull.thetaA_finGL _

theorem actS_eq {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (i : Slot S) (G : H E a b → ℂ) :
    actS φ₁ φ₂ i G = act ((fHm E a b).comp (epsS a b i)) (K2 a b i.pl) (selS φ₁ φ₂ i) G := by
  rcases i with w | w
  · rfl
  · show act ((embT a w.1).prodMap (embT b w.1)) (K2 a b w.1) (φ₂ w.1) G = _
    rw [embT_prod]
    rfl

theorem pair_maximal_compact_open_compact (w : Pl E) : IsCompact (K2 a b w : Set (GLw a w × GLw b w)) ∧ IsOpen (K2 a b w : Set (GLw a w × GLw b w)) :=
  ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2,
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1⟩

theorem hecke_of_test {φ : ∀ w : Pl E, LF a b w} (h : IsTestP φ) (w : Pl E) :
    ∃ A : Subgroup (GLw a w × GLw b w), IsOpen (A : Set (GLw a w × GLw b w)) ∧ IsHecke A (φ w) := by
  obtain ⟨K₁, K₂, h₁, h₂, h₃⟩ := h
  exact ⟨(K₁ w).prod (K₂ w), (h₁.1 w).1.prod (h₂.1 w).1, h₃.1 w⟩

theorem hecke_sel {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) (i : Slot S) :
    ∃ A : Subgroup (GLw a i.pl × GLw b i.pl), IsOpen (A : Set (GLw a i.pl × GLw b i.pl)) ∧ IsHecke A (selS φ₁ φ₂ i) := by
  rcases i with w | w
  · exact hecke_of_test h₁ w.1
  · exact hecke_of_test h₂ w.1

theorem locGL_comm {n : ℕ} {w w' : Pl E} (h : w ≠ w') (g : GLw n w) (g' : GLw n w') :
    locGL E n w g * locGL E n w' g' = locGL E n w' g' * locGL E n w g := by
  have key : ∀ v, GeneralLinearGroup.map (pLoc E v) (locGL E n w g * locGL E n w' g') =
      GeneralLinearGroup.map (pLoc E v) (locGL E n w' g' * locGL E n w g) := fun v => by
    rw [map_mul, map_mul]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL_of_ne h g', mul_one, one_mul]
    · rw [pLoc_locGL_of_ne hv g, mul_one, one_mul]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin n) (v.adicCompletion E) => u.val i j) (key v)

theorem thF_loc {n : ℕ} {w u : Pl E} (h : w = GlobalTheory.ThetaSatake.cw u) (g : GLw n w) :
    ∃ g₀ : GLw n u, thF E n (locGL E n w g) = locGL E n u g₀ := by
  subst h
  exact ⟨_, GlobalTheory.ThetaSatake.theta_locGL u g⟩

theorem cw_cw (w : Pl E) : w = GlobalTheory.ThetaSatake.cw (GlobalTheory.ThetaSatake.cw w) :=
  (GlobalTheory.ThetaPull.conjSrc_conjSrc w).symm

theorem comm_WT {n : ℕ} {w w' : Pl E} (h : w ≠ GlobalTheory.ThetaSatake.cw w') (g : GLw n w) (g' : GLw n w') :
    locGL E n w g * thF E n (locGL E n w' g') = thF E n (locGL E n w' g') * locGL E n w g := by
  obtain ⟨g₀, e⟩ := thF_loc (cw_cw w') g'
  rw [e]
  exact locGL_comm h g g₀

theorem comm_TT {n : ℕ} {w w' : Pl E} (h : GlobalTheory.ThetaSatake.cw w ≠ GlobalTheory.ThetaSatake.cw w') (g : GLw n w) (g' : GLw n w') :
    thF E n (locGL E n w g) * thF E n (locGL E n w' g') = thF E n (locGL E n w' g') * thF E n (locGL E n w g) := by
  obtain ⟨g₀, e⟩ := thF_loc (cw_cw w) g
  obtain ⟨g₁, e'⟩ := thF_loc (cw_cw w') g'
  rw [e, e']
  exact locGL_comm h g₀ g₁

theorem epsS_comm {S : Set (Pl E)} (hS : IsSection S) {i j : Slot S} (hij : i ≠ j)
    (x : GLw a i.pl × GLw b i.pl) (y : GLw a j.pl × GLw b j.pl) :
    epsS a b i x * epsS a b j y = epsS a b j y * epsS a b i x := by
  rcases i with w | w <;> rcases j with w' | w'
  · have hne : w.1 ≠ w'.1 := fun e => hij (congrArg Sum.inl (Subtype.ext e))
    exact Prod.ext (locGL_comm hne _ _) (locGL_comm hne _ _)
  · have hne : w.1 ≠ GlobalTheory.ThetaSatake.cw w'.1 := fun e =>
      GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w'.2.1 w'.2.2 (show GlobalTheory.ThetaSatake.cw w'.1 ∈ S from e ▸ w.2)
    exact Prod.ext (comm_WT hne _ _) (comm_WT hne _ _)
  · have hne : w'.1 ≠ GlobalTheory.ThetaSatake.cw w.1 := fun e =>
      GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w.2.1 w.2.2 (show GlobalTheory.ThetaSatake.cw w.1 ∈ S from e ▸ w'.2)
    exact Prod.ext (comm_WT hne _ _).symm (comm_WT hne _ _).symm
  · have hne : GlobalTheory.ThetaSatake.cw w.1 ≠ GlobalTheory.ThetaSatake.cw w'.1 := fun e =>
      hij (congrArg Sum.inr (Subtype.ext ((cw_cw w.1).trans ((congrArg GlobalTheory.ThetaSatake.cw e).trans (cw_cw w'.1).symm))))
    exact Prod.ext (comm_TT hne _ _) (comm_TT hne _ _)

theorem selS_conv {S : Set (Pl E)} (φ₁ φ₂ ψ₁ ψ₂ : ∀ w : Pl E, LF a b w) (i : Slot S) :
    selS (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₁ w) (ψ₁ w)) (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₂ w) (ψ₂ w)) i =
      fun m => hint (K2 a b i.pl) fun m' => selS φ₁ φ₂ i m' * selS ψ₁ ψ₂ i (m'⁻¹ * m) := by
  rcases i with w | w <;> rfl

theorem actAlg : ActAlg := by
  intro E _ _ _ a b S hS φ₁ φ₂ ψ₁ ψ₂ hφ₁ hφ₂ hψ₁ hψ₂ G G' hG hG' i j
  have hGl : Lev (fHm E a b) G := hG
  have hGl' : Lev (fHm E a b) G' := hG'
  obtain ⟨hK, hKo⟩ := pair_maximal_compact_open_compact (a := a) (b := b) i.pl
  obtain ⟨hKj, hKoj⟩ := pair_maximal_compact_open_compact (a := a) (b := b) j.pl
  obtain ⟨A, hA, hf⟩ := hecke_sel (S := S) hφ₁ hφ₂ i
  obtain ⟨B, hB, hg⟩ := hecke_sel (S := S) hψ₁ hψ₂ i
  obtain ⟨B', hB', hg'⟩ := hecke_sel (S := S) hψ₁ hψ₂ j
  have ci := continuous_epsS (a := a) (b := b) i
  have cj := continuous_epsS (a := a) (b := b) j
  refine ⟨?_, fun c => ?_, fun hij => ?_, ?_⟩
  · rw [actS_eq]
    exact act_lev ci hK hKo hA hf hGl
  · simp only [actS_eq]
    exact act_add hK hKo hA hf (sm_of_lev ci hGl) (sm_of_lev ci hGl') c
  · simp only [actS_eq]
    refine act_comm hK hKo hA hKj hKoj hB' hf hg' (sm_of_lev ci hGl) (sm_of_lev cj hGl) fun x y => ?_
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, epsS_comm hS hij]
  · simp only [actS_eq]
    rw [selS_conv]
    exact act_conv hK hKo hA hB hf hg (sm_of_lev ci hGl)

end GlobalTheory.CompanionTheory.FactorAction

end
