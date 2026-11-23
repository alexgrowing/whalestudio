import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamDieudonneSpansTensorDeRhamPeriods
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.TateFilQuot

open GlobalTheory.DRFil

section Abstract

variable {G B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
  (σ : G → B →+* B) (ρ : G → M →+ M) (F : ℤ → AddSubgroup B) (FM : ℤ → AddSubgroup M)

theorem step_invariant
    (hρ : ∀ g (b : B) (m : M), ρ g (b • m) = σ g b • ρ g m)
    (hmul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (hsmul : ∀ a b x y, x ∈ F a → y ∈ FM b → x • y ∈ FM (a + b))
    (hFG : ∀ g a x, x ∈ F a → σ g x ∈ F a)
    (hMG : ∀ g a x, x ∈ FM a → ρ g x ∈ FM a)
    (hinv : ∀ a b, b ∈ F a → b ∉ F (a + 1) → ∃ β ∈ F (-a), β * b - 1 ∈ F 1)
    (hT : ∀ n e, e ∈ F n → (∀ g, σ g e - e ∈ F (n + 1)) →
      ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ e - κ ∈ F (n + 1))
    {ι : Type} [DecidableEq ι] (k : ι → ℤ) (d : ι → M) (hd : ∀ i g, ρ g (d i) = d i)
    (hdk : ∀ i, d i ∈ FM (k i)) (c : ℤ) (n : ℕ) :
    ∀ (s : Finset ι), s.card = n → ∀ b : ι → B, (∀ i ∈ s, b i ∈ F (c - k i)) →
      (∀ g, ρ g (∑ i ∈ s, b i • d i) - ∑ i ∈ s, b i • d i ∈ FM (c + 1)) →
      ∃ w ∈ FM c, (∀ g, ρ g w = w) ∧ ∑ i ∈ s, b i • d i - w ∈ FM (c + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn b hb hsum
  by_cases hs : ∃ i ∈ s, ∃ κ : ι → B, (∀ j, κ j ∈ F 0 ∧ (∀ g, σ g (κ j) = κ j) ∧ (k i ≠ k j → κ j = 0)) ∧
      d i + ∑ j ∈ s.erase i, κ j • d j ∈ FM (k i + 1)
  · obtain ⟨i, hi, κ, hκ, hmem⟩ := hs
    have heq : ∑ j ∈ s, b j • d j = b i • (d i + ∑ j ∈ s.erase i, κ j • d j) +
        ∑ j ∈ s.erase i, (b j - b i * κ j) • d j := by
      rw [← Finset.add_sum_erase s _ hi]
      simp only [smul_add, Finset.smul_sum, mul_smul, sub_smul, Finset.sum_sub_distrib]
      abel
    have h1 := hsmul _ _ _ _ (hb i hi) hmem
    rw [show c - k i + (k i + 1) = c + 1 by ring] at h1
    rw [heq] at hsum ⊢
    obtain ⟨w, hw, hwg, hw'⟩ := ih _ (hn ▸ Finset.card_erase_lt_of_mem hi) (s.erase i) rfl
      (fun j => b j - b i * κ j) (fun j hj => by
        refine (F _).sub_mem (hb j (Finset.mem_of_mem_erase hj)) ?_
        by_cases hk : k i = k j
        · have := hmul _ _ _ _ (hb i hi) (hκ j).1
          rwa [add_zero, hk] at this
        · rw [(hκ j).2.2 hk, mul_zero]
          exact (F _).zero_mem) (fun g => by
        have h2 := (FM _).sub_mem (hsum g) ((FM _).sub_mem (hMG g _ _ h1) h1)
        convert h2 using 1
        rw [map_add (ρ g) (b i • _)]
        abel)
    refine ⟨w, hw, hwg, ?_⟩
    rw [add_sub_assoc]
    exact (FM _).add_mem h1 hw'
  · have hg : ∀ g, ∀ i ∈ s, σ g (b i) - b i ∈ F (c - k i + 1) := fun g =>
      graded_indep σ ρ F FM hρ hmul hsmul hFG hMG hinv hT k d hd hdk s hs c
        (fun i => σ g (b i) - b i) (fun i hi => (F _).sub_mem (hFG _ _ _ (hb i hi)) (hb i hi)) (by
          convert hsum g using 1
          simp only [map_sum, hρ, hd, sub_smul, Finset.sum_sub_distrib])
    have hκ : ∀ i, ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (c - k i ≠ 0 → κ = 0) ∧
        (i ∈ s → b i - κ ∈ F (c - k i + 1)) := fun i => by
      by_cases hi : i ∈ s
      · obtain ⟨κ, h1, h2, h3, h4⟩ := hT _ _ (hb i hi) (fun g => hg g i hi)
        exact ⟨κ, h1, h2, h3, fun _ => h4⟩
      · exact ⟨0, (F 0).zero_mem, fun g => map_zero _, fun _ => rfl, fun h => (hi h).elim⟩
    choose κ h1 h2 h3 h4 using hκ
    refine ⟨∑ i ∈ s, κ i • d i, (FM _).sum_mem fun i _ => ?_, fun g => ?_, ?_⟩
    · by_cases hk : c - k i = 0
      · have := hsmul _ _ _ _ (h1 i) (hdk i)
        rwa [show 0 + k i = c by omega] at this
      · rw [h3 i hk, zero_smul]
        exact (FM _).zero_mem
    · simp only [map_sum, hρ, hd, h2]
    · rw [← Finset.sum_sub_distrib]
      refine (FM _).sum_mem fun i hi => ?_
      have := hsmul _ _ _ _ (h4 i hi) (hdk i)
      rwa [show c - k i + 1 + k i = c + 1 by ring, sub_smul] at this

theorem invariant_mod
    (hρ : ∀ g (b : B) (m : M), ρ g (b • m) = σ g b • ρ g m)
    (hmul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (hsmul : ∀ a b x y, x ∈ F a → y ∈ FM b → x • y ∈ FM (a + b))
    (hFG : ∀ g a x, x ∈ F a → σ g x ∈ F a)
    (hMG : ∀ g a x, x ∈ FM a → ρ g x ∈ FM a)
    (hinv : ∀ a b, b ∈ F a → b ∉ F (a + 1) → ∃ β ∈ F (-a), β * b - 1 ∈ F 1)
    (hT : ∀ n e, e ∈ F n → (∀ g, σ g e - e ∈ F (n + 1)) →
      ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ e - κ ∈ F (n + 1))
    (hFa : Antitone F) (hMa : Antitone FM) (hFe : ∀ x, ∃ a, x ∈ F a) (hMe : ∀ x, ∃ a, x ∈ FM a)
    (hspan : ∀ y : M, ∃ (m : ℕ) (b : Fin m → B) (d : Fin m → M),
      (∀ i g, ρ g (d i) = d i) ∧ y = ∑ i, b i • d i)
    (a b : ℤ) (z : M) (hz : z ∈ FM a) (hg : ∀ g, ρ g z - z ∈ FM b) :
    ∃ w ∈ FM a, (∀ g, ρ g w = w) ∧ z - w ∈ FM b := by
  have key : ∀ c, a ≤ c → c ≤ max a b → ∃ w ∈ FM a, (∀ g, ρ g w = w) ∧ z - w ∈ FM c := by
    intro c hc
    induction c, hc using Int.le_induction with
    | base => exact fun _ => ⟨0, (FM _).zero_mem, fun g => map_zero _, by rwa [sub_zero]⟩
    | succ c hc ih =>
      intro hcb
      have hcb' : c + 1 ≤ b := by omega
      obtain ⟨w, hw, hwg, hzw⟩ := ih (by omega)
      obtain ⟨m, b₀, d₀, hd₀, e₀⟩ := hspan (z - w)
      obtain ⟨m', k', b', d', h, e⟩ := filtered σ ρ F FM hρ hmul hsmul hFG hMG hinv hT hFa hMa hFe hMe
        c (z - w) hzw m b₀ d₀ hd₀ e₀
      obtain ⟨w', hw', hwg', hzw'⟩ := step_invariant σ ρ F FM hρ hmul hsmul hFG hMG hinv hT k' d'
        (fun i => (h i).1) (fun i => (h i).2.1) c _ Finset.univ rfl b' (fun i _ => (h i).2.2)
        (fun g => by
          rw [← e, map_sub, hwg, sub_sub_sub_cancel_right]
          exact hMa hcb' (hg g))
      refine ⟨w + w', (FM _).add_mem hw (hMa hc hw'), fun g => by rw [map_add, hwg, hwg'], ?_⟩
      rwa [← e, sub_sub] at hzw'
  obtain ⟨w, hw, hwg, hzw⟩ := key (max a b) (le_max_left _ _) le_rfl
  exact ⟨w, hw, hwg, hMa (le_max_right _ _) hzw⟩

end Abstract

theorem tied_invariant_mod (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (TT : LocTied l P AI) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    (hdR : IsDR (P.PD K) ρ) (a b : ℤ) (z : V ⊗[ℚ_[l]] P.R.BdR)
    (hz : z ∈ FilV (P.PD K) (LL := LL) (V := V) a)
    (hg : ∀ g, actVdR (P.PD K) ρ g z - z ∈ FilV (P.PD K) (LL := LL) (V := V) b) :
    ∃ w ∈ DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := LL) (V := V) a,
      z - w ∈ FilV (P.PD K) (LL := LL) (V := V) b := by
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI TT
  have hspan := GlobalTheory.Per.DeRhamSpan.span_of_isField (P.PD K) ρ
    (GlobalTheory.Per.TiedField.tied_field l P AI TT).1 hdR
  let φ : P.R.BdR →+* Module.End LL (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := fun b => AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] b)
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc]
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [add_mul, tmul_add] }
  letI : Module P.R.BdR (V ⊗[ℚ_[l]] P.R.BdR) := Module.compHom _ φ
  have hsm : ∀ (b : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR), b • x =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] b) x := fun _ _ => rfl
  have hD : ∀ x, x ∈ DdR (P.PD K) ρ ↔ ∀ g, actVdR (P.PD K) ρ g x = x := fun x => by
    simp [DdR, Submodule.mem_iInf, sub_eq_zero]
  have htm : ∀ (a : ℤ) (v : V) (x : P.R.BdR), x ∈ (P.PD K).Fil a →
      v ⊗ₜ[ℚ_[l]] x ∈ FilV (P.PD K) (LL := LL) (V := V) a := fun a v x hx =>
    ⟨v ⊗ₜ ⟨x, hx⟩, rfl⟩
  have hind : ∀ (a : ℤ) (S : AddSubgroup (V ⊗[ℚ_[l]] P.R.BdR)),
      (∀ (v : V) (x : P.R.BdR), x ∈ (P.PD K).Fil a → v ⊗ₜ[ℚ_[l]] x ∈ S) →
      ∀ z ∈ FilV (P.PD K) (LL := LL) (V := V) a, z ∈ S := by
    rintro a S hS _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact S.zero_mem
    | tmul v x => exact hS v x x.2
    | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
  have hFa : Antitone fun a => ((P.PD K).Fil a).toAddSubgroup :=
    antitone_int_of_succ_le fun a => (P.PD K).Fil_anti a
  have hMa : Antitone fun a => (FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup :=
    fun a a' h z hz => hind a' _ (fun v x hx => htm a v x (hFa h hx)) z hz
  obtain ⟨w, hw, hwg, hzw⟩ := invariant_mod (G := ↥(GK K))
    (fun g => ((P.PD K).actdR g : P.R.BdR →+* P.R.BdR))
    (fun g => (actVdR (P.PD K) ρ g).toAddMonoidHom)
    (fun a => ((P.PD K).Fil a).toAddSubgroup)
    (fun a => (FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup)
    (fun g b x => by
      rw [hsm, hsm]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v x => simp [actVdR]
      | add x y hx hy => simp only [map_add, hx, hy])
    (P.PD K).Fil_mul
    (fun a c x z hx hz => hind c
      ((FilV (P.PD K) (LL := LL) (V := V) (a + c)).toAddSubgroup.comap (φ x).toAddMonoidHom)
      (fun v w hw => htm _ v (x * w) ((P.PD K).Fil_mul _ _ _ _ hx hw)) z hz)
    (P.PD K).Fil_G
    (fun g a z hz => hind a
      ((FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup.comap (actVdR (P.PD K) ρ g).toAddMonoidHom)
      (fun v w hw => htm _ (ρ g v) ((P.PD K).actdR g w) ((P.PD K).Fil_G _ _ _ hw)) z hz)
    (graded_inv Θ K) (graded_invariants TT Θ K) hFa hMa (P.PD K).Fil_exh
    (fun x => by
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, AddSubgroup.zero_mem _⟩
      | tmul v x =>
        obtain ⟨c, hc⟩ := (P.PD K).Fil_exh x
        exact ⟨c, htm c v x hc⟩
      | add x y hx hy =>
        obtain ⟨c, hc⟩ := hx
        obtain ⟨c', hc'⟩ := hy
        exact ⟨min c c', AddSubgroup.add_mem _ (hMa (min_le_left _ _) hc) (hMa (min_le_right _ _) hc')⟩)
    (fun y => by
      obtain ⟨m, b, d, hd, e⟩ := hspan y
      exact ⟨m, b, d, fun i g => (hD _).1 (hd i) g, e⟩)
    a b z hz hg
  exact ⟨w, ⟨(hD _).2 hwg, hw⟩, hzw⟩

theorem tate_fil_quot : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm5 D := by
  intro D l _ K LL _ _ _ O _ _ hO A hA a b z hz hg
  haveI := hO.2.1
  exact tied_invariant_mod l (D.loc l) (D.locA l) (D.locT l) K LL A.V A.ρ hA a b z hz hg

end GlobalTheory.TateFilQuot
