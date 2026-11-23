import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WordInduction.WordActionLetterSiteApply

open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {j : ℕ}

theorem paramComm_local {A : (Matrix (Fin j) (Fin j) ℂ → E) →ₗ[ℂ] (Matrix (Fin j) (Fin j) ℂ → E)} (hA : ParamComm A) {W : Set (Fin j → Fin j → ℂ)} (hW : IsOpen W)
    (hWd : W ⊆ {Z | (Matrix.of Z).det ≠ 0}) {f g : Matrix (Fin j) (Fin j) ℂ → E} (hfg : ∀ Z ∈ W, f (Matrix.of Z) = g (Matrix.of Z)) :
    ∀ Z ∈ W, A f (Matrix.of Z) = A g (Matrix.of Z) := by
  intro Z hZ
  set h : Matrix (Fin j) (Fin j) ℂ → E := f - g with hh
  set c : ℂ → ℂ := fun τ => if τ = 0 then 1 else 0 with hc
  set U : Set (ℂ × (Fin j → Fin j → ℂ)) := Set.univ ×ˢ W with hUdef
  have hU : IsOpen U := isOpen_univ.prod hW
  have hUd : U ⊆ {q | (Matrix.of q.2).det ≠ 0} := fun q hq => hWd hq.2
  have hsm : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => (c q.1 • h) (Matrix.of q.2)) U := by
    refine (contDiffOn_const (c := (0 : E))).congr fun q hq => ?_
    simp [hh, hfg q.2 hq.2]
  obtain ⟨h1, -⟩ := hA U (fun τ => c τ • h) hU hUd hsm
  have hq0 : ((0 : ℂ), Z) ∈ U := ⟨trivial, hZ⟩
  have hca : ContinuousAt (fun q : ℂ × (Fin j → Fin j → ℂ) => A (c q.1 • h) (Matrix.of q.2)) ((0 : ℂ), Z) :=
    h1.continuousOn.continuousAt (hU.mem_nhds hq0)
  have hcomp : ContinuousAt (fun τ : ℂ => A (c τ • h) (Matrix.of Z)) 0 :=
    hca.comp (f := fun τ : ℂ => (τ, Z)) (continuous_id.prodMk continuous_const).continuousAt
  have t1 := hcomp.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
  have t2 : Filter.Tendsto (fun τ : ℂ => A (c τ • h) (Matrix.of Z)) (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have : τ ≠ 0 := hτ
    simp [hc, this]
  have := tendsto_nhds_unique t1 t2
  simp only [hc, if_true, one_smul] at this
  have e : A h (Matrix.of Z) = A f (Matrix.of Z) - A g (Matrix.of Z) := by
    rw [hh, map_sub]; rfl
  rw [← sub_eq_zero, ← e, this]

theorem dz_family_smooth {U : Set (ℂ × (Fin j → Fin j → ℂ))} (hU : IsOpen U) {F : ℂ → Matrix (Fin j) (Fin j) ℂ → E}
    (hF : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => F q.1 (Matrix.of q.2)) U) :
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => PBP.dz (fun τ => F τ (Matrix.of q.2)) q.1) U ∧
      ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => PBP.dzb (fun τ => F τ (Matrix.of q.2)) q.1) U := by
  set G : ℂ × (Fin j → Fin j → ℂ) → E := fun q => F q.1 (Matrix.of q.2) with hG
  have hD : ContDiffOn ℝ ∞ (fun q => fderiv ℝ G q) U := hF.fderiv_of_isOpen hU (by simp)
  have key : ∀ q ∈ U, ∀ v : ℂ, fderiv ℝ (fun τ => F τ (Matrix.of q.2)) q.1 v = fderiv ℝ G q (v, 0) := by
    intro q hq v
    have hGd : HasFDerivAt G (fderiv ℝ G q) q :=
      ((hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq)).hasFDerivAt
    have hin : HasFDerivAt (fun τ : ℂ => (τ, q.2)) (ContinuousLinearMap.inl ℝ ℂ (Fin j → Fin j → ℂ)) q.1 :=
      hasFDerivAt_prodMk_left q.1 q.2
    have hc := hGd.comp q.1 hin
    rw [show (fun τ => F τ (Matrix.of q.2)) = G ∘ (fun τ : ℂ => (τ, q.2)) from rfl, hc.fderiv]
    rfl
  constructor
  · refine (((hD.clm_apply (contDiffOn_const (c := ((1 : ℂ), (0 : Fin j → Fin j → ℂ))))).sub
      ((hD.clm_apply (contDiffOn_const (c := (Complex.I, (0 : Fin j → Fin j → ℂ))))).const_smul Complex.I)).const_smul
        (1 / 2 : ℂ)).congr fun q hq => ?_
    simp only [PBP.dz, key q hq]
  · refine (((hD.clm_apply (contDiffOn_const (c := ((1 : ℂ), (0 : Fin j → Fin j → ℂ))))).add
      ((hD.clm_apply (contDiffOn_const (c := (Complex.I, (0 : Fin j → Fin j → ℂ))))).const_smul Complex.I)).const_smul
        (1 / 2 : ℂ)).congr fun q hq => ?_
    simp only [PBP.dzb, key q hq]

section lin

variable {X : Type} (A : (X → E) →ₗ[ℂ] (X → E))

theorem linP (a b c : ℂ) (u v w : X → E) :
    A (fun Z => a • u Z + b • v Z - c • w Z) = a • A u + b • A v - c • A w := by
  rw [show (fun Z => a • u Z + b • v Z - c • w Z) = a • u + b • v - c • w from rfl, map_sub, map_add,
    map_smul, map_smul, map_smul]

theorem linM (a b c : ℂ) (u v w : X → E) :
    A (fun Z => a • u Z - b • v Z - c • w Z) = a • A u - b • A v - c • A w := by
  rw [show (fun Z => a • u Z - b • v Z - c • w Z) = a • u - b • v - c • w from rfl, map_sub, map_sub,
    map_smul, map_smul, map_smul]

theorem linS (d : ℂ) (u : X → E) : A (fun Z => d • u Z) = d • A u := by
  rw [show (fun Z => d • u Z) = d • u from rfl, map_smul]

end lin

theorem two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have h : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  exact h i

theorem row_family (κ : ℂ) (pl : Bool) (Y : ℂ) {U : Set (ℂ × (Fin j → Fin j → ℂ))} (hU : IsOpen U)
    (hU0 : U ⊆ {q | q.1 ≠ 0}) {Fa Fb : ℂ → Matrix (Fin j) (Fin j) ℂ → E}
    (ha : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => Fa q.1 (Matrix.of q.2)) U)
    (hb : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => Fb q.1 (Matrix.of q.2)) U) (s : Fin 2) :
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) =>
      row κ pl Y (fun τ => Fa τ (Matrix.of q.2)) (fun τ => Fb τ (Matrix.of q.2)) s q.1) U := by
  obtain ⟨hdz, hdzb⟩ := dz_family_smooth hU ha
  have hm : Set.MapsTo (fun q : ℂ × (Fin j → Fin j → ℂ) => q.1) U {τ | τ ≠ 0} := fun q hq => hU0 hq
  have h1 : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => q.1) U := contDiffOn_fst
  have h2 : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => conj q.1) U := cd_conj.comp contDiffOn_fst hm
  have h3 : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => q.1⁻¹) U := cd_inv.comp contDiffOn_fst hm
  have h4 : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => (conj q.1)⁻¹) U := cd_conjinv.comp contDiffOn_fst hm
  unfold row
  rcases two_cases s with hs | hs <;> cases pl <;> simp only [hs, if_true, Bool.false_eq_true, if_false, one_ne_zero]
  · exact ((contDiffOn_const.smul ha).sub (h2.smul hdzb)).sub (h2.smul hb)
  · exact ((contDiffOn_const.smul ha).add (h1.smul hdz)).sub (h1.smul hb)
  · exact h4.smul ha
  · exact h3.smul ha

theorem row_comm {A : (Matrix (Fin j) (Fin j) ℂ → E) →ₗ[ℂ] (Matrix (Fin j) (Fin j) ℂ → E)} (hA : ParamComm A)
    (κ : ℂ) (pl : Bool) (Y : ℂ) {U : Set (ℂ × (Fin j → Fin j → ℂ))} (hU : IsOpen U)
    (hUd : U ⊆ {q | (Matrix.of q.2).det ≠ 0}) {Fa Fb : ℂ → Matrix (Fin j) (Fin j) ℂ → E}
    (ha : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => Fa q.1 (Matrix.of q.2)) U) (s : Fin 2)
    {q : ℂ × (Fin j → Fin j → ℂ)} (hq : q ∈ U) :
    A (fun Z => row κ pl Y (fun τ => Fa τ Z) (fun τ => Fb τ Z) s q.1) (Matrix.of q.2) =
      row κ pl Y (fun τ => A (Fa τ) (Matrix.of q.2)) (fun τ => A (Fb τ) (Matrix.of q.2)) s q.1 := by
  obtain ⟨-, hc⟩ := hA U Fa hU hUd ha
  obtain ⟨hz, hzb⟩ := hc q hq
  unfold row
  rcases two_cases s with hs | hs <;> cases pl <;> simp only [hs, if_true, Bool.false_eq_true, if_false, one_ne_zero]
  · rw [linM A _ _ _ (Fa q.1) (fun Z => PBP.dzb (fun τ => Fa τ Z) q.1) (Fb q.1)]
    simp only [Pi.sub_apply, Pi.smul_apply, hzb]
  · rw [linP A _ _ _ (Fa q.1) (fun Z => PBP.dz (fun τ => Fa τ Z) q.1) (Fb q.1)]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hz]
  · rw [linS A _ (Fa q.1)]; rfl
  · rw [linS A _ (Fa q.1)]; rfl

section words

variable {S : Type} [Fintype S] [DecidableEq S]

theorem comm_rawBT {A : (Matrix (Fin j) (Fin j) ℂ → E) →ₗ[ℂ] (Matrix (Fin j) (Fin j) ℂ → E)} (hA : ParamComm A)
    {U : Set (ℂ × (Fin j → Fin j → ℂ))} (hU : IsOpen U) (hUd : U ⊆ {q | (Matrix.of q.2).det ≠ 0})
    (hU0 : U ⊆ {q | q.1 ≠ 0}) (κ : ℂ) (L : List (Wd.Letter ℂ S)) (h : Wd.Ix S → ℂ → Matrix (Fin j) (Fin j) ℂ → E)
    (hs : ∀ b, ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => h b q.1 (Matrix.of q.2)) U) :
    (∀ e, ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) =>
        rawBT κ L (fun b τ => h b τ (Matrix.of q.2)) e q.1) U) ∧
      ∀ e, ∀ q ∈ U, A (fun Z => rawBT κ L (fun b τ => h b τ Z) e q.1) (Matrix.of q.2) =
        rawBT κ L (fun b τ => A (h b τ) (Matrix.of q.2)) e q.1 := by
  induction L with
  | nil => exact ⟨hs, fun _ _ _ => rfl⟩
  | cons l L ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · intro e
      exact row_family κ l.plus l.pt hU hU0 (Fa := fun τ Z => rawBT κ L (fun b τ => h b τ Z) _ τ)
        (Fb := fun τ Z => rawBT κ L (fun b τ => h b τ Z) _ τ) (ih1 _) (ih1 _) _
    · intro e q hq
      show A (fun Z => row κ l.plus l.pt _ _ _ q.1) (Matrix.of q.2) = row κ l.plus l.pt _ _ _ q.1
      rw [row_comm hA κ l.plus l.pt hU hUd (Fa := fun τ Z => rawBT κ L (fun b τ => h b τ Z) _ τ)
        (Fb := fun τ Z => rawBT κ L (fun b τ => h b τ Z) _ τ) (ih1 _) _ hq]
      have hV : IsOpen {τ : ℂ | (τ, q.2) ∈ U} :=
        hU.preimage (continuous_id.prodMk continuous_const)
      exact row_congr κ l.plus l.pt hV (fun τ hτ => ih2 _ (τ, q.2) hτ) (fun τ hτ => ih2 _ (τ, q.2) hτ) _ hq

end words

end Formalism.FourierDecayAlt.P.LevelPointCoordinates.WordIndPf
