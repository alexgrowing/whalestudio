import Formalism.LocalRingCardinality.DataBu
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowA

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions

abbrev En (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

abbrev eb (n : ℕ) : OrthonormalBasis (Fin n) ℂ (En n) := EuclideanSpace.basisFun (Fin n) ℂ

section Rows

variable {R : Ranks} (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)
  (kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ)
  (tw : P.Pl → Bool) (htw : ∀ w, tw (P.conj w) = tw w)
  (Word : Type) (cI : Word → Type) [∀ u, Fintype (cI u)] (d Dall d0 : ℕ) (hd : d ≤ Dall)
  (FT : Type) [Fintype FT] [DecidableEq FT] (ft : Fin d → FT) (ft0 : Fin d0 → FT)
  (per : ∀ u : Word, Bool → EuclideanSpace ℂ (cI u) → En d → ℂ)
  (eta : ℕ → P.Pl → ℚ) (heta : ∀ j w, 0 ≤ eta j w)

theorem rank_eq_ratio_identity (d Dall : ℕ) (hd : d ≤ Dall) : (d : ℝ) = (1 - (1 - (d : ℝ) / Dall)) * Dall := by
  rcases Nat.eq_zero_or_pos Dall with h | h
  · subst h
    have : d = 0 := by omega
    subst this; simp
  · have : (Dall : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp
    ring

abbrev rowsN : Rows.Data R where
  LL := LL
  embLL := embLL
  places := P
  O := 𝓞 LL
  OtoLL := algebraMap (𝓞 LL) LL
  Tau := Tau
  card_Tau := hTau
  Tup := Bool
  mu0 := false
  muStar := true
  muStar' := true
  muAt := tw
  muAt_conj := htw
  muTw := fun _ => true
  muTw_conj := fun _ => rfl
  muAt_or := fun w => Bool.eq_false_or_eq_true (tw w) |>.symm
  EE := En d
  Drows := d
  onb := eb d
  Dall := Dall
  delp := 1 - (d : ℝ) / Dall
  delp_le_one := by
    have : (0 : ℝ) ≤ (d : ℝ) / Dall := by positivity
    linarith
  D_eq := rank_eq_ratio_identity d Dall hd
  EE0 := En d0
  D0 := d0
  onb0 := eb d0
  FT := FT
  ft := ft
  ft0 := ft0
  Dstar := Dst
  Amb := fun _ => En d
  Mult := fun _ _ => En d
  multZero := fun _ => LinearIsometryEquiv.refl ℂ (En d)
  multTop := fun _ => LinearIsometryEquiv.refl ℂ (En d)
  io := fun _ _ => LinearMap.id
  Mtilde := fun _ => oB (eb d) _
  eOp := fun _ => LinearMap.id
  eOp_idem := fun _ => rfl
  eOp_sa := fun _ _ _ => rfl
  restRowsFiniteGroupCard := cg
  restRowsFiniteGroupCard_pos := hcg
  Word := Word
  Mu := fun u => EuclideanSpace ℂ (cI u)
  perCol := per
  Bu := fun u φ F => per u false φ F
  ze := fun _ _ => 1
  rowsRest_wordColumnUnit_baseTuple := fun _ => rfl
  Mj := fun _ => En d0
  MjLat := fun _ => oB (eb d0) _
  kaBig := kb
  kaSmall := ks
  Mt := fun _ _ => En d0
  MtLat := fun _ _ => oB (eb d0) _
  MtL := fun _ _ => Fin d0 → LL
  jMt := fun _ _ => jB embLL (eb d0)
  jMt_basis := fun _ _ b => basis_of_basis embLL (jB embLL (eb d0)) (Pi.basisFun LL (Fin d0))
    (jB_basis0 embLL (eb d0)) b
  MtLat_sub := fun _ _ => generators_mem_range embLL (eb d0)
  eMt := fun _ _ => LinearMap.id
  eMt_idem := fun _ _ => rfl
  eMt_sa := fun _ _ _ _ => rfl
  eMt_LL := fun _ _ x => ⟨x, rfl⟩
  thetaP := fun _ _ => LinearMap.id
  isot := fun _ π => Submodule.span ℂ (eb d0 '' {σ | ft0 σ = π})
  lamP := fun _ _ _ => 1
  Ij := fun _ _ _ => 0
  jw := fun _ _ _ => 0
  etaJ := eta
  etaJ_nonneg := heta
  shaLen := sha
  shaLen_nonneg := hsha

end Rows

section RowsLemmas

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] {embLL : LL →+* ℂ} {P : Rows.Places LL}
  {Tau : Type} [Fintype Tau] {hTau : Fintype.card Tau = R.f} {Dst : ℝ}
  {sha : ℕ → ℕ → ℚ} {hsha : ∀ l e, 0 ≤ sha l e} {cg : ℕ} {hcg : 0 < cg}
  {kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ} {ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ}
  {tw : P.Pl → Bool} {htw : ∀ w, tw (P.conj w) = tw w}
  {Word : Type} {cI : Word → Type} [∀ u, Fintype (cI u)] {d Dall d0 : ℕ} {hd : d ≤ Dall}
  {FT : Type} [Fintype FT] [DecidableEq FT] {ft : Fin d → FT} {ft0 : Fin d0 → FT}
  {per : ∀ u : Word, Bool → EuclideanSpace ℂ (cI u) → En d → ℂ}
  {eta : ℕ → P.Pl → ℚ} {heta : ∀ j w, 0 ≤ eta j w}

local notation "RN" => (rowsN (R := R) LL embLL P Tau hTau Dst sha hsha cg hcg kb ks tw htw Word cI d Dall d0 hd FT ft ft0
  per eta heta)

theorem rowsN_downTo (μ : Bool) (j : ℕ) : (RN).downTo μ j = (LinearMap.id : En d →ₗ[ℂ] En d) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show ((RN).downTo μ j).comp (LinearMap.id : En d →ₗ[ℂ] En d) = _
    rw [ih]; rfl

theorem rowsN_iota (μ : Bool) : (RN).iota μ = (LinearMap.id : En d →ₗ[ℂ] En d) := by
  show (LinearMap.id : En d →ₗ[ℂ] En d) ∘ₗ (RN).downTo μ R.m ∘ₗ (LinearMap.id : En d →ₗ[ℂ] En d) = _
  rw [rowsN_downTo]; rfl

theorem rowsN_thetaT (μ : Bool) (j : ℕ) : (RN).thetaT μ j = (LinearMap.id : En d0 →ₗ[ℂ] En d0) :=
  LinearMap.adjoint_id

theorem rowsN_TjSet (μ : Bool) (j : ℕ) :
    (RN).TjSet μ j = (oB (eb d0) (embLL.comp (algebraMap (𝓞 LL) LL))).carrier := by
  have hZ : (RN).Zj μ j = ⊤ := by
    unfold Rows.Data.Zj; rw [rowsN_thetaT]; exact LinearMap.range_id
  have hp : ∀ x, ((RN).Zj μ j).starProjection x = x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (by rw [hZ]; trivial)
  unfold Rows.Data.TjSet
  ext x
  simp only [hp, Set.mem_image]
  exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun h => ⟨x, h, rfl⟩⟩

end RowsLemmas

section Gen

variable {R : Ranks} (D : Rows.Data R)

theorem recordBaseSubspace_top {μ} (he : D.eOp μ = LinearMap.id) : D.V0 μ = ⊤ := by
  unfold Rows.Data.V0; rw [he]; exact LinearMap.range_id

theorem rUsp_bot {μ} (he : D.eOp μ = LinearMap.id) (hi : Function.Injective (D.iota μ)) : D.Usp μ = ⊥ := by
  unfold Rows.Data.Usp; rw [recordBaseSubspace_top D he, LinearMap.ker_eq_bot.mpr hi, inf_bot_eq]

theorem rQsp_top {μ} (he : D.eOp μ = LinearMap.id) (hi : Function.Injective (D.iota μ)) : D.Qsp μ = ⊤ := by
  unfold Rows.Data.Qsp; rw [recordBaseSubspace_top D he, rUsp_bot D he hi, Submodule.bot_orthogonal_eq_top, inf_top_eq]

theorem buDefQ_of (he : D.eOp D.mu0 = LinearMap.id) (hi : Function.Bijective (D.iota D.mu0))
    (h : ∀ u φ F, D.Bu u φ (D.iota D.mu0 F) = D.perCol u D.mu0 φ F) : Rows.BuDefQ D := by
  intro u φ x
  obtain ⟨F, rfl⟩ := hi.2 x
  rw [D.sec_iota _ F (by rw [rQsp_top D he hi.1]; trivial), h]

end Gen

theorem rowsN_buDefQ {R : Ranks} (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
    (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R.f) (Dst : ℝ)
    (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)
    (kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ)
    (tw : P.Pl → Bool) (htw : ∀ w, tw (P.conj w) = tw w)
    (Word : Type) (cI : Word → Type) [∀ u, Fintype (cI u)] (d Dall d0 : ℕ) (hd : d ≤ Dall)
    (FT : Type) [Fintype FT] [DecidableEq FT] (ft : Fin d → FT) (ft0 : Fin d0 → FT)
    (per : ∀ u : Word, Bool → EuclideanSpace ℂ (cI u) → En d → ℂ)
    (eta : ℕ → P.Pl → ℚ) (heta : ∀ j w, 0 ≤ eta j w) :
    Rows.BuDefQ (rowsN (R := R) LL embLL P Tau hTau Dst sha hsha cg hcg kb ks tw htw Word cI d Dall d0 hd FT ft ft0
      per eta heta) := by
  refine buDefQ_of _ rfl ?_ ?_
  · rw [rowsN_iota]; exact Function.bijective_id
  · intro u φ F
    rw [rowsN_iota]; rfl

end Formalism.BasicNotions.Examples₂.NZ
