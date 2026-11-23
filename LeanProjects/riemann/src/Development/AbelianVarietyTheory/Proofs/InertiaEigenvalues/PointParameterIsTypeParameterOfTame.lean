import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.ParOfPoint

theorem inePol_foldr (D : D7) {w : PlE D.host} (x : D.naut.LP w) {α : Type} (c : α → ℝ) (l : List α)
    (σ : GE D.nd) (hσ : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (l.foldr (fun k acc => D.naut.lpSum (D.naut.lpTw x (c k)) acc) (D.naut.lpZero w)) σ =
      D.naut.inePol x σ ^ l.length := by
  induction l with
  | nil =>
    have h := ((D.naut.unr_iff_ine (D.naut.lpZero w)).1 (D.naut.lpZero_unr w)).2 σ hσ
    rw [D.naut.lpDim_zero, pow_zero] at h
    simpa using h
  | cons k l ih =>
    simp only [List.foldr_cons, List.length_cons]
    rw [D.naut.inePol_sum, D.naut.inePol_tw _ _ σ hσ, ih, pow_succ, mul_comm]

theorem inePol_twistIso (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut) (L : List (Part D.naut.CG)) (w : PlE D.host)
    (σ : GE D.nd) (hσ : σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaTinv) w) σ =
      D.naut.inePol (isoLoc D.nd D.naut L w) σ := by
  have hd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ w
  have hu : D.naut.inePol (D.naut.locG D.naut.etaTinv w) σ = X - C 1 := by
    have h := ((D.naut.unr_iff_ine _).1 (D.naut.etaTinv_def w).1).2 σ hσ
    rw [hd, pow_one] at h
    rw [h, map_one]
  have hpart : ∀ {a : ℕ} (π : D.naut.CG a),
      D.naut.inePol (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) σ = D.naut.inePol (D.naut.locG π w) σ := by
    intro a π
    rw [D.naut.locG_tw, ((hT w (D.naut.locG π w) (D.naut.locG π w) _ _ 0 hd hd).2.2.2.2.2 σ hσ).2 1 hu,
      Polynomial.scaleRoots_one]
  induction L with
  | nil => rfl
  | cons p L ih =>
    show D.naut.inePol (D.naut.lpSum (spehLoc D.nd D.naut ⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ w)
      (isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaTinv) w)) σ =
      D.naut.inePol (D.naut.lpSum (spehLoc D.nd D.naut p w) (isoLoc D.nd D.naut L w)) σ
    rw [D.naut.inePol_sum, D.naut.inePol_sum, ih]
    unfold spehLoc
    rw [inePol_foldr D _ _ _ σ hσ, inePol_foldr D _ _ _ σ hσ, hpart]

theorem eq_pow_of_mul_eq (A B : ℂ[X]) (n : ℕ) (hA : A.Monic) (hB : B.Monic) (h : A * B = (X - 1) ^ n) :
    A = (X - 1) ^ A.natDegree := by
  have hdvd : A ∣ (X - C 1) ^ n := by rw [map_one, ← h]; exact dvd_mul_right A B
  obtain ⟨j, -, hj⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C (1 : ℂ)) n).1 hdvd
  have e := Polynomial.eq_of_monic_of_associated hA ((monic_X_sub_C (1 : ℂ)).pow j) hj
  rw [e, (monic_X_sub_C (1 : ℂ)).natDegree_pow, natDegree_X_sub_C, mul_one, map_one]

theorem tw_back (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut)
    (hAN : ∀ Pa Pa' : List (Part D.naut.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa')
    {a : ℕ} (ha : 1 ≤ a) (π : D.naut.CG a) : D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π := by
  have hsing : ∀ (π' : D.naut.CG a) w, isoLoc D.nd D.naut [⟨a, π', 1⟩] w = D.naut.locG π' w := by
    intro π' w
    show D.naut.lpSum (spehLoc D.nd D.naut ⟨a, π', 1⟩ w) (D.naut.lpZero w) = _
    rw [D.naut.lpSum_zero]
    unfold spehLoc
    simp [D.naut.lpSum_zero, D.naut.lpTw_zero]
  have h := hAN [⟨a, D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      rw [hsing, hsing, D.naut.locG_tw, D.naut.locG_tw]
      exact (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hT _).2)
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem main : ∀ D : D7, (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → LabDepth D → DepthZ D → ParSurj D := by
  intro D hPar h0 h5 hsplit hLab hDZ i x Sig hX
  obtain ⟨P, -, hB⟩ := hX
  have hT : SumRepresentations.At.TieLP D.nd D.naut := h0.1
  have hAN := h5.1
  set χ := D.naut.etaTinv with hχ
  have htw : twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ =
      twistIso D.nd D.naut Sig χ ++ twistIso D.nd D.naut [muPart D.nd D.naut i] χ := List.map_append

  have hparts : ∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π := by
    intro p hp
    have hm : (⟨p.a, D.naut.tw p.π χ, p.d⟩ : Part D.naut.CG) ∈
        twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ := by
      rw [htw]
      exact List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩)
    obtain ⟨ha, hd, hc⟩ := hB.1 _ hm
    refine ⟨ha, hd, ?_⟩
    have e := tw_back D hT hAN ha p.π
    rw [← e]
    exact D.naut.csd_tw _ _ h0.2.1.1.1 hc

  have hnodup : (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup := by
    have h2 := hB.2.1
    rw [htw, List.map_append] at h2
    have h3 := (List.nodup_append.1 h2).1
    have e : (twistIso D.nd D.naut Sig χ).map (fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)) =
        (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).map
          (fun q => ((⟨q.1.1, D.naut.tw q.1.2 χ⟩ : Σ a, D.naut.CG a), q.2)) := by
      unfold twistIso
      rw [List.map_map, List.map_map]
      rfl
    rw [e] at h3
    exact h3.of_map _

  have hrank : rankIso D.nd D.naut Sig = D.R.r := by
    have hr := hB.2.2.1
    have e1 : rankIso D.nd D.naut (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) χ) =
        rankIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) := by
      unfold rankIso twistIso
      rw [List.map_map]
      rfl
    rw [e1] at hr
    unfold rankIso at hr ⊢
    rw [List.map_append, List.sum_append] at hr
    simp only [muPart, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at hr
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega

  have hlab : ∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).Monic ∧
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r := by
    intro k v
    set w := D.naut.plGw k v with hw
    have hover := D.naut.plGw_over k v
    obtain ⟨hmon, hiff⟩ := hLab k w hover (isoLoc D.nd D.naut Sig w)
    refine ⟨hmon, ?_⟩
    rw [← hrank, ← lpDim_isoLoc]
    apply hiff.2
    intro σ hσ hwild
    have hloc := hB.2.2.2.1 w (hsplit k v)
    have htame := hDZ i P k w hover σ hσ hwild
    rw [← hloc, inePol_twistIso D hT _ w σ hσ, GlobalTheory.RowThetaParam.isoLoc_append, D.naut.inePol_sum] at htame
    have hd1 : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 := D.naut.locG_dim _ w
    have hm1 := ((hT w (isoLoc D.nd D.naut Sig w) (isoLoc D.nd D.naut Sig w) _ _ 0 hd1 hd1).2.2.2.2.2 σ hσ).1
    have hm2 := ((hT w (isoLoc D.nd D.naut [muPart D.nd D.naut i] w)
      (isoLoc D.nd D.naut [muPart D.nd D.naut i] w) _ _ 0 hd1 hd1).2.2.2.2.2 σ hσ).1
    have e := eq_pow_of_mul_eq _ _ _ hm1.1 hm2.1 htame
    rw [e, hm1.2]
  exact hPar ⟨Sig, hparts, hnodup, hrank, hlab⟩

end GlobalTheory.ParOfPoint
