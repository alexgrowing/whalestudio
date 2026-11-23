import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPush
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {Y : Scheme.{u}} (G : Y.Modules)

lemma eq_of_forall_resF {κ : Type u} (W : κ → Y.Opens) {U : Y.Opens} (hle : ∀ k, W k ≤ U)
    (hcov : U ≤ iSup W) (m m' : Γ(G, U)) (h : ∀ k, resF G (hle k) m = resF G (hle k) m') :
    m = m' :=
  TopCat.Sheaf.eq_of_locally_eq' (modulesAb G) W U (fun k => homOfLE (hle k)) hcov m m' h

lemma exists_resF_eq_of_compatible {κ : Type u} (W : κ → Y.Opens) {U : Y.Opens}
    (hle : ∀ k, W k ≤ U) (hcov : U ≤ iSup W) (σ : ∀ k, Γ(G, W k))
    (hσ : ∀ k l, resF G (inf_le_left : W k ⊓ W l ≤ W k) (σ k) =
      resF G (inf_le_right : W k ⊓ W l ≤ W l) (σ l)) :
    ∃ m : Γ(G, U), ∀ k, resF G (hle k) m = σ k := by
  obtain ⟨m, hm, -⟩ := TopCat.Sheaf.existsUnique_gluing' (modulesAb G) W U
    (fun k => homOfLE (hle k)) hcov σ
    (fun k l => hσ k l)
  exact ⟨m, hm⟩

variable [G.IsQuasicoherent]

lemma basicOpen_resO_le {U W : Y.Opens} (hWU : W ≤ U) (h : Γ(Y, U)) :
    Y.basicOpen (resO hWU h) ≤ Y.basicOpen h := by
  rw [Scheme.basicOpen_res]
  exact inf_le_right

theorem qcoh_exists_pow_smul_eq_zero_of_isCompact {U : Y.Opens} (hU : IsCompact (U : Set Y))
    (h : Γ(Y, U)) (m : Γ(G, U)) (hm : resF G (Y.basicOpen_le h) m = 0) :
    ∃ e : ℕ, h ^ e • m = 0 := by
  classical
  obtain ⟨Us, hUs, hfin, hUeq⟩ := Y.isBasis_affineOpens.exists_finite_of_isCompact hU
  have := hfin.to_subtype
  have hle : ∀ k : Us, (k : Y.Opens) ≤ U := fun k => hUeq ▸ le_sSup k.2
  have key : ∀ k : Us, ∃ e : ℕ, resO (hle k) h ^ e • resF G (hle k) m = 0 := fun k =>
    qcoh_exists_pow_smul_eq_zero G (hUs k.2) (resO (hle k) h) (resF G (hle k) m) (by
      rw [resF_resF, ← resF_resF G (Y.basicOpen_le h) (basicOpen_resO_le (hle k) h), hm, map_zero])
  choose e he using key
  have := Fintype.ofFinite Us
  refine ⟨Finset.univ.sup e, eq_of_forall_resF G (fun k : Us => (k : Y.Opens)) hle
    (by rw [hUeq, sSup_eq_iSup']) _ _ fun k => ?_⟩
  have hk : e k ≤ Finset.univ.sup e := Finset.le_sup (Finset.mem_univ k)
  rw [map_zero, resF_smul, map_pow, ← Nat.sub_add_cancel hk, pow_add, mul_smul, he k, smul_zero]

theorem qcoh_exists_res_eq_of_qcqs {U : Y.Opens} (hU : IsCompact (U : Set Y))
    (hU' : IsQuasiSeparated (U : Set Y)) (h : Γ(Y, U)) (m : Γ(G, Y.basicOpen h)) :
    ∃ (e : ℕ) (m' : Γ(G, U)), resF G (Y.basicOpen_le h) m' = resO (Y.basicOpen_le h) h ^ e • m := by
  classical
  obtain ⟨Us, hUs, hfin, hUeq⟩ := Y.isBasis_affineOpens.exists_finite_of_isCompact hU
  have := hfin.to_subtype
  have := Fintype.ofFinite Us
  let W : Us → Y.Opens := fun k => k
  have hle : ∀ k, W k ≤ U := fun k => hUeq ▸ le_sSup k.2
  have hcov : U ≤ iSup W := by rw [hUeq, sSup_eq_iSup']

  have loc : ∀ k, ∃ (e : ℕ) (mk : Γ(G, W k)),
      resF G (Y.basicOpen_le (resO (hle k) h)) mk =
        resO (Y.basicOpen_le (resO (hle k) h)) (resO (hle k) h) ^ e •
          resF G (basicOpen_resO_le (hle k) h) m := fun k =>
    qcoh_exists_res_eq G (hUs k.2) (resO (hle k) h) (resF G (basicOpen_resO_le (hle k) h) m)
  choose e mk hmk using loc
  set N := Finset.univ.sup e
  obtain ⟨σ, hσ⟩ : ∃ σ : ∀ k, Γ(G, W k), ∀ k,
      resF G (Y.basicOpen_le (resO (hle k) h)) (σ k) =
        resO ((basicOpen_resO_le (hle k) h).trans (Y.basicOpen_le h)) h ^ N •
          resF G (basicOpen_resO_le (hle k) h) m := by
    refine ⟨fun k => resO (hle k) h ^ (N - e k) • mk k, fun k => ?_⟩
    have hk : e k ≤ N := Finset.le_sup (Finset.mem_univ k)
    rw [resF_smul, hmk, smul_smul]
    simp only [map_pow, resO_resO]
    rw [← pow_add, Nat.sub_add_cancel hk]

  have pair : ∀ k l, ∃ e' : ℕ, resO (inf_le_left.trans (hle k) : W k ⊓ W l ≤ U) h ^ e' •
      (resF G (inf_le_left : W k ⊓ W l ≤ W k) (σ k) -
        resF G (inf_le_right : W k ⊓ W l ≤ W l) (σ l)) = 0 := by
    intro k l
    have hkl : IsCompact ((W k ⊓ W l : Y.Opens) : Set Y) :=
      hU' _ _ (hle k) (W k).2 (hUs k.2).isCompact (hle l) (W l).2 (hUs l.2).isCompact
    refine qcoh_exists_pow_smul_eq_zero_of_isCompact G hkl _ _ ?_
    have hb : Y.basicOpen (resO (inf_le_left.trans (hle k) : W k ⊓ W l ≤ U) h) ≤
        Y.basicOpen (resO (hle k) h) := by
      rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
      exact inf_le_inf_right _ inf_le_left
    have hb' : Y.basicOpen (resO (inf_le_left.trans (hle k) : W k ⊓ W l ≤ U) h) ≤
        Y.basicOpen (resO (hle l) h) := by
      rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
      exact inf_le_inf_right _ inf_le_right
    rw [map_sub, resF_resF, resF_resF, sub_eq_zero,
      ← resF_resF G (Y.basicOpen_le (resO (hle k) h)) hb,
      ← resF_resF G (Y.basicOpen_le (resO (hle l) h)) hb', hσ k, hσ l, resF_smul, resF_smul,
      resF_resF, resF_resF, map_pow, map_pow, resO_resO, resO_resO]
  choose e' he' using pair
  set N' := Finset.univ.sup (fun kl : Us × Us => e' kl.1 kl.2)
  obtain ⟨τ, hτdef⟩ : ∃ τ : ∀ k, Γ(G, W k), ∀ k, τ k = resO (hle k) h ^ N' • σ k :=
    ⟨fun k => resO (hle k) h ^ N' • σ k, fun _ => rfl⟩
  have hτ : ∀ k l, resF G (inf_le_left : W k ⊓ W l ≤ W k) (τ k) =
      resF G (inf_le_right : W k ⊓ W l ≤ W l) (τ l) := by
    intro k l
    have hkl : e' k l ≤ N' := Finset.le_sup (f := fun kl : Us × Us => e' kl.1 kl.2)
      (Finset.mem_univ (k, l))
    rw [hτdef, hτdef, resF_smul, resF_smul, map_pow, map_pow, resO_resO, resO_resO, ← sub_eq_zero,
      ← smul_sub, ← Nat.sub_add_cancel hkl, pow_add, mul_smul, he' k l, smul_zero]
  obtain ⟨m', hm'⟩ := exists_resF_eq_of_compatible G W hle hcov τ hτ
  refine ⟨N' + N, m', ?_⟩

  refine eq_of_forall_resF G (fun k => Y.basicOpen (resO (hle k) h))
    (fun k => basicOpen_resO_le (hle k) h) ?_ _ _ fun k => ?_
  · intro x hx
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hcov (Y.basicOpen_le h hx))
    refine Opens.mem_iSup.2 ⟨k, ?_⟩
    rw [Scheme.basicOpen_res]
    exact ⟨hk, hx⟩
  · rw [resF_resF, ← resF_resF G (hle k) (Y.basicOpen_le (resO (hle k) h)), hm', hτdef, resF_smul,
      hσ k, resF_smul, smul_smul]
    simp only [map_pow, resO_resO, ← pow_add]

theorem isQuasicoherent_pushforward_of_qcqs {X : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent := by
  refine isQuasicoherent_of_affineCover _ (fun V : Y.affineOpens => (V : Y.Opens))
    (fun V => V.2) (iSup_affineOpens_eq_top Y) ?_ ?_
  · intro V g
    have hc : IsCompact ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) := f.isCompact_preimage V.2.isCompact
    have hqs : IsQuasiSeparated ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) :=
      f.isQuasiSeparated_preimage V.2.isQuasiSeparated
    have hb : f ⁻¹ᵁ Y.basicOpen g = X.basicOpen (f.app V g) := Scheme.preimage_basicOpen f g
    show ∀ m : Γ(F, f ⁻¹ᵁ Y.basicOpen g), ∃ (e : ℕ) (m' : Γ(F, f ⁻¹ᵁ (V : Y.Opens))),
      resF F ((Opens.map f.base).monotone (Y.basicOpen_le g)) m' =
        f.app (Y.basicOpen g) (resO (Y.basicOpen_le g) g ^ e) • m
    intro m
    obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq_of_qcqs F hc hqs (f.app V g) (resF F hb.ge m)
    refine ⟨e, m', ?_⟩
    have h2 := congrArg (resF F hb.le) hm'
    rw [resF_resF, resF_smul, resF_resF, resF_self, map_pow, resO_resO] at h2
    rw [h2, map_pow, app_resO]
  · intro V g
    have hc : IsCompact ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) := f.isCompact_preimage V.2.isCompact
    have hb : f ⁻¹ᵁ Y.basicOpen g = X.basicOpen (f.app V g) := Scheme.preimage_basicOpen f g
    show ∀ m : Γ(F, f ⁻¹ᵁ (V : Y.Opens)),
      resF F ((Opens.map f.base).monotone (Y.basicOpen_le g)) m = 0 →
        ∃ e : ℕ, f.app V (g ^ e) • m = 0
    intro m hm
    obtain ⟨e, he⟩ := qcoh_exists_pow_smul_eq_zero_of_isCompact F hc (f.app V g) m (by
      have h2 := congrArg (resF F hb.ge) hm
      rw [resF_resF, map_zero] at h2
      exact h2)
    exact ⟨e, by rw [map_pow]; exact he⟩

end

end GroundTheory.Arith.SchemeCoh
