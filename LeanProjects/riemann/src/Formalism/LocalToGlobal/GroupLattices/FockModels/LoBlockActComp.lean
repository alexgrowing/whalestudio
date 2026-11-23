import Formalism.LocalToGlobal.GroupLattices.FockModels.MkP

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems MvPolynomial Formalism.G0

theorem lo_blockAct_comp (K : Type) [CommRing K] {S : Type} {k n : ℕ} (M N : S → Matrix (Fin k) (Fin k) K) :
    (blockAct K (n := n) M).comp (blockAct K N) = blockAct K (fun s => N s * M s) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, blockAct, aeval_X, map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_eq,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← mul_assoc, ← map_mul]

theorem lo_blockAct_one (K : Type) [CommRing K] {S : Type} {k n : ℕ} :
    blockAct K (S := S) (k := k) (n := n) (fun _ => 1) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [blockAct, aeval_X, Matrix.one_apply]

variable {p : ℕ}

theorem lo_loc_inv (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (z : Pol G v) :
    je_loc G v A⁻¹ (je_loc G v A z) = z := by
  have hinv : ∀ s, je_g G v A⁻¹ s = (je_g G v A s)⁻¹ := fun s => je_gPos_inv G v A s
  rw [je_loc_apply, je_loc_apply, map_smul, smul_smul]
  have hc : ∀ s, (je_g G v A s)⁻¹⁻¹ = je_g G v A s := fun s =>
    Matrix.nonsing_inv_nonsing_inv _ (je_g_det G v A s)
  simp only [hinv, hc]
  have hcomp := congrArg (fun f => f z)
    (lo_blockAct_comp G.Kf (n := G.P.m + 1) (fun s => je_g G v A s) (fun s => (je_g G v A s)⁻¹))
  simp only [AlgHom.comp_apply] at hcomp
  rw [hcomp]
  have h1 : (fun s => (je_g G v A s)⁻¹ * je_g G v A s) = fun _ => 1 := by
    funext s; exact Matrix.nonsing_inv_mul _ (je_g_det G v A s)
  rw [h1, lo_blockAct_one, AlgHom.id_apply]
  rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_eq_one (fun s _ => ?_), one_smul]
  have hd : (je_g G v A s).det ≠ 0 := (je_g_det G v A s).ne_zero
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← mul_zpow, inv_mul_cancel₀ hd, one_zpow]

theorem lo_locV_inv (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (x : Vsp G.Kf (G.P.lam0 v)) : je_locV G v A⁻¹ (je_locV G v A x) = x := Subtype.ext (lo_loc_inv G v A (x : Pol G v))

def lo_edge (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1)) : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1) :=
  ⟨e.src.map (nt_phi (G.P.W v) A), e.tgt.map (nt_phi (G.P.W v) A)⟩

theorem lo_edge_inv' (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1)) : lo_edge G v A (lo_edge G v A⁻¹ e) = e := by
  have hm : ∀ S : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v),
      (S.map (nt_phi (G.P.W v) A⁻¹)).map (nt_phi (G.P.W v) A) = S := by
    intro S
    rw [← Submodule.map_comp]
    have : (nt_phi (G.P.W v) A).comp (nt_phi (G.P.W v) A⁻¹) = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, nt_phi, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
        Matrix.mulVec_mulVec, LinearMap.id_apply]
      rw [Units.mul_inv, Matrix.one_mulVec]
    rw [this, Submodule.map_id]
  cases e with
  | mk src tgt =>
    simp only [lo_edge, hm]

theorem lo_isEdge (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1)) (he : IsEdge p (G.P.n' v) G.P.r e) :
    IsEdge p (G.P.n' v) G.P.r (lo_edge G v A e) := by
  have hid1 : (nt_phi (G.P.W v) A).comp (nt_phi (G.P.W v) A⁻¹) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, nt_phi, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, LinearMap.id_apply]
    rw [Units.mul_inv, Matrix.one_mulVec]
  have hid2 : (nt_phi (G.P.W v) A⁻¹).comp (nt_phi (G.P.W v) A) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, nt_phi, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, LinearMap.id_apply]
    rw [Units.inv_mul, Matrix.one_mulVec]
  have hmm : ∀ S : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v), (S.map (nt_phi (G.P.W v) A)).map (nt_phi (G.P.W v) A⁻¹) = S := by
    intro S; rw [← Submodule.map_comp, hid2, Submodule.map_id]
  obtain ⟨hs, ht, hle, hpp, hcard⟩ := he
  have hlat : ∀ S : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v), IsLattice (G.P.W v) S → IsLattice (G.P.W v) (S.map (nt_phi (G.P.W v) A)) := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨(A : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) * g, ?_, ?_⟩
    · rw [Matrix.det_mul]; exact (Matrix.isUnits_det_units A).mul hg
    · unfold colSpan
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
  let φe : (Fin (G.P.m + 1) → G.P.Qq v) ≃ₗ[(G.P.W v)] (Fin (G.P.m + 1) → G.P.Qq v) := LinearEquiv.ofLinear (nt_phi (G.P.W v) A) (nt_phi (G.P.W v) A⁻¹) hid1 hid2
  refine ⟨hlat _ hs, hlat _ ht, Submodule.map_mono hle, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨(p : (G.P.W v)) • x, hpp x hx, map_smul _ _ _⟩
  · rw [← hcard]
    show Nat.card (↥(e.tgt.map (φe : (Fin (G.P.m + 1) → G.P.Qq v) →ₗ[(G.P.W v)] (Fin (G.P.m + 1) → G.P.Qq v))) ⧸ _) = _
    have hPQ : (Submodule.comap e.tgt.subtype e.src).map (φe.submoduleMap e.tgt : ↥e.tgt →ₗ[(G.P.W v)] _) =
        Submodule.comap (e.tgt.map (φe : (Fin (G.P.m + 1) → G.P.Qq v) →ₗ[(G.P.W v)] (Fin (G.P.m + 1) → G.P.Qq v))).subtype
          (e.src.map (φe : (Fin (G.P.m + 1) → G.P.Qq v) →ₗ[(G.P.W v)] (Fin (G.P.m + 1) → G.P.Qq v))) := by
      ext y
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, by simp⟩
      · rintro ⟨z, hz, hzy⟩
        obtain ⟨x, hx, hxy⟩ := y.2
        refine ⟨⟨x, hx⟩, ?_, Subtype.ext (by simpa using hxy)⟩
        have hzx : z = x := φe.injective (hzy.trans hxy.symm)
        have hxs : x ∈ e.src := hzx ▸ hz
        exact hxs
    exact (Nat.card_congr (Submodule.Quotient.equiv _ _ (φe.submoduleMap e.tgt) hPQ).toEquiv).symm

theorem lo_Re (G : GAtP p) (v : Fin G.P.nV) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1)) (he : IsEdge p (G.P.n' v) G.P.r e) (x : Vsp G.Kf (G.P.lam0 v))
    (hx : x ∈ Re (O := G.O) p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) e) :
    je_locV G v A x ∈ Re (O := G.O) p (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) (lo_edge G v A e) := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨je_locV G v A y, ?_, ?_⟩
  · simp only [HLe, toV, SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      Submodule.subtype_apply]
    rw [je_locV_coe]
    cases e with
    | mk S T => exact je_H_Le G v A S T he _ hy
  · simp [LinearMap.lsmul_apply, map_smul]

theorem lo_Nsrc (G : GAtP p) (v : Fin G.P.nV) (tv : ℕ) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (Lv : Lat G v)
    (hLv : IsLattice (G.P.W v) Lv) (x : Vsp G.Kf (G.P.lam0 v))
    (hx : x ∈ Nsrc (O := G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv Lv) :
    je_locV G v A x ∈ Nsrc (O := G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv
      (Lv.map (nt_phi (G.P.W v) A)) := by
  have hid1 : (nt_phi (G.P.W v) A).comp (nt_phi (G.P.W v) A⁻¹) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, nt_phi, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, LinearMap.id_apply]
    rw [Units.mul_inv, Matrix.one_mulVec]
  have hid2 : (nt_phi (G.P.W v) A⁻¹).comp (nt_phi (G.P.W v) A) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, nt_phi, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, LinearMap.id_apply]
    rw [Units.inv_mul, Matrix.one_mulVec]
  have hmm : ∀ S : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v), (S.map (nt_phi (G.P.W v) A)).map (nt_phi (G.P.W v) A⁻¹) = S := by
    intro S; rw [← Submodule.map_comp, hid2, Submodule.map_id]
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hx1
    refine ⟨je_locV G v A y, ?_, ?_⟩
    · simp only [HL, toV, SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
        Submodule.subtype_apply]
      rw [je_locV_coe]
      exact je_H_ext G v A Lv hLv _ hy
    · simp [LinearMap.lsmul_apply, map_smul]
  · rw [Submodule.mem_iInf] at hx2 ⊢
    intro e'
    rw [Submodule.mem_iInf]
    rintro ⟨he', hsrc⟩
    have hE := lo_isEdge G v A⁻¹ e' he'
    have hsrc'' : (lo_edge G v A⁻¹ e').src = Lv := by
      show e'.src.map (nt_phi (G.P.W v) A⁻¹) = Lv
      rw [hsrc, hmm]
    have hx3 := (Submodule.mem_iInf _).1 (hx2 (lo_edge G v A⁻¹ e')) ⟨hE, hsrc''⟩
    have := lo_Re G v A (lo_edge G v A⁻¹ e') hE x hx3
    rwa [lo_edge_inv'] at this

theorem lo_Ntgt (G : GAtP p) (v : Fin G.P.nV) (tv : ℕ) (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (Lv : Lat G v)
    (hLv : IsLattice (G.P.W v) Lv) (φ : Module.Dual G.Kf (Vsp G.Kf (G.P.lam0 v)))
    (hφ : φ ∈ Ntgt (O := G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv
      (Lv.map (nt_phi (G.P.W v) A))) :
    (je_locV G v A).dualMap φ ∈
      Ntgt (O := G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) tv Lv := by
  have hid1 : (nt_phi (G.P.W v) A).comp (nt_phi (G.P.W v) A⁻¹) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, nt_phi, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, LinearMap.id_apply]
    rw [Units.mul_inv, Matrix.one_mulVec]
  have hid2 : (nt_phi (G.P.W v) A⁻¹).comp (nt_phi (G.P.W v) A) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, nt_phi, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, LinearMap.id_apply]
    rw [Units.inv_mul, Matrix.one_mulVec]
  have hmm : ∀ S : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v), (S.map (nt_phi (G.P.W v) A)).map (nt_phi (G.P.W v) A⁻¹) = S := by
    intro S; rw [← Submodule.map_comp, hid2, Submodule.map_id]
  obtain ⟨hφ1, hφ2⟩ := Submodule.mem_inf.1 hφ
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · obtain ⟨ψ, hψ, rfl⟩ := hφ1
    refine ⟨(je_locV G v A).dualMap ψ, ?_, ?_⟩
    · intro x hx
      refine hψ (je_locV G v A x) ?_
      simp only [HL, toV, SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
        Submodule.subtype_apply]
      rw [je_locV_coe]
      exact je_H_ext G v A Lv hLv _ hx
    · ext x
      simp [LinearMap.lsmul_apply, LinearMap.dualMap_apply]
  · rw [Submodule.mem_iInf] at hφ2 ⊢
    intro e
    rw [Submodule.mem_iInf]
    rintro ⟨he, htgt⟩
    have hE := lo_isEdge G v A e he
    have htgt' : (lo_edge G v A e).tgt = Lv.map (nt_phi (G.P.W v) A) := by
      show e.tgt.map (nt_phi (G.P.W v) A) = _
      rw [htgt]
    obtain ⟨ψ, hψ, hψφ⟩ := (Submodule.mem_iInf _).1 (hφ2 (lo_edge G v A e)) ⟨hE, htgt'⟩
    rw [← hψφ]
    refine ⟨(je_locV G v A).dualMap ψ, ?_, ?_⟩
    · intro x hx
      refine hψ (je_locV G v A x) ?_
      simp only [HLe, toV, SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
        Submodule.subtype_apply]
      rw [je_locV_coe]
      cases e with
      | mk S T => exact je_H_Le G v A S T he _ hx
    · ext x
      simp [LinearMap.lsmul_apply, LinearMap.dualMap_apply]

theorem lo_at (G : GAtP p) (v : Fin G.P.nV) (t D : ℕ) (κ : ℝ) (cStar : ℕ)
    (A : GL (Fin (G.P.m + 1)) (G.P.Qq v)) (L : Lat G v) (hL : IsLattice (G.P.W v) L)
    (h : LPprimeAt (O := G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) t D κ cStar L) :
    LPprimeAt (O := G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) t D κ cStar
      (L.map (nt_phi (G.P.W v) A)) := by
  have hid1 : (nt_phi (G.P.W v) A).comp (nt_phi (G.P.W v) A⁻¹) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, nt_phi, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, LinearMap.id_apply]
    rw [Units.mul_inv, Matrix.one_mulVec]
  have hid2 : (nt_phi (G.P.W v) A⁻¹).comp (nt_phi (G.P.W v) A) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, nt_phi, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, LinearMap.id_apply]
    rw [Units.inv_mul, Matrix.one_mulVec]
  have hmm : ∀ S : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v), (S.map (nt_phi (G.P.W v) A)).map (nt_phi (G.P.W v) A⁻¹) = S := by
    intro S; rw [← Submodule.map_comp, hid2, Submodule.map_id]
  have hlat : ∀ S : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v), IsLattice (G.P.W v) S → IsLattice (G.P.W v) (S.map (nt_phi (G.P.W v) A)) := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨(A : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) * g, ?_, ?_⟩
    · rw [Matrix.det_mul]; exact (Matrix.isUnits_det_units A).mul hg
    · unfold colSpan
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
  obtain ⟨M, e, F, h1, h2, h3, n, hn, u, Mm, hu⟩ := h
  refine ⟨M, fun i => lo_edge G v A (e i), fun i => je_locV G v A (F i),
    fun i => ⟨lo_isEdge G v A (e i) (h1 i).1, ?_⟩, fun i => ?_, fun i e' he' hsrc hne => ?_, n, hn, ?_⟩
  · show (e i).tgt.map (nt_phi (G.P.W v) A) = _
    rw [(h1 i).2]
  · exact lo_Nsrc G v t A (e i).src (h1 i).1.1 (F i) (h2 i)
  · have hE := lo_isEdge G v A⁻¹ e' he'
    have hsrc'' : (lo_edge G v A⁻¹ e').src = (e i).src := by
      show e'.src.map (nt_phi (G.P.W v) A⁻¹) = _
      rw [hsrc]
      exact hmm _
    have hne'' : lo_edge G v A⁻¹ e' ≠ e i := by
      intro heq
      apply hne
      show e' = lo_edge G v A (e i)
      rw [← heq, lo_edge_inv']
    obtain ⟨y, hy, hyF⟩ := h3 i _ hE hsrc'' hne''
    have hR := lo_Re G v A _ hE y hy
    rw [lo_edge_inv'] at hR
    refine ⟨je_locV G v A y, hR, ?_⟩
    show _ = je_locV G v A (F i)
    rw [← hyF]
    simp [LinearMap.lsmul_apply, map_smul]
  · have hAL : (L.map (nt_phi (G.P.W v) A)).map (nt_phi (G.P.W v) A⁻¹) = L := hmm L
    have hLA := hlat L hL
    let T := LinearMap.codRestrict
      (Ntgt (O := G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) t (L.map (nt_phi (G.P.W v) A)))
      ((((je_locV G v A⁻¹).dualMap).restrictScalars G.O).comp
        (Ntgt (O := G.O) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) t L).subtype)
      (fun ψ => lo_Ntgt G v t A⁻¹ (L.map (nt_phi (G.P.W v) A)) hLA ψ (by rw [hAL]; exact ψ.2))
    refine ⟨T.comp u, Mm, fun x j => ?_⟩
    rw [← hu x j]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    show ((je_locV G v A⁻¹).dualMap (u x : Module.Dual G.Kf (Vsp G.Kf (G.P.lam0 v))))
        (((p : G.Kf) ^ Ar G.P.r (G.P.lam0 v)) • je_locV G v A (F i)) =
      (u x : Module.Dual G.Kf (Vsp G.Kf (G.P.lam0 v))) (((p : G.Kf) ^ Ar G.P.r (G.P.lam0 v)) • F i)
    rw [LinearMap.dualMap_apply, map_smul, lo_locV_inv]

theorem lo_trans {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}
    (L L1 : Submodule W (Fin k → Qq)) (hL : IsLattice W L) (hL1 : IsLattice W L1) :
    ∃ A : GL (Fin k) Qq, L1 = L.map (nt_phi W A) := by
  obtain ⟨g, hg, rfl⟩ := hL
  obtain ⟨g1, hg1, rfl⟩ := hL1
  refine ⟨⟨g1 * g⁻¹, g * g1⁻¹, ?_, ?_⟩, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc g⁻¹, Matrix.nonsing_inv_mul _ hg, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hg1]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc g1⁻¹, Matrix.nonsing_inv_mul _ hg1, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hg]
  · unfold colSpan
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext c
    funext i
    simp only [Function.comp_apply, nt_phi, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      Units.val_mk]
    rw [Matrix.mulVec, dotProduct, ← Matrix.mul_apply, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg,
      Matrix.mul_one]

theorem lPOneEvery : LPOneEvery := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS m r lam0 t D κ cStar hd h
  obtain ⟨hc, L, hL, hat⟩ := h
  refine ⟨hc, fun L1 hL1 => ?_⟩
  obtain ⟨A, rfl⟩ := lo_trans L L1 hL hL1
  exact lo_at (mkG hS m r lam0 hd) (0 : Fin 1) t D κ cStar A L hL hat

end Formalism.L2.G.Model
