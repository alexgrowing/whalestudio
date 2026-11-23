import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonnegShaOK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyNStageProvisional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeWindow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBaseDataAdmissible
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.RowFormsNZ

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.RowsRestModel

namespace GlobalTheory.Mem.Df.Model

attribute [local instance] GlobalTheory.Mem.Col2.starE

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] (H : HLat K) (σ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module ℂ M]
  (j : H.V →ₛₗ[σ] M) (c : Module.Basis H.ι ℂ M) (hc : ∀ i, c i = j (H.b i))

include hc in
theorem repr_j (x : H.V) (i : H.ι) : c.repr (j x) i = σ (H.b.repr x i) := by
  have h : j x = ∑ k, σ (H.b.repr x k) • c k := by
    conv_lhs => rw [← H.b.sum_repr x, map_sum]
    simp only [LinearMap.map_smulₛₗ, hc]
  rw [h, c.repr_sum_self]

include hc in

theorem exists_coord (hX : ∀ v, IsUnit (H.X v).det) : ∃ e : M ≃ₗ[ℂ] EuclideanSpace ℂ H.ι,
    ∀ x, Formalism.HermitianLatticesTheory.normAt H.b H.X (InfinitePlace.mk σ) x = ‖e (j x)‖ := by
  have key : ∀ Y : Matrix H.ι H.ι ℂ, IsUnit Y.det → ∃ e : M ≃ₗ[ℂ] EuclideanSpace ℂ H.ι,
      ∀ x, ‖e (j x)‖ = Formalism.HermitianLatticesTheory.cnorm (Y.mulVec fun i => σ (H.b.repr x i)) := fun Y hY => by
    refine ⟨(c.equivFun.trans (Matrix.toLinearEquiv' Y (Matrix.invertibleOfIsUnitDet Y hY))).trans
      (WithLp.linearEquiv 2 ℂ (H.ι → ℂ)).symm, fun x => ?_⟩
    have : c.equivFun (j x) = fun i => σ (H.b.repr x i) := funext fun i => repr_j H σ j c hc x i
    rw [EuclideanSpace.norm_eq, LinearEquiv.trans_apply, LinearEquiv.trans_apply, this]
    rfl
  have hU := Matrix.isUnit_nonsing_inv_det _ (hX (InfinitePlace.mk σ))
  rcases InfinitePlace.embedding_mk_eq σ with h | h
  · obtain ⟨e, he⟩ := key _ hU
    refine ⟨e, fun x => ?_⟩
    rw [he]
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
    rw [h]
  · obtain ⟨e, he⟩ := key (((H.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)) (by
      have := hU.map (starRingEnd ℂ)
      rwa [RingHom.map_det] at this)
    refine ⟨e, fun x => ?_⟩
    rw [he]
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt Formalism.HermitianLatticesTheory.cnorm
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.norm_conj]
    congr 2
    simp [Matrix.mulVec, dotProduct, ComplexEmbedding.conjugate_coe_eq]

include hc in

theorem exists_olat (hG : H.Good) {O : Type} [CommRing O] (ι : O →+* K) (hι : ∀ y, IsIntegral ℤ (ι y))
    {N : Type} [AddCommGroup N] [Module ℂ N] (e : M ≃ₗ[ℂ] N) :
    ∃ L : Rows.OLat O (σ.comp ι) N, (∀ y, y ∈ L.carrier ↔ ∃ x ∈ H.L, e (j x) = y) ∧ ∀ y ∈ L.gen, y ∈ L.carrier := by
  classical
  have h1 : (H.L.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 K) H.L := Module.Finite.iff_fg.2 hG.2.1
    have : Module.Finite ℤ H.L := Module.Finite.trans (𝓞 K) H.L
    exact Module.Finite.iff_fg.1 (inferInstanceAs (Module.Finite ℤ H.L))
  obtain ⟨s, hs⟩ := h1
  have hsL : ∀ x ∈ s, x ∈ H.L := fun x hx => by
    have : x ∈ H.L.restrictScalars ℤ := hs ▸ Submodule.subset_span hx
    exact this
  have hgen : ∀ (T : Finset N) (y : N), y ∈ T → ∃ c : N → O, y = ∑ v ∈ T, (σ.comp ι) (c v) • v := fun T y hy =>
    ⟨fun v => if v = y then 1 else 0, by
      rw [Finset.sum_eq_single y (fun v _ h => by simp [h]) (fun h => absurd hy h)]; simp⟩
  have hz : ∀ x ∈ H.L, ∃ c : N → O, e (j x) = ∑ v ∈ s.image (fun x => e (j x)), (σ.comp ι) (c v) • v := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (s : Set H.V) := hs ▸ hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x hx => exact hgen _ _ (Finset.mem_image_of_mem _ hx)
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, ha, hb, ← Finset.sum_add_distrib]; simp [add_smul]⟩
    | smul n x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨fun v => n * a v, ?_⟩
      rw [map_zsmul, map_zsmul, ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [map_mul, map_intCast, mul_smul, Int.cast_smul_eq_zsmul]
  refine ⟨⟨s.image fun x => e (j x), ?_⟩, fun y => ⟨?_, ?_⟩, fun y hy => hgen _ _ hy⟩
  · have h2 : ∀ x : H.V, e (j x) ∈ Submodule.span ℂ ((s.image fun x => e (j x) : Finset N) : Set N) := by
      intro x
      have hx : x ∈ Submodule.span K (H.L : Set H.V) := hG.2.2 ▸ trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha⟩ := hz x hx
        rw [ha]
        exact Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span hv)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
      | smul a x _ hx => rw [LinearMap.map_smulₛₗ, map_smul]; exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff, ← (c.map e).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Module.Basis.map_apply, hc]
    exact h2 _
  · rintro ⟨a, rfl⟩
    refine Finset.sum_induction _ (fun y => ∃ x ∈ H.L, e (j x) = y) ?_ ⟨0, zero_mem _, by simp⟩ ?_
    · rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact ⟨x + y, add_mem hx hy, by simp⟩
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
      let t : 𝓞 K := ⟨ι (a (e (j x))), hι _⟩
      refine ⟨t • x, H.L.smul_mem t (hsL x hx), ?_⟩
      rw [← IsScalarTower.algebraMap_smul K, LinearMap.map_smulₛₗ, map_smul]
      rfl
  · rintro ⟨x, hx, rfl⟩
    exact hz x hx

end Gen

section Pack

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (σ : X.K →+* ℂ)

theorem pack {O : Type} [CommRing O] (ι : O →+* X.K) (hι : ∀ y, IsIntegral ℤ (ι y)) :
    ∃ (n : ℕ) (e : MtP W Ch sel mu P σ ≃ₗ[ℂ] Eu n) (L : Rows.OLat O (σ.comp ι) (Eu n)),
      (∀ x, Formalism.HermitianLatticesTheory.normAt (MtildeH W Ch hX sel mu P).b (MtildeH W Ch hX sel mu P).X (InfinitePlace.mk σ) x =
        ‖e (toMtP W Ch sel mu P σ x)‖) ∧
      (∀ y, y ∈ L.carrier ↔ ∃ x ∈ (MtildeH W Ch hX sel mu P).L, e (toMtP W Ch sel mu P σ x) = y) ∧ ∀ y ∈ L.gen, y ∈ L.carrier := by
  have hG := MtildeH_good W Ch hX sel mu P
  let c : Module.Basis (MtildeH W Ch hX sel mu P).ι ℂ (MtP W Ch sel mu P σ) :=
    basisCForm σ W.sgTrue _ _ hX (MtildeH W Ch hX sel mu P).b
  have hc : ∀ i, c i = toMtP W Ch sel mu P σ ((MtildeH W Ch hX sel mu P).b i) := fun i => basisCForm_apply _ _ _ _ _ _ _
  obtain ⟨e, he⟩ := exists_coord (MtildeH W Ch hX sel mu P) σ (toMtP W Ch sel mu P σ) c hc hG.1
  obtain ⟨L, h1, h2⟩ := exists_olat (MtildeH W Ch hX sel mu P) σ (toMtP W Ch sel mu P σ) c hc hG ι hι e
  exact ⟨_, e, L, he, h1, h2⟩

theorem basis_cx : LinearIndependent ℂ (fun i => toMtP W Ch sel mu P σ ((MtildeH W Ch hX sel mu P).b i)) ∧
    Submodule.span ℂ (Set.range fun i => toMtP W Ch sel mu P σ ((MtildeH W Ch hX sel mu P).b i)) = ⊤ :=
  ⟨toMtilde_linearIndependent W Ch sel mu P σ (MtildeH W Ch hX sel mu P).b.linearIndependent,
    toCForm_span_of_span σ W.sgTrue _ _ hX (MtildeH W Ch hX sel mu P).b.span_eq⟩

omit W Ch hX sel mu P σ in
theorem conj_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (H H' : Subgroup G) (χ : H → ℂ)
    (χ' : H' → ℂ) (t : G) (h : ∀ a : H', ∃ a' : H, a'.1 * t = t * a.1 ∧ χ' a = χ a') (F : V) (hF : F ≠ 0)
    (he : ∀ a : H, ρ a.1 F = χ a • F) : ∃ F' : V, F' ≠ 0 ∧ ∀ a : H', ρ a.1 F' = χ' a • F' := by
  refine ⟨ρ t⁻¹ F, fun h0 => hF ?_, fun a => ?_⟩
  · have h4 := congrArg (ρ t) h0
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero] at h4
  · obtain ⟨a', e1, e2⟩ := h a
    have e3 : a.1 * t⁻¹ = t⁻¹ * a'.1 := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, e1]
    rw [← Module.End.mul_apply, ← map_mul, e3, map_mul, Module.End.mul_apply, he a', map_smul, e2]

omit W Ch hX sel mu P σ in
theorem exists_perm (n k rS : ℕ) (κ : Type) [CommRing κ] : ∃ p : GL (Fin n) κ, ∀ M, toSymOrd κ n k rS M * p = p * M := by
  let s := symPerm n k rS
  refine ⟨⟨(1 : Matrix _ _ κ).submatrix s.symm id, (1 : Matrix _ _ κ).submatrix id s.symm, ?_, ?_⟩, fun M => ?_⟩
  · refine (Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl _) _).trans ?_
    simp
  · rw [Matrix.submatrix_mul_equiv _ _ _ s.symm]
    simp
  · apply Units.ext
    ext i j
    simp only [Units.val_mul, Matrix.mul_apply, toSymOrd_val, Matrix.submatrix_apply, id, Matrix.one_apply]
    rw [← Equiv.sum_comp s]
    simp [s]

omit W hX sel mu P σ in
theorem exists_conj : ∃ t : G0 X.E Pr.vGs R.r, ∀ a : (rPsymF (R := R) Ch).grp, ∃ a' : (rPsym (R := R) Ch).grp,
    a'.1 * t = t * a.1 ∧ (rPsymF (R := R) Ch).chr a = (rPsym (R := R) Ch).chr a' := by
  choose p hp using fun w : {w // w ∈ Pr.vGs} => exists_perm R.r R.k R.rS (𝓞 X.E ⧸ w.1.asIdeal)
  refine ⟨p, fun a => ⟨⟨fun w => toSymOrd _ R.r R.k R.rS (a.1 w), fun w hw => a.2 w hw⟩, funext fun w => hp w (a.1 w), ?_⟩⟩
  rw [LevFam.chr_ev, LevFam.chr_ev]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h1 : a.1 w ∈ (rPsymF (R := R) Ch w).H := a.2 w trivial
  have h2 : toSymOrd _ R.r R.k R.rS (a.1 w) ∈ (rPsym (R := R) Ch w).H := a.2 w trivial
  have h3 : (rPsym (R := R) Ch w).ev (toSymOrd _ R.r R.k R.rS (a.1 w)) = (rPsym (R := R) Ch w).lam ⟨_, h2⟩ := dif_pos h2
  exact (dif_pos h1).trans h3.symm

omit hX P in

theorem nontrivial_symF (h : Nontrivial (MtP W Ch sel mu (rPsym (R := R) Ch) σ)) :
    Nontrivial (MtP W Ch sel mu (rPsymF (R := R) Ch) σ) := by
  obtain ⟨F, hF, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Submodule.nontrivial_iff_ne_bot.1 h)
  obtain ⟨h1, h2⟩ := (mem_MtP_iff W Ch sel mu _ σ F).1 hF
  obtain ⟨t, ht⟩ := exists_conj (R := R) Ch
  obtain ⟨F', h3, h4⟩ := conj_eig (rightTranslationAction W Ch sel mu σ) (rPsym (R := R) Ch).grp (rPsymF (R := R) Ch).grp
    (fun a => σ ((rPsym (R := R) Ch).chr a : X.Kˣ)) (fun a => σ ((rPsymF (R := R) Ch).chr a : X.Kˣ)) t
    (fun a => (ht a).imp fun a' h => ⟨h.1, by rw [h.2]⟩) ⟨F, h1⟩ (fun e => h0 (Submodule.mk_eq_zero _ _ |>.1 e)) h2
  refine Submodule.nontrivial_iff_ne_bot.2 ((Submodule.ne_bot_iff _).2 ⟨F'.1, (mem_MtP_iff W Ch sel mu _ σ _).2 ⟨F'.2, h4⟩, ?_⟩)
  exact fun e => h3 (Subtype.ext e)

end Pack

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (hX : B.fields.Ok)

set_option maxHeartbeats 1000000 in
theorem packI (a : I.ι) : ∃ (n : ℕ) (e : MtCx I a ≃ₗ[ℂ] Eu n) (L : Rows.OLat B.O (B.embLL.comp B.OtoLL) (Eu n)),
    (∀ x, Formalism.HermitianLatticesTheory.normAt (MtHL I hX a).b (MtHL I hX a).X (InfinitePlace.mk B.embLL) x = ‖e (toCx I hX a x)‖) ∧
    (∀ y, y ∈ L.carrier ↔ ∃ x ∈ (MtHL I hX a).L, e (toCx I hX a x) = y) ∧ ∀ y ∈ L.gen, y ∈ L.carrier := by
  have h := pack (X := B.fields) (Pr := B.primes X) B.wts I.Ch hX I.sel (I.tup a) I.Ps B.embLL B.OtoLL B.O_int
  exact h

set_option maxHeartbeats 1000000 in

theorem exists_same (h : I.Ok) (u : B.Word) (a : I.ι) :
    ∃ g : MtCx I a ≃ₗ[ℂ] (I.perIn u a).Mt B.fields.emb B.embLL, ∀ F p, (g F).1 () p = F.1 (toRow I.sel (I.tup a) p.1.1) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) := (LevTwist.levOk_twists B X I h).2.1.mono_right (I.Q_subset_SQ a)
  have g := mtEquiv_apply (X := B.fields) (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.Ps u (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ => 0)
    (fun _ _ _ _ _ _ => 0) B.embLL hd
  exact ⟨_, g⟩

def md (m e j : ℕ) : ℕ := if j = m then e else 0

theorem exists_ka (B : Base) : ∃ (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ),
    ∀ (C : Cols B) (W : RowsRest B C), W.kaBig = kb → W.kaSmall = ks → ∀ V S N G, DV.KapDef (assemble B C W V S N G) := by
  by_cases h : ∃ (C : Cols B) (W : RowsRest B C) (_ : DivStage B C W) (_ : SStage B C W) (_ : NStage B C W), Nonempty (GJStage B C)
  · obtain ⟨C, W, V, S, N, ⟨G⟩⟩ := h
    obtain ⟨kb, ks, hk⟩ := DV.exists_blocks (assemble B C W V S N G)
    refine ⟨kb, ks, fun C' W' h1 h2 V' S' N' G' j _ _ τ => ⟨fun i => ?_, fun c => ?_⟩⟩
    · show ((W'.kaBig j τ i : ℤ) : ℚ) = _
      rw [h1]
      exact (hk j τ).1 i
    · show ((W'.kaSmall j τ c : ℤ) : ℚ) = _
      rw [h2]
      exact (hk j τ).2 c
  · exact ⟨0, 0, fun C W _ _ V S N G => absurd ⟨C, W, V, S, N, ⟨G⟩⟩ h⟩

section Build

variable {C : Cols B} {d₀ : C.Tup → ℕ} (hf : Fits C d₀) (d : C.Tup → ℕ)
  (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Eu (d a)))
  (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] Eu (d C.mu0)) (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] Eu (d a))
  (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ)

theorem md_zero (R : Ranks) (e : ℕ) : md R.m e 0 = 0 := if_neg (by have := R.two_le_m; omega)

def what₂ : RowsRest B C :=
  { model hf 0 0 0 with
    muTw := fun w => if B.places.resChar w = B.host.pde then C.muStar' else C.muStar
    muTw_conj := fun w => by rw [GlobalTheory.Mem.Top.TwFin.resChar_conj]
    muAt_or := fun _ => Or.inl rfl
    Dall := 0
    delp := 0
    delp_le_one := zero_le_one
    D_eq := by simp [model]
    FT := Empty
    instFT := inferInstance
    instFTd := inferInstance
    ft := Fin.elim0
    ft0 := Fin.elim0
    Amb := fun μ => Eu (d μ)
    instAmb := fun _ => inferInstance
    instAmbi := fun _ => inferInstance
    instAmbf := fun _ => inferInstance
    Mult := fun μ j => Eu (md B.R.m (d μ) j)
    instMult := fun _ _ => inferInstance
    instMulti := fun _ _ => inferInstance
    instMultf := fun _ _ => inferInstance
    multZero := fun μ => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr (md_zero B.R (d μ)))
    multTop := fun μ => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr (if_pos rfl))
    io := fun _ _ => 0
    Mtilde := L
    eOp := fun _ => LinearMap.id
    eOp_idem := fun _ => rfl
    eOp_sa := fun _ _ _ => rfl
    perCol := fun u μ φ F => by
      classical
      exact if hμ : μ = C.mu0 then (C.mem u).P.PtilCol (Subtype.val φ) ((e0 u).symm (hμ ▸ F))
        else (C.PTw u μ).PtilCol (C.e0Tw u μ (Subtype.val φ)) ((eT u μ).symm F)
    Bu := fun _ _ _ => 0
    kaBig := kb
    kaSmall := ks
    isot := fun _ _ => ⊤
    lamP := fun _ _ _ => 1
    shaLen := GaloisStage.shaTrue B.host
    shaLen_nonneg := GaloisStage.shaTrue_nonneg B.host
    eMt0 := e0
    perCol_base_eq_PtilCol := fun u φ F => by
      rw [dif_pos rfl]; rfl
    Bu_linL := fun _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
    Bu_linR := fun _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
    eMtTw := eT
    perCol_tie := fun u μ hμ φ F => by
      rw [dif_neg hμ]; rfl }

theorem sub_md (m e j : ℕ) (h : j ≠ m) : Subsingleton (Eu (md m e j)) := by
  rw [md, if_neg h]
  infer_instance

theorem rows_standIn (hk : ∀ V S N G, DV.KapDef (assemble B C (what₂ hf d L e0 eT kb ks) V S N G)) :
    StandIn (what₂ hf d L e0 eT kb ks) where
  drows := rfl
  d0 := rfl
  dall := rfl
  delp := rfl
  ft := ⟨fun x => Empty.elim x⟩
  mult := fun _ _ h => sub_md _ _ _ h
  io := fun _ _ => rfl
  mj := fun _ => inferInstanceAs (Subsingleton (Eu 0))
  mt := fun _ _ => inferInstanceAs (Subsingleton (Eu 0))
  eMt := fun _ _ => rfl
  bu := fun _ _ _ => rfl
  ij := fun _ _ _ => ⟨rfl, rfl⟩
  eta := fun _ _ => rfl
  sha := GlobalTheory.MemN.shaOK_shaTrue B.toPre
  kap := hk

end Build

set_option maxHeartbeats 1000000 in

theorem nonempty_rowsDef (h : I.Ok) : Nonempty (RowsDef I l hX) := by
  choose d e L h1 h2 h3 using packI I hX
  choose g hg using exists_same I h
  obtain ⟨kb, ks, hk⟩ := exists_ka B
  let g' : ∀ u (a : (I.cols l).Tup), MtCx I a ≃ₗ[ℂ] ((I.cols l).PTw u a).Mt := g
  let g0 : ∀ u, MtCx I I.mu0 ≃ₗ[ℂ] ((I.cols l).mem u).P.Mt := fun u => g u I.mu0
  let W : RowsRest B (I.cols l) := what₂ (TrueColsTest.fits l) d L (fun u => (g0 u).symm.trans (e I.mu0))
    (fun u a => (g' u a).symm.trans (e a)) kb ks
  refine ⟨⟨W, e, ⟨fun _ => rfl, fun _ => rfl, fun u F => ?_, fun u a F => ?_, h1, h2, h3, fun _ => rfl, fun _ _ => rfl⟩,
    rows_standIn _ _ _ _ _ _ _ (hk _ _ rfl rfl)⟩⟩
  · have : (W.eMt0 u).symm (e I.mu0 F) = g0 u F := by
      show g0 u ((e I.mu0).symm (e I.mu0 F)) = _
      rw [LinearEquiv.symm_apply_apply]
    intro p
    exact (congrArg (fun G : (I.perIn u I.mu0).Mt B.fields.emb B.embLL => G.1 () p) this).trans (hg u I.mu0 F p)
  · have : (W.eMtTw u a).symm (e a F) = g' u a F := by
      show g' u a ((e a).symm (e a F)) = _
      rw [LinearEquiv.symm_apply_apply]
    intro p
    exact (congrArg (fun G : (I.perIn u a).Mt B.fields.emb B.embLL => G.1 () p) this).trans (hg u a F p)

theorem lat_iff {K : Type} [Field K] [NumberField K] [StarRing K] (H : HLat K) (σ : K →+* ℂ) {N : Type} [AddCommGroup N] [Module ℂ N]
    (j : H.V →ₛₗ[σ] N) (hj : Function.Injective j) {O : Type} [CommRing O] (ι : O →+* K) (hι : ∀ y, IsIntegral ℤ (ι y))
    (L : Rows.OLat O (σ.comp ι) N) (h1 : ∀ y, y ∈ L.carrier ↔ ∃ x ∈ H.L, j x = y) (h2 : ∀ y ∈ L.gen, y ∈ L.carrier) (x : H.V) :
    x ∈ H.L ↔ ∃ c : N → 𝓞 K, j x = ∑ v ∈ L.gen, σ ((c v : 𝓞 K) : K) • v := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := (h1 _).2 ⟨x, hx, rfl⟩
    exact ⟨fun v => ⟨ι (c v), hι _⟩, hc⟩
  · rintro ⟨c, hc⟩
    have : ∃ y ∈ H.L, j y = ∑ v ∈ L.gen, σ ((c v : 𝓞 K) : K) • v := by
      refine Finset.sum_induction _ (fun z => ∃ y ∈ H.L, j y = z) ?_ ⟨0, zero_mem _, map_zero _⟩ ?_
      · rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, add_mem hx hy, map_add _ _ _⟩
      · intro v hv
        obtain ⟨y, hy, rfl⟩ := (h1 v).1 (h2 v hv)
        refine ⟨c (j y) • y, H.L.smul_mem _ hy, ?_⟩
        rw [← IsScalarTower.algebraMap_smul K, LinearMap.map_smulₛₗ]
    obtain ⟨y, hy, e⟩ := this
    rwa [hj (hc.trans e.symm)]

set_option maxHeartbeats 1000000 in
theorem cx_facts (a : I.ι) : ∃ j : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a, (∀ x, j x = toCx I hX a x) ∧ Function.Injective j ∧
    (MtHL I hX a).Good ∧ LinearIndependent ℂ (fun i => j ((MtHL I hX a).b i)) ∧
    Submodule.span ℂ (Set.range fun i => j ((MtHL I hX a).b i)) = ⊤ := by
  have h1 := basis_cx (X := B.fields) (Pr := B.primes X) B.wts I.Ch hX I.sel (I.tup a) I.Ps B.embLL
  have h2 := toMtilde_injective (X := B.fields) (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL
  have h3 := MtildeH_good (X := B.fields) (Pr := B.primes X) B.wts I.Ch hX I.sel (I.tup a) I.Ps
  exact ⟨toMtP (X := B.fields) (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL, fun _ => rfl, h2, h3, h1⟩

set_option maxHeartbeats 1000000 in

theorem exists_ambTrue (Z : TC.Later B (I.cols l)) (e : ∀ a : (I.cols l).Tup, MtCx I a ≃ₗ[ℂ] Z.W.Amb a) (h : DefTrue I l hX Z.W e) :
    ∃ A, AmbTrue I l hX Z e A := by
  choose j hj hinj hG hli hsp using cx_facts I hX
  let J : ∀ a : (I.cols l).Tup, (MtHL I hX a).V →ₛₗ[B.embLL] Z.W.Amb a := fun a => (e a).toLinearMap.comp (j a)
  have hJ : ∀ a x, J a x = e a (toCx I hX a x) := fun a x => congrArg (e a) (hj a x)
  have hl : ∀ a y, y ∈ (Z.W.Mtilde a).carrier ↔ ∃ x ∈ (MtHL I hX a).L, J a x = y := fun a y => by
    simp only [hJ]; exact h.lat a y
  have q1 : ∀ a : (I.cols l).Tup, LinearIndependent ℂ (fun i => J a ((MtHL I hX a).b i)) ∧
      Submodule.span ℂ (Set.range fun i => J a ((MtHL I hX a).b i)) = ⊤ := fun a => ⟨(hli a).map' (e a).toLinearMap (e a).ker, by
    have := congrArg (Submodule.map (e a).toLinearMap) (hsp a)
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at this
    exact this⟩
  have q2 := fun a : (I.cols l).Tup =>
    lat_iff (MtHL I hX a) B.embLL (J a) ((e a).injective.comp (hinj a)) B.OtoLL B.O_int _ (hl a) (h.gen a)
  have q3 : ∀ a : (I.cols l).Tup, ∀ v ∈ (Z.W.Mtilde a).gen, v ∈ Set.range (J a) := fun a v hv => by
    obtain ⟨x, -, hx⟩ := (hl a v).1 (h.gen a v hv)
    exact ⟨x, hx⟩
  have q4 := fun (a : (I.cols l).Tup) x => (h.norm a x).trans (congrArg norm (hJ a x).symm)
  refine ⟨{ MtH := fun a => MtHL I hX a
            jAmb := J
            MtH_good := fun a _ => hG a
            jAmb_basis := fun a _ => q1 a
            jAmb_lat := fun a _ => q2 a
            jAmb_gen := fun a _ => q3 a
            jAmb_norm := fun a _ => q4 a }, ⟨fun a => ?_⟩⟩
  exact congrArg (fun f => (⟨MtHL I hX a, f⟩ : Σ H : HLat B.LL, (H.V → Z.W.Amb a))) (funext (hJ a))

theorem exists_later (hB : StagesInhab.HasLetters B.toPre) (Rw : RowsDef I l hX) : ∃ Z : TC.Later B (I.cols l), Z.W = Rw.W := by
  obtain ⟨Del, letter, hD, hinj, gap, hu⟩ := hB
  obtain ⟨N⟩ := GlobalTheory.MemN.nonempty_nStage_provisional B _ Rw.W (fun _ _ _ => 1) Rw.std.sha (fun j w _ _ => Rw.std.eta j w)
    (Or.inl (GlobalTheory.MemN.goodChi _ _))
  obtain ⟨V, -⟩ := DivInhab.exists_divStage B _ Rw.W
  obtain ⟨S⟩ := SStageInhab.nonempty_sStage B _ Rw.W Del hD gap letter hinj hu
    (fun u x _ y _ => TrueColsTest.ipC_herm l u x y) (fun u x hx h => TrueColsTest.ipC_pos l u x hx h)
    (by rw [Rw.std.drows]; exact Nat.zero_le _)
  obtain ⟨G⟩ := GJInhab.nonempty_stage B (I.cols l)
  exact ⟨⟨Rw.W, V, S, N, G⟩, rfl⟩

set_option maxHeartbeats 1000000 in
include hX in

theorem nontrivial_reference_forms (h : I.Ok) : Nontrivial (MtCx I I.mu0) := by
  have hD := GlobalTheory.T.definiteBaseData_admissible B X I.Ch h.ch_ok h.fromHecke
  have hs : XiSign (B.primes X) I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) := by
    rw [I.trueColumn_tuple_trivial_eq_one]
    exact signCondition_trivialTuple I.sel I.S
  have h1 := (hD.rowsNonzero I.sel (I.tup I.mu0) hs (rPsym I.Ch) (rPsym_le I.Ch)).1
  have h2 := finrank_MtP (X := B.fields) (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) (rPsym I.Ch) B.embLL hX
  exact nontrivial_symF (X := B.fields) (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) B.embLL
    (Module.nontrivial_of_finrank_pos (R := ℂ) (h2.symm ▸ h1))

theorem buDef_iff (Rw : RowsDef I l hX) : Rows.BuDef Rw.W.what₂ ↔ ∀ u φ F, Rw.W.perCol u (I.cols l).mu0 φ F = 0 := by
  constructor
  · intro h u φ F
    have hF : F ∈ Rw.W.what₂.V0 (I.cols l).mu0 := ⟨F, LinearMap.congr_fun (Rw.tru.eOp _) F⟩
    exact (h u φ F hF).trans (Rw.std.bu _ _ _)
  · intro h u φ F _
    exact (h u φ F).trans (Rw.std.bu _ _ _).symm

theorem exists_all : ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (hX : B.fields.Ok) (Z : TC.Later B (I.cols l))
    (e : ∀ a : (I.cols l).Tup, MtCx I a ≃ₗ[ℂ] Z.W.Amb a) (A : AmbForm (I.rec7 l Z) (RowSide.sharp (I.rec7 l Z))),
    I.Ok ∧ TC.Pins B X ∧ I.muStar ≠ I.mu0 ∧ DefTrue I l hX Z.W e ∧ StandIn Z.W ∧ AmbTrue I l hX Z e A ∧
      Nontrivial (Z.W.Amb (I.cols l).mu0) := by
  obtain ⟨B, X, I, hL, h, hP, hs⟩ := TrueColsTest.exists_ok_pins
  have hX := (base_fields_primes_ok B X).1
  have l := TrueColsTest.laws h
  obtain ⟨Rw⟩ := nonempty_rowsDef I l hX h
  obtain ⟨⟨W, V, S, N, G⟩, hZ⟩ := exists_later I l hX hL Rw
  obtain rfl : W = Rw.W := hZ
  obtain ⟨A, hA⟩ := exists_ambTrue I l hX ⟨Rw.W, V, S, N, G⟩ Rw.e Rw.tru
  have : Nontrivial (MtCx I (I.cols l).mu0) := nontrivial_reference_forms I hX h
  exact ⟨B, X, I, l, hX, ⟨Rw.W, V, S, N, G⟩, Rw.e, A, h, hP, hs, Rw.tru, Rw.std, hA, (Rw.e (I.cols l).mu0).symm.toEquiv.nontrivial⟩

end GlobalTheory.Mem.Df.Model

end
