import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAllComparison
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex

set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelUnique

theorem mem_map_prod {O S : Type} [CommRing O] [IsDedekindDomain O] [CommRing S] (f : O →+* S)
    (T : Finset (HeightOneSpectrum O)) {s : S} (h : ∀ P ∈ T, s ∈ P.asIdeal.map f) :
    s ∈ (∏ P ∈ T, P.asIdeal).map f := by
  have e : (∏ P ∈ T, P.asIdeal).map f = ∏ P ∈ T, P.asIdeal.map f := map_prod (Ideal.mapHom f) _ _
  rw [e, Ideal.prod_eq_iInf_of_pairwise_isCoprime (J := fun P : HeightOneSpectrum O => P.asIdeal.map f) fun P _ Q _ hne =>
    (HeightOneSpectrum.isCoprime_of_ne P Q hne).map (Ideal.mapHom f)]
  exact Ideal.mem_iInf.2 fun P => Ideal.mem_iInf.2 fun hP => h P hP

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem sub_mem_idS {P : Pl E} {s t : Formalism.L2.Herm.intAf F E} (h : resS F P s = resS F P t) : s - t ∈ idS F P.asIdeal :=
  Ideal.Quotient.eq.1 ((RingEquiv.ofBijective (cmpS F P.asIdeal) (cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective h)

theorem exists_matrix (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)}) {y y' : GL (Fin n) (Formalism.L2.Herm.intAf F E)}
    (h : ∀ P ∈ T, Formalism.UG.bc (resS F P) y = Formalism.UG.bc (resS F P) y') {b : 𝓞 E} (hb : b ∈ J) :
    ∃ s : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E), oToS F E b • (y.1 - y'.1) = M • s := by
  have key : ∀ i j, ∃ c, oToS F E b * (y.1 i j - y'.1 i j) = M • c := by
    intro i j
    have h1 : y.1 i j - y'.1 i j ∈ (∏ P ∈ T, P.asIdeal).map (oToS F E) :=
      mem_map_prod _ T fun P hP => sub_mem_idS (congrArg (fun g : GL (Fin n) (kP P) => g.1 i j) (h P hP))
    have h2 := Ideal.mul_mem_mul h1 (Ideal.mem_map_of_mem (oToS F E) hb)
    rw [← Ideal.map_mul, hJ, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton'] at h2
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by rw [mul_comm, ← hc, nsmul_eq_mul, mul_comm]⟩
  choose c hc using key
  exact ⟨Matrix.of c, Matrix.ext fun i j => hc i j⟩

end Res

theorem conj_mulVec_mem {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) (s : Matrix (Fin n) (Fin n) S)
    (z : Fin n → R) (hz : ∀ j, ((β⁻¹).1 *ᵥ z) j ∈ S) (i : Fin n) :
    ((β⁻¹).1 *ᵥ ((β.1 * s.map S.subtype * (β⁻¹).1) *ᵥ z)) i ∈ S := by
  rw [Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, ← Matrix.mulVec_mulVec]
  generalize (β⁻¹).1 *ᵥ z = w at hz
  exact Subring.sum_mem S (t := Finset.univ) (f := fun j => (s i j : R) * w j) fun j _ => mul_mem (s i j).2 (hz j)

theorem conj_smul_sub {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) {y y' : GL (Fin n) S}
    {s : Matrix (Fin n) (Fin n) S} {b : S} {M : ℕ} (h : b • (y.1 - y'.1) = M • s) :
    (b : R) • ((β * Formalism.UG.bc S.subtype y * β⁻¹).1 - (β * Formalism.UG.bc S.subtype y' * β⁻¹).1) =
      M • (β.1 * s.map S.subtype * (β⁻¹).1) := by
  have e : (b : R) • ((Formalism.UG.bc S.subtype y).1 - (Formalism.UG.bc S.subtype y').1) = M • s.map S.subtype := by
    ext i j
    have := congrArg (fun m : Matrix (Fin n) (Fin n) S => S.subtype (m i j)) h
    simp only [Matrix.smul_apply, map_nsmul, smul_eq_mul, map_mul, Matrix.sub_apply, map_sub] at this
    exact this
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, ← sub_mul, ← mul_sub, ← smul_mul_assoc, ← mul_smul_comm, e,
    mul_smul_comm, smul_mul_assoc]

theorem exists_matrix_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ} (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)})
    {x x' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hx : x ∈ St β) (hx' : x' ∈ St β)
    (h : ∀ P ∈ T, redFn β P x = redFn β P x') {b : 𝓞 E} (hb : b ∈ J)
    {K K' : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, x.1 i j = Algebra.TensorProduct.comm F _ E (K i j))
    (hK' : ∀ i j, x'.1 i j = Algebra.TensorProduct.comm F _ E (K' i j)) :
    ∃ N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E),
      (∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), N *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) ∧
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) • (K - K') = M • N := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hx'
  simp only [redFn_frGL] at h
  obtain ⟨s, hs⟩ := exists_matrix T hJ h hb
  have e := conj_smul_sub _ β hs
  have hN := fun z hz => (hfr _).2 (conj_mulVec_mem _ β s z ((hfr z).1 hz))
  generalize β.1 * s.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 = N at e hN
  refine ⟨N.map (Algebra.TensorProduct.comm F _ E).symm, fun z hz => ?_, Matrix.ext fun i j => ?_⟩
  · have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ (hN _ (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz))
    convert h4 using 1
    funext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, AlgEquiv.symm_apply_apply, Matrix.map_apply]
  · apply (Algebra.TensorProduct.comm F _ E).injective
    rw [Matrix.smul_apply, Matrix.smul_apply, map_nsmul, Matrix.map_apply, AlgEquiv.apply_symm_apply, smul_eq_mul, map_mul,
      Matrix.sub_apply, map_sub, ← hK, ← hK']
    exact congrFun (congrFun e i) j

variable {D : D7}

theorem mulVec_mem_latGHat {V : HSp D} (N : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    (h : ∀ z ∈ latHat V, N *ᵥ z ∈ latHat V) : ∀ z ∈ latGHat V 1, N *ᵥ z ∈ latGHat V 1 := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, _, ⟨z, hz, rfl⟩, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a, ha, _, ⟨_, h z hz, rfl⟩, ?_⟩
    rw [GlobalTheory.Member.LatMove.fin_one, GlobalTheory.Member.LatMove.fin_one]
    exact Matrix.mulVec_smul N ((1 : Af D.host.F) ⊗ₜ[D.host.F] a) z
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem exists_cong {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (T : Finset (Pl D.host.E)) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)}) {k k' : GA D V}
    (hk : Lev.finE V k ∈ St β) (hk' : Lev.finE V k' ∈ St β)
    (h : ∀ P ∈ T, redFn β P (Lev.finE V k) = redFn β P (Lev.finE V k')) {b : 𝓞 D.host.E} (hb : b ∈ J) :
    ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • ((finHom V k).1 *ᵥ z - (finHom V k').1 *ᵥ z) = M • w := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨N, hN, e⟩ := exists_matrix_hat hfr T hJ hk hk' h hb (K := (finHom V k).1) (K' := (finHom V k').1)
    (fun _ _ => rfl) (fun _ _ => rfl)
  rw [← hl] at hN
  intro z hz
  refine ⟨_, mulVec_mem_latGHat _ hN z hz, ?_⟩
  rw [← Matrix.sub_mulVec, ← Matrix.smul_mulVec, e, Matrix.smul_mulVec]

theorem redFn_eq_of_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (hr : V.rank = L.r)
    {g : G0 L.Pg L.r} {k k' : GA D V} (hk : Lev.IsLevelLift V β L g k) (hk' : Lev.IsLevelLift V β L g k') :
    ∀ P ∈ L.Pg, redFn β P (Lev.finE V k) = redFn β P (Lev.finE V k') := by
  intro P hP
  have e : upperLeftBlock L.hr (redFn β P (Lev.finE V k)) = upperLeftBlock L.hr (redFn β P (Lev.finE V k')) :=
    congrFun (hk.2.2.trans hk'.2.2.symm) ⟨P, hP⟩
  have e' := congrArg Units.val e
  rw [upper_block_val_submatrix _ (blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP)),
    upper_block_val_submatrix _ (blockTri_blkOf_le _ _ (parLev_g hk'.2.1 hP))] at e'
  exact Units.ext (Matrix.ext fun i j => congrFun (congrFun e' (Fin.cast hr i)) (Fin.cast hr j))

theorem sub_eq_nsmul {R : Type} [CommRing R] {n : ℕ} {K K' : Matrix (Fin n) (Fin n) R} {t : R} {x x' z w₁ w₂ w₃ : Fin n → R}
    {M : ℕ} (e₁ : x - K *ᵥ (t • z) = M • w₁) (e₂ : x' - K' *ᵥ (t • z) = M • w₂) (e₃ : t • (K *ᵥ z - K' *ᵥ z) = M • w₃) :
    x - x' = M • (w₁ - w₂ + w₃) := by
  rw [smul_add, smul_sub M, ← e₁, ← e₂, ← e₃, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_sub]
  abel

theorem sub_mem_of_approx {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {I J : Ideal (𝓞 D.host.E)} {M : ℕ} (hM : 0 < M)
    (hI : (M : 𝓞 D.host.E) ∈ I) (hIJ : I ⊔ J = ⊤)
    {K K' : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ b ∈ J, ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((b : 𝓞 D.host.E) : D.host.E)) • (K *ᵥ z - K' *ᵥ z) = M • w)
    {f f' : La →ₗ[𝓞 D.host.E] La}
    (hf : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (f a)) - K *ᵥ finVec V (ι a) = M • w)
    (hf' : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (f' a)) - K' *ᵥ finVec V (ι a) = M • w) (a : La) :
    f a - f' a ∈ I • (⊤ : Submodule (𝓞 D.host.E) La) := by
  have hm : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  have h5 := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1
  obtain ⟨u, hu, b, hb, hub⟩ := Submodule.mem_sup.1 (hIJ ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ I ⊔ J)
  rw [← one_smul (𝓞 D.host.E) (f a - f' a), ← hub, add_smul]
  refine add_mem (Submodule.smul_mem_smul hu Submodule.mem_top) ?_
  obtain ⟨w₁, hw₁, e₁⟩ := hf (b • a) (Submodule.smul_mem_smul hb Submodule.mem_top)
  obtain ⟨w₂, hw₂, e₂⟩ := hf' (b • a) (Submodule.smul_mem_smul hb Submodule.mem_top)
  obtain ⟨w₃, hw₃, e₃⟩ := h b hb _ ((GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hm a))
  have e₀ : finVec V (ι (b • a)) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • finVec V (ι a) := by
    rw [map_smul]; exact GlobalTheory.AdLat.Tower.fv_smul b (ι a)
  have e₄ : finVec V (ι (b • (f a - f' a))) = finVec V (ι (f (b • a))) - finVec V (ι (f' (b • a))) := by
    rw [smul_sub, ← map_smul f, ← map_smul f', map_sub]; exact GlobalTheory.AdLat.Tower.fv_sub _ _
  have e₅ : finVec V (ι (b • (f a - f' a))) = M • (w₁ - w₂ + w₃) := by
    rw [e₀] at e₁ e₂
    exact e₄.trans (sub_eq_nsmul e₁ e₂ e₃)
  obtain ⟨⟨v, hv⟩, ev⟩ := GlobalTheory.AdLat.Tower.exists_div (F := D.host.F) (M := latG V 1)
    (fun v => h5 ▸ (GlobalTheory.Member.LatMove.mem_lat_iff V 1 v).symm) hM ⟨_, hm (b • (f a - f' a))⟩
    (h5 ▸ add_mem (sub_mem hw₁ hw₂) hw₃) e₅
  obtain ⟨c, rfl⟩ : v ∈ LinearMap.range ι := hι.2 ▸ hv
  have e₆ : b • (f a - f' a) = (M : 𝓞 D.host.E) • c := by
    apply hι.1
    rw [Nat.cast_smul_eq_nsmul, map_nsmul]
    exact congrArg Subtype.val ev
  rw [e₆]
  exact Submodule.smul_mem_smul hI Submodule.mem_top

theorem levUnique (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (hL : R.toLevCh.Is A.μ0) (hT : LawsJ T)
    (hM : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal) (i : Fin D.R.m) : GlobalTheory.OneMapAllCompare.LevUnique T R i := by
  intro lev lev' h h' g a
  obtain ⟨k, hk, hf⟩ := h g
  obtain ⟨k', hk', hf'⟩ := h' g
  have hp : T.Q.l.Mb * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)} := T.Q.l.prod
  have hp' : (∏ PP ∈ R.Pg, PP.asIdeal) * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)} := by rw [← hM]; exact hp
  have hI : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb :=
    (hp.ge.trans (Ideal.mul_le_inf.trans inf_le_left)) (Ideal.mem_span_singleton_self _)
  have hc : T.Q.l.Mb ⊔ Mfr T.Q.l = ⊤ := T.Q.l.coprime
  have hr := redFn_eq_of_lift (L := R.datWp i R.triv) (rank_Wc i) hk hk'
  have hcong := fun b hb => exists_cong (b := b) (hL.βW i) R.Pg hp' (parLev_St hk.2.1) (parLev_St hk'.2.1) hr hb
  exact sub_mem_of_approx (GlobalTheory.LevelAction.latEmb_iotaW T hT i) (lt_of_lt_of_le (by norm_num) T.Q.l.three_le) hI hc hcong hf hf' a

end GlobalTheory.LevelUnique
