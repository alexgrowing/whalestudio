import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFullRankSubMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCharacterTranslatesCoinvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWittModelUnitaryActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweSplitSmall

section Local

open GlobalTheory.SplitFlip

theorem eq_coinv_or_eq_top (HB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (hnd : 2 * n ≤ d + 1) {ν β : kˣ →* ℂˣ} (hν : IsSmU ν) (hβ : IsSmU β)
    (C N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ))
    (hC : C = Submodule.span ℂ {z | ∃ (g : GL (Fin n) k) (Ψ : Matrix (Fin n) (Fin d) k → ℂ),
        Ψ ∈ SB (Matrix (Fin n) (Fin d) k) ∧ z = omA ν β g 1 Ψ - Ψ})
    (hCN : C ≤ N) (hN : N ≤ SB (Matrix (Fin n) (Fin d) k))
    (hst : ∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, omA ν β 1 h Ψ ∈ N) :
    N ≤ C ∨ SB (Matrix (Fin n) (Fin d) k) ≤ N := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  have dec : ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ SB (Matrix (Fin n) (Fin d) k),
      (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ₀ Y = 0) ∧ Ψ - Ψ₀ ∈ C := by
    intro Ψ hΨ
    obtain ⟨Ψ₀, h1, h2, h3⟩ := GlobalTheory.SmallRankCoinv.exists_fullRank_sub_mem k n d ν ϖ hϖ (hν.2 ϖ) hnd Ψ hΨ
    refine ⟨Ψ₀, h1, h2, ?_⟩
    rw [hC]
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨g, Ψ', hΨ', rfl⟩
    refine ⟨invT g, Ψ', hΨ', ?_⟩
    congr 1
    funext Y
    simp only [omA, omB, map_one, Units.val_one, Matrix.mul_one, mul_one, apow_one, invT_inv_val, gdet_invT, map_inv,
      inv_inv, apow_inv, neg_div, neg_neg]
  rcases GlobalTheory.T.span_character_translates_coinvariant HB k n d (by omega) ν β hν.1 hν.2 hβ.1 hβ.2 N (hC ▸ hCN) hN hst with h | h
  · left
    intro Ψ hΨ
    obtain ⟨Ψ₀, -, h2, h3⟩ := dec Ψ (hN hΨ)
    have h4 : Ψ₀ ∈ N := by simpa using N.sub_mem hΨ (hCN h3)
    have h5 : Ψ₀ ∈ C := hC ▸ h Ψ₀ h4 h2
    simpa using C.add_mem h3 h5
  · right
    intro Ψ hΨ
    obtain ⟨Ψ₀, h1, h2, h3⟩ := dec Ψ hΨ
    simpa using N.add_mem (hCN h3) (h Ψ₀ h1 h2)

theorem isSmU_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ν : kˣ →* ℂˣ} (h : IsSmU ν) : IsSmU ν⁻¹ := by
  refine ⟨Subgroup.isOpen_mono (H₁ := ν.ker) (fun x hx => ?_) h.1, fun x => ?_⟩
  · rw [MonoidHom.mem_ker, MonoidHom.inv_apply, hx, inv_one]
  · rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, h.2, inv_one]

end Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField E] in

theorem one_mem_UAt {n : ℕ} (Y : Spc F E n) (v : Pl F) : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by
  rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]

theorem surj_herm {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) {v : Pl F}
    (t : E →ₐ[F] Fv F v) (g : GL (Fin n) (Fv F v)) : ∃ x ∈ UAt σ X (evFin F v), locMat t 1 x = g := by
  have hJ : IsUnit (X.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hX.sig (InfinitePlace.mk φ))
    have h1 : X.J.det ≠ 0 := fun e => h0 (by
      rw [show X.J.map _ = RingHom.mapMatrix _ X.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show X.J.map t = (t : E →+* Fv F v).mapMatrix X.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  refine ⟨GlobalTheory.LeviAtPlace.leviHom hB.cm t X.J hJ hX.herm g, GlobalTheory.LeviAtPlace.lift_sub_one_at v _, Units.ext ?_⟩
  rw [locMat_val, GlobalTheory.LeviAtPlace.leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, GlobalTheory.LeviAtPlace.pairMat_fst]
  simp

theorem thetaSub_eq (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (P : IsPair B M χX χW om r s r' s') (hnd : 2 * n ≤ d + 1)
    {v : Pl F} (t : E →ₐ[F] Fv F v) {N : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ)} (hN : GlobalTheory.Published.ThetaSub om v N) :
    N = augAt om v ∨ N = SB _ := by
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_witt_model_local hP F E σ B n d X W M χX χW om r s r' s' P v t 1 1
  have act := GlobalTheory.T.linear_witt_model_unitary_action hP F E σ B n d X W M χX χW om r s r' s' P v t 1 1 ι hι
  have hex := (GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' P v).1
  have hb := Model.IsLin.bij hι
  have hν := isSmU_inv (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E χW P.hW v t).1
  have hβ := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E χX P.hX v t).1
  have haug : augAt om v ≤ SB _ := hN.1.trans hN.2.1
  have pull : ∀ Q : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ), Q ≤ SB _ → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ι φ ∈ Q.map ι → φ ∈ Q := by
    rintro Q hQ φ hφ ⟨ψ, hψ, e⟩
    rw [← hb.injOn (hQ hψ) hφ e]
    exact hψ
  have hC : Submodule.span ℂ {z | ∃ (g : GL (Fin n) (Fv F v)) (Ψ : Matrix (Fin n) (Fin d) (Fv F v) → ℂ),
      Ψ ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)) ∧
        z = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) g 1 Ψ - Ψ} ≤ (augAt om v).map ι := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, Ψ, hΨ, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hb.surjOn hΨ
    obtain ⟨x, hx, rfl⟩ := surj_herm P.base P.herm t g
    obtain ⟨φ₁, ⟨h1, H⟩, -⟩ := hex x hx 1 (one_mem_UAt _ v) φ hφ
    refine ⟨φ₁ - φ, Submodule.subset_span ⟨x, hx, φ, hφ, φ₁, h1, H, rfl⟩, ?_⟩
    rw [map_sub, act x hx 1 (one_mem_UAt _ v) φ hφ φ₁ h1 H, map_one]
  rcases eq_coinv_or_eq_top hP.bernsteinUnitaryProductIrreducible hnd hν hβ _ (N.map ι) rfl
    (hC.trans (Submodule.map_mono hN.1)) (by rintro _ ⟨φ, hφ, rfl⟩; exact hb.mapsTo (hN.2.1 hφ)) (by
      rintro h _ ⟨φ, hφ, rfl⟩
      obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.local_unitary_matrix_surjective F E σ B d W r' s' P.base P.skew v t 1 h
      obtain ⟨φ₁, ⟨h1, H⟩, -⟩ := hex 1 (one_mem_UAt _ v) x hx φ (hN.2.1 hφ)
      refine ⟨φ₁, hN.2.2 x hx φ hφ φ₁ h1 H, ?_⟩
      rw [act 1 (one_mem_UAt _ v) x hx φ (hN.2.1 hφ) φ₁ h1 H, map_one]) with h | h
  · exact Or.inl (le_antisymm (fun φ hφ => pull _ haug φ (hN.2.1 hφ) (hC (h ⟨φ, hφ, rfl⟩))) hN.1)
  · exact Or.inr (le_antisymm hN.2.1 fun φ hφ => pull _ hN.2.1 φ hφ (h (hb.mapsTo hφ)))

theorem isHecke_div {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => χ₁ x / χ₂ x
    exact h₁.1.div' h₂.1
  · rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x, div_one]

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E}
    {m m' : ℕ} (h : ResEtaPow K χ m) (h' : ResEtaPow K χ' m') : ResEtaPow K (χ / χ') (m + m') := by
  intro u
  rw [MonoidHom.div_apply, Circle.coe_div, h u, h' u]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg_one, ← pow_add]

theorem isPair_small {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    add_comm a' a ▸ resEtaPow_div h.chars.resα h.chars.resβ, h.weil'⟩

theorem howe_split_ker_small : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.MinguezThetaGL →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0 := by
  intro hP _ F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v ⟨t⟩
  have hlt := hM.triple.geo.lt
  have key := fun N hN => thetaSub_eq (N := N) hP (isPair_small hM.triple) (by omega) t hN
  refine ⟨⟨2, fun m N hmono hN => ?_⟩, fun N hN hne φ hφ => ?_⟩
  · by_contra hm
    have h01 : N ⟨0, by omega⟩ < N ⟨1, by omega⟩ := hmono (by simp [Fin.lt_def])
    have h12 : N ⟨1, by omega⟩ < N ⟨2, by omega⟩ := hmono (by simp [Fin.lt_def])
    rcases key _ (hN ⟨1, by omega⟩) with h | h
    · exact absurd (h ▸ (hN _).1.trans_lt h01 : augAt om' v < augAt om' v) (lt_irrefl _)
    · exact absurd (h12.trans_le (hN _).2.1) (h ▸ lt_irrefl _)
  · rcases key N hN with h | h
    · exact hM.fin.inv' v (h ▸ hφ)
    · exact absurd h hne

end GlobalTheory.HoweSplitSmall

end
